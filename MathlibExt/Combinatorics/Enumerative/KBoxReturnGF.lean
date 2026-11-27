/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.KBoxPaths

/-!
# Returns of box paths

The theorem `kBoxReturnGF_eq` gives the functional equation for the generating
function of box paths counted by size and returns. Reversing the paths and
compressing the box factors into single steps lets us use first descents to
factor the counting series.
-/

namespace MetaMathlibExt

open SkewDyckStep

namespace kBoxReturnGF_eq

private def rise {α : Type} (step : α → ℤ) (w : List α) : ℤ :=
  (w.map step).sum

@[simp] private theorem rise_nil {α : Type} (step : α → ℤ) : rise step [] = 0 := rfl

@[simp] private theorem rise_cons {α : Type} (step : α → ℤ) (a : α) (w : List α) :
    rise step (a :: w) = step a + rise step w := rfl

@[simp] private theorem rise_append {α : Type} (step : α → ℤ) (a b : List α) :
    rise step (a ++ b) = rise step a + rise step b := by
  simp [rise]

@[simp] private theorem rise_reverse {α : Type} (step : α → ℤ) (w : List α) :
    rise step w.reverse = rise step w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, add_comm, List.reverse_cons]

/-- Every vertex of the walk has nonnegative height. -/
private def Stays {α : Type} (step : α → ℤ) (h : ℤ) : List α → Prop
  | [] => 0 ≤ h
  | a :: w => 0 ≤ h ∧ Stays step (h + step a) w

private def Walk {α : Type} (step : α → ℤ) (h : ℤ) (w : List α) : Prop :=
  Stays step h w ∧ h + rise step w = 0

private theorem stays_append {α : Type} (step : α → ℤ) (h : ℤ) (a b : List α) :
    Stays step h (a ++ b) ↔ Stays step h a ∧ Stays step (h + rise step a) b := by
  have start_nonneg (g : ℤ) (w : List α) : Stays step g w → 0 ≤ g := by
    cases w <;> simp [Stays]
    tauto
  induction a generalizing h with
  | nil =>
    simp only [List.nil_append, Stays, rise_nil, add_zero]
    exact ⟨fun H => ⟨start_nonneg h b H, H⟩, And.right⟩
  | cons x a ih => simp [Stays, ih, add_assoc, and_assoc]

private theorem stays_iff {α : Type} (step : α → ℤ) (h : ℤ) (w : List α) :
    Stays step h w ↔ ∀ i ≤ w.length, 0 ≤ h + rise step (w.take i) := by
  induction w generalizing h with
  | nil => simp [Stays]
  | cons a w ih =>
    simp only [Stays, ih]
    constructor
    · rintro ⟨hh, hw⟩ (i | i) hi
      · simpa using hh
      · simpa [List.take_succ_cons, add_assoc] using hw i (by simpa using hi)
    · intro H
      exact ⟨by simpa using H 0 (by simp), fun i hi => by
        simpa [List.take_succ_cons, add_assoc] using H (i + 1) (by simpa using hi)⟩

/-- Count vertices at height zero, excluding the final vertex. -/
private def visits {α : Type} (step : α → ℤ) (h : ℤ) : List α → ℕ
  | [] => 0
  | a :: w => (if h = 0 then 1 else 0) + visits step (h + step a) w

private theorem visits_append {α : Type} (step : α → ℤ) (h : ℤ) (a b : List α) :
    visits step h (a ++ b) = visits step h a + visits step (h + rise step a) b := by
  induction a generalizing h with
  | nil => simp [visits]
  | cons x a ih => simp [visits, ih, add_assoc]

private theorem visits_zero_of_pos {α : Type} (step : α → ℤ) (h : ℤ) (w : List α)
    (H : Stays step (h - 1) w) : visits step h w = 0 := by
  induction w generalizing h with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨hh, hw⟩ := H
    rw [visits, ite_eq_right (by omega : h ≠ 0), zero_add]
    apply ih
    rwa [show h + step a - 1 = h - 1 + step a by omega]

private def boolStep (k : ℕ) (b : Bool) : ℤ :=
  if b then -1 else k + 1

private def skewStep : SkewDyckStep → ℤ
  | U => -1
  | D | L => 1

private theorem bool_rise (k : ℕ) (w : List Bool) :
    rise (boolStep k) w = (k + 1 : ℤ) * w.count false - w.count true := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b <;> simp [boolStep, ih, Int.mul_add, ← Int.add_assoc] <;> omega

private theorem skew_rise (w : List SkewDyckStep) :
    rise skewStep w = (w.count D : ℤ) + w.count L - w.count U := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp [skewStep, ih] <;> omega

private theorem bool_length (w : List Bool) : w.length = w.count true + w.count false := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [ih] <;> omega

private theorem skew_length (w : List SkewDyckStep) :
    w.length = w.count U + w.count D + w.count L := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp [ih] <;> omega

private theorem reverse_take_rise {α : Type} (step : α → ℤ) (w : List α) (i : ℕ) :
    rise step (w.reverse.take i) = rise step w - rise step (w.take (w.length - i)) := by
  have h := congrArg (rise step) (List.take_append_drop (w.length - i) w)
  simp only [rise_append] at h
  rw [List.take_reverse, rise_reverse]
  omega

private theorem stays_reverse_iff {α : Type} (step : α → ℤ) (w : List α)
    (h : rise step w = 0) :
    Stays step 0 w.reverse ↔ ∀ i ≤ w.length, rise step (w.take i) ≤ 0 := by
  rw [stays_iff]
  simp only [List.length_reverse, zero_add]
  constructor
  · intro H i hi
    specialize H (w.length - i) (by omega)
    rwa [reverse_take_rise step w (w.length - i), h, Nat.sub_sub_self hi, zero_sub, neg_nonneg] at H
  · intro H i hi
    rw [reverse_take_rise step w i, h, zero_sub, neg_nonneg]
    exact H _ (by omega)

private theorem stays_shift {α : Type} (step : α → ℤ) {g h : ℤ} (hg : g ≤ h)
    {w : List α} (hw : Stays step g w) : Stays step h w := by
  rw [stays_iff] at hw ⊢
  intro i hi
  have := hw i hi
  omega

/-- Split a walk at its first descent from level `h + 1` to level `h`. -/
private theorem exists_cut {k h : ℕ} {w : List Bool}
    (hw : Walk (boolStep k) (h + 1) w) :
    ∃ a b, w = a ++ true :: b ∧ Walk (boolStep k) 0 a ∧ Walk (boolStep k) h b := by
  classical
  let δ := boolStep k
  have hlast : rise δ (w.take w.length) < 0 := by
    rw [List.take_length]
    have hd := hw.2
    change (h : ℤ) + 1 + rise δ w = 0 at hd
    omega
  let hex : ∃ i, rise δ (w.take i) < 0 := ⟨w.length, hlast⟩
  have hle : Nat.find hex ≤ w.length := Nat.find_min' hex hlast
  have hpos : 0 < Nat.find hex := by
    have hs := Nat.find_spec hex
    by_contra! hn
    simp [Nat.eq_zero_of_le_zero hn] at hs
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hil : i < w.length := by omega
  have hprefix : ∀ j ≤ i, 0 ≤ rise δ (w.take j) := by
    intro j hj
    by_contra! hn
    have := Nat.find_min' hex hn
    omega
  have hs := Nat.find_spec hex
  rw [hi, List.take_succ_eq_append_getElem hil, rise_append, rise_cons, rise_nil, add_zero] at hs
  have hnonneg := hprefix i le_rfl
  have hx : w[i] = true := by
    cases hb : w[i] with
    | false =>
      rw [hb] at hs
      change rise δ (w.take i) + ((k : ℤ) + 1) < 0 at hs
      omega
    | true => rfl
  have ha : rise δ (w.take i) = 0 := by
    rw [hx] at hs
    change rise δ (w.take i) + -1 < 0 at hs
    omega
  let a := w.take i
  let b := w.drop (i + 1)
  have hab : w = a ++ true :: b := by
    have ht := List.take_append_drop (i + 1) w
    rw [List.take_succ_eq_append_getElem hil, hx, List.append_assoc] at ht
    exact ht.symm
  refine ⟨a, b, hab, ⟨?_, by simpa [a] using ha⟩, ?_⟩
  · rw [stays_iff]
    intro j hj
    have hji : j ≤ i := hj.trans (by simp [a])
    simpa [a, List.take_take, Nat.min_eq_left hji] using hprefix j hji
  · have hw' : Walk δ ((h : ℤ) + 1) (a ++ true :: b) := hab ▸ hw
    change rise δ a = 0 at ha
    refine ⟨?_, ?_⟩
    · have hh := (stays_append δ _ a (true :: b)).mp hw'.1
      have hb := hh.2
      simpa [Stays, ha, δ, boolStep, show ∀ x : ℤ, x + 1 + -1 = x by omega] using hb.2
    · have hb := hw'.2
      simp only [rise_append, rise_cons, ha] at hb
      change (h : ℤ) + 1 + (0 + (-1 + rise δ b)) = 0 at hb
      change (h : ℤ) + rise δ b = 0
      omega

private theorem walk_append_true {k h : ℕ} {a b : List Bool}
    (ha : Walk (boolStep k) 0 a) (hb : Walk (boolStep k) h b) :
    Walk (boolStep k) (h + 1) (a ++ true :: b) := by
  have hra : rise (boolStep k) a = 0 := by simpa using ha.2
  have hh : (h : ℤ) + 1 + boolStep k true = h := by simp [boolStep]
  refine ⟨(stays_append _ _ _ _).mpr ⟨stays_shift _ (by omega) ha.1, ?_⟩, ?_⟩
  · simpa [Stays, hra, hh, show (0 : ℤ) ≤ h + 1 by omega] using hb.1
  · simpa [hra, boolStep, ← add_assoc] using hb.2

private theorem cut_length_le {k : ℕ} {a b c d : List Bool}
    (ha : rise (boolStep k) a = 0) (hc : Stays (boolStep k) 0 c)
    (heq : a ++ true :: b = c ++ true :: d) : c.length ≤ a.length := by
  by_contra! h
  have ht : c.take (a.length + 1) = a ++ [true] := by
    rw [← List.take_append_of_le_length (l₂ := true :: d) h, ← heq]
    simp [List.take_append]
  have hp := (stays_iff _ _ _).mp hc (a.length + 1) h
  simp [ht, ha, boolStep] at hp

private theorem cut_injective {k : ℕ} {a b c d : List Bool}
    (ha : Walk (boolStep k) 0 a) (hc : Walk (boolStep k) 0 c)
    (heq : a ++ true :: b = c ++ true :: d) : a = c ∧ b = d := by
  have hlen := le_antisymm
    (cut_length_le (by simpa using hc.2) ha.1 heq.symm)
    (cut_length_le (by simpa using ha.2) hc.1 heq)
  have ht : a = c := calc
    a = (a ++ true :: b).take a.length := by rw [List.take_left]
    _ = (c ++ true :: d).take a.length := congrArg (List.take a.length) heq
    _ = c := by rw [hlen, List.take_left]
  subst c
  exact ⟨rfl, (List.cons.inj (List.append_cancel_left heq)).2⟩

private theorem visits_append_true {k h : ℕ} {a b : List Bool}
    (ha : Walk (boolStep k) 0 a) :
    visits (boolStep k) (h + 1) (a ++ true :: b) = visits (boolStep k) h b := by
  have hra : rise (boolStep k) a = 0 := by simpa using ha.2
  have hh : (h : ℤ) + 1 - 1 = h := by omega
  rw [visits_append, visits_zero_of_pos _ _ _ (by rw [hh]; exact stays_shift _ (by omega) ha.1)]
  simp [hra, visits, boolStep, ← sub_eq_add_neg, hh, show (h : ℤ) + 1 ≠ 0 by omega]

private theorem mem_ofFn_image {α : Type} [Fintype α] [DecidableEq α]
    (n : ℕ) (w : List α) :
    w ∈ (Finset.univ : Finset (Fin n → α)).image List.ofFn ↔ w.length = n := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun i => w[i.val], List.ofFn_getElem⟩

private noncomputable def walks (k h n : ℕ) : Finset (List Bool) := by
  classical
  exact ((Finset.univ : Finset (Fin ((k + 2) * n + h) → Bool)).image List.ofFn).filter
    (fun w => w.count false = n ∧ Walk (boolStep k) h w)

private theorem mem_walks {k h n : ℕ} {w : List Bool} :
    w ∈ walks k h n ↔ w.count false = n ∧ Walk (boolStep k) h w := by
  classical
  simp only [walks, Finset.mem_filter, mem_ofFn_image, and_iff_right_iff_imp]
  rintro ⟨hn, _, hb⟩
  have hcounts : w.count true = (k + 1) * n + h := by
    rw [bool_rise, hn] at hb
    exact_mod_cast (show (w.count true : ℤ) = ((k : ℤ) + 1) * n + h by omega)
  rw [bool_length, hcounts, hn, show k + 2 = (k + 1) + 1 by omega]
  simp only [Nat.add_mul, one_mul]
  omega

private noncomputable def walkGF (k h : ℕ) (z : Polynomial ℤ) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => ∑ w ∈ walks k h n, z ^ visits (boolStep k) h w

private theorem walkGF_succ (k h : ℕ) (z : Polynomial ℤ) :
    walkGF k (h + 1) z = walkGF k 0 1 * walkGF k h z := by
  classical
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul, walkGF, PowerSeries.coeff_mk, one_pow, Nat.cast_succ]
  symm
  have hsum (ij : ℕ × ℕ) :
      (∑ _w ∈ walks k 0 ij.1, (1 : Polynomial ℤ)) *
          (∑ w ∈ walks k h ij.2, z ^ visits (boolStep k) h w) =
        ∑ p ∈ (walks k 0 ij.1) ×ˢ (walks k h ij.2), z ^ visits (boolStep k) h p.2 := by
    rw [Finset.sum_product, Finset.sum_mul]
    simp only [one_mul]
  simp only [hsum]
  rw [Finset.sum_sigma' (Finset.antidiagonal n)
    (fun ij => walks k 0 ij.1 ×ˢ walks k h ij.2)
    (fun _ p => z ^ visits (boolStep k) h p.2)]
  refine Finset.sum_bij (fun p _ => p.2.1 ++ true :: p.2.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hn, ha, hb⟩ := (Finset.mem_sigma.mp hp).imp Finset.mem_antidiagonal.mp
      Finset.mem_product.mp
    obtain ⟨ha₁, ha₂⟩ := mem_walks.mp ha
    obtain ⟨hb₁, hb₂⟩ := mem_walks.mp hb
    exact mem_walks.mpr ⟨by simp [List.count_append, ha₁, hb₁, hn], walk_append_true ha₂ hb₂⟩
  · rintro ⟨ij, a, b⟩ hp ⟨ij', c, d⟩ hp' he
    have hab := Finset.mem_product.mp (Finset.mem_sigma.mp hp).2
    have hcd := Finset.mem_product.mp (Finset.mem_sigma.mp hp').2
    obtain ⟨rfl, rfl⟩ := cut_injective (mem_walks.mp hab.1).2 (mem_walks.mp hcd.1).2 he
    have hij : ij = ij' := Prod.ext
      ((mem_walks.mp hab.1).1.symm.trans (mem_walks.mp hcd.1).1)
      ((mem_walks.mp hab.2).1.symm.trans (mem_walks.mp hcd.2).1)
    subst ij'
    rfl
  · intro w hw
    obtain ⟨hn, hw⟩ := mem_walks.mp hw
    obtain ⟨a, b, rfl, ha, hb⟩ := exists_cut hw
    exact ⟨⟨(a.count false, b.count false), (a, b)⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_antidiagonal.mpr (by simpa [List.count_append] using hn),
        Finset.mem_product.mpr ⟨mem_walks.mpr ⟨rfl, ha⟩, mem_walks.mpr ⟨rfl, hb⟩⟩⟩, rfl⟩
  · intro p hp
    have ha := (Finset.mem_product.mp (Finset.mem_sigma.mp hp).2).1
    rw [visits_append_true (mem_walks.mp ha).2]

private theorem walkGF_eq_pow (k h : ℕ) (z : Polynomial ℤ) :
    walkGF k h z = walkGF k 0 1 ^ h * walkGF k 0 z := by
  induction h with
  | zero => simp
  | succ h ih => rw [walkGF_succ, ih, pow_succ', mul_assoc]

private theorem walkGF_zero_height (k : ℕ) (z : Polynomial ℤ) :
    walkGF k 0 z = 1 + PowerSeries.C z * PowerSeries.X * walkGF k (k + 1) z := by
  classical
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    have hz : walks k 0 0 = {[]} := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw, _, he⟩ := mem_walks.mp hw
        rw [bool_rise, hw] at he
        simpa using List.eq_nil_of_length_eq_zero (by rw [bool_length, hw]; omega)
      · intro hw
        have : w = [] := by simpa using hw
        simp [this, mem_walks, Walk, Stays]
    simp [walkGF, hz, PowerSeries.coeff_zero_X_mul, visits]
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, zero_add, PowerSeries.coeff_succ_X_mul,
      walkGF, PowerSeries.coeff_mk, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun w _ => false :: w) ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨hn, hw⟩ := mem_walks.mp hw
      simpa [mem_walks, Walk, Stays, boolStep, hn, add_assoc] using hw
    · intro a _ b _ hab
      exact (List.cons.inj hab).2
    · intro w hw
      obtain ⟨hw₁, hw₂⟩ := mem_walks.mp hw
      cases w with
      | nil => simp at hw₁
      | cons b w =>
        cases b with
        | false =>
          exact ⟨w, mem_walks.mpr ⟨by simpa using hw₁,
            by simpa [Walk, Stays, boolStep, add_assoc] using hw₂⟩, rfl⟩
        | true =>
          have hs := (stays_iff _ _ _).mp hw₂.1 1 (by simp)
          simp [boolStep] at hs
    · intro w _
      simp [visits, boolStep, pow_add]

/-! ### Recovering full box blocks -/

private theorem augment_true (k : ℕ) (w : List Bool) :
    augmentKDyckWord (k + 1) (true :: w) = U :: augmentKDyckWord (k + 1) w := rfl

private theorem augment_false (k : ℕ) (w : List Bool) :
    augmentKDyckWord (k + 1) (false :: w) =
      boxFactor k ++ D :: augmentKDyckWord (k + 1) w := by
  simp [augmentKDyckWord, boxFactor, List.append_assoc]

private theorem augment_append (k : ℕ) (u v : List Bool) :
    augmentKDyckWord (k + 1) (u ++ v) =
      augmentKDyckWord (k + 1) u ++ augmentKDyckWord (k + 1) v := by
  simp [augmentKDyckWord]

private theorem augment_starts (k : ℕ) (w : List Bool) :
    augmentKDyckWord (k + 1) w = [] ∨ ∃ r, augmentKDyckWord (k + 1) w = U :: r := by
  cases w with
  | nil => exact Or.inl rfl
  | cons b w => cases b <;> exact Or.inr ⟨_, rfl⟩

private theorem augment_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (augmentKDyckWord (k + 1)) := by
  have hne (u v : List Bool) :
      augmentKDyckWord (k + 1) (true :: u) ≠ augmentKDyckWord (k + 1) (false :: v) := by
    intro H
    rw [augment_true, augment_false] at H
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have ht := (List.cons.inj H).2
    rcases augment_starts (j + 1) u with hu | ⟨_, hu⟩ <;>
      simp [List.replicate_succ, hu] at ht
  intro u
  induction u with
  | nil =>
    rintro (_ | ⟨b, v⟩) h
    · rfl
    · cases b <;> simp [augmentKDyckWord] at h
  | cons b u ih =>
    rintro (_ | ⟨c, v⟩) h
    · cases b <;> simp [augmentKDyckWord] at h
    · cases b <;> cases c
      · rw [augment_false, augment_false] at h
        exact congrArg (false :: ·) (ih ((List.cons.inj (List.append_cancel_left h)).2))
      · exact (hne v u h.symm).elim
      · exact (hne u v h).elim
      · rw [augment_true, augment_true] at h
        exact congrArg (true :: ·) (ih (List.cons.inj h).2)

private abbrev factors (k : ℕ) (w : List SkewDyckStep) :=
  skewFactorCount (boxFactor k) w

private abbrev downs (w : List SkewDyckStep) := w.count D + w.count L

private theorem factors_cons (k : ℕ) (a : SkewDyckStep) (w : List SkewDyckStep) :
    factors k (a :: w) = factors k w + if boxFactor k <+: a :: w then 1 else 0 := by
  simp [skewFactorCount, List.countP_cons, List.isPrefixOf_iff_prefix]

private theorem factors_cons_of_ne (k : ℕ) {a : SkewDyckStep} (ha : a ≠ U)
    (w : List SkewDyckStep) : factors k (a :: w) = factors k w := by
  rw [factors_cons]
  simp [boxFactor, List.cons_prefix_cons, Ne.symm ha]

private theorem factors_box (k : ℕ) (w : List SkewDyckStep) :
    factors k (boxFactor k ++ w) = factors k w + 1 := by
  have hr (j : ℕ) : factors k (List.replicate j D ++ L :: w) = factors k w := by
    induction j with
    | zero => simp [factors_cons_of_ne k (by decide : L ≠ U)]
    | succ j ih =>
      simpa [List.replicate_succ, factors_cons_of_ne k (by decide : D ≠ U)] using ih
  rw [show boxFactor k ++ w = U :: (List.replicate k D ++ L :: w) by
    simp [boxFactor, List.append_assoc], factors_cons, ← show boxFactor k ++ w =
      U :: (List.replicate k D ++ L :: w) by simp [boxFactor, List.append_assoc],
    ite_eq_left (List.prefix_append _ _), hr]

private theorem boxFactor_last (k : ℕ) : (boxFactor k).getLast? = some L := by
  change ((U :: List.replicate k D) ++ [L]).getLast? = _
  rw [List.getLast?_append]
  rfl

private theorem factors_end_D (k : ℕ) (w : List SkewDyckStep) :
    factors k (w ++ [D]) = factors k w := by
  have hp (v : List SkewDyckStep) : boxFactor k <+: v ++ [D] ↔ boxFactor k <+: v := by
    refine ⟨fun h => ?_, fun h => h.trans (List.prefix_append _ _)⟩
    by_cases hl : (boxFactor k).length ≤ v.length
    · simpa only [List.prefix_iff_eq_take, List.take_append_of_le_length hl] using h
    · obtain ⟨r, hr⟩ := h
      have he : r = [] := List.eq_nil_of_length_eq_zero (by
        have := congrArg List.length hr
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega)
      simp only [he, List.append_nil] at hr
      have hl := congrArg List.getLast? hr
      simp [boxFactor_last, List.getLast?_append] at hl
  induction w with
  | nil => simp [skewFactorCount, boxFactor]
  | cons a w ih =>
    rw [List.cons_append, factors_cons, factors_cons, ih]
    simp only [← List.cons_append, hp]

private theorem factors_augment {k : ℕ} (hk : 1 ≤ k) (w : List Bool) :
    factors k (augmentKDyckWord (k + 1) w) = w.count false := by
  induction w with
  | nil => simp [augmentKDyckWord, skewFactorCount, boxFactor]
  | cons b w ih =>
    cases b with
    | false =>
      simp [augment_false, factors_box, factors_cons_of_ne k (by decide : D ≠ U), ih]
    | true =>
      rw [augment_true, factors_cons, ih]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rcases augment_starts (j + 1) w with hw | ⟨_, hw⟩ <;>
        simp [hw, boxFactor, List.replicate_succ, List.cons_prefix_cons]

private theorem downs_augment (k : ℕ) (w : List Bool) :
    downs (augmentKDyckWord (k + 1) w) = (k + 2) * w.count false := by
  induction w with
  | nil => simp [augmentKDyckWord]
  | cons b w ih =>
    cases b with
    | false =>
      simp [downs, augment_false, boxFactor, List.count_replicate, Nat.mul_succ] at *
      omega
    | true => simpa [downs, augment_true] using ih

private def EndsD (w : List SkewDyckStep) : Prop :=
  w = [] ∨ w.getLast? = some D

private theorem endsD_suffix {a b : List SkewDyckStep} (h : EndsD (a ++ b)) :
    EndsD b := by
  cases b with
  | nil => exact Or.inl rfl
  | cons c b => simpa [EndsD, List.getLast?_append] using h

/-- In a word ending in `D`, each box consumes `k + 2` descending steps.
If the bound is attained, every step belongs to a single `U` or a full box block. -/
private theorem parse (k : ℕ) (w : List SkewDyckStep) (hlu : ¬ [L, U] <:+: w)
    (hend : EndsD w) :
    (k + 2) * factors k w ≤ downs w ∧
      (downs w = (k + 2) * factors k w → ∃ a, augmentKDyckWord (k + 1) a = w) := by
  cases w with
  | nil => exact ⟨by simp [skewFactorCount, boxFactor], fun _ => ⟨[], rfl⟩⟩
  | cons x w =>
    by_cases hp : boxFactor k <+: x :: w
    · obtain ⟨r, hr⟩ := hp
      cases r with
      | nil =>
        rw [← hr] at hend
        simp [EndsD, boxFactor_last, show boxFactor k ≠ [] by simp [boxFactor]] at hend
      | cons b s =>
        rw [← hr] at hlu hend ⊢
        have hb : b ≠ U := by
          rintro rfl
          exact hlu ⟨U :: List.replicate k D, s, by simp [boxFactor]⟩
        have hlus : ¬ [L, U] <:+: s := fun h =>
          hlu (h.trans ((List.suffix_cons b s).trans (List.suffix_append _ _)).isInfix)
        have hend' : EndsD s := endsD_suffix (a := boxFactor k ++ [b])
          (by simpa [List.append_assoc] using hend)
        have hshort : s.length < (x :: w).length := by
          rw [← hr]
          simp
          omega
        obtain ⟨hl, hs⟩ := parse k s hlus hend'
        rw [factors_box, factors_cons_of_ne k hb, Nat.mul_succ]
        have hc : downs (boxFactor k ++ b :: s) = downs s + (k + 2) := by
          cases b with
          | U => exact (hb rfl).elim
          | D | L => simp [downs, boxFactor, List.count_replicate]; omega
        rw [hc]
        refine ⟨Nat.add_le_add_right hl _, fun he => ?_⟩
        obtain ⟨a, ha⟩ := hs (Nat.add_right_cancel he)
        cases b with
        | U => exact (hb rfl).elim
        | D => exact ⟨false :: a, by rw [augment_false, ha]⟩
        | L =>
          rcases augment_starts k a with hnil | ⟨t, ht⟩
          · rw [← ha, hnil] at hend
            change EndsD (boxFactor k ++ [L]) at hend
            simp [EndsD, List.getLast?_append] at hend
          · exfalso
            exact hlu ⟨boxFactor k, t, by rw [← ha, ht]; simp [List.append_assoc]⟩
    · have hshort : w.length < (x :: w).length := by simp
      obtain ⟨hl, hs⟩ := parse k w (fun h => hlu (List.infix_cons_iff.mpr (.inr h)))
        (endsD_suffix (a := [x]) hend)
      rw [factors_cons, ite_eq_right hp, Nat.add_zero]
      cases x with
      | U =>
        refine ⟨by simpa [downs] using hl, fun he => ?_⟩
        obtain ⟨a, ha⟩ := hs (by simpa [downs] using he)
        exact ⟨true :: a, by rw [augment_true, ha]⟩
      | D | L =>
        dsimp only [downs] at hl
        constructor
        · simp [downs]; omega
        · simp [downs]; omega
termination_by w.length

private def Avoids (w : List SkewDyckStep) : Prop :=
  ¬ [U, L] <:+: w ∧ ¬ [L, U] <:+: w

private theorem avoids_cons {a : SkewDyckStep} {w : List SkewDyckStep} (hw : Avoids w)
    (hul : ¬ [U, L] <+: a :: w) (hlu : ¬ [L, U] <+: a :: w) :
    Avoids (a :: w) := by
  simpa [Avoids, List.infix_cons_iff, hul, hlu] using hw

private theorem avoids_box {k : ℕ} (hk : 1 ≤ k) {w : List SkewDyckStep}
    (hw : Avoids (L :: w)) : Avoids (boxFactor k ++ w) := by
  have hr (j : ℕ) : Avoids (D :: List.replicate j D ++ L :: w) := by
    induction j with
    | zero => apply avoids_cons hw <;> simp [List.cons_prefix_cons]
    | succ j ih =>
      simp only [List.replicate_succ, List.cons_append]
      apply avoids_cons ih <;> simp [List.cons_prefix_cons]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [boxFactor, List.replicate_succ, List.cons_append, List.append_assoc]
  apply avoids_cons (hr j) <;> simp [List.cons_prefix_cons]

private theorem avoids_augment {k : ℕ} (hk : 1 ≤ k) (w : List Bool) :
    Avoids (augmentKDyckWord (k + 1) w) := by
  induction w with
  | nil => simp [Avoids, augmentKDyckWord]
  | cons b w ih =>
    cases b with
    | true =>
      rw [augment_true]
      apply avoids_cons ih _ (by simp [List.cons_prefix_cons])
      rcases augment_starts k w with h | ⟨t, h⟩ <;> simp [h, List.cons_prefix_cons]
    | false =>
      rw [augment_false]
      refine avoids_box hk (avoids_cons (avoids_cons ih ?_ ?_) ?_ ?_) <;>
        simp [List.cons_prefix_cons]

private def box (k : ℕ) (w : List Bool) : List SkewDyckStep :=
  augmentKDyckWord (k + 1) w.reverse ++ boxFactor k

private theorem box_end_D (k : ℕ) (w : List Bool) :
    box k w ++ [D] = augmentKDyckWord (k + 1) (w.reverse ++ [false]) := by
  rw [augment_append, augment_false]
  simp [box, augmentKDyckWord, List.append_assoc]

private theorem avoids_box_word {k : ℕ} (hk : 1 ≤ k) (w : List Bool) :
    Avoids (box k w) := by
  have h := avoids_augment hk (w.reverse ++ [false])
  rw [← box_end_D] at h
  exact ⟨fun hi => h.1 (hi.trans (List.prefix_append _ _).isInfix),
    fun hi => h.2 (hi.trans (List.prefix_append _ _).isInfix)⟩

/-! ### Comparing reversed box paths with walks -/

private def ramp (k : ℕ) : List SkewDyckStep := L :: (List.replicate k D ++ [U])

private def encode (k : ℕ) (w : List Bool) : List SkewDyckStep :=
  (augmentKDyckWord (k + 1) w.reverse).reverse

private theorem encode_cons (k : ℕ) (b : Bool) (w : List Bool) :
    encode k (b :: w) = (if b then [U] else D :: ramp k) ++ encode k w := by
  rw [encode, List.reverse_cons, augment_append, List.reverse_append]
  cases b <;> simp [ramp, encode, augmentKDyckWord, List.reverse_append, List.append_assoc]

private theorem reverse_box (k : ℕ) (w : List Bool) :
    (box k w).reverse = ramp k ++ encode k w := by
  simp [box, encode, ramp, boxFactor, List.reverse_append, List.reverse_cons, List.append_assoc]

private theorem rise_replicate_D (n : ℕ) : rise skewStep (List.replicate n D) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, skewStep, add_comm]

private theorem ramp_rise (k : ℕ) : rise skewStep (ramp k) = k := by
  simp [ramp, rise_replicate_D, skewStep]

private theorem stays_replicate_D (n : ℕ) (h : ℤ) :
    Stays skewStep h (List.replicate n D) ↔ 0 ≤ h := by
  induction n generalizing h with
  | zero => simp [Stays]
  | succ n ih => simp [List.replicate_succ, Stays, skewStep, ih]; omega

private theorem stays_ramp (k : ℕ) (h : ℤ) :
    Stays skewStep h (ramp k) ↔ 0 ≤ h := by
  simp [ramp, Stays, skewStep, stays_append, stays_replicate_D, rise_replicate_D]
  omega

private theorem visits_replicate_D (n : ℕ) {h : ℤ} (hh : 0 < h) :
    visits skewStep h (List.replicate n D) = 0 :=
  visits_zero_of_pos _ _ _ ((stays_replicate_D n _).mpr (by omega))

private theorem visits_ramp (k : ℕ) {h : ℤ} (hh : 0 ≤ h) :
    visits skewStep h (ramp k) = if h = 0 then 1 else 0 := by
  simp [ramp, visits, visits_append, skewStep, rise_replicate_D,
    visits_replicate_D k (show 0 < h + 1 by omega), ite_eq_right (by omega : h + 1 + k ≠ 0)]

private theorem encode_rise (k : ℕ) (w : List Bool) :
    rise skewStep (encode k w) = rise (boolStep k) w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [encode_cons, rise_append, ih]
    cases b <;> simp [boolStep, skewStep, ramp_rise, add_comm]

private theorem encode_stays (k : ℕ) (h : ℤ) (w : List Bool) :
    Stays skewStep h (encode k w) ↔ Stays (boolStep k) h w := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih =>
    rw [encode_cons]
    cases b
    · simp [stays_append, Stays, skewStep, boolStep, stays_ramp, ramp_rise, ih, add_assoc,
        show ∀ x : ℤ, 1 + x = x + 1 from fun x => add_comm 1 x]
      omega
    · simp [Stays, skewStep, boolStep, ih]

private theorem encode_visits (k : ℕ) (h : ℤ) (w : List Bool)
    (hw : Stays (boolStep k) h w) :
    visits skewStep h (encode k w) = visits (boolStep k) h w := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨hh, hw⟩ := hw
    rw [encode_cons]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.cons_append, visits, skewStep]
      rw [visits_append, ramp_rise, visits_ramp k (by omega),
        ite_eq_right (by omega : h + 1 ≠ 0), zero_add]
      rw [show h + 1 + k = h + boolStep k false by simp [boolStep]; omega, ih _ hw]
    · have hh := ih _ hw
      simpa [visits, skewStep, boolStep, hh]

private theorem box_walk (k : ℕ) (w : List Bool) :
    Walk skewStep 0 (box k w).reverse ↔ Walk (boolStep k) k w := by
  simp [Walk, reverse_box, stays_append, stays_ramp, ramp_rise, encode_rise, encode_stays]

private theorem box_factors {k : ℕ} (hk : 1 ≤ k) (w : List Bool) :
    factors k (box k w) = w.count false + 1 := by
  rw [← factors_end_D k, box_end_D, factors_augment hk]
  simp [List.count_append]

private theorem box_downs (k : ℕ) (w : List Bool) :
    downs (box k w) = (k + 2) * (w.count false + 1) - 1 := by
  have h := downs_augment k (w.reverse ++ [false])
  rw [← box_end_D] at h
  simp [downs, List.count_append] at h ⊢
  omega

private theorem mem_kBoxPaths {k n : ℕ} {w : List SkewDyckStep} :
    w ∈ kBoxPaths k n ↔
      Avoids w ∧ Walk skewStep 0 w.reverse ∧ downs w = (k + 2) * n - 1 ∧ factors k w = n := by
  simp only [kBoxPaths, skewDyckWords, Finset.mem_filter, mem_ofFn_image, Walk,
    rise_reverse, zero_add, IsSkewDyckWord, Avoids, downs]
  have hbal : rise skewStep w = 0 ↔ w.count U = w.count D + w.count L := by
    rw [skew_rise]
    omega
  by_cases he : rise skewStep w = 0
  · simp only [stays_reverse_iff _ _ he, skew_rise, he, hbal.mp he, true_and, and_true]
    have hp (i : ℕ) : (↑((w.take i).count D) + ↑((w.take i).count L) -
        ↑((w.take i).count U) : ℤ) ≤ 0 ↔
          (w.take i).count D + (w.take i).count L ≤ (w.take i).count U := by omega
    simp only [hp, skew_length w, hbal.mp he]
    constructor <;> intro H
    · exact ⟨⟨H.1.2.1, H.1.2.2.1⟩, H.1.2.2.2, by omega, H.2⟩
    · exact ⟨⟨by omega, H.1.1, H.1.2, H.2.1⟩, H.2.2.2⟩
  · simp [he, mt hbal.mpr he]

private theorem box_mem {k n : ℕ} (hk : 1 ≤ k) (w : List Bool) :
    box k w ∈ kBoxPaths k (n + 1) ↔ w ∈ walks k k n := by
  simp only [mem_kBoxPaths, mem_walks, box_walk, box_downs, box_factors hk,
    avoids_box_word hk, true_and, Nat.add_right_cancel_iff]
  exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, by rw [h.1], h.1⟩⟩

private theorem box_injective {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (box k) := by
  intro a b hab
  exact List.reverse_inj.mp (augment_injective hk (List.append_cancel_right hab))

private theorem box_surjective {k n : ℕ} (hk : 1 ≤ k) {w : List SkewDyckStep}
    (hw : w ∈ kBoxPaths k (n + 1)) :
    ∃ v ∈ walks k k n, box k v = w := by
  obtain ⟨ha, _, hd, hf⟩ := mem_kBoxPaths.mp hw
  have hlu : ¬ [L, U] <:+: w ++ [D] := by
    intro h
    have h' : ¬ [U, L] <:+: D :: w.reverse := by
      intro H
      rcases List.infix_cons_iff.mp H with hp | hi
      · simp [List.cons_prefix_cons] at hp
      · exact ha.2 (by simpa using hi.reverse)
    exact h' (by simpa using h.reverse)
  have hd' : downs (w ++ [D]) = (k + 2) * factors k (w ++ [D]) := by
    rw [factors_end_D, hf]
    have hn : 0 < (k + 2) * (n + 1) := Nat.mul_pos (by omega) (by omega)
    have he : downs (w ++ [D]) = downs w + 1 := by
      simp [downs, List.count_append]
      omega
    rw [he, hd, Nat.sub_add_cancel (by omega)]
  obtain ⟨a, he⟩ := (parse k (w ++ [D]) hlu (by simp [EndsD, List.getLast?_append])).2 hd'
  match ha : a.reverse with
  | [] =>
    have hz : a = [] := List.reverse_inj.mp (ha.trans rfl)
    simp [hz, augmentKDyckWord] at he
  | b :: v =>
    have hav : a = v.reverse ++ [b] := by
      have h := congrArg List.reverse ha
      simpa [List.reverse_cons] using h
    rw [hav, augment_append] at he
    cases b
    · have he' : box k v ++ [D] = w ++ [D] := by
        rw [box_end_D, augment_append]
        exact he
      have hv := List.append_cancel_right he'
      exact ⟨v, (box_mem hk v).mp (hv ▸ hw), hv⟩
    · have hl := congrArg List.getLast? he
      simp [augmentKDyckWord, List.getLast?_append] at hl

private theorem visits_eq_countP {α : Type} (step : α → ℤ) (h : ℤ) (w : List α) :
    visits step h w =
      (List.range w.length).countP (fun i => decide (h + rise step (w.take i) = 0)) := by
  induction w generalizing h with
  | nil => simp [visits]
  | cons a w ih =>
    simp [visits, List.range_succ_eq_map, List.countP_cons, List.countP_map, ih,
      Function.comp_def, List.take_succ_cons, add_assoc, Nat.add_comm]
    rfl

private theorem countP_range (p : ℕ → Bool) (n : ℕ) :
    (List.range n).countP p = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp [List.countP_cons]

private theorem skewReturns_reverse {w : List SkewDyckStep} (hw : Walk skewStep 0 w.reverse) :
    skewReturns w = visits skewStep 0 w.reverse := by
  have hzero : rise skewStep w = 0 := by simpa using hw.2
  rw [visits_eq_countP, skewReturns, ← List.countP_eq_length_filter]
  simp only [List.length_reverse, countP_range, decide_eq_true_eq, zero_add]
  refine Finset.sum_bij (fun i _ => w.length - (i + 1)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro a ha b hb he
    simp only [Finset.mem_range] at ha hb
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact ⟨w.length - (i + 1), Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [reverse_take_rise, hzero, show w.length - (w.length - (i + 1)) = i + 1 by omega]
    simp only [zero_sub, neg_eq_zero, skew_rise]
    exact if_congr (by omega) rfl rfl

private theorem returns_box {k n : ℕ} (w : List Bool) (hw : w ∈ walks k k n) :
    skewReturns (box k w) = visits (boolStep k) k w + 1 := by
  have hb := (mem_walks.mp hw).2
  rw [skewReturns_reverse ((box_walk k w).mpr hb), reverse_box, visits_append,
    ramp_rise, zero_add, visits_ramp k le_rfl, ite_eq_left rfl, encode_visits _ _ _ hb.1,
    Nat.add_comm]

private theorem box_GF (k : ℕ) (hk : 1 ≤ k) :
    kBoxReturnGF k =
      PowerSeries.C Polynomial.X * PowerSeries.X * walkGF k k Polynomial.X := by
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [kBoxReturnGF, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp only [PowerSeries.coeff_succ_X_mul, kBoxReturnGF, walkGF, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ite_false, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun w _ => box k w) (fun w hw => (box_mem hk w).mpr hw)
      (fun _ _ _ _ h => box_injective hk h) ?_ ?_
    · intro w hw
      obtain ⟨v, hv, he⟩ := box_surjective hk hw
      exact ⟨v, hv, he⟩
    · intro w hw
      rw [returns_box w hw, pow_succ']

private theorem mem_kDyckWords_reverse {k n : ℕ} {w : List Bool} :
    w.reverse ∈ kDyckWords (k + 1) n ↔ w ∈ walks k 0 n := by
  rw [kDyckWords, Finset.mem_filter, mem_ofFn_image, mem_walks]
  simp only [IsKDyckWord, Walk, List.count_reverse, List.length_reverse, Nat.cast_zero, zero_add]
  have hb : rise (boolStep k) w = 0 ↔ w.count true = (k + 1) * w.count false := by
    rw [bool_rise]
    exact ⟨fun h => by exact_mod_cast (show (w.count true : ℤ) =
      ((k : ℤ) + 1) * w.count false by omega), fun h => by
        have h' : (w.count true : ℤ) = ((k : ℤ) + 1) * w.count false := by exact_mod_cast h
        omega⟩
  by_cases he : rise (boolStep k) w = 0
  · have hp (i : ℕ) : rise (boolStep k) (w.reverse.take i) ≤ 0 ↔
        (k + 1) * (w.reverse.take i).count false ≤ (w.reverse.take i).count true := by
      rw [bool_rise, sub_nonpos]
      exact_mod_cast Iff.rfl
    have hlen : w.length = (k + 2) * w.count false := by
      rw [bool_length, hb.mp he, show k + 2 = (k + 1) + 1 by omega]
      simp [Nat.add_mul]
    have hs : Stays (boolStep k) 0 w ↔
        ∀ i ≤ w.reverse.length, rise (boolStep k) (w.reverse.take i) ≤ 0 := by
      simpa using stays_reverse_iff (boolStep k) w.reverse (by simp [he])
    rw [hs]
    simp only [List.length_reverse, hb.mp he, true_and, hp, he, and_true]
    constructor
    · intro H
      exact ⟨H.2.2, H.2.1⟩
    · intro H
      exact ⟨by simpa [H.1] using hlen, H.2, H.1⟩
  · simp [he, mt hb.mpr he]

private theorem dyck_GF {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) = walkGF k 0 1 := by
  apply PowerSeries.ext
  intro n
  have hc : (augmentedKDyckPaths (k + 1) n).card = (walks k 0 n).card := by
    rw [augmentedKDyckPaths, Finset.card_image_of_injective _ (augment_injective hk)]
    have heq : (walks k 0 n).image List.reverse = kDyckWords (k + 1) n := by
      ext w
      constructor
      · intro hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact mem_kDyckWords_reverse.mpr ha
      · intro hw
        exact Finset.mem_image.mpr ⟨w.reverse, mem_kDyckWords_reverse.mp
          (by simpa using hw), List.reverse_reverse _⟩
    rw [← heq, Finset.card_image_of_injective _ List.reverse_injective]
  simp [PowerSeries.coeff_map, augmentedKDyckGF, walkGF, hc]

end kBoxReturnGF_eq

open kBoxReturnGF_eq

@[expose] public section

local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
local notation "𝒕" => PowerSeries.C (Polynomial.X : Polynomial ℤ)

/-- **Functional equation for the returns generating function.** Let $k \ge 1$, let
$F_k(t, x) \in \mathbb{Z}[t][[x]]$ be the generating function of $k$-box paths of size at least
$1$ by number of returns (exponent of $t$) and size (exponent of $x$), and let $G_{k+1}(x)$ be
the generating function of augmented $(k+1)$-Dyck paths by size, viewed in $\mathbb{Z}[t][[x]]$.
Then
$$\bigl(1 - t x G_{k+1}^{k+1}\bigr) F_k = t x G_{k+1}^k.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 8
(`jis-2024-24.2.4-lem-8`). -/
public theorem kBoxReturnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    (1 - 𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ (k + 1)) *
        kBoxReturnGF k =
      𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ k := by
  rw [dyck_GF hk, box_GF k hk, walkGF_eq_pow k k Polynomial.X]
  let G := walkGF k 0 1
  let W := walkGF k 0 Polynomial.X
  have hW : W = 1 + 𝒕 * 𝒙 * G ^ (k + 1) * W := by
    simpa only [walkGF_eq_pow k (k + 1), ← mul_assoc] using walkGF_zero_height k Polynomial.X
  have he : (1 - 𝒕 * 𝒙 * G ^ (k + 1)) * W = 1 := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact hW
  change (1 - 𝒕 * 𝒙 * G ^ (k + 1)) * (𝒕 * 𝒙 * (G ^ k * W)) = 𝒕 * 𝒙 * G ^ k
  calc
    _ = (𝒕 * 𝒙 * G ^ k) * ((1 - 𝒕 * 𝒙 * G ^ (k + 1)) * W) := by ac_rfl
    _ = _ := by rw [he, mul_one]

/-- **Functional equation for the augmented Dyck generating function.** Let $k \ge 1$ and let
$G_{k+1}(x) \in \mathbb{Z}[[x]]$ be the generating function of augmented $(k+1)$-Dyck paths
by size. Then
$$G_{k+1} = 1 + x \, G_{k+1}^{k+2}.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public theorem augmentedKDyckGF_eq {k : ℕ} (hk : 1 ≤ k) :
    augmentedKDyckGF (k + 1) =
      1 + PowerSeries.X * augmentedKDyckGF (k + 1) ^ (k + 2) := by
  have hG : PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) =
      1 + PowerSeries.X *
        PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ (k + 2) := by
    rw [dyck_GF hk]
    calc walkGF k 0 1 = 1 + PowerSeries.C 1 * PowerSeries.X * walkGF k (k + 1) 1 :=
          walkGF_zero_height k 1
      _ = 1 + PowerSeries.X * walkGF k 0 1 ^ (k + 2) := by
          have hpow : walkGF k 0 1 ^ (k + 2) =
              walkGF k 0 1 ^ (k + 1) * walkGF k 0 1 := pow_succ _ _
          rw [walkGF_eq_pow k (k + 1) 1, hpow]
          simp
  exact PowerSeries.map_injective Polynomial.C Polynomial.C_injective
    (by simpa using hG)

end

end MetaMathlibExt
