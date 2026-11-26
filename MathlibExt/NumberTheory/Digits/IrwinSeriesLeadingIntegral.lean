/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
import Mathlib.Tactic

/-!
# Prefix reciprocal sums as integrals against the Irwin measures

This module proves that the prefix-restricted reciprocal terms of a positive
integer sum to the integral of $1/(n + x)$ over $[0, 1)$ against the Irwin
measure.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace integral_eq_leadingReciprocal_hasSum

private noncomputable def phi (b d : ℕ) (hd : d < b) (X : List (Fin b)) : ℝ :=
  (b : ℝ) ^ (-(X.length : ℤ)) * (1 / 2 : ℝ) ^ (X.count ⟨d, hd⟩)

private noncomputable def wt (b d : ℕ) (hd : d < b) (a : Fin b) : ℝ :=
  if a = ⟨d, hd⟩ then (1 / 2 : ℝ) / b else 1 / (b : ℝ)

private theorem phi_nonneg (b d : ℕ) (hd : d < b) (X : List (Fin b)) :
    0 ≤ phi b d hd X := by
  unfold phi
  positivity

private theorem phi_nil (b d : ℕ) (hd : d < b) : phi b d hd [] = 1 := by
  simp [phi]

private theorem phi_cons (b d : ℕ) (hb : 1 < b) (hd : d < b) (a : Fin b)
    (X : List (Fin b)) : phi b d hd (a :: X) = wt b d hd a * phi b d hd X := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hcount : (a :: X).count ⟨d, hd⟩ =
      X.count ⟨d, hd⟩ + (if a = ⟨d, hd⟩ then 1 else 0) := by
    by_cases ha : a = ⟨d, hd⟩
    · subst ha
      rw [List.count_cons_self]
      simp
    · rw [List.count_cons_of_ne ha]
      simp [ha]
  unfold phi wt
  simp only [List.length_cons, hcount]
  have hpow : (b : ℝ) ^ (-((X.length + 1 : ℕ) : ℤ)) =
      (b : ℝ) ^ (-(X.length : ℤ)) * (b : ℝ)⁻¹ := by
    have h : (-((X.length + 1 : ℕ) : ℤ)) = (-(X.length : ℤ)) + (-1 : ℤ) := by
      push_cast; ring
    rw [h, zpow_add₀ hbR, zpow_neg_one]
  rw [hpow]
  split_ifs with ha
  · rw [pow_add, pow_one]
    field_simp
  · simp only [add_zero]
    rw [one_div]
    ring

private theorem sum_wt (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    ∑ a : Fin b, wt b d hd a = ((b : ℝ) - 1 / 2) / b := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h := (Finset.add_sum_erase Finset.univ (fun a => wt b d hd a)
    (Finset.mem_univ (⟨d, hd⟩ : Fin b))).symm
  have herase : ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), wt b d hd a = ((b : ℝ) - 1) / b := by
    have h1 : ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), wt b d hd a =
        ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), (1 / (b : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hane : a ≠ ⟨d, hd⟩ := by
        intro hEq
        exact (Finset.mem_erase.mp ha).1 hEq
      simp [wt, hane]
    rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (⟨d, hd⟩ : Fin b)),
      Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ b)]
    push_cast
    ring
  rw [h, herase]
  simp [wt]
  field_simp
  ring

private theorem phi_bound : ∀ (T : ℕ) (b d : ℕ) (_hb : 1 < b) (hd : d < b)
    (F : Finset (List (Fin b))), (∀ X ∈ F, X.length ≤ T) →
    ∑ X ∈ F, phi b d hd X ≤
      ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
  intro T
  induction T with
  | zero =>
    intro b d _hb hd F hF
    have hsub : F ⊆ {[]} := by
      intro X hX
      have hlen := hF X hX
      simp only [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun X _ _ => phi_nonneg b d hd X)
    rw [Finset.sum_singleton, phi_nil] at hle
    simpa using hle
  | succ T ih =>
    intro b d _hb hd F hF
    have hq : ((b : ℝ) - 1 / 2) / b = ∑ a : Fin b, wt b d hd a := (sum_wt b d _hb hd).symm
    set F0 := F.filter (fun X => X = []) with hF0
    set F1 := F.filter (fun X => ¬ X = []) with hF1
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun X => X = [])
      (phi b d hd)
    have hF0le : ∑ X ∈ F0, phi b d hd X ≤ 1 := by
      have hsub : F0 ⊆ {[]} := by
        intro X hX
        simp only [hF0, Finset.mem_filter, Finset.mem_singleton] at hX ⊢
        exact hX.2
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun X _ _ => phi_nonneg b d hd X)
      rwa [Finset.sum_singleton, phi_nil] at hle
    have hF1le : ∑ X ∈ F1, phi b d hd X ≤
        (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
      set tails := F1.image List.tail with htails
      have hTails : ∀ Y ∈ tails, Y.length ≤ T := by
        intro Y hY
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
        have hlen := hF X (Finset.mem_of_mem_filter X hX)
        have hne : X ≠ [] := (Finset.mem_filter.mp hX).2
        have htl : X.tail.length = X.length - 1 := by simp [List.length_tail]
        omega
      have hIH := ih b d _hb hd tails hTails
      set P := (Finset.univ ×ˢ tails).filter (fun p : Fin b × List (Fin b) =>
        p.1 :: p.2 ∈ F1) with hP
      have himg : P.image (fun p : Fin b × List (Fin b) => p.1 :: p.2) = F1 := by
        ext X
        constructor
        · intro hX
          obtain ⟨p, hp, hpX⟩ := Finset.mem_image.mp hX
          rw [← hpX]
          exact (Finset.mem_filter.mp hp).2
        · intro hX
          have hne : X ≠ [] := (Finset.mem_filter.mp hX).2
          refine Finset.mem_image.mpr ⟨⟨X.head hne, X.tail⟩, ?_, List.cons_head_tail hne⟩
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            exact ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨X, hX, rfl⟩⟩
          · rw [List.cons_head_tail hne]
            exact hX
      have hF1eq : ∑ X ∈ F1, phi b d hd X =
          ∑ p ∈ P, phi b d hd (p.1 :: p.2) := by
        rw [← himg]
        rw [Finset.sum_image]
        intro p _ q _ hpq
        exact Prod.ext (List.cons.inj hpq).1 (List.cons.inj hpq).2
      have hPle : ∑ p ∈ P, phi b d hd (p.1 :: p.2) ≤
          ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 := by
        have h1 : ∑ p ∈ P, phi b d hd (p.1 :: p.2) ≤
            ∑ p ∈ Finset.univ ×ˢ tails, phi b d hd (p.1 :: p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => phi_nonneg b d hd (p.1 :: p.2))
        have h2 : ∑ p ∈ Finset.univ ×ˢ tails, phi b d hd (p.1 :: p.2) =
            ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 := by
          apply Finset.sum_congr rfl
          intro p _
          rw [phi_cons b d _hb hd p.1 p.2]
        exact h1.trans_eq h2
      have hprod : ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 =
          (∑ a : Fin b, wt b d hd a) * ∑ Y ∈ tails, phi b d hd Y := by
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      rw [hF1eq]
      rw [hprod] at hPle
      have hwt : 0 ≤ ∑ a : Fin b, wt b d hd a := by
        apply Finset.sum_nonneg
        intro a _
        unfold wt
        split_ifs <;> positivity
      calc ∑ p ∈ P, phi b d hd (p.1 :: p.2)
          ≤ (∑ a : Fin b, wt b d hd a) * ∑ Y ∈ tails, phi b d hd Y := hPle
        _ ≤ (∑ a : Fin b, wt b d hd a) *
            ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t :=
          mul_le_mul_of_nonneg_left hIH hwt
        _ = (((b : ℝ) - 1 / 2) / b) *
            ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
          rw [hq]
    have htot : ∑ X ∈ F, phi b d hd X ≤
        1 + (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
      have h := hsplit
      rw [← h]
      linarith [hF0le, hF1le]
    have hgeom : 1 + (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t =
        ∑ t ∈ Finset.range (T + 2), (((b : ℝ) - 1 / 2) / b) ^ t := by
      conv_rhs => rw [Finset.sum_range_succ', pow_zero, add_comm]
      rw [Finset.mul_sum]
      apply congrArg (1 + ·)
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_succ]
      ring
    rw [hgeom] at htot
    exact htot

private theorem summable_stringWeight (b d k : ℕ) (hb : 1 < b) (hd : d < b) :
    Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
      (stringWeight b X.1).toReal) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hq0 : (0 : ℝ) ≤ ((b : ℝ) - 1 / 2) / b := by
    apply div_nonneg _ hbR.le
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hq1 : ((b : ℝ) - 1 / 2) / b < 1 := by
    rw [div_lt_one hbR]
    linarith
  have hgeom : Summable (fun t : ℕ => (((b : ℝ) - 1 / 2) / b) ^ t) :=
    summable_geometric_of_lt_one hq0 hq1
  have htsum : ∑' t : ℕ, (((b : ℝ) - 1 / 2) / b) ^ t = 2 * (b : ℝ) := by
    rw [tsum_geometric_of_lt_one hq0 hq1]
    have h1 : (1 : ℝ) - ((b : ℝ) - 1 / 2) / b = (1 / 2) / b := by
      field_simp
      ring
    rw [h1, inv_div]
    field_simp
  apply summable_of_sum_le (f := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
    (stringWeight b X.1).toReal) (c := (2 : ℝ) ^ k * (2 * b))
  · intro X
    exact ENNReal.toReal_nonneg
  · intro U
    set F := U.image (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} => X.1) with hF
    have hsumU : ∑ X ∈ U, (stringWeight b X.1).toReal =
        ∑ X ∈ F, (stringWeight b X).toReal := by
      rw [hF]
      exact (Finset.sum_image (s := U)
        (g := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} => X.1)
        (f := fun X : List (Fin b) => (stringWeight b X).toReal)
        (fun X _ Y _ hXY => Subtype.ext hXY)).symm
    rw [hsumU]
    have hterm : ∀ X ∈ F, (stringWeight b X).toReal =
        (2 : ℝ) ^ k * phi b d hd X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      unfold stringWeight phi
      rw [ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _), Y.2]
      have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc (b : ℝ) ^ (-(Y.1.length : ℤ))
          = (b : ℝ) ^ (-(Y.1.length : ℤ)) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by
            rw [h2, mul_one]
        _ = (2 : ℝ) ^ k * ((b : ℝ) ^ (-(Y.1.length : ℤ)) * (1 / 2 : ℝ) ^ k) := by
            ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set T := F.sup List.length with hT
    have hlen : ∀ X ∈ F, X.length ≤ T := fun X hX => Finset.le_sup hX
    have hbound := phi_bound T b d hb hd F hlen
    have hle1 : (2 : ℝ) ^ k * ∑ X ∈ F, phi b d hd X ≤
        (2 : ℝ) ^ k * ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    have hle2 : ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t ≤
        ∑' t : ℕ, (((b : ℝ) - 1 / 2) / b) ^ t :=
      hgeom.sum_le_tsum _ (fun t _ => by positivity)
    rw [htsum] at hle2
    have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    calc (2 : ℝ) ^ k * ∑ X ∈ F, phi b d hd X
        ≤ (2 : ℝ) ^ k * (2 * (b : ℝ)) :=
          hle1.trans (mul_le_mul_of_nonneg_left hle2 h2k)
      _ = (2 : ℝ) ^ k * (2 * (b : ℝ)) := rfl

private theorem foldl_stringValue (b : ℕ) :
    ∀ (Z : List (Fin b)) (m : ℕ),
      Z.foldl (fun n a => b * n + a.val) m =
        m * b ^ Z.length + Z.foldl (fun n a => b * n + a.val) 0 := by
  intro Z
  induction Z with
  | nil => intro m; simp
  | cons a Z ih =>
    intro m
    simp only [List.length_cons, List.foldl_cons, pow_succ', mul_zero, zero_add]
    rw [ih (b * m + a.val), ih a.val]
    ring

private theorem stringValue_append (b : ℕ) (A Z : List (Fin b)) :
    stringValue b (A ++ Z) = stringValue b A * b ^ Z.length + stringValue b Z := by
  unfold stringValue
  rw [List.foldl_append, foldl_stringValue]

private theorem stringValue_cons (b : ℕ) (a : Fin b) (X : List (Fin b)) :
    stringValue b (a :: X) = a.val * b ^ X.length + stringValue b X := by
  unfold stringValue
  simp only [List.foldl_cons]
  rw [foldl_stringValue]
  simp

private theorem stringValue_ofDigits (b : ℕ) (X : List (Fin b)) :
    stringValue b X = Nat.ofDigits b (X.reverse.map Fin.val) := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    rw [stringValue_cons, ih, List.reverse_cons, List.map_append, List.map_singleton,
      Nat.ofDigits_append]
    simp [List.length_map]
    ring

private theorem stringValue_lt (b : ℕ) (hb : 1 < b) (X : List (Fin b)) :
    stringValue b X < b ^ X.length := by
  rw [stringValue_ofDigits]
  have hlen : (X.reverse.map Fin.val).length = X.length := by simp
  rw [← hlen]
  exact Nat.ofDigits_lt_base_pow_length hb (fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact a.isLt)

private theorem count_map_val (b d : ℕ) (hd : d < b) (X : List (Fin b)) :
    (X.reverse.map Fin.val).count d = X.count ⟨d, hd⟩ := by
  calc (X.reverse.map Fin.val).count d = X.reverse.count ⟨d, hd⟩ :=
        List.count_map_of_injective X.reverse Fin.val Fin.val_injective ⟨d, hd⟩
    _ = X.count ⟨d, hd⟩ := List.count_reverse

private theorem ofDigits_eq_of_length_eq (b : ℕ) (hb : 1 < b) :
    ∀ (S R : List ℕ), (∀ x ∈ S, x < b) → (∀ x ∈ R, x < b) →
      S.length = R.length → Nat.ofDigits b S = Nat.ofDigits b R → S = R := by
  intro S
  induction S with
  | nil =>
    intro R _ _ hlen _
    exact (List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)).symm
  | cons s S ih =>
    intro R hS hR hlen hEq
    cases R with
    | nil => simp at hlen
    | cons r R =>
      have hs : s < b := hS s (by simp)
      have hr : r < b := hR r (by simp)
      have hsr : s = r := by
        have hmod : (Nat.ofDigits b (s :: S)) % b = s := by
          simp [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
        have hmod' : (Nat.ofDigits b (r :: R)) % b = r := by
          simp [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        rw [hEq] at hmod
        exact hmod.symm.trans hmod'
      have htail : Nat.ofDigits b S = Nat.ofDigits b R := by
        have h1 : s + b * Nat.ofDigits b S = r + b * Nat.ofDigits b R := by
          have := hEq
          simpa [Nat.ofDigits_cons] using this
        rw [hsr] at h1
        exact Nat.mul_left_cancel (by omega : 0 < b) (Nat.add_left_cancel h1)
      have hlen' : S.length = R.length := by
        simpa using hlen
      rw [hsr, ih R (fun x hx => hS x (by simp [hx])) (fun x hx => hR x (by simp [hx]))
        hlen' htail]

private theorem pmap_map_val (b : ℕ) :
    ∀ (L : List (Fin b)) (h : ∀ a ∈ L.map Fin.val, a < b),
      (L.map Fin.val).pmap (fun a (ha : a < b) => (⟨a, ha⟩ : Fin b)) h = L := by
  intro L
  induction L with
  | nil => intro h; simp
  | cons a L ih =>
    intro h
    simp only [List.map_cons, List.pmap_cons]
    rw [ih (fun x hx => h x (by simp [hx]))]

private theorem count_pmap (b d : ℕ) (hd : d < b) :
    ∀ (S : List ℕ) (h : ∀ a ∈ S, a < b),
      (S.pmap (fun a (ha : a < b) => (⟨a, ha⟩ : Fin b)) h).count ⟨d, hd⟩ =
        S.count d := by
  intro S
  induction S with
  | nil => intro h; simp
  | cons a S ih =>
    intro h
    rw [List.pmap_cons]
    by_cases ha0 : a = d
    · subst ha0
      rw [List.count_cons_self, List.count_cons_self, ih
        (fun x hx => h x (by simp [hx]))]
    · have hne : (⟨a, h a (by simp)⟩ : Fin b) ≠ ⟨d, hd⟩ := by
        simp only [ne_eq, Fin.ext_iff]
        exact ha0
      rw [List.count_cons_of_ne hne, List.count_cons_of_ne ha0, ih
        (fun x hx => h x (by simp [hx]))]

private noncomputable def prefixedValue (b n : ℕ) (X : List (Fin b)) : ℕ :=
  n * b ^ X.length + stringValue b X

private theorem prefixedValue_pos (b n : ℕ) (hb : 1 < b) (hn : 0 < n)
    (X : List (Fin b)) : 0 < prefixedValue b n X := by
  unfold prefixedValue
  have hB : 0 < b ^ X.length := pow_pos (Nat.zero_lt_of_lt hb) _
  exact Nat.lt_of_lt_of_le (Nat.mul_pos hn hB) (Nat.le_add_right _ _)

private theorem prefixedValue_digitCount (b d n : ℕ) (hb : 1 < b) (hd : d < b)
    (hn : 0 < n) (X : List (Fin b)) :
    digitCount b d (prefixedValue b n X) = digitCount b d n + X.count ⟨d, hd⟩ := by
  induction X using List.reverseRecOn with
  | nil =>
    simp [prefixedValue, stringValue, digitCount]
  | append_singleton Y a ih =>
    have hpos : 0 < prefixedValue b n Y := prefixedValue_pos b n hb hn Y
    have hstep : prefixedValue b n (Y ++ [a]) =
        a.val + b * prefixedValue b n Y := by
      unfold prefixedValue
      rw [List.length_append, List.length_singleton, pow_succ,
        stringValue_append]
      simp [stringValue]
      ring
    have hcount : (Y ++ [a]).count ⟨d, hd⟩ =
        Y.count ⟨d, hd⟩ + (if a = ⟨d, hd⟩ then 1 else 0) := by
      rw [List.count_append, List.count_singleton]
      by_cases ha : a = ⟨d, hd⟩
      · subst ha
        simp
      · have hbeq : ¬ ((a == ⟨d, hd⟩) = true) := by rwa [beq_iff_eq]
        simp [hbeq, ha]
    have hdig : digitCount b d (a.val + b * prefixedValue b n Y) =
        digitCount b d (prefixedValue b n Y) +
          (if a = ⟨d, hd⟩ then 1 else 0) := by
      unfold digitCount
      rw [Nat.digits_add b hb a.val (prefixedValue b n Y) a.isLt (Or.inr (ne_of_gt hpos))]
      by_cases ha : a = ⟨d, hd⟩
      · subst ha
        rw [List.count_cons_self]
        simp
      · have hne : a.val ≠ d := fun h => ha (Fin.ext h)
        rw [List.count_cons_of_ne hne]
        simp [ha]
    rw [hstep, hdig, ih, hcount, add_assoc]

private theorem prefixedValue_div (b n : ℕ) (hb : 1 < b)
    (X : List (Fin b)) :
    prefixedValue b n X / b ^ X.length = n := by
  have hv : stringValue b X < b ^ X.length := stringValue_lt b hb X
  have hB : 0 < b ^ X.length := pow_pos (Nat.zero_lt_of_lt hb) _
  apply Nat.div_eq_of_lt_le
  · unfold prefixedValue
    exact Nat.le_add_right _ _
  · have h2 : (n + 1) * b ^ X.length = n * b ^ X.length + b ^ X.length := by ring
    unfold prefixedValue
    omega

private theorem prefixedValue_length (b n : ℕ) (hb : 1 < b) (hn : 0 < n)
    (X : List (Fin b)) :
    integerLength b (prefixedValue b n X) = integerLength b n + X.length := by
  unfold integerLength
  set L := (Nat.digits b n).length with hL
  have hne : Nat.digits b n ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hLpos : 0 < L := by
    rw [hL]
    cases hdig : Nat.digits b n with
    | nil => exact absurd hdig hne
    | cons _ _ => simp
  have hnlt : n < b ^ L := by
    have h := (Nat.digits_length_le_iff hb n).mp (le_refl _)
    rw [← hL] at h
    exact h
  have hLle : b ^ (L - 1) ≤ n :=
    (Nat.lt_digits_length_iff hb n).mp (by omega)
  have hlt : prefixedValue b n X < b ^ (L + X.length) := by
    have hv : stringValue b X < b ^ X.length := stringValue_lt b hb X
    have hle : n + 1 ≤ b ^ L := hnlt
    have hmul : (n + 1) * b ^ X.length ≤ b ^ L * b ^ X.length :=
      Nat.mul_le_mul_right _ hle
    have hpow : b ^ L * b ^ X.length = b ^ (L + X.length) := (pow_add b L X.length).symm
    have h2 : (n + 1) * b ^ X.length = n * b ^ X.length + b ^ X.length := by ring
    unfold prefixedValue
    omega
  have hge : b ^ (L + X.length - 1) ≤ prefixedValue b n X := by
    have hpow : b ^ (L + X.length - 1) = b ^ (L - 1) * b ^ X.length := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    calc b ^ (L - 1) * b ^ X.length ≤ n * b ^ X.length :=
          Nat.mul_le_mul_right _ hLle
      _ ≤ prefixedValue b n X := by
          unfold prefixedValue
          exact Nat.le_add_right _ _
  have hle : (Nat.digits b (prefixedValue b n X)).length ≤ L + X.length := by
    exact (Nat.digits_length_le_iff hb _).mpr hlt
  have hgt : L + X.length - 1 < (Nat.digits b (prefixedValue b n X)).length := by
    exact (Nat.lt_digits_length_iff hb _).mpr hge
  omega

private noncomputable def paddedDigits (b n m : ℕ) : List ℕ :=
  Nat.digits b (m % b ^ (integerLength b m - integerLength b n)) ++
    List.replicate
      ((integerLength b m - integerLength b n) -
        (Nat.digits b (m % b ^ (integerLength b m - integerLength b n))).length) 0

private theorem paddedDigits_lt (b n m : ℕ) (hb : 1 < b) :
    ∀ a ∈ paddedDigits b n m, a < b := by
  intro a ha
  unfold paddedDigits at ha
  rcases List.mem_append.mp ha with h | h
  · exact Nat.digits_lt_base hb h
  · obtain ⟨-, rfl⟩ := List.mem_replicate.mp h
    exact Nat.zero_lt_of_lt hb

private noncomputable def inverseString (b n m : ℕ) (hb : 1 < b) : List (Fin b) :=
  ((paddedDigits b n m).pmap (fun a (ha : a < b) => (⟨a, ha⟩ : Fin b))
    (paddedDigits_lt b n m hb)).reverse

private theorem map_val_pmap (b : ℕ) :
    ∀ (S : List ℕ) (h : ∀ a ∈ S, a < b),
      (S.pmap (fun a (ha : a < b) => (⟨a, ha⟩ : Fin b)) h).map Fin.val = S := by
  intro S
  induction S with
  | nil => intro h; simp
  | cons a S ih =>
    intro h
    simp only [List.pmap_cons, List.map_cons]
    rw [ih (fun x hx => h x (by simp [hx]))]

private theorem inverseString_length (b n m : ℕ) (hb : 1 < b) :
    (inverseString b n m hb).length =
      integerLength b m - integerLength b n := by
  unfold inverseString
  rw [List.length_reverse, List.length_pmap]
  unfold paddedDigits
  rw [List.length_append, List.length_replicate]
  have hle : (Nat.digits b (m % b ^ (integerLength b m - integerLength b n))).length ≤
      integerLength b m - integerLength b n := by
    apply (Nat.digits_length_le_iff hb _).mpr
    exact Nat.mod_lt _ (pow_pos (Nat.zero_lt_of_lt hb) _)
  omega

private theorem inverseString_count (b d n m : ℕ) (hd : d < b) (hb : 1 < b) :
    (inverseString b n m hb).count ⟨d, hd⟩ = (paddedDigits b n m).count d := by
  unfold inverseString
  rw [List.count_reverse, count_pmap b d hd]

private theorem inverseString_value (b n m : ℕ) (hb : 1 < b) :
    stringValue b (inverseString b n m hb) =
      m % b ^ (integerLength b m - integerLength b n) := by
  rw [stringValue_ofDigits]
  unfold inverseString
  rw [List.reverse_reverse, map_val_pmap]
  unfold paddedDigits
  rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_replicate_zero]
  simp

private theorem digits_eq_paddedDigits_append (b n m : ℕ) (hb : 1 < b) (hn : 0 < n)
    (hlead : leadingDigits b (integerLength b n) m = n) :
    Nat.digits b m = paddedDigits b n m ++ Nat.digits b n := by
  set t := integerLength b m - integerLength b n with ht
  have hdiv : m / b ^ t = n := hlead
  have hmod : m % b ^ t + b ^ t * n = m := by
    have h := Nat.div_add_mod m (b ^ t)
    rw [hdiv] at h
    omega
  have hlen : (Nat.digits b (m % b ^ t)).length ≤ t := by
    apply (Nat.digits_length_le_iff hb _).mpr
    exact Nat.mod_lt _ (pow_pos (Nat.zero_lt_of_lt hb) _)
  have hdigits : Nat.digits b (m % b ^ t) ++
      List.replicate (t - (Nat.digits b (m % b ^ t)).length) 0 ++ Nat.digits b n =
        Nat.digits b (m % b ^ t + b ^ ((Nat.digits b (m % b ^ t)).length +
          (t - (Nat.digits b (m % b ^ t)).length)) * n) :=
    Nat.digits_append_zeroes_append_digits hb hn
  have hexp : (Nat.digits b (m % b ^ t)).length +
      (t - (Nat.digits b (m % b ^ t)).length) = t := by omega
  rw [hexp] at hdigits
  have hval : m % b ^ t + b ^ t * n = m := by omega
  rw [hval] at hdigits
  unfold paddedDigits
  rw [← hdigits]

private theorem inverseString_count_eq (b d n m k : ℕ) (hb : 1 < b) (hd : d < b)
    (hn : 0 < n)
    (hlead : leadingDigits b (integerLength b n) m = n)
    (hcount : digitCount b d m = digitCount b d n + k) :
    (inverseString b n m hb).count ⟨d, hd⟩ = k := by
  rw [inverseString_count]
  have hdig := digits_eq_paddedDigits_append b n m hb hn hlead
  unfold digitCount at hcount
  rw [hdig, List.count_append] at hcount
  omega

private noncomputable def stringEquiv (b d n k : ℕ) (hb : 1 < b) (hd : d < b) (hn : 0 < n) :
    {X : List (Fin b) // X.count ⟨d, hd⟩ = k} ≃
      {m : ℕ // 0 < m ∧ integerLength b n ≤ integerLength b m ∧
        leadingDigits b (integerLength b n) m = n ∧
        digitCount b d m = digitCount b d n + k} where
  toFun X :=
    ⟨prefixedValue b n X.1,
      prefixedValue_pos b n hb hn X.1,
      by rw [prefixedValue_length b n hb hn X.1]; exact Nat.le_add_right _ _,
      by
        unfold leadingDigits
        rw [prefixedValue_length b n hb hn X.1, Nat.add_sub_cancel_left,
          prefixedValue_div b n hb X.1],
      by rw [prefixedValue_digitCount b d n hb hd hn X.1, X.2]⟩
  invFun m :=
    ⟨inverseString b n m.1 hb,
      inverseString_count_eq b d n m.1 k hb hd hn m.2.2.2.1 m.2.2.2.2⟩
  left_inv X := by
    apply Subtype.ext
    change inverseString b n (prefixedValue b n X.1) hb = X.1
    set t := X.1.length with ht
    have hlen : integerLength b (prefixedValue b n X.1) - integerLength b n = t := by
      rw [prefixedValue_length b n hb hn X.1, Nat.add_sub_cancel_left]
    have hmod : prefixedValue b n X.1 % b ^ t = stringValue b X.1 := by
      have hv : stringValue b X.1 < b ^ t := stringValue_lt b hb X.1
      unfold prefixedValue
      rw [← ht, mul_comm n (b ^ t), Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
    have hpad : paddedDigits b n (prefixedValue b n X.1) = X.1.reverse.map Fin.val := by
      apply ofDigits_eq_of_length_eq b hb
      · intro x hx
        exact paddedDigits_lt b n (prefixedValue b n X.1) hb x hx
      · intro x hx
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
        exact a.isLt
      · unfold paddedDigits
        rw [List.length_append, List.length_replicate, hlen, hmod]
        have hle : (Nat.digits b (stringValue b X.1)).length ≤ t := by
          apply (Nat.digits_length_le_iff hb _).mpr
          exact stringValue_lt b hb X.1
        have hlenS : (X.1.reverse.map Fin.val).length = t := by simp [ht]
        omega
      · unfold paddedDigits
        rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_replicate_zero,
          hlen, hmod]
        simp [stringValue_ofDigits b X.1]
    have h' : ∀ a ∈ X.1.reverse.map Fin.val, a < b := fun a ha =>
      paddedDigits_lt b n (prefixedValue b n X.1) hb a (by rw [hpad]; exact ha)
    have hpm : (paddedDigits b n (prefixedValue b n X.1)).pmap
        (fun a (ha : a < b) => (⟨a, ha⟩ : Fin b))
        (paddedDigits_lt b n (prefixedValue b n X.1) hb) = X.1.reverse := by
      rw [← pmap_map_val b X.1.reverse h']
      congr 1
    unfold inverseString
    rw [hpm, List.reverse_reverse]
  right_inv m := by
    apply Subtype.ext
    change prefixedValue b n (inverseString b n m.1 hb) = m.1
    unfold prefixedValue
    rw [inverseString_length, inverseString_value]
    have hdiv : m.1 / b ^ (integerLength b m.1 - integerLength b n) = n := m.2.2.2.1
    have h := Nat.div_add_mod m.1 (b ^ (integerLength b m.1 - integerLength b n))
    rw [hdiv, mul_comm (b ^ (integerLength b m.1 - integerLength b n)) n] at h
    exact h

private theorem normalizedStringValue_mem_Ico (b : ℕ) (hb : 1 < b)
    (X : List (Fin b)) :
    normalizedStringValue b X ∈ Set.Ico (0 : ℝ) 1 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hB : (0 : ℝ) < (b : ℝ) ^ X.length := pow_pos hbR _
  constructor
  · unfold normalizedStringValue
    exact div_nonneg (Nat.cast_nonneg _) hB.le
  · unfold normalizedStringValue
    rw [div_lt_one hB]
    exact_mod_cast stringValue_lt b hb X

private theorem atom_eq (b n : ℕ) (hb : 1 < b) (hn : 0 < n)
    (X : List (Fin b)) :
    (stringWeight b X).toReal * (((n : ℝ) + normalizedStringValue b X)⁻¹) =
      ((prefixedValue b n X : ℝ))⁻¹ := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hBne : (b : ℝ) ^ X.length ≠ 0 := pow_ne_zero _ (ne_of_gt hbR)
  have hPpos : (0 : ℝ) < (prefixedValue b n X : ℝ) := by
    exact_mod_cast prefixedValue_pos b n hb hn X
  unfold stringWeight normalizedStringValue
  rw [ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _)]
  have hz : (b : ℝ) ^ (-(X.length : ℤ)) = ((b : ℝ) ^ X.length)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hz]
  have hvy : (n : ℝ) + (stringValue b X : ℝ) / (b : ℝ) ^ X.length =
      (prefixedValue b n X : ℝ) / (b : ℝ) ^ X.length := by
    rw [eq_div_iff hBne]
    unfold prefixedValue
    push_cast
    field_simp
  rw [hvy, inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hBne, one_mul]

private theorem hasSum_atom_integral (b d n k : ℕ) (hb : 1 < b) (hd : d < b)
    (hn : 0 < n) :
    HasSum (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
        ((prefixedValue b n X.1 : ℝ))⁻¹)
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd) := by
  have hmeas : irwinMeasure b d k hd =
      Measure.sum (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
        stringWeight b X.1 • Measure.dirac (normalizedStringValue b X.1)) := rfl
  have hsumm : Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
      (stringWeight b X.1).toReal *
        ‖(Set.Ico (0 : ℝ) 1).indicator (fun x : ℝ => ((n : ℝ) + x)⁻¹)
          (normalizedStringValue b X.1)‖) := by
    have hnonneg : ∀ X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k},
        0 ≤ (stringWeight b X.1).toReal *
          ‖(Set.Ico (0 : ℝ) 1).indicator (fun x : ℝ => ((n : ℝ) + x)⁻¹)
            (normalizedStringValue b X.1)‖ := fun X =>
      mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    have hle : ∀ X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k},
        (stringWeight b X.1).toReal *
          ‖(Set.Ico (0 : ℝ) 1).indicator (fun x : ℝ => ((n : ℝ) + x)⁻¹)
            (normalizedStringValue b X.1)‖ ≤
          (n : ℝ)⁻¹ * (stringWeight b X.1).toReal := by
      intro X
      have hy := normalizedStringValue_mem_Ico b hb X.1
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnn : (0 : ℝ) ≤ (n : ℝ) + normalizedStringValue b X.1 := by linarith [hy.1]
      rw [Set.indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnn)]
      have hle1 : ((n : ℝ) + normalizedStringValue b X.1)⁻¹ ≤ (n : ℝ)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hnR (by linarith [hy.1])
      calc (stringWeight b X.1).toReal * ((n : ℝ) + normalizedStringValue b X.1)⁻¹
          ≤ (stringWeight b X.1).toReal * (n : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left hle1 ENNReal.toReal_nonneg
        _ = (n : ℝ)⁻¹ * (stringWeight b X.1).toReal := mul_comm _ _
    have hmajor : Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
        (n : ℝ)⁻¹ * (stringWeight b X.1).toReal) :=
      (summable_stringWeight b d k hb hd).mul_left _
    exact Summable.of_nonneg_of_le hnonneg hle hmajor
  have hdirac := MeasureTheory.hasSum_integral_sum_dirac
    (f := (Set.Ico (0 : ℝ) 1).indicator (fun x : ℝ => ((n : ℝ) + x)⁻¹))
    (x := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
      normalizedStringValue b X.1)
    (c := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} => stringWeight b X.1)
    (fun X => ENNReal.ofReal_ne_top) hsumm
  rw [← MeasureTheory.integral_indicator measurableSet_Ico, hmeas]
  refine hdirac.congr_fun (fun X => ?_)
  rw [Set.indicator_of_mem (normalizedStringValue_mem_Ico b hb X.1), smul_eq_mul,
    atom_eq b n hb hn X.1]

end integral_eq_leadingReciprocal_hasSum

/-- **Prefix reciprocal sums as integrals against the Irwin measure.** Let $b > 1$ and $d < b$
be natural numbers, let $n > 0$ and $k$ be natural numbers, let $k(n)$ be the number of
occurrences of the digit $d$ in the base-$b$ representation of $n$, and let $\mu_k$ be the Irwin
measure of base $b$ and digit $d$ with index $k$. Then the family that assigns $1/m$ to each
positive integer $m$ whose base-$b$ representation begins with that of $n$ and contains exactly
$k(n) + k$ occurrences of $d$, and $0$ to every other natural number $m$, is summable with sum
$\int_{[0,1)} \frac{1}{n + x}\, d\mu_k(x)$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Proposition 4. -/
public theorem integral_eq_leadingReciprocal_hasSum
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (n k : ℕ) (hn : 0 < n) :
    HasSum (leadingReciprocalTerm b d (digitCount b d n + k) n)
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd) := by
  classical
  have hpref : HasSum
      (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
        leadingReciprocalTerm b d (digitCount b d n + k) n
          (integral_eq_leadingReciprocal_hasSum.prefixedValue b n X.1))
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd) := by
    refine (integral_eq_leadingReciprocal_hasSum.hasSum_atom_integral b d n k hb hd hn).congr_fun
      (fun X => ?_)
    have hP : 0 < integral_eq_leadingReciprocal_hasSum.prefixedValue b n X.1 ∧
        integerLength b n ≤
          integerLength b (integral_eq_leadingReciprocal_hasSum.prefixedValue b n X.1) ∧
        leadingDigits b (integerLength b n)
            (integral_eq_leadingReciprocal_hasSum.prefixedValue b n X.1) = n ∧
        digitCount b d (integral_eq_leadingReciprocal_hasSum.prefixedValue b n X.1) =
          digitCount b d n + k := by
      refine ⟨integral_eq_leadingReciprocal_hasSum.prefixedValue_pos b n hb hn X.1,
        ?_, ?_, ?_⟩
      · rw [integral_eq_leadingReciprocal_hasSum.prefixedValue_length b n hb hn X.1]
        exact Nat.le_add_right _ _
      · unfold leadingDigits
        rw [integral_eq_leadingReciprocal_hasSum.prefixedValue_length b n hb hn X.1,
          Nat.add_sub_cancel_left,
          integral_eq_leadingReciprocal_hasSum.prefixedValue_div b n hb X.1]
      · rw [integral_eq_leadingReciprocal_hasSum.prefixedValue_digitCount b d n hb hd hn X.1,
          X.2]
    unfold leadingReciprocalTerm
    split_ifs
    · rw [one_div]
  have hsub : HasSum
      (leadingReciprocalTerm b d (digitCount b d n + k) n ∘ Subtype.val)
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd) :=
    (Equiv.hasSum_iff
      (integral_eq_leadingReciprocal_hasSum.stringEquiv b d n k hb hd hn)).mp hpref
  have hsup : Function.support (leadingReciprocalTerm b d (digitCount b d n + k) n) ⊆
      {m : ℕ | 0 < m ∧ integerLength b n ≤ integerLength b m ∧
        leadingDigits b (integerLength b n) m = n ∧
        digitCount b d m = digitCount b d n + k} := by
    intro m hm
    have hne : leadingReciprocalTerm b d (digitCount b d n + k) n m ≠ 0 :=
      Function.mem_support.mp hm
    by_contra hP
    have hP' : ¬ (0 < m ∧ integerLength b n ≤ integerLength b m ∧
        leadingDigits b (integerLength b n) m = n ∧
        digitCount b d m = digitCount b d n + k) := hP
    exact hne (by simp [leadingReciprocalTerm, hP'])
  exact (hasSum_subtype_iff_of_support_subset hsup).mp hsub

end

end MetaMathlibExt
