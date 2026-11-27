/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import Mathlib.Order.Fin.Tuple

/-!
# A seven-pattern Wilf-equivalence for signed inversion sequences

We prove that a final barred weak maximum and a strictly increasing barred suffix give
equinumerous avoidance classes, by fixing the magnitude of the first bar.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0

private abbrev InversionWord (n : ℕ) := {f : Fin n → ℕ // ∀ i, f i ≤ i}

/-- The unbarred prefix before the final barred entry of magnitude `m`. -/
private abbrev Left (n m : ℕ) := {f : Fin n → ℕ // ∀ i, f i ≤ i ∧ f i ≤ m}

/-- Magnitudes at least `m` form a strictly rising suffix. -/
private def Rises {n : ℕ} (m : ℕ) (f : Fin n → ℕ) : Prop :=
  ∀ i j, i < j → m ≤ f i → f i < f j

/-- The unsigned word on the right, with the first barred magnitude fixed at `m`. -/
private abbrev Right (n m : ℕ) :=
  {f : Fin (n + 1) → ℕ // (∀ i, f i ≤ i) ∧ (∃ i, f i = m) ∧ Rises m f}

private theorem rises_snoc {n m x : ℕ} {f : Fin n → ℕ} (h : Rises m f)
    (hx : ∀ i, m ≤ f i → f i < x) : Rises m (Fin.snoc f x) := by
  intro i j hij hi
  cases j using Fin.lastCases with
  | last =>
    cases i using Fin.lastCases with
    | last => exact (lt_irrefl _ hij).elim
    | cast i => simpa using hx i (by simpa using hi)
  | cast j =>
    cases i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
    | cast i => simpa using h i j (Fin.castSucc_lt_castSucc_iff.mp hij) (by simpa using hi)

private def leftStep {n m : ℕ} (hm : m ≤ n) : Fin (m + 1) × Left n m ≃ Left (n + 1) m where
  toFun x := ⟨Fin.snoc x.2.val x.1.val, fun i ↦ Fin.lastCases
    (by simpa using ⟨(Nat.le_of_lt_succ x.1.isLt).trans hm, Nat.le_of_lt_succ x.1.isLt⟩)
    (fun j ↦ by simpa using x.2.property j) i⟩
  invFun f :=
    (⟨f.val (Fin.last n), Nat.lt_succ_of_le (f.property _).2⟩,
      ⟨Fin.init f.val, fun i ↦ f.property i.castSucc⟩)
  left_inv x := Prod.ext (Fin.ext (by simp)) (Subtype.ext (by simp))
  right_inv f := Subtype.ext (by simp)

private def lastEquiv (n : ℕ) : Left n n ≃ Right n n where
  toFun f := ⟨Fin.snoc f.val n,
    (fun i ↦ Fin.lastCases (by simp) (fun j ↦ by simpa using (f.property j).1) i),
    ⟨Fin.last n, by simp⟩,
    rises_snoc (fun i _ _ hi ↦ by have := (f.property i).1; omega)
      (fun i _ ↦ lt_of_le_of_lt (f.property i).1 i.isLt)⟩
  invFun f := ⟨Fin.init f.val, fun i ↦
    ⟨f.property.1 i.castSucc, (f.property.1 i.castSucc).trans (Nat.le_of_lt i.isLt)⟩⟩
  left_inv f := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by
    obtain ⟨i, hi⟩ := f.property.2.1
    have hi' : i = Fin.last n := Fin.ext (by have := f.property.1 i; simp; omega)
    rw [hi'] at hi
    simp [← hi])

private def rightSnoc {n m : ℕ} (f : Right n m) : Right (n + 1) m :=
  ⟨Fin.snoc f.val (n + 1),
    (fun i ↦ Fin.lastCases (by simp) (fun j ↦ by simpa using f.property.1 j) i),
    (by obtain ⟨i, hi⟩ := f.property.2.1; exact ⟨i.castSucc, by simpa using hi⟩),
    rises_snoc f.property.2.2 (fun i _ ↦ lt_of_le_of_lt (f.property.1 i) i.isLt)⟩

private def rightInit {n m : ℕ} (hm : m ≤ n) (f : Right (n + 1) m)
    (hlast : f.val (Fin.last (n + 1)) = n + 1) : Right n m :=
  ⟨Fin.init f.val, (fun i ↦ f.property.1 i.castSucc), by
    obtain ⟨i, hi⟩ := f.property.2.1
    refine Fin.lastCases ?_ (fun j ↦ ?_) i hi
    · intro h; omega
    · exact fun h ↦ ⟨j, h⟩,
    (fun i j hij ↦ f.property.2.2 i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij))⟩

private theorem rises_insert {n m : ℕ} {f : Fin n → ℕ} {p : Fin (n + 1)} {a : ℕ}
    (h : Rises m f) (ha : a < m) (hp : ∀ i, p.succAbove i < p → f i < m) :
    Rises m (p.insertNth a f) := by
  intro i j hij hi
  by_cases hip : i = p
  · subst i
    simp at hi
    omega
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hip
  rw [Fin.insertNth_apply_succAbove] at hi ⊢
  by_cases hjp : j = p
  · subst j
    exact (not_lt_of_ge hi (hp i hij)).elim
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hjp
  rw [Fin.insertNth_apply_succAbove]
  exact h i j ((Fin.strictMono_succAbove p).lt_iff_lt.mp hij) hi

private def rightInsert {n m : ℕ} (hm : m ≤ n) (a : Fin m)
    (f : Right n m) : Right (n + 1) m := by
  let p : Fin (n + 2) := ⟨m, by omega⟩
  refine ⟨p.insertNth a.val f.val, ?_, ?_, rises_insert f.property.2.2 a.isLt ?_⟩
  · intro i
    by_cases hi : i = p
    · subst i
      simp [p, Nat.le_of_lt a.isLt]
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Fin.insertNth_apply_succAbove]
    exact (f.property.1 j).trans (by unfold Fin.succAbove; split <;> simp)
  · obtain ⟨i, hi⟩ := f.property.2.1
    exact ⟨p.succAbove i, by simpa using hi⟩
  · intro i hi
    have hi' : i.castSucc < p := (Fin.succAbove_lt_iff_castSucc_lt p i).mp hi
    exact lt_of_le_of_lt (f.property.1 i) (Fin.lt_def.mp hi')

-- A rising suffix whose last entry is below the last index is below every one of its indices.
private theorem below_index {n m : ℕ} (f : Right n m) (hlast : f.val (Fin.last n) < n)
    (i : Fin (n + 1)) (hi : m ≤ f.val i) : f.val i < i.val := by
  refine Nat.decreasingInduction'
    (motive := fun k ↦ ∀ (hk : k < n + 1), m ≤ f.val ⟨k, hk⟩ → f.val ⟨k, hk⟩ < k)
    ?_ (Nat.le_of_lt_succ i.isLt) (fun _ _ ↦ hlast) i.isLt hi
  intro k hk _ ih hk' h
  have hg := f.property.2.2 ⟨k, hk'⟩ ⟨k + 1, by omega⟩ (Nat.lt_succ_self _) h
  exact lt_of_lt_of_le hg (Nat.le_of_lt_succ (ih (by omega) (h.trans hg.le)))

private def rightRemove {n m : ℕ} (hm : m ≤ n) (f : Right (n + 1) m)
    (hlast : f.val (Fin.last (n + 1)) < n + 1) : Fin m × Right n m := by
  let p : Fin (n + 2) := ⟨m, by omega⟩
  have hp : f.val p < m := lt_of_not_ge fun h ↦ not_lt_of_ge h (below_index f hlast p h)
  refine (⟨f.val p, hp⟩, ⟨p.removeNth f.val, ?_, ?_, ?_⟩)
  · intro i
    change f.val (p.succAbove i) ≤ i.val
    by_cases hi : i.castSucc < p
    · simpa [Fin.succAbove_of_castSucc_lt _ _ hi] using f.property.1 (p.succAbove i)
    have he := Fin.succAbove_of_le_castSucc p i (le_of_not_gt hi)
    by_cases h : m ≤ f.val (p.succAbove i)
    · have hb := below_index f hlast (p.succAbove i) h
      rw [he]
      rw [he] at hb
      exact Nat.le_of_lt_succ hb
    · exact le_trans (Nat.le_of_lt (lt_of_not_ge h)) (Fin.le_def.mp (le_of_not_gt hi))
  · obtain ⟨i, hi⟩ := f.property.2.1
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (show i ≠ p by rintro rfl; omega)
    exact ⟨j, hi⟩
  · exact fun i j hij ↦ f.property.2.2 _ _ (Fin.strictMono_succAbove p hij)

private theorem rightInsert_last {n m : ℕ} (hm : m ≤ n) (a : Fin m) (f : Right n m) :
    (rightInsert hm a f).val (Fin.last (n + 1)) = f.val (Fin.last n) := by
  let p : Fin (n + 2) := ⟨m, by omega⟩
  have hp : p ≠ Fin.last (n + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [p] at this
    omega
  change Fin.insertNth (α := fun _ ↦ ℕ) p a.val f.val (Fin.last (n + 1)) = _
  rw [← Fin.succAbove_ne_last_last hp, Fin.insertNth_apply_succAbove]

/-- Extend the word by a new largest bar or insert an unbarred entry at index `m`. -/
private noncomputable def rightStep {n m : ℕ} (hm : m ≤ n) :
    Fin (m + 1) × Right n m ≃ Right (n + 1) m where
  toFun x := if ha : x.1.val < m then rightInsert hm ⟨x.1.val, ha⟩ x.2 else rightSnoc x.2
  invFun f := if hlast : f.val (Fin.last (n + 1)) = n + 1 then
      (Fin.last m, rightInit hm f hlast)
    else
      let x := rightRemove hm f (lt_of_le_of_ne (f.property.1 _) hlast)
      (x.1.castSucc, x.2)
  left_inv := by
    rintro ⟨a, f⟩
    dsimp
    split_ifs with ha hlast hlast
    · rw [rightInsert_last] at hlast
      have := f.property.1 (Fin.last n)
      simp only [Fin.val_last] at this
      omega
    · exact Prod.ext (Fin.ext (by simp [rightRemove, rightInsert]))
        (Subtype.ext (by simp [rightRemove, rightInsert]))
    · exact Prod.ext (Fin.ext (by have := a.isLt; simp; omega))
        (Subtype.ext (by simp [rightInit, rightSnoc]))
    · exact (hlast (by simp [rightSnoc])).elim
  right_inv := by
    intro f
    dsimp
    split_ifs with hlast ha ha
    · exact (Nat.lt_irrefl m ha).elim
    · apply Subtype.ext
      change Fin.snoc (Fin.init f.val) (n + 1) = f.val
      exact (congrArg (Fin.snoc (Fin.init f.val)) hlast.symm).trans (Fin.snoc_init_self _)
    · exact Subtype.ext (Fin.insertNth_self_removeNth _ _)
    · exact (ha (rightRemove hm f (lt_of_le_of_ne (f.property.1 _) hlast)).1.isLt).elim

private noncomputable def barredEquiv {n m : ℕ} (hm : m ≤ n) : Left n m ≃ Right n m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
    exact lastEquiv 0
  | succ n ih =>
    by_cases h : m = n + 1
    · subst m
      exact lastEquiv (n + 1)
    · have h' : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hm h)
      exact (leftStep h').symm.trans (((Equiv.refl _).prodCongr (ih h')).trans (rightStep h'))

private abbrev patterns (right : Bool) : Finset SignedPattern2 :=
  if right then
    {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
      ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}
  else
    {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
      ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

private def PairRule (right : Bool) (x y : ℕ × Bool) : Prop :=
  if right then (x.2 = true → y.2 = true) ∧ (y.2 = true → x.1 < y.1)
  else x.2 = false ∧ (y.2 = true → x.1 ≤ y.1)

private theorem avoids_iff {n : ℕ} (right : Bool) (e : Fin n → ℕ × Bool) :
    (∀ p ∈ patterns right, ¬ SignedInvSeqContains e p) ↔
      ∀ i j, i < j → PairRule right (e i) (e j) := by
  have pair (x y : ℕ × Bool) :
      ⟨compare x.1 y.1, x.2, y.2⟩ ∉ patterns right ↔ PairRule right x y := by
    cases right <;> cases hx : x.2 <;> cases hy : y.2 <;>
      simp [patterns, PairRule, SignedPattern2.mk.injEq, hx, hy, compare_lt_iff_lt,
        compare_gt_iff_gt] <;> omega
  constructor
  · intro h i j hij
    exact (pair _ _).mp fun hp ↦ h _ hp ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hp ⟨i, j, hij, ho, hi, hj⟩
    exact (pair _ _).mpr (h i j hij) (by simpa only [ho, hi, hj] using hp)

private abbrev Avoiders (right : Bool) (n : ℕ) :=
  {e : Fin n → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ patterns right, ¬ SignedInvSeqContains e p}

private abbrev HasBar {n : ℕ} (e : Fin n → ℕ × Bool) : Prop := ∃ i, (e i).2 = true

private def plainEquiv (right : Bool) (n : ℕ) :
    InversionWord n ≃ {e : Avoiders right n // ¬ HasBar e.val} where
  toFun f := ⟨⟨fun i ↦ (f.val i, false), f.property, (avoids_iff _ _).mpr
    (by cases right <;> simp [PairRule])⟩, by simp⟩
  invFun e := ⟨fun i ↦ (e.val.val i).1, e.val.property.1⟩
  left_inv _ := rfl
  right_inv e := Subtype.ext (Subtype.ext (funext fun i ↦ Prod.ext rfl
    (Bool.eq_false_iff.mpr (fun hi ↦ e.property ⟨i, hi⟩)).symm))

private def signLast {n : ℕ} (m : Fin (n + 1)) (f : Left n m.val) :
    {e : Avoiders false (n + 1) // HasBar e.val} := by
  let e := Fin.snoc (α := fun _ ↦ ℕ × Bool) (fun i ↦ (f.val i, false)) (m.val, true)
  refine ⟨⟨e, ?_, (avoids_iff _ _).mpr ?_⟩, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simpa [e] using Nat.le_of_lt_succ m.isLt
    | cast j => simpa [e] using (f.property j).1
  · intro i j hij
    cases i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
    | cast i =>
      cases j using Fin.lastCases with
      | last => simpa [e, PairRule] using (f.property i).2
      | cast j => simp [e, PairRule]
  · exact ⟨Fin.last n, by simp [e]⟩

private theorem last_is_barred {n : ℕ} {e : Avoiders false (n + 1)} (he : HasBar e.val) :
    (e.val (Fin.last n)).2 = true := by
  have h := (avoids_iff _ _).mp e.property.2
  obtain ⟨k, hk⟩ := he
  have he : k = Fin.last n := eq_of_le_of_not_lt (Fin.le_last _) fun hlt ↦
    Bool.noConfusion (hk.symm.trans (h k _ hlt).1)
  exact he ▸ hk

private def leftEquiv (n : ℕ) :
    (Σ m : Fin (n + 1), Left n m.val) ≃ {e : Avoiders false (n + 1) // HasBar e.val} where
  toFun u := signLast u.1 u.2
  invFun e := by
    have h := (avoids_iff _ _).mp e.val.property.2
    let m := (e.val.val (Fin.last n)).1
    have hlast := last_is_barred e.property
    exact ⟨⟨m, Nat.lt_succ_of_le (e.val.property.1 _)⟩,
      ⟨fun i ↦ (e.val.val i.castSucc).1, fun i ↦
        ⟨e.val.property.1 i.castSucc, (h _ _ i.castSucc_lt_last).2 hlast⟩⟩⟩
  left_inv := by
    rintro ⟨m, f⟩
    apply Sigma.subtype_ext
    · exact Fin.ext (by simp [signLast])
    · funext i
      simp [signLast]
  right_inv := by
    intro e
    have h := (avoids_iff _ _).mp e.val.property.2
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i using Fin.lastCases with
    | last => exact Prod.ext (by simp [signLast]) (by simpa [signLast] using
        (last_is_barred e.property).symm)
    | cast i =>
      have hi := (h _ _ i.castSucc_lt_last).1
      exact Prod.ext (by simp [signLast]) (by simpa [signLast] using hi.symm)

private def signSuffix {n : ℕ} (m : Fin (n + 1)) (f : Right n m.val) :
    {e : Avoiders true (n + 1) // HasBar e.val} := by
  let e (i : Fin (n + 1)) := (f.val i, decide (m.val ≤ f.val i))
  refine ⟨⟨e, f.property.1, (avoids_iff _ _).mpr ?_⟩, ?_⟩
  · intro i j hij
    simp only [PairRule, e, ite_true, decide_eq_true_eq]
    constructor
    · intro hi
      exact hi.trans (f.property.2.2 i j hij hi).le
    · intro hj
      by_cases hi : m.val ≤ f.val i
      · exact f.property.2.2 i j hij hi
      · exact (lt_of_not_ge hi).trans_le hj
  · obtain ⟨i, hi⟩ := f.property.2.1
    exact ⟨i, by simp [e, hi]⟩

private noncomputable def rightEquiv (n : ℕ) :
    (Σ m : Fin (n + 1), Right n m.val) ≃ {e : Avoiders true (n + 1) // HasBar e.val} := by
  apply Equiv.ofBijective (fun u ↦ signSuffix u.1 u.2)
  constructor
  · rintro ⟨m, f⟩ ⟨m', f'⟩ he
    have he' (i : Fin (n + 1)) :
        (f.val i, decide (m.val ≤ f.val i)) = (f'.val i, decide (m'.val ≤ f'.val i)) :=
      congrArg (fun e : {e : Avoiders true (n + 1) // HasBar e.val} ↦ e.val.val i) he
    have hval : f.val = f'.val := funext fun i ↦ congrArg Prod.fst (he' i)
    have hmle : m.val ≤ m'.val := by
      obtain ⟨i, hi⟩ := f'.property.2.1
      have hsign := congrArg Prod.snd (he' i)
      simpa [hval, hi] using hsign
    have hmle' : m'.val ≤ m.val := by
      obtain ⟨i, hi⟩ := f.property.2.1
      have hsign := congrArg Prod.snd (he' i).symm
      simpa [← hval, hi] using hsign
    exact Sigma.subtype_ext (Fin.ext (hmle.antisymm hmle')) hval
  · intro e
    have h := (avoids_iff _ _).mp e.val.property.2
    obtain ⟨k, hk, hmin⟩ := wellFounded_lt.has_min {i | (e.val.val i).2 = true} e.property
    change (e.val.val k).2 = true at hk
    let f (i : Fin (n + 1)) := (e.val.val i).1
    have hsign (i : Fin (n + 1)) : (e.val.val i).2 = true ↔ f k ≤ f i := by
      rcases lt_trichotomy i k with hik | rfl | hki
      · exact ⟨fun hi ↦ (hmin i hi hik).elim,
          fun hki ↦ (not_lt_of_ge hki ((h i k hik).2 hk)).elim⟩
      · simp [hk]
      · exact ⟨fun hi ↦ ((h k i hki).2 hi).le, fun _ ↦ (h k i hki).1 hk⟩
    refine ⟨⟨⟨f k, (e.val.property.1 k).trans_lt k.isLt⟩,
      ⟨f, e.val.property.1, ⟨k, rfl⟩, fun i j hij hi ↦
        (h i j hij).2 ((h i j hij).1 ((hsign i).mpr hi))⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Prod.ext rfl ?_
    change decide (f k ≤ f i) = (e.val.val i).2
    cases hi : (e.val.val i).2 <;> simp [hi, ← hsign]

private noncomputable def avoidersEquiv (n : ℕ) : Avoiders false (n + 1) ≃ Avoiders true (n + 1) :=
  haveI := Classical.propDecidable
  (Equiv.sumCompl (fun e : Avoiders false (n + 1) ↦ HasBar e.val)).symm.trans <|
    (Equiv.sumCongr
      ((leftEquiv n).symm.trans <| (Equiv.sigmaCongrRight fun m ↦ barredEquiv
          (Nat.le_of_lt_succ m.isLt)).trans (rightEquiv n))
      ((plainEquiv false _).symm.trans (plainEquiv true _))).trans <|
    Equiv.sumCompl (fun e : Avoiders true (n + 1) ↦ HasBar e.val)

end signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0

open signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0 in
/-- **Mansour–Safadi Theorem 18: a Wilf-equivalence of seven-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar0\bar0, \bar00, \bar01, 1\bar0\} \sim
\{\bar1\bar0, \bar10, \bar0\bar0, \bar00, \bar01, 0\bar0, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 18 (`integers-2026-A74-thm-18`). -/
public theorem signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} := by
  funext n
  cases n with
  | zero => simp only [signedInvAvoidCount_zero]
  | succ n => exact Nat.card_congr (avoidersEquiv n)

end MetaMathlibExt
