/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Actual short-vector coordinate shapes and monomial normalization. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The positive pair vector used as a common target. -/
def leechShortPairTarget : Fin 24 → ℤ := fun i => if i = 0 ∨ i = 1 then 4 else 0

/-- An injective tuple of fewer than 24 positions extends by one position. -/
theorem leechShort_extend_tuple {n : ℕ} (hn : n < 24) (a : Fin n → Fin 24)
    (ha : Function.Injective a) :
    ∃ b : Fin (n + 1) → Fin 24, Function.Injective b ∧ ∀ j, b j.castSucc = a j := by
  classical
  have hnonsurj : ¬ Function.Surjective a := by
    intro hs
    have hc := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Set.range a := by
    simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnonsurj
  exact ⟨Fin.snoc a v, Fin.snoc_injective_of_injective ha hv, fun j => by simp⟩

/-- Any selected four absolute coordinates can be assigned their desired signs
at the first tetrad by the actual monomial generators. -/
theorem leechShort_monomial_four (u : leechIntegral) (f : Fin 4 → Fin 24)
    (hf : Function.Injective f) (b : Fin 4 → ℤ)
    (habs : ∀ j, (u.val (f j)).natAbs = (b j).natAbs) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) = b j := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive f
    (fun j : Fin 4 => Fin.castAdd 20 j) hf (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j)) b habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
      (golayPermutationIsometry_mem_concrete p), ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hp j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

/-- Two coordinates already exhaust the square sum of a short pair vector. -/
theorem leechShort_eq_pair_of_first (u : Fin 24 → ℤ)
    (hs : leechSquareSum u = 32) (h0 : u 0 = 4) (h1 : u 1 = 4) :
    u = leechShortPairTarget := by
  have hr : ∑ i : Fin 22, u i.succ.succ ^ 2 = 0 := by
    change (∑ i : Fin 24, u i ^ 2) = 32 at hs
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, h0] at hs
    change 4 ^ 2 + (u 1 ^ 2 + ∑ i : Fin 22, u i.succ.succ ^ 2) = 32 at hs
    rw [h1] at hs
    linarith
  have hz (i : Fin 22) : u i.succ.succ = 0 := by
    have hb := Finset.single_le_sum (fun j _ => sq_nonneg (u j.succ.succ))
      (Finset.mem_univ i)
    rw [hr] at hb
    nlinarith
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simpa [leechShortPairTarget] using h0
  · simpa [leechShortPairTarget] using h1
  · have hk : k.succ.succ ≠ (1 : Fin 24) := by
      intro h
      have he := congrArg Fin.val h
      change k.val + 1 + 1 = 1 at he
      omega
    simpa [leechShortPairTarget, Fin.succ_ne_zero, hk] using hz k

/-- At norm 32, two absolute-four positions can be normalized to the positive pair. -/
theorem leechShort_pair_reduction (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (i j : Fin 24) (hij : i ≠ j) (hi : (u.val i).natAbs = 4)
    (hj : (u.val j).natAbs = 4) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  let a : Fin 2 → Fin 24 := ![i, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  obtain ⟨b, hb, hba⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨f, hf, hfb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  have hfi : f 0 = i := (hfb 0).trans (hba 0)
  have hfj : f 1 = j := (hfb 1).trans (hba 1)
  obtain ⟨e, he, hrow⟩ := leechShort_monomial_four u f hf
    ![4, 4, u.val (f 2), u.val (f 3)] (by
      intro k
      fin_cases k <;> simp [hfi, hfj, hi, hj])
  exact ⟨e, he, leechShort_eq_pair_of_first _
    (by rw [leechIntegralAction_squareSum, hs]) (hrow 0) (hrow 1)⟩

/-- Actual common odd parity supplies a first row `(3,1,1,1)`. -/
theorem leechShort_odd_preparation (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (ho : ∀ i, Odd (u.val i)) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) = ![3, 1, 1, 1] j := by
  obtain ⟨i, hi, hother⟩ := odd_short_coordinates u.val hs ho
  obtain ⟨a, ha, hia⟩ := leechShort_extend_tuple (by decide : 1 < 24)
    (fun _ : Fin 1 => i) (by intro x y _; exact Subsingleton.elim x y)
  obtain ⟨b, hb, hba⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨f, hf, hfb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  have hfi : f 0 = i := (hfb 0).trans ((hba 0).trans (hia 0))
  apply leechShort_monomial_four u f hf ![3, 1, 1, 1]
  intro j
  by_cases hj : j = 0
  · subst j
    rcases hi with hi | hi <;> simp [hfi, hi]
  · have hji : f j ≠ i := by
      intro h
      exact hj (hf (h.trans hfi.symm))
    rcases hother (f j) hji with h | h <;> fin_cases j <;> simp_all

/-- The even norm-32 branch is a pair or a genuine octad; a zero coordinate
rules out the odd branch. -/
theorem leechShort_even_shapes (u : leechIntegral) (hs : leechSquareSum u.val = 32)
    (z : Fin 24) (hz : u.val z = 0) :
    (∃ i j : Fin 24, i ≠ j ∧ (u.val i).natAbs = 4 ∧ (u.val j).natAbs = 4) ∨
      (∃ c : Fin 24 → ZMod 2, c ∈ golayCode ∧ (∑ i, (c i).val) = 8 ∧
        ∀ i, u.val i ^ 2 = 4 * (c i).val) := by
  obtain ⟨m, hm, c, hc, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hm0 : m = 0 := by
    rcases hm with hm | hm
    · exact hm
    · have hh := hr z
      rw [hz, hm] at hh
      have hv : (c z).val = 0 ∨ (c z).val = 1 := by have h := ZMod.val_lt (c z); omega
      rcases hv with hv | hv
      · norm_num [hv] at hh
        exact False.elim ((by decide : (0 : ZMod 4) ≠ 1) hh)
      · norm_num [hv] at hh
        exact False.elim ((by decide : (0 : ZMod 4) ≠ 3) hh)
  subst m
  have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by simpa using hr
  have hb := leechEvenCode_square_lower u.val c hr0
  have hw := golayCode_weights c hc
  have hweight : (∑ i, (c i).val) = 0 ∨ (∑ i, (c i).val) = 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [hs] at hb
    omega
  rcases hweight with hw | hw
  · have hc0 : c = 0 := by
      funext i
      apply (ZMod.val_eq_zero _).mp
      have hci := Finset.single_le_sum (fun j _ => Nat.zero_le (c j).val) (Finset.mem_univ i)
      omega
    have hf (i : Fin 24) : 4 ∣ u.val i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      simpa [hc0] using hr0 i
    obtain ⟨s, p, hp⟩ := four_short_pair u.val hs hf
    let i := (griessCoordinatePair p).1
    let j := (griessCoordinatePair p).2
    have hij : i ≠ j := griessCoordinatePair_ne p
    left
    refine ⟨i, j, hij, ?_, ?_⟩ <;>
      rcases hp with hp | hp <;> fin_cases s <;>
      simp [hp, griessShortIntegral, i, j, hij, Ne.symm hij]
  · exact Or.inr ⟨c, hc, hw, leechEvenCode_short_equality u.val c hs hw hr0⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
