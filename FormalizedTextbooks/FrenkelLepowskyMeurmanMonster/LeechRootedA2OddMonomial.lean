/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PairMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! Actual root-line-preserving monomial normalization of neighboring odd short vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The integral sign attached to an actual binary Golay coordinate. -/
def leechRootedA2CodeSign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- Binary sign cancellation retains the exact physical sign. -/
theorem leechRootedA2CodeSign_cancel (a b : ZMod 2) :
    leechRootedA2CodeSign (a + b) * leechRootedA2CodeSign a = leechRootedA2CodeSign b := by
  have h : ∀ a b : ZMod 2,
      leechRootedA2CodeSign (a + b) * leechRootedA2CodeSign a = leechRootedA2CodeSign b := by
    decide +kernel
  exact h a b

/-- A fixed genuine Golay word with opposite bits at the two root coordinates. -/
def leechRootedA2OddTargetCode : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 3072), ⟨_, rfl⟩⟩

/-- Both target root signs are certified against the original encoder. -/
theorem leechRootedA2OddTargetCode_root :
    leechRootedA2OddTargetCode.val 0 = 1 ∧ leechRootedA2OddTargetCode.val 1 = 0 := by
  decide +kernel

/-- The common actual odd target has its exceptional coordinate at0. -/
def leechRootedA2PositiveOdd : Fin 24 → ℤ := fun i =>
  leechRootedA2CodeSign (leechRootedA2OddTargetCode.val i) * (if i = 0 then -3 else 1)

/-- The two root coordinates can be permuted to put the odd exception at0. -/
theorem leechRootedA2Odd_permutation (j : Fin 24) (hj : j = 0 ∨ j = 1) :
    ∃ p : golayAutomorphismSubgroup, p.val j = 0 ∧
      ((p.val 0 = 0 ∧ p.val 1 = 1) ∨ (p.val 0 = 1 ∧ p.val 1 = 0)) := by
  rcases hj with rfl | rfl
  · exact ⟨1, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · let a : Fin 3 → Fin 24 := ![0, 1, 2]
    let b : Fin 3 → Fin 24 := ![1, 0, 2]
    have ha : Function.Injective a := by decide +kernel
    have hb : Function.Injective b := by decide +kernel
    obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
    exact ⟨p, hp 1, Or.inr ⟨hp 0, hp 1⟩⟩

/-- The source encoder's integral signs agree with its actual binary coordinates. -/
theorem leechRootedA2Odd_encoder_sign (d : Fin 2048) (i : Fin 24) :
    (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) =
      leechRootedA2CodeSign (golayEncoder (golayLabelCoefficients
        (⟨d.val, by omega⟩ : Fin 4096)) i) := by
  have he := golayLabelEncoder_match (⟨d.val, by omega⟩ : Fin 4096) i
  have hz : golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) i = 0 ↔
      (golayEncodedMask d.val).testBit i.val = false := by
    rw [← ZMod.val_eq_zero, he]
    change (if (golayEncodedMask d.val).testBit i.val then 1 else 0) = 0 ↔ _
    cases (golayEncodedMask d.val).testBit i.val <;> decide
  simp only [leechRootedA2CodeSign, hz]
  cases (golayEncodedMask d.val).testBit i.val <;> rfl

/-- Opposite original odd root bits remain opposite after encoding. -/
theorem leechRootedA2Odd_encoder_root_ne (d : Fin 2048)
    (h : (golayEncodedMask d.val).testBit 0 ≠ (golayEncodedMask d.val).testBit 1) :
    golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) 0 ≠
      golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) 1 := by
  intro he
  have hv := congrArg ZMod.val he
  rw [golayLabelEncoder_match, golayLabelEncoder_match] at hv
  change (if (golayEncodedMask d.val).testBit 0 then 1 else 0) =
    (if (golayEncodedMask d.val).testBit 1 then 1 else 0) at hv
  cases h0 : (golayEncodedMask d.val).testBit 0 <;>
    cases h1 : (golayEncodedMask d.val).testBit 1 <;> simp_all

/-- Every actual neighboring odd short vector reaches the common target preserving root line. -/
theorem leechRootedA2Odd_monomial_reduction (d : Fin 2048) (j : Fin 24)
    (hr : leechRootedA2NeighborPredicate (Sum.inr (Sum.inr (d, j)))) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inr (Sum.inr (d, j))))).val =
        leechRootedA2PositiveOdd := by
  have hh := (leechRootedA2Odd_neighbor_iff d j).mp hr
  obtain ⟨p, hpj, hpp⟩ := leechRootedA2Odd_permutation j hh.2
  let c : golayCode :=
    ⟨golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)), ⟨_, rfl⟩⟩
  let cp : golayCode := golayCodePermutation p c
  have hc : c.val 0 ≠ c.val 1 := leechRootedA2Odd_encoder_root_ne d hh.1
  have hcp : cp.val 0 ≠ cp.val 1 := by
    rcases hpp with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩
    · have hs0 : p.val.symm 0 = 0 := by rw [p.val.symm_apply_eq]; exact hp0.symm
      have hs1 : p.val.symm 1 = 1 := by rw [p.val.symm_apply_eq]; exact hp1.symm
      change c.val (p.val.symm 0) ≠ c.val (p.val.symm 1)
      rwa [hs0, hs1]
    · have hs0 : p.val.symm 0 = 1 := by rw [p.val.symm_apply_eq]; exact hp1.symm
      have hs1 : p.val.symm 1 = 0 := by rw [p.val.symm_apply_eq]; exact hp0.symm
      change c.val (p.val.symm 0) ≠ c.val (p.val.symm 1)
      rw [hs0, hs1]
      exact hc.symm
  let signs : golayCode := cp + leechRootedA2OddTargetCode
  have hsigns : signs.val 0 = signs.val 1 := by
    change cp.val 0 + leechRootedA2OddTargetCode.val 0 =
      cp.val 1 + leechRootedA2OddTargetCode.val 1
    rw [leechRootedA2OddTargetCode_root.1, leechRootedA2OddTargetCode_root.2, add_zero]
    have hb : ∀ a b : ZMod 2, a ≠ b → a + 1 = b := by decide +kernel
    exact hb _ _ hcp
  have hpr : leechIntegralAction (golayPermutationIsometry p) leechRootedA2Root =
      leechRootedA2Root := by
    rcases hpp with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩
    · exact leechRootedA2Root_permutation p hp0 hp1
    · exact leechRootedA2Root_permutation_swap p hp0 hp1
  refine ⟨golaySignIsometry signs * golayPermutationIsometry p, ⟨signs, p, rfl⟩,
    leechRootedA2PreservesRootLine_mul _ _ (leechRootedA2Root_sign signs hsigns)
      (Or.inl hpr), ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  funext i
  have hpi : p.val.symm i = j ↔ i = 0 := by rw [p.val.symm_apply_eq, hpj]
  have hv : golayIntegerPermute p.val
      (griessShortLatticeVector (Sum.inr (Sum.inr (d, j)))).val i =
        leechRootedA2CodeSign (cp.val i) * (if i = 0 then -3 else 1) := by
    simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
      leechRootedA2Odd_encoder_sign, hpi]
    rfl
  change (if signs.val i = 0 then
      golayIntegerPermute p.val (griessShortLatticeVector (Sum.inr (Sum.inr (d, j)))).val i
    else -golayIntegerPermute p.val
      (griessShortLatticeVector (Sum.inr (Sum.inr (d, j)))).val i) = _
  rw [hv]
  have hs : (if signs.val i = 0 then
        leechRootedA2CodeSign (cp.val i) * (if i = 0 then (-3 : ℤ) else 1)
      else -(leechRootedA2CodeSign (cp.val i) * (if i = 0 then (-3 : ℤ) else 1))) =
      leechRootedA2CodeSign (signs.val i) * leechRootedA2CodeSign (cp.val i) *
        (if i = 0 then -3 else 1) := by
    by_cases hsi : signs.val i = 0 <;>
      simp only [leechRootedA2CodeSign, hsi, ite_true, ite_false] <;> ring
  rw [hs]
  change leechRootedA2CodeSign (cp.val i + leechRootedA2OddTargetCode.val i) *
    leechRootedA2CodeSign (cp.val i) * (if i = 0 then (-3 : ℤ) else 1) = _
  rw [leechRootedA2CodeSign_cancel]
  rfl

/-- The positive odd target is the negative of an original preferred short representative. -/
theorem leechRootedA2PositiveOdd_actual_short :
    leechRootedA2PositiveOdd = -griessShortIntegral (Sum.inr (Sum.inr (1024, 0))) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
