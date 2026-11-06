/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual first-tetrad norm-eight vectors and their genuine codeword-sign changes. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual Xi-image of the genuine norm-eight coordinate frame. -/
def monsterCo1GeometryTetradVector : leechIntegral :=
  leechIntegralAction co1XiIsometry (leechCoordinateFrameLattice 0)

/-- The displayed source Xi numerator has the exact first-column entries used here. -/
theorem monsterCo1GeometryTetradXi_column : ∀ i : Fin 24,
    co1XiNumerator i 0 = if i.val < 4 then -1 else 0 := by
  decide +kernel

/-- The actual integral Xi-image is minus four in its first tetrad and zero elsewhere. -/
theorem monsterCo1GeometryTetradVector_coordinates (i : Fin 24) :
    monsterCo1GeometryTetradVector.val i = if i.val < 4 then -4 else 0 := by
  have hi := congrFun (co1Xi_integral_double (leechCoordinateFrameLattice 0)) i
  have he : (co1XiNumerator *ᵥ (leechCoordinateFrameLattice 0).val) i =
      if i.val < 4 then -8 else 0 := by
    simp only [leechCoordinateFrameLattice, leechCoordinateFrameVector, Matrix.mulVec,
      dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, monsterCo1GeometryTetradXi_column]
    split_ifs <;> norm_num
  rw [he] at hi
  change 2 * monsterCo1GeometryTetradVector.val i = _ at hi
  split_ifs at hi ⊢ <;> omega

/-- The sum of genuine coordinate frame vectors selected by the first tetrad's code bits. -/
def monsterCo1GeometryTetradFrameChange (d : golayCode) : leechIntegral :=
  ∑ j : Fin 4, (d.val (Fin.castAdd 20 j)).val • leechCoordinateFrameLattice (Fin.castAdd 20 j)

/-- This actual frame sum has its literal selected-coordinate entries. -/
theorem monsterCo1GeometryTetradFrameChange_coordinates (d : golayCode) (i : Fin 24) :
    (monsterCo1GeometryTetradFrameChange d).val i =
      if i.val < 4 then 8 * ((d.val i).val : ℤ) else 0 := by
  have hs : (monsterCo1GeometryTetradFrameChange d).val =
      ∑ j : Fin 4, (d.val (Fin.castAdd 20 j)).val •
        (leechCoordinateFrameLattice (Fin.castAdd 20 j)).val := by
    change leechIntegral.subtype (∑ j : Fin 4,
      (d.val (Fin.castAdd 20 j)).val • leechCoordinateFrameLattice (Fin.castAdd 20 j)) = _
    simp only [map_sum, map_nsmul]
    rfl
  rw [hs]
  simp only [Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_def,
    leechCoordinateFrameLattice,
    leechCoordinateFrameVector, Pi.single_apply, mul_ite, mul_zero]
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    have hij : Fin.castAdd 20 j = i := Fin.ext rfl
    have he (k : Fin 4) : i = Fin.castAdd 20 k ↔ k = j := by
      constructor
      · intro h
        exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h.symm)
      · intro h
        rw [h, hij]
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hi, hij]
    ring
  · have he (j : Fin 4) : i ≠ Fin.castAdd 20 j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    simp only [he, ite_false, Finset.sum_const_zero, hi]

/-- Every actual codeword sign changes this vector by exactly the selected genuine frame vectors. -/
theorem monsterCo1GeometryTetradVector_sign (d : golayCode) :
    leechIntegralAction (golaySignIsometry d) monsterCo1GeometryTetradVector =
      monsterCo1GeometryTetradVector + monsterCo1GeometryTetradFrameChange d := by
  apply Subtype.ext
  ext i
  rw [leechIntegralAction_golaySign]
  simp only [golayIntegerSign, Submodule.coe_add, Pi.add_apply,
    monsterCo1GeometryTetradVector_coordinates, monsterCo1GeometryTetradFrameChange_coordinates]
  have hc : d.val i = 0 ∨ d.val i = 1 := by
    have h := (d.val i).val_lt
    have hv : (d.val i).val = 0 ∨ (d.val i).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (ZMod.val_injective 2 (by simpa only [ZMod.val_zero, ZMod.val_one] using hv))
    · exact Or.inr (ZMod.val_injective 2 (by simpa only [ZMod.val_zero, ZMod.val_one] using hv))
  rcases hc with hc | hc
  all_goals simp only [hc, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  all_goals split_ifs <;> norm_num at *

/-- The binary scalar selecting the two possible source line points. -/
def monsterCo1GeometryTetradParity (d : golayCode) : ZMod 2 :=
  ∑ j : Fin 4, d.val (Fin.castAdd 20 j)

/-- Selected genuine frame vectors all reduce to the same actual base-point coordinate vector. -/
theorem monsterCo1GeometryTetradFrameChange_binary (d : golayCode) :
    leechHyperbolicCoordinates (leechReduction (monsterCo1GeometryTetradFrameChange d)) =
      monsterCo1GeometryTetradParity d • monsterCo1GeometryBasePoint.val := by
  simp only [monsterCo1GeometryTetradFrameChange, map_sum, map_nsmul,
    leechFrame_reduction_eq, monsterCo1GeometryBasePoint_value,
    ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  simp only [map_smul]
  rw [← Finset.sum_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
