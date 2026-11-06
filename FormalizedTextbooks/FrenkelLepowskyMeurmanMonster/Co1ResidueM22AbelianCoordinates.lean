/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22LinearReduction
public import Mathlib.Algebra.BigOperators.Fin

/-! The eleven selected original point images evaluate every certified point coordinate row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem filter_sum {I V : Type*} [AddCommMonoid V]
    (p : I → Bool) (f : I → V) (row : List I) :
    ((row.filter p).map f).sum = (row.map (fun i => if p i then f i else 0)).sum := by
  induction row with
  | nil => simp
  | cons a row ih =>
    cases ha : p a <;> simp [ha, ih]

/-- The linear evaluation of the eleven selected original point images. -/
def co1ResidueM22AbelianCoordinates {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (phi : Co1ResidueM22Point 0 1 → V) : (Fin 11 → ZMod 2) →ₗ[ZMod 2] V :=
  (Pi.basisFun (ZMod 2) (Fin 11)).constr (ZMod 2)
    (fun k => phi (co1ResidueM22FinitePoint (co1ResidueM22LinearBasis k)))

/-- The original hexad relations make the linear evaluation agree with
every original point image. -/
theorem co1ResidueM22AbelianCoordinates_point {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (phi : Co1ResidueM22Point 0 1 → V)
    (hline : ∀ s t u, co1ResidueM22Line 0 1 s t u → phi s + phi t + phi u = 0)
    (i : Fin 231) :
    co1ResidueM22AbelianCoordinates phi
        (monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)) =
      phi (co1ResidueM22FinitePoint i) := by
  rw [co1ResidueM22Linear_point_reduction phi hline i]
  simp only [co1ResidueM22AbelianCoordinates, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, monsterCo1GeometryBinaryMaskDecode]
  simp only [ite_smul, one_smul, zero_smul]
  rw [Fin.sum_univ_def]
  simp only [co1ResidueM22LinearBasisRow, List.map_map]
  exact (filter_sum _ _ _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
