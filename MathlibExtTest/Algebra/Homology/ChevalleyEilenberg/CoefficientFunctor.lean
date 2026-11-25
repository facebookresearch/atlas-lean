/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Actual coefficient functor clients with a nontrivial Lie action

The Lie algebra is the noncommutative ring of two-by-two integer matrices,
with its commutator bracket and adjoint coefficient action. Matrix units have
a nonzero bracket, so the actual incoming CE boundary is nonzero. The
coefficient morphism doubles the right tensor factor; no chosen comparison,
chain-square certificate or vanishing-action hypothesis is supplied.
-/

noncomputable section

open CategoryTheory ChevalleyEilenberg
open scoped TensorProduct Matrix

namespace ChevalleyEilenberg.CoefficientFunctorTests

abbrev L := Matrix (Fin 2) (Fin 2) ℤ

local instance : LieRing L := LieRing.ofAssociativeRing

abbrev adjoint : LieModuleCat ℤ L := LieModuleCat.of ℤ L L

def e12 : L := !![0, 1; 0, 0]
def e21 : L := !![0, 0; 1, 0]

def twice : adjoint ⟶ adjoint :=
  (2 : ℤ) • (LieModuleHom.id : L →ₗ⁅ℤ,L⁆ L)

example : (⁅e12, e21⁆ : L) 0 0 = 1 := by
  norm_num [Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two, e12, e21]

example : (((coefficientComplexFunctor ℤ L).map twice).f 0).hom
    (exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] e12) =
      exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ((2 : ℤ) • e12) := by
  have h := coefficientComplexFunctor_map_f_tmul ℤ L twice 0
    (exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L)) e12
  have ht : twice e12 = (2 : ℤ) • e12 := by
    change ((2 : ℤ) • (LieModuleHom.id : L →ₗ⁅ℤ,L⁆ L)) e12 = (2 : ℤ) • e12
    rfl
  exact h.trans (congrArg
    (fun m : L => exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] m) ht)

/-- The actual first coefficient differential has a nonzero matrix coordinate. -/
theorem incoming_boundary_coordinate :
    (coefficientZeroEquiv ℤ L L
      (coefficientDifferential ℤ L L 0
        (exteriorPower.ιMulti ℤ 1 (fun _ => e12) ⊗ₜ[ℤ] e21))) 0 0 = -1 := by
  have h : coefficientZeroEquiv ℤ L L
      (coefficientDifferential ℤ L L 0
        (exteriorPower.ιMulti ℤ 1 (fun _ => e12) ⊗ₜ[ℤ] e21)) = -⁅e12, e21⁆ := by
    calc
      _ = coefficientZeroEquiv ℤ L L
          (-(exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ⁅e12, e21⁆)) :=
        congrArg (coefficientZeroEquiv ℤ L L) (coefficientDifferential_ι_tmul ℤ L L e12 e21)
      _ = -(coefficientZeroEquiv ℤ L L
          (exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ⁅e12, e21⁆)) :=
        (show ((coefficientZeroEquiv ℤ L L).toLinearMap :
            (⋀[ℤ]^0 L) ⊗[ℤ] L →ₗ[ℤ] L)
              (-(exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ⁅e12, e21⁆)) =
            -((coefficientZeroEquiv ℤ L L).toLinearMap :
              (⋀[ℤ]^0 L) ⊗[ℤ] L →ₗ[ℤ] L)
                (exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ⁅e12, e21⁆) from
          LinearMap.map_neg
            ((coefficientZeroEquiv ℤ L L).toLinearMap :
              (⋀[ℤ]^0 L) ⊗[ℤ] L →ₗ[ℤ] L)
            (exteriorPower.ιMulti ℤ 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[ℤ] ⁅e12, e21⁆))
      _ = _ := congrArg Neg.neg (coefficientZeroEquiv_ι_tmul ℤ L L ⁅e12, e21⁆)
  rw [h]
  norm_num [Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two, e12, e21]

example : coefficientDifferential ℤ L L 0
    (exteriorPower.ιMulti ℤ 1 (fun _ => e12) ⊗ₜ[ℤ] e21) ≠ 0 := by
  intro h
  let E : (⋀[ℤ]^0 L) ⊗[ℤ] L →ₗ[ℤ] L :=
    (coefficientZeroEquiv ℤ L L).toLinearMap
  have hz : E 0 = 0 := E.map_zero
  have he := congrArg (fun a : (⋀[ℤ]^0 L) ⊗[ℤ] L => E a) h
  have hval : E (coefficientDifferential ℤ L L 0
      (exteriorPower.ιMulti ℤ 1 (fun _ => e12) ⊗ₜ[ℤ] e21)) = 0 := he.trans hz
  have hc : (E (coefficientDifferential ℤ L L 0
      (exteriorPower.ιMulti ℤ 1 (fun _ => e12) ⊗ₜ[ℤ] e21))) 0 0 = 0 :=
    congrArg (fun a : L => a 0 0) hval
  have hn : (-1 : ℤ) = 0 := incoming_boundary_coordinate.symm.trans hc
  norm_num at hn

example : coefficientHomologyFunctor ℤ L 0 ≅ coefficientCoinvariantsFunctor ℤ L :=
  coefficientHomologyZeroNatIso ℤ L

example : (coefficientComplexFunctor ℤ L).map (twice + twice) =
    (coefficientComplexFunctor ℤ L).map twice + (coefficientComplexFunctor ℤ L).map twice :=
  (coefficientComplexFunctor ℤ L).map_add

example : (coefficientCoinvariantsFunctor ℤ L).map ((3 : ℤ) • twice) =
    (3 : ℤ) • (coefficientCoinvariantsFunctor ℤ L).map twice :=
  Functor.map_smul _ _ _

-- Scalar naturality in every degree for the same nonzero matrix-action model.
example (n : ℕ) : (coefficientHomologyFunctor ℤ L n).map ((3 : ℤ) • twice) =
    (3 : ℤ) • (coefficientHomologyFunctor ℤ L n).map twice :=
  Functor.map_smul _ _ _

end ChevalleyEilenberg.CoefficientFunctorTests
