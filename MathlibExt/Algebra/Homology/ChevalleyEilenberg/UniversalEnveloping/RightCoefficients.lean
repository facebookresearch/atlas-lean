/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Right enveloping modules as Chevalley–Eilenberg coefficients

A right enveloping module restricts to the ground ring and has left Lie
action given by negative right multiplication by Lie generators. The
exterior-first coefficient differential then has positive right-action terms.
Right enveloping-module homomorphisms induce coefficient maps and chain maps.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

attribute [local instance] LieRing.ofAssociativeRing

/-- Negative right action of the original Lie generators on an right
module over the native enveloping algebra. -/
@[instance_reducible]
def rightCoefficientLieRingModule (N : ModuleCat.{w} Uᵐᵒᵖ) : LieRingModule L N where
  bracket x m := -(op (UniversalEnvelopingAlgebra.ι R x) • m)
  add_lie x y m := by
    change -(op (UniversalEnvelopingAlgebra.ι R (x + y)) • m) =
      -(op (UniversalEnvelopingAlgebra.ι R x) • m) +
        -(op (UniversalEnvelopingAlgebra.ι R y) • m)
    rw [map_add, MulOpposite.op_add, add_smul, neg_add]
  lie_add x m n := by
    change -(op (UniversalEnvelopingAlgebra.ι R x) • (m + n)) =
      -(op (UniversalEnvelopingAlgebra.ι R x) • m) +
        -(op (UniversalEnvelopingAlgebra.ι R x) • n)
    rw [smul_add, neg_add]
  leibniz_lie x y m := by
    change -(op (UniversalEnvelopingAlgebra.ι R x) •
        -(op (UniversalEnvelopingAlgebra.ι R y) • m)) =
      -(op (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) • m) +
        -(op (UniversalEnvelopingAlgebra.ι R y) •
          -(op (UniversalEnvelopingAlgebra.ι R x) • m))
    simp only [smul_neg, neg_neg]
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket,
      MulOpposite.op_sub, sub_smul, neg_sub]
    simp only [← mul_smul, ← MulOpposite.op_mul]
    exact (sub_add_cancel _ _).symm

/-- The Lie action is linear for the native restricted scalar action. -/
@[instance_reducible]
def rightCoefficientLieModule (N : ModuleCat.{w} Uᵐᵒᵖ) :
    @LieModule R L N _ _ _ _ _ (rightCoefficientLieRingModule R L N) := by
  letI := rightCoefficientLieRingModule R L N
  constructor
  · intro r x m
    change -(op (UniversalEnvelopingAlgebra.ι R (r • x)) • m) =
      r • -(op (UniversalEnvelopingAlgebra.ι R x) • m)
    have hop : op (r • UniversalEnvelopingAlgebra.ι R x) =
        r • op (UniversalEnvelopingAlgebra.ι R x) := rfl
    rw [map_smul, hop, smul_assoc, smul_neg]
  · intro r x m
    change -(op (UniversalEnvelopingAlgebra.ι R x) • (r • m)) =
      r • -(op (UniversalEnvelopingAlgebra.ι R x) • m)
    rw [smul_comm (op (UniversalEnvelopingAlgebra.ι R x)) r m, smul_neg]

/-- The original right UEA carrier, with native scalar restriction and the
computed negative left Lie action. -/
@[implicit_reducible]
def rightCoefficients (N : ModuleCat.{w} Uᵐᵒᵖ) : LieModuleCat.{w} R L where
  carrier := N
  lieRingModule := rightCoefficientLieRingModule R L N
  lieModule := rightCoefficientLieModule R L N

@[simp]
theorem rightCoefficients_lie (N : ModuleCat.{w} Uᵐᵒᵖ) (x : L)
    (m : rightCoefficients R L N) :
    ⁅x, m⁆ = -(op (UniversalEnvelopingAlgebra.ι R x) • (show N from m)) := rfl

@[simp]
theorem rightCoefficients_smul (N : ModuleCat.{w} Uᵐᵒᵖ) (r : R)
    (m : rightCoefficients R L N) :
    r • m = op (algebraMap R U r) • (show N from m) := rfl

/-- The right acting-ring action is the original module action. -/
instance rightCoefficientsModule (N : ModuleCat.{w} Uᵐᵒᵖ) :
    Module Uᵐᵒᵖ (rightCoefficients R L N) :=
  inferInstanceAs (Module Uᵐᵒᵖ N)

/-- Restriction gives the scalar tower used by balanced cancellation. -/
instance rightCoefficients_scalarTower (N : ModuleCat.{w} Uᵐᵒᵖ) :
    IsScalarTower R Uᵐᵒᵖ (rightCoefficients R L N) :=
  inferInstanceAs (IsScalarTower R Uᵐᵒᵖ N)

/-- Central scalar restriction commutes with the original right action. -/
instance rightCoefficients_smulComm (N : ModuleCat.{w} Uᵐᵒᵖ) :
    SMulCommClass R Uᵐᵒᵖ (rightCoefficients R L N) where
  smul_comm r a m := by
    change (algebraMap R Uᵐᵒᵖ r) • (a • (show N from m)) =
      a • ((algebraMap R Uᵐᵒᵖ r) • (show N from m))
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- An right UEA map is a map for the Lie coefficient actions. -/
def rightCoefficientsMap {N N' : ModuleCat.{w} Uᵐᵒᵖ} (f : N ⟶ N') :
    rightCoefficients R L N →ₗ⁅R,L⁆ rightCoefficients R L N' where
  toLinearMap := ((ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).map f).hom
  map_lie' := by
    intro x m
    change f.hom (-(op (UniversalEnvelopingAlgebra.ι R x) • m)) =
      -(op (UniversalEnvelopingAlgebra.ι R x) • f.hom m)
    rw [map_neg, f.hom.map_smul]

@[simp]
theorem rightCoefficientsMap_apply {N N' : ModuleCat.{w} Uᵐᵒᵖ} (f : N ⟶ N')
    (m : rightCoefficients R L N) : rightCoefficientsMap R L f m = f.hom m := rfl

/-- The coefficient restriction is an functor on original right modules. -/
def rightCoefficientsFunctor : ModuleCat.{w} Uᵐᵒᵖ ⥤ LieModuleCat.{w} R L where
  obj := rightCoefficients R L
  map := rightCoefficientsMap R L
  map_id N := by apply LieModuleHom.ext; intro m; rfl
  map_comp f g := by apply LieModuleHom.ext; intro m; rfl

/-- The original all-degree coefficient complex for an right UEA module. -/
abbrev rightEnvelopingCoefficientComplex (N : ModuleCat.{w} Uᵐᵒᵖ) :
    ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  coefficientComplex R L (rightCoefficients R L N)

/-- The original action boundary has the positive right-action sign. -/
theorem rightCoefficientActionBoundary_apply_ιMulti_tmul (N : ModuleCat.{w} Uᵐᵒᵖ)
    (n : ℕ) (v : Fin (n + 1) → L) (m : rightCoefficients R L N) :
    coefficientActionBoundary R L (rightCoefficients R L N) n
      (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R]
          (op (UniversalEnvelopingAlgebra.ι R (v i)) • m)) := by
  rw [coefficientActionBoundary_apply_ιMulti_tmul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rightCoefficients_lie, pow_succ, mul_smul]
  congr 1
  rw [← TensorProduct.tmul_smul, neg_one_smul, neg_neg]

/-- The all-degree chain formula, with the original bracket boundary
and positive right multiplication with the coefficient order fixed. -/
theorem rightEnvelopingCoefficientDifferential_apply_ιMulti_tmul (N : ModuleCat.{w} Uᵐᵒᵖ)
    (n : ℕ) (v : Fin (n + 1) → L) (m : rightCoefficients R L N) :
    coefficientDifferential R L (rightCoefficients R L N) n
      (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m) =
      differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R]
            (op (UniversalEnvelopingAlgebra.ι R (v i)) • m)) := by
  rw [coefficientDifferential_eq_bracket_add_action, LinearMap.add_apply,
    LinearMap.rTensor_tmul, rightCoefficientActionBoundary_apply_ιMulti_tmul]

end ChevalleyEilenberg
