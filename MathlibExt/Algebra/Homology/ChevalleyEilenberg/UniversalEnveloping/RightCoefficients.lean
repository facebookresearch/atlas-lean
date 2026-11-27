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
# Right enveloping modules as Lie-homology coefficients

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `U = U_R(L)`. A right `U`-module is
represented as a left `Uᵐᵒᵖ`-module `N`. It restricts to an `R`-module and has left Lie action
`[x,m] = -op(ι(x)) • m`.

On the exterior-first coefficient chain term `⋀ⁿ[R] L ⊗[R] N`, the action boundary deletes
each Lie argument with sign `(-1)^i` and applies its right generator action to `N`. The full
differential adds the bracket boundary. Right enveloping-linear morphisms induce Lie
coefficient morphisms, and the coefficient carrier universe is independent of the scalar and
Lie universes.
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

/-- The negative Lie action of right enveloping coefficients.

For a left `U_R(L)ᵐᵒᵖ`-module `N`, the bracket `[x,m] = -op(ι(x)) • m` defines a left Lie-
ring-module structure on its carrier. -/
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

/-- Ground-linearity of the negative right coefficient action.

The Lie action `[x,m] = -op(ι(x)) • m` is `R`-bilinear for the scalar action restricted from
`U_R(L)ᵐᵒᵖ`. -/
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

/-- The Lie coefficient module of a right enveloping module.

A right `U_R(L)`-module `N` gives a left `L`-module with the same coefficient carrier, ground
scalars restricted along `R → Uᵐᵒᵖ`, and bracket `[x,m] = -op(ι(x)) • m`. -/
@[implicit_reducible]
def rightCoefficients (N : ModuleCat.{w} Uᵐᵒᵖ) : LieModuleCat.{w} R L where
  carrier := N
  lieRingModule := rightCoefficientLieRingModule R L N
  lieModule := rightCoefficientLieModule R L N

/-- The bracket formula for right enveloping coefficients.

For `x ∈ L` and `m ∈ N`, the associated left Lie action is the negative right generator action
`-op(ι(x)) • m`. -/
@[simp]
theorem rightCoefficients_lie (N : ModuleCat.{w} Uᵐᵒᵖ) (x : L)
    (m : rightCoefficients R L N) :
    ⁅x, m⁆ = -(op (UniversalEnvelopingAlgebra.ι R x) • (show N from m)) := rfl

/-- The ground-scalar formula for right enveloping coefficients.

For `r ∈ R`, the coefficient scalar action is `r • m = op(algebraMap(R,U)(r)) • m`. -/
@[simp]
theorem rightCoefficients_smul (N : ModuleCat.{w} Uᵐᵒᵖ) (r : R)
    (m : rightCoefficients R L N) :
    r • m = op (algebraMap R U r) • (show N from m) := rfl

/-- The opposite-enveloping action on right Lie coefficients.

The Lie coefficient carrier associated to `N` retains its given module action over
`U_R(L)ᵐᵒᵖ`. -/
instance rightCoefficientsModule (N : ModuleCat.{w} Uᵐᵒᵖ) :
    Module Uᵐᵒᵖ (rightCoefficients R L N) :=
  inferInstanceAs (Module Uᵐᵒᵖ N)

/-- The scalar tower for right enveloping coefficients.

The actions on the coefficient module form the scalar tower `R → U_R(L)ᵐᵒᵖ → N`. -/
instance rightCoefficients_scalarTower (N : ModuleCat.{w} Uᵐᵒᵖ) :
    IsScalarTower R Uᵐᵒᵖ (rightCoefficients R L N) :=
  inferInstanceAs (IsScalarTower R Uᵐᵒᵖ N)

/-- Commutation of ground scalars with the right enveloping action.

For `r ∈ R` and `a ∈ U_R(L)ᵐᵒᵖ`, the two coefficient actions commute: `r • (a • m) = a • (r •
m)`. -/
instance rightCoefficients_smulComm (N : ModuleCat.{w} Uᵐᵒᵖ) :
    SMulCommClass R Uᵐᵒᵖ (rightCoefficients R L N) where
  smul_comm r a m := by
    change (algebraMap R Uᵐᵒᵖ r) • (a • (show N from m)) =
      a • ((algebraMap R Uᵐᵒᵖ r) • (show N from m))
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The Lie coefficient map of a right enveloping morphism.

A `U_R(L)ᵐᵒᵖ`-linear map restricts to an `R`-linear map commuting with the negative generator
Lie action. -/
def rightCoefficientsMap {N N' : ModuleCat.{w} Uᵐᵒᵖ} (f : N ⟶ N') :
    rightCoefficients R L N →ₗ⁅R,L⁆ rightCoefficients R L N' where
  toLinearMap := ((ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).map f).hom
  map_lie' := by
    intro x m
    change f.hom (-(op (UniversalEnvelopingAlgebra.ι R x) • m)) =
      -(op (UniversalEnvelopingAlgebra.ι R x) • f.hom m)
    rw [map_neg, f.hom.map_smul]

/-- The value of a right enveloping map as a Lie coefficient map.

For a right enveloping-module morphism `f`, the induced Lie coefficient map has value
`f.hom(m)`. -/
@[simp]
theorem rightCoefficientsMap_apply {N N' : ModuleCat.{w} Uᵐᵒᵖ} (f : N ⟶ N')
    (m : rightCoefficients R L N) : rightCoefficientsMap R L f m = f.hom m := rfl

/-- The Lie coefficient functor on right enveloping modules.

This functor restricts a right enveloping module to the negative left generator action and
retains coefficient-map values. -/
def rightCoefficientsFunctor : ModuleCat.{w} Uᵐᵒᵖ ⥤ LieModuleCat.{w} R L where
  obj := rightCoefficients R L
  map := rightCoefficientsMap R L
  map_id N := by apply LieModuleHom.ext; intro m; rfl
  map_comp f g := by apply LieModuleHom.ext; intro m; rfl

/-- The Lie-homology chain complex of a right enveloping module.

For `N`, this is the Chevalley–Eilenberg complex with degree `n` equal to `⋀ⁿ[R] L ⊗[R] N` and
the negative right-generator coefficient action. Its carrier universe includes the scalar,
Lie, and coefficient universes. -/
abbrev rightEnvelopingCoefficientComplex (N : ModuleCat.{w} Uᵐᵒᵖ) :
    ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  coefficientComplex R L (rightCoefficients R L N)

/-- The positive right-action formula for coefficient boundaries.

The action boundary of `(⋀ᵢ vᵢ) ⊗ m` is `∑ᵢ (-1)^i (⋀_(j≠i) vⱼ) ⊗ (op(ι(vᵢ)) • m)`, with
exterior survivors in order. -/
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

/-- The full boundary formula for right enveloping coefficients.

The differential of `(⋀ᵢ vᵢ) ⊗ m` is the bracket boundary tensored with `m`, plus `∑ᵢ (-1)^i
(⋀_(j≠i) vⱼ) ⊗ (op(ι(vᵢ)) • m)`. The generator acts on the right coefficient factor. -/
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
