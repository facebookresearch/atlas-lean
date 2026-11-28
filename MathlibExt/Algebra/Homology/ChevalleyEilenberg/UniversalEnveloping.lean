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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CommutingScalars
public import MathlibExt.LinearAlgebra.ExteriorPower.Projective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Regular enveloping coefficients and their CE augmentation

Let U be the universal enveloping algebra of an R-Lie algebra L over a commutative ring R.
Negative right multiplication, ⁅x,a⁆ = −a*ι(x), makes U a left Lie module. Left regular
multiplication commutes with this action and equips its CE coefficient complex with a left
U-module structure.

The terms are ⋀[R]^n L ⊗[R] U. Swapping factors gives U-linear coordinates U ⊗[R] ⋀[R]^n L,
and the degree-one boundary in these coordinates is a ⊗ x ↦ a*ι(x). The augmentation maps the
degree-zero coefficient to its scalar augmentation, with target ULift R acted on by U through
ε.

Every term is U-projective when L is projective as an R-module. The complex and augmentation
themselves are constructed for arbitrary L; positive exactness is treated separately.

See Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

attribute [local instance] LieRing.ofAssociativeRing

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. The additive carrier of U has a LieRingModule structure over L with ⁅x,a⁆ =
−a*ι(x). The Lie module identity follows from associativity and ι(⁅x,y⁆) = ι(x)*ι(y) −
ι(y)*ι(x). -/
@[instance_reducible]
def rightRegularLieRingModule : LieRingModule L U where
  bracket x a := -(a * UniversalEnvelopingAlgebra.ι R x)
  add_lie x y a := by
    change -(a * UniversalEnvelopingAlgebra.ι R (x + y)) =
      -(a * UniversalEnvelopingAlgebra.ι R x) + -(a * UniversalEnvelopingAlgebra.ι R y)
    rw [map_add, mul_add, neg_add]
  lie_add x a b := by
    change -((a + b) * UniversalEnvelopingAlgebra.ι R x) =
      -(a * UniversalEnvelopingAlgebra.ι R x) + -(b * UniversalEnvelopingAlgebra.ι R x)
    rw [add_mul, neg_add]
  leibniz_lie x y a := by
    change -(-(a * UniversalEnvelopingAlgebra.ι R y) * UniversalEnvelopingAlgebra.ι R x) =
      -(a * UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) +
        -(-(a * UniversalEnvelopingAlgebra.ι R x) * UniversalEnvelopingAlgebra.ι R y)
    simp only [neg_mul, neg_neg]
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_sub, neg_sub]
    simp only [mul_assoc]
    exact (sub_add_cancel _ _).symm

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. With the LieRingModule structure ⁅x,a⁆ = −a*ι(x), U is a LieModule R L U. The
scalar compatibility uses the R-linearity of ι and the central R-algebra action on U. -/
theorem rightRegularLieModule :
    letI := rightRegularLieRingModule R L
    LieModule R L U := by
  let _ := rightRegularLieRingModule R L
  constructor
  · intro r x a
    change -(a * UniversalEnvelopingAlgebra.ι R (r • x)) =
      r • -(a * UniversalEnvelopingAlgebra.ι R x)
    rw [map_smul, mul_smul_comm, smul_neg]
  · intro r x a
    change -((r • a) * UniversalEnvelopingAlgebra.ι R x) =
      r • -(a * UniversalEnvelopingAlgebra.ι R x)
    rw [smul_mul_assoc, smul_neg]

attribute [local instance] rightRegularLieRingModule rightRegularLieModule

attribute [local implicit_reducible] coefficientComplex

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. regularCoefficients R L is U in LieModuleCat.{max u v} R L with Lie action ⁅x,a⁆
= −a*ι(x) and its R-algebra module structure. -/
abbrev regularCoefficients : LieModuleCat.{max u v} R L :=
  letI := rightRegularLieRingModule R L
  letI := rightRegularLieModule R L
  LieModuleCat.of R L U

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. For x : L and a : regularCoefficients R L, ⁅x,a⁆ = −a*ι(x). -/
@[simp]
theorem regularCoefficients_lie (x : L) (a : regularCoefficients R L) :
    ⁅x, a⁆ = -(a * UniversalEnvelopingAlgebra.ι R x) := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. For a : U, regularCoefficientsLeftMap a : regularCoefficients R L →ₗ⁅R,L⁆
regularCoefficients R L sends b to a*b. It is Lie-equivariant because a*(−b*ι(x)) =
−(a*b)*ι(x). -/
def regularCoefficientsLeftMap (a : U) :
    regularCoefficients R L →ₗ⁅R,L⁆ regularCoefficients R L where
  toLinearMap := (Algebra.lmul R U) a
  map_lie' := by
    intro x b
    change a * -(b * UniversalEnvelopingAlgebra.ι R x) =
      -((a * b) * UniversalEnvelopingAlgebra.ι R x)
    rw [mul_neg, mul_assoc]

@[simp]
theorem regularCoefficientsLeftMap_apply (a : U) (b : regularCoefficients R L) :
    regularCoefficientsLeftMap R L a b = a * b := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. regularCoefficientComplex R L is the ℕ-indexed R-module coefficient
complex with terms C_n and boundary coefficientDifferential for this negative right-regular
Lie action. -/
abbrev regularCoefficientComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  coefficientComplex R L (regularCoefficients R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. For x : L and a : U, the boundary sends ιMulti_R^1(x) ⊗ a to
ιMulti_R^0(empty) ⊗ (a*ι(x)). The negative coefficient-boundary convention cancels the
negative right-regular Lie action. -/
theorem regularCoefficientComplex_d_one (x : L) (a : regularCoefficients R L) :
    ((regularCoefficientComplex R L).d 1 0).hom
        (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] a) =
      exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R]
        (a * UniversalEnvelopingAlgebra.ι R x) := by
  change coefficientDifferential R L (regularCoefficients R L) 0
      (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] a) = _
  rw [coefficientDifferential_ι_tmul, regularCoefficients_lie]
  rw [← TensorProduct.tmul_neg]
  exact congrArg (fun b : regularCoefficients R L =>
    exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] b)
      (neg_neg (a * UniversalEnvelopingAlgebra.ι R x))

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. The R-linear map a ↦ ε(a), viewed in TrivialLieModule R L R, gives
augmentationCoefficientMap from regularCoefficients R L. It preserves the Lie actions because
ε(ι(x)) = 0. -/
def augmentationCoefficientMap :
    regularCoefficients R L →ₗ⁅R,L⁆ TrivialLieModule R L R where
  toLinearMap := (TrivialLieModule.equiv R L R).symm.toLinearMap.comp
    (UniversalEnvelopingAlgebra.augmentation R L).toLinearMap
  map_lie' := by
    intro x a
    change UniversalEnvelopingAlgebra.augmentation R L (-(a * UniversalEnvelopingAlgebra.ι R x)) = 0
    rw [map_neg, map_mul, UniversalEnvelopingAlgebra.augmentation_ι, mul_zero, neg_zero]

@[simp]
theorem augmentationCoefficientMap_apply (a : regularCoefficients R L) :
    augmentationCoefficientMap R L a = UniversalEnvelopingAlgebra.augmentation R L a := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. regularLeftAction : U →+* Module.End R (regularCoefficients R L) sends a to the
R-linear map b ↦ a*b. -/
def regularLeftAction : U →+* Module.End R (regularCoefficients R L) :=
  (Algebra.lmul R U).toRingHom

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. For a, b : U and x : L, regularLeftAction a (⁅x,b⁆) = ⁅x,regularLeftAction a b⁆,
using ⁅x,b⁆ = −b*ι(x). -/
theorem regularLeftAction_lie (a : U) (x : L) (b : regularCoefficients R L) :
    regularLeftAction R L a ⁅x, b⁆ = ⁅x, regularLeftAction R L a b⁆ :=
  (regularCoefficientsLeftMap R L a).map_lie x b

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. envelopingComplex R L is the chain complex in ModuleCat.{max u v} U
obtained from the coefficient complex by its commuting left U-action. The underlying terms C_n
and boundary functions are those of regularCoefficientComplex. -/
abbrev envelopingComplex : ChainComplex (ModuleCat.{max u v} U) ℕ :=
  coefficientScalarComplex R L (regularCoefficients R L)
    (regularLeftAction R L) (regularLeftAction_lie R L)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. For n : ℕ, envelopingCoordinates R L n : (envelopingComplex R L).X n
≃ₗ[U] U ⊗[R] ⋀[R]^n L sends a tensor w ⊗ b to b ⊗ w. The target U-action is left
multiplication on its first factor. -/
def envelopingCoordinates (n : ℕ) :
    (envelopingComplex R L).X n ≃ₗ[U] U ⊗[R] (⋀[R]^n L) := by
  let e := TensorProduct.comm R (⋀[R]^n L) U
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a p
  change e (coefficientDegreeRingAction R L (regularCoefficients R L)
      (regularLeftAction R L) (regularLeftAction_lie R L) n a p) = a • e p
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, smul_add, hp, hq]
  | tmul w b =>
      rw [coefficientDegreeRingAction_apply, coefficientComplexRingAction_f_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul']
      rfl

theorem envelopingCoordinates_tmul (n : ℕ) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    envelopingCoordinates R L n (w ⊗ₜ[R] a) = a ⊗ₜ[R] w :=
  TensorProduct.comm_tmul R (⋀[R]^n L) U w a

theorem envelopingCoordinates_symm_tmul (n : ℕ) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    (envelopingCoordinates R L n).symm (a ⊗ₜ[R] w) = w ⊗ₜ[R] a := by
  apply (envelopingCoordinates R L n).injective
  rw [LinearEquiv.apply_symm_apply, envelopingCoordinates_tmul]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. For x : L and a : U, (envelopingComplex R L).d 1 0 sends ιMulti_R^1(x) ⊗
a to ιMulti_R^0(empty) ⊗ (a*ι(x)). -/
theorem envelopingComplex_d_one (x : L) (a : regularCoefficients R L) :
    ((envelopingComplex R L).d 1 0).hom
        (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] a) =
      exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R]
        (a * UniversalEnvelopingAlgebra.ι R x) := by
  change coefficientDifferential R L (regularCoefficients R L) 0
      (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] a) = _
  rw [coefficientDifferential_ι_tmul, regularCoefficients_lie]
  rw [← TensorProduct.tmul_neg]
  exact congrArg (fun b : regularCoefficients R L =>
    exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] b)
      (neg_neg (a * UniversalEnvelopingAlgebra.ι R x))

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its universal enveloping
algebra, ι its generator map and ε its augmentation. Give U the coefficient Lie action ⁅x,a⁆ =
−a*ι(x). In the U-linear equivalences envelopingCoordinates, the degree-one boundary sends a ⊗
ιMulti_R^1(x) to (a*ι(x)) ⊗ ιMulti_R^0(empty). -/
theorem envelopingComplex_d_one_coordinates (x : L) (a : regularCoefficients R L) :
    envelopingCoordinates R L 0
        (((envelopingComplex R L).d 1 0).hom
          ((envelopingCoordinates R L 1).symm
            (a ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => x)))) =
      (a * UniversalEnvelopingAlgebra.ι R x) ⊗ₜ[R]
        exteriorPower.ιMulti R 0 Fin.elim0 := by
  rw [envelopingCoordinates_symm_tmul, envelopingComplex_d_one,
    envelopingCoordinates_tmul]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. If L is projective as an R-module, then (envelopingComplex R L).X n is
projective as a U-module for every n : ℕ. Its coefficient-first coordinates identify it with U
⊗[R] ⋀[R]^n L. -/
instance envelopingComplex_moduleProjective [Module.Projective R L] (n : ℕ) :
    Module.Projective U ((envelopingComplex R L).X n) := by
  let _ : Module.Projective R (⋀[R]^n L) := inferInstance
  let _ : Module.Projective U (U ⊗[R] (⋀[R]^n L)) :=
    Module.Projective.tensorProduct (R := U) (R₀ := R) (M := U) (N := ⋀[R]^n L)
  exact Module.Projective.of_equiv' (envelopingCoordinates R L n).symm

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. If Module.Projective R L holds, each object (envelopingComplex R L).X n
is projective in the category ModuleCat.{max u v} U. -/
instance envelopingComplex_projective [Module.Projective R L] (n : ℕ) :
    CategoryTheory.Projective ((envelopingComplex R L).X n) := by
  infer_instance

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. The U-linear equivalence envelopingZeroEquiv : C₀ ≃ₗ[U] U is obtained
from coefficient-first coordinates, ⋀[R]^0 L ≃ₗ[R] R and the tensor right unitor. It sends the
empty exterior word tensored with a to a. -/
def envelopingZeroEquiv : (envelopingComplex R L).X 0 ≃ₗ[U] U :=
  (envelopingCoordinates R L 0).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl U U)
      (exteriorPower.zeroEquiv R L)).trans (TensorProduct.AlgebraTensorModule.rid R U U))

theorem envelopingZeroEquiv_tmul (w : ⋀[R]^0 L) (a : regularCoefficients R L) :
    envelopingZeroEquiv R L (w ⊗ₜ[R] a) = (exteriorPower.zeroEquiv R L w) • a := by
  change (exteriorPower.zeroEquiv R L w) • a = (exteriorPower.zeroEquiv R L w) • a
  rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. envelopingTrivialObject R L is ULift.{max u v} R in ModuleCat.{max u v} U, with
a • ULift.up r = ULift.up (ε(a)*r). -/
abbrev envelopingTrivialObject : ModuleCat.{max u v} U :=
  letI : Module U (ULift.{max u v} R) :=
    Module.compHom (ULift.{max u v} R) (UniversalEnvelopingAlgebra.augmentation R L).toRingHom
  ModuleCat.of U (ULift.{max u v} R)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. The U-module structure on envelopingTrivialObject R L is the restriction of
scalar multiplication on ULift R along ε : U → R. Its action is a • ULift.up r = ULift.up
(ε(a)*r). -/
instance envelopingTrivialObjectModule : Module U (envelopingTrivialObject R L) :=
  (envelopingTrivialObject R L).isModule

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. The map envelopingAugmentationLinear : U →ₗ[U] envelopingTrivialObject R L sends
a to ULift.up (ε(a)). Its linearity is the multiplicativity of ε with the target action
induced by ε. -/
def envelopingAugmentationLinear : U →ₗ[U] envelopingTrivialObject R L where
  toFun a := ULift.up (UniversalEnvelopingAlgebra.augmentation R L a)
  map_add' a b := by
    apply ULift.ext
    exact (UniversalEnvelopingAlgebra.augmentation R L).map_add a b
  map_smul' a b := by
    apply ULift.ext
    change UniversalEnvelopingAlgebra.augmentation R L (a * b) =
      UniversalEnvelopingAlgebra.augmentation R L a * UniversalEnvelopingAlgebra.augmentation R L b
    exact (UniversalEnvelopingAlgebra.augmentation R L).map_mul a b

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. The degree-zero map envelopingAugmentationComponent : C₀ →ₗ[U]
envelopingTrivialObject R L is envelopingAugmentationLinear composed with envelopingZeroEquiv.
In particular the empty word tensored with a maps to ULift.up (ε(a)). -/
def envelopingAugmentationComponent :
    (envelopingComplex R L).X 0 →ₗ[U] envelopingTrivialObject R L :=
  (envelopingAugmentationLinear R L).comp (envelopingZeroEquiv R L).toLinearMap

theorem envelopingAugmentationComponent_apply (p : (envelopingComplex R L).X 0) :
    envelopingAugmentationComponent R L p =
      ULift.up (UniversalEnvelopingAlgebra.augmentation R L (envelopingZeroEquiv R L p)) := rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. The composite (envelopingComplex R L).d 1 0 ≫
envelopingAugmentationComponent is zero. Its generator values have augmentation ε(a*ι(x)) = 0. -/
theorem envelopingAugmentationComponent_boundary :
    (envelopingComplex R L).d 1 0 ≫ ModuleCat.ofHom
      (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
      (envelopingAugmentationComponent R L) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  change envelopingAugmentationComponent R L
      (((envelopingComplex R L).d 1 0).hom p) = 0
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | tmul w a =>
      have hw : w = exteriorPower.ιMulti R 1 (fun _ => exteriorPower.oneEquiv R L w) := by
        apply (exteriorPower.oneEquiv R L).injective
        rw [exteriorPower.oneEquiv_ιMulti]
      rw [hw, envelopingComplex_d_one, envelopingAugmentationComponent_apply,
        envelopingZeroEquiv_tmul, exteriorPower.zeroEquiv_ιMulti, one_smul]
      apply ULift.ext
      change UniversalEnvelopingAlgebra.augmentation R L
          (a * UniversalEnvelopingAlgebra.ι R (exteriorPower.oneEquiv R L w)) = 0
      rw [map_mul, UniversalEnvelopingAlgebra.augmentation_ι, mul_zero]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. envelopingAugmentation is the chain map from envelopingComplex R L to
the complex concentrated in degree zero at envelopingTrivialObject R L. Its zero component is
envelopingAugmentationComponent and its positive-degree components target zero objects. -/
def envelopingAugmentation :
    envelopingComplex R L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} U)).obj (envelopingTrivialObject R L) :=
  (ChainComplex.toSingle₀Equiv (envelopingComplex R L) (envelopingTrivialObject R L)).symm
    ⟨ModuleCat.ofHom
      (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
      (envelopingAugmentationComponent R L),
      envelopingAugmentationComponent_boundary R L⟩

@[simp]
theorem envelopingAugmentation_f_zero :
    (envelopingAugmentation R L).f 0 = ModuleCat.ofHom
      (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
      (envelopingAugmentationComponent R L) := by
  unfold envelopingAugmentation
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero
    (C := envelopingComplex R L) (X := envelopingTrivialObject R L)
    (ModuleCat.ofHom
      (X := (envelopingComplex R L).X 0) (Y := envelopingTrivialObject R L)
      (envelopingAugmentationComponent R L))
    (envelopingAugmentationComponent_boundary R L)

end ChevalleyEilenberg
