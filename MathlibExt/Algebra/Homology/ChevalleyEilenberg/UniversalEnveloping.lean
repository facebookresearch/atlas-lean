/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CommutingScalars
public import MathlibExt.LinearAlgebra.ExteriorPower.Projective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Enveloping-algebra coefficients for Chevalley–Eilenberg chains

The left Lie action on the universal enveloping algebra is negative right
multiplication. Left regular multiplication commutes with that action,
so the coefficient complex is a complex of left enveloping-algebra modules.
Swapping tensor factors gives the coefficient-first right-regular boundary
convention.

The augmentation uses the trivial enveloping action. Each term is projective
when the underlying Lie module is projective.
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

/-- Negative right multiplication is the left Lie action corresponding to
right regular enveloping coefficients. -/
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

/-- The right-regular Lie action is linear over the original scalar ring. -/
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

/-- The native enveloping carrier, bundled with negative right regular
Lie coefficients. Its carrier and scalar action are unchanged. -/
abbrev regularCoefficients : LieModuleCat.{max u v} R L :=
  letI := rightRegularLieRingModule R L
  letI := rightRegularLieModule R L
  LieModuleCat.of R L U

/-- The regular coefficient model retains the native right action. -/
@[simp]
theorem regularCoefficients_lie (x : L) (a : regularCoefficients R L) :
    ⁅x, a⁆ = -(a * UniversalEnvelopingAlgebra.ι R x) := rfl

/-- Left multiplication on the coefficients commutes with the Lie action. -/
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

/-- The existing coefficient CE complex at native enveloping coefficients. -/
abbrev regularCoefficientComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  coefficientComplex R L (regularCoefficients R L)

/-- The native left-coefficient sign gives positive right multiplication on
regular enveloping coefficients in degree one. -/
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

/-- The augmentation is a map from regular coefficients to the
native trivial coefficient module, preserving the Lie actions. -/
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

/-- The left regular action on right-regular Lie coefficients. -/
def regularLeftAction : U →+* Module.End R (regularCoefficients R L) :=
  (Algebra.lmul R U).toRingHom

/-- Associativity earns the required commuting coefficient and Lie actions. -/
theorem regularLeftAction_lie (a : U) (x : L) (b : regularCoefficients R L) :
    regularLeftAction R L a ⁅x, b⁆ = ⁅x, regularLeftAction R L a b⁆ :=
  (regularCoefficientsLeftMap R L a).map_lie x b

/-- The CE complex over the enveloping algebra, using the original
right-regular coefficient differential and commuting left multiplication. -/
abbrev envelopingComplex : ChainComplex (ModuleCat.{max u v} U) ℕ :=
  coefficientScalarComplex R L (regularCoefficients R L)
    (regularLeftAction R L) (regularLeftAction_lie R L)

/-- Coefficient-first coordinates are linear for the original left enveloping action. -/
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

/-- The enveloping-module degree-one differential has positive right multiplication. -/
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

/-- In coefficient-first coordinates the differential is the u tensor x -> u iota(x) map of the
enveloping CE resolution model. -/
theorem envelopingComplex_d_one_coordinates (x : L) (a : regularCoefficients R L) :
    envelopingCoordinates R L 0
        (((envelopingComplex R L).d 1 0).hom
          ((envelopingCoordinates R L 1).symm
            (a ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => x)))) =
      (a * UniversalEnvelopingAlgebra.ι R x) ⊗ₜ[R]
        exteriorPower.ιMulti R 0 Fin.elim0 := by
  rw [envelopingCoordinates_symm_tmul, envelopingComplex_d_one,
    envelopingCoordinates_tmul]

/-- Every original enveloping CE term is projective when the underlying Lie
module is projective. Exactness and PBW are not assumed or concluded. -/
instance envelopingComplex_moduleProjective [Module.Projective R L] (n : ℕ) :
    Module.Projective U ((envelopingComplex R L).X n) := by
  let _ : Module.Projective R (⋀[R]^n L) := inferInstance
  let _ : Module.Projective U (U ⊗[R] (⋀[R]^n L)) :=
    Module.Projective.tensorProduct (R := U) (R₀ := R) (M := U) (N := ⋀[R]^n L)
  exact Module.Projective.of_equiv' (envelopingCoordinates R L n).symm

/-- The module projectivity supplies the native categorical notion
at each term, in the given module-category universe. -/
instance envelopingComplex_projective [Module.Projective R L] (n : ℕ) :
    CategoryTheory.Projective ((envelopingComplex R L).X n) := by
  infer_instance

/-- Native degree-zero coefficient-first tensor coordinates over the enveloping algebra. -/
def envelopingZeroEquiv : (envelopingComplex R L).X 0 ≃ₗ[U] U :=
  (envelopingCoordinates R L 0).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl U U)
      (exteriorPower.zeroEquiv R L)).trans (TensorProduct.AlgebraTensorModule.rid R U U))

theorem envelopingZeroEquiv_tmul (w : ⋀[R]^0 L) (a : regularCoefficients R L) :
    envelopingZeroEquiv R L (w ⊗ₜ[R] a) = (exteriorPower.zeroEquiv R L w) • a := by
  change (exteriorPower.zeroEquiv R L w) • a = (exteriorPower.zeroEquiv R L w) • a
  rfl

/-- The original scalar module, canonically lifted only to the enveloping-complex universe,
with the augmentation action of U(L). -/
abbrev envelopingTrivialObject : ModuleCat.{max u v} U :=
  letI : Module U (ULift.{max u v} R) :=
    Module.compHom (ULift.{max u v} R) (UniversalEnvelopingAlgebra.augmentation R L).toRingHom
  ModuleCat.of U (ULift.{max u v} R)

/-- The concrete lifted scalar carrier uses its stored native augmentation module. -/
instance envelopingTrivialObjectModule : Module U (envelopingTrivialObject R L) :=
  (envelopingTrivialObject R L).isModule

/-- The augmentation is linear for the trivial enveloping action. -/
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

/-- Degree zero of the augmentation retains the original native scalar coordinates. -/
def envelopingAugmentationComponent :
    (envelopingComplex R L).X 0 →ₗ[U] envelopingTrivialObject R L :=
  (envelopingAugmentationLinear R L).comp (envelopingZeroEquiv R L).toLinearMap

theorem envelopingAugmentationComponent_apply (p : (envelopingComplex R L).X 0) :
    envelopingAugmentationComponent R L p =
      ULift.up (UniversalEnvelopingAlgebra.augmentation R L (envelopingZeroEquiv R L p)) := rfl

/-- The augmentation chain condition is from its vanishing on the Lie generators. -/
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

/-- The augmented regular enveloping CE complex. This constructs the
augmentation, without asserting a quasi-isomorphism or a resolution. -/
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
