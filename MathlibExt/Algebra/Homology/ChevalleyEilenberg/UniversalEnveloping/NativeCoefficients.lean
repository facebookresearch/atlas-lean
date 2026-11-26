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

public import MathlibExt.Algebra.Category.LieModuleCat.RightUniversalEnveloping
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.TorZeroAt
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor

/-!
# Lie coefficient recovery and enveloping Tor comparisons

Extend a left Lie-module M to a right enveloping representation N with generator action m·ι(x)
= −[x,m]. Converting N back to left Lie coefficients by [x,m] = −m·ι(x) recovers the given
action and scalar structure on the same carrier. Applying the coefficient CE functor gives an
isomorphism of complexes.

Degree-zero homology maps canonically to N balanced-tensored with the trivial module, sending
the empty-word class of m to [m,1]. When L is free over R, every coefficient homology degree
computes the left-derived right tensor functor at the lifted trivial module. The comparisons
commute with compatible Lie and coefficient maps in their common carrier height.
-/

@[expose] public section

noncomputable section

universe u v v' w z z'

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

local instance nativeCoefficientTensor_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{z} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, v, z, z'} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. nativeRightCoefficientsIso : M ≅ rightCoefficients R L N uses
identity carrier maps in both directions. The double negative generator action recovers the
given Lie action, and the represented ground scalar action equals the R-action of M. -/
def nativeRightCoefficientsIso (M : LieModuleCat.{max u v v' w} R L) :
    M ≅ rightCoefficients R L (LieModuleCat.RightUniversalEnveloping.representObj R L M) where
  hom :=
    { toLinearMap :=
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun r m =>
            (LieModuleCat.RightUniversalEnveloping.representObj_ground_smul R L M r m).symm }
      map_lie' := by
        intro x m
        change @Bracket.bracket L M M.lieRingModule.toBracket x (show M from m) =
          -(op (UniversalEnvelopingAlgebra.ι R x) •
          (show LieModuleCat.RightUniversalEnveloping.representObj R L M from m))
        have h := LieModuleCat.RightUniversalEnveloping.representObj_op_ι R L M x (show M from m)
        exact ((congrArg Neg.neg h).trans (neg_neg _)).symm }
  inv :=
    { toLinearMap :=
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun r m =>
            LieModuleCat.RightUniversalEnveloping.representObj_ground_smul R L M r m }
      map_lie' := by
        intro x m
        change -(op (UniversalEnvelopingAlgebra.ι R x) •
          (show LieModuleCat.RightUniversalEnveloping.representObj R L M from m)) = @Bracket.bracket L M
            M.lieRingModule.toBracket x (show M from m)
        have h := LieModuleCat.RightUniversalEnveloping.representObj_op_ι R L M x (show M from m)
        exact (congrArg Neg.neg h).trans (neg_neg _) }
  hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
  inv_hom_id := by apply LieModuleHom.ext; intro m; rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. Mapping nativeRightCoefficientsIso through
coefficientComplexFunctor gives coefficientComplex R L M ≅ rightEnvelopingCoefficientComplex R
L N. -/
def nativeRightCoefficientComplexIso (M : LieModuleCat.{max u v v' w} R L) :
    coefficientComplex R L M ≅ rightEnvelopingCoefficientComplex R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) :=
  (coefficientComplexFunctor R L).mapIso (nativeRightCoefficientsIso.{u, v, v', w} R L M)

theorem nativeRightCoefficientComplexIso_f_tmul (M : LieModuleCat.{max u v v' w} R L)
    (n : ℕ) (x : ⋀[R]^n L) (m : M) :
    ((nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom.f n).hom (x ⊗ₜ[R] m) =
      x ⊗ₜ[R] (show rightCoefficients R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) from m) :=
  by
    have h := coefficientComplexFunctor_map_f_tmul R L
      (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom n x m
    exact h.trans (congrArg (fun y : rightCoefficients R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) => x ⊗ₜ[R] y) (show
        (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom m = m from rfl))

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. nativeCoefficientHomologyZeroTensorIso identifies H₀(CE(L,M)) with
ModuleCat.BalancedTensor.functor R U N applied to T₀, using coefficient recovery and the
coinvariant/unit tensor comparison. -/
def nativeCoefficientHomologyZeroTensorIso (M : LieModuleCat.{max u v v' w} R L) :
    (coefficientComplex R L M).homology 0 ≅
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj (envelopingTrivialObject R L) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) 0).mapIso
    (nativeRightCoefficientComplexIso.{u, v, v', w} R L M) ≪≫
      rightCoefficientHomologyZeroTensorIso R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. For m : M, the H₀ class of the empty exterior word ⊗ m maps under
nativeCoefficientHomologyZeroTensorIso to Balanced.mk R U N T₀ m (ULift.up 1). -/
theorem nativeCoefficientHomologyZeroTensorIso_class (M : LieModuleCat.{max u v v' w} R L)
    (m : M) :
    (nativeCoefficientHomologyZeroTensorIso.{u, v, v', w} R L M).hom
      ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] m))) =
      TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R)) := by
  let a := (nativeRightCoefficientsIso.{u, v, v', w} R L M).hom
  have h := coefficientHomologyMap_zero_class R L M a m
  have hValue : a m = (show rightCoefficients R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L M) from m) := rfl
  have hClass := (rightCoefficientHomologyZeroTensorIso_class R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M) m)
  have hMap := congrArg (rightCoefficientHomologyZeroTensorIso R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M)).hom h
  exact hMap.trans hClass

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{max u v v' w} R L) (M' : LieModuleCat.{max u v v' w} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

local notation "N" => LieModuleCat.RightUniversalEnveloping.representObj R L M
local notation "N'" => LieModuleCat.RightUniversalEnveloping.representObj R L' M'
local notation "g" => LieModuleCat.RightUniversalEnveloping.representLieMapSemilinear R L f h

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Let L' : Type v' be another R-Lie algebra, f : L →ₗ⁅R⁆ L', H = max u v v' w, M and M' Lie
modules in height H, and h : M →ₗ⁅R,L⁆ f* M'. Let N,N' be their right U- and
U'-representations and g the induced semilinear right-module map along UEA.map f.
nativeCoefficientLieComplexMap : CE(L,M) ⟶ CE(L',M') has degree-n component ⋀^n f ⊗ h,
obtained from homogeneous differential naturality. -/
def nativeCoefficientLieComplexMap : coefficientComplex R L M ⟶ coefficientComplex R L' M' :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (coefficientLieDegreeMap R L f M M' h n)) (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom (coefficientLieDifferential_naturality R L f M M' h n).symm)

theorem nativeCoefficientLieComplexMap_f_tmul (n : ℕ) (x : ⋀[R]^n L) (m : M) :
    ((nativeCoefficientLieComplexMap R L f M M' h).f n).hom (x ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap x ⊗ₜ[R] h m :=
  coefficientLieDegreeMap_tmul R L f M M' h n x m

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Let L' : Type v' be another R-Lie algebra, f : L →ₗ⁅R⁆ L', H = max u v v' w, M and M' Lie
modules in height H, and h : M →ₗ⁅R,L⁆ f* M'. Let N,N' be their right U- and
U'-representations and g the induced semilinear right-module map along UEA.map f. The CE map
followed by nativeRightCoefficientComplexIso for M' equals the coefficient-recovery
isomorphism for M followed by rightEnvelopingCoefficientLieComplexMap(f,g). -/
theorem nativeRightCoefficientComplexIso_lie_naturality :
    nativeCoefficientLieComplexMap R L f M M' h ≫ (nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom =
      (nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom ≫ rightEnvelopingCoefficientLieComplexMap R L f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x m
  change ((nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom.f n).hom
      (((nativeCoefficientLieComplexMap R L f M M' h).f n).hom (x ⊗ₜ[R] m)) =
    ((rightEnvelopingCoefficientLieComplexMap R L f g).f n).hom
      (((nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom.f n).hom (x ⊗ₜ[R] m))
  rw [nativeCoefficientLieComplexMap_f_tmul, nativeRightCoefficientComplexIso_f_tmul,
    nativeRightCoefficientComplexIso_f_tmul, rightEnvelopingCoefficientLieComplexMap_f_tmul]
  rfl

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Let L' : Type v' be another R-Lie algebra, f : L →ₗ⁅R⁆ L', H = max u v v' w, M and M' Lie
modules in height H, and h : M →ₗ⁅R,L⁆ f* M'. Let N,N' be their right U- and
U'-representations and g the induced semilinear right-module map along UEA.map f. For n : ℕ,
nativeLieCoefficientTorMap is rightEnvelopingTorLieMapAt R L f N N' g n, derived from the
represented right-module map and the canonical enveloping scalar-change square. -/
def nativeLieCoefficientTorMap (n : ℕ) :=
  rightEnvelopingTorLieMapAt R L f N N' g n

end JointMaps

section ResolutionComparison

variable [Module.Free R L]

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. Assume Module.Free R L. For n : ℕ, nativeCoefficientHomologyIsoTor
identifies H_n(CE(L,M)) with the n-th left-derived functor of X ↦ Balanced(R,U,N,X), evaluated
at liftedEnvelopingTrivial in height H. -/
def nativeCoefficientHomologyIsoTor (M : LieModuleCat.{max u v v' w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≅
      (((ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) :
          ModuleCat.{max u v v' w} U ⥤ (ModuleCat.{max u v v' w} R)).leftDerived n).obj
        (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w} R) (ComplexShape.down ℕ) n).mapIso
    (nativeRightCoefficientComplexIso.{u, v, v', w} R L M) ≪≫
      rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) n

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. Assume Module.Free R L. The degree-zero CE/Tor comparison followed
by fromLeftDerivedZero at the lifted trivial module and rightTrivialTensorLiftEquiv equals
nativeCoefficientHomologyZeroTensorIso. -/
theorem nativeCoefficientHomologyIsoTor_zero_canonical (M : LieModuleCat.{max u v v' w} R L) :
    (nativeCoefficientHomologyIsoTor.{u, v, v', w} R L M 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M) :
          ModuleCat.{max u v v' w} U ⥤ (ModuleCat.{max u v v' w} R)).fromLeftDerivedZero.app
            (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≫
      (rightTrivialTensorLiftEquiv.{u, v, v', w} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)).toModuleIso.hom =
      (nativeCoefficientHomologyZeroTensorIso.{u, v, v', w} R L M).hom := by
  let a := HomologicalComplex.homologyMap (nativeRightCoefficientComplexIso.{u, v, v', w} R L M).hom 0
  have h := rightCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w} R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L M)
  exact (Category.assoc _ _ _).trans (congrArg (fun t => a ≫ t) h)

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] [Module.Free R L']
  (f : L →ₗ⁅R⁆ L') (M : LieModuleCat.{max u v v' w} R L) (M' : LieModuleCat.{max u v v' w} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Let L' : Type v' be another R-Lie algebra, f : L →ₗ⁅R⁆ L', H = max u v v' w, M and M' Lie
modules in height H, and h : M →ₗ⁅R,L⁆ f* M'. Let N,N' be their right U- and
U'-representations and g the induced semilinear right-module map along UEA.map f. Assume
Module.Free R L and Module.Free R L'. For n : ℕ, H_n(nativeCoefficientLieComplexMap) followed
by the target CE/Tor comparison equals the source comparison followed by
nativeLieCoefficientTorMap n. -/
theorem nativeCoefficientHomologyIsoTor_lie_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (nativeCoefficientLieComplexMap R L f M M' h) n ≫
      (nativeCoefficientHomologyIsoTor.{u, v', v, w} R L' M' n).hom =
        (nativeCoefficientHomologyIsoTor.{u, v, v', w} R L M n).hom ≫ nativeLieCoefficientTorMap R L f M M' h n := by
  have hH := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (nativeRightCoefficientComplexIso_lie_naturality R L f M M' h)
  simp only [HomologicalComplex.homologyMap_comp] at hH
  change HomologicalComplex.homologyMap (nativeCoefficientLieComplexMap R L f M M' h) n ≫
      (HomologicalComplex.homologyMap (nativeRightCoefficientComplexIso.{u, v', v, w} R L' M').hom n ≫ _) = _
  rw [← Category.assoc, hH, Category.assoc, rightCoefficientHomologyIsoTorAt_lie_naturality]
  rfl

end ResolutionComparison

end ChevalleyEilenberg
