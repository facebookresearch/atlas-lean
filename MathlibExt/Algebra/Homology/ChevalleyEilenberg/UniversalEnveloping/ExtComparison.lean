/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.LeftCochain
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Resolution
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.Ext.ProjectiveLinearComparison
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Enveloping Chevalley–Eilenberg cohomology and linear Ext

Under `Module.Free R L`, the enveloping Chevalley–Eilenberg complex resolves
the trivial module. A universe lift places that resolution and an independently
sized left coefficient module in a common module category, preserving
exactness and projectivity.

Unit/down coordinates compare the linear Yoneda cochains of the lifted
resolution with Hom from the unlifted complex. The resolution comparison
identifies the exterior-cochain homology with first-variable linear Ext.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The native universe lift of the original enveloping module category. -/
abbrev envelopingLiftFunctor : ModuleCat.{max u v} U ⥤ (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  ModuleCat.uliftFunctor.{w, max u v} U

local instance envelopingLift_preservesHomology :
    (envelopingLiftFunctor.{u, v, w} R L).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact ModuleCat.uliftFunctor_map_exact U S hS

/-- The original trivial module under the exact native universe lift. -/
abbrev liftedEnvelopingTrivial : (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  (envelopingLiftFunctor.{u, v, w} R L).obj (envelopingTrivialObject R L)

/-- The original native projective resolution mapped by the exact native
universe lift, retaining the mapped complex and augmentation. -/
def liftedEnvelopingProjectiveResolution [Module.Free R L] :
    ProjectiveResolution (liftedEnvelopingTrivial.{u, v, w} R L) :=
  (envelopingLiftFunctor.{u, v, w} R L).mapProjectiveResolution
    (envelopingProjectiveResolution R L)

@[simp]
theorem liftedEnvelopingProjectiveResolution_complex [Module.Free R L] :
    (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex =
      (((envelopingLiftFunctor.{u, v, w} R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (envelopingComplex R L)) := rfl

/-- The native mapped augmentation has the original augmentation's degree-zero image, by the
existing resolution precomposition API. -/
theorem liftedEnvelopingProjectiveResolution_π_f_zero [Module.Free R L] :
    (liftedEnvelopingProjectiveResolution.{u, v, w} R L).π.f 0 =
      (envelopingLiftFunctor.{u, v, w} R L).map ((envelopingAugmentation R L).f 0) :=
  ProjectiveResolution.mapProjectiveResolution_π_f_zero (envelopingLiftFunctor.{u, v, w} R L)
    (envelopingProjectiveResolution R L)

variable (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L))

/-- The original left coefficient module under the native common-universe lift. -/
abbrev liftedLeftCoefficient : (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) :=
  (ModuleCat.uliftFunctor.{max u v, w} U).obj M

/-- Hom coordinates between the native lifted module-category Hom
and Hom from the original CE carrier to the original coefficients. -/
def liftedEnvelopingHomCoordinates (n : ℕ) :
    ((envelopingLiftFunctor.{u, v, w} R L).obj ((envelopingComplex R L).X n) ⟶
      liftedLeftCoefficient R L M) ≃ₗ[R] envelopingHomTerm R L M n where
  toFun f :=
    (ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[U] M).toLinearMap.comp
      (f.hom.comp
        (ULift.moduleEquiv : ULift.{w} ((envelopingComplex R L).X n) ≃ₗ[U]
          (envelopingComplex R L).X n).symm.toLinearMap)
  invFun f := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{max u v} M ≃ₗ[U] M).symm.toLinearMap.comp
      (f.comp
        (ULift.moduleEquiv : ULift.{w} ((envelopingComplex R L).X n) ≃ₗ[U]
          (envelopingComplex R L).X n).toLinearMap))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply ULift.ext
    rfl
  right_inv f := by apply LinearMap.ext; intro z; rfl
  map_add' f g := by apply LinearMap.ext; intro z; rfl
  map_smul' r f := by apply LinearMap.ext; intro z; rfl

theorem liftedEnvelopingHomCoordinates_apply (n : ℕ)
    (f : (envelopingLiftFunctor.{u, v, w} R L).obj ((envelopingComplex R L).X n) ⟶
      liftedLeftCoefficient R L M) (z : (envelopingComplex R L).X n) :
    liftedEnvelopingHomCoordinates R L M n f z = (f.hom (ULift.up z)).down := rfl

/-- The native linear Yoneda cochain complex of the lifted original
projective resolution. -/
abbrev liftedEnvelopingHomComplex [Module.Free R L] :
    CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex.linearYonedaObj R
    (liftedLeftCoefficient R L M)

/-- Precomposition gives the outgoing Hom differential of the lifted resolution. -/
theorem liftedEnvelopingHomComplex_d_apply [Module.Free R L] (n : ℕ)
    (f : (liftedEnvelopingHomComplex R L M).X n) :
    ((liftedEnvelopingHomComplex R L M).d n (n + 1)).hom f =
      (liftedEnvelopingProjectiveResolution.{u, v, w} R L).complex.d (n + 1) n ≫ f := by
  let P := liftedEnvelopingProjectiveResolution.{u, v, w} R L
  let Y := liftedLeftCoefficient R L M
  have h := P.linearYonedaComplex_g_apply R Y n f
  change ((P.linearYonedaComplex R Y).d n ((ComplexShape.up ℕ).next n)).hom f =
    P.complex.d ((ComplexShape.up ℕ).next n) n ≫ f at h
  have hn : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
  rw [hn] at h
  exact h

/-- Native linear Yoneda of the lifted resolution compares with Hom of the original unlifted CE
complex, by the native up/down coordinates. -/
def liftedEnvelopingHomIso [Module.Free R L] :
    liftedEnvelopingHomComplex R L M ≅ envelopingHomComplex R L M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (liftedEnvelopingHomCoordinates R L M n).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      rw [envelopingHomComplex_d_succ]
      apply LinearMap.ext
      intro f
      change envelopingHomDifferential R L M i
        (liftedEnvelopingHomCoordinates R L M i f) =
        liftedEnvelopingHomCoordinates R L M (i + 1)
          (((liftedEnvelopingHomComplex R L M).d i (i + 1)).hom f)
      rw [liftedEnvelopingHomComplex_d_apply]
      ext z
      rfl)

/-- The original native first-variable linear Ext term with both original
module carriers lifted only by the canonical universe functor. -/
abbrev leftEnvelopingExt (n : ℕ) : ModuleCat.{max u v w} R :=
  ((_root_.Ext R (ModuleCat.{max u v w} (UniversalEnvelopingAlgebra R L)) n).obj
    (op (liftedEnvelopingTrivial.{u, v, w} R L))).obj
    (liftedLeftCoefficient R L M)

/-- Left-coefficient cohomology computes native linear Ext through
the original free-base enveloping CE resolution and the native universe lift. -/
def leftCoefficientHomologyIsoExt [Module.Free R L] (n : ℕ) :
    (leftCoefficientCochainComplex R L M).homology n ≅ leftEnvelopingExt R L M n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.up ℕ) n).mapIso
    (envelopingHomCoefficientIso R L M).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.up ℕ) n).mapIso
        (liftedEnvelopingHomIso R L M).symm ≪≫
          ((liftedEnvelopingProjectiveResolution.{u, v, w} R L).isoExt (R := R) n
            (liftedLeftCoefficient R L M)).symm

end ChevalleyEilenberg
