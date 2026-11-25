/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineCoefficientModules
public import MathlibExt.AlgebraicGeometry.FourierMukai
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Actual affine derived coefficient functors and their source comparison

The tilde functor is the native exact-functor localization. Derived scalar
extension is the native total left derived functor of termwise extension
of scalars. The Spec pullback is the fixed native scheme-module derived
pullback. Its comparison is normalized on every cochain by those actual
derived counits and the completed ordinary adjunction-unit comparison.
No assigned derived coefficient operator replaces these constructions.

The exactness/existence and comparison producers are completed-source
integration, AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Modules/TildeExactness.lean`,
`DerivedTilde/Basic.lean`, and
`Duality/DerivedTilde/AffineSchemePullbackComparison.lean` (Apache License 2.0).
Those files list no individual author or copyright notice. Adaptation:
use the preferred native Mathlib derived model, native exact-functor and
Kan-extension constructors, and the full native cochain counit square.
No duplicate Wanted is introduced for these completed generic producers.

The comparison applies to arbitrary complexes and affine ring maps.
There is no determinant-amplitude or relative-dimension restriction here.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open AffineCoefficientModules FourierMukai

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R S : CommRingCat.{u}} (g : R ⟶ S)

/-- Degreewise native sheafification of the actual module complex. -/
def tildeComplex (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (Spec R).Modules ℤ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- Degreewise native scalar extension of the actual module complex. -/
def scalarComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars g.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The cochain comparison uses the computed native module comparison in every degree. -/
def cochainComparison (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (tildeComplex R P) ≅ tildeComplex S (scalarComplex g P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (pullbackTildeIso g).app (P.X i))
    (by intro i j _; exact ((pullbackTildeIso g).hom.naturality (P.d i j)).symm)

/-- Exact component normalization, including all actual coefficient maps. -/
theorem cochainComparison_hom_f (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (cochainComparison g P).hom.f i = (pullbackTildeIso g).hom.app (P.X i) := rfl

/-- The fixed cochain source for genuine derived scalar extension. -/
def scalarExtensionSource : CochainComplex (ModuleCat.{u} R) ℤ ⥤
    DerivedCategory (ModuleCat.{u} S) :=
  (ModuleCat.extendScalars g.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The actual quasi-isomorphisms of module complexes. -/
abbrev ringQuasiIso (R : CommRingCat.{u}) :
    MorphismProperty (CochainComplex (ModuleCat.{u} R) ℤ) :=
  HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)

/-- Termwise extension of scalars has a left derived functor: an instance of this class asserts
that, for every homomorphism of commutative rings $g : R \to S$, the functor
`scalarExtensionSource g` from $\mathbb{Z}$-indexed cochain complexes of $R$-modules to the derived
category of $S$-modules (termwise extension of scalars along $g$, followed by the localization
functor) has a left derived functor with respect to quasi-isomorphisms. -/
class HasDerivedScalarExtensions : Prop where
  hasLeftDerivedFunctor : ∀ {R S : CommRingCat.{u}} (g : R ⟶ S),
    (scalarExtensionSource g).HasLeftDerivedFunctor (ringQuasiIso R)

attribute [instance] HasDerivedScalarExtensions.hasLeftDerivedFunctor

variable [HasDerivedScalarExtensions.{u}]

/-- The native total left derived functor of actual termwise scalar extension. -/
def derivedScalarExtension : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} S) :=
  (scalarExtensionSource g).totalLeftDerived DerivedCategory.Q (ringQuasiIso R)

/-- Its actual cochain counit. -/
def derivedScalarExtensionCounit :
    DerivedCategory.Q ⋙ derivedScalarExtension g ⟶ scalarExtensionSource g :=
  (scalarExtensionSource g).totalLeftDerivedCounit DerivedCategory.Q (ringQuasiIso R)

/-- Its defining universal property is the native left-derived property. -/
instance derivedScalarExtension_isLeftDerivedFunctor :
    (derivedScalarExtension g).IsLeftDerivedFunctor (derivedScalarExtensionCounit g)
      (ringQuasiIso R) := by
  dsimp only [derivedScalarExtension, derivedScalarExtensionCounit]
  infer_instance

/-- The derived tilde functor of a commutative ring $R$ whose tilde functor
$M \mapsto \widetilde{M}$, from $R$-modules to sheaves of modules on $\operatorname{Spec} R$,
preserves finite limits: the functor from the derived category of $R$-modules to the derived
category of sheaves of modules on $\operatorname{Spec} R$ induced by this exact functor
(`Functor.mapDerivedCategory`), which applies $\widetilde{(-)}$ termwise to cochain complexes. -/
def derivedTilde (R : CommRingCat.{u}) [PreservesFiniteLimits (tilde.functor R)] :
    DerivedCategory (ModuleCat.{u} R) ⥤ FourierMukai.D (Spec R) :=
  (tilde.functor R).mapDerivedCategory

/-- Its full cochain/object/map factorization is native exact-functor localization. -/
def derivedTildeFactors (R : CommRingCat.{u}) [PreservesFiniteLimits (tilde.functor R)] :
    DerivedCategory.Q ⋙ derivedTilde R ≅
      (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (tilde.functor R).mapDerivedCategoryFactors

variable [HasDerivedPullbacks.{u}]
  [PreservesFiniteLimits (tilde.functor R)] [PreservesFiniteLimits (tilde.functor S)]

/-- A comparison of derived pullback along $\operatorname{Spec} g$ with derived extension of scalars
along a homomorphism of commutative rings $g : R \to S$, given derived pullbacks, derived scalar
extensions, and tilde functors of $R$ and $S$ that preserve finite limits: a natural isomorphism
$L(\operatorname{Spec} g)^* \widetilde{K} \cong (S \otimes^{L}_R K)^\sim$ of functors from the
derived category of $R$-modules to the derived category of sheaves of modules on
$\operatorname{Spec} S$, such that for every cochain complex $P$ of $R$-modules the two resulting
maps $L(\operatorname{Spec} g)^* \widetilde{P} \to (S \otimes_R P)^\sim$ in the derived category
agree, where $\widetilde{P}$ and $S \otimes_R P$ are taken termwise: the counit of derived pullback
at $\widetilde{P}$ followed by the termwise isomorphism
$(\operatorname{Spec} g)^* \widetilde{P} \cong (S \otimes_R P)^\sim$ (`cochainComparison`), and this
natural isomorphism at $P$ followed by the derived tilde of the counit of derived scalar extension
at $P$. The derived tilde functors are identified with termwise tilde on complexes by
`derivedTildeFactors`. -/
structure DerivedComparison where
  comparison : derivedTilde R ⋙ derivedPullback (Spec.map g) ≅
    derivedScalarExtension g ⋙ derivedTilde S
  normalization : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
    (derivedPullback (Spec.map g)).map ((derivedTildeFactors R).hom.app P) ≫
      (derivedPullbackCounit (Spec.map g)).app (tildeComplex R P) ≫
      DerivedCategory.Q.map (cochainComparison g P).hom =
    comparison.hom.app (DerivedCategory.Q.obj P) ≫
      (derivedTilde S).map ((derivedScalarExtensionCounit g).app P) ≫
      (derivedTildeFactors S).hom.app (scalarComplex g P)

/-- The actual coefficient functor on an arbitrary affine scheme. -/
def affineTilde (T : Scheme.{u}) [IsAffine T] : ModuleCat.{u} Γ(T, ⊤) ⥤ T.Modules :=
  tilde.functor Γ(T, ⊤) ⋙ Scheme.Modules.pullback T.isoSpec.hom

/-- Its actual derived counterpart, with both canonical affine and derived pullbacks. -/
def affineDerivedTilde (T : Scheme.{u}) [IsAffine T]
    [PreservesFiniteLimits (tilde.functor Γ(T, ⊤))] :
    DerivedCategory (ModuleCat.{u} Γ(T, ⊤)) ⥤ FourierMukai.D T :=
  derivedTilde Γ(T, ⊤) ⋙ derivedPullback T.isoSpec.hom

end MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules
