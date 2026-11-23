/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
public import MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Proper flat complex families over arbitrary ordinary scheme tests

The source situation is an actual proper, flat, finitely presented
scheme morphism X to Y. Its tests are all schemes T over Y and its
complexes are actual small étale derived modules on X times_Y T.

Relative-perfect affine presentations use bounded complexes of finitely
presented B-modules flat over the actual chart coefficient ring A.
Pseudo-coherence is separately retained through finite perfect
approximations of that B-complex in every truncation. Terms need not
be projective over B, so this does not replace relative perfection by
absolute perfection when X over Y is singular. The affine source map
and the comparison with the native inverse image of E are both fixed.

The comparison from this presentation criterion to the pinned source's
pseudo-coherent plus finite relative Tor definition is an adaptation
proof request. AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
ComplexesStack.lean (0DLD/0DLE) and
Spaces/Perfect/RelativeSubcategory.lean (0DKN/0DKR).
This module covers general scheme source situations. The source's
algebraic-space extension is a distinct scope; no identity-only claim
is used to certify it.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperComplexFamilySources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The actual general scheme source situation of Stacks 0DLE. -/
structure ProperComplexesSituation where
  X : Scheme.{u}
  Y : Scheme.{u}
  f : X ⟶ Y
  proper : IsProper f
  flat : Flat f
  locallyFinitePresentation : LocallyOfFinitePresentation f
  quasiCompact : QuasiCompact f
  quasiSeparated : QuasiSeparated f

/-- All ordinary scheme tests over the actual base Y. -/
abbrev FamilyTest (D : ProperComplexesSituation.{u}) := Over D.Y

/-- The actual native fibre product X_T, rather than an independently chosen family space. -/
def familySpace (D : ProperComplexesSituation.{u}) (T : FamilyTest D) : Scheme.{u} :=
  pullback D.f T.hom

/-- The actual source projection X_T to T. -/
def familyProjection (D : ProperComplexesSituation.{u}) (T : FamilyTest D) : familySpace D T ⟶ T.left :=
  pullback.snd D.f T.hom

/-- Native base change on every coefficient/test arrow. -/
def familyMap {D : ProperComplexesSituation.{u}} {T T' : FamilyTest D} (h : T ⟶ T') :
    familySpace D T ⟶ familySpace D T' :=
  pullback.map D.f T.hom D.f T'.hom (𝟙 D.X) h.left (𝟙 D.Y)
    (by simp) (by simpa using Over.w h)

/-- The source arrow retains its native projection equation. -/
theorem familyMap_projection {D : ProperComplexesSituation.{u}} {T T' : FamilyTest D} (h : T ⟶ T') :
    familyMap h ≫ familyProjection D T' = familyProjection D T ≫ h.left := by
  simp [familyMap, familyProjection]

/-- Pseudo-coherence is measured by actual finite perfect approximations in every degree range. -/
def IsPseudoCoherentComplex (B : CommRingCat.{u}) (K : CochainComplex (ModuleCat.{u} B) ℤ) : Prop :=
  ∀ m : ℤ, ∃ P : StrictPerfectComplex B,
    ∃ a : DerivedCategory.Q.obj P.complex ⟶ DerivedCategory.Q.obj K,
      ∀ i : ℤ, m ≤ i → IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map a)

/-- A pseudo-coherent affine complex has a genuine finite-projective, bounded-above source resolution. -/
structure PseudoCoherentResolution (B : CommRingCat.{u}) (K : CochainComplex (ModuleCat.{u} B) ℤ) where
  complex : CochainComplex (ModuleCat.{u} B) ℤ
  upper : ℤ
  above : ∀ n : ℤ, upper < n → IsZero (complex.X n)
  finite : ∀ n : ℤ, Module.Finite B (complex.X n)
  projective : ∀ n : ℤ, Module.Projective B (complex.X n)
  augmentation : complex ⟶ K
  quasiIso : QuasiIso augmentation

/-- The ordinary tensor product with `M` of the scalar restriction of the resolution. It computes
the relative Tor complex `K ⊗ᴸ_A M` when `α` is flat (as in `IsCanonicalRelativePerfect`): the
restriction of a complex of projective `B`-modules is then a complex of flat `A`-modules. -/
def restrictedTensorComplex {A B : CommRingCat.{u}} (α : A ⟶ B)
    {K : CochainComplex (ModuleCat.{u} B) ℤ} (R : PseudoCoherentResolution B K)
    (M : ModuleCat.{u} A) : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj
    (((ModuleCat.restrictScalars α.hom).mapHomologicalComplex (.up ℤ)).obj R.complex)

/-- The actual pseudo-coherent plus finite relative Tor criterion, with flatness of the chart map retained. -/
def IsCanonicalRelativePerfect {A B : CommRingCat.{u}} (α : A ⟶ B)
    (_hflat : RingHom.Flat α.hom) (K : CochainComplex (ModuleCat.{u} B) ℤ) : Prop :=
  ∃ R : PseudoCoherentResolution B K, ∃ lower upper : ℤ,
    ∀ (M : ModuleCat.{u} A) (i : ℤ), i < lower ∨ upper < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) i).obj
        (restrictedTensorComplex α R M))

/-- A bounded relative-perfect affine presentation retains the actual A-action and pseudo-coherence over B. -/
structure RelativePerfectComplex {A B : CommRingCat.{u}} (α : A ⟶ B) where
  complex : CochainComplex (ModuleCat.{u} B) ℤ
  lower : ℤ
  upper : ℤ
  outside : ∀ n : ℤ, n < lower ∨ upper < n → IsZero (complex.X n)
  finitePresentation : ∀ n : ℤ, Module.FinitePresentation B (complex.X n)
  flat : ∀ n : ℤ, Module.Flat A ((ModuleCat.restrictScalars α.hom).obj (complex.X n))
  pseudoCoherent : IsPseudoCoherentComplex B complex

/-- A presentation comparison fixes the actual B-derived object, not a newly chosen perfect complex. -/
def HasRelativePerfectPresentation {A B : CommRingCat.{u}} (α : A ⟶ B)
    (K : CochainComplex (ModuleCat.{u} B) ℤ) : Prop :=
  ∃ P : RelativePerfectComplex α,
    Nonempty (DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj K)

/-- An affine presentation is attached to the actual projection, including its ring map and both open charts. -/
structure RelativeAffineChart {D : ProperComplexesSituation.{u}} (T : FamilyTest D) where
  A : CommRingCat.{u}
  B : CommRingCat.{u}
  coefficient : A ⟶ B
  baseOpen : Spec A ⟶ T.left
  sourceOpen : Spec B ⟶ familySpace D T
  base_openImmersion : IsOpenImmersion baseOpen
  source_openImmersion : IsOpenImmersion sourceOpen
  square : sourceOpen ≫ familyProjection D T = Spec.map coefficient ≫ baseOpen
  coefficient_flat : RingHom.Flat coefficient.hom

/-- A local criterion in the actual native source category, with every affine complex comparison specified. -/
def IsRelativelyPerfect {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (D : ProperComplexesSituation.{u}) (T : FamilyTest D)
    (E : EtaleDerived O (familySpace D T)) : Prop :=
  ∀ x : familySpace D T, ∃ C : RelativeAffineChart T,
    x ∈ Set.range C.sourceOpen ∧
    ∃ P : RelativePerfectComplex C.coefficient,
      Nonempty ((etaleDerivedPullback (L.derived C.sourceOpen)).obj E ≅
        associatedEtaleDerived (J C.B) P.complex)

/-- Source negative self-Ext uses actual field base changes of the same general situation. -/
def HasNoNegativeFibreExt {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (D : ProperComplexesSituation.{u}) (T : FamilyTest D)
    (E : EtaleDerived O (familySpace D T)) : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ T.left) (i : ℤ), i < 0 →
    let Ty : FamilyTest D := Over.mk (y ≫ T.hom)
    let h : Ty ⟶ T := Over.homMk y
    Subsingleton ((etaleDerivedPullback (L.derived (familyMap h))).obj E ⟶
      ((etaleDerivedPullback (L.derived (familyMap h))).obj E)⟦i⟧)

/-- The proper-X native source objects retain both relative perfection and the actual field Ext condition. -/
def ComplexesProperty {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (D : ProperComplexesSituation.{u}) (T : FamilyTest D) :
    ObjectProperty (EtaleDerived O (familySpace D T)) :=
  fun E => IsRelativelyPerfect L J D T E ∧ HasNoNegativeFibreExt L D T E

/-- The groupoid of actual relatively perfect derived objects and their actual isomorphisms. -/
abbrev ComplexesFibre {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (D : ProperComplexesSituation.{u}) (T : FamilyTest D) :=
  Core ((ComplexesProperty L J D T).FullSubcategory)

/-- Source pullback preservation concerns the actual familyMap operator and both source conditions. -/
structure ComplexesPullbackSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    {D : ProperComplexesSituation.{u}} {T T' : FamilyTest D} (h : T ⟶ T') : Prop where
  preserves : ∀ E : EtaleDerived O (familySpace D T'), ComplexesProperty L J D T' E →
    ComplexesProperty L J D T ((etaleDerivedPullback (L.derived (familyMap h))).obj E)

/-- The actual derived inverse image acts on the exact general-source objects and their arrows. -/
def complexesPullbackUnderlying {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A}
    {D : ProperComplexesSituation.{u}} {T T' : FamilyTest D} {h : T ⟶ T'}
    (H : ComplexesPullbackSource L J h) :
    (ComplexesProperty L J D T').FullSubcategory ⥤ (ComplexesProperty L J D T).FullSubcategory where
  obj E := ⟨(etaleDerivedPullback (L.derived (familyMap h))).obj E.obj, H.preserves E.obj E.property⟩
  map a := ObjectProperty.homMk ((etaleDerivedPullback (L.derived (familyMap h))).map a.hom)
  map_id E := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (familyMap h))).map_id E.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (familyMap h))).map_comp a.hom b.hom

/-- Native pullback on the actual groupoid fibres. -/
def complexesPullback {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A}
    {D : ProperComplexesSituation.{u}} {T T' : FamilyTest D} {h : T ⟶ T'}
    (H : ComplexesPullbackSource L J h) : ComplexesFibre L J D T' ⥤ ComplexesFibre L J D T :=
  (complexesPullbackUnderlying H).core

end MathlibExt.AlgebraicGeometry.ProperComplexFamilySources
