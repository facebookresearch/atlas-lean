/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralEtalePullbackCoherence
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections

/-!
# Full coherent étale coefficient families and categorical section limits

The raw category is the native Grothendieck category of the entire
cochain inverse-image pseudofunctor. Weak maps are actual base
isomorphisms with quasi-isomorphic native coefficient maps. The enhanced
family is characterized by the full categorical localization of this
raw source and its cocartesian projection; no space core is used.

Constructible/amplitude vertices refer to the actual source complexes
through the object-preserving localization model. Their full enhanced
subcategory retains all noninvertible parameter maps. Categorical limits
are the native cocartesian section objects of these full families.

Source: Bhatt--Mathew arXiv:1807.04725v4, Notation 5.8 and Theorem 5.13;
Lurie, HTT, Sections 2.4/3.3; native Grothendieck and coherent section models.
Construction, native K-injective comparison and hyperdescent are separate goals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralEtaleCoherentFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open DerivedCoefficientImageModels SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open scoped Simplicial

variable (Λ : Type) [Ring Λ]
  [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), EtalePullbackSource Λ f)
  (U : ∀ X : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource X)
  (C : CoefficientPseudofunctorSource Λ S U)

/-- The source family's actual complex, using the prescribed category equality. -/
def sourceComplex (a : CoefficientFamilies Λ S U C) :
    CoefficientComplexes Λ a.base.unop.scheme :=
  (eqToHom (C.object a.base)).toFunctor.obj a.fiber

/-- The literal weak maps of the entire coefficient Grothendieck category. -/
def IsFamilyWeak {a b : CoefficientFamilies Λ S U C} (f : a ⟶ b) : Prop :=
  IsIso f.base ∧ QuasiIso ((eqToHom (C.object b.base)).toFunctor.map f.fiber)

/-- Actual base nerve in the universe of the full enhanced coefficient category. -/
abbrev BaseSet : SSet.{2} := liftSet.{1, 2} (nerve QcqsSchemeᵒᵖ)

/-- Every source/base joint simplex is projected by the actual native forget functor. -/
def sourceBaseMap : nerve (CoefficientFamilies Λ S U C) ⟶ BaseSet where
  app n := ↾fun a => ULift.up (a ⋙ familyProjection Λ S U C)
  naturality n m f := by
    ext a
    apply congrArg ULift.up
    rfl

/-- The full functor-space condition of inverting actual weak source maps. -/
def InvertsFamilyWeak (Z : SSet.{2})
    (a : (mapping (nerve (CoefficientFamilies Λ S U C)) Z) _⦋0⦌) : Prop :=
  ∀ (x y : CoefficientFamilies Λ S U C) (f : x ⟶ y), IsFamilyWeak Λ S U C f →
    IsEquivalenceEdge Z (((SimplicialCategory.homEquiv' _ _).symm a).app (op ⦋1⦌)
      (nerve.edgeMk f).edge)

/-- A native full derived family is a categorical localization of this
entire native source, with actual cocartesian base change. The chosen
object-preserving model is the standard simplicial-localization form.
There is no constructible, arc or hyperdescent conclusion inside it. -/
structure DerivedCoefficientFamily where
  total : SSet.{2}
  projection : total ⟶ BaseSet
  source : nerve (CoefficientFamilies Λ S U C) ⟶ total
  base_eq : source ≫ projection = sourceBaseMap Λ S U C
  quasicategory : SSet.Quasicategory total
  cocartesian : CocartesianFibration projection
  source_objects : Function.Bijective (source.app (op ⦋0⦌))
  invert : ∀ (x y : CoefficientFamilies Λ S U C) (f : x ⟶ y), IsFamilyWeak Λ S U C f →
    IsEquivalenceEdge total (source.app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (Z : SSet.{2}) [SSet.Quasicategory Z],
    ∃ f : mapping total Z ⟶
      ((mapping (nerve (CoefficientFamilies Λ S U C)) Z).fullEnhancedSubcategory
        (InvertsFamilyWeak Λ S U C Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition source Z ∧
        CategoricalWeakEquivalence f

variable (D : DerivedCoefficientFamily Λ S U C)

/-- A vertex is an actual source family object through the specified
object-preserving localization, not an independently supplied module. -/
def representative (x : D.total _⦋0⦌) : CoefficientFamilies Λ S U C :=
  ((Equiv.ofBijective (D.source.app (op ⦋0⦌)) D.source_objects).symm x).obj 0

/-- Constructibility is the actual source complex's finite-stratum cohomology. -/
def IsConstructibleVertex (x : D.total _⦋0⦌) : Prop :=
  IsBoundedConstructible Λ S (representative Λ S U C D x).base.unop
    (sourceComplex Λ S U C (representative Λ S U C D x))

/-- The native full bounded constructible enhanced family; parameter
morphisms retain all noninvertible homogeneous module maps. -/
abbrev constructibleFamily : SSet.{2} :=
  (D.total.fullEnhancedSubcategory (IsConstructibleVertex Λ S U C D)).toSSet

/-- Its actual projection onto the qcqs scheme base. -/
def constructibleProjection : constructibleFamily Λ S U C D ⟶ BaseSet :=
  (D.total.fullEnhancedSubcategory (IsConstructibleVertex Λ S U C D)).ι ≫ D.projection

/-- The cohomological-amplitude condition on these same actual complexes. -/
def IsAmplitudeVertex (a b : ℤ) (x : D.total _⦋0⦌) : Prop :=
  IsConstructibleVertex Λ S U C D x ∧
    InAmplitude Λ (sourceComplex Λ S U C (representative Λ S U C D x)) a b

/-- Native full fixed-amplitude family, without replacing it by a core space. -/
abbrev amplitudeFamily (a b : ℤ) : SSet.{2} :=
  (D.total.fullEnhancedSubcategory (IsAmplitudeVertex Λ S U C D a b)).toSSet

/-- A small scheme diagram induces its full native value-lifted base map. -/
def diagramBaseMap {J : Type} [Category.{0} J] (H : J ⥤ QcqsSchemeᵒᵖ) :
    liftSet.{0, 2} (nerve J) ⟶ BaseSet where
  app n := ↾fun a => ULift.up (a.down ⋙ H)
  naturality n m f := by
    ext a
    apply congrArg ULift.up
    rfl

/-- The full categorical derived limit of a constructible coefficient diagram. -/
def constructibleLimit {J : Type} [Category.{0} J] (H : J ⥤ QcqsSchemeᵒᵖ) : SSet.{2} :=
  sectionsOver (constructibleProjection Λ S U C D) (diagramBaseMap H)

end MathlibExt.AlgebraicGeometry.GeneralEtaleCoherentFamilies
