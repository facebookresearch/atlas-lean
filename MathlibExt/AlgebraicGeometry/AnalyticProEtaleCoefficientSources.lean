/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites
public import MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
public import MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Actual analytic pro-etale coefficient and structure sheaves

The site is the full formal pro-object site of the published analytic
model, with the BMS18 transfinite covering topology. Continuous integral
and rational coefficients are literal continuous functions on its actual
point limits. The rational carrier permits all locally continuous `Q_p`
sections on every object.

The regular structure is the native inverse image of the ORIGINAL etale
global-section sheaf. Positive etale sections are subrings of those
original rings, fixed by every original stalk valuation. Nilpotents remain
elements of the section rings.

References: Scholze, arXiv:1205.3463v2, Definitions 3.9, 6.1 and 6.8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1. The etale global
ring functor is adapted from this repository's
`FormalNearbyCycleModels.analyticEtaleRings`, commit
`8b07dc902f707a43fa2d01f11e7a196910cfa9a3`. Native sheaf-module and
continuous-function constructions use Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticProEtaleCoefficientSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticDiamondEtaleSites AnalyticProObjectSites
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations

/-- Raise the coefficient universe without changing any original ring operation. -/
def liftRings : CommRingCat.{0} ⥤ CommRingCat.{1} where
  obj R := CommRingCat.of (ULift.{1} R)
  map f := CommRingCat.ofHom
    { toFun := fun x => ULift.up (f.hom x.down)
      map_one' := by apply ULift.ext; exact map_one f.hom
      map_mul' x y := by apply ULift.ext; exact map_mul f.hom x.down y.down
      map_zero' := by apply ULift.ext; exact map_zero f.hom
      map_add' x y := by apply ULift.ext; exact map_add f.hom x.down y.down }
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

variable (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p)

abbrev Etale := AnalyticProObjectSites.Etale p X
abbrev Proetale := AnalyticProObjectSites.ProEtaleSite p X

/-- The original etale coefficient rings are native global sections. -/
def etaleRings : (Etale p X)ᵒᵖ ⥤ CommRingCat.{0} :=
  (ObjectProperty.ι _ ⋙ Over.forget X ⋙ ObjectProperty.ι (HasAnalyticAtlas p) ⋙
    forgetValuations).op ⋙ LocallyRingedSpace.Γ

def etaleRingsLarge : (Etale p X)ᵒᵖ ⥤ CommRingCat.{1} :=
  etaleRings p X ⋙ liftRings

/-- The regular etale sheaf is fixed on every original object and arrow. -/
def regularEtale (h : Presheaf.IsSheaf (analyticEtaleTopology p X) (etaleRingsLarge p X)) :
    Sheaf (analyticEtaleTopology p X) CommRingCat.{1} :=
  ⟨etaleRingsLarge p X, h⟩

/-- Integrality is tested in every actual original stalk valuation. -/
def integralSection (U : (Etale p X)ᵒᵖ) (a : (etaleRings p X).obj U) : Prop :=
  ∀ x : U.unop.obj.left.obj.space,
    (U.unop.obj.left.obj.valuation x).vle
      (U.unop.obj.left.obj.space.presheaf.germ ⊤ x (by trivial) a) 1

/-- The positive rings remain subrings of the original native section rings. -/
structure IntegralStructure where
  rings : ∀ U : (Etale p X)ᵒᵖ, Subring ((etaleRings p X).obj U)
  membership : ∀ (U : (Etale p X)ᵒᵖ) (a : (etaleRings p X).obj U),
    a ∈ rings U ↔ integralSection p X U a
  restrict : ∀ {U V : (Etale p X)ᵒᵖ} (f : U ⟶ V) (a : (etaleRings p X).obj U),
    a ∈ rings U → ((etaleRings p X).map f).hom a ∈ rings V

namespace IntegralStructure

variable (A : IntegralStructure p X)

def presheaf : (Etale p X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj U := CommRingCat.of (A.rings U)
  map f := CommRingCat.ofHom
    { toFun := fun a => ⟨((etaleRings p X).map f).hom a.val, A.restrict f a.val a.property⟩
      map_one' := by apply Subtype.ext; exact map_one _
      map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _ }
  map_id U := by ext a; simp
  map_comp f g := by ext a; simp

def inclusion : A.presheaf ⟶ etaleRings p X where
  app U := CommRingCat.ofHom (A.rings U).subtype
  naturality {U V} f := by ext a; rfl

def positiveEtale
    (h : Presheaf.IsSheaf (analyticEtaleTopology p X) (A.presheaf ⋙ liftRings)) :
    Sheaf (analyticEtaleTopology p X) CommRingCat.{1} :=
  ⟨A.presheaf ⋙ liftRings, h⟩

end IntegralStructure

variable (P : AnalyticProObjectSites.PointRealization p X)

abbrev proTopology := AnalyticProObjectSites.bmsTopology p X P
abbrev etaleInclusion := AnalyticProObjectSites.etaleEmbedding p X

/-- Continuous coefficients on every actual formal pro-object point limit. -/
def continuousRings (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] : (Proetale p X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj U := CommRingCat.of C(P.functor.obj U.unop, E)
  map f := CommRingCat.ofHom
    { toFun := fun a => a.comp (P.functor.map f.unop).hom
      map_one' := by ext x; rfl
      map_mul' a b := by ext x; rfl
      map_zero' := by ext x; rfl
      map_add' a b := by ext x; rfl }
  map_id U := by ext a x; simp
  map_comp f g := by ext a x; simp

variable [HasSheafify (proTopology p X P) CommRingCat.{1}]

def continuousCoefficientSheaf (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] : Sheaf (proTopology p X P) CommRingCat.{1} :=
  (presheafToSheaf (proTopology p X P) CommRingCat.{1}).obj
    (continuousRings p X P E ⋙ liftRings)

/-- Actual continuous integral p-adic coefficients. -/
def Zhat : Sheaf (proTopology p X P) CommRingCat.{1} :=
  continuousCoefficientSheaf p X P ℤ_[p]

/-- Actual continuous rational coefficients; the carrier has no chosen integral lattice. -/
def Qhat : Sheaf (proTopology p X P) CommRingCat.{1} :=
  continuousCoefficientSheaf p X P ℚ_[p]

variable [(etaleInclusion p X).IsContinuous (analyticEtaleTopology p X) (proTopology p X P)]
  [((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
    (analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint]

/-- The original structure sheaf is pulled back before any completion. -/
def originalStructure
    (h : Presheaf.IsSheaf (analyticEtaleTopology p X) (etaleRingsLarge p X)) :
    Sheaf (proTopology p X P) CommRingCat.{1} :=
  ((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
    (analyticEtaleTopology p X) (proTopology p X P)).leftAdjoint.obj (regularEtale p X h)

def originalPositive (A : IntegralStructure p X)
    (h : Presheaf.IsSheaf (analyticEtaleTopology p X) (A.presheaf ⋙ liftRings)) :
    Sheaf (proTopology p X P) CommRingCat.{1} :=
  ((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
    (analyticEtaleTopology p X) (proTopology p X P)).leftAdjoint.obj
      (IntegralStructure.positiveEtale (p := p) (X := X) (A := A) h)

end MathlibExt.AlgebraicGeometry.AnalyticProEtaleCoefficientSources

namespace MathlibExt.CategoryTheory.FiniteLocallyFreeSource

open _root_.CategoryTheory
open RingedDerivedCoefficientOperations

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{1}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (S : Sheaf J CommRingCat.{1})

/-- Finite local freeness uses the native local generator covers and every local arrow. -/
def IsFiniteLocallyFree (M : Modules S) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{1} M,
    q.IsLocallyFreeData ∧ ∀ i : q.I, Finite (q.generators i).I

end MathlibExt.CategoryTheory.FiniteLocallyFreeSource
