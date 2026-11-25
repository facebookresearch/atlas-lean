/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), the module-sheafification argument:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: specialized to the quasisyntomic basis and integer coefficients.
-/
module

public import MathlibExt.AlgebraicGeometry.AbsolutePrismaticBasis
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import MathlibExt.CategoryTheory.FunctorialKInjective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Actual quasisyntomic Nygaard sheaves and cochain completion

The structural and filtered sheaves are sheafifications of actual
initial-prism rings and their actual ideal preimages. R-Gamma is the
right Kan-derived functor of their literal module-section limit.

Functorial K-injective resolutions are ordinary source integration.
Finite quotients are the native cones of the actual Nygaard inclusions;
their transition is the native map of the commuting arrow square.
The completed object is the literal Milnor fiber. This does not infer
the BMS scalar/twist convention from the name Nygaard.

References: Bhatt--Scholze arXiv:1905.08229v4, Theorem 1.14(3),
Sections 12--13; BMS arXiv:1802.03261v2, Theorem 1.12 and Section 7.
The sheafification proof adapts AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b, ProetaleComparison
(Apache 2.0), with the actual quasisyntomic basis and integer coefficients.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticNygaardCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open MathlibExt.RingTheory
open AbsolutePrismaticBasis
open PrismaticNygaardTowers
open MathlibExt.RingTheory.DerivedModuleScalarOperations

attribute [local instance] HasDerivedCategory.standard

/-- Native cone functoriality for an actual square sharing its target. -/
def coneSquareMap {C E F : Cochains ℤ} (f : C ⟶ F) (g : E ⟶ F)
    (a : C ⟶ E) (h : a ≫ g = f) :
    CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j : ℤ ↦ ⟨j - 1, by simp⟩)
    (Arrow.homMk a (𝟙 F) (by simpa using h))

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))

/-- Module sheafification on the actual basis site. -/
instance moduleSheafify : HasSheafify (topology p A) (ModuleCat.{1} ℤ) := by
  let : HasLimits (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} ℤ
  let : PreservesFilteredColimits (forget (ModuleCat.{1} ℤ)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (forget (ModuleCat.{1} ℤ)) := inferInstance
  infer_instance

/-- Actual module sheaves on the quasisyntomic basis. -/
abbrev Sheaves := Sheaf (topology p A) (ModuleCat.{1} ℤ)

/-- Sheafification of the actual initial delta rings. -/
def deltaSheaf : Sheaves p A :=
  (presheafToSheaf (topology p A) _).obj (deltaPresheaf p A D)

/-- Sheafification of the literal ideal-preimage Nygaard modules. -/
def nygaardSheaf (n : ℕ) : Sheaves p A :=
  (presheafToSheaf (topology p A) _).obj (nygaardPresheaf p A D n)

/-- The actual filtered inclusion after module sheafification. -/
def canSheaf (n : ℕ) : nygaardSheaf p A D n ⟶ deltaSheaf p A D :=
  (presheafToSheaf (topology p A) _).map (inclusion p A D n)

/-- Adjacent filtration maps retain the genuine ideal inclusions. -/
def stepPresheaf (n : ℕ) :
    nygaardPresheaf p A D (n + 1) ⟶ nygaardPresheaf p A D n where
  app B := ModuleCat.ofHom
    { toFun x := ULift.up ⟨x.down.val,
        nygaard_antitone p (D B.unop.unop).lift.prism.ring
          (D B.unop.unop).lift.prism.ideal (Nat.le_succ n) x.down.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality _ _ f := by ext x; rfl

/-- The actual adjacent sheaf filtration map. -/
def stepSheaf (n : ℕ) : nygaardSheaf p A D (n + 1) ⟶ nygaardSheaf p A D n :=
  (presheafToSheaf (topology p A) _).map (stepPresheaf p A D n)

/-- The filtration square commutes on every actual initial-ring element. -/
theorem stepSheaf_can (n : ℕ) : stepSheaf p A D n ≫ canSheaf p A D n =
    canSheaf p A D (n + 1) := by
  have h : stepPresheaf p A D n ≫ inclusion p A D n = inclusion p A D (n + 1) := by
    ext B x
    rfl
  let F := presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)
  exact (F.map_comp _ _).symm.trans (congrArg F.map h)

instance sectionLimits :
    HasLimitsOfShape ((Basis p A)ᵒᵖ)ᵒᵖ (ModuleCat.{1} ℤ) := by
  let : HasLimitsOfSize.{0, 1} (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfSize.{0, 1, 1, 0}
  infer_instance

/-- Literal module-section limits on this specified basis site. -/
def sections : Sheaves p A ⥤ ModuleCat.{1} ℤ :=
  sheafToPresheaf (topology p A) _ ⋙ lim.{0, 1, 1, 2}

instance sections_additive : (sections p A).Additive where
  map_add {F G} f g := by
    apply limit.hom_ext
    intro B
    change limMap (f.hom + g.hom) ≫ limit.π G.obj B =
      (limMap f.hom + limMap g.hom) ≫ limit.π G.obj B
    rw [Preadditive.add_comp]
    simp

/-- The actual sections source for its right-derived Kan functor. -/
def sectionsSource : CochainComplex (Sheaves p A) ℤ ⥤ DerivedCategory (ModuleCat.{1} ℤ) :=
  (sections p A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Generic derived existence on this fixed source, independent of any comparison theorem. -/
class HasDerivedSections : Prop where
  exists_derived : (sectionsSource p A).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaves p A) (ComplexShape.up ℤ))

attribute [instance] HasDerivedSections.exists_derived

/-- Actual quasisyntomic R-Gamma selected by its defining native Kan property. -/
def derivedSections [HasDerivedSections p A] :
    DerivedCategory (Sheaves p A) ⥤ DerivedCategory (ModuleCat.{1} ℤ) :=
  (sectionsSource p A).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaves p A) (ComplexShape.up ℤ))

/-- Derived sections of the actual delta sheaf. -/
def delta [HasDerivedSections p A] : DerivedCategory (ModuleCat.{1} ℤ) :=
  (derivedSections p A).obj
    ((DerivedCategory.singleFunctor (Sheaves p A) 0).obj (deltaSheaf p A D))

/-- The genuine Nygaard step, as derived sections of the actual preimage sheaf. -/
def nygaard [HasDerivedSections p A] (n : ℕ) : DerivedCategory (ModuleCat.{1} ℤ) :=
  (derivedSections p A).obj
    ((DerivedCategory.singleFunctor (Sheaves p A) 0).obj (nygaardSheaf p A D n))

/-- Its actual derived inclusion. -/
def can [HasDerivedSections p A] (n : ℕ) : nygaard p A D n ⟶ delta p A D :=
  (derivedSections p A).map
    ((DerivedCategory.singleFunctor (Sheaves p A) 0).map (canSheaf p A D n))

/-- A functorial K-injective resolution of cochain complexes of sheaves of abelian groups on the
semiperfectoid basis of the quasisyntomic site of $A$: an endofunctor $I$ of the category of such
complexes with a natural transformation $K \to I(K)$ from the identity that is a
quasi-isomorphism for every complex $K$, and such that every $I(K)$ is K-injective. -/
abbrev Resolution := FunctorialKInjective (Sheaves p A)

namespace Resolution

variable {p A D} (R : Resolution p A)

/-- Actual global sections of the resolved structural sheaf. -/
def deltaComplex : Cochains ℤ :=
  ((sections p A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (R.functor.obj
      ((HomologicalComplex.single (Sheaves p A) (ComplexShape.up ℤ) 0).obj
        (deltaSheaf p A D)))

/-- Actual global sections of the resolved Nygaard sheaf. -/
def nygaardComplex (n : ℕ) : Cochains ℤ :=
  ((sections p A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (R.functor.obj
      ((HomologicalComplex.single (Sheaves p A) (ComplexShape.up ℤ) 0).obj
        (nygaardSheaf p A D n)))

/-- The fixed resolved cochain inclusion. -/
def canComplex (n : ℕ) : R.nygaardComplex (D := D) n ⟶ R.deltaComplex (D := D) :=
  ((sections p A).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (R.functor.map
      ((HomologicalComplex.single (Sheaves p A) (ComplexShape.up ℤ) 0).map
        (canSheaf p A D n)))

/-- Adjacent cochain inclusions come from the same native source square. -/
def stepComplex (n : ℕ) :
    R.nygaardComplex (D := D) (n + 1) ⟶ R.nygaardComplex (D := D) n :=
  ((sections p A).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (R.functor.map
      ((HomologicalComplex.single (Sheaves p A) (ComplexShape.up ℤ) 0).map
        (stepSheaf p A D n)))

theorem stepComplex_can (n : ℕ) :
    R.stepComplex (D := D) n ≫ R.canComplex (D := D) n =
      R.canComplex (D := D) (n + 1) := by
  let F := HomologicalComplex.single (Sheaves p A) (ComplexShape.up ℤ) 0 ⋙
    R.functor ⋙ (sections p A).mapHomologicalComplex (ComplexShape.up ℤ)
  exact (F.map_comp _ _).symm.trans (congrArg F.map (stepSheaf_can p A D n))

/-- The actual finite derived Nygaard quotient is the native inclusion cone. -/
def quotientComplex (n : ℕ) : Cochains ℤ :=
  CochainComplex.mappingCone (R.canComplex (D := D) (n + 1))

/-- Native cone functoriality applied to the actual commuting filtration square. -/
def quotientTransition (n : ℕ) :
    R.quotientComplex (D := D) (n + 1) ⟶ R.quotientComplex (D := D) n :=
  coneSquareMap (R.canComplex (D := D) (n + 2))
    (R.canComplex (D := D) (n + 1)) (R.stepComplex (D := D) (n + 1))
      (R.stepComplex_can (D := D) (n + 1))

/-- The literal global quotient product complex. -/
abbrev productComplex := ∏ᶜ (R.quotientComplex (D := D))

/-- The real Milnor difference of the native adjacent quotient maps. -/
def difference : R.productComplex (D := D) ⟶ R.productComplex (D := D) :=
  Pi.lift (fun n ↦ Pi.π (R.quotientComplex (D := D)) n -
    Pi.π (R.quotientComplex (D := D)) (n + 1) ≫ R.quotientTransition (D := D) n)

/-- The actual complete filtered delta cochain carrier. -/
def completedDelta : Cochains ℤ :=
  CochainComplex.mappingCocone (R.difference (D := D))

/-- Its finite quotient projection is the native fiber projection. -/
def projection (n : ℕ) :
    R.completedDelta (D := D) ⟶ R.quotientComplex (D := D) n :=
  CochainComplex.mappingCocone.fst (R.difference (D := D)) ≫
    Pi.π (R.quotientComplex (D := D)) n

/-- Positive completed Nygaard steps are actual fibers of the quotient projections. -/
def completedNygaard (n : ℕ) : Cochains ℤ :=
  CochainComplex.mappingCocone (R.projection (D := D) n)

/-- Their actual inclusion into the native complete delta carrier. -/
def completedCan (n : ℕ) :
    R.completedNygaard (D := D) n ⟶ R.completedDelta (D := D) :=
  CochainComplex.mappingCocone.fst (R.projection (D := D) n)

end Resolution

end MathlibExt.AlgebraicGeometry.PrismaticNygaardCohomology
