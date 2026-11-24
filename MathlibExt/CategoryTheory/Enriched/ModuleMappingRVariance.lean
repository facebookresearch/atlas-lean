/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingR
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedMaps

/-!
# Both full original variances of the translated action equalizer

The source diagram retains the whole original action equalizer. Complete
source and target module arrows act on every original end projection, at the
literal index `j tensor c`, and form its genuine diagram-valued bifunctor.
No commutativity of the coefficient monoid or module-valued output is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- Every full original source-module arrow acts on the same raw translated equalizer. -/
def pre {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    diagram d b S L M N ⟶ diagram d b S L M' N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.pre (⟨S⟩ : EnrichedFunctorCat V I) f N

/-- Every full original target-module arrow acts on the same raw translated equalizer. -/
def post (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    diagram d b S L M N ⟶ diagram d b S L M N' := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.post (⟨S⟩ : EnrichedFunctorCat V I) M g

/-- Every raw source map retains the whole original source carrier at the ambient end. -/
@[reassoc]
theorem pre_ι {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L) :
    pre d b S L f N ≫ ι d b S L M' N =
      ι d b S L M N ≫ Closed.pre d (SphereModuleMappingEnd.moduleMap d S L f)
        (SphereModuleMappingEnd.diagram d S L N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := RightModuleMappingEnd.pre_ι (⟨S⟩ : EnrichedFunctorCat V I) f N
  exact h.trans (congrArg (fun q => ι d b S L M N ≫ q)
    (Closed.closedPre_eq d (SphereModuleMappingEnd.moduleMap d S L f)
      (SphereModuleMappingEnd.diagram d S L N)))

/-- Every raw target map retains the whole original translated target carrier map. -/
@[reassoc]
theorem post_ι (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    post d b S L M g ≫ ι d b S L M N' =
      ι d b S L M N ≫ (Closed.rightFunctor d (SphereModuleMappingEnd.diagram d S L M)).map
        (SphereModuleMappingEnd.moduleMap d S L g) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.post_ι (⟨S⟩ : EnrichedFunctorCat V I) M g

/-- Every original source map precomposes the full right-translation component. -/
@[reassoc]
theorem pre_π {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L) (c j : I) :
    component (pre d b S L f N) c ≫ π d b S L M' N c j =
      π d b S L M N c j ≫
        (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) := by
  have h := congrArg (fun q => component q c) (pre_ι d b S L f N)
  rw [component_comp, component_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ Closed.π d (SphereModuleMappingEnd.diagram d S L M')
      (SphereModuleMappingEnd.diagram d S L N) c j) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => valueι d b S L M N c ≫ q)
          (Closed.pre_π d (SphereModuleMappingEnd.moduleMap d S L f)
            (SphereModuleMappingEnd.diagram d S L N) c j)).trans
          (Category.assoc _ _ _).symm)))

/-- Every original target arrow postcomposes at the unchanged literal index `j ⊗ c`. -/
@[reassoc]
theorem post_π (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') (c j : I) :
    component (post d b S L M g) c ≫ π d b S L M N' c j =
      π d b S L M N c j ≫
        (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).map
          (component (SphereModuleMappingEnd.moduleMap d S L g) (j ⊗ c)) := by
  have h := congrArg (fun q => component q c) (post_ι d b S L M g)
  rw [component_comp, component_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ Closed.π d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N') c j) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => valueι d b S L M N c ≫ q)
          (Closed.rightMap_π d (SphereModuleMappingEnd.diagram d S L M)
            (SphereModuleMappingEnd.moduleMap d S L g) c j)).trans
          (Category.assoc _ _ _).symm)))

/-- The whole raw translated source map preserves the complete original identity. -/
@[simp]
theorem pre_id (M N : Module d S L) : pre d b S L (𝟙 M) N = 𝟙 (diagram d b S L M N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.pre_id (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- The whole raw translated target map preserves the complete original identity. -/
@[simp]
theorem post_id (M N : Module d S L) : post d b S L M (𝟙 N) = 𝟙 (diagram d b S L M N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.post_id (⟨S⟩ : EnrichedFunctorCat V I) M N

/-- Every original contravariant source composition is retained on the complete diagram. -/
theorem pre_comp {M M' M'' : Module d S L} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : Module d S L) : pre d b S L (g ≫ f) N = pre d b S L f N ≫ pre d b S L g N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.pre_comp (⟨S⟩ : EnrichedFunctorCat V I) f g N

/-- Every original covariant target composition is retained on the complete diagram. -/
theorem post_comp (M : Module d S L) {N N' N'' : Module d S L} (f : N ⟶ N') (g : N' ⟶ N'') :
    post d b S L M (f ≫ g) = post d b S L M f ≫ post d b S L M g := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.post_comp (⟨S⟩ : EnrichedFunctorCat V I) M f g

/-- Both whole original variances commute without commutative coefficients. -/
theorem pre_post {M M' N N' : Module d S L} (f : M' ⟶ M) (g : N ⟶ N') :
    pre d b S L f N ≫ post d b S L M' g = post d b S L M g ≫ pre d b S L f N' := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.pre_post (⟨S⟩ : EnrichedFunctorCat V I) f g

/-- The actual raw translated equalizer and all complete target arrows form a functor. -/
def diagramFunctor (M : Module d S L) : Module d S L ⥤ EnrichedFunctorCat V I where
  obj := diagram d b S L M
  map := post d b S L M
  map_id := post_id d b S L M
  map_comp := post_comp d b S L M

/-- Every complete original source arrow gives its actual target-natural raw end map. -/
def diagramSourceMap {M M' : Module d S L} (f : M' ⟶ M) :
    diagramFunctor d b S L M ⟶ diagramFunctor d b S L M' where
  app := pre d b S L f
  naturality _ _ g := (pre_post d b S L f g).symm

/-- The whole raw translated source mapping diagram is a bifunctor without commutativity. -/
def diagramBifunctor : (Module d S L)ᵒᵖ ⥤ (Module d S L ⥤ EnrichedFunctorCat V I) where
  obj M := diagramFunctor d b S L M.unop
  map f := diagramSourceMap d b S L f.unop
  map_id M := by
    apply NatTrans.ext
    funext N
    exact pre_id d b S L M.unop N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    exact pre_comp d b S L f.unop g.unop N

end CategoryTheory.Enriched.ModuleMappingR
