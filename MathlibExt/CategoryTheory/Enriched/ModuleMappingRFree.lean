/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRVariance
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeMappingEnd

/-!
# The actual noncommutative free-source right-translation end

Specialize the proved original free-right-module equalizer isomorphism to
the actual enriched Day category. Its target is the literal full end
`[F(j), N(j ⊗ c)]`. The forward map uses the original free generator; the
inverse uses the whole original parameterized extension, target action and
coefficient reassociation. All parameter Hom and complete source and target
arrows are retained. No commutativity law for the coefficient functor is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
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

/-- The literal original free right Day module, with no scalar commutativity premise. -/
def freeModule (F : EnrichedFunctorCat V I) : Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.freeObject (⟨S⟩ : EnrichedFunctorCat V I) F

/-- The literal original free-right-module generator, hence its original adjunction unit. -/
def freeUnit (F : EnrichedFunctorCat V I) :
    F ⟶ SphereModuleMappingEnd.diagram d S L (freeModule d S L F) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.freeGenerator (⟨S⟩ : EnrichedFunctorCat V I) F

/-- Every original source diagram arrow induces its actual complete free-module arrow. -/
def freeMap {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F) :
    freeModule d S L F' ⟶ freeModule d S L F := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.freeMap (⟨S⟩ : EnrichedFunctorCat V I) f

/-- The whole free-source mapping diagram is the original full right-translation end. -/
def freeSourceIso (F : EnrichedFunctorCat V I) (N : Module d S L) :
    diagram d b S L (freeModule d S L F) N ≅
      Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.freeSourceIso (⟨S⟩ : EnrichedFunctorCat V I) F N

/-- The original free-source value is compared at every unchanged parameter object. -/
def freeSourceValueIso (F : EnrichedFunctorCat V I) (N : Module d S L) (c : I) :
    value d b S L (freeModule d S L F) N c ≅
      Closed.object d F (SphereModuleMappingEnd.diagram d S L N) c :=
  (EnrichedFunctorCat.evaluation (V := V) c).mapIso (freeSourceIso d b S L F N)

/-- The whole original forward map restricts by the actual free generator after the inclusion. -/
theorem freeSourceIso_hom (F : EnrichedFunctorCat V I) (N : Module d S L) :
    (freeSourceIso d b S L F N).hom =
      ι d b S L (freeModule d S L F) N ≫
        Closed.pre d (freeUnit d S L F) (SphereModuleMappingEnd.diagram d S L N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := RightModuleMappingEnd.freeSourceIso_hom (⟨S⟩ : EnrichedFunctorCat V I) F N
  exact h.trans (congrArg (fun q => ι d b S L (freeModule d S L F) N ≫ q)
    (Closed.closedPre_eq d (freeUnit d S L F) (SphereModuleMappingEnd.diagram d S L N)))

/-- Every full free-source projection uses the original generator at the same source index. -/
@[reassoc]
theorem freeSourceIso_hom_π (F : EnrichedFunctorCat V I) (N : Module d S L) (c j : I) :
    component (freeSourceIso d b S L F N).hom c ≫
        Closed.π d F (SphereModuleMappingEnd.diagram d S L N) c j =
      π d b S L (freeModule d S L F) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d S L F) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) := by
  have h := congrArg (fun q => component q c) (freeSourceIso_hom d b S L F N)
  rw [component_comp] at h
  exact (congrArg (fun q => q ≫ Closed.π d F
    (SphereModuleMappingEnd.diagram d S L N) c j) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => valueι d b S L (freeModule d S L F) N c ≫ q)
        (Closed.pre_π d (freeUnit d S L F)
          (SphereModuleMappingEnd.diagram d S L N) c j)).trans
        (Category.assoc _ _ _).symm))

/-- Every value-isomorphism projection retains the same whole original generator restriction. -/
@[reassoc]
theorem freeSourceValueIso_hom_π (F : EnrichedFunctorCat V I) (N : Module d S L) (c j : I) :
    (freeSourceValueIso d b S L F N c).hom ≫
        Closed.π d F (SphereModuleMappingEnd.diagram d S L N) c j =
      π d b S L (freeModule d S L F) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d S L F) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) :=
  freeSourceIso_hom_π d b S L F N c j

/-- The original full parameterized free extension in the actual Day category. -/
def freeExtension (F P : EnrichedFunctorCat V I) (N : Module d S L)
    (q : Closed.tensorObject d F P ⟶ SphereModuleMappingEnd.diagram d S L N) :
    Closed.tensorObject d (SphereModuleMappingEnd.diagram d S L (freeModule d S L F)) P ⟶
      SphereModuleMappingEnd.diagram d S L N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.freeSourceExtension (⟨S⟩ : EnrichedFunctorCat V I) F P N q

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every full extension keeps the original coefficient reassociation and target right action. -/
theorem freeExtension_reassociation (F P : EnrichedFunctorCat V I) (N : Module d S L)
    (q : Closed.tensorObject d F P ⟶ SphereModuleMappingEnd.diagram d S L N) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    freeExtension d b S L F P N q =
      (α_ F (⟨S⟩ : EnrichedFunctorCat V I) P).hom ≫
        (F ◁ (β_ (⟨S⟩ : EnrichedFunctorCat V I) P).hom) ≫
        (α_ F P (⟨S⟩ : EnrichedFunctorCat V I)).inv ≫
        (q ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ SphereModuleMappingEnd.action d S L N := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.freeSourceExtension_reassociation
    (⟨S⟩ : EnrichedFunctorCat V I) F P N q

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every whole original coefficient arrow is recovered at the actual free generator. -/
@[reassoc]
theorem freeExtension_generator (F P : EnrichedFunctorCat V I) (N : Module d S L)
    (q : Closed.tensorObject d F P ⟶ SphereModuleMappingEnd.diagram d S L N) :
    letI := ColimitMonoidal.monoidalCategory d
    (freeUnit d S L F ▷ P) ≫ freeExtension d b S L F P N q = q := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.freeSourceExtension_generator
    (⟨S⟩ : EnrichedFunctorCat V I) F P N q

/-- The full inverse retains the original extension transpose under the actual inclusion. -/
@[reassoc]
theorem freeSourceIso_inv_ι (F : EnrichedFunctorCat V I) (N : Module d S L) :
    (freeSourceIso d b S L F N).inv ≫ ι d b S L (freeModule d S L F) N =
      Closed.transpose d (SphereModuleMappingEnd.diagram d S L (freeModule d S L F))
        (Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N))
        (SphereModuleMappingEnd.diagram d S L N)
        (freeExtension d b S L F
          (Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N)) N
          (Closed.evaluation d F (SphereModuleMappingEnd.diagram d S L N))) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := RightModuleMappingEnd.freeSourceIso_inv_ι (⟨S⟩ : EnrichedFunctorCat V I) F N
  let E := Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N)
  have he : (ihom.ev F).app (SphereModuleMappingEnd.diagram d S L N) =
      Closed.evaluation d F (SphereModuleMappingEnd.diagram d S L N) := by
    change (Closed.adjunction d F).counit.app (SphereModuleMappingEnd.diagram d S L N) = _
    exact Closed.adjunction_counit_app d F (SphereModuleMappingEnd.diagram d S L N)
  have hx := congrArg (fun q => MonoidalClosed.curry
    (RightModuleMappingEnd.freeSourceExtension (⟨S⟩ : EnrichedFunctorCat V I) F E N q)) he
  have hc : MonoidalClosed.curry
      (freeExtension d b S L F E N
        (Closed.evaluation d F (SphereModuleMappingEnd.diagram d S L N))) =
    Closed.transpose d (SphereModuleMappingEnd.diagram d S L (freeModule d S L F)) E
      (SphereModuleMappingEnd.diagram d S L N)
      (freeExtension d b S L F E N
        (Closed.evaluation d F (SphereModuleMappingEnd.diagram d S L N))) :=
    Closed.adjunction_homEquiv d
      (SphereModuleMappingEnd.diagram d S L (freeModule d S L F)) E
      (SphereModuleMappingEnd.diagram d S L N) _
  exact h.trans (hx.trans hc)

/-- The full original enriched parameter Hom action is preserved by the actual free-source iso. -/
@[reassoc]
theorem freeSourceIso_parameter (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c c' : I) :
    parameterAction d b S L (freeModule d S L F) N c c' ≫
        component (freeSourceIso d b S L F N).hom c' =
      (component (freeSourceIso d b S L F N).hom c ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        MonoidalClosed.uncurry
          ((Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N)).toEnrichedFunctor.map
            c c') :=
  (freeSourceIso d b S L F N).hom.uncurriedNaturality c c'

/-- Every complete original free-module source arrow is restricted through its actual generator. -/
@[reassoc]
theorem freeSourceIso_sourceArrow {F F' : EnrichedFunctorCat V I}
    (f : freeModule d S L F' ⟶ freeModule d S L F) (N : Module d S L) :
    pre d b S L f N ≫ (freeSourceIso d b S L F' N).hom =
      ι d b S L (freeModule d S L F) N ≫
        Closed.pre d (freeUnit d S L F' ≫ SphereModuleMappingEnd.moduleMap d S L f)
          (SphereModuleMappingEnd.diagram d S L N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have h := RightModuleMappingEnd.freeSourceForward_pre (⟨S⟩ : EnrichedFunctorCat V I) f N
  exact h.trans (congrArg (fun q => ι d b S L (freeModule d S L F) N ≫ q)
    (Closed.closedPre_eq d (freeUnit d S L F' ≫ SphereModuleMappingEnd.moduleMap d S L f)
      (SphereModuleMappingEnd.diagram d S L N)))

/-- Every complete original target module arrow is retained by the whole free-source iso. -/
@[reassoc]
theorem freeSourceIso_target (F : EnrichedFunctorCat V I) {N N' : Module d S L} (g : N ⟶ N') :
    post d b S L (freeModule d S L F) g ≫ (freeSourceIso d b S L F N').hom =
      (freeSourceIso d b S L F N).hom ≫
        (Closed.rightFunctor d F).map (SphereModuleMappingEnd.moduleMap d S L g) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleMappingEnd.freeSourceForward_naturality_target
    (⟨S⟩ : EnrichedFunctorCat V I) F g

/-- The full actual free-source value represents every genuine V-parameter family. -/
def freeValueParameterEquiv (F : EnrichedFunctorCat V I) (N : Module d S L) (c : I) (P : V) :
    (P ⟶ value d b S L (freeModule d S L F) N c) ≃
      GradedNatTrans ((Center.ofBraided V).obj P) F.toEnrichedFunctor
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor :=
  ((Iso.refl P).homCongr (freeSourceValueIso d b S L F N c)).trans
    (GradingConvention.endHomEquiv F.toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor P)

/-- Every represented complete V-parameter family retains the original free-source forward map. -/
theorem freeValueParameterEquiv_apply (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) {P : V} (f : P ⟶ value d b S L (freeModule d S L F) N c) :
    freeValueParameterEquiv d b S L F N c P f =
      GradingConvention.endToPositive F.toEnrichedFunctor
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
        (f ≫ (freeSourceValueIso d b S L F N c).hom) := by
  simp only [freeValueParameterEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp, GradingConvention.endHomEquiv_apply]

/-- The complete inverse V-family map is the actual inverse original free-source isomorphism. -/
theorem freeValueParameterEquiv_symm_apply (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) {P : V} (t : GradedNatTrans ((Center.ofBraided V).obj P) F.toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    (freeValueParameterEquiv d b S L F N c P).symm t =
      GradingConvention.endFromPositive F.toEnrichedFunctor
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor t ≫
        (freeSourceValueIso d b S L F N c).inv := by
  change (Iso.refl P).hom ≫
    (GradingConvention.endHomEquiv F.toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor
      P).symm t ≫ (freeSourceValueIso d b S L F N c).inv = _
  rw [Iso.refl_hom, Category.id_comp, GradingConvention.endHomEquiv_symm_apply]

/-- Every original free-source V-family projection retains its complete j component. -/
theorem freeValueParameterEquiv_app (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) {P : V} (f : P ⟶ value d b S L (freeModule d S L F) N c) (j : I) :
    (freeValueParameterEquiv d b S L F N c P f).app j =
      (f ≫ (freeSourceValueIso d b S L F N c).hom) ≫
        Closed.π d F (SphereModuleMappingEnd.diagram d S L N) c j := by
  rw [freeValueParameterEquiv_apply]
  exact GradingConvention.endToPositive_app_symmetric _ _ _ j

/-- All original coefficient arrows are retained by the whole free-source V-family map. -/
theorem freeValueParameterEquiv_regrade (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) {P Q : V} (r : P ⟶ Q) (f : Q ⟶ value d b S L (freeModule d S L F) N c) :
    freeValueParameterEquiv d b S L F N c P (r ≫ f) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r)
        (freeValueParameterEquiv d b S L F N c Q f) := by
  rw [freeValueParameterEquiv_apply, Category.assoc, GradingConvention.endToPositive_naturality,
    freeValueParameterEquiv_apply]

end CategoryTheory.Enriched.ModuleMappingR
