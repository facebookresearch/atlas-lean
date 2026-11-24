/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAction

/-!
# Coefficient-first families of the translated Mapping_R end

The represented families have the literal MMSS order `P ⊗ M(j) → N(j ⊗ c)`.
Their action balance is the coefficient-first form of the proved complete
action equalizer condition. The conversion uses the actual value braiding;
the target action retains the original index crossing κ.

All maps below act on the genuine represented end. They include every
coefficient arrow, complete original source and target module arrows, and
the entire parameter Hom. The coefficient monoid need not be commutative.
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

private theorem parameter_first_shuffle
    {C : Type uV} [Category.{vV} C] [MonoidalCategory C] [SymmetricCategory C]
    (P X A : C) :
    (β_ P (X ⊗ A)).hom ≫ coefficientSwap X A P =
      (α_ P X A).inv ≫ ((β_ P X).hom ▷ A) := by
  dsimp only [coefficientSwap]
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id,
    Category.id_comp]
  simp only [Iso.hom_inv_id, Category.comp_id]

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

/-- The actual coefficient-first component of every complete represented family. -/
abbrev Family.evaluation {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j : I) :
    P ⊗ (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j ⟶
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c) :=
  GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) q.transformation j

/-- The order conversion retains the original value braid and the whole curried component. -/
theorem Family.evaluation_eq {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j : I) :
    q.evaluation d b S L j =
      (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).hom ≫
        MonoidalClosed.uncurry (q.transformation.app j) := rfl

/-- Every represented component has full enriched source-Hom naturality. -/
theorem Family.evaluation_naturality {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j k : I) :
    (α_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      (j ⟶[V] k)).hom ≫
      (P ◁ MonoidalClosed.uncurry
        ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.map j k)) ≫
      q.evaluation d b S L k =
    (q.evaluation d b S L j ▷ (j ⟶[V] k)) ≫
      MonoidalClosed.uncurry
        ((Closed.translatedTarget d
          (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor.map j k) :=
  GradedNatTrans.gradeFirstComponent_naturality ((Center.ofBraided V).obj P)
    q.transformation j k

/-- The exact coefficient-first MMSS balance retains the original source action,
target action and index κ, for every source/coefficient pair. -/
theorem Family.evaluation_action_balance {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j a : I) :
    (P ◁ ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.action d S L M) j a) ≫ q.evaluation d b S L (j ⊗ a) =
    (α_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      (S.obj a)).inv ≫
      (q.evaluation d b S L j ▷ S.obj a) ≫ translatedAction d S L N c j a := by
  let X := (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j
  let sm := ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
    (SphereModuleMappingEnd.action d S L M) j a
  have hq := q.action_balance d b S L j a
  rw [Family.evaluation_eq, Family.evaluation_eq]
  calc
    _ = (β_ P (X ⊗ S.obj a)).hom ≫ (sm ▷ P) ≫
        MonoidalClosed.uncurry (q.transformation.app (j ⊗ a)) :=
      braiding_naturality_right_assoc P sm
        (MonoidalClosed.uncurry (q.transformation.app (j ⊗ a)))
    _ = (β_ P (X ⊗ S.obj a)).hom ≫ coefficientSwap X (S.obj a) P ≫
        (MonoidalClosed.uncurry (q.transformation.app j) ▷ S.obj a) ≫
        translatedAction d S L N c j a :=
      congrArg (fun z => (β_ P (X ⊗ S.obj a)).hom ≫ z) hq
    _ = (α_ P X (S.obj a)).inv ≫ ((β_ P X).hom ▷ S.obj a) ≫
        (MonoidalClosed.uncurry (q.transformation.app j) ▷ S.obj a) ≫
        translatedAction d S L N c j a := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        (MonoidalClosed.uncurry (q.transformation.app j) ▷ S.obj a) ≫
        translatedAction d S L N c j a) (parameter_first_shuffle P X (S.obj a))
    _ = _ := by simp only [X, comp_whiskerRight, Category.assoc]

/-- The entire action-end condition is equivalent to the exact coefficient-first MMSS
balance. The reverse direction retains the genuine full Day/Kan detection property. -/
theorem condition_iff_gradeFirst_balance (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    (ambientFamily d S L M N c t ≫ component (sourceActionMap d S L M N) c =
      ambientFamily d S L M N c t ≫ component (targetActionMap d b S L M N) c) ↔
    (∀ j a,
      (P ◁ ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.action d S L M) j a) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) t (j ⊗ a) =
      (α_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a)).inv ≫
        (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) t j ▷ S.obj a) ≫
          translatedAction d S L N c j a) := by
  constructor
  · intro h j a
    let q : Family d b S L M N c P := { transformation := t, condition := h }
    exact q.evaluation_action_balance d b S L j a
  · intro h
    apply (condition_iff_actionBalance d b S L M N c t).2
    intro j a
    let X := (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j
    let A := S.obj a
    let sm := ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.action d S L M) j a
    let fx := MonoidalClosed.uncurry (t.app j)
    let fy := MonoidalClosed.uncurry (t.app (j ⊗ a))
    let tail := translatedAction d S L N c j a
    have hp := h j a
    change (P ◁ sm) ≫
        (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj (j ⊗ a))).hom ≫
        fy = (α_ P X A).inv ≫ (((β_ P X).hom ≫ fx) ▷ A) ≫ tail at hp
    apply (cancel_epi (β_ P (X ⊗ A)).hom).1
    change (β_ P (X ⊗ A)).hom ≫ (sm ▷ P) ≫ fy =
      (β_ P (X ⊗ A)).hom ≫ coefficientSwap X A P ≫ (fx ▷ A) ≫ tail
    calc
      _ = (P ◁ sm) ≫
          (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj
            (j ⊗ a))).hom ≫ fy :=
        (braiding_naturality_right_assoc P sm fy).symm
      _ = (α_ P X A).inv ≫ (((β_ P X).hom ≫ fx) ▷ A) ≫ tail := hp
      _ = (α_ P X A).inv ≫ ((β_ P X).hom ▷ A) ≫ (fx ▷ A) ≫ tail := by
        simp only [comp_whiskerRight, Category.assoc]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ (fx ▷ A) ≫ tail)
          (parameter_first_shuffle P X A).symm

/-- The whole represented family is determined by all its coefficient-first components. -/
@[ext]
theorem Family.evaluation_ext {M N : Module d S L} {c : I} {P : V}
    (q q' : Family d b S L M N c P)
    (h : ∀ j, q.evaluation d b S L j = q'.evaluation d b S L j) : q = q' := by
  apply Family.ext
  apply GradedNatTrans.ext
  funext j
  apply MonoidalClosed.uncurry_injective
  exact (cancel_epi
    (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).hom).1 (h j)

/-- Lifting every full coefficient-first family retains its actual end projection. -/
theorem Family.lift_evaluation {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (j : I) :
    q.evaluation d b S L j =
      (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).hom ≫
        MonoidalClosed.uncurry (lift d b S L M N c q ≫ π d b S L M N c j) := by
  rw [lift_π]
  exact q.evaluation_eq d b S L j

/-- The inverse correspondence retains every whole coefficient-first evaluation. -/
theorem toFamily_evaluation (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ value d b S L M N c) (j : I) :
    (toFamily d b S L M N c f).evaluation d b S L j =
      (β_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).hom ≫
        MonoidalClosed.uncurry (f ≫ π d b S L M N c j) := by
  rw [Family.evaluation_eq, toFamily_app]

/-- Every original coefficient arrow acts through the actual represented Mapping_R value. -/
def Family.regrade {M N : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (q : Family d b S L M N c Q) : Family d b S L M N c P :=
  toFamily d b S L M N c (h ≫ lift d b S L M N c q)

/-- Regrading retains each original full curried source component. -/
theorem Family.regrade_app {M N : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (q : Family d b S L M N c Q) (j : I) :
    (q.regrade d b S L h).transformation.app j = h ≫ q.transformation.app j := by
  rw [Family.regrade, toFamily_app, Category.assoc, lift_π]

/-- The complete coefficient-first family map uses the original coefficient tensor arrow. -/
theorem Family.regrade_evaluation {M N : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (q : Family d b S L M N c Q) (j : I) :
    (q.regrade d b S L h).evaluation d b S L j =
      (h ▷ (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j) ≫
        q.evaluation d b S L j := by
  rw [Family.evaluation_eq, Family.evaluation_eq, Family.regrade_app,
    MonoidalClosed.uncurry_natural_left]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ MonoidalClosed.uncurry (q.transformation.app j))
      (braiding_naturality_left h
        ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).symm

/-- The identity coefficient arrow retains every complete represented family. -/
@[simp]
theorem Family.regrade_id {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) : q.regrade d b S L (𝟙 P) = q := by
  rw [Family.regrade, Category.id_comp, toFamily_lift]

/-- Lifting retains the entire original coefficient arrow on the represented end. -/
theorem Family.lift_regrade {M N : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (q : Family d b S L M N c Q) :
    lift d b S L M N c (q.regrade d b S L h) = h ≫ lift d b S L M N c q :=
  lift_toFamily d b S L M N c _

/-- Complete coefficient composites retain the original contravariant order. -/
theorem Family.regrade_comp {M N : Module d S L} {c : I} {P Q T : V}
    (h : P ⟶ Q) (k : Q ⟶ T) (q : Family d b S L M N c T) :
    q.regrade d b S L (h ≫ k) = (q.regrade d b S L k).regrade d b S L h := by
  apply Family.ext
  apply GradedNatTrans.ext
  funext j
  rw [Family.regrade_app, Family.regrade_app, Family.regrade_app, Category.assoc]

/-- Every complete original source-module arrow acts on every represented family. -/
def Family.sourceMap {M M' N : Module d S L} {c : I} {P : V}
    (f : M' ⟶ M) (q : Family d b S L M N c P) : Family d b S L M' N c P :=
  toFamily d b S L M' N c
    (lift d b S L M N c q ≫ component (pre d b S L f N) c)

/-- The whole source map retains precisely the original full carrier precomposition. -/
theorem Family.sourceMap_app {M M' N : Module d S L} {c : I} {P : V}
    (f : M' ⟶ M) (q : Family d b S L M N c P) (j : I) :
    (q.sourceMap d b S L f).transformation.app j = q.transformation.app j ≫
      (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) := by
  rw [Family.sourceMap, toFamily_app, Category.assoc, pre_π, ← Category.assoc, lift_π]

/-- The source family map retains the literal coefficient-first original carrier map. -/
theorem Family.sourceMap_evaluation {M M' N : Module d S L} {c : I} {P : V}
    (f : M' ⟶ M) (q : Family d b S L M N c P) (j : I) :
    (q.sourceMap d b S L f).evaluation d b S L j =
      (P ◁ component (SphereModuleMappingEnd.moduleMap d S L f) j) ≫
        q.evaluation d b S L j := by
  let Y := (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)
  let X := (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j
  let X' := (SphereModuleMappingEnd.diagram d S L M').toEnrichedFunctor.obj j
  let t : P ⟶ (ihom X).obj Y := q.transformation.app j
  let t' : P ⟶ (ihom X').obj Y :=
    (q.sourceMap d b S L f).transformation.app j
  let fj : X' ⟶ X := component (SphereModuleMappingEnd.moduleMap d S L f) j
  have hs : t' = t ≫ (MonoidalClosed.pre fj).app Y :=
    q.sourceMap_app d b S L f j
  change (β_ P X').hom ≫ MonoidalClosed.uncurry t' =
    (P ◁ fj) ≫ (β_ P X).hom ≫ MonoidalClosed.uncurry t
  rw [hs, MonoidalClosed.uncurry_pre_app]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ MonoidalClosed.uncurry t)
    (braiding_naturality_right P fj).symm

/-- Every complete original target-module arrow acts on every represented family. -/
def Family.targetMap {M N N' : Module d S L} {c : I} {P : V}
    (g : N ⟶ N') (q : Family d b S L M N c P) : Family d b S L M N' c P :=
  toFamily d b S L M N' c
    (lift d b S L M N c q ≫ component (post d b S L M g) c)

/-- The whole target map retains its literal right-translation carrier postcomposition. -/
theorem Family.targetMap_app {M N N' : Module d S L} {c : I} {P : V}
    (g : N ⟶ N') (q : Family d b S L M N c P) (j : I) :
    (q.targetMap d b S L g).transformation.app j = q.transformation.app j ≫
      (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).map
        (component (SphereModuleMappingEnd.moduleMap d S L g) (j ⊗ c)) := by
  rw [Family.targetMap, toFamily_app, Category.assoc, post_π, ← Category.assoc, lift_π]

/-- The target family map retains literal postcomposition at the original j ⊗ c value. -/
theorem Family.targetMap_evaluation {M N N' : Module d S L} {c : I} {P : V}
    (g : N ⟶ N') (q : Family d b S L M N c P) (j : I) :
    (q.targetMap d b S L g).evaluation d b S L j =
      q.evaluation d b S L j ≫ component (SphereModuleMappingEnd.moduleMap d S L g)
        (j ⊗ c) := by
  rw [Family.evaluation_eq, Family.evaluation_eq, Family.targetMap_app,
    MonoidalClosed.uncurry_natural_right]
  exact (Category.assoc _ _ _).symm

/-- Lifting preserves the entire original source map between the actual represented values. -/
theorem Family.lift_sourceMap {M M' N : Module d S L} {c : I} {P : V}
    (f : M' ⟶ M) (q : Family d b S L M N c P) :
    lift d b S L M' N c (q.sourceMap d b S L f) =
      lift d b S L M N c q ≫ component (pre d b S L f N) c :=
  lift_toFamily d b S L M' N c _

/-- Lifting preserves the entire original target map between the actual represented values. -/
theorem Family.lift_targetMap {M N N' : Module d S L} {c : I} {P : V}
    (g : N ⟶ N') (q : Family d b S L M N c P) :
    lift d b S L M N' c (q.targetMap d b S L g) =
      lift d b S L M N c q ≫ component (post d b S L M g) c :=
  lift_toFamily d b S L M N' c _

/-- The entire parameter Hom acts on every genuine represented coefficient family. -/
def Family.parameterMap {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (c' : I) :
    Family d b S L M N c' (P ⊗ (c ⟶[V] c')) :=
  toFamily d b S L M N c'
    ((lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ parameterAction d b S L M N c c')

/-- The whole parameter-family component is the original full parameter Hom composition. -/
theorem Family.parameterMap_app {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (c' j : I) :
    (q.parameterMap d b S L c').transformation.app j =
      (q.transformation.app j ⊗ₘ
        Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' j) ≫
        eComp V ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c')) := by
  rw [Family.parameterMap, toFamily_app, Category.assoc, parameterAction_π]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, lift_π]

/-- Lifting the full parameter family preserves the complete original end action. -/
theorem Family.lift_parameterMap {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (c' : I) :
    lift d b S L M N c' (q.parameterMap d b S L c') =
      (lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ parameterAction d b S L M N c c' :=
  lift_toFamily d b S L M N c' _

/-- Every complete source-module map commutes with the whole parameter Hom family action. -/
theorem Family.parameterMap_sourceMap {M M' N : Module d S L} {c : I} {P : V}
    (f : M' ⟶ M) (q : Family d b S L M N c P) (c' : I) :
    (q.sourceMap d b S L f).parameterMap d b S L c' =
      (q.parameterMap d b S L c').sourceMap d b S L f := by
  change toFamily d b S L M' N c'
      ((lift d b S L M' N c (q.sourceMap d b S L f) ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        parameterAction d b S L M' N c c') =
    toFamily d b S L M' N c'
      (lift d b S L M N c' (q.parameterMap d b S L c') ≫
        component (pre d b S L f N) c')
  rw [Family.lift_sourceMap, Family.lift_parameterMap]
  apply congrArg (toFamily d b S L M' N c')
  have hf : ((lift d b S L M N c q ≫ component (pre d b S L f N) c) ⊗ₘ
        𝟙 (c ⟶[V] c')) =
      (lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        (component (pre d b S L f N) c ⊗ₘ 𝟙 (c ⟶[V] c')) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (lift d b S L M N c q) (𝟙 (c ⟶[V] c'))
        (component (pre d b S L f N) c) (𝟙 (c ⟶[V] c'))).symm
  rw [hf, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun z => (lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ z)
    ((pre d b S L f N).uncurriedNaturality c c').symm

/-- Every complete target-module map commutes with the whole parameter Hom family action. -/
theorem Family.parameterMap_targetMap {M N N' : Module d S L} {c : I} {P : V}
    (g : N ⟶ N') (q : Family d b S L M N c P) (c' : I) :
    (q.targetMap d b S L g).parameterMap d b S L c' =
      (q.parameterMap d b S L c').targetMap d b S L g := by
  change toFamily d b S L M N' c'
      ((lift d b S L M N' c (q.targetMap d b S L g) ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        parameterAction d b S L M N' c c') =
    toFamily d b S L M N' c'
      (lift d b S L M N c' (q.parameterMap d b S L c') ≫
        component (post d b S L M g) c')
  rw [Family.lift_targetMap, Family.lift_parameterMap]
  apply congrArg (toFamily d b S L M N' c')
  have hf : ((lift d b S L M N c q ≫ component (post d b S L M g) c) ⊗ₘ
        𝟙 (c ⟶[V] c')) =
      (lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        (component (post d b S L M g) c ⊗ₘ 𝟙 (c ⟶[V] c')) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (lift d b S L M N c q) (𝟙 (c ⟶[V] c'))
        (component (post d b S L M g) c) (𝟙 (c ⟶[V] c'))).symm
  rw [hf, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun z => (lift d b S L M N c q ⊗ₘ 𝟙 (c ⟶[V] c')) ≫ z)
    ((post d b S L M g).uncurriedNaturality c c').symm

/-- Every actual coefficient arrow commutes with the entire parameter Hom action. -/
theorem Family.parameterMap_regrade {M N : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (q : Family d b S L M N c Q) (c' : I) :
    (q.regrade d b S L h).parameterMap d b S L c' =
      (q.parameterMap d b S L c').regrade d b S L (h ⊗ₘ 𝟙 (c ⟶[V] c')) := by
  change toFamily d b S L M N c'
      ((lift d b S L M N c (q.regrade d b S L h) ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        parameterAction d b S L M N c c') =
    toFamily d b S L M N c'
      ((h ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        lift d b S L M N c' (q.parameterMap d b S L c'))
  rw [Family.lift_regrade, Family.lift_parameterMap]
  apply congrArg (toFamily d b S L M N c')
  simpa only [Category.id_comp, Category.assoc] using congrArg
    (fun z => z ≫ parameterAction d b S L M N c c')
    (tensorHom_comp_tensorHom h (𝟙 (c ⟶[V] c'))
      (lift d b S L M N c q) (𝟙 (c ⟶[V] c'))).symm

end CategoryTheory.Enriched.ModuleMappingR
