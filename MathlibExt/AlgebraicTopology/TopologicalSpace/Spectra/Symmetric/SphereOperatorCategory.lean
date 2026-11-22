/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory
public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerCoefficient
public import MathlibExt.Topology.Category.CGWH.Colimits

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereSequence
public import MathlibExt.Topology.Category.PointedCGWH.CopowerHomDescent
public import MathlibExt.Topology.Category.PointedCGWH.CopowerDiagramComparison
public import MathlibExt.Topology.Category.PointedCGWH.DiscreteSmash
public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerIndex
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendPoint
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorUnit
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorFunctorActions
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexUnitFunctor
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ModuleGeneratorLaws

/-!
# Sphere operators and symmetric module reconstruction

Constructs the enriched operator category associated to the symmetric sphere sequence and
reconstructs the sphere-module action from its Hom maps. Complete recovery isomorphisms give the
module/operator equivalence, with component formulas and both triangle identities.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v uI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace PointedCGWH

attribute [local instance] copowerUnderlyingEnrichedOrdinary
  copowerUnderlyingMonoidal

/-- The actual finite-bijection copower index, tagged by the original native
sphere coefficient data. No operator law is provided by the caller. -/
abbrev SymmetricOperatorIndex : Type :=
  Enriched.SphereOperator.OperatorIndex
    (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid)
    sphereCopowerEnrichedFunctor.{u, v} sphereCopowerLaxData.{u, v}

/-- Actual CGWH and Under colimits provide precisely the native relation coproducts. -/
instance symmetricOperatorRelationCoproduct
    (n m : CopowerUnderlying.{u, v, 0} Operad.SmallFinBijGroupoid) :
    HasCoproduct (Enriched.weightedCoend.relations
      (Enriched.SphereOperator.weight
        (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid) n m)
      sphereCopowerEnrichedFunctor.{u, v}) := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

/-- The corresponding object coproducts use the same actual native colimits. -/
instance symmetricOperatorObjectCoproduct
    (n m : CopowerUnderlying.{u, v, 0} Operad.SmallFinBijGroupoid) :
    HasCoproduct (Enriched.weightedCoend.objects
      (Enriched.SphereOperator.weight
        (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid) n m)
      sphereCopowerEnrichedFunctor.{u, v}) := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

/-- The selected two full relation maps have their native coequalizer. -/
instance symmetricOperatorCoequalizer
    (n m : CopowerUnderlying.{u, v, 0} Operad.SmallFinBijGroupoid) :
    HasCoequalizer
      (Enriched.weightedCoend.leftMap
        (Enriched.SphereOperator.weight
          (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid) n m)
        sphereCopowerEnrichedFunctor.{u, v})
      (Enriched.weightedCoend.rightMap
        (Enriched.SphereOperator.weight
          (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid) n m)
        sphereCopowerEnrichedFunctor.{u, v}) := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

/-- The original finite index object is sent to the same copower object. -/
def symmetricOperatorObj (n : Operad.SmallFinBijGroupoid) :
    SymmetricOperatorIndex.{u, v} :=
  ⟨ForgetEnrichment.of PointedCGWH.{u, v}
    (copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid n)⟩

/-- The full native Hom is the original generic coend using the identical
native coefficient and copower monoidal data. -/
theorem symmetricOperator_hom (n m : Operad.SmallFinBijGroupoid) :
    (symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
        symmetricOperatorObj.{u, v} m) =
      Enriched.SphereOperator.Hom
        (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid)
        sphereCopowerEnrichedFunctor.{u, v}
        ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj n)
        ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj m) := rfl

end PointedCGWH

open scoped CategoryTheory.MonObj
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace PointedCGWH

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The original finite index maps by its actual unit-coefficient enriched functor. -/
def symmetricIndexInclusion : EnrichedFunctor PointedCGWH.{u, v}
    (CopowerUnderlying.{u, v, 0} Operad.SmallFinBijGroupoid) SymmetricOperatorIndex.{u, v} :=
  Enriched.SphereOperator.indexUnitFunctor
    (copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid)
    sphereCopowerEnrichedFunctor.{u, v} sphereCopowerLaxData.{u, v}

/-- Complete canonical restriction data, with the original enriched restriction
and both original diagram equivalences, including their maps and functor laws. -/
def symmetricSequenceRestrictionData : EnrichedFunctorCat PointedCGWH.{u, v}
    SymmetricOperatorIndex.{u, v} ⥤ SymmetricSequence.{u, v} :=
  (show EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v}
        (CopowerIndex.{u, v, 0} Operad.SmallFinBijGroupoid) from
    EnrichedFunctorCat.restriction symmetricIndexInclusion.{u, v}) ⋙
    (copowerDiagramEquivalence.{u, v, 0} (I := Operad.SmallFinBijGroupoid)).inverse ⋙
    (DayFunctor.equiv Operad.SmallFinBijGroupoid PointedCGWH.{u, v}).inverse

/-- Canonical sequence restriction uses the existing enriched restriction and
diagram equivalence. -/
def symmetricSequenceRestriction : EnrichedFunctorCat PointedCGWH.{u, v}
    SymmetricOperatorIndex.{u, v} ⥤ SymmetricSequence.{u, v} :=
  { obj := fun F =>
      { functor :=
        { obj := fun n => F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
          map := fun {n k} f =>
            (eHomEquiv PointedCGWH.{u, v}).symm
              (basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
                symmetricIndexInclusion.{u, v}.map
                  ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj n)
                  ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj k) ≫
                F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
                  (symmetricOperatorObj.{u, v} k))
          map_id := fun n => ((symmetricSequenceRestrictionData.{u, v}).obj F).functor.map_id n
          map_comp := fun f g =>
            ((symmetricSequenceRestrictionData.{u, v}).obj F).functor.map_comp f g } }
    map := fun f => (symmetricSequenceRestrictionData.{u, v}).map f
    map_id := fun F => (symmetricSequenceRestrictionData.{u, v}).map_id F
    map_comp := fun f g => (symmetricSequenceRestrictionData.{u, v}).map_comp f g }

/-- Every restricted level is the original canonical enriched-functor object. -/
theorem symmetricSequenceRestriction_obj
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (n : Operad.SmallFinBijGroupoid) :
    ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n =
      F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n) := rfl

/-- Every original index arrow acts through its entire unit-coefficient operator Hom map. -/
theorem symmetricSequenceRestriction_map
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    {n k : Operad.SmallFinBijGroupoid} (f : n ⟶ k) :
    ((symmetricSequenceRestriction.{u, v}).obj F).functor.map f =
      (eHomEquiv PointedCGWH.{u, v}).symm
        (basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
          symmetricIndexInclusion.{u, v}.map
            ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj n)
            ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj k) ≫
          F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
            (symmetricOperatorObj.{u, v} k)) := rfl

/-- Canonical restriction keeps every genuine transformation's original level component. -/
theorem symmetricSequenceRestriction_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}}
    (f : F ⟶ G) (n : Operad.SmallFinBijGroupoid) :
    ((symmetricSequenceRestriction.{u, v}).map f).natTrans.app n =
      EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} n) := by
  change EnrichedFunctorCat.component
      (EnrichedFunctorCat.restrictionMap symmetricIndexInclusion.{u, v} f)
      ((copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj n) = _
  exact EnrichedFunctorCat.restrictionMap_component symmetricIndexInclusion.{u, v} f _

end PointedCGWH

namespace PointedCGWH.SymmetricModulePresentation

open LawfulDayConvolutionMonoidalCategoryStruct

attribute [local instance] copowerUnderlyingEnrichedOrdinary
  copowerUnderlyingMonoidal sphereSequenceMonObj
local notation "I" => Operad.SmallFinBijGroupoid

variable (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u,
    v}) sphereSequence.{u, v})

/-- The complete pair transformation retains the original Day multiplication. -/
def pairTransformation :
    sphereSequence.{u, v}.functor ⊠ M.X.functor ⟶ tensor I ⋙ M.X.functor :=
  DayFunctor.η sphereSequence.{u, v} M.X ≫ Functor.whiskerLeft (tensor I)
    (ModObj.smul (M := sphereSequence.{u, v}) (X := M.X)).natTrans

/-- The pair action uses the sphere coefficient followed by the indexed object. -/
def pairAction (a n : I) :
    sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶ M.X.functor.obj (a ⊗ n) :=
  (pairTransformation M).app (a, n)

/-- Every pair of original index arrows satisfies the complete naturality square. -/
theorem pairAction_naturality {a a' n n' : I} (r : a ⟶ a') (g : n ⟶ n') :
    (sphereSequence.{u, v}.functor.map r ⊗ₘ M.X.functor.map g) ≫ pairAction M a' n' =
      pairAction M a n ≫ M.X.functor.map (r ⊗ₘ g) := by
  exact (pairTransformation M).naturality
    (show (a, n) ⟶ (a', n') from (r, g))

/-- Naturality in the whole original coefficient arrow keeps its tensor action. -/
theorem pairAction_coefficient {a a' : I} (r : a ⟶ a') (n : I) :
    (sphereSequence.{u, v}.functor.map r ▷ M.X.functor.obj n) ≫ pairAction M a' n =
      pairAction M a n ≫ M.X.functor.map (r ⊗ₘ 𝟙 n) := by
  simpa only [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id] using
    pairAction_naturality M r (𝟙 n)

/-- Naturality in the original source index keeps the actual diagram arrow. -/
theorem pairAction_input (a : I) {n n' : I} (g : n ⟶ n') :
    (sphereSequence.{u, v}.functor.obj a ◁ M.X.functor.map g) ≫ pairAction M a n' =
      pairAction M a n ≫ M.X.functor.map (𝟙 a ⊗ₘ g) := by
  simpa only [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] using
    pairAction_naturality M (𝟙 a) g

/-- Every original tensor-index arrow acts after the literal module pair action. -/
def arrowAction (a n k : I) (f : (a ⊗ n) ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶ M.X.functor.obj k :=
  pairAction M a n ≫ M.X.functor.map f

/-- The complete coefficient relation follows from the original pair naturality. -/
theorem arrowAction_coefficient {a a' : I} (r : a ⟶ a') (n k : I)
    (f : (a' ⊗ n) ⟶ k) :
    (sphereSequence.{u, v}.functor.map r ▷ M.X.functor.obj n) ≫ arrowAction M a' n k f =
      arrowAction M a n k ((r ⊗ₘ 𝟙 n) ≫ f) := by
  let q : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      M.X.functor.obj (a ⊗ n) := pairAction M a n
  let q' : sphereSequence.{u, v}.functor.obj a' ⊗ M.X.functor.obj n ⟶
      M.X.functor.obj (a' ⊗ n) := pairAction M a' n
  let j : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      sphereSequence.{u, v}.functor.obj a' ⊗ M.X.functor.obj n :=
    sphereSequence.{u, v}.functor.map r ▷ M.X.functor.obj n
  let p : M.X.functor.obj (a ⊗ n) ⟶ M.X.functor.obj (a' ⊗ n) :=
    M.X.functor.map (r ⊗ₘ 𝟙 n)
  let t : M.X.functor.obj (a' ⊗ n) ⟶ M.X.functor.obj k :=
    M.X.functor.map f
  have hPair : j ≫ q' = q ≫ p := pairAction_coefficient M r n
  have hCompose : p ≫ t = M.X.functor.map ((r ⊗ₘ 𝟙 n) ≫ f) :=
    (M.X.functor.map_comp (r ⊗ₘ 𝟙 n) f).symm
  change j ≫ q' ≫ t = q ≫ M.X.functor.map ((r ⊗ₘ 𝟙 n) ≫ f)
  exact (Category.assoc j q' t).symm.trans
    ((congrArg (fun z : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      M.X.functor.obj (a' ⊗ n) => z ≫ t) hPair).trans
        ((Category.assoc q p t).trans
          (congrArg (fun z : M.X.functor.obj (a ⊗ n) ⟶
            M.X.functor.obj k => q ≫ z) hCompose)))

/-- The complete input-index relation follows from the original pair naturality. -/
theorem arrowAction_input (a : I) {n n' : I} (g : n ⟶ n') (k : I)
    (f : (a ⊗ n') ⟶ k) :
    (sphereSequence.{u, v}.functor.obj a ◁ M.X.functor.map g) ≫ arrowAction M a n' k f =
      arrowAction M a n k ((𝟙 a ⊗ₘ g) ≫ f) := by
  let q : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      M.X.functor.obj (a ⊗ n) := pairAction M a n
  let q' : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n' ⟶
      M.X.functor.obj (a ⊗ n') := pairAction M a n'
  let j : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n' :=
    sphereSequence.{u, v}.functor.obj a ◁ M.X.functor.map g
  let p : M.X.functor.obj (a ⊗ n) ⟶ M.X.functor.obj (a ⊗ n') :=
    M.X.functor.map (𝟙 a ⊗ₘ g)
  let t : M.X.functor.obj (a ⊗ n') ⟶ M.X.functor.obj k :=
    M.X.functor.map f
  have hPair : j ≫ q' = q ≫ p := pairAction_input M a g
  have hCompose : p ≫ t = M.X.functor.map ((𝟙 a ⊗ₘ g) ≫ f) :=
    (M.X.functor.map_comp (𝟙 a ⊗ₘ g) f).symm
  change j ≫ q' ≫ t = q ≫ M.X.functor.map ((𝟙 a ⊗ₘ g) ≫ f)
  exact (Category.assoc j q' t).symm.trans
    ((congrArg (fun z : sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n ⟶
      M.X.functor.obj (a ⊗ n') => z ≫ t) hPair).trans
        ((Category.assoc q p t).trans
          (congrArg (fun z : M.X.functor.obj (a ⊗ n) ⟶
            M.X.functor.obj k => q ≫ z) hCompose)))

/-- Postcomposition retains the complete original ordinary diagram composite. -/
theorem arrowAction_target (a n : I) {k l : I}
    (f : (a ⊗ n) ⟶ k) (g : k ⟶ l) :
    arrowAction M a n k f ≫ M.X.functor.map g =
      arrowAction M a n l (f ≫ g) :=
  (Category.assoc (pairAction M a n) (M.X.functor.map f)
    (M.X.functor.map g)).trans
      (congrArg (fun z : M.X.functor.obj (a ⊗ n) ⟶ M.X.functor.obj l =>
        pairAction M a n ≫ z) (M.X.functor.map_comp f g).symm)

/-- The whole native Hom map descends all original tensor-index arrows. -/
def fullHomMap (a n k : I) :
    basedDiscreteObj.{u, v, 0} ((a ⊗ n) ⟶ k) ⟶
      (ihom (sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n)).obj (M.X.functor.obj k) :=
  copowerHomMap.{u, v, 0} ((a ⊗ n) ⟶ k)
    (sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n) (M.X.functor.obj k)
    (arrowAction M a n k)

/-- Every original point injection retains the complete corresponding arrow action. -/
theorem fullHomMap_generator (a n k : I) (f : (a ⊗ n) ⟶ k) :
    basedDiscreteIncl.{u, v, 0} ((a ⊗ n) ⟶ k) f ≫ fullHomMap M a n k =
      eHomEquiv PointedCGWH.{u, v} (arrowAction M a n k f) :=
  copowerHomMap_generator.{u, v, 0} ((a ⊗ n) ⟶ k)
    (sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n) (M.X.functor.obj k)
    (arrowAction M a n k) f

/-- The identity-arrow injection recovers the original entire pair action. -/
theorem fullHomMap_identity (a n : I) :
    (eHomEquiv PointedCGWH.{u, v}).symm
      (basedDiscreteIncl.{u, v, 0} ((a ⊗ n) ⟶ (a ⊗ n)) (𝟙 (a ⊗ n)) ≫
        fullHomMap M a n (a ⊗ n)) = pairAction M a n := by
  let A : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a ⊗ M.X.functor.obj n
  let B : PointedCGWH.{u, v} := M.X.functor.obj (a ⊗ n)
  let e : (A ⟶ B) ≃ ((𝟙_ PointedCGWH.{u, v}) ⟶ (ihom A).obj B) :=
    eHomEquiv PointedCGWH.{u, v}
  have h : basedDiscreteIncl.{u, v, 0} ((a ⊗ n) ⟶ (a ⊗ n)) (𝟙 (a ⊗ n)) ≫
      fullHomMap M a n (a ⊗ n) = e (arrowAction M a n (a ⊗ n) (𝟙 (a ⊗ n))) :=
    fullHomMap_generator M a n (a ⊗ n) (𝟙 (a ⊗ n))
  have hAction : arrowAction M a n (a ⊗ n) (𝟙 (a ⊗ n)) = pairAction M a n :=
    (congrArg (fun z : B ⟶ B => pairAction M a n ≫ z)
      (M.X.functor.map_id (a ⊗ n))).trans (Category.comp_id (pairAction M a n))
  exact (congrArg e.symm h).trans ((e.symm_apply_apply _).trans hAction)

/-- The original whole Day multiplication is recovered by its pair transformation. -/
theorem pairTransformation_reconstructs_action :
    DayFunctor.tensorDesc (pairTransformation M) =
      ModObj.smul (M := sphereSequence.{u, v}) (X := M.X) := by
  apply DayFunctor.tensor_hom_ext
  intro a n
  exact DayFunctor.η_comp_tensorDesc_app (pairTransformation M) a n




/-- The fixed-left transpose of the literal coefficient-first arrow action. -/
def curriedArrowAction (a n k : I) (f : (a ⊗ n) ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⟶ (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k) :=
  MonoidalClosed.curry
    ((β_ (sphereSequence.{u, v}.functor.obj a) (M.X.functor.obj n)).inv ≫ arrowAction M a n k f)

/-- The actual coefficient cofan supplies the entire coend-generator leg. -/
def coendGeneratorMap (a n k : I) :
    basedDiscreteObj.{u, v, 0} ((a ⊗ n) ⟶ k) ⊗ sphereSequence.{u, v}.functor.obj a ⟶
      (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k) :=
  discreteSmashDesc.{u, v, 0} ((a ⊗ n) ⟶ k) (sphereSequence.{u, v}.functor.obj a)
    (curriedArrowAction M a n k)

/-- Every native coefficient injection retains the entire original arrow action. -/
theorem coendGeneratorMap_generator (a n k : I) (f : (a ⊗ n) ⟶ k) :
    discreteSmashIncl.{u, v, 0} ((a ⊗ n) ⟶ k) (sphereSequence.{u, v}.functor.obj a) f ≫
        coendGeneratorMap M a n k = curriedArrowAction M a n k f :=
  discreteSmashDesc_generator.{u, v, 0} ((a ⊗ n) ⟶ k) (sphereSequence.{u, v}.functor.obj a)
    (curriedArrowAction M a n k) f

private theorem curriedArrowAction_coefficient {a a' : I} (r : a ⟶ a')
    (n k : I) (f : (a' ⊗ n) ⟶ k) :
    sphereSequence.{u, v}.functor.map r ≫ curriedArrowAction M a' n k f =
      curriedArrowAction M a n k ((r ⊗ₘ 𝟙 n) ≫ f) := by
  let X : PointedCGWH.{u, v} := M.X.functor.obj n
  let A : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a
  let B : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a'
  let Y : PointedCGWH.{u, v} := M.X.functor.obj k
  let p : A ⟶ B := sphereSequence.{u, v}.functor.map r
  let q : B ⊗ X ⟶ Y := arrowAction M a' n k f
  let q' : A ⊗ X ⟶ Y := arrowAction M a n k ((r ⊗ₘ 𝟙 n) ≫ f)
  have hBraid : X ◁ p ≫ (β_ B X).inv =
      (β_ A X).inv ≫ p ▷ X :=
    BraidedCategory.braiding_inv_naturality_right X p
  have hAction : (p ▷ X) ≫ q = q' := arrowAction_coefficient M r n k f
  have hFull : (X ◁ p) ≫ ((β_ B X).inv ≫ q) = (β_ A X).inv ≫ q' :=
    (Category.assoc (X ◁ p) (β_ B X).inv q).symm.trans
      ((congrArg (fun t : X ⊗ A ⟶ B ⊗ X => t ≫ q) hBraid).trans
        ((Category.assoc (β_ A X).inv (p ▷ X) q).trans
          (congrArg (fun t : A ⊗ X ⟶ Y => (β_ A X).inv ≫ t) hAction)))
  change p ≫ MonoidalClosed.curry ((β_ B X).inv ≫ q) =
    MonoidalClosed.curry ((β_ A X).inv ≫ q')
  exact (MonoidalClosed.curry_natural_left p ((β_ B X).inv ≫ q)).symm.trans
    (congrArg (fun t : X ⊗ A ⟶ Y => MonoidalClosed.curry t) hFull)

private theorem discreteSmashIncl_index
    {E E' : Type} (h : E → E') (A : PointedCGWH.{u, v}) (e : E) :
    discreteSmashIncl.{u, v, 0} E A e ≫
        (basedDiscreteFunctor.{u, v, 0}.map (↾h) ▷ A) =
      discreteSmashIncl.{u, v, 0} E' A (h e) := by
  let U : PointedCGWH.{u, v} := 𝟙_ PointedCGWH.{u, v}
  let D : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E
  let D' : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E'
  let i : U ⟶ D := basedDiscreteIncl.{u, v, 0} E e
  let i' : U ⟶ D' := basedDiscreteIncl.{u, v, 0} E' (h e)
  let p : D ⟶ D' := basedDiscreteFunctor.{u, v, 0}.map (↾h)
  have hi : i ≫ p = i' := basedDiscreteIncl_naturality.{u, v, 0} h e
  have hp : p ⊗ₘ 𝟙 A = p ▷ A := MonoidalCategory.tensorHom_id p A
  have hTensor : (i ⊗ₘ 𝟙 A) ≫ (p ▷ A) = i' ⊗ₘ 𝟙 A :=
    (congrArg
      (fun t : D ⊗ A ⟶ D' ⊗ A => (i ⊗ₘ 𝟙 A) ≫ t) hp.symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom i (𝟙 A) p (𝟙 A)).trans
        (congrArg₂ (fun s t => s ⊗ₘ t) hi (Category.comp_id (𝟙 A))))
  change (λ_ A).inv ≫ (i ⊗ₘ 𝟙 A) ≫ (p ▷ A) =
    (λ_ A).inv ≫ (i' ⊗ₘ 𝟙 A)
  exact (Category.assoc (λ_ A).inv (i ⊗ₘ 𝟙 A) (p ▷ A)).trans
    (congrArg (fun t : U ⊗ A ⟶ D' ⊗ A => (λ_ A).inv ≫ t) hTensor)

private theorem discreteSmashIncl_coefficient
    (E : Type) {A B : PointedCGWH.{u, v}} (p : A ⟶ B) (e : E) :
    discreteSmashIncl.{u, v, 0} E A e ≫ (basedDiscreteObj.{u, v, 0} E ◁ p) =
      p ≫ discreteSmashIncl.{u, v, 0} E B e := by
  let U : PointedCGWH.{u, v} := 𝟙_ PointedCGWH.{u, v}
  let D : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E
  let i : U ⟶ D := basedDiscreteIncl.{u, v, 0} E e
  have hp : 𝟙 D ⊗ₘ p = D ◁ p := MonoidalCategory.id_tensorHom D p
  have hTensor : (i ⊗ₘ 𝟙 A) ≫ (D ◁ p) = i ⊗ₘ p :=
    (congrArg
      (fun t : D ⊗ A ⟶ D ⊗ B => (i ⊗ₘ 𝟙 A) ≫ t) hp.symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom i (𝟙 A) (𝟙 D) p).trans
        (congrArg₂ (fun s t => s ⊗ₘ t) (Category.comp_id i) (Category.id_comp p)))
  change (λ_ A).inv ≫ (i ⊗ₘ 𝟙 A) ≫ (D ◁ p) =
    p ≫ (λ_ B).inv ≫ (i ⊗ₘ 𝟙 B)
  have hUnitor : (λ_ A).inv ≫ (i ⊗ₘ p) =
      p ≫ (λ_ B).inv ≫ (i ⊗ₘ 𝟙 B) := by
    simpa only [MonoidalCategory.tensorHom_id] using leftUnitor_inv_comp_tensorHom i p
  exact (Category.assoc (λ_ A).inv (i ⊗ₘ 𝟙 A) (D ◁ p)).trans
    ((congrArg (fun t : U ⊗ A ⟶ D ⊗ B => (λ_ A).inv ≫ t) hTensor).trans hUnitor)

/-- Both sides of the coefficient relation retain the full native Hom and coefficient. -/
theorem coendGeneratorMap_coefficient {a a' : I} (r : a ⟶ a') (n k : I) :
    (basedDiscreteFunctor.{u, v, 0}.map
        (↾fun f : (a' ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f) ▷ sphereSequence.{u, v}.functor.obj a) ≫
        coendGeneratorMap M a n k =
      (basedDiscreteObj.{u, v, 0} ((a' ⊗ n) ⟶ k) ◁ sphereSequence.{u, v}.functor.map r) ≫
        coendGeneratorMap M a' n k := by
  let E : Type := (a' ⊗ n) ⟶ k
  let E' : Type := (a ⊗ n) ⟶ k
  let A : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a
  let B : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a'
  let Y : PointedCGWH.{u, v} :=
    (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k)
  let h : E → E' := fun f => (r ⊗ₘ 𝟙 n) ≫ f
  let p : basedDiscreteObj.{u, v, 0} E ⟶ basedDiscreteObj.{u, v, 0} E' :=
    basedDiscreteFunctor.{u, v, 0}.map (↾h)
  let q : A ⟶ B := sphereSequence.{u, v}.functor.map r
  let g : discreteSmashObj.{u, v, 0} E' A ⟶ Y := coendGeneratorMap M a n k
  let g' : discreteSmashObj.{u, v, 0} E B ⟶ Y := coendGeneratorMap M a' n k
  change (p ▷ A) ≫ g = (basedDiscreteObj.{u, v, 0} E ◁ q) ≫ g'
  apply discreteSmash_hom_ext.{u, v, 0} E A
  intro f
  let j : A ⟶ discreteSmashObj.{u, v, 0} E A :=
    discreteSmashIncl.{u, v, 0} E A f
  let j' : A ⟶ discreteSmashObj.{u, v, 0} E' A :=
    discreteSmashIncl.{u, v, 0} E' A (h f)
  let jB : B ⟶ discreteSmashObj.{u, v, 0} E B :=
    discreteSmashIncl.{u, v, 0} E B f
  have hPre : j ≫ (p ▷ A) = j' := discreteSmashIncl_index h A f
  have hCoefficient : j ≫ (basedDiscreteObj.{u, v, 0} E ◁ q) = q ≫ jB :=
    discreteSmashIncl_coefficient E q f
  have hFac : j' ≫ g = curriedArrowAction M a n k (h f) :=
    coendGeneratorMap_generator M a n k (h f)
  have hFac' : jB ≫ g' = curriedArrowAction M a' n k f :=
    coendGeneratorMap_generator M a' n k f
  have hL : j ≫ ((p ▷ A) ≫ g) = curriedArrowAction M a n k (h f) :=
    (Category.assoc j (p ▷ A) g).symm.trans
      ((congrArg (fun t : A ⟶ discreteSmashObj.{u, v, 0} E' A => t ≫ g) hPre).trans
        hFac)
  have hR : j ≫ ((basedDiscreteObj.{u, v, 0} E ◁ q) ≫ g') =
      curriedArrowAction M a n k (h f) :=
    (Category.assoc j (basedDiscreteObj.{u, v, 0} E ◁ q) g').symm.trans
      ((congrArg (fun t : A ⟶ discreteSmashObj.{u, v, 0} E B => t ≫ g')
        hCoefficient).trans
        ((Category.assoc q jB g').trans
          ((congrArg (fun t : B ⟶ Y => q ≫ t) hFac').trans
            (curriedArrowAction_coefficient M r n k f))))
  exact hL.trans hR.symm

/-- The identity label recovers the complete coefficient-first module pair action. -/
theorem coendGeneratorMap_identity (a n : I) :
    MonoidalClosed.uncurry
        (discreteSmashIncl.{u, v, 0} ((a ⊗ n) ⟶ (a ⊗ n))
          (sphereSequence.{u, v}.functor.obj a) (𝟙 (a ⊗ n)) ≫ coendGeneratorMap M a n (a ⊗ n)) =
      (β_ (sphereSequence.{u, v}.functor.obj a) (M.X.functor.obj n)).inv ≫ pairAction M a n := by
  rw [coendGeneratorMap_generator]
  dsimp only [curriedArrowAction]
  rw [MonoidalClosed.uncurry_curry]
  dsimp only [arrowAction]
  rw [M.X.functor.map_id, Category.comp_id]


/-- The native point copower detects the entire enriched coend relation. -/
private theorem native_coendCondition_of_pointRelations
    {T : Type uI} [Category.{0} T]
    (W : EnrichedFunctor PointedCGWH.{u, v} (CopowerUnderlying.{u, v, 0} T)ᵒᵖ
      PointedCGWH.{u, v})
    (F : EnrichedFunctor PointedCGWH.{u, v} (CopowerUnderlying.{u, v, 0} T)
      PointedCGWH.{u, v})
    {Z : PointedCGWH.{u, v}}
    (legs : ∀ a, W.obj (Opposite.op a) ⊗ F.obj a ⟶ Z)
    (h : ∀ (a b : CopowerUnderlying.{u, v, 0} T)
      (r : (show T from a) ⟶ (show T from b)),
      let e : (𝟙_ PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] b) :=
        basedDiscreteIncl.{u, v, 0} ((show T from a) ⟶ (show T from b)) r
      (((ρ_ (W.obj (Opposite.op b))).inv ≫
          W.obj (Opposite.op b) ◁ e ≫
          MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a))) ⊗ₘ
            𝟙 (F.obj a)) ≫ legs a =
        (W.obj (Opposite.op b) ◁
          ((ρ_ (F.obj a)).inv ≫ F.obj a ◁ e ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ legs b) :
    ∀ a b,
      ((α_ (W.obj (Opposite.op b)) (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
            𝟙 (F.obj a))) ≫ legs a =
        (W.obj (Opposite.op b) ◁
          ((β_ (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ legs b := by
  intro a b
  let E : Type := (show T from a) ⟶ (show T from b)
  let U : PointedCGWH.{u, v} := W.obj (Opposite.op b)
  let U' : PointedCGWH.{u, v} := W.obj (Opposite.op a)
  let H : PointedCGWH.{u, v} := a ⟶[PointedCGWH.{u, v}] b
  let X : PointedCGWH.{u, v} := F.obj a
  let Y : PointedCGWH.{u, v} := F.obj b
  let p : U ⊗ H ⟶ U' :=
    MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a))
  let q : X ⊗ H ⟶ Y := MonoidalClosed.uncurry (F.map a b)
  let wf : U ⊗ (H ⊗ X) ⟶ U' ⊗ X := (α_ U H X).inv ≫ (p ⊗ₘ 𝟙 X)
  let df : U ⊗ (H ⊗ X) ⟶ U ⊗ Y := U ◁ ((β_ H X).hom ≫ q)
  have hGenerator (r : E) :
      (U ◁ discreteSmashIncl.{u, v, 0} E X r) ≫ (wf ≫ legs a) =
        (U ◁ discreteSmashIncl.{u, v, 0} E X r) ≫ (df ≫ legs b) := by
    let e : (𝟙_ PointedCGWH.{u, v}) ⟶ H := basedDiscreteIncl.{u, v, 0} E r
    let pre : U ⊗ X ⟶ U ⊗ (H ⊗ X) :=
      U ◁ ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X))
    let wa : U ⟶ U' := (ρ_ U).inv ≫ U ◁ e ≫ p
    let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ e ≫ q
    have hNatural :
        U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv =
          (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv ≫ ((U ◁ e) ▷ X) := by
      simpa only [id_tensorHom, tensorHom_id] using
        associator_inv_naturality (𝟙 U) e (𝟙 X)
    have hTriangle :
        U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv =
          (ρ_ U).inv ▷ X := by
      monoidal
    have hLeft : pre ≫ wf = wa ⊗ₘ 𝟙 X := by
      calc
        pre ≫ wf = U ◁ (λ_ X).inv ≫
            (U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv) ≫ (p ⊗ₘ 𝟙 X) := by
          simp only [pre, wf, whiskerLeft_comp, Category.assoc]
        _ = U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv ≫
            ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
          simpa only [Category.assoc] using congrArg
            (fun t : U ⊗ ((𝟙_ PointedCGWH.{u, v}) ⊗ X) ⟶ (U ⊗ H) ⊗ X =>
              U ◁ (λ_ X).inv ≫ t ≫ (p ⊗ₘ 𝟙 X)) hNatural
        _ = ((ρ_ U).inv ▷ X) ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
          simpa only [Category.assoc] using congrArg
            (fun t : U ⊗ X ⟶ (U ⊗ (𝟙_ PointedCGWH.{u, v})) ⊗ X =>
              t ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X)) hTriangle
        _ = wa ⊗ₘ 𝟙 X := by
          simpa only [wa, comp_whiskerRight, Category.assoc] using
            whiskerRight_comp_tensorHom ((ρ_ U).inv ≫ U ◁ e) p (𝟙 X)
    have hUnitCross :
        ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫ (β_ H X).hom =
          (ρ_ X).inv ≫ X ◁ e := by
      simpa only [id_tensorHom, Category.assoc,
        CategoryTheory.braiding_tensorUnit_left, Iso.inv_hom_id_assoc] using
        congrArg
          (fun t : (𝟙_ PointedCGWH.{u, v}) ⊗ X ⟶ X ⊗ H => (λ_ X).inv ≫ t)
          (BraidedCategory.braiding_naturality e (𝟙 X))
    have hRight : pre ≫ df = U ◁ fa := by
      calc
        pre ≫ df = U ◁ (((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫ (β_ H X).hom ≫ q) := by
          simp only [pre, df, whiskerLeft_comp, Category.assoc]
        _ = U ◁ (((ρ_ X).inv ≫ X ◁ e) ≫ q) :=
          (congrArg (fun t : X ⟶ Y => U ◁ t)
            (Category.assoc ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) (β_ H X).hom q).symm).trans
              (congrArg (fun t : X ⟶ X ⊗ H => U ◁ (t ≫ q)) hUnitCross)
        _ = U ◁ fa := by simp only [fa, Category.assoc]
    have hPoint : (wa ⊗ₘ 𝟙 X) ≫ legs a = (U ◁ fa) ≫ legs b := h a b r
    have hL : pre ≫ (wf ≫ legs a) = (wa ⊗ₘ 𝟙 X) ≫ legs a :=
      (Category.assoc pre wf (legs a)).symm.trans
        (congrArg (fun t : U ⊗ X ⟶ U' ⊗ X => t ≫ legs a) hLeft)
    have hR : pre ≫ (df ≫ legs b) = (U ◁ fa) ≫ legs b :=
      (Category.assoc pre df (legs b)).symm.trans
        (congrArg (fun t : U ⊗ X ⟶ U ⊗ Y => t ≫ legs b) hRight)
    change pre ≫ (wf ≫ legs a) = pre ≫ (df ≫ legs b)
    exact hL.trans (hPoint.trans hR.symm)
  let G : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := tensorLeft U
  have hColimit :
      CategoryTheory.Limits.IsColimit
        (G.mapCocone (discreteSmashCofan.{u, v, 0} E X)) :=
    CategoryTheory.Limits.isColimitOfPreserves G
      (discreteSmashCofanIsColimit.{u, v, 0} E X)
  change wf ≫ legs a = df ≫ legs b
  apply hColimit.hom_ext
  intro r
  change (U ◁ discreteSmashIncl.{u, v, 0} E X r.as) ≫ (wf ≫ legs a) =
    (U ◁ discreteSmashIncl.{u, v, 0} E X r.as) ≫ (df ≫ legs b)
  exact hGenerator r.as


section NativePointMaps

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

private theorem nativeRestriction_precomposition (a b k : I) (r : a ⟶ b) :
    eHomWhiskerRight PointedCGWH.{u, v}
        ((copowerRestriction.{u, v, 0} I).map r)
        ((copowerRestriction.{u, v, 0} I).obj k) =
      basedDiscreteFunctor.{u, v, 0}.map (↾fun f : b ⟶ k => r ≫ f) := by
  let V := PointedCGWH.{u, v}
  let C := CopowerUnderlying.{u, v, 0} I
  let R := copowerRestriction.{u, v, 0} I
  let E : Type := b ⟶ k
  let H : V := basedDiscreteObj.{u, v, 0} E
  let H' : V := basedDiscreteObj.{u, v, 0} (a ⟶ k)
  let t : H ⟶ H' := eHomWhiskerRight V (R.map r) (R.obj k)
  let p : H ⟶ H' := basedDiscreteFunctor.{u, v, 0}.map (↾fun f : E => r ≫ f)
  change t = p
  apply (basedDiscreteCofanIsColimit.{u, v, 0} E).hom_ext
  intro f
  let g : b ⟶ k := f.as
  let i : 𝟙_ V ⟶ H := basedDiscreteIncl.{u, v, 0} E g
  let i' : 𝟙_ V ⟶ H' := basedDiscreteIncl.{u, v, 0} (a ⟶ k) (r ≫ g)
  have hG : eHomEquiv V (R.map g) = i := copowerRestriction_map.{u, v, 0} I g
  have hRG : eHomEquiv V (R.map (r ≫ g)) = i' :=
    copowerRestriction_map.{u, v, 0} I (r ≫ g)
  have hCompose : eHomEquiv V (R.map r ≫ R.map g) = i' :=
    (congrArg (fun q : R.obj a ⟶ R.obj k => eHomEquiv V q)
      (R.map_comp r g).symm).trans hRG
  have hWhisker : eHomEquiv V (R.map g) ≫ t =
      eHomEquiv V (R.map r ≫ R.map g) :=
    eHomEquiv_comp_eHomWhiskerRight (V := V) (C := C) (R.map r) (R.map g)
  have hL : i ≫ t = i' :=
    (congrArg (fun q : (𝟙_ V) ⟶ H => q ≫ t) hG.symm).trans
      (hWhisker.trans hCompose)
  have hR : i ≫ p = i' :=
    basedDiscreteIncl_naturality.{u, v, 0} (fun f : E => r ≫ f) g
  change i ≫ t = i ≫ p
  exact hL.trans hR.symm

private theorem nativeSphere_pointMap {a b : I} (r : a ⟶ b) :
    (ρ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
        sphereSequence.{u, v}.functor.obj a ◁ basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry
          (sphereCopowerEnrichedFunctor.{u, v}.map
            ((copowerRestriction.{u, v, 0} I).obj a)
            ((copowerRestriction.{u, v, 0} I).obj b)) =
      sphereSequence.{u, v}.functor.map r := by
  let V := PointedCGWH.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let H : V := basedDiscreteObj.{u, v, 0} (a ⟶ b)
  let e : (𝟙_ V) ⟶ H := basedDiscreteIncl.{u, v, 0} (a ⟶ b) r
  let p : H ⟶ (ihom A).obj B :=
    sphereCopowerEnrichedFunctor.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj a)
      ((copowerRestriction.{u, v, 0} I).obj b)
  let q : A ⟶ B := sphereSequence.{u, v}.functor.map r
  have hGen : e ≫ p = eHomEquiv V q :=
    originalDiagramHomMap_generator.{u, v, 0} sphereSequence.{u, v}.functor r
  have hInverse :
      MonoidalClosed.uncurry' (eHomEquiv V q) = q :=
    (MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm V
      (eHomEquiv V q)).symm.trans ((eHomEquiv V).symm_apply_apply q)
  have h : MonoidalClosed.uncurry' (e ≫ p) = q :=
    (congrArg
      (fun t : (𝟙_ V) ⟶ (ihom A).obj B => MonoidalClosed.uncurry' t) hGen).trans
        hInverse
  dsimp only [MonoidalClosed.uncurry'] at h
  rw [MonoidalClosed.uncurry_natural_left] at h
  change (ρ_ A).inv ≫ A ◁ e ≫ MonoidalClosed.uncurry p = q
  simpa only [Category.assoc] using h

private theorem nativeWeight_pointMap (n k a b : I) (r : a ⟶ b) :
    let W := Enriched.SphereOperator.weight
      (copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
    (ρ_ (W.obj (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b)))).inv ≫
        W.obj (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b)) ◁
          basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry
          (W.map (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b))
            (Opposite.op ((copowerRestriction.{u, v, 0} I).obj a))) =
      basedDiscreteFunctor.{u, v, 0}.map
        (↾fun f : (b ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let W := Enriched.SphereOperator.weight d (R.obj n) (R.obj k)
  have hPoint : eHomEquiv V (R.map r) =
      basedDiscreteIncl.{u, v, 0} (a ⟶ b) r := copowerRestriction_map.{u, v, 0} I r
  have hTensor : R.map r ⊗ₘ 𝟙 (R.obj n) = R.map (r ⊗ₘ 𝟙 n) :=
    (congrArg (fun q : R.obj n ⟶ R.obj n => R.map r ⊗ₘ q) (R.map_id n).symm).trans
      (copowerUnderlyingMonoidal_tensor_original.{u, v, 0} I r (𝟙 n))
  have h := Enriched.SphereOperator.weight_point_pre d (R.obj n) (R.obj k)
    (R.obj a) (R.obj b) (R.map r)
  rw [hPoint] at h
  have hWhisker :
      eHomWhiskerRight V (R.map r ⊗ₘ 𝟙 (R.obj n)) (R.obj k) =
        eHomWhiskerRight V (R.map (r ⊗ₘ 𝟙 n)) (R.obj k) :=
    congrArg
      (fun q : R.obj (a ⊗ n) ⟶ R.obj (b ⊗ n) => eHomWhiskerRight V q (R.obj k))
      hTensor
  exact h.trans (hWhisker.trans (nativeRestriction_precomposition (a ⊗ n) (b ⊗ n)
    k (r ⊗ₘ 𝟙 n)))

end NativePointMaps


section NativeCoendDescent

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The full native enriched relation follows from the actual module coefficient square. -/
theorem coendGeneratorMap_balanced (n k : I) :
    let R := copowerRestriction.{u, v, 0} I
    let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
      (R.obj n) (R.obj k)
    let F := sphereCopowerEnrichedFunctor.{u, v}
    ∀ a b : CopowerUnderlying.{u, v, 0} I,
      ((α_ (W.obj (Opposite.op b)) (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
            𝟙 (F.obj a))) ≫ coendGeneratorMap M (show I from a) n k =
        (W.obj (Opposite.op b) ◁
          ((β_ (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫
              coendGeneratorMap M (show I from b) n k := by
  let R := copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  let F := sphereCopowerEnrichedFunctor.{u, v}
  change ∀ a b : CopowerUnderlying.{u, v, 0} I,
    ((α_ (W.obj (Opposite.op b)) (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
          𝟙 (F.obj a))) ≫ coendGeneratorMap M (show I from a) n k =
      (W.obj (Opposite.op b) ◁
        ((β_ (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))) ≫
            coendGeneratorMap M (show I from b) n k
  apply native_coendCondition_of_pointRelations W F
    (fun a => coendGeneratorMap M (show I from a) n k)
  intro a b r
  let a₀ : I := a
  let b₀ : I := b
  have hWeight := nativeWeight_pointMap n k a₀ b₀ r
  have hSphere := nativeSphere_pointMap r
  change
    (((ρ_ (W.obj (Opposite.op b))).inv ≫ W.obj (Opposite.op b) ◁
      basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
      MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a))) ⊗ₘ
      𝟙 (sphereSequence.{u, v}.functor.obj a₀)) ≫ coendGeneratorMap M a₀ n k =
    (W.obj (Opposite.op b) ◁
      ((ρ_ (sphereSequence.{u, v}.functor.obj a₀)).inv ≫ sphereSequence.{u, v}.functor.obj a₀ ◁
        basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
        MonoidalClosed.uncurry (F.map a b))) ≫ coendGeneratorMap M b₀ n k
  let A : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a₀
  let B : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj b₀
  let p : W.obj (Opposite.op b) ⟶ W.obj (Opposite.op a) :=
    basedDiscreteFunctor.{u, v, 0}.map
      (↾fun f : (b₀ ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f)
  have hW : (ρ_ (W.obj (Opposite.op b))).inv ≫
      W.obj (Opposite.op b) ◁ basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
        MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) = p :=
    hWeight
  have hS : (ρ_ A).inv ≫ A ◁ basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
      MonoidalClosed.uncurry (F.map a b) = sphereSequence.{u, v}.functor.map r :=
    hSphere
  have hLeft := congrArg
    (fun z : W.obj (Opposite.op b) ⟶ W.obj (Opposite.op a) =>
      (z ⊗ₘ 𝟙 A) ≫ coendGeneratorMap M a₀ n k) hW
  have hRight := congrArg
    (fun z : A ⟶ B => (W.obj (Opposite.op b) ◁ z) ≫ coendGeneratorMap M b₀ n k) hS
  have hCanonicalBase : (p ▷ A) ≫ coendGeneratorMap M a₀ n k =
      (W.obj (Opposite.op b) ◁ sphereSequence.{u, v}.functor.map r) ≫
        coendGeneratorMap M b₀ n k :=
    coendGeneratorMap_coefficient M r n k
  have hCanonical : (p ⊗ₘ 𝟙 A) ≫ coendGeneratorMap M a₀ n k =
      (W.obj (Opposite.op b) ◁ sphereSequence.{u, v}.functor.map r) ≫
        coendGeneratorMap M b₀ n k :=
    (congrArg
      (fun z : W.obj (Opposite.op b) ⊗ A ⟶ W.obj (Opposite.op a) ⊗ A =>
        z ≫ coendGeneratorMap M a₀ n k) (MonoidalCategory.tensorHom_id p A)).trans
      hCanonicalBase
  exact hLeft.trans (hCanonical.trans hRight.symm)

/-- Descend all native Hom and sphere coefficients to the actual internal Hom of the levels. -/
def operatorHomMap (n k : I) :
    Enriched.SphereOperator.Hom
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k) ⟶
      (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k) :=
  Enriched.weightedCoend.desc
    (Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k))
    sphereCopowerEnrichedFunctor.{u, v}
    (fun a => coendGeneratorMap M (show I from a) n k)
    (coendGeneratorMap_balanced M n k)

/-- Every whole native coend summand retains its original entire coefficient leg. -/
theorem operatorHomMap_generator (n k : I) (a : CopowerUnderlying.{u, v, 0} I) :
    Enriched.weightedCoend.ι
        (Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
          ((copowerRestriction.{u, v, 0} I).obj n)
          ((copowerRestriction.{u, v, 0} I).obj k))
        sphereCopowerEnrichedFunctor.{u, v} a ≫ operatorHomMap M n k =
      coendGeneratorMap M (show I from a) n k :=
  Enriched.weightedCoend.ι_desc
    (Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k))
    sphereCopowerEnrichedFunctor.{u, v}
    (fun a => coendGeneratorMap M (show I from a) n k)
    (coendGeneratorMap_balanced M n k) a

end NativeCoendDescent


/-- The literal Day module unit acts as the unit on the original whole pair component. -/
theorem pairAction_unit (n : I) :
    MonoidalCategory.whiskerRight (C := PointedCGWH.{u, v})
        (sphereCopowerLaxData.{u, v}.epsilon :
          (𝟙_ PointedCGWH.{u, v}) ⟶ sphereSequence.{u, v}.functor.obj (𝟙_ I))
        (M.X.functor.obj n) ≫ pairAction M (𝟙_ I) n =
      (MonoidalCategory.leftUnitor (C := PointedCGWH.{u, v})
          (M.X.functor.obj n)).hom ≫
        M.X.functor.map (MonoidalCategory.leftUnitor (C := I) n).inv := by
  let e : (𝟙_ PointedCGWH.{u, v}) ⟶ sphereSequence.{u, v}.functor.obj (𝟙_ I) :=
    DayFunctor.ν I PointedCGWH.{u, v} ≫ sphereSequenceMonObj.one.natTrans.app (𝟙_ I)
  have he : e = sphereCopowerLaxData.{u, v}.epsilon := sphereCopowerLaxData_one.{u, v}
  have hBase : (e ▷ M.X.functor.obj n) ≫ pairAction M (𝟙_ I) n =
      (λ_ (M.X.functor.obj n)).hom ≫ M.X.functor.map (λ_ n).inv :=
    CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.modulePairUnit
      (C₀ := I) (V₀ := PointedCGWH.{u, v}) (D₀ := SymmetricSequence.{u, v})
      sphereSequence.{u, v} M.X n
  have hUnit : (e ▷ M.X.functor.obj n) ≫ pairAction M (𝟙_ I) n =
      (sphereCopowerLaxData.{u, v}.epsilon ▷ M.X.functor.obj n) ≫ pairAction M (𝟙_ I) n :=
    congrArg
      (fun z : (𝟙_ PointedCGWH.{u, v}) ⟶ sphereSequence.{u, v}.functor.obj (𝟙_ I) =>
        (z ▷ M.X.functor.obj n) ≫ pairAction M (𝟙_ I) n) he
  exact hUnit.symm.trans hBase

/-- The actual coefficient unit and original left-unitor label act as the level identity. -/
theorem arrowAction_unit (n : I) :
    (sphereCopowerLaxData.{u, v}.epsilon ▷ M.X.functor.obj n) ≫
        arrowAction M (𝟙_ I) n n (λ_ n).hom = (λ_ (M.X.functor.obj n)).hom := by
  let X : PointedCGWH.{u, v} := M.X.functor.obj n
  have h := congrArg
    (fun f : (𝟙_ PointedCGWH.{u, v}) ⊗ X ⟶ M.X.functor.obj ((𝟙_ I) ⊗ n) =>
      f ≫ M.X.functor.map (λ_ n).hom) (pairAction_unit M n)
  have hInverse :
      M.X.functor.map (λ_ n).inv ≫ M.X.functor.map (λ_ n).hom = 𝟙 X := by
    rw [← M.X.functor.map_comp, Iso.inv_hom_id, M.X.functor.map_id]
  change (sphereCopowerLaxData.{u, v}.epsilon ▷ X) ≫
    (pairAction M (𝟙_ I) n ≫ M.X.functor.map (λ_ n).hom) = (λ_ X).hom
  exact (Category.assoc (sphereCopowerLaxData.{u, v}.epsilon ▷ X)
    (pairAction M (𝟙_ I) n) (M.X.functor.map (λ_ n).hom)).symm.trans
      (h.trans ((Category.assoc (λ_ X).hom
        (M.X.functor.map (λ_ n).inv) (M.X.functor.map (λ_ n).hom)).trans
          ((congrArg (fun f : X ⟶ X => (λ_ X).hom ≫ f) hInverse).trans
            (Category.comp_id (λ_ X).hom))))

section NativeOperatorUnit

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The actual coefficient unit and complete native Hom descent preserve the operator identity. -/
theorem operatorHomMap_id (n : I) :
    Enriched.SphereOperator.identityGenerator
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v} ((copowerRestriction.{u, v, 0} I).obj n) ≫
      operatorHomMap M n n = eId PointedCGWH.{u, v} (M.X.functor.obj n) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let X : V := M.X.functor.obj n
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let U : V := 𝟙_ V
  let E : Type := ((𝟙_ I) ⊗ n) ⟶ n
  let P : V := basedDiscreteObj.{u, v, 0} E ⊗ A
  let H : V := Enriched.SphereOperator.Hom d F (R.obj n) (R.obj n)
  let ε : U ⟶ A := L.epsilon
  let p : U ⟶ basedDiscreteObj.{u, v, 0} E :=
    basedDiscreteIncl.{u, v, 0} E (λ_ n).hom
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} E A (λ_ n).hom
  let i : P ⟶ H :=
    Enriched.weightedCoend.ι (Enriched.SphereOperator.weight d (R.obj n) (R.obj n))
      F (R.obj (𝟙_ I))
  let q : P ⟶ (ihom X).obj X := coendGeneratorMap M (𝟙_ I) n n
  let f : H ⟶ (ihom X).obj X := operatorHomMap M n n
  have hPoint : eHomEquiv V (λ_ (R.obj n)).hom = p := by
    change eHomEquiv V (R.map (λ_ n).hom) = p
    exact copowerRestriction_map.{u, v, 0} I (λ_ n).hom
  have hj : j = (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := rfl
  have hPairPad : (λ_ U).inv ≫ (p ⊗ₘ ε) =
      ε ≫ (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := by
    simpa only [MonoidalCategory.tensorHom_id] using
      MonoidalCategory.leftUnitor_inv_comp_tensorHom p ε
  have hPair : (λ_ U).inv ≫ (p ⊗ₘ ε) = ε ≫ j :=
    hPairPad.trans (congrArg (fun z : A ⟶ P => ε ≫ z) hj.symm)
  have hIdentity : Enriched.SphereOperator.identityGenerator d F L (R.obj n) =
      ε ≫ j ≫ i := by
    have hLiteral : Enriched.SphereOperator.identityGenerator d F L (R.obj n) =
        (λ_ U).inv ≫ (eHomEquiv V (λ_ (R.obj n)).hom ⊗ₘ ε) ≫ i := rfl
    have hPointPad := congrArg
      (fun z : U ⟶ basedDiscreteObj.{u, v, 0} E => (λ_ U).inv ≫ (z ⊗ₘ ε) ≫ i) hPoint
    have hLast : (λ_ U).inv ≫ (p ⊗ₘ ε) ≫ i = ε ≫ j ≫ i :=
      (Category.assoc (λ_ U).inv (p ⊗ₘ ε) i).symm.trans
        ((congrArg (fun z : U ⟶ P => z ≫ i) hPair).trans (Category.assoc ε j i))
    exact hLiteral.trans (hPointPad.trans hLast)
  have hGenerator : i ≫ f = q := operatorHomMap_generator M n n (R.obj (𝟙_ I))
  have hPointAction : j ≫ i ≫ f = curriedArrowAction M (𝟙_ I) n n (λ_ n).hom := by
    calc
      _ = j ≫ q := congrArg (fun z : P ⟶ (ihom X).obj X => j ≫ z) hGenerator
      _ = _ := coendGeneratorMap_generator M (𝟙_ I) n n (λ_ n).hom
  have hResult : Enriched.SphereOperator.identityGenerator d F L (R.obj n) ≫ f =
      ε ≫ curriedArrowAction M (𝟙_ I) n n (λ_ n).hom := by
    rw [hIdentity]
    simpa only [Category.assoc] using congrArg
      (fun z : A ⟶ (ihom X).obj X => ε ≫ z) hPointAction
  have hBraid : (X ◁ ε) ≫ (β_ A X).inv =
      (β_ U X).inv ≫ (ε ▷ X) :=
    BraidedCategory.braiding_inv_naturality_right X ε
  have hUnit : (ε ▷ X) ≫ arrowAction M (𝟙_ I) n n (λ_ n).hom =
      (λ_ X).hom := arrowAction_unit M n
  apply MonoidalClosed.uncurry_injective
  change MonoidalClosed.uncurry
      (Enriched.SphereOperator.identityGenerator d F L (R.obj n) ≫ f) =
    MonoidalClosed.uncurry (eId V X)
  rw [hResult, MonoidalClosed.uncurry_natural_left]
  dsimp only [curriedArrowAction]
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
  calc
    _ = (β_ U X).inv ≫ (ε ▷ X) ≫ arrowAction M (𝟙_ I) n n (λ_ n).hom := by
      simpa only [Category.assoc] using congrArg
        (fun z : X ⊗ U ⟶ A ⊗ X => z ≫ arrowAction M (𝟙_ I) n n (λ_ n).hom)
        hBraid
    _ = (β_ U X).inv ≫ (λ_ X).hom :=
      congrArg (fun z : U ⊗ X ⟶ X => (β_ U X).inv ≫ z) hUnit
    _ = (ρ_ X).hom := by
      rw [CategoryTheory.braiding_inv_tensorUnit_left, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]

end NativeOperatorUnit

section NativeDayMultiplication

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The whole Day module multiplication has the original late-first coefficient order. -/
theorem pairAction_mul (b a n : I) :
    MonoidalCategory.whiskerRight (C := PointedCGWH.{u, v})
        (sphereCopowerLaxData.{u, v}.mu
            ((copowerRestriction.{u, v, 0} I).obj b)
            ((copowerRestriction.{u, v, 0} I).obj a) :
          sphereSequence.{u, v}.functor.obj b ⊗ sphereSequence.{u, v}.functor.obj a ⟶
            sphereSequence.{u, v}.functor.obj (b ⊗ a))
        (M.X.functor.obj n) ≫ pairAction M (b ⊗ a) n =
    (MonoidalCategory.associator (C := PointedCGWH.{u, v})
        (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
        (M.X.functor.obj n)).hom ≫
      MonoidalCategory.whiskerLeft (C := PointedCGWH.{u, v})
        (sphereSequence.{u, v}.functor.obj b) (pairAction M a n) ≫
      pairAction M b (a ⊗ n) ≫
        M.X.functor.map (MonoidalCategory.associator (C := I) b a n).inv := by
  let μ₀ : sphereSequence.{u, v}.functor.obj b ⊗ sphereSequence.{u, v}.functor.obj a ⟶
      sphereSequence.{u, v}.functor.obj (b ⊗ a) :=
    (DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ≫
      sphereSequenceMonObj.mul.natTrans.app (b ⊗ a)
  have hCoefficient : μ₀ = sphereCopowerLaxData.{u, v}.mu
      ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a) :=
    sphereCopowerLaxData_mul.{u, v} b a
  have hBase : (μ₀ ▷ M.X.functor.obj n) ≫ pairAction M (b ⊗ a) n =
      (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
          (M.X.functor.obj n)).hom ≫
        (sphereSequence.{u, v}.functor.obj b ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ M.X.functor.map (α_ b a n).inv :=
    CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.modulePairMul
      (C₀ := I) (V₀ := PointedCGWH.{u, v}) (D₀ := SymmetricSequence.{u, v})
      sphereSequence.{u, v} M.X b a n
  have hBridge : (μ₀ ▷ M.X.functor.obj n) ≫ pairAction M (b ⊗ a) n =
      (sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a) ▷
          M.X.functor.obj n) ≫ pairAction M (b ⊗ a) n :=
    congrArg
      (fun z : sphereSequence.{u, v}.functor.obj b ⊗ sphereSequence.{u, v}.functor.obj a ⟶
          sphereSequence.{u, v}.functor.obj (b ⊗ a) =>
        (z ▷ M.X.functor.obj n) ≫ pairAction M (b ⊗ a) n) hCoefficient
  exact hBridge.symm.trans hBase

/-- Every two original arrow actions multiply with the actual source associator label. -/
theorem arrowAction_comp (a b n k l : I) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ▷ M.X.functor.obj n) ≫
      arrowAction M (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) =
    (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
        (M.X.functor.obj n)).hom ≫
      (sphereSequence.{u, v}.functor.obj b ◁ arrowAction M a n k f) ≫ arrowAction M b k l g := by
  let X : I ⥤ PointedCGWH.{u, v} := M.X.functor
  let A : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a
  let B : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj b
  let μ₀ : B ⊗ A ⟶ sphereSequence.{u, v}.functor.obj (b ⊗ a) :=
    sphereCopowerLaxData.{u, v}.mu
    ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a)
  let h : (b ⊗ a) ⊗ n ⟶ l := (α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g
  have hLabel : (α_ b a n).inv ≫ h = (𝟙 b ⊗ₘ f) ≫ g := by
    dsimp only [h]
    rw [Iso.inv_hom_id_assoc]
  have hMap : X.map (α_ b a n).inv ≫ X.map h =
      X.map (𝟙 b ⊗ₘ f) ≫ X.map g := by
    rw [← X.map_comp, hLabel, X.map_comp]
  have hInput : pairAction M b (a ⊗ n) ≫ X.map (𝟙 b ⊗ₘ f) ≫ X.map g =
      (B ◁ X.map f) ≫ pairAction M b k ≫ X.map g := by
    simpa only [Category.assoc] using congrArg
      (fun z : B ⊗ X.obj (a ⊗ n) ⟶ X.obj (b ⊗ k) => z ≫ X.map g)
      (pairAction_input M b f).symm
  have hProduct : (μ₀ ▷ X.obj n) ≫ pairAction M (b ⊗ a) n =
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ X.map (α_ b a n).inv :=
    pairAction_mul M b a n
  have hFirst : (μ₀ ▷ X.obj n) ≫ pairAction M (b ⊗ a) n ≫ X.map h =
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ X.map (α_ b a n).inv ≫ X.map h := by
    simpa only [Category.assoc] using congrArg
      (fun z : (B ⊗ A) ⊗ X.obj n ⟶ X.obj ((b ⊗ a) ⊗ n) => z ≫ X.map h)
      hProduct
  have hSecond :
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ X.map (α_ b a n).inv ≫ X.map h =
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ X.map (𝟙 b ⊗ₘ f) ≫ X.map g :=
    congrArg
      (fun z : X.obj (b ⊗ (a ⊗ n)) ⟶ X.obj l =>
        (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
          pairAction M b (a ⊗ n) ≫ z) hMap
  have hThird :
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        pairAction M b (a ⊗ n) ≫ X.map (𝟙 b ⊗ₘ f) ≫ X.map g =
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        (B ◁ X.map f) ≫ pairAction M b k ≫ X.map g :=
    congrArg
      (fun z : B ⊗ X.obj (a ⊗ n) ⟶ X.obj l =>
        (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫ z) hInput
  have hFourth :
      (α_ B A (X.obj n)).hom ≫ (B ◁ pairAction M a n) ≫
        (B ◁ X.map f) ≫ pairAction M b k ≫ X.map g =
      (α_ B A (X.obj n)).hom ≫
        (B ◁ (pairAction M a n ≫ X.map f)) ≫
        (pairAction M b k ≫ X.map g) := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  change (μ₀ ▷ X.obj n) ≫ pairAction M (b ⊗ a) n ≫ X.map h =
    (α_ B A (X.obj n)).hom ≫
      (B ◁ (pairAction M a n ≫ X.map f)) ≫ (pairAction M b k ≫ X.map g)
  exact hFirst.trans (hSecond.trans (hThird.trans hFourth))

private theorem nativeArrowBraidShuffle (X A B : PointedCGWH.{u, v}) :
    (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫ (β_ B (A ⊗ X)).inv =
      (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (α_ B A X).hom := by
  -- Native smash symmetry is already part of the original symmetric-sequence base.
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding A X,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding B (A ⊗ X),
    ← SymmetricCategory.braiding_swap_eq_inv_braiding (B ⊗ A) X]
  simpa only [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using (BraidedCategory.yang_baxter X A B)

/-- The complete curried arrow actions preserve every coefficient product and index composite. -/
theorem curriedArrowAction_comp (a b n k l : I) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (curriedArrowAction M a n k f ⊗ₘ curriedArrowAction M b k l g) ≫
      eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k)
        (M.X.functor.obj l) =
    (β_ (sphereSequence.{u, v}.functor.obj a) (sphereSequence.{u, v}.functor.obj b)).hom ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      curriedArrowAction M (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  let V := PointedCGWH.{u, v}
  let A := sphereSequence.{u, v}.functor.obj a
  let B := sphereSequence.{u, v}.functor.obj b
  let C := sphereSequence.{u, v}.functor.obj (b ⊗ a)
  let X := M.X.functor.obj n
  let Y := M.X.functor.obj k
  let Z := M.X.functor.obj l
  let h : (b ⊗ a) ⊗ n ⟶ l := (α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g
  let u₀ : A ⊗ X ⟶ Y := arrowAction M a n k f
  let v₀ : B ⊗ Y ⟶ Z := arrowAction M b k l g
  let w₀ : C ⊗ X ⟶ Z := arrowAction M (b ⊗ a) n l h
  let μ₀ : B ⊗ A ⟶ C := sphereCopowerLaxData.{u, v}.mu
    ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a)
  have hAction : (μ₀ ▷ X) ≫ w₀ = (α_ B A X).hom ≫ (B ◁ u₀) ≫ v₀ :=
    arrowAction_comp M a b n k l f g
  have hBraid : (X ◁ μ₀) ≫ (β_ C X).inv =
      (β_ (B ⊗ A) X).inv ≫ (μ₀ ▷ X) :=
    BraidedCategory.braiding_inv_naturality_right X μ₀
  have hLeft : MonoidalClosed.uncurry
      ((curriedArrowAction M a n k f ⊗ₘ curriedArrowAction M b k l g) ≫
        eComp V X Y Z) =
      (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫
        (β_ B (A ⊗ X)).inv ≫ (B ◁ u₀) ≫ v₀ := by
    rw [MonoidalClosed.uncurry_eComp]
    simp only [curriedArrowAction, MonoidalClosed.uncurry_curry,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [BraidedCategory.braiding_inv_naturality_left_assoc]
  have hRight : MonoidalClosed.uncurry
      ((β_ A B).hom ≫ μ₀ ≫ curriedArrowAction M (b ⊗ a) n l h) =
      (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫
        (α_ B A X).hom ≫ (B ◁ u₀) ≫ v₀ := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left]
    simp only [curriedArrowAction, MonoidalClosed.uncurry_curry]
    calc
      _ = (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (μ₀ ▷ X) ≫ w₀ := by
        simpa only [Category.assoc] using congrArg
          (fun z : X ⊗ (B ⊗ A) ⟶ C ⊗ X => (X ◁ (β_ A B).hom) ≫ z ≫ w₀)
          hBraid
      _ = _ := congrArg
        (fun z : (B ⊗ A) ⊗ X ⟶ Z =>
          (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ z) hAction
  apply MonoidalClosed.uncurry_injective
  calc
    _ = (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫
        (β_ B (A ⊗ X)).inv ≫ (B ◁ u₀) ≫ v₀ := hLeft
    _ = (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫
        (α_ B A X).hom ≫ (B ◁ u₀) ≫ v₀ := by
      simpa only [Category.assoc] using congrArg
        (fun z : X ⊗ (A ⊗ B) ⟶ B ⊗ (A ⊗ X) => z ≫ (B ◁ u₀) ≫ v₀)
        (nativeArrowBraidShuffle X A B)
    _ = _ := hRight.symm

private theorem nativeDiscretePair_delta {E G : Type}
    (A B : PointedCGWH.{u, v}) (f : E) (g : G) :
    (discreteSmashIncl.{u, v, 0} E A f ⊗ₘ discreteSmashIncl.{u, v, 0} G B g) ≫
      MonoidalCategory.tensorδ (basedDiscreteObj.{u, v, 0} E)
        (basedDiscreteObj.{u, v, 0} G) A B =
    (λ_ (A ⊗ B)).inv ≫
      (basedDiscretePairIncl.{u, v, 0} E G f g ⊗ₘ 𝟙 (A ⊗ B)) := by
  let V := PointedCGWH.{u, v}
  let U : V := 𝟙_ V
  let P : V := basedDiscreteObj.{u, v, 0} E
  let Q : V := basedDiscreteObj.{u, v, 0} G
  let p : U ⟶ P := basedDiscreteIncl.{u, v, 0} E f
  let q : U ⟶ Q := basedDiscreteIncl.{u, v, 0} G g
  have hNatural : ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫
      MonoidalCategory.tensorδ P Q A B =
    MonoidalCategory.tensorδ U U A B ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by
    have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
      (show (U, U) ⟶ (P, Q) from (p, q))
      (show (A, B) ⟶ (A, B) from (𝟙 A, 𝟙 B))
    simp only [MonoidalCategory.tensor_δ] at h
    change MonoidalCategory.tensorδ U U A B ≫
        ((p ⊗ₘ q) ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) =
      ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫
        MonoidalCategory.tensorδ P Q A B at h
    simpa only [MonoidalCategory.id_tensorHom_id] using h.symm
  have hUnit : ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫
      MonoidalCategory.tensorδ U U A B =
    (λ_ (A ⊗ B)).inv ≫ ((λ_ U).inv ⊗ₘ 𝟙 (A ⊗ B)) := by
    dsimp only [MonoidalCategory.tensorδ]
    rw [CategoryTheory.braiding_inv_tensorUnit_left]
    monoidal
  have hPre : discreteSmashIncl.{u, v, 0} E A f ⊗ₘ
      discreteSmashIncl.{u, v, 0} G B g =
    ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫ ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) :=
    (MonoidalCategory.tensorHom_comp_tensorHom
      (λ_ A).inv (λ_ B).inv (p ⊗ₘ 𝟙 A) (q ⊗ₘ 𝟙 B)).symm
  calc
    _ = ((λ_ A).inv ⊗ₘ (λ_ B).inv) ≫
        MonoidalCategory.tensorδ U U A B ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by
      rw [hPre, Category.assoc, hNatural]
    _ = (λ_ (A ⊗ B)).inv ≫ ((λ_ U).inv ⊗ₘ 𝟙 (A ⊗ B)) ≫
        ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by
      simpa only [Category.assoc] using congrArg
        (fun z : A ⊗ B ⟶ (U ⊗ U) ⊗ (A ⊗ B) =>
          z ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B))) hUnit
    _ = (λ_ (A ⊗ B)).inv ≫ (((λ_ U).inv ≫ (p ⊗ₘ q)) ⊗ₘ 𝟙 (A ⊗ B)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    _ = _ := rfl

private theorem nativeIndexGenerator_point (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    basedDiscretePairIncl.{u, v, 0} (a ⊗ n ⟶ k) (b ⊗ k ⟶ l) f g ≫
      Enriched.SphereOperator.indexGenerator (copowerUnderlyingMonoidalData.{u, v, 0} I)
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l)
        ((copowerRestriction.{u, v, 0} I).obj a)
        ((copowerRestriction.{u, v, 0} I).obj b) =
    basedDiscreteIncl.{u, v, 0} ((b ⊗ a) ⊗ n ⟶ l)
      ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  let V := PointedCGWH.{u, v}
  let U : V := 𝟙_ V
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let a₀ : CopowerUnderlying.{u, v, 0} I := R.obj a
  let b₀ : CopowerUnderlying.{u, v, 0} I := R.obj b
  let n₀ : CopowerUnderlying.{u, v, 0} I := R.obj n
  let k₀ : CopowerUnderlying.{u, v, 0} I := R.obj k
  let l₀ : CopowerUnderlying.{u, v, 0} I := R.obj l
  let f₀ : a₀ ⊗ n₀ ⟶ k₀ := R.map f
  let g₀ : b₀ ⊗ k₀ ⟶ l₀ := R.map g
  let A : V := (a₀ ⊗ n₀) ⟶[V] k₀
  let B : V := (b₀ ⊗ k₀) ⟶[V] l₀
  let C : V := (b₀ ⊗ (a₀ ⊗ n₀)) ⟶[V] (b₀ ⊗ k₀)
  let D : V := (b₀ ⊗ (a₀ ⊗ n₀)) ⟶[V] l₀
  let E : V := ((b₀ ⊗ a₀) ⊗ n₀) ⟶[V] l₀
  let p : U ⟶ A := eHomEquiv V f₀
  let q : U ⟶ B := eHomEquiv V g₀
  let t : (b₀ ⟶[V] b₀) ⊗ A ⟶ C := d.tensorMap b₀ b₀ (a₀ ⊗ n₀) k₀
  let j : A ⟶ C := (λ_ A).inv ≫ (eId V b₀ ⊗ₘ 𝟙 A) ≫ t
  let h : b₀ ⊗ (a₀ ⊗ n₀) ⟶ b₀ ⊗ k₀ := 𝟙 b₀ ⊗ₘ f₀
  let αI : (b₀ ⊗ a₀) ⊗ n₀ ⟶ b₀ ⊗ (a₀ ⊗ n₀) := (α_ b₀ a₀ n₀).hom
  let pre : D ⟶ E := eHomWhiskerRight V αI l₀
  have hTensor : (U ◁ p) ≫ (eId V b₀ ⊗ₘ 𝟙 A) = eId V b₀ ⊗ₘ p := by
    simpa only [MonoidalCategory.id_tensorHom, Category.id_comp, Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) p (eId V b₀) (𝟙 A)
  have hShift : p ≫ j =
      (λ_ U).inv ≫ (U ◁ p) ≫ (eId V b₀ ⊗ₘ 𝟙 A) ≫ t := by
    dsimp only [j]
    rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
  have hTensorShift :
      (λ_ U).inv ≫ (U ◁ p) ≫ (eId V b₀ ⊗ₘ 𝟙 A) ≫ t =
      (λ_ U).inv ≫ (eId V b₀ ⊗ₘ p) ≫ t := by
    simpa only [Category.assoc] using congrArg
      (fun z : U ⊗ U ⟶ (b₀ ⟶[V] b₀) ⊗ A => (λ_ U).inv ≫ z ≫ t) hTensor
  have hMapPoint : (λ_ U).inv ≫ (eId V b₀ ⊗ₘ p) ≫ t = eHomEquiv V h := by
    have hBase := d.tensorMap_eHomEquiv (𝟙 b₀) f₀
    rw [eHomEquiv_id] at hBase
    exact hBase
  have hPoint : p ≫ j = eHomEquiv V h := hShift.trans (hTensorShift.trans hMapPoint)
  have hMap : h = R.map (𝟙 b ⊗ₘ f) := by
    dsimp only [h, f₀]
    have hId : 𝟙 b₀ = R.map (𝟙 b) := (R.map_id b).symm
    rw [hId]
    exact copowerUnderlyingMonoidal_tensor_original.{u, v, 0} I (𝟙 b) f
  have hAssoc : αI = R.map (α_ b a n).hom := rfl
  have hLabel : αI ≫ h ≫ g₀ = R.map ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
    rw [hAssoc, hMap]
    dsimp only [g₀]
    simp only [R.map_comp]
    rfl
  have hRaw : Enriched.SphereOperator.indexGenerator d n₀ k₀ l₀ a₀ b₀ =
      (j ⊗ₘ 𝟙 B) ≫ eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀ ≫ pre := by
    simp only [Enriched.SphereOperator.indexGenerator, j, t, pre, αI, A, B, C,
      eHomWhiskerRight, MonoidalCategory.tensorHom_id, Category.assoc]
    rfl
  have hPair : basedDiscretePairIncl.{u, v, 0} (a ⊗ n ⟶ k) (b ⊗ k ⟶ l) f g =
      (λ_ U).inv ≫ (p ⊗ₘ q) := rfl
  have hTensorPair : (p ⊗ₘ q) ≫ (j ⊗ₘ 𝟙 B) = (p ≫ j) ⊗ₘ q := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hPointPair : ((λ_ U).inv ≫ (p ⊗ₘ q)) ≫ (j ⊗ₘ 𝟙 B) =
      (λ_ U).inv ≫ ((p ≫ j) ⊗ₘ q) :=
    (Category.assoc (λ_ U).inv (p ⊗ₘ q) (j ⊗ₘ 𝟙 B)).trans
      (congrArg (fun z : U ⊗ U ⟶ C ⊗ B => (λ_ U).inv ≫ z) hTensorPair)
  have hFirst : basedDiscretePairIncl.{u, v, 0} (a ⊗ n ⟶ k) (b ⊗ k ⟶ l) f g ≫
      Enriched.SphereOperator.indexGenerator d n₀ k₀ l₀ a₀ b₀ =
      (λ_ U).inv ≫ ((p ≫ j) ⊗ₘ q) ≫
        eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀ ≫ pre := by
    rw [hRaw, hPair]
    let c : C ⊗ B ⟶ D := eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀
    change ((λ_ U).inv ≫ (p ⊗ₘ q)) ≫ (j ⊗ₘ 𝟙 B) ≫ c ≫ pre =
      (λ_ U).inv ≫ ((p ≫ j) ⊗ₘ q) ≫ c ≫ pre
    exact (Category.assoc ((λ_ U).inv ≫ (p ⊗ₘ q)) (j ⊗ₘ 𝟙 B) (c ≫ pre)).symm.trans
      ((congrArg (fun z : U ⟶ C ⊗ B => z ≫ (c ≫ pre)) hPointPair).trans
        (Category.assoc (λ_ U).inv ((p ≫ j) ⊗ₘ q) (c ≫ pre)))
  have hSecond :
      (λ_ U).inv ≫ ((p ≫ j) ⊗ₘ q) ≫
        eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀ ≫ pre =
      (λ_ U).inv ≫ (eHomEquiv V h ⊗ₘ q) ≫
        eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀ ≫ pre := by
    rw [hPoint]
  have hThird : (λ_ U).inv ≫ (eHomEquiv V h ⊗ₘ q) ≫
      eComp V (b₀ ⊗ (a₀ ⊗ n₀)) (b₀ ⊗ k₀) l₀ ≫ pre =
      eHomEquiv V (h ≫ g₀) ≫ pre := by
    dsimp only [q, U, V]
    rw [eHomEquiv_comp]
    simp only [Category.assoc]
  have hFourth : eHomEquiv V (h ≫ g₀) ≫ pre = eHomEquiv V (αI ≫ h ≫ g₀) :=
    eHomEquiv_comp_eHomWhiskerRight V (CopowerUnderlying.{u, v, 0} I) αI (h ≫ g₀)
  have hFifth : eHomEquiv V (αI ≫ h ≫ g₀) =
      eHomEquiv V (R.map ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g)) :=
    congrArg (fun z : (b₀ ⊗ a₀) ⊗ n₀ ⟶ l₀ => eHomEquiv V z) hLabel
  have hLast : eHomEquiv V (R.map ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g)) =
      basedDiscreteIncl.{u, v, 0} ((b ⊗ a) ⊗ n ⟶ l)
        ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) :=
    copowerRestriction_map.{u, v, 0} I _
  change basedDiscretePairIncl.{u, v, 0} (a ⊗ n ⟶ k) (b ⊗ k ⟶ l) f g ≫
      Enriched.SphereOperator.indexGenerator d n₀ k₀ l₀ a₀ b₀ =
    basedDiscreteIncl.{u, v, 0} ((b ⊗ a) ⊗ n ⟶ l)
      ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g)
  exact hFirst.trans (hSecond.trans (hThird.trans (hFourth.trans (hFifth.trans hLast))))

private theorem compositionGenerator_point (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a) f ⊗ₘ
      discreteSmashIncl.{u, v, 0} (b ⊗ k ⟶ l) (sphereSequence.{u, v}.functor.obj b) g) ≫
      Enriched.SphereOperator.compositionGenerator
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l)
        ((copowerRestriction.{u, v, 0} I).obj a)
        ((copowerRestriction.{u, v, 0} I).obj b) ≫ operatorHomMap M n l =
    (β_ (sphereSequence.{u, v}.functor.obj a) (sphereSequence.{u, v}.functor.obj b)).hom ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      curriedArrowAction M (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let E : Type := a ⊗ n ⟶ k
  let G : Type := b ⊗ k ⟶ l
  let H : Type := (b ⊗ a) ⊗ n ⟶ l
  let A := sphereSequence.{u, v}.functor.obj a
  let B := sphereSequence.{u, v}.functor.obj b
  let C := sphereSequence.{u, v}.functor.obj (b ⊗ a)
  let P := basedDiscreteObj.{u, v, 0} E ⊗ basedDiscreteObj.{u, v, 0} G
  let Q := basedDiscreteObj.{u, v, 0} H
  let p : (𝟙_ PointedCGWH.{u, v}) ⟶ P := basedDiscretePairIncl.{u, v, 0} E G f g
  let h : H := (α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g
  let q : (𝟙_ PointedCGWH.{u, v}) ⟶ Q := basedDiscreteIncl.{u, v, 0} H h
  let t : P ⟶ Q := Enriched.SphereOperator.indexGenerator d
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  let μ₀ : B ⊗ A ⟶ C := L.mu (R.obj b) (R.obj a)
  let i : Q ⊗ C ⟶ Enriched.SphereOperator.Hom d F (R.obj n) (R.obj l) :=
    Enriched.weightedCoend.ι (Enriched.SphereOperator.weight d (R.obj n) (R.obj l))
      F (R.obj (b ⊗ a))
  have hPoint : p ≫ t = q := nativeIndexGenerator_point a b n k l f g
  have hTensor : (p ⊗ₘ 𝟙 (A ⊗ B)) ≫ (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) =
      q ⊗ₘ ((β_ A B).hom ≫ μ₀) := by
    have hFirst : (p ⊗ₘ 𝟙 (A ⊗ B)) ≫ (𝟙 P ⊗ₘ (β_ A B).hom) =
        p ⊗ₘ (β_ A B).hom := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    calc
      _ = (p ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) := by
        simpa only [Category.assoc] using congrArg
          (fun z : (𝟙_ PointedCGWH.{u, v}) ⊗ (A ⊗ B) ⟶ P ⊗ (B ⊗ A) => z ≫ (t ⊗ₘ μ₀)) hFirst
      _ = (p ≫ t) ⊗ₘ ((β_ A B).hom ≫ μ₀) :=
        MonoidalCategory.tensorHom_comp_tensorHom p (β_ A B).hom t μ₀
      _ = _ := congrArg (fun z : (𝟙_ PointedCGWH.{u, v}) ⟶ Q => z ⊗ₘ ((β_ A B).hom ≫ μ₀)) hPoint
  have hGenerator : i ≫ operatorHomMap M n l = coendGeneratorMap M (b ⊗ a) n l :=
    operatorHomMap_generator M n l (R.obj (b ⊗ a))
  have hCoefficient : (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) =
      (β_ A B).hom ≫ μ₀ ≫ discreteSmashIncl.{u, v, 0} H C h := by
    have hLeg : (λ_ C).inv ≫ (q ▷ C) = discreteSmashIncl.{u, v, 0} H C h := by
      change (λ_ C).inv ≫ (q ▷ C) = (λ_ C).inv ≫ (q ⊗ₘ 𝟙 C)
      exact congrArg
        (fun z : (𝟙_ PointedCGWH.{u, v}) ⊗ C ⟶ Q ⊗ C => (λ_ C).inv ≫ z)
        (MonoidalCategory.tensorHom_id q C).symm
    have hNatural : (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) =
        ((β_ A B).hom ≫ μ₀) ≫ (λ_ C).inv ≫ (q ▷ C) :=
      MonoidalCategory.leftUnitor_inv_comp_tensorHom q ((β_ A B).hom ≫ μ₀)
    have hFinish : ((β_ A B).hom ≫ μ₀) ≫ (λ_ C).inv ≫ (q ▷ C) =
        (β_ A B).hom ≫ μ₀ ≫ discreteSmashIncl.{u, v, 0} H C h :=
      (congrArg (fun z : C ⟶ Q ⊗ C => ((β_ A B).hom ≫ μ₀) ≫ z) hLeg).trans
        (Category.assoc (β_ A B).hom μ₀ (discreteSmashIncl.{u, v, 0} H C h))
    exact hNatural.trans hFinish
  change (discreteSmashIncl.{u, v, 0} E A f ⊗ₘ discreteSmashIncl.{u, v, 0} G B g) ≫
    (MonoidalCategory.tensorδ (basedDiscreteObj.{u, v, 0} E)
      (basedDiscreteObj.{u, v, 0} G) A B ≫
      (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i) ≫ operatorHomMap M n l =
    (β_ A B).hom ≫ μ₀ ≫ curriedArrowAction M (b ⊗ a) n l h
  calc
    _ = (λ_ (A ⊗ B)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ B)) ≫
        (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i ≫ operatorHomMap M n l := by
      simpa only [Category.assoc] using congrArg
        (fun z : A ⊗ B ⟶ P ⊗ (A ⊗ B) => z ≫
          (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i ≫ operatorHomMap M n l)
        (nativeDiscretePair_delta A B f g)
    _ = (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) ≫
        i ≫ operatorHomMap M n l := by
      simpa only [Category.assoc] using congrArg
        (fun z : (𝟙_ PointedCGWH.{u, v}) ⊗ (A ⊗ B) ⟶ Q ⊗ C =>
          (λ_ (A ⊗ B)).inv ≫ z ≫ i ≫ operatorHomMap M n l) hTensor
    _ = (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) ≫
        coendGeneratorMap M (b ⊗ a) n l :=
      congrArg
        (fun z : Q ⊗ C ⟶ (ihom (M.X.functor.obj n)).obj (M.X.functor.obj l) =>
          (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) ≫ z) hGenerator
    _ = (β_ A B).hom ≫ μ₀ ≫ discreteSmashIncl.{u, v, 0} H C h ≫
        coendGeneratorMap M (b ⊗ a) n l := by
      simpa only [Category.assoc] using congrArg
        (fun z : A ⊗ B ⟶ Q ⊗ C => z ≫ coendGeneratorMap M (b ⊗ a) n l) hCoefficient
    _ = _ := by rw [coendGeneratorMap_generator]

private theorem coendGeneratorMap_comp (a b n k l : I) :
    (coendGeneratorMap M a n k ⊗ₘ coendGeneratorMap M b k l) ≫
      eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k)
        (M.X.functor.obj l) =
    Enriched.SphereOperator.compositionGenerator
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj l)
      ((copowerRestriction.{u, v, 0} I).obj a)
      ((copowerRestriction.{u, v, 0} I).obj b) ≫ operatorHomMap M n l := by
  let A := sphereSequence.{u, v}.functor.obj a
  let B := sphereSequence.{u, v}.functor.obj b
  let E : Type := a ⊗ n ⟶ k
  let G : Type := b ⊗ k ⟶ l
  let P := basedDiscreteObj.{u, v, 0} E ⊗ A
  let Q := basedDiscreteObj.{u, v, 0} G ⊗ B
  let Z := (ihom (M.X.functor.obj n)).obj (M.X.functor.obj l)
  let qL : P ⊗ Q ⟶ Z := (coendGeneratorMap M a n k ⊗ₘ coendGeneratorMap M b k l) ≫
    eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k) (M.X.functor.obj l)
  let qR : P ⊗ Q ⟶ Z := Enriched.SphereOperator.compositionGenerator
    (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
    sphereCopowerLaxData.{u, v}
    ((copowerRestriction.{u, v, 0} I).obj n)
    ((copowerRestriction.{u, v, 0} I).obj k)
    ((copowerRestriction.{u, v, 0} I).obj l)
    ((copowerRestriction.{u, v, 0} I).obj a)
    ((copowerRestriction.{u, v, 0} I).obj b) ≫ operatorHomMap M n l
  change qL = qR
  apply (CategoryTheory.Limits.isColimitOfPreserves (tensorRight Q)
    (discreteSmashCofanIsColimit.{u, v, 0} E A)).hom_ext
  intro f₀
  let f : E := f₀.as
  let p : A ⟶ P := discreteSmashIncl.{u, v, 0} E A f
  change (p ▷ Q) ≫ qL = (p ▷ Q) ≫ qR
  apply (CategoryTheory.Limits.isColimitOfPreserves (tensorLeft A)
    (discreteSmashCofanIsColimit.{u, v, 0} G B)).hom_ext
  intro g₀
  let g : G := g₀.as
  let q : B ⟶ Q := discreteSmashIncl.{u, v, 0} G B g
  have hTensor : (p ⊗ₘ q) ≫ (coendGeneratorMap M a n k ⊗ₘ coendGeneratorMap M b k l) =
      curriedArrowAction M a n k f ⊗ₘ curriedArrowAction M b k l g :=
    (MonoidalCategory.tensorHom_comp_tensorHom p q
      (coendGeneratorMap M a n k) (coendGeneratorMap M b k l)).trans
      (congrArg₂ (fun x y => x ⊗ₘ y) (coendGeneratorMap_generator M a n k f)
        (coendGeneratorMap_generator M b k l g))
  have hLeft : (p ⊗ₘ q) ≫ qL =
      (β_ A B).hom ≫ sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      curriedArrowAction M (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
    dsimp only [qL]
    calc
      _ = (curriedArrowAction M a n k f ⊗ₘ curriedArrowAction M b k l g) ≫
          eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k) (M.X.functor.obj l) := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k)
            (M.X.functor.obj l)) hTensor
      _ = _ := curriedArrowAction_comp M a b n k l f g
  have hRight : (p ⊗ₘ q) ≫ qR =
      (β_ A B).hom ≫ sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      curriedArrowAction M (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) :=
    compositionGenerator_point M a b n k l f g
  have hPre : (p ⊗ₘ q) = (A ◁ q) ≫ (p ▷ Q) :=
    MonoidalCategory.tensorHom_def' p q
  change (A ◁ q) ≫ (p ▷ Q) ≫ qL = (A ◁ q) ≫ (p ▷ Q) ≫ qR
  calc
    _ = (p ⊗ₘ q) ≫ qL := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ qL) hPre.symm
    _ = (p ⊗ₘ q) ≫ qR := hLeft.trans hRight.symm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ qR) hPre

/-- Both complete native Hom coends preserve the literal operator composition. -/
theorem operatorHomMap_comp (n k l : I) :
    Enriched.SphereOperator.composition
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l) ≫ operatorHomMap M n l =
    (operatorHomMap M n k ⊗ₘ operatorHomMap M k l) ≫
      eComp PointedCGWH.{u, v} (M.X.functor.obj n) (M.X.functor.obj k)
        (M.X.functor.obj l) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let W₁ := Enriched.SphereOperator.weight d (R.obj n) (R.obj k)
  let W₂ := Enriched.SphereOperator.weight d (R.obj k) (R.obj l)
  let H := Enriched.SphereOperator.Hom d F (R.obj n) (R.obj k)
  let K := Enriched.SphereOperator.Hom d F (R.obj k) (R.obj l)
  let Z := (ihom (M.X.functor.obj n)).obj (M.X.functor.obj l)
  let qL : H ⊗ K ⟶ Z := Enriched.SphereOperator.composition d F L
    (R.obj n) (R.obj k) (R.obj l) ≫ operatorHomMap M n l
  let qR : H ⊗ K ⟶ Z := (operatorHomMap M n k ⊗ₘ operatorHomMap M k l) ≫
    eComp V (M.X.functor.obj n) (M.X.functor.obj k) (M.X.functor.obj l)
  change qL = qR
  apply Enriched.weightedCoend.Mapped.hom_ext W₁ F (tensorRight K)
  intro a
  let P := Enriched.weightedCoend.objects W₁ F a
  let p : P ⟶ H := Enriched.weightedCoend.ι W₁ F a
  change (p ▷ K) ≫ qL = (p ▷ K) ≫ qR
  apply Enriched.weightedCoend.Mapped.hom_ext W₂ F (tensorLeft P)
  intro b
  let Q := Enriched.weightedCoend.objects W₂ F b
  let q : Q ⟶ K := Enriched.weightedCoend.ι W₂ F b
  let c : P ⊗ Q ⟶ Enriched.SphereOperator.Hom d F (R.obj n) (R.obj l) :=
    Enriched.SphereOperator.compositionGenerator d F L (R.obj n) (R.obj k) (R.obj l) a b
  have hSource : (p ⊗ₘ q) ≫ Enriched.SphereOperator.composition d F L
      (R.obj n) (R.obj k) (R.obj l) = c :=
    Enriched.SphereOperator.composition_generator d F L (R.obj n) (R.obj k) (R.obj l) a b
  have hTensor : (p ⊗ₘ q) ≫ (operatorHomMap M n k ⊗ₘ operatorHomMap M k l) =
      coendGeneratorMap M (show I from a) n k ⊗ₘ
        coendGeneratorMap M (show I from b) k l :=
    (MonoidalCategory.tensorHom_comp_tensorHom p q
      (operatorHomMap M n k) (operatorHomMap M k l)).trans
      (congrArg₂ (fun x y => x ⊗ₘ y) (operatorHomMap_generator M n k a)
        (operatorHomMap_generator M k l b))
  have hLeft : (p ⊗ₘ q) ≫ qL = c ≫ operatorHomMap M n l := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ operatorHomMap M n l) hSource
  have hComp :
      (show P ⊗ Q ⟶ Z from
        (coendGeneratorMap M (show I from a) n k ⊗ₘ
          coendGeneratorMap M (show I from b) k l) ≫
          eComp V (M.X.functor.obj n) (M.X.functor.obj k) (M.X.functor.obj l)) =
      c ≫ operatorHomMap M n l :=
    coendGeneratorMap_comp M (show I from a) (show I from b) n k l
  have hRight : (p ⊗ₘ q) ≫ qR = c ≫ operatorHomMap M n l := by
    dsimp only [qR]
    exact (Category.assoc (p ⊗ₘ q) (operatorHomMap M n k ⊗ₘ operatorHomMap M k l)
      (eComp V (M.X.functor.obj n) (M.X.functor.obj k) (M.X.functor.obj l))).symm.trans
        ((congrArg
          (fun z => z ≫ eComp V (M.X.functor.obj n) (M.X.functor.obj k)
            (M.X.functor.obj l))
          hTensor).trans hComp)
  have hPre : (p ⊗ₘ q) = (P ◁ q) ≫ (p ▷ K) := MonoidalCategory.tensorHom_def' p q
  change (P ◁ q) ≫ (p ▷ K) ≫ qL = (P ◁ q) ≫ (p ▷ K) ≫ qR
  calc
    _ = (p ⊗ₘ q) ≫ qL := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ qL) hPre.symm
    _ = (p ⊗ₘ q) ≫ qR := hLeft.trans hRight.symm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ qR) hPre

/-- The module determines an object of the canonical operator enriched-functor carrier. -/
def toOperatorFunctor : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} where
  toEnrichedFunctor :=
    { obj := fun n => M.X.functor.obj (show I from n.asIndex)
      map := fun n k => operatorHomMap M (show I from n.asIndex) (show I from k.asIndex)
      map_id := fun n => operatorHomMap_id M (show I from n.asIndex)
      map_comp := by
        intro n k l
        let i : I := show I from n.asIndex
        let j : I := show I from k.asIndex
        let t : I := show I from l.asIndex
        have hComposition := Enriched.SphereOperator.operatorIndex_comp
          (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
          sphereCopowerLaxData.{u, v} n k l
        exact (congrArg (fun c => c ≫ operatorHomMap M i t) hComposition).trans
          (operatorHomMap_comp M i j t) }

end NativeDayMultiplication

section ModuleMorphisms

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

variable {M} {N : CategoryTheory.Mod (C := SymmetricSequence.{u, v})
    (SymmetricSequence.{u, v}) sphereSequence.{u, v}}

/-- Every module morphism intertwines the complete original pair actions. -/
theorem pairAction_morphism (f : M ⟶ N) (a n : I) :
    pairAction M a n ≫ f.hom.natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v}.functor.obj a ◁ f.hom.natTrans.app n) ≫ pairAction N a n := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  let m := f.hom
  let γM : sphereSequence.{u, v} ⊗ M.X ⟶ M.X := ModObj.smul (M := sphereSequence.{u, v}) (X := M.X)
  let γN : sphereSequence.{u, v} ⊗ N.X ⟶ N.X := ModObj.smul (M := sphereSequence.{u, v}) (X := N.X)
  let iM := (DayFunctor.η sphereSequence.{u, v} M.X).app (a, n)
  let iN := (DayFunctor.η sphereSequence.{u, v} N.X).app (a, n)
  have hModule : γM ≫ m = (sphereSequence.{u, v} ◁ m) ≫ γN :=
    IsModHom.smul_hom (A := sphereSequence.{u, v}) (f := m)
  have hApp : γM.natTrans.app (a ⊗ n) ≫ m.natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v} ◁ m).natTrans.app (a ⊗ n) ≫ γN.natTrans.app (a ⊗ n) := by
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using congrArg
      (fun z : sphereSequence.{u, v} ⊗ M.X ⟶ N.X => z.natTrans.app (a ⊗ n)) hModule
  have hConvolution : iM ≫ (sphereSequence.{u, v} ◁ m).natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ iN := by
    change
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
          sphereSequence.{u, v} M.X).app
        (a, n) ≫ ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map
          (sphereSequence.{u, v} ◁ m)).app (a ⊗ n) =
      (((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj sphereSequence.{u, v}).obj a ◁
        ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map m).app n) ≫
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
          sphereSequence.{u, v} N.X).app
        (a, n)
    exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V sphereSequence.{u, v} m a n
  change (iM ≫ γM.natTrans.app (a ⊗ n)) ≫ m.natTrans.app (a ⊗ n) =
    (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ iN ≫ γN.natTrans.app (a ⊗ n)
  calc
    _ = iM ≫ (sphereSequence.{u, v} ◁ m).natTrans.app (a ⊗ n) ≫ γN.natTrans.app (a ⊗ n) := by
      simpa only [Category.assoc] using congrArg
        (fun z : (sphereSequence.{u, v} ⊗ M.X).functor.obj (a ⊗ n) ⟶ N.X.functor.obj (a ⊗ n) =>
          iM ≫ z) hApp
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ γN.natTrans.app (a ⊗ n)) hConvolution

/-- The whole ordinary label action is natural for every module morphism. -/
theorem arrowAction_morphism (f : M ⟶ N) (a n k : I) (g : a ⊗ n ⟶ k) :
    arrowAction M a n k g ≫ f.hom.natTrans.app k =
      (sphereSequence.{u, v}.functor.obj a ◁ f.hom.natTrans.app n) ≫ arrowAction N a n k g := by
  have hTarget := f.hom.natTrans.naturality g
  have hPair := pairAction_morphism f a n
  change (pairAction M a n ≫ M.X.functor.map g) ≫ f.hom.natTrans.app k =
    (sphereSequence.{u, v}.functor.obj a ◁ f.hom.natTrans.app n) ≫ pairAction N a n ≫
        N.X.functor.map g
  calc
    _ = pairAction M a n ≫ f.hom.natTrans.app (a ⊗ n) ≫ N.X.functor.map g := by
      simpa only [Category.assoc] using congrArg (fun z => pairAction M a n ≫ z) hTarget
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ N.X.functor.map g) hPair

private theorem curriedArrowAction_morphism (f : M ⟶ N) (a n k : I)
    (g : a ⊗ n ⟶ k) :
    curriedArrowAction M a n k g ≫
      (ihom (M.X.functor.obj n)).map (f.hom.natTrans.app k) =
    curriedArrowAction N a n k g ≫
      (MonoidalClosed.pre (f.hom.natTrans.app n)).app (N.X.functor.obj k) := by
  let A := sphereSequence.{u, v}.functor.obj a
  let X := M.X.functor.obj n
  let Y := N.X.functor.obj n
  let p : X ⟶ Y := f.hom.natTrans.app n
  let q := f.hom.natTrans.app k
  let u₀ := arrowAction M a n k g
  let v₀ := arrowAction N a n k g
  have hAction : u₀ ≫ q = (A ◁ p) ≫ v₀ := arrowAction_morphism f a n k g
  have hBraid : (p ▷ A) ≫ (β_ A Y).inv = (β_ A X).inv ≫ (A ◁ p) :=
    BraidedCategory.braiding_inv_naturality_left p A
  have hFull : ((β_ A X).inv ≫ u₀) ≫ q = (p ▷ A) ≫ (β_ A Y).inv ≫ v₀ := by
    calc
      _ = (β_ A X).inv ≫ (A ◁ p) ≫ v₀ := by
        simpa only [Category.assoc] using congrArg (fun z => (β_ A X).inv ≫ z) hAction
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ v₀) hBraid.symm
  change MonoidalClosed.curry ((β_ A X).inv ≫ u₀) ≫ (ihom X).map q =
    MonoidalClosed.curry ((β_ A Y).inv ≫ v₀) ≫ (MonoidalClosed.pre p).app _
  calc
    _ = MonoidalClosed.curry (((β_ A X).inv ≫ u₀) ≫ q) :=
      (MonoidalClosed.curry_natural_right ((β_ A X).inv ≫ u₀) q).symm
    _ = MonoidalClosed.curry ((p ▷ A) ≫ (β_ A Y).inv ≫ v₀) :=
      congrArg MonoidalClosed.curry hFull
    _ = _ := (MonoidalClosed.curry_pre_app p ((β_ A Y).inv ≫ v₀)).symm

private theorem coendGeneratorMap_morphism (f : M ⟶ N) (a n k : I) :
    coendGeneratorMap M a n k ≫
      (ihom (M.X.functor.obj n)).map (f.hom.natTrans.app k) =
    coendGeneratorMap N a n k ≫
      (MonoidalClosed.pre (f.hom.natTrans.app n)).app (N.X.functor.obj k) := by
  apply discreteSmash_hom_ext.{u, v, 0} (a ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a)
  intro g
  have hM := coendGeneratorMap_generator M a n k g
  have hN := coendGeneratorMap_generator N a n k g
  calc
    _ = curriedArrowAction M a n k g ≫
        (ihom (M.X.functor.obj n)).map (f.hom.natTrans.app k) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (ihom (M.X.functor.obj n)).map (f.hom.natTrans.app k)) hM
    _ = curriedArrowAction N a n k g ≫
        (MonoidalClosed.pre (f.hom.natTrans.app n)).app (N.X.functor.obj k) :=
      curriedArrowAction_morphism f a n k g
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (MonoidalClosed.pre (f.hom.natTrans.app n)).app
          (N.X.functor.obj k)) hN.symm

/-- Every module morphism is natural on the entire descended operator Hom. -/
theorem operatorHomMap_morphism (f : M ⟶ N) (n k : I) :
    operatorHomMap M n k ≫ (ihom (M.X.functor.obj n)).map (f.hom.natTrans.app k) =
      operatorHomMap N n k ≫
        (MonoidalClosed.pre (f.hom.natTrans.app n)).app (N.X.functor.obj k) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  apply Enriched.weightedCoend.hom_ext W sphereCopowerEnrichedFunctor.{u, v}
  intro a
  let P : V := Enriched.weightedCoend.objects W sphereCopowerEnrichedFunctor.{u, v} a
  let H : V := Enriched.weightedCoend W sphereCopowerEnrichedFunctor.{u, v}
  let A : V := M.X.functor.obj n
  let B : V := M.X.functor.obj k
  let C : V := N.X.functor.obj n
  let D : V := N.X.functor.obj k
  let T : V := (ihom A).obj D
  let i : P ⟶ H := Enriched.weightedCoend.ι W sphereCopowerEnrichedFunctor.{u, v} a
  let m : H ⟶ (ihom A).obj B := operatorHomMap M n k
  let q : H ⟶ (ihom C).obj D := operatorHomMap N n k
  let post : (ihom A).obj B ⟶ T := (ihom A).map (f.hom.natTrans.app k)
  let pre : (ihom C).obj D ⟶ T :=
    (MonoidalClosed.pre (f.hom.natTrans.app n)).app D
  let pM : P ⟶ (ihom A).obj B := coendGeneratorMap M (show I from a) n k
  let pN : P ⟶ (ihom C).obj D := coendGeneratorMap N (show I from a) n k
  have hM : i ≫ m = pM := operatorHomMap_generator M n k a
  have hN : i ≫ q = pN := operatorHomMap_generator N n k a
  have hMiddle : pM ≫ post = pN ≫ pre := coendGeneratorMap_morphism f (show I from a) n k
  have hLeft : i ≫ m ≫ post = pM ≫ post :=
    (Category.assoc i m post).symm.trans
      (congrArg (fun z : P ⟶ (ihom A).obj B => z ≫ post) hM)
  have hRight : pN ≫ pre = i ≫ q ≫ pre :=
    (congrArg (fun z : P ⟶ (ihom C).obj D => z ≫ pre) hN.symm).trans
      (Category.assoc i q pre)
  change i ≫ m ≫ post = i ≫ q ≫ pre
  exact hLeft.trans (hMiddle.trans hRight)

/-- The actual uncurried operator action retains full component naturality. -/
theorem operatorHomMap_uncurried_morphism (f : M ⟶ N) (n k : I) :
    MonoidalClosed.uncurry (operatorHomMap M n k) ≫ f.hom.natTrans.app k =
      (f.hom.natTrans.app n ⊗ₘ
        𝟙 (Enriched.SphereOperator.Hom
          (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
          ((copowerRestriction.{u, v, 0} I).obj n)
          ((copowerRestriction.{u, v, 0} I).obj k))) ≫
        MonoidalClosed.uncurry (operatorHomMap N n k) := by
  have h := congrArg MonoidalClosed.uncurry (operatorHomMap_morphism f n k)
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app] at h
  simpa only [MonoidalCategory.tensorHom_id] using h

/-- An arbitrary module morphism gives its genuine unit-graded operator transformation. -/
def toOperatorMorphism (f : M ⟶ N) : toOperatorFunctor M ⟶ toOperatorFunctor N :=
  GradedNatTrans.unitOfComponents
    (F' := (toOperatorFunctor M).toEnrichedFunctor)
    (G' := (toOperatorFunctor N).toEnrichedFunctor)
    (fun n => f.hom.natTrans.app (show I from n.asIndex))
    (by
      intro n k
      exact operatorHomMap_uncurried_morphism f (show I from n.asIndex)
        (show I from k.asIndex))

/-- The comparison retains every original underlying level component. -/
theorem toOperatorMorphism_component (f : M ⟶ N) (n : SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (toOperatorMorphism f) n =
      f.hom.natTrans.app (show I from n.asIndex) :=
  GradedNatTrans.unitOfComponents_component _ _ n

/-- The original module presentation maps to the canonical enriched-functor category. -/
def moduleToOperator :
    CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v} ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} where
  obj := toOperatorFunctor
  map := fun f => toOperatorMorphism f
  map_id M := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [toOperatorMorphism_component, EnrichedFunctorCat.component_id,
      Mod.id_hom', DayFunctor.id_natTrans]
    rfl
  map_comp f g := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [toOperatorMorphism_component, EnrichedFunctorCat.component_comp,
      Mod.comp_hom', DayFunctor.comp_natTrans]
    rfl

end ModuleMorphisms

section NativeInverseGenerators

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The complete sphere coefficient at an original label enters the actual native operator Hom. -/
def operatorGenerator (a n k : I) (f : a ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⟶ Enriched.SphereOperator.Hom
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k) :=
  discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a) f ≫
    Enriched.weightedCoend.ι
      (Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k))
      sphereCopowerEnrichedFunctor.{u, v} ((copowerRestriction.{u, v, 0} I).obj a)

/-- The forward functor retains every entire original labelled coefficient action. -/
theorem operatorHomMap_point
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v})
    (a n k : I) (f : a ⊗ n ⟶ k) :
    operatorGenerator a n k f ≫ operatorHomMap M n k = curriedArrowAction M a n k f := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  let A : V := sphereSequence.{u, v}.functor.obj a
  let P : V := Enriched.weightedCoend.objects W sphereCopowerEnrichedFunctor.{u, v} (R.obj a)
  let H : V := Enriched.weightedCoend W sphereCopowerEnrichedFunctor.{u, v}
  let Z : V := (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k)
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) A f
  let i : P ⟶ H := Enriched.weightedCoend.ι W sphereCopowerEnrichedFunctor.{u, v} (R.obj a)
  let m : H ⟶ Z := operatorHomMap M n k
  let q : P ⟶ Z := coendGeneratorMap M a n k
  have hGenerator : i ≫ m = q := operatorHomMap_generator M n k (R.obj a)
  have hPre : (j ≫ i) ≫ m = j ≫ q :=
    (Category.assoc j i m).trans
      (congrArg (fun z : P ⟶ Z => j ≫ z) hGenerator)
  have hPoint : j ≫ q = curriedArrowAction M a n k f :=
    coendGeneratorMap_generator M a n k f
  change (j ≫ i) ≫ m = curriedArrowAction M a n k f
  exact hPre.trans hPoint

/-- The original epsilon and unitor label are exactly the enriched operator identity. -/
theorem operatorGenerator_unit (n : I) :
    Enriched.SphereOperator.identityGenerator
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v} ((copowerRestriction.{u, v, 0} I).obj n) =
    sphereCopowerLaxData.{u, v}.epsilon ≫ operatorGenerator (𝟙_ I) n n (λ_ n).hom := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let U : V := 𝟙_ V
  let E : Type := ((𝟙_ I) ⊗ n) ⟶ n
  let P : V := basedDiscreteObj.{u, v, 0} E ⊗ A
  let H : V := Enriched.SphereOperator.Hom d F (R.obj n) (R.obj n)
  let ε : U ⟶ A := L.epsilon
  let p : U ⟶ basedDiscreteObj.{u, v, 0} E := basedDiscreteIncl.{u, v, 0} E (λ_ n).hom
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} E A (λ_ n).hom
  let i : P ⟶ H := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight d (R.obj n) (R.obj n)) F (R.obj (𝟙_ I))
  have hPoint : eHomEquiv V (λ_ (R.obj n)).hom = p := by
    change eHomEquiv V (R.map (λ_ n).hom) = p
    exact copowerRestriction_map.{u, v, 0} I (λ_ n).hom
  have hj : j = (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := rfl
  have hPairPad : (λ_ U).inv ≫ (p ⊗ₘ ε) =
      ε ≫ (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := by
    simpa only [MonoidalCategory.tensorHom_id] using
      MonoidalCategory.leftUnitor_inv_comp_tensorHom p ε
  have hPair : (λ_ U).inv ≫ (p ⊗ₘ ε) = ε ≫ j :=
    hPairPad.trans (congrArg (fun z : A ⟶ P => ε ≫ z) hj.symm)
  have hLiteral : Enriched.SphereOperator.identityGenerator d F L (R.obj n) =
      (λ_ U).inv ≫ (eHomEquiv V (λ_ (R.obj n)).hom ⊗ₘ ε) ≫ i := rfl
  have hPointPad := congrArg
    (fun z : U ⟶ basedDiscreteObj.{u, v, 0} E => (λ_ U).inv ≫ (z ⊗ₘ ε) ≫ i) hPoint
  have hLast : (λ_ U).inv ≫ (p ⊗ₘ ε) ≫ i = ε ≫ j ≫ i :=
    (Category.assoc (λ_ U).inv (p ⊗ₘ ε) i).symm.trans
      ((congrArg (fun z : U ⟶ P => z ≫ i) hPair).trans (Category.assoc ε j i))
  change Enriched.SphereOperator.identityGenerator d F L (R.obj n) = ε ≫ j ≫ i
  exact hLiteral.trans (hPointPad.trans hLast)

/-- The actual coend relation retains all ordinary coefficient arrows at every label. -/
theorem operatorGenerator_coefficient {a b : I} (r : a ⟶ b) (n k : I)
    (f : b ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.map r ≫ operatorGenerator b n k f =
      operatorGenerator a n k ((r ⊗ₘ 𝟙 n) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let U : V := W.obj (Opposite.op (R.obj b))
  let U' : V := W.obj (Opposite.op (R.obj a))
  let H : V := R.obj a ⟶[V] R.obj b
  let Z : V := Enriched.weightedCoend W F
  let E : Type := b ⊗ n ⟶ k
  let G : Type := a ⊗ n ⟶ k
  let h : E → G := fun f => (r ⊗ₘ 𝟙 n) ≫ f
  let p : U ⟶ U' := basedDiscreteFunctor.{u, v, 0}.map (↾h)
  let q : A ⟶ B := sphereSequence.{u, v}.functor.map r
  let e : (𝟙_ V) ⟶ H := eHomEquiv V (R.map r)
  let w : U ⟶ U' :=
    (ρ_ U).inv ≫ U ◁ e ≫
      MonoidalClosed.uncurry (W.map (Opposite.op (R.obj b)) (Opposite.op (R.obj a)))
  let s : A ⟶ B :=
    (ρ_ A).inv ≫ A ◁ e ≫ MonoidalClosed.uncurry (F.map (R.obj a) (R.obj b))
  let P : V := U ⊗ A
  let P' : V := U' ⊗ A
  let Q : V := U ⊗ B
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} E A f
  let j' : A ⟶ P' := discreteSmashIncl.{u, v, 0} G A (h f)
  let jB : B ⟶ Q := discreteSmashIncl.{u, v, 0} E B f
  let iA : P' ⟶ Z := Enriched.weightedCoend.ι W F (R.obj a)
  let iB : Q ⟶ Z := Enriched.weightedCoend.ι W F (R.obj b)
  have hPoint : e = basedDiscreteIncl.{u, v, 0} (a ⟶ b) r :=
    copowerRestriction_map.{u, v, 0} I r
  have hWeight :
      (ρ_ U).inv ≫ U ◁ basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry
          (W.map (Opposite.op (R.obj b)) (Opposite.op (R.obj a))) = p :=
    nativeWeight_pointMap n k a b r
  have hSphere :
      (ρ_ A).inv ≫ A ◁ basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry (F.map (R.obj a) (R.obj b)) = q :=
    nativeSphere_pointMap r
  have hW : w = p :=
    (congrArg
      (fun z : (𝟙_ V) ⟶ H => (ρ_ U).inv ≫ U ◁ z ≫
        MonoidalClosed.uncurry
          (W.map (Opposite.op (R.obj b)) (Opposite.op (R.obj a)))) hPoint).trans hWeight
  have hS : s = q :=
    (congrArg
      (fun z : (𝟙_ V) ⟶ H => (ρ_ A).inv ≫ A ◁ z ≫
        MonoidalClosed.uncurry (F.map (R.obj a) (R.obj b))) hPoint).trans hSphere
  have hCondition : (w ⊗ₘ 𝟙 A) ≫ iA = (𝟙 U ⊗ₘ s) ≫ iB :=
    Enriched.weightedCoend.condition_unitPoint W F (R.obj a) (R.obj b) e
  have hLeftMap : (w ⊗ₘ 𝟙 A) ≫ iA = (p ⊗ₘ 𝟙 A) ≫ iA :=
    congrArg (fun z : U ⟶ U' => (z ⊗ₘ 𝟙 A) ≫ iA) hW
  have hRightMap : (𝟙 U ⊗ₘ s) ≫ iB = (𝟙 U ⊗ₘ q) ≫ iB :=
    congrArg (fun z : A ⟶ B => (𝟙 U ⊗ₘ z) ≫ iB) hS
  have hWhole : (p ⊗ₘ 𝟙 A) ≫ iA = (𝟙 U ⊗ₘ q) ≫ iB :=
    hLeftMap.symm.trans (hCondition.trans hRightMap)
  have hIndex : j ≫ (p ⊗ₘ 𝟙 A) = j' :=
    (congrArg (fun z : P ⟶ P' => j ≫ z)
      (MonoidalCategory.tensorHom_id p A)).trans (discreteSmashIncl_index h A f)
  have hCoefficient : j ≫ (𝟙 U ⊗ₘ q) = q ≫ jB :=
    (congrArg (fun z : P ⟶ Q => j ≫ z)
      (MonoidalCategory.id_tensorHom U q)).trans (discreteSmashIncl_coefficient E q f)
  have hLeft : j ≫ ((p ⊗ₘ 𝟙 A) ≫ iA) = j' ≫ iA :=
    (Category.assoc j (p ⊗ₘ 𝟙 A) iA).symm.trans
      (congrArg (fun z : A ⟶ P' => z ≫ iA) hIndex)
  have hRight : j ≫ ((𝟙 U ⊗ₘ q) ≫ iB) = q ≫ jB ≫ iB :=
    (Category.assoc j (𝟙 U ⊗ₘ q) iB).symm.trans
      ((congrArg (fun z : A ⟶ Q => z ≫ iB) hCoefficient).trans (Category.assoc q jB iB))
  change q ≫ jB ≫ iB = j' ≫ iA
  exact hRight.symm.trans ((congrArg (fun z : P ⟶ Z => j ≫ z) hWhole.symm).trans hLeft)

private theorem operatorGenerator_compositionPoint (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a) f ⊗ₘ
      discreteSmashIncl.{u, v, 0} (b ⊗ k ⟶ l) (sphereSequence.{u, v}.functor.obj b) g) ≫
      Enriched.SphereOperator.compositionGenerator
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l)
        ((copowerRestriction.{u, v, 0} I).obj a)
        ((copowerRestriction.{u, v, 0} I).obj b) =
    (β_ (sphereSequence.{u, v}.functor.obj a) (sphereSequence.{u, v}.functor.obj b)).hom ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      operatorGenerator (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let E : Type := a ⊗ n ⟶ k
  let G : Type := b ⊗ k ⟶ l
  let H : Type := (b ⊗ a) ⊗ n ⟶ l
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let C : V := sphereSequence.{u, v}.functor.obj (b ⊗ a)
  let P : V := basedDiscreteObj.{u, v, 0} E ⊗ basedDiscreteObj.{u, v, 0} G
  let Q : V := basedDiscreteObj.{u, v, 0} H
  let p : (𝟙_ V) ⟶ P := basedDiscretePairIncl.{u, v, 0} E G f g
  let h : H := (α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g
  let q : (𝟙_ V) ⟶ Q := basedDiscreteIncl.{u, v, 0} H h
  let t : P ⟶ Q := Enriched.SphereOperator.indexGenerator d
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  let μ₀ : B ⊗ A ⟶ C := L.mu (R.obj b) (R.obj a)
  let i : Q ⊗ C ⟶ Enriched.SphereOperator.Hom d F (R.obj n) (R.obj l) :=
    Enriched.weightedCoend.ι (Enriched.SphereOperator.weight d (R.obj n) (R.obj l))
      F (R.obj (b ⊗ a))
  have hPoint : p ≫ t = q := nativeIndexGenerator_point a b n k l f g
  have hTensor : (p ⊗ₘ 𝟙 (A ⊗ B)) ≫ (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) =
      q ⊗ₘ ((β_ A B).hom ≫ μ₀) := by
    have hFirst : (p ⊗ₘ 𝟙 (A ⊗ B)) ≫ (𝟙 P ⊗ₘ (β_ A B).hom) =
        p ⊗ₘ (β_ A B).hom := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    calc
      _ = (p ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ (t ⊗ₘ μ₀)) hFirst
      _ = (p ≫ t) ⊗ₘ ((β_ A B).hom ≫ μ₀) :=
        MonoidalCategory.tensorHom_comp_tensorHom p (β_ A B).hom t μ₀
      _ = _ := congrArg (fun z => z ⊗ₘ ((β_ A B).hom ≫ μ₀)) hPoint
  let j : C ⟶ Q ⊗ C := discreteSmashIncl.{u, v, 0} H C h
  have hj : j = (λ_ C).inv ≫ (q ⊗ₘ 𝟙 C) := rfl
  have hPad : (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) =
      ((β_ A B).hom ≫ μ₀) ≫ (λ_ C).inv ≫ (q ⊗ₘ 𝟙 C) := by
    simpa only [MonoidalCategory.tensorHom_id] using
      MonoidalCategory.leftUnitor_inv_comp_tensorHom q ((β_ A B).hom ≫ μ₀)
  have hPair : (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) =
      ((β_ A B).hom ≫ μ₀) ≫ j :=
    hPad.trans (congrArg (fun z : C ⟶ Q ⊗ C => ((β_ A B).hom ≫ μ₀) ≫ z) hj.symm)
  have hCoefficient : (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) =
      (β_ A B).hom ≫ μ₀ ≫ discreteSmashIncl.{u, v, 0} H C h :=
    hPair.trans (Category.assoc (β_ A B).hom μ₀ j)
  change (discreteSmashIncl.{u, v, 0} E A f ⊗ₘ discreteSmashIncl.{u, v, 0} G B g) ≫
    (MonoidalCategory.tensorδ (basedDiscreteObj.{u, v, 0} E)
      (basedDiscreteObj.{u, v, 0} G) A B ≫
      (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i) =
    (β_ A B).hom ≫ μ₀ ≫ discreteSmashIncl.{u, v, 0} H C h ≫ i
  calc
    _ = (λ_ (A ⊗ B)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ B)) ≫
        (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (𝟙 P ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ μ₀) ≫ i)
        (nativeDiscretePair_delta A B f g)
    _ = (λ_ (A ⊗ B)).inv ≫ (q ⊗ₘ ((β_ A B).hom ≫ μ₀)) ≫ i := by
      simpa only [Category.assoc] using congrArg
        (fun z => (λ_ (A ⊗ B)).inv ≫ z ≫ i) hTensor
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ i) hCoefficient

/-- The actual native coefficient generators multiply by the original whole operator composition. -/
theorem operatorGenerator_comp (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (operatorGenerator a n k f ⊗ₘ operatorGenerator b k l g) ≫
      Enriched.SphereOperator.composition
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l) =
    (β_ (sphereSequence.{u, v}.functor.obj a) (sphereSequence.{u, v}.functor.obj b)).hom ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      operatorGenerator (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let p := discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a) f
  let q := discreteSmashIncl.{u, v, 0} (b ⊗ k ⟶ l) (sphereSequence.{u, v}.functor.obj b) g
  let iA := Enriched.weightedCoend.ι (Enriched.SphereOperator.weight d (R.obj n) (R.obj k))
    F (R.obj a)
  let iB := Enriched.weightedCoend.ι (Enriched.SphereOperator.weight d (R.obj k) (R.obj l))
    F (R.obj b)
  have hTensor : (p ⊗ₘ q) ≫ (iA ⊗ₘ iB) =
      operatorGenerator a n k f ⊗ₘ operatorGenerator b k l g :=
    MonoidalCategory.tensorHom_comp_tensorHom p q iA iB
  have hWhole := Enriched.SphereOperator.composition_generator d F L
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  calc
    _ = (p ⊗ₘ q) ≫ (iA ⊗ₘ iB) ≫ Enriched.SphereOperator.composition d F L
        (R.obj n) (R.obj k) (R.obj l) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ Enriched.SphereOperator.composition d F L
          (R.obj n) (R.obj k) (R.obj l)) hTensor.symm
    _ = (p ⊗ₘ q) ≫ Enriched.SphereOperator.compositionGenerator d F L
        (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b) :=
      congrArg (fun z => (p ⊗ₘ q) ≫ z) hWhole
    _ = _ := operatorGenerator_compositionPoint a b n k l f g

/-- The full original index point is the same actual unit-coefficient operator generator. -/
theorem operatorGenerator_indexPoint {n k : I} (f : n ⟶ k) :
    basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫ symmetricIndexInclusion.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k) =
    sphereCopowerLaxData.{u, v}.epsilon ≫
      operatorGenerator (𝟙_ I) n k ((λ_ n).hom ≫ f) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let U : V := 𝟙_ V
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let E : Type := ((𝟙_ I) ⊗ n) ⟶ k
  let B : V := basedDiscreteObj.{u, v, 0} E
  let T : V := R.obj n ⟶[V] R.obj k
  let P : V := B ⊗ A
  let Z : V := Enriched.SphereOperator.Hom d F (R.obj n) (R.obj k)
  let ε : U ⟶ A := L.epsilon
  let p₀ : U ⟶ T := eHomEquiv V (R.map f)
  let p₁ : U ⟶ B := eHomEquiv V ((λ_ (R.obj n)).hom ≫ R.map f)
  let p : U ⟶ B := basedDiscreteIncl.{u, v, 0} E ((λ_ n).hom ≫ f)
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} E A ((λ_ n).hom ≫ f)
  let i : P ⟶ Z := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight d (R.obj n) (R.obj k)) F (R.obj (𝟙_ I))
  let m : T ⟶ Z := Enriched.SphereOperator.indexHom d F L (R.obj n) (R.obj k)
  have hPoint : p₀ = basedDiscreteIncl.{u, v, 0} (n ⟶ k) f :=
    copowerRestriction_map.{u, v, 0} I f
  have hLabel : (λ_ (R.obj n)).hom ≫ R.map f = R.map ((λ_ n).hom ≫ f) := by
    change R.map (λ_ n).hom ≫ R.map f = R.map ((λ_ n).hom ≫ f)
    exact (R.map_comp (λ_ n).hom f).symm
  have hLabelPoint : p₁ = p :=
    (congrArg (fun z => eHomEquiv V z) hLabel).trans
      (copowerRestriction_map.{u, v, 0} I ((λ_ n).hom ≫ f))
  have hIndex : p₀ ≫ m = (λ_ U).inv ≫ (p₁ ⊗ₘ ε) ≫ i :=
    Enriched.SphereOperator.indexHom_point d F L (R.map f)
  have hPointLeft : basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫ m = p₀ ≫ m :=
    congrArg (fun z : U ⟶ T => z ≫ m) hPoint.symm
  have hPointRight : (λ_ U).inv ≫ (p₁ ⊗ₘ ε) ≫ i =
      (λ_ U).inv ≫ (p ⊗ₘ ε) ≫ i :=
    congrArg (fun z : U ⟶ B => (λ_ U).inv ≫ (z ⊗ₘ ε) ≫ i) hLabelPoint
  have hj : j = (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := rfl
  have hPad : (λ_ U).inv ≫ (p ⊗ₘ ε) = ε ≫ (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := by
    simpa only [MonoidalCategory.tensorHom_id] using
      MonoidalCategory.leftUnitor_inv_comp_tensorHom p ε
  have hPair : (λ_ U).inv ≫ (p ⊗ₘ ε) = ε ≫ j :=
    hPad.trans (congrArg (fun z : A ⟶ P => ε ≫ z) hj.symm)
  have hFinal : (λ_ U).inv ≫ (p ⊗ₘ ε) ≫ i = ε ≫ j ≫ i :=
    (Category.assoc (λ_ U).inv (p ⊗ₘ ε) i).symm.trans
      ((congrArg (fun z : U ⟶ P => z ≫ i) hPair).trans (Category.assoc ε j i))
  change basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫ m = ε ≫ j ≫ i
  exact hPointLeft.trans (hIndex.trans (hPointRight.trans hFinal))

section GenericGeneratorTransport
universe uC vC uV vV
variable {C₀ : Type uC} [Category.{vC} C₀] [MonoidalCategory C₀]
  {V₀ : Type uV} [Category.{vV} V₀] [MonoidalCategory V₀] [BraidedCategory V₀]
  (S : C₀ ⥤ V₀) (H : C₀ → C₀ → V₀)
  (epsilon : 𝟙_ V₀ ⟶ S.obj (𝟙_ C₀))
  (mul : ∀ b a : C₀, S.obj b ⊗ S.obj a ⟶ S.obj (b ⊗ a))
  (generator : ∀ a n k : C₀, (a ⊗ n ⟶ k) → (S.obj a ⟶ H n k))
  (index : ∀ {n k : C₀}, (n ⟶ k) → (𝟙_ V₀ ⟶ H n k))
  (comp : ∀ n k l : C₀, H n k ⊗ H k l ⟶ H n l)
  (index_point : ∀ {n k : C₀} (g : n ⟶ k),
    index g = epsilon ≫ generator (𝟙_ C₀) n k ((λ_ n).hom ≫ g))
  (generator_comp : ∀ (a b n k l : C₀) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l),
    (generator a n k f ⊗ₘ generator b k l g) ≫ comp n k l =
      (β_ (S.obj a) (S.obj b)).hom ≫ mul b a ≫
        generator (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g))
  (generator_coefficient : ∀ {a b : C₀} (r : a ⟶ b) (n k : C₀) (f : b ⊗ n ⟶ k),
    S.map r ≫ generator b n k f = generator a n k ((r ⊗ₘ 𝟙 n) ≫ f))
  (left_unit : ∀ a : C₀,
    (λ_ (S.obj a)).inv ≫ (epsilon ▷ S.obj a) ≫ mul (𝟙_ C₀) a = S.map (λ_ a).inv)
  (right_unit : ∀ a : C₀,
    (ρ_ (S.obj a)).inv ≫ (S.obj a ◁ epsilon) ≫ mul a (𝟙_ C₀) = S.map (ρ_ a).inv)

include index_point generator_comp generator_coefficient left_unit in
private theorem nativeGeneratorTargetTransport (a n k l : C₀)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    (ρ_ (S.obj a)).inv ≫ (generator a n k f ⊗ₘ index g) ≫ comp n k l =
      generator a n l (f ≫ g) := by
  let A : V₀ := S.obj a
  let U : V₀ := 𝟙_ V₀
  let E : V₀ := S.obj (𝟙_ C₀)
  let C : V₀ := S.obj ((𝟙_ C₀) ⊗ a)
  let H₀ : V₀ := H n k
  let H₁ : V₀ := H k l
  let H₂ : V₀ := H n l
  let ε : U ⟶ E := epsilon
  let p : A ⟶ H₀ := generator a n k f
  let q : E ⟶ H₁ := generator (𝟙_ C₀) k l ((λ_ k).hom ≫ g)
  let j : U ⟶ H₁ := index g
  let μ₀ : E ⊗ A ⟶ C := mul (𝟙_ C₀) a
  let c : H₀ ⊗ H₁ ⟶ H₂ := comp n k l
  let r₀ : A ⟶ A ⊗ U := (ρ_ A).inv
  let x₀ : A ⊗ U ⟶ A ⊗ E := A ◁ ε
  let t : A ⊗ E ⟶ H₀ ⊗ H₁ := p ⊗ₘ q
  let b₀ : A ⊗ E ⟶ E ⊗ A := (β_ A E).hom
  let r₁ : A ⟶ U ⊗ A := (λ_ A).inv
  let x₁ : U ⊗ A ⟶ E ⊗ A := ε ▷ A
  let m : A ⟶ C := S.map (λ_ a).inv
  let m' : C ⟶ A := S.map (λ_ a).hom
  let h : ((𝟙_ C₀) ⊗ a) ⊗ n ⟶ l :=
    (α_ (𝟙_ C₀) a n).hom ≫ (𝟙 (𝟙_ C₀) ⊗ₘ f) ≫ (λ_ k).hom ≫ g
  let k₀ : C ⟶ H₂ := generator ((𝟙_ C₀) ⊗ a) n l h
  let z : A ⟶ H₂ := generator a n l (f ≫ g)
  have hIndex : j = ε ≫ q := index_point g
  have hTensor : x₀ ≫ t = p ⊗ₘ (ε ≫ q) :=
    (congrArg (fun v : A ⊗ U ⟶ A ⊗ E => v ≫ t)
      (MonoidalCategory.id_tensorHom A ε).symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom (𝟙 A) ε p q).trans
        (congrArg (fun v : A ⟶ H₀ => v ⊗ₘ (ε ≫ q)) (Category.id_comp p)))
  have hComp : t ≫ c = b₀ ≫ μ₀ ≫ k₀ :=
    generator_comp a (𝟙_ C₀) n k l f ((λ_ k).hom ≫ g)
  have hBraid : x₀ ≫ b₀ = (β_ A U).hom ≫ x₁ :=
    BraidedCategory.braiding_naturality_right (C := V₀) A ε
  have hCross : r₀ ≫ x₀ ≫ b₀ = r₁ ≫ x₁ :=
    (congrArg (fun v : A ⊗ U ⟶ E ⊗ A => r₀ ≫ v) hBraid).trans
      ((Category.assoc r₀ (β_ A U).hom x₁).symm.trans
        (congrArg (fun v : A ⟶ U ⊗ A => v ≫ x₁)
          (CategoryTheory.rightUnitor_inv_braiding A)))
  have hLabel : h = ((λ_ a).hom ⊗ₘ 𝟙 n) ≫ f ≫ g := by
    have hNaturality : (𝟙 (𝟙_ C₀) ⊗ₘ f) ≫ (λ_ k).hom =
        (λ_ (a ⊗ n)).hom ≫ f := by
      simpa only [MonoidalCategory.id_tensorHom] using
        MonoidalCategory.leftUnitor_naturality f
    have hUnit : (α_ (𝟙_ C₀) a n).hom ≫ (λ_ (a ⊗ n)).hom =
        (λ_ a).hom ⊗ₘ 𝟙 n := by
      rw [MonoidalCategory.tensorHom_id]
      monoidal
    dsimp only [h]
    calc
      _ = (α_ (𝟙_ C₀) a n).hom ≫ (λ_ (a ⊗ n)).hom ≫ f ≫ g := by
        simpa only [Category.assoc] using congrArg
          (fun v => (α_ (𝟙_ C₀) a n).hom ≫ v ≫ g) hNaturality
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun v => v ≫ f ≫ g) hUnit
  have hCoefficientBase : m' ≫ z =
      generator ((𝟙_ C₀) ⊗ a) n l (((λ_ a).hom ⊗ₘ 𝟙 n) ≫ f ≫ g) :=
    generator_coefficient (λ_ a).hom n l (f ≫ g)
  have hCoefficient : m' ≫ z = k₀ :=
    hCoefficientBase.trans
      (congrArg (fun v : ((𝟙_ C₀) ⊗ a) ⊗ n ⟶ l =>
        generator ((𝟙_ C₀) ⊗ a) n l v) hLabel.symm)
  have hCancel : m ≫ m' = 𝟙 A :=
    (S.map_comp (λ_ a).inv (λ_ a).hom).symm.trans
      ((congrArg (fun v : a ⟶ a => S.map v) (Iso.inv_hom_id (λ_ a))).trans (S.map_id a))
  have hFinal : m ≫ k₀ = z :=
    (congrArg (fun v : C ⟶ H₂ => m ≫ v) hCoefficient.symm).trans
      ((Category.assoc m m' z).symm.trans
        ((congrArg (fun v : A ⟶ A => v ≫ z) hCancel).trans (Category.id_comp z)))
  have hUnit : r₁ ≫ x₁ ≫ μ₀ = m := left_unit a
  have h₀ : r₀ ≫ (p ⊗ₘ j) ≫ c = r₀ ≫ (p ⊗ₘ (ε ≫ q)) ≫ c :=
    congrArg (fun v : U ⟶ H₁ => r₀ ≫ (p ⊗ₘ v) ≫ c) hIndex
  have h₁ : r₀ ≫ (p ⊗ₘ (ε ≫ q)) ≫ c = r₀ ≫ (x₀ ≫ t) ≫ c :=
    congrArg (fun v : A ⊗ U ⟶ H₀ ⊗ H₁ => r₀ ≫ v ≫ c) hTensor.symm
  have h₂ : r₀ ≫ (x₀ ≫ t) ≫ c = r₀ ≫ x₀ ≫ t ≫ c :=
    congrArg (fun v : A ⊗ U ⟶ H₂ => r₀ ≫ v) (Category.assoc x₀ t c)
  have h₃ : r₀ ≫ x₀ ≫ t ≫ c = r₀ ≫ x₀ ≫ b₀ ≫ μ₀ ≫ k₀ :=
    congrArg (fun v : A ⊗ E ⟶ H₂ => r₀ ≫ x₀ ≫ v) hComp
  have h₄ : r₀ ≫ x₀ ≫ b₀ ≫ μ₀ ≫ k₀ = ((r₀ ≫ x₀) ≫ b₀) ≫ μ₀ ≫ k₀ :=
    (Category.assoc r₀ x₀ (b₀ ≫ μ₀ ≫ k₀)).symm.trans
      (Category.assoc (r₀ ≫ x₀) b₀ (μ₀ ≫ k₀)).symm
  have h₅ : ((r₀ ≫ x₀) ≫ b₀) ≫ μ₀ ≫ k₀ = ((r₁ ≫ x₁) ≫ μ₀) ≫ k₀ :=
    (congrArg (fun v : A ⟶ E ⊗ A => v ≫ μ₀ ≫ k₀)
      ((Category.assoc r₀ x₀ b₀).trans hCross)).trans
        (Category.assoc (r₁ ≫ x₁) μ₀ k₀).symm
  have h₆ : ((r₁ ≫ x₁) ≫ μ₀) ≫ k₀ = m ≫ k₀ :=
    congrArg (fun v : A ⟶ C => v ≫ k₀) ((Category.assoc r₁ x₁ μ₀).trans hUnit)
  change r₀ ≫ (p ⊗ₘ j) ≫ c = z
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans hFinal))))))

include index_point generator_comp generator_coefficient right_unit in
private theorem nativeGeneratorInputTransport (a n n' k : C₀)
    (g : n ⟶ n') (f : a ⊗ n' ⟶ k) :
    (λ_ (S.obj a)).inv ≫ (index g ⊗ₘ generator a n' k f) ≫ comp n n' k =
      generator a n k ((𝟙 a ⊗ₘ g) ≫ f) := by
  let A : V₀ := S.obj a
  let U : V₀ := 𝟙_ V₀
  let E : V₀ := S.obj (𝟙_ C₀)
  let C : V₀ := S.obj (a ⊗ (𝟙_ C₀))
  let H₀ : V₀ := H n n'
  let H₁ : V₀ := H n' k
  let H₂ : V₀ := H n k
  let ε : U ⟶ E := epsilon
  let p : E ⟶ H₀ := generator (𝟙_ C₀) n n' ((λ_ n).hom ≫ g)
  let q : A ⟶ H₁ := generator a n' k f
  let j : U ⟶ H₀ := index g
  let μ₀ : A ⊗ E ⟶ C := mul a (𝟙_ C₀)
  let c : H₀ ⊗ H₁ ⟶ H₂ := comp n n' k
  let r₀ : A ⟶ U ⊗ A := (λ_ A).inv
  let x₀ : U ⊗ A ⟶ E ⊗ A := ε ▷ A
  let t : E ⊗ A ⟶ H₀ ⊗ H₁ := p ⊗ₘ q
  let b₀ : E ⊗ A ⟶ A ⊗ E := (β_ E A).hom
  let r₁ : A ⟶ A ⊗ U := (ρ_ A).inv
  let x₁ : A ⊗ U ⟶ A ⊗ E := A ◁ ε
  let m : A ⟶ C := S.map (ρ_ a).inv
  let m' : C ⟶ A := S.map (ρ_ a).hom
  let h : (a ⊗ (𝟙_ C₀)) ⊗ n ⟶ k :=
    (α_ a (𝟙_ C₀) n).hom ≫ (𝟙 a ⊗ₘ ((λ_ n).hom ≫ g)) ≫ f
  let k₀ : C ⟶ H₂ := generator (a ⊗ (𝟙_ C₀)) n k h
  let z : A ⟶ H₂ := generator a n k ((𝟙 a ⊗ₘ g) ≫ f)
  have hIndex : j = ε ≫ p := index_point g
  have hTensor : x₀ ≫ t = (ε ≫ p) ⊗ₘ q :=
    (congrArg (fun v : U ⊗ A ⟶ E ⊗ A => v ≫ t)
      (MonoidalCategory.tensorHom_id ε A).symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom ε (𝟙 A) p q).trans
        (congrArg (fun v : A ⟶ H₁ => (ε ≫ p) ⊗ₘ v) (Category.id_comp q)))
  have hComp : t ≫ c = b₀ ≫ μ₀ ≫ k₀ :=
    generator_comp (𝟙_ C₀) a n n' k ((λ_ n).hom ≫ g) f
  have hBraid : x₀ ≫ b₀ = (β_ U A).hom ≫ x₁ :=
    BraidedCategory.braiding_naturality_left (C := V₀) ε A
  have hCross : r₀ ≫ x₀ ≫ b₀ = r₁ ≫ x₁ :=
    (congrArg (fun v : U ⊗ A ⟶ A ⊗ E => r₀ ≫ v) hBraid).trans
      ((Category.assoc r₀ (β_ U A).hom x₁).symm.trans
        (congrArg (fun v : A ⟶ A ⊗ U => v ≫ x₁)
          (CategoryTheory.leftUnitor_inv_braiding A)))
  have hLabel : h = ((ρ_ a).hom ⊗ₘ 𝟙 n) ≫ (𝟙 a ⊗ₘ g) ≫ f := by
    have hSplit : 𝟙 a ⊗ₘ ((λ_ n).hom ≫ g) =
        (𝟙 a ⊗ₘ (λ_ n).hom) ≫ (𝟙 a ⊗ₘ g) := by
      simpa only [MonoidalCategory.id_tensorHom] using
        MonoidalCategory.whiskerLeft_comp a (λ_ n).hom g
    have hUnit : (α_ a (𝟙_ C₀) n).hom ≫ (𝟙 a ⊗ₘ (λ_ n).hom) =
        (ρ_ a).hom ⊗ₘ 𝟙 n := by
      rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
      monoidal
    dsimp only [h]
    calc
      _ = (α_ a (𝟙_ C₀) n).hom ≫ (𝟙 a ⊗ₘ (λ_ n).hom) ≫ (𝟙 a ⊗ₘ g) ≫ f := by
        simpa only [Category.assoc] using congrArg
          (fun v => (α_ a (𝟙_ C₀) n).hom ≫ v ≫ f) hSplit
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun v => v ≫ (𝟙 a ⊗ₘ g) ≫ f) hUnit
  have hCoefficientBase : m' ≫ z =
      generator (a ⊗ (𝟙_ C₀)) n k
        (((ρ_ a).hom ⊗ₘ 𝟙 n) ≫ (𝟙 a ⊗ₘ g) ≫ f) :=
    generator_coefficient (ρ_ a).hom n k ((𝟙 a ⊗ₘ g) ≫ f)
  have hCoefficient : m' ≫ z = k₀ :=
    hCoefficientBase.trans
      (congrArg (fun v : (a ⊗ (𝟙_ C₀)) ⊗ n ⟶ k =>
        generator (a ⊗ (𝟙_ C₀)) n k v) hLabel.symm)
  have hCancel : m ≫ m' = 𝟙 A :=
    (S.map_comp (ρ_ a).inv (ρ_ a).hom).symm.trans
      ((congrArg (fun v : a ⟶ a => S.map v) (Iso.inv_hom_id (ρ_ a))).trans (S.map_id a))
  have hFinal : m ≫ k₀ = z :=
    (congrArg (fun v : C ⟶ H₂ => m ≫ v) hCoefficient.symm).trans
      ((Category.assoc m m' z).symm.trans
        ((congrArg (fun v : A ⟶ A => v ≫ z) hCancel).trans (Category.id_comp z)))
  have hUnit : r₁ ≫ x₁ ≫ μ₀ = m := right_unit a
  have h₀ : r₀ ≫ (j ⊗ₘ q) ≫ c = r₀ ≫ ((ε ≫ p) ⊗ₘ q) ≫ c :=
    congrArg (fun v : U ⟶ H₀ => r₀ ≫ (v ⊗ₘ q) ≫ c) hIndex
  have h₁ : r₀ ≫ ((ε ≫ p) ⊗ₘ q) ≫ c = r₀ ≫ (x₀ ≫ t) ≫ c :=
    congrArg (fun v : U ⊗ A ⟶ H₀ ⊗ H₁ => r₀ ≫ v ≫ c) hTensor.symm
  have h₂ : r₀ ≫ (x₀ ≫ t) ≫ c = r₀ ≫ x₀ ≫ t ≫ c :=
    congrArg (fun v : U ⊗ A ⟶ H₂ => r₀ ≫ v) (Category.assoc x₀ t c)
  have h₃ : r₀ ≫ x₀ ≫ t ≫ c = r₀ ≫ x₀ ≫ b₀ ≫ μ₀ ≫ k₀ :=
    congrArg (fun v : E ⊗ A ⟶ H₂ => r₀ ≫ x₀ ≫ v) hComp
  have h₄ : r₀ ≫ x₀ ≫ b₀ ≫ μ₀ ≫ k₀ = ((r₀ ≫ x₀) ≫ b₀) ≫ μ₀ ≫ k₀ :=
    (Category.assoc r₀ x₀ (b₀ ≫ μ₀ ≫ k₀)).symm.trans
      (Category.assoc (r₀ ≫ x₀) b₀ (μ₀ ≫ k₀)).symm
  have h₅ : ((r₀ ≫ x₀) ≫ b₀) ≫ μ₀ ≫ k₀ = ((r₁ ≫ x₁) ≫ μ₀) ≫ k₀ :=
    (congrArg (fun v : A ⟶ A ⊗ E => v ≫ μ₀ ≫ k₀)
      ((Category.assoc r₀ x₀ b₀).trans hCross)).trans
        (Category.assoc (r₁ ≫ x₁) μ₀ k₀).symm
  have h₆ : ((r₁ ≫ x₁) ≫ μ₀) ≫ k₀ = m ≫ k₀ :=
    congrArg (fun v : A ⟶ C => v ≫ k₀) ((Category.assoc r₁ x₁ μ₀).trans hUnit)
  change r₀ ≫ (j ⊗ₘ q) ≫ c = z
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans hFinal))))))

end GenericGeneratorTransport

private theorem nativeSphere_leftUnit (a : I) :
    (λ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
      (sphereCopowerLaxData.{u, v}.epsilon ▷ sphereSequence.{u, v}.functor.obj a) ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj (𝟙_ I))
        ((copowerRestriction.{u, v, 0} I).obj a) =
    sphereSequence.{u, v}.functor.map (λ_ a).inv := by
  let _ : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  change (λ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
    (Functor.LaxMonoidal.ε sphereSequence.{u, v}.functor ▷ sphereSequence.{u, v}.functor.obj a) ≫
      Functor.LaxMonoidal.μ sphereSequence.{u, v}.functor (𝟙_ I) a = sphereSequence.{u,
          v}.functor.map (λ_ a).inv
  exact Functor.LaxMonoidal.left_unitality_inv sphereSequence.{u, v}.functor a

private theorem nativeSphere_rightUnit (a : I) :
    (ρ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
      (sphereSequence.{u, v}.functor.obj a ◁ sphereCopowerLaxData.{u, v}.epsilon) ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj a)
        ((copowerRestriction.{u, v, 0} I).obj (𝟙_ I)) =
    sphereSequence.{u, v}.functor.map (ρ_ a).inv := by
  let _ : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  change (ρ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
    (sphereSequence.{u, v}.functor.obj a ◁ Functor.LaxMonoidal.ε sphereSequence.{u, v}.functor) ≫
      Functor.LaxMonoidal.μ sphereSequence.{u, v}.functor a (𝟙_ I) = sphereSequence.{u,
          v}.functor.map (ρ_ a).inv
  exact Functor.LaxMonoidal.right_unitality_inv sphereSequence.{u, v}.functor a

/-- The whole labelled coefficient generator is covariant in every original target arrow. -/
theorem operatorGenerator_target (a n k l : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    (ρ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
      (operatorGenerator a n k f ⊗ₘ
        (basedDiscreteIncl.{u, v, 0} (k ⟶ l) g ≫ symmetricIndexInclusion.{u, v}.map
          ((copowerRestriction.{u, v, 0} I).obj k)
          ((copowerRestriction.{u, v, 0} I).obj l))) ≫
      Enriched.SphereOperator.composition
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l) =
    operatorGenerator a n l (f ≫ g) := by
  exact nativeGeneratorTargetTransport
    (S := sphereSequence.{u, v}.functor)
    (H := fun n k => Enriched.SphereOperator.Hom
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k))
    (epsilon := sphereCopowerLaxData.{u, v}.epsilon)
    (mul := fun b a => sphereCopowerLaxData.{u, v}.mu
      ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a))
    (generator := operatorGenerator.{u, v})
    (index := fun {n k} g => basedDiscreteIncl.{u, v, 0} (n ⟶ k) g ≫
      symmetricIndexInclusion.{u, v}.map
        ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k))
    (comp := fun n k l => Enriched.SphereOperator.composition
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj l))
    (index_point := fun {n k} g => operatorGenerator_indexPoint g)
    (generator_comp := fun a b n k l f g => operatorGenerator_comp a b n k l f g)
    (generator_coefficient := fun {a b} r n k f => operatorGenerator_coefficient r n k f)
    (left_unit := fun a => nativeSphere_leftUnit a) a n k l f g

/-- The whole coefficient generator is contravariant in every original source-index arrow. -/
theorem operatorGenerator_input (a n n' k : I) (g : n ⟶ n') (f : a ⊗ n' ⟶ k) :
    (λ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
      ((basedDiscreteIncl.{u, v, 0} (n ⟶ n') g ≫ symmetricIndexInclusion.{u, v}.map
          ((copowerRestriction.{u, v, 0} I).obj n)
          ((copowerRestriction.{u, v, 0} I).obj n')) ⊗ₘ operatorGenerator a n' k f) ≫
      Enriched.SphereOperator.composition
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj n')
        ((copowerRestriction.{u, v, 0} I).obj k) =
    operatorGenerator a n k ((𝟙 a ⊗ₘ g) ≫ f) := by
  exact nativeGeneratorInputTransport
    (S := sphereSequence.{u, v}.functor)
    (H := fun n k => Enriched.SphereOperator.Hom
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k))
    (epsilon := sphereCopowerLaxData.{u, v}.epsilon)
    (mul := fun b a => sphereCopowerLaxData.{u, v}.mu
      ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a))
    (generator := operatorGenerator.{u, v})
    (index := fun {n k} g => basedDiscreteIncl.{u, v, 0} (n ⟶ k) g ≫
      symmetricIndexInclusion.{u, v}.map
        ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k))
    (comp := fun n k l => Enriched.SphereOperator.composition
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj l))
    (index_point := fun {n k} g => operatorGenerator_indexPoint g)
    (generator_comp := fun a b n k l f g => operatorGenerator_comp a b n k l f g)
    (generator_coefficient := fun {a b} r n k f => operatorGenerator_coefficient r n k f)
    (right_unit := fun a => nativeSphere_rightUnit a) a n n' k g f


end NativeInverseGenerators

section ReconstructedActions

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

variable (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})

/-- The inverse uses the complete native coefficient generator followed by the
actual functor map. -/
def reconstructedCurriedAction (a n k : I) (f : a ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⟶
      (ihom (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))).obj
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)) :=
  operatorGenerator a n k f ≫ F.toEnrichedFunctor.map
    (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)

/-- The actual functor carries the whole native coefficient relation to the inverse action. -/
theorem reconstructedCurriedAction_coefficient {a b : I} (r : a ⟶ b) (n k : I)
    (f : b ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.map r ≫ reconstructedCurriedAction F b n k f =
      reconstructedCurriedAction F a n k ((r ⊗ₘ 𝟙 n) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let SF := sphereCopowerEnrichedFunctor.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let H : V := Enriched.SphereOperator.Hom d SF (R.obj n) (R.obj k)
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Y : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)
  let Z : V := (ihom X).obj Y
  let c : A ⟶ B := sphereSequence.{u, v}.functor.map r
  let p : B ⟶ H := operatorGenerator b n k f
  let q : A ⟶ H := operatorGenerator a n k ((r ⊗ₘ 𝟙 n) ≫ f)
  let m : H ⟶ Z := F.toEnrichedFunctor.map
    (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)
  have hCoefficient : c ≫ p = q := operatorGenerator_coefficient r n k f
  change c ≫ p ≫ m = q ≫ m
  exact (Category.assoc c p m).symm.trans
    (congrArg (fun v : A ⟶ H => v ≫ m) hCoefficient)

/-- The inverse coefficient unit is the actual functor's enriched identity. -/
theorem reconstructedCurriedAction_unit (n : I) :
    sphereCopowerLaxData.{u, v}.epsilon ≫
      reconstructedCurriedAction F (𝟙_ I) n n (λ_ n).hom =
    eId PointedCGWH.{u, v} (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let SF := sphereCopowerEnrichedFunctor.{u, v}
  let L := sphereCopowerLaxData.{u, v}
  let U : V := 𝟙_ V
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let H : V := Enriched.SphereOperator.Hom d SF (R.obj n) (R.obj n)
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Z : V := (ihom X).obj X
  let ε : U ⟶ A := L.epsilon
  let p : A ⟶ H := operatorGenerator (𝟙_ I) n n (λ_ n).hom
  let i : U ⟶ H := Enriched.SphereOperator.identityGenerator d SF L (R.obj n)
  let m : H ⟶ Z := F.toEnrichedFunctor.map
    (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} n)
  have hGenerator : i = ε ≫ p := operatorGenerator_unit n
  have hMap : i ≫ m = eId V X :=
    F.toEnrichedFunctor.map_id (symmetricOperatorObj.{u, v} n)
  change ε ≫ p ≫ m = eId V X
  exact (Category.assoc ε p m).symm.trans
    ((congrArg (fun v : U ⟶ H => v ≫ m) hGenerator.symm).trans hMap)

section GenericCurriedTransport
universe uV vV
variable {V₀ : Type uV} [Category.{vV} V₀] [MonoidalCategory V₀]
  [BraidedCategory V₀] [MonoidalClosed V₀]

omit [BraidedCategory V₀] in
private theorem selfComposition_rightPoint (X Y Z A : V₀)
    (p : A ⟶ (ihom X).obj Y) (q : Y ⟶ Z) :
    (ρ_ A).inv ≫ (p ⊗ₘ eHomEquiv V₀ q) ≫
      eComp V₀ X Y Z = p ≫ (ihom X).map q := by
  let V := V₀
  let U : V := 𝟙_ V
  let H₀ : V := (ihom X).obj Y
  let H₁ : V := (ihom Y).obj Z
  let H₂ : V := (ihom X).obj Z
  let e : U ⟶ H₁ := eHomEquiv V q
  let c : H₀ ⊗ H₁ ⟶ H₂ := eComp V X Y Z
  let s : H₀ ⊗ U ⟶ H₀ ⊗ H₁ := H₀ ◁ e
  let d : H₀ ⟶ H₂ := (ρ_ H₀).inv ≫ s ≫ c
  have hSelf : d = (ihom X).map q :=
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft V X q
  have hPad : (ρ_ A).inv ≫ (p ⊗ₘ e) = p ≫ (ρ_ H₀).inv ≫ s :=
    MonoidalCategory.rightUnitor_inv_comp_tensorHom p e
  have h₀ : (ρ_ A).inv ≫ (p ⊗ₘ e) ≫ c = ((ρ_ A).inv ≫ (p ⊗ₘ e)) ≫ c :=
    (Category.assoc (ρ_ A).inv (p ⊗ₘ e) c).symm
  have h₁ : ((ρ_ A).inv ≫ (p ⊗ₘ e)) ≫ c = (p ≫ (ρ_ H₀).inv ≫ s) ≫ c :=
    congrArg (fun v : A ⟶ H₀ ⊗ H₁ => v ≫ c) hPad
  have h₂ : (p ≫ (ρ_ H₀).inv ≫ s) ≫ c = p ≫ d :=
    (Category.assoc p ((ρ_ H₀).inv ≫ s) c).trans
      (congrArg (fun v : H₀ ⟶ H₂ => p ≫ v) (Category.assoc (ρ_ H₀).inv s c))
  have h₃ : p ≫ d = p ≫ (ihom X).map q :=
    congrArg (fun v : H₀ ⟶ H₂ => p ≫ v) hSelf
  change (ρ_ A).inv ≫ (p ⊗ₘ e) ≫ c = p ≫ (ihom X).map q
  exact h₀.trans (h₁.trans (h₂.trans h₃))

omit [BraidedCategory V₀] in
private theorem selfComposition_leftPoint (X Y Z A : V₀)
    (p : X ⟶ Y) (q : A ⟶ (ihom Y).obj Z) :
    (λ_ A).inv ≫ (eHomEquiv V₀ p ⊗ₘ q) ≫
      eComp V₀ X Y Z =
    q ≫ (MonoidalClosed.pre p).app Z := by
  let V := V₀
  let U : V := 𝟙_ V
  let H₀ : V := (ihom X).obj Y
  let H₁ : V := (ihom Y).obj Z
  let H₂ : V := (ihom X).obj Z
  let e : U ⟶ H₀ := eHomEquiv V p
  let c : H₀ ⊗ H₁ ⟶ H₂ := eComp V X Y Z
  let s : U ⊗ H₁ ⟶ H₀ ⊗ H₁ := e ▷ H₁
  let d : H₁ ⟶ H₂ := (λ_ H₁).inv ≫ s ≫ c
  have hSelf : d = (MonoidalClosed.pre p).app Z :=
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight V p Z
  have hPad : (λ_ A).inv ≫ (e ⊗ₘ q) = q ≫ (λ_ H₁).inv ≫ s :=
    MonoidalCategory.leftUnitor_inv_comp_tensorHom e q
  have h₀ : (λ_ A).inv ≫ (e ⊗ₘ q) ≫ c = ((λ_ A).inv ≫ (e ⊗ₘ q)) ≫ c :=
    (Category.assoc (λ_ A).inv (e ⊗ₘ q) c).symm
  have h₁ : ((λ_ A).inv ≫ (e ⊗ₘ q)) ≫ c = (q ≫ (λ_ H₁).inv ≫ s) ≫ c :=
    congrArg (fun v : A ⟶ H₀ ⊗ H₁ => v ≫ c) hPad
  have h₂ : (q ≫ (λ_ H₁).inv ≫ s) ≫ c = q ≫ d :=
    (Category.assoc q ((λ_ H₁).inv ≫ s) c).trans
      (congrArg (fun v : H₁ ⟶ H₂ => q ≫ v) (Category.assoc (λ_ H₁).inv s c))
  have h₃ : q ≫ d = q ≫ (MonoidalClosed.pre p).app Z :=
    congrArg (fun v : H₁ ⟶ H₂ => q ≫ v) hSelf
  change (λ_ A).inv ≫ (e ⊗ₘ q) ≫ c = q ≫ (MonoidalClosed.pre p).app Z
  exact h₀.trans (h₁.trans (h₂.trans h₃))

private theorem nativeCurriedCompositionTransport
    {A B C X Y Z H₀ H₁ H₂ : V₀}
    (p : A ⟶ H₀) (q : B ⟶ H₁) (r : C ⟶ H₂)
    (u : H₀ ⟶ (ihom X).obj Y) (v : H₁ ⟶ (ihom Y).obj Z)
    (w : H₂ ⟶ (ihom X).obj Z) (c : H₀ ⊗ H₁ ⟶ H₂) (mul₀ : B ⊗ A ⟶ C)
    (hMap : c ≫ w = (u ⊗ₘ v) ≫ eComp V₀ X Y Z)
    (hSource : (p ⊗ₘ q) ≫ c = (β_ A B).hom ≫ mul₀ ≫ r) :
    ((p ≫ u) ⊗ₘ (q ≫ v)) ≫ eComp V₀ X Y Z = (β_ A B).hom ≫ mul₀ ≫ r ≫ w := by
  rw [← MonoidalCategory.tensorHom_comp_tensorHom p q u v, Category.assoc,
    ← hMap, ← Category.assoc, hSource]
  simp only [Category.assoc]

omit [BraidedCategory V₀] in
private theorem nativeCurriedTargetTransport
    {A X Y Z H₀ H₁ H₂ : V₀}
    (p : A ⟶ H₀) (q : 𝟙_ V₀ ⟶ H₁) (z : A ⟶ H₂) (t : Y ⟶ Z)
    (u : H₀ ⟶ (ihom X).obj Y) (v : H₁ ⟶ (ihom Y).obj Z)
    (w : H₂ ⟶ (ihom X).obj Z) (c : H₀ ⊗ H₁ ⟶ H₂)
    (hImage : q ≫ v = eHomEquiv V₀ t)
    (hMap : c ≫ w = (u ⊗ₘ v) ≫ eComp V₀ X Y Z)
    (hSource : (ρ_ A).inv ≫ (p ⊗ₘ q) ≫ c = z) :
    (p ≫ u) ≫ (ihom X).map t = z ≫ w := by
  have hTensor : (p ⊗ₘ q) ≫ (u ⊗ₘ v) = (p ≫ u) ⊗ₘ eHomEquiv V₀ t :=
    (MonoidalCategory.tensorHom_comp_tensorHom p q u v).trans
      (congrArg (fun e => (p ≫ u) ⊗ₘ e) hImage)
  calc
    _ = (ρ_ A).inv ≫ ((p ≫ u) ⊗ₘ eHomEquiv V₀ t) ≫ eComp V₀ X Y Z :=
      (selfComposition_rightPoint X Y Z A (p ≫ u) t).symm
    _ = (ρ_ A).inv ≫ ((p ⊗ₘ q) ≫ (u ⊗ₘ v)) ≫ eComp V₀ X Y Z := by
      rw [hTensor]
    _ = (ρ_ A).inv ≫ (p ⊗ₘ q) ≫ c ≫ w := by
      simp only [Category.assoc]
      rw [← hMap]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun e => e ≫ w) hSource

omit [BraidedCategory V₀] in
private theorem nativeCurriedInputTransport
    {A X Y Z H₀ H₁ H₂ : V₀}
    (p : 𝟙_ V₀ ⟶ H₀) (q : A ⟶ H₁) (z : A ⟶ H₂) (t : X ⟶ Y)
    (u : H₀ ⟶ (ihom X).obj Y) (v : H₁ ⟶ (ihom Y).obj Z)
    (w : H₂ ⟶ (ihom X).obj Z) (c : H₀ ⊗ H₁ ⟶ H₂)
    (hImage : p ≫ u = eHomEquiv V₀ t)
    (hMap : c ≫ w = (u ⊗ₘ v) ≫ eComp V₀ X Y Z)
    (hSource : (λ_ A).inv ≫ (p ⊗ₘ q) ≫ c = z) :
    (q ≫ v) ≫ (MonoidalClosed.pre t).app Z = z ≫ w := by
  have hTensor : (p ⊗ₘ q) ≫ (u ⊗ₘ v) = eHomEquiv V₀ t ⊗ₘ (q ≫ v) :=
    (MonoidalCategory.tensorHom_comp_tensorHom p q u v).trans
      (congrArg (fun e => e ⊗ₘ (q ≫ v)) hImage)
  calc
    _ = (λ_ A).inv ≫ (eHomEquiv V₀ t ⊗ₘ (q ≫ v)) ≫ eComp V₀ X Y Z :=
      (selfComposition_leftPoint X Y Z A t (q ≫ v)).symm
    _ = (λ_ A).inv ≫ ((p ⊗ₘ q) ≫ (u ⊗ₘ v)) ≫ eComp V₀ X Y Z := by
      rw [hTensor]
    _ = (λ_ A).inv ≫ (p ⊗ₘ q) ≫ c ≫ w := by
      simp only [Category.assoc]
      rw [← hMap]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun e => e ≫ w) hSource
end GenericCurriedTransport

private theorem nativeFunctorComposition
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (n k l : I) :
    Enriched.SphereOperator.composition
        (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
        sphereCopowerLaxData.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj l) ≫
      F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} l) =
    (F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k) ⊗ₘ
      F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} k) (symmetricOperatorObj.{u, v} l)) ≫
      eComp PointedCGWH.{u, v}
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k))
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} l)) := by
  have hMap := F.toEnrichedFunctor.map_comp (symmetricOperatorObj.{u, v} n)
    (symmetricOperatorObj.{u, v} k) (symmetricOperatorObj.{u, v} l)
  have hComp := Enriched.SphereOperator.operatorIndex_comp
    (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
    sphereCopowerLaxData.{u, v} (symmetricOperatorObj.{u, v} n)
    (symmetricOperatorObj.{u, v} k) (symmetricOperatorObj.{u, v} l)
  exact (congrArg (fun c => c ≫ F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
    (symmetricOperatorObj.{u, v} l)) hComp).symm.trans hMap

/-- The inverse retains all original coefficient products and source-associator labels. -/
theorem reconstructedCurriedAction_comp (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (reconstructedCurriedAction F a n k f ⊗ₘ reconstructedCurriedAction F b k l g) ≫
      eComp PointedCGWH.{u, v}
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k))
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} l)) =
    (β_ (sphereSequence.{u, v}.functor.obj a) (sphereSequence.{u, v}.functor.obj b)).hom ≫
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ≫
      reconstructedCurriedAction F (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) := by
  exact nativeCurriedCompositionTransport
    (p := operatorGenerator a n k f) (q := operatorGenerator b k l g)
    (r := operatorGenerator (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g))
    (mul₀ := sphereCopowerLaxData.{u, v}.mu
      ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a))
    (u := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k))
    (v := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} k) (symmetricOperatorObj.{u, v} l))
    (w := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} l))
    (c := Enriched.SphereOperator.composition
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj l))
    (hMap := nativeFunctorComposition F n k l)
    (hSource := operatorGenerator_comp a b n k l f g)

private theorem reconstructed_indexMap {n k : I} (f : n ⟶ k) :
    eHomEquiv PointedCGWH.{u, v}
      (((symmetricSequenceRestriction.{u, v}).obj F).functor.map f) =
    basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫ symmetricIndexInclusion.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k) ≫
      F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k) :=
  (congrArg (fun z => eHomEquiv PointedCGWH.{u, v} z)
    (symmetricSequenceRestriction_map F f)).trans (Equiv.apply_symm_apply _ _)

/-- Every full inverse coefficient action is natural in the original target-index arrow. -/
theorem reconstructedCurriedAction_target (a n k l : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    reconstructedCurriedAction F a n k f ≫
      (ihom (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))).map
        (((symmetricSequenceRestriction.{u, v}).obj F).functor.map g) =
    reconstructedCurriedAction F a n l (f ≫ g) := by
  exact nativeCurriedTargetTransport
    (p := operatorGenerator a n k f)
    (q := basedDiscreteIncl.{u, v, 0} (k ⟶ l) g ≫ symmetricIndexInclusion.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj k) ((copowerRestriction.{u, v, 0} I).obj l))
    (z := operatorGenerator a n l (f ≫ g))
    (t := ((symmetricSequenceRestriction.{u, v}).obj F).functor.map g)
    (u := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k))
    (v := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} k) (symmetricOperatorObj.{u, v} l))
    (w := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} l))
    (c := Enriched.SphereOperator.composition
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj l))
    (hMap := nativeFunctorComposition F n k l)
    (hImage := (reconstructed_indexMap F g).symm)
    (hSource := operatorGenerator_target a n k l f g)

/-- Every inverse coefficient action is natural in the entire original source-index arrow. -/
theorem reconstructedCurriedAction_input (a n n' k : I)
    (g : n ⟶ n') (f : a ⊗ n' ⟶ k) :
    reconstructedCurriedAction F a n' k f ≫
      (MonoidalClosed.pre (((symmetricSequenceRestriction.{u, v}).obj F).functor.map g)).app
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)) =
    reconstructedCurriedAction F a n k ((𝟙 a ⊗ₘ g) ≫ f) := by
  exact nativeCurriedInputTransport
    (p := basedDiscreteIncl.{u, v, 0} (n ⟶ n') g ≫ symmetricIndexInclusion.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj n'))
    (q := operatorGenerator a n' k f)
    (z := operatorGenerator a n k ((𝟙 a ⊗ₘ g) ≫ f))
    (t := ((symmetricSequenceRestriction.{u, v}).obj F).functor.map g)
    (u := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} n'))
    (v := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n') (symmetricOperatorObj.{u, v} k))
    (w := F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k))
    (c := Enriched.SphereOperator.composition
      (copowerUnderlyingMonoidalData.{u, v, 0} I) sphereCopowerEnrichedFunctor.{u, v}
      sphereCopowerLaxData.{u, v}
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj n')
      ((copowerRestriction.{u, v, 0} I).obj k))
    (hMap := nativeFunctorComposition F n n' k)
    (hImage := (reconstructed_indexMap F g).symm)
    (hSource := operatorGenerator_input a n n' k g f)

/-- Every reconstructed ordinary label acts by its entire native coefficient generator. -/
def reconstructedArrowAction (a n k : I) (f : a ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⊗ ((symmetricSequenceRestriction.{u, v}).obj
        F).functor.obj n ⟶
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj k :=
  (β_ (sphereSequence.{u, v}.functor.obj a)
    (((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n)).hom ≫
      MonoidalClosed.uncurry (reconstructedCurriedAction F a n k f)

/-- The Day pair action uses the original identity label in the entire native Hom. -/
def reconstructedPairAction (a n : I) :
    sphereSequence.{u, v}.functor.obj a ⊗ ((symmetricSequenceRestriction.{u, v}).obj
        F).functor.obj n ⟶
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj (a ⊗ n) :=
  reconstructedArrowAction F a n (a ⊗ n) (𝟙 (a ⊗ n))

/-- The reconstructed action is natural for every actual target-index map. -/
theorem reconstructedArrowAction_target (a n k l : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    reconstructedArrowAction F a n k f ≫
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.map g =
    reconstructedArrowAction F a n l (f ≫ g) := by
  let V := PointedCGWH.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Y : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)
  let Z : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} l)
  let H : V := (ihom X).obj Y
  let H' : V := (ihom X).obj Z
  let p : A ⟶ H := reconstructedCurriedAction F a n k f
  let q : A ⟶ H' := reconstructedCurriedAction F a n l (f ≫ g)
  let t : Y ⟶ Z := ((symmetricSequenceRestriction.{u, v}).obj F).functor.map g
  let b : A ⊗ X ⟶ X ⊗ A := (β_ A X).hom
  let u : X ⊗ A ⟶ Y := MonoidalClosed.uncurry p
  let v : X ⊗ A ⟶ Z := MonoidalClosed.uncurry q
  have hCurried : p ≫ (ihom X).map t = q := reconstructedCurriedAction_target F a n k l f g
  have hUncurry : MonoidalClosed.uncurry (p ≫ (ihom X).map t) = v :=
    congrArg (fun z : A ⟶ H' => MonoidalClosed.uncurry z) hCurried
  have hNatural : MonoidalClosed.uncurry (p ≫ (ihom X).map t) = u ≫ t :=
    MonoidalClosed.uncurry_natural_right p t
  change (b ≫ u) ≫ t = b ≫ v
  exact (Category.assoc b u t).trans
    (congrArg (fun z : X ⊗ A ⟶ Z => b ≫ z) (hNatural.symm.trans hUncurry))

/-- The full inverse pair followed by an arbitrary label is the whole labelled action. -/
theorem reconstructedPairAction_target (a n k : I) (f : a ⊗ n ⟶ k) :
    reconstructedPairAction F a n ≫
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.map f =
    reconstructedArrowAction F a n k f := by
  simpa only [reconstructedPairAction, Category.id_comp] using
    reconstructedArrowAction_target F a n (a ⊗ n) k (𝟙 (a ⊗ n)) f

/-- The entire inverse action retains the original sphere coefficient naturality. -/
theorem reconstructedArrowAction_coefficient {a b : I} (r : a ⟶ b) (n k : I)
    (f : b ⊗ n ⟶ k) :
    (sphereSequence.{u, v}.functor.map r ▷ ((symmetricSequenceRestriction.{u, v}).obj
        F).functor.obj n) ≫
      reconstructedArrowAction F b n k f =
    reconstructedArrowAction F a n k ((r ⊗ₘ 𝟙 n) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Y : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let H : V := (ihom X).obj Y
  let p : A ⟶ B := sphereSequence.{u, v}.functor.map r
  let q : B ⟶ H := reconstructedCurriedAction F b n k f
  let t : A ⟶ H := reconstructedCurriedAction F a n k ((r ⊗ₘ 𝟙 n) ≫ f)
  let u : X ⊗ B ⟶ Y := MonoidalClosed.uncurry q
  let v : X ⊗ A ⟶ Y := MonoidalClosed.uncurry t
  let bA : A ⊗ X ⟶ X ⊗ A := (β_ A X).hom
  let bB : B ⊗ X ⟶ X ⊗ B := (β_ B X).hom
  let d : A ⊗ X ⟶ B ⊗ X := p ▷ X
  let s : X ⊗ A ⟶ X ⊗ B := X ◁ p
  have hCurried : p ≫ q = t := reconstructedCurriedAction_coefficient F r n k f
  have hUncurry : MonoidalClosed.uncurry (p ≫ q) = v :=
    congrArg (fun z : A ⟶ H => MonoidalClosed.uncurry z) hCurried
  have hNatural : MonoidalClosed.uncurry (p ≫ q) = s ≫ u :=
    MonoidalClosed.uncurry_natural_left p q
  have hWhole : s ≫ u = v := hNatural.symm.trans hUncurry
  have hBraid : d ≫ bB = bA ≫ s := BraidedCategory.braiding_naturality_left (C := V) p X
  have h₀ : d ≫ bB ≫ u = (d ≫ bB) ≫ u := (Category.assoc d bB u).symm
  have h₁ : (d ≫ bB) ≫ u = (bA ≫ s) ≫ u :=
    congrArg (fun z : A ⊗ X ⟶ X ⊗ B => z ≫ u) hBraid
  have h₂ : (bA ≫ s) ≫ u = bA ≫ s ≫ u := Category.assoc bA s u
  have h₃ : bA ≫ s ≫ u = bA ≫ v :=
    congrArg (fun z : X ⊗ A ⟶ Y => bA ≫ z) hWhole
  change d ≫ bB ≫ u = bA ≫ v
  exact h₀.trans (h₁.trans (h₂.trans h₃))

/-- The entire inverse action retains every original source-index naturality square. -/
theorem reconstructedArrowAction_input (a n n' k : I)
    (g : n ⟶ n') (f : a ⊗ n' ⟶ k) :
    (sphereSequence.{u, v}.functor.obj a ◁ ((symmetricSequenceRestriction.{u, v}).obj
        F).functor.map g) ≫
      reconstructedArrowAction F a n' k f =
    reconstructedArrowAction F a n k ((𝟙 a ⊗ₘ g) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Y : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n')
  let Z : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k)
  let A : V := sphereSequence.{u, v}.functor.obj a
  let H : V := (ihom Y).obj Z
  let H' : V := (ihom X).obj Z
  let p : X ⟶ Y := ((symmetricSequenceRestriction.{u, v}).obj F).functor.map g
  let q : A ⟶ H := reconstructedCurriedAction F a n' k f
  let t : A ⟶ H' := reconstructedCurriedAction F a n k ((𝟙 a ⊗ₘ g) ≫ f)
  let u : Y ⊗ A ⟶ Z := MonoidalClosed.uncurry q
  let v : X ⊗ A ⟶ Z := MonoidalClosed.uncurry t
  let bX : A ⊗ X ⟶ X ⊗ A := (β_ A X).hom
  let bY : A ⊗ Y ⟶ Y ⊗ A := (β_ A Y).hom
  let d : A ⊗ X ⟶ A ⊗ Y := A ◁ p
  let s : X ⊗ A ⟶ Y ⊗ A := p ▷ A
  have hCurried : q ≫ (MonoidalClosed.pre p).app Z = t :=
    reconstructedCurriedAction_input F a n n' k g f
  have hUncurry : MonoidalClosed.uncurry (q ≫ (MonoidalClosed.pre p).app Z) = v :=
    congrArg (fun z : A ⟶ H' => MonoidalClosed.uncurry z) hCurried
  have hNatural : MonoidalClosed.uncurry (q ≫ (MonoidalClosed.pre p).app Z) = s ≫ u :=
    MonoidalClosed.uncurry_pre_app Z q p
  have hWhole : s ≫ u = v := hNatural.symm.trans hUncurry
  have hBraid : d ≫ bY = bX ≫ s := BraidedCategory.braiding_naturality_right (C := V) A p
  have h₀ : d ≫ bY ≫ u = (d ≫ bY) ≫ u := (Category.assoc d bY u).symm
  have h₁ : (d ≫ bY) ≫ u = (bX ≫ s) ≫ u :=
    congrArg (fun z : A ⊗ X ⟶ Y ⊗ A => z ≫ u) hBraid
  have h₂ : (bX ≫ s) ≫ u = bX ≫ s ≫ u := Category.assoc bX s u
  have h₃ : bX ≫ s ≫ u = bX ≫ v :=
    congrArg (fun z : X ⊗ A ⟶ Z => bX ≫ z) hWhole
  change d ≫ bY ≫ u = bX ≫ v
  exact h₀.trans (h₁.trans (h₂.trans h₃))

/-- The original coefficient unit acts as the actual level identity in the inverse. -/
theorem reconstructedArrowAction_unit (n : I) :
    (sphereCopowerLaxData.{u, v}.epsilon ▷
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n) ≫
      reconstructedArrowAction F (𝟙_ I) n n (λ_ n).hom =
    (λ_ (((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n)).hom := by
  let V := PointedCGWH.{u, v}
  let U : V := 𝟙_ V
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let H : V := (ihom X).obj X
  let ε : U ⟶ A := sphereCopowerLaxData.{u, v}.epsilon
  let p : A ⟶ H := reconstructedCurriedAction F (𝟙_ I) n n (λ_ n).hom
  let u : X ⊗ A ⟶ X := MonoidalClosed.uncurry p
  let d : U ⊗ X ⟶ A ⊗ X := ε ▷ X
  let b : A ⊗ X ⟶ X ⊗ A := (β_ A X).hom
  let bU : U ⊗ X ⟶ X ⊗ U := (β_ U X).hom
  let s : X ⊗ U ⟶ X ⊗ A := X ◁ ε
  have hCurried : ε ≫ p = eId V X := reconstructedCurriedAction_unit F n
  have hUncurry : MonoidalClosed.uncurry (ε ≫ p) = MonoidalClosed.uncurry (eId V X) :=
    congrArg (fun z : U ⟶ H => MonoidalClosed.uncurry z) hCurried
  have hNatural : MonoidalClosed.uncurry (ε ≫ p) = s ≫ u :=
    MonoidalClosed.uncurry_natural_left ε p
  have hId : eId V X = MonoidalClosed.curry (ρ_ X).hom := rfl
  have hIdUncurry : MonoidalClosed.uncurry (eId V X) = (ρ_ X).hom :=
    (congrArg (fun z : U ⟶ H => MonoidalClosed.uncurry z) hId).trans
      (MonoidalClosed.uncurry_curry (ρ_ X).hom)
  have hWhole : s ≫ u = (ρ_ X).hom := hNatural.symm.trans (hUncurry.trans hIdUncurry)
  have hBraid : d ≫ b = bU ≫ s := BraidedCategory.braiding_naturality_left (C := V) ε X
  have h₀ : d ≫ b ≫ u = (d ≫ b) ≫ u := (Category.assoc d b u).symm
  have h₁ : (d ≫ b) ≫ u = (bU ≫ s) ≫ u :=
    congrArg (fun z : U ⊗ X ⟶ X ⊗ A => z ≫ u) hBraid
  have h₂ : (bU ≫ s) ≫ u = bU ≫ s ≫ u := Category.assoc bU s u
  have h₃ : bU ≫ s ≫ u = bU ≫ (ρ_ X).hom :=
    congrArg (fun z : X ⊗ U ⟶ X => bU ≫ z) hWhole
  have h₄ : bU ≫ (ρ_ X).hom = (λ_ X).hom := CategoryTheory.braiding_rightUnitor X
  change d ≫ b ≫ u = (λ_ X).hom
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/-- Both original index coordinates are retained by the inverse Day pair naturality. -/
theorem reconstructedPairAction_naturality {a a' n n' : I}
    (r : a ⟶ a') (g : n ⟶ n') :
    (sphereSequence.{u, v}.functor.map r ⊗ₘ ((symmetricSequenceRestriction.{u, v}).obj
        F).functor.map g) ≫
      reconstructedPairAction F a' n' =
    reconstructedPairAction F a n ≫
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.map (r ⊗ₘ g) := by
  let X := ((symmetricSequenceRestriction.{u, v}).obj F).functor
  let k : I := a' ⊗ n'
  have hCoefficientRaw : (sphereSequence.{u, v}.functor.map r ▷ X.obj n') ≫
      reconstructedPairAction F a' n' =
      reconstructedArrowAction F a n' k ((r ⊗ₘ 𝟙 n') ≫ 𝟙 k) :=
    reconstructedArrowAction_coefficient F r n' k (𝟙 k)
  have hCoefficient : (sphereSequence.{u, v}.functor.map r ▷ X.obj n') ≫
      reconstructedPairAction F a' n' =
      reconstructedArrowAction F a n' k (r ⊗ₘ 𝟙 n') :=
    hCoefficientRaw.trans
      (congrArg (fun z : a ⊗ n' ⟶ k => reconstructedArrowAction F a n' k z)
        (Category.comp_id (r ⊗ₘ 𝟙 n')))
  have hInput := reconstructedArrowAction_input F a n n' k g (r ⊗ₘ 𝟙 n')
  have hLabel : (𝟙 a ⊗ₘ g) ≫ (r ⊗ₘ 𝟙 n') = r ⊗ₘ g := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  calc
    _ = (sphereSequence.{u, v}.functor.obj a ◁ X.map g) ≫ (sphereSequence.{u,
        v}.functor.map r ▷ X.obj n') ≫
        reconstructedPairAction F a' n' := by
      rw [MonoidalCategory.tensorHom_def', Category.assoc]
    _ = (sphereSequence.{u, v}.functor.obj a ◁ X.map g) ≫ reconstructedArrowAction F a
        n' k (r ⊗ₘ 𝟙 n') :=
      congrArg (fun z => (sphereSequence.{u, v}.functor.obj a ◁ X.map g) ≫ z) hCoefficient
    _ = reconstructedArrowAction F a n k ((𝟙 a ⊗ₘ g) ≫ (r ⊗ₘ 𝟙 n')) := hInput
    _ = reconstructedArrowAction F a n k (r ⊗ₘ g) :=
      congrArg (fun z => reconstructedArrowAction F a n k z) hLabel
    _ = _ := (reconstructedPairAction_target F a n k (r ⊗ₘ g)).symm

/-- The complete inverse pair transformation is formed from the actual operator action. -/
def reconstructedPairTransformation :
    sphereSequence.{u, v}.functor ⊠ ((symmetricSequenceRestriction.{u, v}).obj F).functor ⟶
      tensor I ⋙ ((symmetricSequenceRestriction.{u, v}).obj F).functor where
  app p := reconstructedPairAction F p.1 p.2
  naturality := by
    rintro ⟨a, n⟩ ⟨a', n'⟩ ⟨r, g⟩
    exact reconstructedPairAction_naturality F r g

/-- Descend the whole inverse Day pair transformation through its original Kan
universal property. -/
def reconstructedModuleAction :
    sphereSequence.{u, v} ⊗ ((symmetricSequenceRestriction.{u, v}).obj F) ⟶
      ((symmetricSequenceRestriction.{u, v}).obj F) :=
  DayFunctor.tensorDesc (reconstructedPairTransformation F)

/-- Every original Day pair generator is retained by the inverse action descent. -/
theorem reconstructedModuleAction_generator (a n : I) :
    (DayFunctor.η sphereSequence.{u, v} ((symmetricSequenceRestriction.{u, v}).obj F)).app (a, n) ≫
      (reconstructedModuleAction F).natTrans.app (a ⊗ n) = reconstructedPairAction F a n :=
  DayFunctor.η_comp_tensorDesc_app (reconstructedPairTransformation F) a n

/-- Every two inverse labelled actions multiply by the original late-first sphere tensorator. -/
theorem reconstructedArrowAction_comp (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ▷
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n) ≫
      reconstructedArrowAction F (b ⊗ a) n l
        ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) =
    (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
      (((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n)).hom ≫
      (sphereSequence.{u, v}.functor.obj b ◁ reconstructedArrowAction F a n k f) ≫
        reconstructedArrowAction F b k l g := by
  let V := PointedCGWH.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let C : V := sphereSequence.{u, v}.functor.obj (b ⊗ a)
  let X : V := ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n
  let Y : V := ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj k
  let Z : V := ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj l
  let h : (b ⊗ a) ⊗ n ⟶ l := (α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g
  let p : A ⟶ (ihom X).obj Y := reconstructedCurriedAction F a n k f
  let q : B ⟶ (ihom Y).obj Z := reconstructedCurriedAction F b k l g
  let r : C ⟶ (ihom X).obj Z := reconstructedCurriedAction F (b ⊗ a) n l h
  let u₀ : A ⊗ X ⟶ Y := reconstructedArrowAction F a n k f
  let v₀ : B ⊗ Y ⟶ Z := reconstructedArrowAction F b k l g
  let w₀ : C ⊗ X ⟶ Z := reconstructedArrowAction F (b ⊗ a) n l h
  let μ₀ : B ⊗ A ⟶ C := sphereCopowerLaxData.{u, v}.mu
    ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a)
  have hu : MonoidalClosed.uncurry p = (β_ A X).inv ≫ u₀ := by
    dsimp only [p, u₀, reconstructedArrowAction]
    rw [Iso.inv_hom_id_assoc]
    rfl
  have hv : MonoidalClosed.uncurry q = (β_ B Y).inv ≫ v₀ := by
    dsimp only [q, v₀, reconstructedArrowAction]
    rw [Iso.inv_hom_id_assoc]
    rfl
  have hw : MonoidalClosed.uncurry r = (β_ C X).inv ≫ w₀ := by
    dsimp only [r, w₀, reconstructedArrowAction]
    rw [Iso.inv_hom_id_assoc]
    rfl
  have hFunctor : MonoidalClosed.uncurry ((p ⊗ₘ q) ≫ eComp V X Y Z) =
      MonoidalClosed.uncurry ((β_ A B).hom ≫ μ₀ ≫ r) :=
    congrArg MonoidalClosed.uncurry (reconstructedCurriedAction_comp F a b n k l f g)
  have hLeft : MonoidalClosed.uncurry ((p ⊗ₘ q) ≫ eComp V X Y Z) =
      (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫ (β_ B (A ⊗ X)).inv ≫
        (B ◁ u₀) ≫ v₀ := by
    rw [MonoidalClosed.uncurry_eComp, hu, hv]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [BraidedCategory.braiding_inv_naturality_left_assoc]
  have hRight : MonoidalClosed.uncurry ((β_ A B).hom ≫ μ₀ ≫ r) =
      (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (μ₀ ▷ X) ≫ w₀ := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left, hw]
    rw [BraidedCategory.braiding_inv_naturality_right_assoc]
  have hShuffle : (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫
      (β_ B (A ⊗ X)).inv ≫ (B ◁ u₀) ≫ v₀ =
    (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (α_ B A X).hom ≫
      (B ◁ u₀) ≫ v₀ := by
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ (B ◁ u₀) ≫ v₀) (nativeArrowBraidShuffle X A B)
  have hWhole : (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (α_ B A X).hom ≫
      (B ◁ u₀) ≫ v₀ =
    (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (μ₀ ▷ X) ≫ w₀ :=
    hShuffle.symm.trans (hLeft.symm.trans (hFunctor.trans hRight))
  have hCancel₁ := (cancel_epi (X ◁ (β_ A B).hom)).1 hWhole
  have hCancel₂ := (cancel_epi (β_ (B ⊗ A) X).inv).1 hCancel₁
  exact hCancel₂.symm

/-- The actual inverse Day pair has the original coefficient-unit and left-unitor equation. -/
theorem reconstructedPairAction_unit (n : I) :
    (sphereCopowerLaxData.{u, v}.epsilon ▷
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n) ≫
      reconstructedPairAction F (𝟙_ I) n =
    (λ_ (((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n)).hom ≫
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.map (λ_ n).inv := by
  let V := PointedCGWH.{u, v}
  let T := ((symmetricSequenceRestriction.{u, v}).obj F).functor
  let U : V := 𝟙_ V
  let E : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let X : V := T.obj n
  let B : V := T.obj ((𝟙_ I) ⊗ n)
  let ε : U ⟶ E := sphereCopowerLaxData.{u, v}.epsilon
  let s : U ⊗ X ⟶ E ⊗ X := ε ▷ X
  let p : E ⊗ X ⟶ B := reconstructedPairAction F (𝟙_ I) n
  let q : B ⟶ X := T.map (λ_ n).hom
  let r : X ⟶ B := T.map (λ_ n).inv
  let l : U ⊗ X ⟶ X := (λ_ X).hom
  let a : E ⊗ X ⟶ X := reconstructedArrowAction F (𝟙_ I) n n (λ_ n).hom
  have hPair : p ≫ q = a := reconstructedPairAction_target F (𝟙_ I) n n (λ_ n).hom
  have hArrow : s ≫ a = l := reconstructedArrowAction_unit F n
  have hUnit : s ≫ p ≫ q = l :=
    (congrArg (fun z : E ⊗ X ⟶ X => s ≫ z) hPair).trans hArrow
  have hCancel : q ≫ r = 𝟙 B :=
    (T.map_comp (λ_ n).hom (λ_ n).inv).symm.trans
      ((congrArg (fun z : (𝟙_ I) ⊗ n ⟶ (𝟙_ I) ⊗ n => T.map z)
        (Iso.hom_inv_id (λ_ n))).trans (T.map_id ((𝟙_ I) ⊗ n)))
  have h₀ : s ≫ p = (s ≫ p) ≫ 𝟙 B := (Category.comp_id (s ≫ p)).symm
  have h₁ : (s ≫ p) ≫ 𝟙 B = (s ≫ p) ≫ q ≫ r :=
    congrArg (fun z : B ⟶ B => (s ≫ p) ≫ z) hCancel.symm
  have h₂ : (s ≫ p) ≫ q ≫ r = (s ≫ p ≫ q) ≫ r :=
    (Category.assoc (s ≫ p) q r).symm.trans
      (congrArg (fun z : U ⊗ X ⟶ X => z ≫ r) (Category.assoc s p q))
  have h₃ : (s ≫ p ≫ q) ≫ r = l ≫ r :=
    congrArg (fun z : U ⊗ X ⟶ X => z ≫ r) hUnit
  change s ≫ p = l ≫ r
  exact h₀.trans (h₁.trans (h₂.trans h₃))

/-- The actual inverse pair multiplication retains the complete late-first
coefficient tensorator. -/
theorem reconstructedPairAction_mul (b a n : I) :
    (sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ▷
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n) ≫
      reconstructedPairAction F (b ⊗ a) n =
    (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
      (((symmetricSequenceRestriction.{u, v}).obj F).functor.obj n)).hom ≫
      (sphereSequence.{u, v}.functor.obj b ◁ reconstructedPairAction F a n) ≫
      reconstructedPairAction F b (a ⊗ n) ≫
        ((symmetricSequenceRestriction.{u, v}).obj F).functor.map (α_ b a n).inv := by
  let V := PointedCGWH.{u, v}
  let T := ((symmetricSequenceRestriction.{u, v}).obj F).functor
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let C : V := sphereSequence.{u, v}.functor.obj (b ⊗ a)
  let X : V := T.obj n
  let Y : V := T.obj ((b ⊗ a) ⊗ n)
  let Z : V := T.obj (b ⊗ (a ⊗ n))
  let W : V := T.obj (a ⊗ n)
  let μ₀ : B ⊗ A ⟶ C := sphereCopowerLaxData.{u, v}.mu
    ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a)
  let s : (B ⊗ A) ⊗ X ⟶ C ⊗ X := μ₀ ▷ X
  let p : C ⊗ X ⟶ Y := reconstructedPairAction F (b ⊗ a) n
  let q : Y ⟶ Z := T.map (α_ b a n).hom
  let r : Z ⟶ Y := T.map (α_ b a n).inv
  let t : A ⊗ X ⟶ W := reconstructedPairAction F a n
  let u : B ⊗ W ⟶ Z := reconstructedPairAction F b (a ⊗ n)
  let k : (B ⊗ A) ⊗ X ⟶ Z := (α_ B A X).hom ≫ (B ◁ t) ≫ u
  let h : (b ⊗ a) ⊗ n ⟶ b ⊗ (a ⊗ n) :=
    (α_ b a n).hom ≫ (𝟙 b ⊗ₘ 𝟙 (a ⊗ n)) ≫ 𝟙 (b ⊗ (a ⊗ n))
  have hLabel : h = (α_ b a n).hom := by
    simp only [h, MonoidalCategory.id_tensorHom_id, Category.comp_id]
  have hRaw : s ≫ reconstructedArrowAction F (b ⊗ a) n (b ⊗ (a ⊗ n)) h = k :=
    reconstructedArrowAction_comp F a b n (a ⊗ n) (b ⊗ (a ⊗ n))
      (𝟙 (a ⊗ n)) (𝟙 (b ⊗ (a ⊗ n)))
  have hArrow : s ≫
      reconstructedArrowAction F (b ⊗ a) n (b ⊗ (a ⊗ n)) (α_ b a n).hom = k :=
    (congrArg (fun z : (b ⊗ a) ⊗ n ⟶ b ⊗ (a ⊗ n) =>
      s ≫ reconstructedArrowAction F (b ⊗ a) n (b ⊗ (a ⊗ n)) z) hLabel.symm).trans hRaw
  have hPair : p ≫ q =
      reconstructedArrowAction F (b ⊗ a) n (b ⊗ (a ⊗ n)) (α_ b a n).hom :=
    reconstructedPairAction_target F (b ⊗ a) n (b ⊗ (a ⊗ n)) (α_ b a n).hom
  have hJoined : s ≫ p ≫ q = k :=
    (congrArg (fun z : C ⊗ X ⟶ Z => s ≫ z) hPair).trans hArrow
  have hCancel : q ≫ r = 𝟙 Y :=
    (T.map_comp (α_ b a n).hom (α_ b a n).inv).symm.trans
      ((congrArg (fun z : (b ⊗ a) ⊗ n ⟶ (b ⊗ a) ⊗ n => T.map z)
        (Iso.hom_inv_id (α_ b a n))).trans (T.map_id ((b ⊗ a) ⊗ n)))
  have h₀ : s ≫ p = (s ≫ p) ≫ 𝟙 Y := (Category.comp_id (s ≫ p)).symm
  have h₁ : (s ≫ p) ≫ 𝟙 Y = (s ≫ p) ≫ q ≫ r :=
    congrArg (fun z : Y ⟶ Y => (s ≫ p) ≫ z) hCancel.symm
  have h₂ : (s ≫ p) ≫ q ≫ r = (s ≫ p ≫ q) ≫ r :=
    (Category.assoc (s ≫ p) q r).symm.trans
      (congrArg (fun z : (B ⊗ A) ⊗ X ⟶ Z => z ≫ r) (Category.assoc s p q))
  have h₃ : (s ≫ p ≫ q) ≫ r = k ≫ r :=
    congrArg (fun z : (B ⊗ A) ⊗ X ⟶ Z => z ≫ r) hJoined
  change s ≫ p = k ≫ r
  exact h₀.trans (h₁.trans (h₂.trans h₃))

private def dayRightProbe (A B Y : SymmetricSequence.{u, v})
    (f : A ⊗ B ⟶ Y) (n : I) :
    A.functor ⋙ tensorRight (B.functor.obj n) ⟶ tensorRight n ⋙ Y.functor where
  app a := (DayFunctor.η A B).app (a, n) ≫ f.natTrans.app (a ⊗ n)
  naturality := by
    intro a a' r
    let V := PointedCGWH.{u, v}
    let A₀ : V := A.functor.obj a
    let A₁ : V := A.functor.obj a'
    let B₀ : V := B.functor.obj n
    let P₀ : V := A₀ ⊗ B₀
    let P₁ : V := A₁ ⊗ B₀
    let Q₀ : V := (A ⊗ B).functor.obj (a ⊗ n)
    let Q₁ : V := (A ⊗ B).functor.obj (a' ⊗ n)
    let Z₀ : V := Y.functor.obj (a ⊗ n)
    let Z₁ : V := Y.functor.obj (a' ⊗ n)
    let p : P₀ ⟶ P₁ := A.functor.map r ▷ B₀
    let j : P₁ ⟶ P₁ := A₁ ◁ 𝟙 B₀
    let i₀ : P₀ ⟶ Q₀ := (DayFunctor.η A B).app (a, n)
    let i₁ : P₁ ⟶ Q₁ := (DayFunctor.η A B).app (a', n)
    let u : Q₀ ⟶ Q₁ := (A ⊗ B).functor.map (r ▷ n)
    let q₀ : Q₀ ⟶ Z₀ := f.natTrans.app (a ⊗ n)
    let q₁ : Q₁ ⟶ Z₁ := f.natTrans.app (a' ⊗ n)
    let v : Z₀ ⟶ Z₁ := Y.functor.map (r ▷ n)
    have hηRaw : (p ≫ j) ≫ i₁ = i₀ ≫ u := by
      simpa only [externalProductBifunctor_obj_map, CategoryTheory.Functor.map_id,
        Functor.comp_map, tensor_map, MonoidalCategory.tensorHom_id] using
        (DayFunctor.η A B).naturality
          (show (a, n) ⟶ (a', n) from (r, 𝟙 n))
    have hj : j = 𝟙 P₁ := MonoidalCategory.whiskerLeft_id A₁ B₀
    have hPad : p ≫ j = p :=
      (congrArg (fun z : P₁ ⟶ P₁ => p ≫ z) hj).trans (Category.comp_id p)
    have hη : p ≫ i₁ = i₀ ≫ u :=
      (congrArg (fun z : P₀ ⟶ P₁ => z ≫ i₁) hPad.symm).trans hηRaw
    have hf : q₀ ≫ v = u ≫ q₁ := (f.natTrans.naturality (r ▷ n)).symm
    have h₀ : p ≫ (i₁ ≫ q₁) = (p ≫ i₁) ≫ q₁ := (Category.assoc p i₁ q₁).symm
    have h₁ : (p ≫ i₁) ≫ q₁ = (i₀ ≫ u) ≫ q₁ :=
      congrArg (fun z : P₀ ⟶ Q₁ => z ≫ q₁) hη
    have h₂ : (i₀ ≫ u) ≫ q₁ = i₀ ≫ u ≫ q₁ := Category.assoc i₀ u q₁
    have h₃ : i₀ ≫ u ≫ q₁ = i₀ ≫ q₀ ≫ v :=
      congrArg (fun z : Q₀ ⟶ Z₁ => i₀ ≫ z) hf.symm
    have h₄ : i₀ ≫ q₀ ≫ v = (i₀ ≫ q₀) ≫ v := (Category.assoc i₀ q₀ v).symm
    change p ≫ (i₁ ≫ q₁) = (i₀ ≫ q₀) ≫ v
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/-- The right-probe component is precisely its defining full Day generator composite. -/
private theorem dayRightProbe_app (A B Y : SymmetricSequence.{u, v})
    (f : A ⊗ B ⟶ Y) (n a : I) :
    (dayRightProbe A B Y f n).app a =
      (DayFunctor.η A B).app (a, n) ≫ f.natTrans.app (a ⊗ n) := rfl

/-- The original Day unit Kan extension lifts the derived whole pair unit law
to the complete inverse module action. -/
theorem reconstructedModuleAction_one :
    (η : 𝟙_ (SymmetricSequence.{u, v}) ⟶ sphereSequence.{u, v}) ▷
        ((symmetricSequenceRestriction.{u, v}).obj F) ≫ reconstructedModuleAction F =
      (λ_ ((symmetricSequenceRestriction.{u, v}).obj F)).hom := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  let X : D := (symmetricSequenceRestriction.{u, v}).obj F
  let one : 𝟙_ D ⟶ sphereSequence.{u, v} := η
  let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
  apply DayFunctor.tensor_hom_ext
  intro a n
  let L := dayRightProbe (𝟙_ D) X X ((one ▷ X) ≫ action) n
  let R := dayRightProbe (𝟙_ D) X X (λ_ X).hom n
  let E : Functor.LeftExtension (Functor.fromPUnit.{0} (𝟙_ I))
      (Functor.fromPUnit.{0} (𝟙_ V)) :=
    Functor.LeftExtension.mk (𝟙_ D).functor (DayFunctor.νNatTrans I V)
  let EP := (Functor.LeftExtension.postcompose₂
    (Functor.fromPUnit.{0} (𝟙_ I)) (Functor.fromPUnit.{0} (𝟙_ V))
    (tensorRight (X.functor.obj n))).obj E
  have hE : E.IsPointwiseLeftKanExtension :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit I V D
  have hEP : EP.IsPointwiseLeftKanExtension :=
    hE.postcompose (tensorRight (X.functor.obj n))
  let EPC : Functor.LeftExtension (Functor.fromPUnit.{0} (𝟙_ I))
      (Functor.fromPUnit.{0} (𝟙_ V) ⋙ tensorRight (X.functor.obj n)) :=
    Functor.LeftExtension.mk ((𝟙_ D).functor ⋙ tensorRight (X.functor.obj n))
      (Functor.whiskerRight (DayFunctor.νNatTrans I V)
          (tensorRight (X.functor.obj n)) ≫ (Functor.associator _ _ _).hom)
  let e : EP ≅ EPC := Functor.LeftExtension.postcompose₂ObjMkIso
    (tensorRight (X.functor.obj n)) (DayFunctor.νNatTrans I V)
  have hEPC : EPC.IsPointwiseLeftKanExtension :=
    (Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso e) hEP
  let _ : EPC.right.IsLeftKanExtension EPC.hom := hEPC.isLeftKanExtension
  have hLR : L = R := by
    apply Functor.hom_ext_of_isLeftKanExtension EPC.right EPC.hom L R
    apply NatTrans.ext
    funext p
    rcases p with ⟨x⟩
    cases x
    simp only [NatTrans.comp_app]
    dsimp [EPC]
    simp only [Category.comp_id]
    let A : V := X.functor.obj n
    let U : V := (𝟙_ D).functor.obj (𝟙_ I)
    let ν : 𝟙_ V ⟶ U := DayFunctor.ν I V
    let η₀ := (DayFunctor.η (𝟙_ D) X).app (𝟙_ I, n)
    let ηS := (DayFunctor.η sphereSequence.{u, v} X).app (𝟙_ I, n)
    let u₀ := (one ▷ X).natTrans.app ((𝟙_ I) ⊗ n)
    let a₀ := action.natTrans.app ((𝟙_ I) ⊗ n)
    let l₀ := (λ_ X).hom.natTrans.app ((𝟙_ I) ⊗ n)
    have hConv : η₀ ≫ u₀ = (one.natTrans.app (𝟙_ I) ▷ A) ≫ ηS := by
      change
        (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
            (𝟙_ D) X).app (𝟙_ I, n) ≫
          ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map
            (one ▷ X)).app ((𝟙_ I) ⊗ n) =
        (((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map one).app
            (𝟙_ I) ▷ ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj X).obj n) ≫
          (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
            sphereSequence.{u, v} X).app (𝟙_ I, n)
      exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app I V one X (𝟙_ I) n
    have hOne : ν ≫ one.natTrans.app (𝟙_ I) = sphereCopowerLaxData.{u, v}.epsilon :=
      sphereCopowerLaxData_one.{u, v}
    have hWhisker : (ν ▷ A) ≫ (one.natTrans.app (𝟙_ I) ▷ A) =
        sphereCopowerLaxData.{u, v}.epsilon ▷ A :=
      (MonoidalCategory.comp_whiskerRight ν (one.natTrans.app (𝟙_ I)) A).symm.trans
        (congrArg (fun z : (𝟙_ V) ⟶ sphereSequence.{u, v}.functor.obj (𝟙_ I) => z ▷ A) hOne)
    have hGen : ηS ≫ a₀ = reconstructedPairAction F (𝟙_ I) n :=
      reconstructedModuleAction_generator F (𝟙_ I) n
    have hUnitor : (ν ▷ A) ≫ η₀ ≫ l₀ =
        (λ_ A).hom ≫ X.functor.map (λ_ n).inv := by
      change
        LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V D ▷
            ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj X).obj n ≫
          (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
            (𝟙_ D) X).app (𝟙_ I, n) ≫
          ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map (λ_ X).hom).app
            ((𝟙_ I) ⊗ n) =
        (λ_ (((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj X).obj n)).hom ≫
          ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj X).map (λ_ n).inv
      exact LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app V X n
    change (ν ▷ A) ≫ η₀ ≫ u₀ ≫ a₀ =
      (ν ▷ A) ≫ η₀ ≫ l₀
    calc
      _ = ((ν ▷ A) ≫ (one.natTrans.app (𝟙_ I) ▷ A)) ≫ (ηS ≫ a₀) := by
        slice_lhs 2 3 => rw [hConv]
        simp only [Category.assoc]
      _ = (sphereCopowerLaxData.{u, v}.epsilon ▷ A) ≫
          reconstructedPairAction F (𝟙_ I) n := by
        rw [hWhisker, hGen]
        rfl
      _ = (λ_ A).hom ≫ X.functor.map (λ_ n).inv := reconstructedPairAction_unit F n
      _ = _ := hUnitor.symm
  change L.app a = R.app a
  exact NatTrans.congr_app hLR a

/-- Composition of the existing lawful associator and generator naturality
comparisons; the plain Day arrow need not satisfy any action/module law. -/
private theorem nativeDayActionTailCharacteristic
    (S X : SymmetricSequence.{u, v}) (action : S ⊗ X ⟶ X) (b a n : I) :
    ((DayFunctor.η S S).app (b, a) ▷ X.functor.obj n) ≫
      (DayFunctor.η (S ⊗ S) X).app (b ⊗ a, n) ≫
      ((α_ S S X).hom ≫ (S ◁ action) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) =
    (α_ (S.functor.obj b) (S.functor.obj a) (X.functor.obj n)).hom ≫
      (S.functor.obj b ◁
        ((DayFunctor.η S X).app (a, n) ≫ action.natTrans.app (a ⊗ n))) ≫
      (DayFunctor.η S X).app (b, a ⊗ n) ≫
      action.natTrans.app (b ⊗ (a ⊗ n)) ≫ X.functor.map (α_ b a n).inv := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency true in
    have hFixed
        {C₀ : Type} [Category.{0} C₀] [MonoidalCategory C₀]
        {V₀ : Type _} [Category.{v} V₀] [MonoidalCategory V₀]
        {D₀ : Type _} [Category.{v} D₀] [MonoidalCategoryStruct D₀]
        [LawfulDayConvolutionMonoidalCategoryStruct C₀ V₀ D₀]
        (S X : D₀) (action : S ⊗ X ⟶ X) (b a n : C₀) :
        ((convolutionExtensionUnit C₀ V₀ S S).app (b, a) ▷
            ((ι C₀ V₀ D₀).obj X).obj n) ≫
          (convolutionExtensionUnit C₀ V₀ (S ⊗ S) X).app (b ⊗ a, n) ≫
          ((ι C₀ V₀ D₀).map
            ((α_ S S X).hom ≫ (S ◁ action) ≫ action)).app ((b ⊗ a) ⊗ n) =
        (α_ (((ι C₀ V₀ D₀).obj S).obj b) (((ι C₀ V₀ D₀).obj S).obj a)
          (((ι C₀ V₀ D₀).obj X).obj n)).hom ≫
          (((ι C₀ V₀ D₀).obj S).obj b ◁
            ((convolutionExtensionUnit C₀ V₀ S X).app (a, n) ≫
              ((ι C₀ V₀ D₀).map action).app (a ⊗ n))) ≫
          (convolutionExtensionUnit C₀ V₀ S X).app (b, a ⊗ n) ≫
          ((ι C₀ V₀ D₀).map action).app (b ⊗ (a ⊗ n)) ≫
          ((ι C₀ V₀ D₀).obj X).map (α_ b a n).inv := by
      let J : D₀ ⥤ C₀ ⥤ V₀ := ι C₀ V₀ D₀
      let B := (J.obj S).obj b
      let A := (J.obj S).obj a
      let N := (J.obj X).obj n
      let T := (b ⊗ a) ⊗ n
      let T' := b ⊗ (a ⊗ n)
      let Y := J.obj (S ⊗ X)
      let H := J.obj (S ⊗ (S ⊗ X))
      let t : H.obj T' ⟶ H.obj T := H.map (α_ b a n).inv
      let p : H ⟶ Y := J.map (S ◁ action)
      let q : Y ⟶ J.obj X := J.map action
      let iSS := (convolutionExtensionUnit C₀ V₀ S S).app (b, a)
      let iOuter := (convolutionExtensionUnit C₀ V₀ (S ⊗ S) X).app (b ⊗ a, n)
      let iInner := (convolutionExtensionUnit C₀ V₀ S X).app (a, n)
      let iRight := (convolutionExtensionUnit C₀ V₀ S (S ⊗ X)).app (b, a ⊗ n)
      let iAct := (convolutionExtensionUnit C₀ V₀ S X).app (b, a ⊗ n)
      let alpha := (J.map (α_ S S X).hom).app T
      have hAssoc : (iSS ▷ N) ≫ iOuter ≫ alpha =
          (α_ B A N).hom ≫ (B ◁ iInner) ≫ iRight ≫ t :=
        associator_hom_unit_unit V₀ S S X b a n
      have hp := p.naturality (α_ b a n).inv
      have hq := q.naturality (α_ b a n).inv
      have hNat : t ≫ p.app T ≫ q.app T =
          p.app T' ≫ q.app T' ≫ (J.obj X).map (α_ b a n).inv :=
        (Category.assoc t (p.app T) (q.app T)).symm.trans
          ((congrArg (fun z : H.obj T' ⟶ Y.obj T => z ≫ q.app T) hp).trans
            ((Category.assoc (p.app T') (Y.map (α_ b a n).inv) (q.app T)).trans
              (congrArg (fun z : Y.obj T' ⟶ (J.obj X).obj T => p.app T' ≫ z) hq)))
      have hOuter : iRight ≫ p.app T' = (B ◁ q.app (a ⊗ n)) ≫ iAct :=
        convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V₀ S action b (a ⊗ n)
      simp only [Functor.map_comp, NatTrans.comp_app]
      change (iSS ▷ N) ≫ iOuter ≫ alpha ≫ p.app T ≫ q.app T =
        (α_ B A N).hom ≫ (B ◁ (iInner ≫ q.app (a ⊗ n))) ≫
          iAct ≫ q.app T' ≫ (J.obj X).map (α_ b a n).inv
      slice_lhs 1 3 => rw [hAssoc]
      simp only [Category.assoc]
      rw [hNat]
      slice_lhs 3 4 => rw [hOuter]
      slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
    have hRaw := hFixed (C₀ := I) (V₀ := V) (D₀ := D) S X action b a n
    dsimp only [V, D] at hRaw
    simpa only [DayFunctor.η, DayFunctor.ι_obj, DayFunctor.ι_map] using hRaw

/-- Composition of the selected lawful right-whisker comparison with the
original generators; no law is assumed of either plain Day arrow. -/
private theorem nativeDayMultiplyTailCharacteristic
    (S X : SymmetricSequence.{u, v}) (mul : S ⊗ S ⟶ S) (action : S ⊗ X ⟶ X)
    (b a n : I) :
    ((DayFunctor.η S S).app (b, a) ▷ X.functor.obj n) ≫
      (DayFunctor.η (S ⊗ S) X).app (b ⊗ a, n) ≫
      ((mul ▷ X) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) =
    (((DayFunctor.η S S).app (b, a) ≫ mul.natTrans.app (b ⊗ a)) ▷
        X.functor.obj n) ≫
      ((DayFunctor.η S X).app (b ⊗ a, n) ≫
        action.natTrans.app ((b ⊗ a) ⊗ n)) := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency true in
    have hFixed
        {C₀ : Type} [Category.{0} C₀] [MonoidalCategory C₀]
        {V₀ : Type _} [Category.{v} V₀] [MonoidalCategory V₀]
        {D₀ : Type _} [Category.{v} D₀] [MonoidalCategoryStruct D₀]
        [LawfulDayConvolutionMonoidalCategoryStruct C₀ V₀ D₀]
        (S X : D₀) (mul : S ⊗ S ⟶ S) (action : S ⊗ X ⟶ X)
        (b a n : C₀) :
        ((convolutionExtensionUnit C₀ V₀ S S).app (b, a) ▷
            ((ι C₀ V₀ D₀).obj X).obj n) ≫
          (convolutionExtensionUnit C₀ V₀ (S ⊗ S) X).app (b ⊗ a, n) ≫
          ((ι C₀ V₀ D₀).map ((mul ▷ X) ≫ action)).app ((b ⊗ a) ⊗ n) =
        (((convolutionExtensionUnit C₀ V₀ S S).app (b, a) ≫
            ((ι C₀ V₀ D₀).map mul).app (b ⊗ a)) ▷
              ((ι C₀ V₀ D₀).obj X).obj n) ≫
          ((convolutionExtensionUnit C₀ V₀ S X).app (b ⊗ a, n) ≫
            ((ι C₀ V₀ D₀).map action).app ((b ⊗ a) ⊗ n)) := by
      let J : D₀ ⥤ C₀ ⥤ V₀ := ι C₀ V₀ D₀
      let N := (J.obj X).obj n
      let T := (b ⊗ a) ⊗ n
      let iSS := (convolutionExtensionUnit C₀ V₀ S S).app (b, a)
      let iOuter := (convolutionExtensionUnit C₀ V₀ (S ⊗ S) X).app (b ⊗ a, n)
      let iAct := (convolutionExtensionUnit C₀ V₀ S X).app (b ⊗ a, n)
      let m := (J.map mul).app (b ⊗ a)
      let w := (J.map (mul ▷ X)).app T
      let q := (J.map action).app T
      have hW : iOuter ≫ w = (m ▷ N) ≫ iAct :=
        convolutionExtensionUnit_comp_ι_map_whiskerRight_app (D := D₀) C₀ V₀ mul X (b ⊗ a) n
      have hWtail : iOuter ≫ w ≫ q = (m ▷ N) ≫ iAct ≫ q :=
        (Category.assoc iOuter w q).symm.trans
          ((congrArg (fun z : (J.obj (S ⊗ S)).obj (b ⊗ a) ⊗ N ⟶
              (J.obj (S ⊗ X)).obj T => z ≫ q) hW).trans
            (Category.assoc (m ▷ N) iAct q))
      simp only [Functor.map_comp, NatTrans.comp_app]
      change (iSS ▷ N) ≫ iOuter ≫ w ≫ q = ((iSS ≫ m) ▷ N) ≫ (iAct ≫ q)
      simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [hWtail]
    have hRaw := hFixed (C₀ := I) (V₀ := V) (D₀ := D) S X mul action b a n
    dsimp only [V, D] at hRaw
    simpa only [DayFunctor.η, DayFunctor.ι_obj, DayFunctor.ι_map] using hRaw

/-- The original multiplication and action generators give the left pair composite. -/
private theorem reconstructedModuleAction_mul_leftGenerator (b a n : I) :
    let X : SymmetricSequence.{u, v} := (symmetricSequenceRestriction.{u, v}).obj F
    let mul : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v} := μ
    let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
    ((DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ▷
        X.functor.obj n) ≫
      (DayFunctor.η (sphereSequence.{u, v} ⊗ sphereSequence.{u, v}) X).app (b ⊗ a, n) ≫
      ((mul ▷ X) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) =
    (sphereCopowerLaxData.{u, v}.mu
      ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a) ▷
        X.functor.obj n) ≫ reconstructedPairAction F (b ⊗ a) n := by
  let X : SymmetricSequence.{u, v} := (symmetricSequenceRestriction.{u, v}).obj F
  let mul : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v} := μ
  let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
  have hL := nativeDayMultiplyTailCharacteristic sphereSequence.{u, v} X mul action b a n
  have hMul : (DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ≫
      mul.natTrans.app (b ⊗ a) =
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b) ((copowerRestriction.{u, v, 0} I).obj a) :=
    sphereCopowerLaxData_mul.{u, v} b a
  have hGen : (DayFunctor.η sphereSequence.{u, v} X).app (b ⊗ a, n) ≫
      action.natTrans.app ((b ⊗ a) ⊗ n) = reconstructedPairAction F (b ⊗ a) n :=
    reconstructedModuleAction_generator F (b ⊗ a) n
  rw [hMul, hGen] at hL
  exact hL

/-- The original action generators give the right pair composite with the
unchanged inverse associator in the original index category. -/
private theorem reconstructedModuleAction_mul_rightGenerator (b a n : I) :
    let X : SymmetricSequence.{u, v} := (symmetricSequenceRestriction.{u, v}).obj F
    let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
    ((DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ▷
        X.functor.obj n) ≫
      (DayFunctor.η (sphereSequence.{u, v} ⊗ sphereSequence.{u, v}) X).app (b ⊗ a, n) ≫
      ((α_ sphereSequence.{u, v} sphereSequence.{u, v} X).hom ≫
        (sphereSequence.{u, v} ◁ action) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) =
    (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
      (X.functor.obj n)).hom ≫
      (sphereSequence.{u, v}.functor.obj b ◁ reconstructedPairAction F a n) ≫
      reconstructedPairAction F b (a ⊗ n) ≫ X.functor.map (α_ b a n).inv := by
  let X : SymmetricSequence.{u, v} := (symmetricSequenceRestriction.{u, v}).obj F
  let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
  have hR := nativeDayActionTailCharacteristic sphereSequence.{u, v} X action b a n
  have hGenInner : (DayFunctor.η sphereSequence.{u, v} X).app (a, n) ≫
      action.natTrans.app (a ⊗ n) = reconstructedPairAction F a n :=
    reconstructedModuleAction_generator F a n
  have hGenRight : (DayFunctor.η sphereSequence.{u, v} X).app (b, a ⊗ n) ≫
      action.natTrans.app (b ⊗ (a ⊗ n)) = reconstructedPairAction F b (a ⊗ n) :=
    reconstructedModuleAction_generator F b (a ⊗ n)
  have hGenRightTail :
      (DayFunctor.η sphereSequence.{u, v} X).app (b, a ⊗ n) ≫
        action.natTrans.app (b ⊗ (a ⊗ n)) ≫ X.functor.map (α_ b a n).inv =
      reconstructedPairAction F b (a ⊗ n) ≫ X.functor.map (α_ b a n).inv :=
    (Category.assoc ((DayFunctor.η sphereSequence.{u, v} X).app (b, a ⊗ n))
      (action.natTrans.app (b ⊗ (a ⊗ n))) (X.functor.map (α_ b a n).inv)).symm.trans
      (congrArg (fun z : sphereSequence.{u, v}.functor.obj b ⊗ X.functor.obj (a ⊗ n) ⟶
          X.functor.obj (b ⊗ (a ⊗ n)) => z ≫ X.functor.map (α_ b a n).inv) hGenRight)
  rw [hGenInner, hGenRightTail] at hR
  exact hR

/-- The already-derived pair multiplication comparison in the original full
two-Day-generator vocabulary. No module/action law is supplied as a premise. -/
private theorem reconstructedModuleAction_mul_generatorComparison (b a n : I) :
    let X : SymmetricSequence.{u, v} := (symmetricSequenceRestriction.{u, v}).obj F
    let mul : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v} := μ
    let action : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
    ((DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ▷
        X.functor.obj n) ≫
      (DayFunctor.η (sphereSequence.{u, v} ⊗ sphereSequence.{u, v}) X).app (b ⊗ a, n) ≫
      ((mul ▷ X) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) =
    ((DayFunctor.η sphereSequence.{u, v} sphereSequence.{u, v}).app (b, a) ▷
        X.functor.obj n) ≫
      (DayFunctor.η (sphereSequence.{u, v} ⊗ sphereSequence.{u, v}) X).app (b ⊗ a, n) ≫
      ((α_ sphereSequence.{u, v} sphereSequence.{u, v} X).hom ≫
        (sphereSequence.{u, v} ◁ action) ≫ action).natTrans.app ((b ⊗ a) ⊗ n) := by
  exact (reconstructedModuleAction_mul_leftGenerator F b a n).trans
    ((reconstructedPairAction_mul F b a n).trans
      (reconstructedModuleAction_mul_rightGenerator F b a n).symm)

/-- The actual two Day Kan-extension witnesses detect equality on every full
two-coefficient generator, with native tensor-right colimit preservation. -/
private theorem nativeDayTripleTensor_hom_ext
    {P Q X Y : SymmetricSequence.{u, v}} {f g : (P ⊗ Q) ⊗ X ⟶ Y}
    (h : ∀ (b a n : I),
      ((DayFunctor.η P Q).app (b, a) ▷ X.functor.obj n) ≫
        (DayFunctor.η (P ⊗ Q) X).app (b ⊗ a, n) ≫
        f.natTrans.app ((b ⊗ a) ⊗ n) =
      ((DayFunctor.η P Q).app (b, a) ▷ X.functor.obj n) ≫
        (DayFunctor.η (P ⊗ Q) X).app (b ⊗ a, n) ≫
        g.natTrans.app ((b ⊗ a) ⊗ n)) :
    f = g := by
  apply DayFunctor.tensor_hom_ext
  intro U n
  let L := dayRightProbe (P ⊗ Q) X Y f n
  let R := dayRightProbe (P ⊗ Q) X Y g n
  let E : Functor.LeftExtension (tensor I) (P.functor ⊠ Q.functor) :=
    Functor.LeftExtension.mk (P ⊗ Q).functor (DayFunctor.η P Q)
  let EP := (Functor.LeftExtension.postcompose₂ (tensor I)
    (P.functor ⊠ Q.functor) (tensorRight (X.functor.obj n))).obj E
  have hE : E.IsPointwiseLeftKanExtension :=
    isPointwiseLeftKanExtensionConvolutionExtensionUnit P Q
  have hEP : EP.IsPointwiseLeftKanExtension :=
    hE.postcompose (tensorRight (X.functor.obj n))
  let EPC : Functor.LeftExtension (tensor I)
      ((P.functor ⊠ Q.functor) ⋙ tensorRight (X.functor.obj n)) :=
    Functor.LeftExtension.mk ((P ⊗ Q).functor ⋙ tensorRight (X.functor.obj n))
      (Functor.whiskerRight (DayFunctor.η P Q) (tensorRight (X.functor.obj n)) ≫
        (Functor.associator _ _ _).hom)
  let e : EP ≅ EPC := Functor.LeftExtension.postcompose₂ObjMkIso
    (tensorRight (X.functor.obj n)) (DayFunctor.η P Q)
  have hEPC : EPC.IsPointwiseLeftKanExtension :=
    (Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso e) hEP
  let _ : EPC.right.IsLeftKanExtension EPC.hom := hEPC.isLeftKanExtension
  have hLR : L = R := by
    apply Functor.hom_ext_of_isLeftKanExtension EPC.right EPC.hom L R
    apply NatTrans.ext
    funext p
    rcases p with ⟨b, a⟩
    simp only [NatTrans.comp_app]
    dsimp [EPC]
    simp only [Category.comp_id]
    simp only [L, R, dayRightProbe_app]
    exact h b a n
  change L.app U = R.app U
  exact NatTrans.congr_app hLR U

/-- The original Day convolution Kan extension lifts the derived whole pair
multiplication law to the complete inverse module action. -/
theorem reconstructedModuleAction_mul :
    (μ : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v}) ▷
        ((symmetricSequenceRestriction.{u, v}).obj F) ≫
        reconstructedModuleAction F =
      (α_ sphereSequence.{u, v} sphereSequence.{u, v} ((symmetricSequenceRestriction.{u,
          v}).obj F)).hom ≫
        (sphereSequence.{u, v} ◁ reconstructedModuleAction F) ≫ reconstructedModuleAction F := by
  apply nativeDayTripleTensor_hom_ext
    (P := sphereSequence.{u, v}) (Q := sphereSequence.{u, v})
    (X := (symmetricSequenceRestriction.{u, v}).obj F)
    (Y := (symmetricSequenceRestriction.{u, v}).obj F)
  intro b a n
  exact reconstructedModuleAction_mul_generatorComparison F b a n

/-- The entire original reconstructed module, including both derived module laws,
shared by the reconstruction and inverse functor object data. -/
def reconstructedModuleData :
    CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v} where
  X := (symmetricSequenceRestriction.{u, v}).obj F
  mod :=
    { smul := reconstructedModuleAction F
      one_smul := by exact reconstructedModuleAction_one F
      mul_smul := by exact reconstructedModuleAction_mul F }

/-- The inverse enriched functor supplies a genuine module over the original
sphere Day monoid. Both module laws are derived from its complete action. -/
def reconstructedModule :
    CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v} :=
  { reconstructedModuleData F with
    mod :=
      { smul := (reconstructedModuleData F).mod.smul
        one_smul := (by exact reconstructedModuleAction_one F :
          MonoidalCategory.MonoidalLeftActionStruct.actionHomLeft
              (η : 𝟙_ (SymmetricSequence.{u, v}) ⟶ sphereSequence.{u, v})
              ((symmetricSequenceRestriction.{u, v}).obj F) ≫ reconstructedModuleAction F =
            (MonoidalCategory.MonoidalLeftActionStruct.actionUnitIso
              (C := SymmetricSequence.{u, v}) ((symmetricSequenceRestriction.{u, v}).obj F)).hom)
        mul_smul := (by exact reconstructedModuleAction_mul F :
          MonoidalCategory.MonoidalLeftActionStruct.actionHomLeft
              (μ : sphereSequence.{u, v} ⊗ sphereSequence.{u, v} ⟶ sphereSequence.{u, v})
              ((symmetricSequenceRestriction.{u, v}).obj F) ≫ reconstructedModuleAction F =
            (MonoidalCategory.MonoidalLeftActionStruct.actionAssocIso
              sphereSequence.{u, v} sphereSequence.{u, v}
              ((symmetricSequenceRestriction.{u, v}).obj F)).hom ≫
              MonoidalCategory.MonoidalLeftActionStruct.actionHomRight
                sphereSequence.{u, v} (reconstructedModuleAction F) ≫
                  reconstructedModuleAction F) } }

/-- The inverse module uses exactly the original canonical restricted sequence. -/
theorem reconstructedModule_obj :
    (reconstructedModule F).X = (symmetricSequenceRestriction.{u, v}).obj F := rfl

/-- The complete inverse module action is exactly its original Day Kan descent. -/
theorem reconstructedModule_smul :
    ModObj.smul (M := sphereSequence.{u, v}) (X := (reconstructedModule F).X) =
      reconstructedModuleAction F := rfl

end ReconstructedActions

section ReconstructedMorphisms

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

variable {F G H : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}}

/-- Every genuine operator transformation intertwines every whole labelled
coefficient action in the inverse module. -/
theorem reconstructedArrowAction_morphism (f : F ⟶ G) (a n k : I)
    (g : a ⊗ n ⟶ k) :
    reconstructedArrowAction F a n k g ≫
        EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} k) =
      (sphereSequence.{u, v}.functor.obj a ◁ EnrichedFunctorCat.component f
          (symmetricOperatorObj.{u, v} n)) ≫
        reconstructedArrowAction G a n k g := by
  let V := PointedCGWH.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let X : V := F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let Y : V := G.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n)
  let K : V := symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    symmetricOperatorObj.{u, v} k
  let p : A ⟶ K := operatorGenerator a n k g
  let q : X ⟶ Y := EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} n)
  let t := EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} k)
  let u₀ := MonoidalClosed.uncurry
    (F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
      (symmetricOperatorObj.{u, v} k))
  let v₀ := MonoidalClosed.uncurry
    (G.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
      (symmetricOperatorObj.{u, v} k))
  have hNat : u₀ ≫ t = (q ▷ K) ≫ v₀ := by
    dsimp only [u₀, v₀, t, q, K, EnrichedFunctorCat.component]
    simpa only [← symmetricOperator_hom, MonoidalCategory.tensorHom_id] using
      GradedNatTrans.uncurriedNaturality f (symmetricOperatorObj.{u, v} n)
        (symmetricOperatorObj.{u, v} k)
  have hF : MonoidalClosed.uncurry (reconstructedCurriedAction F a n k g) =
      (X ◁ p) ≫ u₀ :=
    MonoidalClosed.uncurry_natural_left p
      (F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
        (symmetricOperatorObj.{u, v} k))
  have hG : MonoidalClosed.uncurry (reconstructedCurriedAction G a n k g) =
      (Y ◁ p) ≫ v₀ :=
    MonoidalClosed.uncurry_natural_left p
      (G.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
        (symmetricOperatorObj.{u, v} k))
  have hExchange : (X ◁ p) ≫ (q ▷ K) = (q ▷ A) ≫ (Y ◁ p) :=
    MonoidalCategory.whisker_exchange q p
  have hPoint : MonoidalClosed.uncurry (reconstructedCurriedAction F a n k g) ≫ t =
      (q ▷ A) ≫ MonoidalClosed.uncurry (reconstructedCurriedAction G a n k g) := by
    have h₀ : MonoidalClosed.uncurry (reconstructedCurriedAction F a n k g) ≫ t =
        ((X ◁ p) ≫ u₀) ≫ t :=
      congrArg
        (fun z : X ⊗ A ⟶ F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k) =>
          z ≫ t) hF
    have h₁ : ((X ◁ p) ≫ u₀) ≫ t = (X ◁ p) ≫ u₀ ≫ t :=
      Category.assoc (X ◁ p) u₀ t
    have h₂ : (X ◁ p) ≫ u₀ ≫ t = (X ◁ p) ≫ (q ▷ K) ≫ v₀ :=
      congrArg
        (fun z : X ⊗ K ⟶ G.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k) =>
          (X ◁ p) ≫ z) hNat
    have h₃ : (X ◁ p) ≫ (q ▷ K) ≫ v₀ = ((X ◁ p) ≫ (q ▷ K)) ≫ v₀ :=
      (Category.assoc (X ◁ p) (q ▷ K) v₀).symm
    have h₄ : ((X ◁ p) ≫ (q ▷ K)) ≫ v₀ = ((q ▷ A) ≫ (Y ◁ p)) ≫ v₀ :=
      congrArg (fun z : X ⊗ A ⟶ Y ⊗ K => z ≫ v₀) hExchange
    have h₅ : ((q ▷ A) ≫ (Y ◁ p)) ≫ v₀ = (q ▷ A) ≫ (Y ◁ p) ≫ v₀ :=
      Category.assoc (q ▷ A) (Y ◁ p) v₀
    have h₆ : (q ▷ A) ≫ (Y ◁ p) ≫ v₀ =
        (q ▷ A) ≫ MonoidalClosed.uncurry (reconstructedCurriedAction G a n k g) :=
      congrArg
        (fun z : Y ⊗ A ⟶ G.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k) =>
          (q ▷ A) ≫ z) hG.symm
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))
  have hBraid : (A ◁ q) ≫ (β_ A Y).hom = (β_ A X).hom ≫ (q ▷ A) :=
    BraidedCategory.braiding_naturality_right A q
  change (β_ A X).hom ≫ MonoidalClosed.uncurry
      (reconstructedCurriedAction F a n k g) ≫ t =
    (A ◁ q) ≫ (β_ A Y).hom ≫ MonoidalClosed.uncurry
      (reconstructedCurriedAction G a n k g)
  calc
    _ = (β_ A X).hom ≫ (q ▷ A) ≫
        MonoidalClosed.uncurry (reconstructedCurriedAction G a n k g) := by
      simpa only [Category.assoc] using congrArg (fun z => (β_ A X).hom ≫ z) hPoint
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ MonoidalClosed.uncurry (reconstructedCurriedAction G a n k g))
        hBraid.symm

/-- Every original level component intertwines the full inverse Day pair. -/
theorem reconstructedPairAction_morphism (f : F ⟶ G) (a n : I) :
    reconstructedPairAction F a n ≫
        ((symmetricSequenceRestriction.{u, v}).map f).natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v}.functor.obj a ◁ ((symmetricSequenceRestriction.{u, v}).map
          f).natTrans.app n) ≫
        reconstructedPairAction G a n := by
  simpa only [symmetricSequenceRestriction_component, reconstructedPairAction,
    symmetricSequenceRestriction_obj] using
    reconstructedArrowAction_morphism f a n (a ⊗ n) (𝟙 (a ⊗ n))

/-- The whole Day descent, not only its point components, is natural for every
genuine operator transformation. -/
theorem reconstructedModuleAction_morphism (f : F ⟶ G) :
    reconstructedModuleAction F ≫ (symmetricSequenceRestriction.{u, v}).map f =
      (sphereSequence.{u, v} ◁ (symmetricSequenceRestriction.{u, v}).map f) ≫
          reconstructedModuleAction G := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  let X : D := (symmetricSequenceRestriction.{u, v}).obj F
  let Y : D := (symmetricSequenceRestriction.{u, v}).obj G
  let m : X ⟶ Y := (symmetricSequenceRestriction.{u, v}).map f
  let sF : sphereSequence.{u, v} ⊗ X ⟶ X := reconstructedModuleAction F
  let sG : sphereSequence.{u, v} ⊗ Y ⟶ Y := reconstructedModuleAction G
  apply DayFunctor.tensor_hom_ext
  intro a n
  have hConv : (DayFunctor.η sphereSequence.{u, v} X).app (a, n) ≫
      (sphereSequence.{u, v} ◁ m).natTrans.app (a ⊗ n) =
    (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ (DayFunctor.η
        sphereSequence.{u, v} Y).app (a, n) := by
    change
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
          sphereSequence.{u, v} X).app
          (a, n) ≫ ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map
            (sphereSequence.{u, v} ◁ m)).app (a ⊗ n) =
        (((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).obj sphereSequence.{u, v}).obj a ◁
          ((LawfulDayConvolutionMonoidalCategoryStruct.ι I V D).map m).app n) ≫
          (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit I V
              sphereSequence.{u, v} Y).app
            (a, n)
    exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V sphereSequence.{u, v} m a n
  have hF : (DayFunctor.η sphereSequence.{u, v} X).app (a, n) ≫ sF.natTrans.app (a ⊗ n) =
      reconstructedPairAction F a n := reconstructedModuleAction_generator F a n
  have hG : (DayFunctor.η sphereSequence.{u, v} Y).app (a, n) ≫ sG.natTrans.app (a ⊗ n) =
      reconstructedPairAction G a n := reconstructedModuleAction_generator G a n
  change (DayFunctor.η sphereSequence.{u, v} X).app (a, n) ≫ (sF ≫ m).natTrans.app (a ⊗ n) =
    (DayFunctor.η sphereSequence.{u, v} X).app (a, n) ≫ ((sphereSequence.{u, v} ◁ m) ≫
        sG).natTrans.app (a ⊗ n)
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  calc
    _ = reconstructedPairAction F a n ≫ m.natTrans.app (a ⊗ n) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ m.natTrans.app (a ⊗ n)) hF
    _ = (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ reconstructedPairAction G a n :=
      reconstructedPairAction_morphism f a n
    _ = (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ (DayFunctor.η
        sphereSequence.{u, v} Y).app (a, n) ≫
        sG.natTrans.app (a ⊗ n) := by
      simpa only [Category.assoc] using congrArg
        (fun z => (sphereSequence.{u, v}.functor.obj a ◁ m.natTrans.app n) ≫ z) hG.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ sG.natTrans.app (a ⊗ n)) hConv.symm

/-- A genuine operator transformation yields the original complete Day module morphism. -/
def reconstructedModuleMap (f : F ⟶ G) : reconstructedModule F ⟶ reconstructedModule G :=
  Mod.Hom.mk' ((symmetricSequenceRestriction.{u, v}).map f)
    (by
      change reconstructedModuleAction F ≫ (symmetricSequenceRestriction.{u, v}).map f =
        (sphereSequence.{u, v} ◁ (symmetricSequenceRestriction.{u, v}).map f) ≫
            reconstructedModuleAction G
      exact reconstructedModuleAction_morphism f)

/-- The inverse module morphism retains its complete canonical restricted transformation. -/
theorem reconstructedModuleMap_hom (f : F ⟶ G) :
    (reconstructedModuleMap f).hom = (symmetricSequenceRestriction.{u, v}).map f := rfl

/-- The actual operator carrier maps back to the original module presentation
on every object and every morphism. -/
def operatorToModule : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} ⥤
    CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v} where
  obj F := reconstructedModule F
  map := fun f => reconstructedModuleMap f
  map_id F := by
    apply Mod.hom_ext
    change (symmetricSequenceRestriction.{u, v}).map (𝟙 F) =
      𝟙 ((symmetricSequenceRestriction.{u, v}).obj F)
    exact (symmetricSequenceRestriction.{u, v}).map_id F
  map_comp f g := by
    apply Mod.hom_ext
    change (symmetricSequenceRestriction.{u, v}).map (f ≫ g) =
      (symmetricSequenceRestriction.{u, v}).map f ≫
        (symmetricSequenceRestriction.{u, v}).map g
    exact (symmetricSequenceRestriction.{u, v}).map_comp f g

end ReconstructedMorphisms

section CompleteHomRecovery

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

variable (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})

/-- The inverse module retains every complete original pair action of the
operator functor, at every coefficient and index. -/
theorem reconstructedModule_pairAction (a n : I) :
    pairAction (reconstructedModule F) a n = reconstructedPairAction F a n :=
  reconstructedModuleAction_generator F a n

/-- The inverse module retains every original label after the complete coefficient action. -/
theorem reconstructedModule_arrowAction (a n k : I) (f : a ⊗ n ⟶ k) :
    arrowAction (reconstructedModule F) a n k f = reconstructedArrowAction F a n k f := by
  change pairAction (reconstructedModule F) a n ≫
      ((symmetricSequenceRestriction.{u, v}).obj F).functor.map f = _
  rw [reconstructedModule_pairAction]
  exact reconstructedPairAction_target F a n k f

/-- The inverse module retains the entire closed transpose at every original coefficient label. -/
theorem reconstructedModule_curriedAction (a n k : I) (f : a ⊗ n ⟶ k) :
    curriedArrowAction (reconstructedModule F) a n k f =
      reconstructedCurriedAction F a n k f := by
  dsimp only [curriedArrowAction]
  rw [reconstructedModule_arrowAction]
  dsimp only [reconstructedArrowAction]
  change MonoidalClosed.curry
      ((β_ (sphereSequence.{u, v}.functor.obj a)
        (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))).inv ≫
        (β_ (sphereSequence.{u, v}.functor.obj a)
          (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))).hom ≫
        MonoidalClosed.uncurry (reconstructedCurriedAction F a n k f)) =
      reconstructedCurriedAction F a n k f
  rw [Iso.inv_hom_id_assoc]
  exact MonoidalClosed.curry_uncurry (reconstructedCurriedAction F a n k f)

/-- Every full native Hom coend and every coefficient leg is recovered, with
no projection to point injections in the resulting equality. -/
theorem operatorHomMap_reconstructed (n k : I) :
    operatorHomMap (reconstructedModule F) n k =
      F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n)
        (symmetricOperatorObj.{u, v} k) := by
  let Z : PointedCGWH.{u, v} :=
    (ihom (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n))).obj
      (F.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} k))
  let K : PointedCGWH.{u, v} := symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    symmetricOperatorObj.{u, v} k
  change (operatorHomMap (reconstructedModule F) n k : K ⟶ Z) =
    F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)
  let R := copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  apply Enriched.weightedCoend.hom_ext W sphereCopowerEnrichedFunctor.{u, v}
  intro a
  let a₀ : I := a
  apply discreteSmash_hom_ext.{u, v, 0} (a₀ ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a₀)
  intro f
  have hPoint := operatorHomMap_point (reconstructedModule F) a₀ n k f
  have hCurried := reconstructedModule_curriedAction F a₀ n k f
  change operatorGenerator a₀ n k f ≫
      (operatorHomMap (reconstructedModule F) n k : K ⟶ Z) =
    (curriedArrowAction (reconstructedModule F) a₀ n k f :
      sphereSequence.{u, v}.functor.obj a₀ ⟶ Z) at hPoint
  change (curriedArrowAction (reconstructedModule F) a₀ n k f :
      sphereSequence.{u, v}.functor.obj a₀ ⟶ Z) =
    (reconstructedCurriedAction F a₀ n k f : sphereSequence.{u, v}.functor.obj a₀ ⟶ Z)
      at hCurried
  have hRecovery := hPoint.trans hCurried
  let j := discreteSmashIncl.{u, v, 0} (a₀ ⊗ n ⟶ k) (sphereSequence.{u, v}.functor.obj a₀) f
  let i := Enriched.weightedCoend.ι W sphereCopowerEnrichedFunctor.{u, v} a
  let u : K ⟶ Z := operatorHomMap (reconstructedModule F) n k
  let v : K ⟶ Z :=
    F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)
  change (j ≫ i) ≫ u = (j ≫ i) ≫ v at hRecovery
  change j ≫ i ≫ u = j ≫ i ≫ v
  exact (Category.assoc j i u).symm.trans (hRecovery.trans (Category.assoc j i v))

end CompleteHomRecovery

section OriginalModuleRecovery

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- Restriction of the forward operator functor recovers every arbitrary
original finite-index arrow. -/
theorem symmetricSequenceRestriction_forward_map
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v})
    {n k : I} (f : n ⟶ k) :
    ((symmetricSequenceRestriction.{u, v}).obj (toOperatorFunctor M)).functor.map f =
      M.X.functor.map f := by
  let V := PointedCGWH.{u, v}
  let X : V := M.X.functor.obj n
  let A : V := sphereSequence.{u, v}.functor.obj (𝟙_ I)
  let ε : 𝟙_ V ⟶ A := sphereCopowerLaxData.{u, v}.epsilon
  let g : (𝟙_ I) ⊗ n ⟶ k := (λ_ n).hom ≫ f
  let p : 𝟙_ PointedCGWH.{u, v} ⟶
      (symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} k) :=
    basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
      symmetricIndexInclusion.{u, v}.map ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
  have hPoint : p = ε ≫ operatorGenerator (𝟙_ I) n k g :=
    operatorGenerator_indexPoint f
  have hFull : p ≫ operatorHomMap M n k = ε ≫ curriedArrowAction M (𝟙_ I) n k g :=
    (congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⟶
        (symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}] symmetricOperatorObj.{u, v} k) =>
          z ≫ operatorHomMap M n k) hPoint).trans
      ((Category.assoc ε (operatorGenerator (𝟙_ I) n k g) (operatorHomMap M n k)).trans
        (congrArg (fun z : A ⟶ (ihom (M.X.functor.obj n)).obj (M.X.functor.obj k) =>
          ε ≫ z) (operatorHomMap_point M (𝟙_ I) n k g)))
  have hCross : (ρ_ X).inv ≫ (X ◁ ε) ≫ (β_ A X).inv =
      (λ_ X).inv ≫ (ε ▷ X) := by
    have hBraid := BraidedCategory.braiding_inv_naturality_right X ε
    calc
      _ = (ρ_ X).inv ≫ (β_ (𝟙_ V) X).inv ≫ (ε ▷ X) :=
        congrArg (fun z => (ρ_ X).inv ≫ z) hBraid
      _ = _ := by
        rw [braiding_inv_tensorUnit_left]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hUnit : (ε ▷ X) ≫ arrowAction M (𝟙_ I) n k g =
      (λ_ X).hom ≫ M.X.functor.map f := by
    have hTarget := arrowAction_target M (𝟙_ I) n (λ_ n).hom f
    have hTargetPre :=
      congrArg (fun z : A ⊗ X ⟶ M.X.functor.obj k => (ε ▷ X) ≫ z) hTarget.symm
    have hUnitPost :=
      congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⊗ M.X.functor.obj n ⟶
          M.X.functor.obj n => z ≫ M.X.functor.map f) (arrowAction_unit M n)
    exact hTargetPre.trans
      ((Category.assoc (ε ▷ X) (arrowAction M (𝟙_ I) n n (λ_ n).hom)
        (M.X.functor.map f)).symm.trans hUnitPost)
  rw [symmetricSequenceRestriction_map]
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm V]
  change MonoidalClosed.uncurry' (p ≫ operatorHomMap M n k) = M.X.functor.map f
  rw [hFull]
  dsimp only [MonoidalClosed.uncurry', curriedArrowAction]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  change (ρ_ X).inv ≫ (X ◁ ε) ≫ (β_ A X).inv ≫
    arrowAction M (𝟙_ I) n k g = M.X.functor.map f
  calc
    _ = (λ_ X).inv ≫ (ε ▷ X) ≫ arrowAction M (𝟙_ I) n k g := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ arrowAction M (𝟙_ I) n k g) hCross
    _ = (λ_ X).inv ≫ (λ_ X).hom ≫ M.X.functor.map f :=
      congrArg (fun z => (λ_ X).inv ≫ z) hUnit
    _ = _ := by rw [Iso.inv_hom_id_assoc]

/-- The inverse of the forward functor retains every entire labelled module action. -/
theorem reconstructedArrowAction_forward
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v})
    (a n k : I) (f : a ⊗ n ⟶ k) :
    reconstructedArrowAction (toOperatorFunctor M) a n k f = arrowAction M a n k f := by
  change (β_ (sphereSequence.{u, v}.functor.obj a) (M.X.functor.obj n)).hom ≫
    MonoidalClosed.uncurry (operatorGenerator a n k f ≫ operatorHomMap M n k) = _
  rw [operatorHomMap_point]
  dsimp only [curriedArrowAction]
  rw [MonoidalClosed.uncurry_curry, Iso.hom_inv_id_assoc]

/-- The inverse of the forward functor retains every original Day pair action. -/
theorem reconstructedPairAction_forward
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v})
    (a n : I) :
    reconstructedPairAction (toOperatorFunctor M) a n = pairAction M a n := by
  dsimp only [reconstructedPairAction]
  rw [reconstructedArrowAction_forward]
  dsimp only [arrowAction]
  rw [M.X.functor.map_id, Category.comp_id]

/-- The whole inverse module pair recovers every original sphere coefficient action. -/
theorem reconstructedModule_forward_pair
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v})
    (a n : I) :
    pairAction (reconstructedModule (toOperatorFunctor M)) a n = pairAction M a n :=
  (reconstructedModule_pairAction (toOperatorFunctor M) a n).trans
    (reconstructedPairAction_forward M a n)

/-- The canonical restricted sequence is isomorphic to the original whole
diagram, with identity components and naturality on every original arrow. -/
def sequenceRecoveryIso
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) :
    (symmetricSequenceRestriction.{u, v}).obj (toOperatorFunctor M) ≅ M.X where
  hom :=
    { natTrans :=
        { app n := 𝟙 (M.X.functor.obj n)
          naturality := by
            intro n k f
            let r : M.X.functor.obj n ⟶ M.X.functor.obj k :=
              ((symmetricSequenceRestriction.{u, v}).obj (toOperatorFunctor M)).functor.map f
            have hr : r = M.X.functor.map f := symmetricSequenceRestriction_forward_map M f
            change r ≫ 𝟙 (M.X.functor.obj k) = 𝟙 (M.X.functor.obj n) ≫ M.X.functor.map f
            exact (Category.comp_id r).trans
              (hr.trans (Category.id_comp (M.X.functor.map f)).symm) } }
  inv :=
    { natTrans :=
        { app n := 𝟙 (M.X.functor.obj n)
          naturality := by
            intro n k f
            let r : M.X.functor.obj n ⟶ M.X.functor.obj k :=
              ((symmetricSequenceRestriction.{u, v}).obj (toOperatorFunctor M)).functor.map f
            have hr : r = M.X.functor.map f := symmetricSequenceRestriction_forward_map M f
            change M.X.functor.map f ≫ 𝟙 (M.X.functor.obj k) = 𝟙 (M.X.functor.obj n) ≫ r
            exact (Category.comp_id (M.X.functor.map f)).trans
              (hr.symm.trans (Category.id_comp r).symm) } }
  hom_inv_id := by
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext n
    change (𝟙 (M.X.functor.obj n)) ≫ 𝟙 (M.X.functor.obj n) = 𝟙 (M.X.functor.obj n)
    exact Category.id_comp _
  inv_hom_id := by
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext n
    change (𝟙 (M.X.functor.obj n)) ≫ 𝟙 (M.X.functor.obj n) = 𝟙 (M.X.functor.obj n)
    exact Category.id_comp _

/-- Every comparison component is the original complete level identity. -/
theorem sequenceRecoveryIso_hom_component
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (n : I) :
    (sequenceRecoveryIso M).hom.natTrans.app n = 𝟙 (M.X.functor.obj n) := rfl

/-- Every inverse comparison component is the original complete level identity. -/
theorem sequenceRecoveryIso_inv_component
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (n : I) :
    (sequenceRecoveryIso M).inv.natTrans.app n = 𝟙 (M.X.functor.obj n) := rfl

/-- Native Day whisker-left naturality is the same complete generator comparison. -/
private theorem nativeDayWhiskerLeftCharacteristic
    (P : SymmetricSequence.{u, v}) {Q Q' : SymmetricSequence.{u, v}}
    (f : Q ⟶ Q') (x y : I) :
    (DayFunctor.η P Q).app (x, y) ≫ (P ◁ f).natTrans.app (x ⊗ y) =
      (P.functor.obj x ◁ f.natTrans.app y) ≫
        (DayFunctor.η P Q').app (x, y) := by
  let V := PointedCGWH.{u, v}
  let D := SymmetricSequence.{u, v}
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency true in
    have hRaw := convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      (D := D) V P f x y
    dsimp only [V, D] at hRaw
    simpa only [DayFunctor.η, DayFunctor.ι_obj, DayFunctor.ι_map] using hRaw

/-- The original native Day universal property detects full intertwining
on every generator. Neither plain action arrow is assumed lawful. -/
private theorem nativeDay_intertwining
    {P Q Q' : SymmetricSequence.{u, v}} {f : P ⊗ Q ⟶ Q} {g : P ⊗ Q' ⟶ Q'}
    {m : Q ⟶ Q'}
    (h : ∀ a n : I,
      (DayFunctor.η P Q).app (a, n) ≫ f.natTrans.app (a ⊗ n) ≫
          m.natTrans.app (a ⊗ n) =
        (P.functor.obj a ◁ m.natTrans.app n) ≫
          (DayFunctor.η P Q').app (a, n) ≫ g.natTrans.app (a ⊗ n)) :
    f ≫ m = (P ◁ m) ≫ g := by
  apply DayFunctor.tensor_hom_ext
  intro a n
  have hW := nativeDayWhiskerLeftCharacteristic P m a n
  have hWTail :
      (DayFunctor.η P Q).app (a, n) ≫ (P ◁ m).natTrans.app (a ⊗ n) ≫
          g.natTrans.app (a ⊗ n) =
        (P.functor.obj a ◁ m.natTrans.app n) ≫
          (DayFunctor.η P Q').app (a, n) ≫ g.natTrans.app (a ⊗ n) :=
    (Category.assoc ((DayFunctor.η P Q).app (a, n))
      ((P ◁ m).natTrans.app (a ⊗ n)) (g.natTrans.app (a ⊗ n))).symm.trans
        ((congrArg (fun z : P.functor.obj a ⊗ Q.functor.obj n ⟶
            (P ⊗ Q').functor.obj (a ⊗ n) => z ≫ g.natTrans.app (a ⊗ n)) hW).trans
          (Category.assoc (P.functor.obj a ◁ m.natTrans.app n)
            ((DayFunctor.η P Q').app (a, n)) (g.natTrans.app (a ⊗ n))))
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  exact (h a n).trans hWTail.symm

/-- The actual recovered pair action intertwines the real sequence comparison
at every original sphere coefficient, before the Day universal property. -/
private theorem moduleRecovery_pairSquare
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (a n : I) :
    pairAction (reconstructedModule (toOperatorFunctor M)) a n ≫
        (sequenceRecoveryIso M).hom.natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v}.functor.obj a ◁
        (sequenceRecoveryIso M).hom.natTrans.app n) ≫ pairAction M a n := by
  let B : PointedCGWH.{u, v} := sphereSequence.{u, v}.functor.obj a
  let X : PointedCGWH.{u, v} := M.X.functor.obj n
  let Y : PointedCGWH.{u, v} := M.X.functor.obj (a ⊗ n)
  let p : B ⊗ X ⟶ Y := pairAction (reconstructedModule (toOperatorFunctor M)) a n
  let q : B ⊗ X ⟶ Y := pairAction M a n
  let b : Y ⟶ Y := (sequenceRecoveryIso M).hom.natTrans.app (a ⊗ n)
  let c : X ⟶ X := (sequenceRecoveryIso M).hom.natTrans.app n
  have hp : p = q := reconstructedModule_forward_pair M a n
  have hb : b = 𝟙 Y := rfl
  have hc : c = 𝟙 X := rfl
  change p ≫ b = (B ◁ c) ≫ q
  rw [hp, hb, hc, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Every original Day pair generator gives the full action square of the
actual sequence recovery isomorphism. No new module law is supplied. -/
private theorem moduleRecovery_action
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) :
    let R := reconstructedModule (toOperatorFunctor M)
    let e : R.X ≅ M.X := sequenceRecoveryIso M
    ModObj.smul (M := sphereSequence.{u, v}) (X := R.X) ≫ e.hom =
      (sphereSequence.{u, v} ◁ e.hom) ≫
        ModObj.smul (M := sphereSequence.{u, v}) (X := M.X) := by
  let R := reconstructedModule (toOperatorFunctor M)
  let e : R.X ≅ M.X := sequenceRecoveryIso M
  apply nativeDay_intertwining
    (P := sphereSequence.{u, v}) (Q := R.X) (Q' := M.X)
    (f := ModObj.smul (M := sphereSequence.{u, v}) (X := R.X))
    (g := ModObj.smul (M := sphereSequence.{u, v}) (X := M.X)) (m := e.hom)
  intro a n
  change pairAction R a n ≫ e.hom.natTrans.app (a ⊗ n) =
    (sphereSequence.{u, v}.functor.obj a ◁ e.hom.natTrans.app n) ≫ pairAction M a n
  exact moduleRecovery_pairSquare M a n

/-- The whole reconstructed module is isomorphic to the original module.
Its full action square follows from all original Day pair generators. -/
@[no_expose]
def moduleRecoveryIso
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) :
    reconstructedModule (toOperatorFunctor M) ≅ M := by
  let R := reconstructedModule (toOperatorFunctor M)
  let e : R.X ≅ M.X := sequenceRecoveryIso M
  let γR : sphereSequence.{u, v} ⊗ R.X ⟶ R.X :=
    ModObj.smul (M := sphereSequence.{u, v}) (X := R.X)
  let γM : sphereSequence.{u, v} ⊗ M.X ⟶ M.X :=
    ModObj.smul (M := sphereSequence.{u, v}) (X := M.X)
  have h : γR ≫ e.hom = (sphereSequence.{u, v} ◁ e.hom) ≫ γM := by
    exact moduleRecovery_action M
  letI : IsModHom sphereSequence.{u, v} e.hom := ⟨h⟩
  have hInv : γM ≫ e.inv = (sphereSequence.{u, v} ◁ e.inv) ≫ γR :=
    IsModHom.smul_hom (A := sphereSequence.{u, v}) (f := e.inv)
  exact
    { hom := Mod.Hom.mk' e.hom h
      inv := Mod.Hom.mk' e.inv hInv
      hom_inv_id := by
        apply Mod.hom_ext
        change e.hom ≫ e.inv = 𝟙 R.X
        exact e.hom_inv_id
      inv_hom_id := by
        apply Mod.hom_ext
        change e.inv ≫ e.hom = 𝟙 M.X
        exact e.inv_hom_id }

/-- The module comparison retains every entire original level component. -/
theorem moduleRecoveryIso_hom_component
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (n : I) :
    (moduleRecoveryIso M).hom.hom.natTrans.app n = 𝟙 (M.X.functor.obj n) := by
  change (sequenceRecoveryIso M).hom.natTrans.app n = 𝟙 (M.X.functor.obj n)
  exact sequenceRecoveryIso_hom_component M n

/-- The inverse module comparison retains every entire original level component. -/
theorem moduleRecoveryIso_inv_component
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (n : I) :
    (moduleRecoveryIso M).inv.hom.natTrans.app n = 𝟙 (M.X.functor.obj n) := by
  change (sequenceRecoveryIso M).inv.natTrans.app n = 𝟙 (M.X.functor.obj n)
  exact sequenceRecoveryIso_inv_component M n

end OriginalModuleRecovery

section OperatorComparison

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

/-- The whole reconstructed operator functor is isomorphic to the original
genuine functor. Full Hom naturality is the complete coend recovery theorem. -/
def operatorRecoveryIso
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :
    toOperatorFunctor (reconstructedModule F) ≅ F := by
  let A := toOperatorFunctor (reconstructedModule F)
  let q : ∀ n, A.toEnrichedFunctor.obj n ⟶ F.toEnrichedFunctor.obj n :=
    fun n => 𝟙 (F.toEnrichedFunctor.obj n)
  have hq : ∀ n k, MonoidalClosed.uncurry (A.toEnrichedFunctor.map n k) ≫ q k =
      (q n ⊗ₘ 𝟙 (n ⟶[PointedCGWH.{u, v}] k)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map n k) := by
    intro n k
    let X : PointedCGWH.{u, v} := F.toEnrichedFunctor.obj n
    let Y : PointedCGWH.{u, v} := F.toEnrichedFunctor.obj k
    let K : PointedCGWH.{u, v} := n ⟶[PointedCGWH.{u, v}] k
    let aMap : K ⟶ (ihom X).obj Y := A.toEnrichedFunctor.map n k
    let fMap : K ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map n k
    have hFull : aMap = fMap := by
      dsimp only [aMap, fMap, A]
      cases n
      cases k
      exact operatorHomMap_reconstructed F _ _
    have hRaw := congrArg (fun z : K ⟶ (ihom X).obj Y => MonoidalClosed.uncurry z) hFull
    change MonoidalClosed.uncurry aMap ≫ 𝟙 Y =
      (𝟙 X ⊗ₘ 𝟙 K) ≫ MonoidalClosed.uncurry fMap
    simpa only [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp] using hRaw
  let α : A ⟶ F := GradedNatTrans.unitOfComponents
    (F' := A.toEnrichedFunctor) (G' := F.toEnrichedFunctor) q hq
  let p : ∀ n, F.toEnrichedFunctor.obj n ⟶ A.toEnrichedFunctor.obj n :=
    fun n => 𝟙 (F.toEnrichedFunctor.obj n)
  have hp : ∀ n k, MonoidalClosed.uncurry (F.toEnrichedFunctor.map n k) ≫ p k =
      (p n ⊗ₘ 𝟙 (n ⟶[PointedCGWH.{u, v}] k)) ≫
        MonoidalClosed.uncurry (A.toEnrichedFunctor.map n k) := by
    intro n k
    let X : PointedCGWH.{u, v} := F.toEnrichedFunctor.obj n
    let Y : PointedCGWH.{u, v} := F.toEnrichedFunctor.obj k
    let K : PointedCGWH.{u, v} := n ⟶[PointedCGWH.{u, v}] k
    let aMap : K ⟶ (ihom X).obj Y := A.toEnrichedFunctor.map n k
    let fMap : K ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map n k
    have hFull : aMap = fMap := by
      dsimp only [aMap, fMap, A]
      cases n
      cases k
      exact operatorHomMap_reconstructed F _ _
    have hRaw := congrArg (fun z : K ⟶ (ihom X).obj Y => MonoidalClosed.uncurry z) hFull
    change MonoidalClosed.uncurry fMap ≫ 𝟙 Y =
      (𝟙 X ⊗ₘ 𝟙 K) ≫ MonoidalClosed.uncurry aMap
    simpa only [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp] using
      hRaw.symm
  let β : F ⟶ A := GradedNatTrans.unitOfComponents
    (F' := F.toEnrichedFunctor) (G' := A.toEnrichedFunctor) p hp
  have hα (n) : EnrichedFunctorCat.component α n = 𝟙 (F.toEnrichedFunctor.obj n) :=
    GradedNatTrans.unitOfComponents_component q hq n
  have hβ (n) : EnrichedFunctorCat.component β n = 𝟙 (F.toEnrichedFunctor.obj n) :=
    GradedNatTrans.unitOfComponents_component p hp n
  exact
    { hom := α
      inv := β
      hom_inv_id := by
        apply EnrichedFunctorCat.hom_ext
        intro n
        rw [EnrichedFunctorCat.component_comp, hα, hβ, EnrichedFunctorCat.component_id]
        change 𝟙 (F.toEnrichedFunctor.obj n) ≫ 𝟙 (F.toEnrichedFunctor.obj n) =
          𝟙 (F.toEnrichedFunctor.obj n)
        exact Category.id_comp _
      inv_hom_id := by
        apply EnrichedFunctorCat.hom_ext
        intro n
        rw [EnrichedFunctorCat.component_comp, hβ, hα, EnrichedFunctorCat.component_id]
        change 𝟙 (F.toEnrichedFunctor.obj n) ≫ 𝟙 (F.toEnrichedFunctor.obj n) =
          𝟙 (F.toEnrichedFunctor.obj n)
        exact Category.id_comp _ }

/-- Every actual operator comparison component is the complete level identity. -/
theorem operatorRecoveryIso_hom_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (n : SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (operatorRecoveryIso F).hom n =
      𝟙 (F.toEnrichedFunctor.obj n) := by
  dsimp only [operatorRecoveryIso, EnrichedFunctorCat.component]
  exact GradedNatTrans.unitOfComponents_component _ _ n

/-- Every actual inverse operator comparison component is the complete level identity. -/
theorem operatorRecoveryIso_inv_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (n : SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (operatorRecoveryIso F).inv n =
      𝟙 (F.toEnrichedFunctor.obj n) := by
  dsimp only [operatorRecoveryIso, EnrichedFunctorCat.component]
  exact GradedNatTrans.unitOfComponents_component _ _ n

/-- The module comparison is natural under every original module morphism. -/
def moduleRecoveryNatIso : moduleToOperator.{u, v} ⋙ operatorToModule.{u, v} ≅
    𝟭 (CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) :=
  NatIso.ofComponents moduleRecoveryIso (by
    intro M N f
    apply Mod.hom_ext
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext n
    change ((symmetricSequenceRestriction.{u, v}).map (toOperatorMorphism f)).natTrans.app n ≫
        (moduleRecoveryIso N).hom.hom.natTrans.app n =
      (moduleRecoveryIso M).hom.hom.natTrans.app n ≫ f.hom.natTrans.app n
    rw [moduleRecoveryIso_hom_component, moduleRecoveryIso_hom_component,
      symmetricSequenceRestriction_component, toOperatorMorphism_component]
    change f.hom.natTrans.app n ≫ 𝟙 (N.X.functor.obj n) =
      𝟙 (M.X.functor.obj n) ≫ f.hom.natTrans.app n
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The operator comparison is natural under every genuine full-Hom transformation. -/
def operatorRecoveryNatIso : operatorToModule.{u, v} ⋙ moduleToOperator.{u, v} ≅
    𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :=
  NatIso.ofComponents operatorRecoveryIso (by
    intro F G f
    apply EnrichedFunctorCat.hom_ext
    intro n
    change EnrichedFunctorCat.component
        (toOperatorMorphism (reconstructedModuleMap f) ≫ (operatorRecoveryIso G).hom) n =
      EnrichedFunctorCat.component ((operatorRecoveryIso F).hom ≫ f) n
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      operatorRecoveryIso_hom_component, operatorRecoveryIso_hom_component,
      toOperatorMorphism_component, reconstructedModuleMap_hom,
      symmetricSequenceRestriction_component]
    change EnrichedFunctorCat.component f n ≫ 𝟙 (G.toEnrichedFunctor.obj n) =
      𝟙 (F.toEnrichedFunctor.obj n) ≫ EnrichedFunctorCat.component f n
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The original sphere Day modules and the canonical operator enriched
functors are equivalent on complete objects, Hom maps and coefficient actions. -/
def moduleOperatorEquivalence :
    CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v} ≌
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} where
  functor := moduleToOperator
  inverse := operatorToModule
  unitIso := moduleRecoveryNatIso.symm
  counitIso := operatorRecoveryNatIso
  functor_unitIso_comp M := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    change EnrichedFunctorCat.component
        (toOperatorMorphism (moduleRecoveryIso M).inv ≫
          (operatorRecoveryIso (toOperatorFunctor M)).hom) n =
      EnrichedFunctorCat.component (𝟙 (toOperatorFunctor M)) n
    rw [EnrichedFunctorCat.component_comp, toOperatorMorphism_component,
      moduleRecoveryIso_inv_component, operatorRecoveryIso_hom_component,
      EnrichedFunctorCat.component_id]
    change 𝟙 (M.X.functor.obj (show I from n.asIndex)) ≫
        𝟙 (M.X.functor.obj (show I from n.asIndex)) =
      𝟙 (M.X.functor.obj (show I from n.asIndex))
    exact Category.id_comp _

/-- The equivalence unit retains the original complete module identities at every level. -/
theorem moduleOperatorEquivalence_unit_component
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) (n : I) :
    (moduleOperatorEquivalence.{u, v}.unitIso.hom.app M).hom.natTrans.app n =
      𝟙 (M.X.functor.obj n) := moduleRecoveryIso_inv_component M n

/-- The equivalence counit retains the original complete operator identities at every object. -/
theorem moduleOperatorEquivalence_counit_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v})
    (n : SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (moduleOperatorEquivalence.{u, v}.counitIso.hom.app F) n =
      𝟙 (F.toEnrichedFunctor.obj n) := operatorRecoveryIso_hom_component F n

/-- The complete operator morphism recovered through modules is conjugated by
the actual full-Hom comparison isomorphisms. -/
theorem moduleOperatorEquivalence_operator_map_inverse
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}} (f : F ⟶ G) :
    moduleToOperator.{u, v}.map (operatorToModule.{u, v}.map f) =
      (operatorRecoveryIso F).hom ≫ f ≫ (operatorRecoveryIso G).inv :=
  moduleOperatorEquivalence.{u, v}.fun_inv_map F G f

/-- Every original module morphism is recovered through operator functors by
the actual module comparison isomorphisms. -/
theorem moduleOperatorEquivalence_module_map_inverse
    {M N : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}}
    (f : M ⟶ N) :
    operatorToModule.{u, v}.map (moduleToOperator.{u, v}.map f) =
      (moduleRecoveryIso M).hom ≫ f ≫ (moduleRecoveryIso N).inv :=
  moduleOperatorEquivalence.{u, v}.inv_fun_map M N f

/-- The actual unit and counit satisfy the full operator triangle identity. -/
theorem moduleOperatorEquivalence_operator_triangle
    (M : CategoryTheory.Mod (C := SymmetricSequence.{u, v}) (SymmetricSequence.{u, v})
        sphereSequence.{u, v}) :
    moduleToOperator.{u, v}.map (moduleOperatorEquivalence.{u, v}.unitIso.hom.app M) ≫
        moduleOperatorEquivalence.{u, v}.counitIso.hom.app (toOperatorFunctor M) =
      𝟙 (toOperatorFunctor M) :=
  moduleOperatorEquivalence.{u, v}.functor_unit_comp M

/-- The actual unit and counit satisfy the full module triangle identity. -/
theorem moduleOperatorEquivalence_module_triangle
    (F : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :
    moduleOperatorEquivalence.{u, v}.unitIso.hom.app (reconstructedModule F) ≫
        operatorToModule.{u, v}.map (moduleOperatorEquivalence.{u, v}.counitIso.hom.app F) =
      𝟙 (reconstructedModule F) :=
  moduleOperatorEquivalence.{u, v}.unit_inverse_comp F

end OperatorComparison

end PointedCGWH.SymmetricModulePresentation
