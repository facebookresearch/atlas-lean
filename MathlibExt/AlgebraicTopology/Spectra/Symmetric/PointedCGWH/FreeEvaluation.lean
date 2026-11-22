/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.Basic
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeFreeSourceComparison
import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluationRelabeling

/-!
# Native free and evaluation operations for public symmetric spectra

Every public operation uses the genuine enriched free/evaluation factory.
Relabeling is the inverse mate of the actual restricted permutation map.
The source Day free objects remain available through their proved natural
isomorphisms; they do not supply a second public spectrum carrier.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricSpectrum

private abbrev I := Operad.SmallFinBijGroupoid

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj

/-- Native evaluation at the actual finite-bijection operator object. -/
def evaluation (n : I) : SymmetricSpectrum.{u, v} ⥤ PointedCGWH.{u, v} :=
  EnrichedFunctorCat.evaluation (symmetricOperatorObj.{u, v} n)

/-- The canonical native free spectrum at the actual operator object. -/
def freeAt (n : I) : PointedCGWH.{u, v} ⥤ SymmetricSpectrum.{u, v} :=
  EnrichedFunctorCat.Free.functor (symmetricOperatorObj.{u, v} n)

/-- The public free/evaluation adjunction is the original enriched factory value. -/
def freeAtEvaluationAdjunction (n : I) : freeAt.{u, v} n ⊣ evaluation n :=
  EnrichedFunctorCat.Free.adjunction (symmetricOperatorObj.{u, v} n)

/-- Evaluation keeps the literal original sequence level. -/
@[simp]
theorem evaluation_obj (n : I) (F : SymmetricSpectrum.{u, v}) :
    (evaluation n).obj F = F.X.functor.obj n := rfl

/-- Evaluation keeps the whole original level transformation. -/
@[simp]
theorem evaluation_map (n : I) {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G) :
    (evaluation n).map f = (hom f).natTrans.app n := (hom_app f n).symm

/-- Free values retain the entire native operator Hom, without choosing a point. -/
@[simp]
theorem freeAt_obj_level (r n : I) (M : PointedCGWH.{u, v}) :
    ((freeAt r).obj M).X.functor.obj n =
      M ⊗ (symmetricOperatorObj.{u, v} r ⟶[PointedCGWH.{u, v}]
        symmetricOperatorObj.{u, v} n) := rfl

/-- A free coefficient arrow tensors with the identity of the entire native Hom. -/
theorem freeAt_map_level (r n : I) {M N : PointedCGWH.{u, v}} (f : M ⟶ N) :
    (hom ((freeAt r).map f)).natTrans.app n =
      f ▷ (symmetricOperatorObj.{u, v} r ⟶[PointedCGWH.{u, v}]
        symmetricOperatorObj.{u, v} n) := by
  rw [hom_app]
  exact EnrichedFunctorCat.Free.coefficientMap_component _ f _

/-- Permutation relabeling uses the restricted native index action. -/
def evaluationRelabel {n k : I} (g : n ⟶ k) : evaluation.{u, v} n ⟶ evaluation k where
  app F := F.X.functor.map g
  naturality {F G} f := by
    rw [evaluation_map, evaluation_map]
    exact ((hom f).natTrans.naturality g).symm

/-- Every relabeling component is the original complete permutation map. -/
theorem evaluationRelabel_app {n k : I} (g : n ⟶ k) (F : SymmetricSpectrum.{u, v}) :
    (evaluationRelabel g).app F = F.X.functor.map g := rfl

/-- The complete identity index map acts identically on every evaluated spectrum. -/
@[simp]
theorem evaluationRelabel_id (n : I) :
    evaluationRelabel.{u, v} (𝟙 n) = 𝟙 (evaluation n) := by
  apply NatTrans.ext
  funext F
  exact F.X.functor.map_id n

/-- Both original permutation maps retain their ordinary composition order. -/
@[simp]
theorem evaluationRelabel_comp {n k l : I} (f : n ⟶ k) (g : k ⟶ l) :
    evaluationRelabel.{u, v} (f ≫ g) = evaluationRelabel f ≫ evaluationRelabel g := by
  apply NatTrans.ext
  funext F
  exact F.X.functor.map_comp f g

/-- The complete native free relabeling is the inverse mate of the original evaluation map. -/
def freeAtRelabel {n k : I} (g : n ⟶ k) : freeAt.{u, v} k ⟶ freeAt n :=
  (conjugateEquiv (freeAtEvaluationAdjunction n)
    (freeAtEvaluationAdjunction k)).symm (evaluationRelabel g)

/-- Native free spectra vary contravariantly by the mates of their actual evaluation maps. -/
def freeAtFunctor : Iᵒᵖ ⥤ (PointedCGWH.{u, v} ⥤ SymmetricSpectrum.{u, v}) where
  obj n := freeAt n.unop
  map {n k} g := freeAtRelabel g.unop
  map_id n := by
    unfold freeAtRelabel
    rw [unop_id, evaluationRelabel_id]
    exact conjugateEquiv_symm_id (freeAtEvaluationAdjunction n.unop)
  map_comp {n k l} f g := by
    unfold freeAtRelabel
    rw [unop_comp, evaluationRelabel_comp]
    exact (conjugateEquiv_symm_comp
      (freeAtEvaluationAdjunction l.unop) (freeAtEvaluationAdjunction k.unop)
      (freeAtEvaluationAdjunction n.unop)
      (evaluationRelabel g.unop) (evaluationRelabel f.unop)).symm

/-- Every complete map of the contravariant free family is the same original inverse mate. -/
theorem freeAtFunctor_map {n k : I} (g : n ⟶ k) :
    freeAtFunctor.{u, v}.map g.op = freeAtRelabel g := rfl

/-- The actual native free relabeling retains the complete original unit mate square. -/
theorem freeAtFunctor_map_unit {n k : I} (g : n ⟶ k) (M : PointedCGWH.{u, v}) :
    (freeAtEvaluationAdjunction n).unit.app M ≫ (evaluationRelabel g).app ((freeAt n).obj M) =
      (freeAtEvaluationAdjunction k).unit.app M ≫
        (evaluation k).map ((freeAtRelabel g).app M) :=
  unit_conjugateEquiv_symm (freeAtEvaluationAdjunction n)
    (freeAtEvaluationAdjunction k) (evaluationRelabel g) M

/-- Native relabeling retains every target's complete original counit mate square. -/
theorem freeAtFunctor_map_counit {n k : I} (g : n ⟶ k) (F : SymmetricSpectrum.{u, v}) :
    (freeAt k).map ((evaluationRelabel g).app F) ≫ (freeAtEvaluationAdjunction k).counit.app F =
      (freeAtRelabel g).app ((evaluation n).obj F) ≫
        (freeAtEvaluationAdjunction n).counit.app F :=
  conjugateEquiv_counit_symm (freeAtEvaluationAdjunction n)
    (freeAtEvaluationAdjunction k) (evaluationRelabel g) F

/-- The original entire HSS free functor has its canonical native image. -/
abbrev originalFreeComparison (n : I) :
    Mod.dayFreeAt sphereSequence.{u, v} n ⋙ ofModule.{u, v} ≅ freeAt n :=
  NativeOmegaPreparation.SymmetricNativeFree.operatorComparison n

/-- Native free objects have the complete original sphere-module presentation. -/
abbrev freeModuleComparison (n : I) :
    Mod.dayFreeAt sphereSequence.{u, v} n ≅ freeAt n ⋙ toModule.{u, v} :=
  NativeOmegaPreparation.SymmetricNativeFree.comparison n

/-- The entire native free/evaluation correspondence satisfies its free triangle. -/
theorem freeAt_triangle (n : I) (M : PointedCGWH.{u, v}) :
    (freeAt n).map ((freeAtEvaluationAdjunction n).unit.app M) ≫
      (freeAtEvaluationAdjunction n).counit.app ((freeAt n).obj M) = 𝟙 _ :=
  (freeAtEvaluationAdjunction n).left_triangle_components M

/-- The same chosen unit and counit satisfy the complete evaluation triangle. -/
theorem evaluation_triangle (n : I) (F : SymmetricSpectrum.{u, v}) :
    (freeAtEvaluationAdjunction n).unit.app ((evaluation n).obj F) ≫
      (evaluation n).map ((freeAtEvaluationAdjunction n).counit.app F) = 𝟙 _ :=
  (freeAtEvaluationAdjunction n).right_triangle_components F

end PointedCGWH.SymmetricSpectrum
