/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedRealizationMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroContraction
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge
public import Mathlib.Tactic.FinCases

/-!
# Original mapped-zero edge for mixed general Waldhausen functors

The original degree-one mapped-to-target zero diagram is constructed from
explicit general Waldhausen exactness, retaining the actual mapped chosen
source zero and selected target zero. All maps come from the original zero
object. Its actual nerve faces give the original mixed mapped-zero vertex
and target-zero vertex. A separate exact specialization checks the whole
original degree-one object and morphism recipe, without an assumption on
the main general declarations.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open scoped Simplicial Topology

universe uB vB uD vD

namespace CategoryTheory.Waldhausen.SConstruction

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategory D]
variable (F : B ⥤ D)

/-- The ORIGINAL mapped/target degree-one object recipe, with actual F(Bzero). -/
def mixedWaldhausenZeroEdgeDiagramObj (A : Ar 1) : D :=
  if A.left = (0 : Fin 2) then F.obj (0 : B) else (0 : D)

private theorem mixedWaldhausenZeroEdgeDiagramObj_isZero
    (hF : F.IsWaldhausenExact) (A : Ar 1) :
    IsZero (mixedWaldhausenZeroEdgeDiagramObj F A) := by
  unfold mixedWaldhausenZeroEdgeDiagramObj
  split_ifs with h
  · exact hF.map_isZero (isZero_zero B)
  · exact isZero_zero D

/-- The ORIGINAL degree-one zero diagram, using only the canonical target-zero morphisms. -/
def mixedWaldhausenZeroEdgeDiagram (hF : F.IsWaldhausenExact) : Ar 1 ⥤ D := by
  letI : HasZeroMorphisms D := (isZero_zero D).hasZeroMorphisms
  exact
    { obj := mixedWaldhausenZeroEdgeDiagramObj F
      map := fun _ => 0
      map_id := fun A => ((IsZero.iff_id_eq_zero _).mp
        (mixedWaldhausenZeroEdgeDiagramObj_isZero F hF A)).symm
      map_comp := fun _ _ => by simp only [comp_zero] }

/-- Every actual degree-one diagram object is zero, from the original structural hF. -/
theorem mixedWaldhausenZeroEdgeDiagram_isZero
    (hF : F.IsWaldhausenExact) (A : Ar 1) :
    IsZero ((mixedWaldhausenZeroEdgeDiagram F hF).obj A) :=
  mixedWaldhausenZeroEdgeDiagramObj_isZero F hF A

/-- The general pointwise-zero stage constructor earns the actual original degree-one stage. -/
theorem mixedWaldhausenZeroEdgeDiagram_isStage (hF : F.IsWaldhausenExact) :
    IsStage 1 (mixedWaldhausenZeroEdgeDiagram F hF) :=
  isStage_of_pointwise_zero D _ (mixedWaldhausenZeroEdgeDiagram_isZero F hF)

/-- The actual general degree-one stage with the original mapped/target object recipe. -/
def mixedWaldhausenZeroEdgeStage (hF : F.IsWaldhausenExact) : Stage D 1 :=
  ⟨mixedWaldhausenZeroEdgeDiagram F hF, mixedWaldhausenZeroEdgeDiagram_isStage F hF⟩

/-- The actual general weak degree-one stage. -/
def mixedWaldhausenZeroEdgeWeak (hF : F.IsWaldhausenExact) : StageWeakCategory D 1 :=
  ⟨mixedWaldhausenZeroEdgeStage F hF⟩

/-- The actual original diagonal simplex is the identity on this SAME weak stage. -/
def mixedWaldhausenZeroEdgeSimplex (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonal D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF))

/-- The actual source reindexing recovers hF of ORIGINAL source Stage-zero, in independent worlds. -/
theorem mixedWaldhausenZeroEdge_reindex_src (hF : F.IsWaldhausenExact) :
    (reindexStageWeak D (SimplexCategory.δ 1)).obj (mixedWaldhausenZeroEdgeWeak F hF) =
      (hF.mapStageWeak 0).obj (⟨stageZero B⟩ : StageWeakCategory B 0) := by
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply Functor.hext
  · intro A
    have hA := arZero_eq_diag A
    subst A
    change mixedWaldhausenZeroEdgeDiagramObj F
      ((indexFunctor (SimplexCategory.δ 1)).obj (diag (0 : Fin 1))) = F.obj (0 : B)
    have hIdx : ((indexFunctor (SimplexCategory.δ 1)).obj (diag (0 : Fin 1))).left =
        (0 : Fin 2) := by
      decide
    simp only [mixedWaldhausenZeroEdgeDiagramObj, hIdx, ite_true]
  · intro A A' f
    have hA := arZero_eq_diag A
    have hA' := arZero_eq_diag A'
    subst A
    subst A'
    apply heq_of_eq
    apply IsZero.eq_of_src
    exact mixedWaldhausenZeroEdgeDiagram_isZero F hF
      ((indexFunctor (SimplexCategory.δ 1)).obj (diag (0 : Fin 1)))

/-- The actual target reindexing recovers ORIGINAL target Stage-zero. -/
theorem mixedWaldhausenZeroEdge_reindex_tgt (hF : F.IsWaldhausenExact) :
    (reindexStageWeak D (SimplexCategory.δ 0)).obj (mixedWaldhausenZeroEdgeWeak F hF) =
      (⟨stageZero D⟩ : StageWeakCategory D 0) := by
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply Functor.hext
  · intro A
    have hA := arZero_eq_diag A
    subst A
    change mixedWaldhausenZeroEdgeDiagramObj F
      ((indexFunctor (SimplexCategory.δ 0)).obj (diag (0 : Fin 1))) = (0 : D)
    have hIdx : ¬ ((indexFunctor (SimplexCategory.δ 0)).obj
        (diag (0 : Fin 1))).left = (0 : Fin 2) := by
      decide
    simp only [mixedWaldhausenZeroEdgeDiagramObj, hIdx, ite_false]
  · intro A A' f
    have hA := arZero_eq_diag A
    have hA' := arZero_eq_diag A'
    subst A
    subst A'
    apply heq_of_eq
    apply IsZero.eq_of_src
    exact mixedWaldhausenZeroEdgeDiagram_isZero F hF
      ((indexFunctor (SimplexCategory.δ 0)).obj (diag (0 : Fin 1)))

private theorem mixedWaldhausenZeroEdge_inner_face
    (hF : F.IsWaldhausenExact) (i : Fin 2) :
    ((CategoryTheory.nerve (StageWeakCategory D 1)).map (SimplexCategory.δ i).op)
        (ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF))) =
      ComposableArrows.mk₀ (mixedWaldhausenZeroEdgeWeak F hF) := by
  apply ComposableArrows.ext₀
  fin_cases i <;> rfl

/-- The actual diagonal source face is SAME original hF-mapped Stage-zero vertex. -/
theorem mixedWaldhausenZeroEdge_diag_src (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonal D).δ 1 (mixedWaldhausenZeroEdgeSimplex F hF) =
      hF.stageWeakDiagonalMixedMappedZeroVertex := by
  change (stageWeakDiagonal D).map (SimplexCategory.δ 1).op
    (mixedWaldhausenZeroEdgeSimplex F hF) = _
  have hMap : (stageWeakDiagonal D).map (SimplexCategory.δ 1).op
      (mixedWaldhausenZeroEdgeSimplex F hF) =
      (CategoryTheory.nerveMap (reindexStageWeak D (SimplexCategory.δ 1))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory D 1)).map (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF)))) := rfl
  rw [hMap, mixedWaldhausenZeroEdge_inner_face, CategoryTheory.nerveMap_app_mk₀,
    mixedWaldhausenZeroEdge_reindex_src]
  exact (Functor.IsWaldhausenExact.stageWeakDiagonalMixedMappedZeroVertex_eq hF).symm

/-- The actual diagonal target face is SAME original selected D-zero vertex. -/
theorem mixedWaldhausenZeroEdge_diag_tgt (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonal D).δ 0 (mixedWaldhausenZeroEdgeSimplex F hF) =
      stageWeakDiagonalZeroVertex D := by
  change (stageWeakDiagonal D).map (SimplexCategory.δ 0).op
    (mixedWaldhausenZeroEdgeSimplex F hF) = _
  have hMap : (stageWeakDiagonal D).map (SimplexCategory.δ 0).op
      (mixedWaldhausenZeroEdgeSimplex F hF) =
      (CategoryTheory.nerveMap (reindexStageWeak D (SimplexCategory.δ 0))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory D 1)).map (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF)))) := rfl
  rw [hMap, mixedWaldhausenZeroEdge_inner_face, CategoryTheory.nerveMap_app_mk₀,
    mixedWaldhausenZeroEdge_reindex_tgt]
  rfl

/-- The original mapped-to-target zero edge, now earned for arbitrary mixed Waldhausen functors. -/
def stageWeakDiagonalMixedZeroEdge (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonal D).Edge hF.stageWeakDiagonalMixedMappedZeroVertex
      (stageWeakDiagonalZeroVertex D) :=
  SSet.Edge.ofEq (SSet.Edge.mk' (mixedWaldhausenZeroEdgeSimplex F hF))
    (mixedWaldhausenZeroEdge_diag_src F hF) (mixedWaldhausenZeroEdge_diag_tgt F hF)

private theorem originalMixedZeroEdgeValueComputed (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonalMixedZeroEdge F hF).edge =
      ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF)) := rfl

/-- The whole actual edge retains the ORIGINAL identity-simplex recipe. -/
theorem stageWeakDiagonalMixedZeroEdge_edge (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonalMixedZeroEdge F hF).edge =
      ComposableArrows.mk₁ (𝟙 (mixedWaldhausenZeroEdgeWeak F hF)) :=
  originalMixedZeroEdgeValueComputed F hF

private theorem originalMixedZeroEdgeOfEqValue
    {X : SSet.{max uB vB}} {a b a' b' : X.obj (op ⦋0⦌)}
    (e : X.Edge a b) (ha : a = a') (hb : b = b') :
    (e.ofEq ha hb).edge = e.edge := by
  cases ha
  cases hb
  rfl

end CategoryTheory.Waldhausen.SConstruction

namespace CategoryTheory.Waldhausen.SConstruction

variable (B : Type uB) [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasBinaryBiproducts B] [ExactCategory B]
variable (D : Type uD) [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : B ⥤ D) [F.Additive] [Functor.IsExact F]

omit [Functor.IsExact F] in
/-- Under the separately stated exact specialization, the WHOLE general
degree-one object/morphism diagram is the unchanged ORIGINAL LevelZeroEdge recipe. -/
theorem mixedWaldhausenZeroEdgeDiagram_exactRecipe
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    mixedWaldhausenZeroEdgeDiagram F hF = levelZeroEdgeDiagram B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  apply Functor.hext
  · intro A
    rfl
  · intro A A' f
    apply heq_of_eq
    exact (mixedWaldhausenZeroEdgeDiagram_isZero F hF A).eq_of_src _ _

omit [Functor.IsExact F] in
/-- The actual weak stage itself agrees with the ORIGINAL exact recipe,
using whole diagram equality and only proof irrelevance of the stage predicate. -/
theorem mixedWaldhausenZeroEdgeWeak_exactRecipe
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    mixedWaldhausenZeroEdgeWeak F hF = levelZeroEdgeWeak B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  exact mixedWaldhausenZeroEdgeDiagram_exactRecipe B D F hF

/-- The general actual mapped Stage-zero vertex agrees with the ORIGINAL exact vertex recipe. -/
theorem mixedWaldhausenZeroEdgeMappedVertex_exactRecipe
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.stageWeakDiagonalMixedMappedZeroVertex = levelZeroEdgeMappedVertex B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  rw [Functor.IsWaldhausenExact.stageWeakDiagonalMixedMappedZeroVertex_eq]
  apply ComposableArrows.ext₀
  apply WideSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply Functor.hext
  · intro A
    rfl
  · intro A A' f
    rfl

/-- The complete general edge agrees with the ORIGINAL exact mapped-to-target
edge after only its earned actual mapped-vertex cast; no reverse connector is selected. -/
theorem stageWeakDiagonalMixedZeroEdge_exactRecipe
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    (stageWeakDiagonalMixedZeroEdge F hF).ofEq
      (mixedWaldhausenZeroEdgeMappedVertex_exactRecipe B D F hF) rfl =
      stageWeakDiagonalLevelZeroEdge B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  apply SSet.Edge.ext
  rw [originalMixedZeroEdgeOfEqValue.{uD, vD}, stageWeakDiagonalMixedZeroEdge_edge,
    stageWeakDiagonalLevelZeroEdge_edge]
  exact congrArg (fun T : StageWeakCategory D 1 => ComposableArrows.mk₁ (𝟙 T))
    (mixedWaldhausenZeroEdgeWeak_exactRecipe B D F hF)

end CategoryTheory.Waldhausen.SConstruction

end

noncomputable section

open CategoryTheory Limits

universe uWeakViewB vWeakViewB uWeakViewD vWeakViewD

namespace CategoryTheory.Waldhausen.SConstruction

variable {B : Type uWeakViewB} [Category.{vWeakViewB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uWeakViewD} [Category.{vWeakViewD} D] [HasZeroObject D] [WaldhausenCategory D]
variable (F : B ⥤ D)

private theorem originalMixedZeroWeakDiagramValueComputed (hF : F.IsWaldhausenExact) :
    (mixedWaldhausenZeroEdgeWeak F hF).obj.obj = mixedWaldhausenZeroEdgeDiagram F hF := by
  rfl

/-- The whole diagram beneath the SAME original weak-stage object is the
SAME original mapped-to-target degree1 diagram, with all object/Hom roles retained. -/
theorem mixedWaldhausenZeroEdgeWeak_diagram (hF : F.IsWaldhausenExact) :
    (mixedWaldhausenZeroEdgeWeak F hF).obj.obj = mixedWaldhausenZeroEdgeDiagram F hF :=
  originalMixedZeroWeakDiagramValueComputed F hF

end CategoryTheory.Waldhausen.SConstruction

end

namespace CategoryTheory.Waldhausen.SConstruction

open CategoryTheory Limits ZeroObject

universe uEdgeValueB vEdgeValueB uEdgeValueD vEdgeValueD

variable {B : Type uEdgeValueB} [Category.{vEdgeValueB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uEdgeValueD} [Category.{vEdgeValueD} D] [HasZeroObject D] [WaldhausenCategory D]
variable (F : B ⥤ D)

omit [WaldhausenCategory B] [WaldhausenCategory D] in
private theorem originalMixedZeroObjectRecipeValueComputed (A : Ar 1) :
    mixedWaldhausenZeroEdgeDiagramObj F A =
      if A.left = (0 : Fin 2) then F.obj (0 : B) else (0 : D) := by
  rfl

omit [WaldhausenCategory B] [WaldhausenCategory D] in
/-- The actual original mapped-to-target object recipe keeps F(Bzero)
on the left-zero branch and the original selected target zero otherwise. -/
theorem mixedWaldhausenZeroEdgeDiagramObj_apply (A : Ar 1) :
    mixedWaldhausenZeroEdgeDiagramObj F A =
      if A.left = (0 : Fin 2) then F.obj (0 : B) else (0 : D) :=
  originalMixedZeroObjectRecipeValueComputed F A

private theorem originalMixedZeroDiagramObjectValueComputed
    (hF : F.IsWaldhausenExact) (A : Ar 1) :
    (mixedWaldhausenZeroEdgeDiagram F hF).obj A = mixedWaldhausenZeroEdgeDiagramObj F A := by
  rfl

/-- Every object of the original exact mapped-zero diagram is its same
original two-branch object recipe, without a changed zero-object choice. -/
theorem mixedWaldhausenZeroEdgeDiagram_obj (hF : F.IsWaldhausenExact) (A : Ar 1) :
    (mixedWaldhausenZeroEdgeDiagram F hF).obj A = mixedWaldhausenZeroEdgeDiagramObj F A :=
  originalMixedZeroDiagramObjectValueComputed F hF A

private theorem originalMixedZeroDiagramMapValueComputed
    (hF : F.IsWaldhausenExact) {A A' : Ar 1} (f : A ⟶ A') :
    letI : HasZeroMorphisms D := (isZero_zero D).hasZeroMorphisms;
    (mixedWaldhausenZeroEdgeDiagram F hF).map f = 0 := by
  rfl

/-- Every morphism of the original mapped-zero diagram is the same
canonical zero morphism from the original selected target-zero structure. -/
theorem mixedWaldhausenZeroEdgeDiagram_map
    (hF : F.IsWaldhausenExact) {A A' : Ar 1} (f : A ⟶ A') :
    letI : HasZeroMorphisms D := (isZero_zero D).hasZeroMorphisms;
    (mixedWaldhausenZeroEdgeDiagram F hF).map f = 0 :=
  originalMixedZeroDiagramMapValueComputed F hF f

end CategoryTheory.Waldhausen.SConstruction
