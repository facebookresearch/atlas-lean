/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Equivalence
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMap
public import MathlibExt.KTheory.Waldhausen.K0.Functor
public import Mathlib.CategoryTheory.Conj

/-!
# Exact-functor naturality of the combinatorial weak-diagonal K-zero comparison

For a same-universe additive exact functor `F : C ⥤ D`, the induced map of
weak-stage diagonals gives a map between their based combinatorial fundamental
groups.  Since the mapped zero vertex need not be the selected target zero
vertex definitionally, the map first uses the equality from
`stageWeakDiagonalMap_zeroVertex`, then conjugates by the mapped-zero edge.

The canonical object generator maps to the explicitly conjugated mapped
object edge.  After applying the K-zero decode functor, the connector cancels
only because `Multiplicative (K₀ D)` is commutative.  The resulting decode
map agrees with `WaldhausenKTheory.K0.map F` on every fundamental-group
element, by induction over the existing object-generator closure theorem.

This module does not assert that the connector is an identity, that the
unbased fundamental-groupoid map preserves the chosen basepoint strictly, or
that these maps assemble into a continuous map or natural isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

/-- A conjugated endomorphism has the same K-zero value as its middle
endomorphism.  The proof commutes the middle value past the connector only in
the commutative single-object group `Multiplicative (K₀ E)`. -/
private theorem stageWeakDiagonalK0Functor_map_conj
    (E : Type u) [Category.{v} E] [Limits.HasZeroObject E]
    [WaldhausenCategoryWithoutGluing E]
    {x y : (stageWeakDiagonal E).obj (op ⦋0⦌)}
    (p : SSet.FundamentalGroupoid.mk x ≅
      SSet.FundamentalGroupoid.mk y)
    (h : SSet.FundamentalGroupoid.mk x ⟶
      SSet.FundamentalGroupoid.mk x) :
    (stageWeakDiagonalK0Functor E).map (p.inv ≫ h ≫ p.hom) =
      (stageWeakDiagonalK0Functor E).map h := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [SingleObj.comp_as_mul]
  let qh : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map p.hom
  let qi : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map p.inv
  let a : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map h
  change (qh * a) * qi = a
  have hpCat :
      (stageWeakDiagonalK0Functor E).map p.inv ≫
          (stageWeakDiagonalK0Functor E).map p.hom =
        𝟙 _ := by
    rw [← Functor.map_comp, p.inv_hom_id, Functor.map_id]
  have hp : qh * qi = 1 := by
    dsimp only [qh, qi]
    simpa only [SingleObj.comp_as_mul, SingleObj.id_as_one] using hpCat
  calc
    _ = (qh * qi) * a := by ac_rfl
    _ = _ := by rw [hp, one_mul]

section SameUniverseNaturality

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

set_option backward.isDefEq.respectTransparency false in
/-- Underlying degree-one simplex of a mapped object edge.  This is the
load-bearing use of `stageWeakDiagonalMap_app_mk₁`. -/
private theorem stageWeakDiagonalMappedObjectEdge_edge (X : C) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((stageWeakDiagonalObjectEdge C X).map
        (stageWeakDiagonalMap C D F)).edge =
        ComposableArrows.mk₁ (𝟙 ((mapStageWeak C D F 1).obj
          (stageOneWeakObj C X)))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [SSet.Edge.map_edge, stageWeakDiagonalObjectEdge_edge]
  convert stageWeakDiagonalMap_app_mk₁ C D F
    (𝟙 (stageOneWeakObj C X)) using 1
  simp only [Functor.map_id]

/-- The K-zero functor sends the mapped object edge to the class of
`F.obj X`. -/
private theorem stageWeakDiagonalK0Functor_map_mappedObjectEdge (X : C) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalK0Functor D).map
        (SSet.FundamentalGroupoid.homMk
          ((stageWeakDiagonalObjectEdge C X).map
            (stageWeakDiagonalMap C D F))) =
        Multiplicative.ofAdd (WaldhausenKTheory.K0.mk (F.obj X))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [stageWeakDiagonalK0Functor_map_homMk]
  apply Multiplicative.ofAdd.injective
  rw [stageWeakDiagonalMappedObjectEdge_edge]
  exact congrArg WaldhausenKTheory.K0.mk
    (stageOneEval_obj D (F.obj X))

set_option backward.isDefEq.respectTransparency false in
/-- The induced fundamental-groupoid functor maps the fundamental morphism of
an object edge to that of the mapped object edge. -/
private theorem stageWeakDiagonalMapFundamental_objectEdge (X : C) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (SSet.mapFundamentalGroupoid (stageWeakDiagonalMap C D F)).map
          (SSet.FundamentalGroupoid.homMk
            (stageWeakDiagonalObjectEdge C X)) =
        SSet.FundamentalGroupoid.homMk
          ((stageWeakDiagonalObjectEdge C X).map
            (stageWeakDiagonalMap C D F))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact SSet.mapFundamentalGroupoid_map_homMk
    (stageWeakDiagonalMap C D F) (stageWeakDiagonalObjectEdge C X)

/-- Basepoint change from the mapped source zero vertex to the selected
target zero vertex.  Its first factor is equality transport to the named
mapped-zero vertex; its second factor is the mapped-zero edge. -/
noncomputable def stageWeakDiagonalFundamentalBasepointIso :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      SSet.FundamentalGroupoid.mk
          ((stageWeakDiagonalMap C D F).app (op ⦋0⦌)
            (stageWeakDiagonalZeroVertex C)) ≅
        SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex D)) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact eqToIso (congrArg SSet.FundamentalGroupoid.mk
      (stageWeakDiagonalMap_zeroVertex C D F)) ≪≫
    asIso (SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalLevelZeroEdge C D F))

/-- Based combinatorial fundamental-group map induced by an additive exact
functor, with explicit basepoint change along the mapped-zero edge. -/
noncomputable def stageWeakDiagonalFundamentalMap :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalFundamentalGroup C →*
        stageWeakDiagonalFundamentalGroup D) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact
    (stageWeakDiagonalFundamentalBasepointIso C D F).conj.toMonoidHom.comp
      ((SSet.mapFundamentalGroupoid
        (stageWeakDiagonalMap C D F)).mapEnd
          (SSet.FundamentalGroupoid.mk
            (stageWeakDiagonalZeroVertex C)))

/-- The based map sends an object generator to the mapped object edge
conjugated by the explicit mapped-zero-to-target-zero connector. -/
theorem stageWeakDiagonalFundamentalMap_objectGenerator (X : C) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalFundamentalMap C D F
          (stageWeakDiagonalObjectGenerator C X) =
        End.of ((stageWeakDiagonalFundamentalBasepointIso C D F).inv ≫
          SSet.FundamentalGroupoid.homMk
            ((stageWeakDiagonalObjectEdge C X).map
              (stageWeakDiagonalMap C D F)) ≫
          (stageWeakDiagonalFundamentalBasepointIso C D F).hom)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  simp only [stageWeakDiagonalFundamentalMap,
    stageWeakDiagonalObjectGenerator]
  change (stageWeakDiagonalFundamentalBasepointIso C D F).conj
      (End.of ((SSet.mapFundamentalGroupoid
        (stageWeakDiagonalMap C D F)).map
          (SSet.FundamentalGroupoid.homMk
            (stageWeakDiagonalObjectEdge C X)))) = _
  calc
    _ = (stageWeakDiagonalFundamentalBasepointIso C D F).conj
        (End.of (SSet.FundamentalGroupoid.homMk
          ((stageWeakDiagonalObjectEdge C X).map
            (stageWeakDiagonalMap C D F)))) :=
      congrArg (fun z =>
        (stageWeakDiagonalFundamentalBasepointIso C D F).conj (End.of z))
        (stageWeakDiagonalMapFundamental_objectEdge C D F X)
    _ = _ := by
      apply End.ext
      exact CategoryTheory.Iso.conj_apply_asHom _ _

/-- Naturality on one object generator.  Connector cancellation happens in
the K-zero target, after the explicit conjugation formula above. -/
private theorem
    stageWeakDiagonalFundamentalToK0_naturality_objectGenerator (X : C) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalFundamentalToK0 D
          (stageWeakDiagonalFundamentalMap C D F
            (stageWeakDiagonalObjectGenerator C X)) =
        Multiplicative.ofAdd (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd (stageWeakDiagonalFundamentalToK0 C
            (stageWeakDiagonalObjectGenerator C X))))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [stageWeakDiagonalFundamentalMap_objectGenerator]
  change (stageWeakDiagonalK0Functor D).map
      ((stageWeakDiagonalFundamentalBasepointIso C D F).inv ≫
        SSet.FundamentalGroupoid.homMk
          ((stageWeakDiagonalObjectEdge C X).map
            (stageWeakDiagonalMap C D F)) ≫
        (stageWeakDiagonalFundamentalBasepointIso C D F).hom) = _
  rw [stageWeakDiagonalK0Functor_map_conj,
    stageWeakDiagonalK0Functor_map_mappedObjectEdge,
    stageWeakDiagonalFundamentalToK0_objectGenerator]
  change Multiplicative.ofAdd (WaldhausenKTheory.K0.mk (F.obj X)) =
    Multiplicative.ofAdd
      (WaldhausenKTheory.K0.map F (WaldhausenKTheory.K0.mk X))
  rw [WaldhausenKTheory.K0.map_mk]

/-- K-zero decode is natural under a same-universe additive exact functor. -/
theorem stageWeakDiagonalFundamentalToK0_naturality
    (g : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalFundamentalGroup C)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalFundamentalToK0 D
          (stageWeakDiagonalFundamentalMap C D F g) =
        Multiplicative.ofAdd (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd
            (stageWeakDiagonalFundamentalToK0 C g)))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let lhs : stageWeakDiagonalFundamentalGroup C →*
      Multiplicative (WaldhausenKTheory.K0 D) :=
    (stageWeakDiagonalFundamentalToK0 D).comp
      (stageWeakDiagonalFundamentalMap C D F)
  let rhs : stageWeakDiagonalFundamentalGroup C →*
      Multiplicative (WaldhausenKTheory.K0 D) :=
    (AddMonoidHom.toMultiplicative
      (WaldhausenKTheory.K0.map F)).comp
        (stageWeakDiagonalFundamentalToK0 C)
  change lhs g = rhs g
  have hg := stageWeakDiagonalFundamentalGroup_mem_objectGenerators C g
  refine Subgroup.closure_induction
    (p := fun z _ => lhs z = rhs z) ?_ ?_ ?_ ?_ hg
  · intro z hz
    obtain ⟨X, rfl⟩ := hz
    change stageWeakDiagonalFundamentalToK0 D
        (stageWeakDiagonalFundamentalMap C D F
          (stageWeakDiagonalObjectGenerator C X)) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.map F
        (Multiplicative.toAdd (stageWeakDiagonalFundamentalToK0 C
          (stageWeakDiagonalObjectGenerator C X))))
    exact
      stageWeakDiagonalFundamentalToK0_naturality_objectGenerator C D F X
  · simp only [map_one]
  · intro x y hx hy hxEq hyEq
    simp only [map_mul, hxEq, hyEq]
  · intro x hx hxEq
    simp only [map_inv, hxEq]

/-- The decode-forward multiplicative equivalence obeys the same exact-functor
naturality formula. -/
theorem stageWeakDiagonalFundamentalK0MulEquiv_naturality
    (g : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalFundamentalGroup C)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalFundamentalK0MulEquiv D
          (stageWeakDiagonalFundamentalMap C D F g) =
        Multiplicative.ofAdd (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd
            (stageWeakDiagonalFundamentalK0MulEquiv C g)))) := by
  simpa only [stageWeakDiagonalFundamentalK0MulEquiv_apply] using
    stageWeakDiagonalFundamentalToK0_naturality C D F g

end SameUniverseNaturality

end CategoryTheory.Waldhausen.SConstruction

end
