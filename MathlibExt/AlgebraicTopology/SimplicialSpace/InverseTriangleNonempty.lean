/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InverseTriangleData
import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleShearFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleTargetReedyFibration

/-!
# Original inverse-triangle spaces and intrinsic invertibility

The original fixed-first and fixed-last middle maps are pullbacks of the
actual Reedy triangle shears. The paired space keeps its two inverse
candidates independent. Its semantic recognition uses the existing original
Z(3) theorem and the same chosen pullbacks.

Source: Rezk (2001), Sections 5.5 and 11.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InverseTriangle

open SegalHomotopy

variable (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
  (f : (mappingFibre W x y) _⦋0⦌)

/-- The original fixed-first middle map is the pullback of the middle-first shear. -/
theorem rightMiddle_isPullback :
    IsPullback (FixedEdgeTriangle.rightTriangleProjection W x y f) (rightMiddle W x y f)
      (triangleShear W x y x)
      (prod.lift (𝟙 (mappingFibre W x x))
        (mappingFibre.snd W x x ≫ SSet.yonedaEquiv.symm f)) := by
  let r := FixedEdgeTriangle.rightTriangleProjection W x y f
  let c := FixedEdgeTriangle.rightProjection W x y f
  have hfix : r ≫ triangleComparison W x y x ≫ prod.fst =
      c ≫ mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm f := by
    have h := congrArg (fun k => k ≫ prod.fst) (FixedEdgeTriangle.rightGeometry W x y f).2.1
    simpa only [Category.assoc, FixedEdgeTriangle.rightPair, prod.lift_fst] using h
  have hvar : r ≫ triangleComparison W x y x ≫ prod.snd = c := by
    have h := congrArg (fun k => k ≫ prod.snd) (FixedEdgeTriangle.rightGeometry W x y f).2.1
    simpa only [Category.assoc, FixedEdgeTriangle.rightPair, prod.lift_snd,
      Category.comp_id] using h
  have hw : r ≫ triangleShear W x y x = rightMiddle W x y f ≫
      prod.lift (𝟙 (mappingFibre W x x))
        (mappingFibre.snd W x x ≫ SSet.yonedaEquiv.symm f) := by
    apply prod.hom_ext
    · simp only [Category.assoc, triangleShear_middle, prod.lift_fst,
        Category.comp_id, rightMiddle]
      rfl
    · simp only [Category.assoc, triangleShear_first, prod.lift_snd]
      rw [hfix]
      exact congrArg (fun k => k ≫ SSet.yonedaEquiv.symm f)
        (SSet.stdSimplex.isTerminalObj₀.hom_ext
          (c ≫ mappingFibre.snd W y x) (rightMiddle W x y f ≫ mappingFibre.snd W x x))
  refine IsPullback.mk' hw ?_ ?_
  · intro T a b hab _
    apply pullback.hom_ext
    · exact hab
    · change a ≫ c = b ≫ c
      rw [← hvar]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ triangleComparison W x y x ≫ prod.snd) hab
  · intro T a b hab
    let d := a ≫ triangleComparison W x y x ≫ prod.snd
    have hh : a ≫ triangleComparison W x y x ≫ prod.fst =
        b ≫ mappingFibre.snd W x x ≫ SSet.yonedaEquiv.symm f := by
      have h := congrArg (fun k => k ≫ prod.snd) hab
      simpa only [Category.assoc, triangleShear_first, prod.lift_snd] using h
    have hd : a ≫ triangleComparison W x y x = d ≫ FixedEdgeTriangle.rightPair W x y f := by
      apply prod.hom_ext
      · simp only [Category.assoc, FixedEdgeTriangle.rightPair, prod.lift_fst]
        rw [hh]
        exact congrArg (fun k => k ≫ SSet.yonedaEquiv.symm f)
          (SSet.stdSimplex.isTerminalObj₀.hom_ext
            (b ≫ mappingFibre.snd W x x) (d ≫ mappingFibre.snd W y x))
      · simp only [Category.assoc, FixedEdgeTriangle.rightPair, prod.lift_snd,
          Category.comp_id]
        rfl
    let l : T ⟶ FixedEdgeTriangle.rightTriangle W x y f := pullback.lift a d hd
    have hl : l ≫ r = a := pullback.lift_fst _ _ _
    refine ⟨l, hl, ?_⟩
    change l ≫ (r ≫ triangleMiddle W x y x) = b
    rw [← Category.assoc, hl]
    have h := congrArg (fun k => k ≫ prod.fst) hab
    simpa only [Category.assoc, triangleShear_middle, prod.lift_fst,
      Category.comp_id] using h

/-- The original fixed-last middle map is the pullback of the middle-last shear. -/
theorem leftMiddle_isPullback :
    IsPullback (FixedEdgeTriangle.leftTriangleProjection W x y f) (leftMiddle W x y f)
      (triangleTargetShear W y x y)
      (prod.lift (𝟙 (mappingFibre W y y))
        (mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm f)) := by
  let r := FixedEdgeTriangle.leftTriangleProjection W x y f
  let c := FixedEdgeTriangle.leftProjection W x y f
  have hfix : r ≫ triangleComparison W y x y ≫ prod.snd =
      c ≫ mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm f := by
    have h := congrArg (fun k => k ≫ prod.snd) (FixedEdgeTriangle.leftGeometry W x y f).2.1
    simpa only [Category.assoc, FixedEdgeTriangle.leftPair, prod.lift_snd] using h
  have hvar : r ≫ triangleComparison W y x y ≫ prod.fst = c := by
    have h := congrArg (fun k => k ≫ prod.fst) (FixedEdgeTriangle.leftGeometry W x y f).2.1
    simpa only [Category.assoc, FixedEdgeTriangle.leftPair, prod.lift_fst,
      Category.comp_id] using h
  have hw : r ≫ triangleTargetShear W y x y = leftMiddle W x y f ≫
      prod.lift (𝟙 (mappingFibre W y y))
        (mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm f) := by
    apply prod.hom_ext
    · simp only [Category.assoc, triangleTargetShear_fst, prod.lift_fst,
        Category.comp_id, leftMiddle]
      rfl
    · simp only [Category.assoc, triangleTargetShear_snd, prod.lift_snd]
      rw [hfix]
      exact congrArg (fun k => k ≫ SSet.yonedaEquiv.symm f)
        (SSet.stdSimplex.isTerminalObj₀.hom_ext
          (c ≫ mappingFibre.snd W y x) (leftMiddle W x y f ≫ mappingFibre.snd W y y))
  refine IsPullback.mk' hw ?_ ?_
  · intro T a b hab _
    apply pullback.hom_ext
    · exact hab
    · change a ≫ c = b ≫ c
      rw [← hvar]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ triangleComparison W y x y ≫ prod.fst) hab
  · intro T a b hab
    let d := a ≫ triangleComparison W y x y ≫ prod.fst
    have hh : a ≫ triangleComparison W y x y ≫ prod.snd =
        b ≫ mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm f := by
      have h := congrArg (fun k => k ≫ prod.snd) hab
      simpa only [Category.assoc, triangleTargetShear_snd, prod.lift_snd] using h
    have hd : a ≫ triangleComparison W y x y = d ≫ FixedEdgeTriangle.leftPair W x y f := by
      apply prod.hom_ext
      · simp only [Category.assoc, FixedEdgeTriangle.leftPair, prod.lift_fst,
          Category.comp_id]
        rfl
      · simp only [Category.assoc, FixedEdgeTriangle.leftPair, prod.lift_snd]
        rw [hh]
        exact congrArg (fun k => k ≫ SSet.yonedaEquiv.symm f)
          (SSet.stdSimplex.isTerminalObj₀.hom_ext
            (b ≫ mappingFibre.snd W y y) (d ≫ mappingFibre.snd W y x))
    let l : T ⟶ FixedEdgeTriangle.leftTriangle W x y f := pullback.lift a d hd
    have hl : l ≫ r = a := pullback.lift_fst _ _ _
    refine ⟨l, hl, ?_⟩
    change l ≫ (r ≫ triangleMiddle W y x y) = b
    rw [← Category.assoc, hl]
    have h := congrArg (fun k => k ≫ prod.fst) hab
    simpa only [Category.assoc, triangleTargetShear_fst, prod.lift_fst,
      Category.comp_id] using h

/-- Actual Reedy fibrancy makes the original right middle map a scalar Kan fibration. -/
theorem rightMiddle_fibration :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → Fibration (rightMiddle W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  exact (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
    (rightMiddle_isPullback W x y f)
    ((fibration_iff _).mp (ReedyModel.triangleShear_fibration W x y x hW)))

/-- Actual Reedy fibrancy makes the original left middle map a scalar Kan fibration. -/
theorem leftMiddle_fibration :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → Fibration (leftMiddle W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  exact (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
    (leftMiddle_isPullback W x y f)
    ((fibration_iff _).mp (ReedyModel.triangleTargetShear_fibration W y x y hW)))

/-- Select the public isomorphism dictionary of the actual Kan horn-RLP class. -/
private lemma scalarFibrations_respectsIso : (fibrations SSet.{u}).RespectsIso := by
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  exact MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ g hg => by
    let _ : IsIso g := hg
    exact MorphismProperty.rlp_of_isIso SSet.modelCategoryQuillen.J g

/-- The same chosen right inverse space is Kan under RF alone. -/
theorem rightSpace_kanComplex :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.KanComplex (rightSpace W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  let _ : (fibrations SSet.{u}).RespectsIso := scalarFibrations_respectsIso
  let _ : Fibration (rightMiddle W x y f) := rightMiddle_fibration W x y f hW
  let _ : Fibration (rightToPoint W x y f) :=
    (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
      (right_isPullback W x y f) ((fibration_iff _).mp inferInstance))
  let _ : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      SSet.stdSimplex.isTerminalObj₀).mpr (by infer_instance)
  exact isFibrant_of_fibration (rightToPoint W x y f)

/-- The same chosen left inverse space is Kan under RF alone. -/
theorem leftSpace_kanComplex :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.KanComplex (leftSpace W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  let _ : (fibrations SSet.{u}).RespectsIso := scalarFibrations_respectsIso
  let _ : Fibration (leftMiddle W x y f) := leftMiddle_fibration W x y f hW
  let _ : Fibration (leftToPoint W x y f) :=
    (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
      (left_isPullback W x y f) ((fibration_iff _).mp inferInstance))
  let _ : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      SSet.stdSimplex.isTerminalObj₀).mpr (by infer_instance)
  exact isFibrant_of_fibration (leftToPoint W x y f)

/-- The original ordered product of both independent inverse spaces is Kan under RF alone. -/
theorem pairedSpace_kanComplex :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.KanComplex (pairedSpace W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  intro hW
  let _ : IsFibrant (leftSpace W x y f) := leftSpace_kanComplex W x y f hW
  let _ : IsFibrant (rightSpace W x y f) := rightSpace_kanComplex W x y f hW
  exact isFibrant_of_fibration (prod.fst : pairedSpace W x y f ⟶ leftSpace W x y f)

/-- The original vertex of a point map is unchanged after any map to the terminal simplex. -/
private lemma constant_vertex {X Y : SSet.{u}} (p : X ⟶ (Δ[0] : SSet.{u}))
    (a : Y _⦋0⦌) (s : X _⦋0⦌) :
    (p ≫ SSet.yonedaEquiv.symm a).app (op ⦋0⦌) s = a := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, ← Category.assoc]
  have h : SSet.yonedaEquiv.symm s ≫ p = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

/-- Every original left inverse-triangle point gives its exact intrinsic left-inverse identity. -/
theorem leftCandidate_comp (hW : segalSpaces W) (s : (leftSpace W x y f) _⦋0⦌) :
    compose W hW (SSet.π₀.mk ((leftCandidate W x y f).app (op ⦋0⦌) s))
      (SSet.π₀.mk f) = identity W y := by
  have h := compose_of_triangle W hW y x y
    (SSet.π₀.mk ((leftTriangle W x y f).app (op ⦋0⦌) s))
  simp only [SSet.mapπ₀_mk] at h
  change compose W hW
    (SSet.π₀.mk ((leftTriangle W x y f ≫ triangleComparison W y x y ≫ prod.fst).app
      (op ⦋0⦌) s))
    (SSet.π₀.mk ((leftTriangle W x y f ≫ triangleComparison W y x y ≫ prod.snd).app
      (op ⦋0⦌) s)) =
    SSet.π₀.mk ((leftTriangle W x y f ≫ triangleMiddle W y x y).app (op ⦋0⦌) s) at h
  rw [left_varyingFirst, left_fixedLast, left_middle] at h
  simpa only [constant_vertex, identityPoint, identity] using h

/-- Every original right inverse-triangle point gives its exact intrinsic right-inverse identity. -/
theorem comp_rightCandidate (hW : segalSpaces W) (s : (rightSpace W x y f) _⦋0⦌) :
    compose W hW (SSet.π₀.mk f)
      (SSet.π₀.mk ((rightCandidate W x y f).app (op ⦋0⦌) s)) = identity W x := by
  have h := compose_of_triangle W hW x y x
    (SSet.π₀.mk ((rightTriangle W x y f).app (op ⦋0⦌) s))
  simp only [SSet.mapπ₀_mk] at h
  change compose W hW
    (SSet.π₀.mk ((rightTriangle W x y f ≫ triangleComparison W x y x ≫ prod.fst).app
      (op ⦋0⦌) s))
    (SSet.π₀.mk ((rightTriangle W x y f ≫ triangleComparison W x y x ≫ prod.snd).app
      (op ⦋0⦌) s)) =
    SSet.π₀.mk ((rightTriangle W x y f ≫ triangleMiddle W x y x).app (op ⦋0⦌) s) at h
  rw [right_fixedFirst, right_varyingLast, right_middle] at h
  simpa only [constant_vertex, identityPoint, identity] using h

/-- The actual original outer edge between two ordered vertices of a three-simplex. -/
private def outerEdge (i j : Fin 4) (hij : i ≤ j) : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ :=
  W.diagram.map (SimplexCategory.mkOfLe i j hij).op

/-- Its original source is the first selected outer vertex. -/
private lemma outerEdge_source (i j : Fin 4) (hij : i ≤ j) :
    outerEdge W i j hij ≫ W.diagram.δ (1 : Fin 2) =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op = _
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ i := by ext k; fin_cases k; rfl
  simpa only [outerEdge, Functor.map_comp, op_comp] using
    congrArg (fun a => W.diagram.map a.op) h

/-- Its original target is the second selected outer vertex. -/
private lemma outerEdge_target (i j : Fin 4) (hij : i ≤ j) :
    outerEdge W i j hij ≫ W.diagram.δ (0 : Fin 2) =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ j).op := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op = _
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ j := by ext k; fin_cases k; rfl
  simpa only [outerEdge, Functor.map_comp, op_comp] using
    congrArg (fun a => W.diagram.map a.op) h

/-- The raw finite ordinal face identity gives the same original contravariant edge map. -/
private lemma face_outerEdge (i : Fin 4) (j : Fin 3) (a b : Fin 4) (hab : a ≤ b)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfLe a b hab) :
    W.diagram.δ i ≫ W.diagram.δ j = outerEdge W a b hab := by
  change W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op = W.diagram.map (SimplexCategory.mkOfLe a b hab).op
  simpa only [outerEdge, Functor.map_comp, op_comp] using
    congrArg (fun a => W.diagram.map a.op) h

/-- A genuine original Z(3) witness gives a paired point through the same chosen pullbacks. -/
private lemma paired_nonempty_of_original_inverseData
    (t : (W.diagram _⦋3⦌) _⦋0⦌)
    (ht : (inverseRestriction W).app (op ⦋0⦌) t =
      (identityTriple W).app (op ⦋0⦌) ((mappingFibre.fst W x y).app (op ⦋0⦌) f)) :
    (pairedSpace W x y f).Nonempty := by
  let F : (Δ[0] : SSet.{u}) ⟶ mappingFibre W x y := SSet.yonedaEquiv.symm f
  let G : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋1⦌ := F ≫ mappingFibre.fst W x y
  let T : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋3⦌ := SSet.yonedaEquiv.symm t
  have hFp : F ≫ mappingFibre.snd W x y = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hGs : G ≫ W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm x := by
    dsimp only [G]
    rw [Category.assoc, mappingFibre.source_eq, ← Category.assoc, hFp, Category.id_comp]
  have hGt : G ≫ W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm y := by
    dsimp only [G]
    rw [Category.assoc, mappingFibre.target_eq, ← Category.assoc, hFp, Category.id_comp]
  have hT : T ≫ inverseRestriction W = G ≫ identityTriple W := by
    apply SSet.yonedaEquiv.injective
    simpa only [T, G, F, Category.assoc, SSet.yonedaEquiv_comp,
      NatTrans.comp_app, ConcreteCategory.comp_apply, Equiv.apply_symm_apply] using ht
  have h02 : T ≫ outerEdge W 0 2 (by decide) =
      identityPoint W y ≫ mappingFibre.fst W y y := by
    have h := congrArg (fun k => k ≫ inverseFirst W) hT
    have hh : T ≫ outerEdge W 0 2 (by decide) =
        G ≫ W.diagram.δ (0 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) := by
      simpa only [Category.assoc, inverseRestriction_first, identityTriple_first,
        outerEdge] using h
    rw [← Category.assoc, hGt, ← identityPoint_fst] at hh
    exact hh
  have h12 : T ≫ outerEdge W 1 2 (by decide) = G := by
    have h := congrArg (fun k => k ≫ inverseMiddle W) hT
    simpa only [Category.assoc, inverseRestriction_middle, identityTriple_middle,
      Category.comp_id, outerEdge] using h
  have h13 : T ≫ outerEdge W 1 3 (by decide) =
      identityPoint W x ≫ mappingFibre.fst W x x := by
    have h := congrArg (fun k => k ≫ inverseLast W) hT
    have hh : T ≫ outerEdge W 1 3 (by decide) =
        G ≫ W.diagram.δ (1 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) := by
      simpa only [Category.assoc, inverseRestriction_last, identityTriple_last,
        outerEdge] using h
    rw [← Category.assoc, hGs, ← identityPoint_fst] at hh
    exact hh
  let B₀ := T ≫ outerEdge W 0 1 (by decide)
  let C₀ := T ≫ outerEdge W 2 3 (by decide)
  have hBs : B₀ ≫ W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm y := by
    dsimp only [B₀]
    rw [Category.assoc, outerEdge_source,
      ← outerEdge_source W 0 2 (by decide), ← Category.assoc, h02,
      Category.assoc, mappingFibre.source_eq, ← Category.assoc,
      identityPoint_snd, Category.id_comp]
  have hBt : B₀ ≫ W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm x := by
    dsimp only [B₀]
    rw [Category.assoc, outerEdge_target,
      ← outerEdge_source W 1 2 (by decide), ← Category.assoc, h12]
    exact hGs
  have hCs : C₀ ≫ W.diagram.δ (1 : Fin 2) = SSet.yonedaEquiv.symm y := by
    dsimp only [C₀]
    rw [Category.assoc, outerEdge_source,
      ← outerEdge_target W 1 2 (by decide), ← Category.assoc, h12]
    exact hGt
  have hCt : C₀ ≫ W.diagram.δ (0 : Fin 2) = SSet.yonedaEquiv.symm x := by
    dsimp only [C₀]
    rw [Category.assoc, outerEdge_target,
      ← outerEdge_target W 1 3 (by decide), ← Category.assoc, h13,
      Category.assoc, mappingFibre.target_eq, ← Category.assoc,
      identityPoint_snd, Category.id_comp]
  have hB : B₀ ≫ mappingEndpoint W = 𝟙 (Δ[0] : SSet.{u}) ≫ mappingPointPair W y x := by
    apply prod.hom_ext
    · simpa only [Category.assoc, mappingEndpoint_fst, Category.id_comp,
        mappingPointPair_fst] using hBs
    · simpa only [Category.assoc, mappingEndpoint_snd, Category.id_comp,
        mappingPointPair_snd] using hBt
  have hC : C₀ ≫ mappingEndpoint W = 𝟙 (Δ[0] : SSet.{u}) ≫ mappingPointPair W y x := by
    apply prod.hom_ext
    · simpa only [Category.assoc, mappingEndpoint_fst, Category.id_comp,
        mappingPointPair_fst] using hCs
    · simpa only [Category.assoc, mappingEndpoint_snd, Category.id_comp,
        mappingPointPair_snd] using hCt
  let B : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y x := pullback.lift B₀ (𝟙 _) hB
  let C : (Δ[0] : SSet.{u}) ⟶ mappingFibre W y x := pullback.lift C₀ (𝟙 _) hC
  have hBf : B ≫ mappingFibre.fst W y x = B₀ := pullback.lift_fst _ _ _
  have hBp : B ≫ mappingFibre.snd W y x = 𝟙 (Δ[0] : SSet.{u}) := pullback.lift_snd _ _ _
  have hCf : C ≫ mappingFibre.fst W y x = C₀ := pullback.lift_fst _ _ _
  have hCp : C ≫ mappingFibre.snd W y x = 𝟙 (Δ[0] : SSet.{u}) := pullback.lift_snd _ _ _
  let U_L := T ≫ W.diagram.δ (3 : Fin 4)
  let U_R := T ≫ W.diagram.δ (0 : Fin 4)
  have hLf : U_L ≫ W.diagram.δ (2 : Fin 3) = B₀ := by
    dsimp only [U_L, B₀]
    rw [Category.assoc, face_outerEdge W 3 2 0 1 (by decide) (by decide)]
  have hLm : U_L ≫ W.diagram.δ (1 : Fin 3) =
      identityPoint W y ≫ mappingFibre.fst W y y := by
    dsimp only [U_L]
    rw [Category.assoc, face_outerEdge W 3 1 0 2 (by decide) (by decide), h02]
  have hLl : U_L ≫ W.diagram.δ (0 : Fin 3) = G := by
    dsimp only [U_L]
    rw [Category.assoc, face_outerEdge W 3 0 1 2 (by decide) (by decide), h12]
  have hRf : U_R ≫ W.diagram.δ (2 : Fin 3) = G := by
    dsimp only [U_R]
    rw [Category.assoc, face_outerEdge W 0 2 1 2 (by decide) (by decide), h12]
  have hRm : U_R ≫ W.diagram.δ (1 : Fin 3) =
      identityPoint W x ≫ mappingFibre.fst W x x := by
    dsimp only [U_R]
    rw [Category.assoc, face_outerEdge W 0 1 1 3 (by decide) (by decide), h13]
  have hRl : U_R ≫ W.diagram.δ (0 : Fin 3) = C₀ := by
    dsimp only [U_R, C₀]
    rw [Category.assoc, face_outerEdge W 0 0 2 3 (by decide) (by decide)]
  have hQL : U_L ≫ twoEdgeComparison W = prod.lift B F ≫ twoEdgePair W y x y := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
        prod.lift_fst_assoc, hBf] using hLf
    · simpa only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
        prod.lift_snd_assoc] using hLl
  have hQR : U_R ≫ twoEdgeComparison W = prod.lift F C ≫ twoEdgePair W x y x := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
        prod.lift_fst_assoc] using hRf
    · simpa only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
        prod.lift_snd_assoc, hCf] using hRl
  let Q_L : (Δ[0] : SSet.{u}) ⟶ triangleSpace W y x y := pullback.lift U_L (prod.lift B F) hQL
  let Q_R : (Δ[0] : SSet.{u}) ⟶ triangleSpace W x y x := pullback.lift U_R (prod.lift F C) hQR
  have hQLf : Q_L ≫ triangleProjection W y x y = U_L := pullback.lift_fst _ _ _
  have hQLp : Q_L ≫ triangleComparison W y x y = prod.lift B F := pullback.lift_snd _ _ _
  have hQRf : Q_R ≫ triangleProjection W x y x = U_R := pullback.lift_fst _ _ _
  have hQRp : Q_R ≫ triangleComparison W x y x = prod.lift F C := pullback.lift_snd _ _ _
  have hAL : Q_L ≫ triangleComparison W y x y = B ≫ FixedEdgeTriangle.leftPair W x y f := by
    rw [hQLp]
    apply prod.hom_ext
    · simp only [FixedEdgeTriangle.leftPair, Category.assoc, prod.lift_fst, Category.comp_id]
    · simp only [FixedEdgeTriangle.leftPair, Category.assoc, prod.lift_snd]
      rw [← Category.assoc, hBp, Category.id_comp]
  have hAR : Q_R ≫ triangleComparison W x y x = C ≫ FixedEdgeTriangle.rightPair W x y f := by
    rw [hQRp]
    apply prod.hom_ext
    · simp only [FixedEdgeTriangle.rightPair, Category.assoc, prod.lift_fst]
      rw [← Category.assoc, hCp, Category.id_comp]
    · simp only [FixedEdgeTriangle.rightPair, Category.assoc, prod.lift_snd, Category.comp_id]
  let A_L : (Δ[0] : SSet.{u}) ⟶ FixedEdgeTriangle.leftTriangle W x y f := pullback.lift Q_L B hAL
  let A_R : (Δ[0] : SSet.{u}) ⟶ FixedEdgeTriangle.rightTriangle W x y f := pullback.lift Q_R C hAR
  have hALf : A_L ≫ FixedEdgeTriangle.leftTriangleProjection W x y f = Q_L :=
      pullback.lift_fst _ _ _
  have hALp : A_L ≫ FixedEdgeTriangle.leftProjection W x y f = B := pullback.lift_snd _ _ _
  have hARf : A_R ≫ FixedEdgeTriangle.rightTriangleProjection W x y f = Q_R :=
      pullback.lift_fst _ _ _
  have hARp : A_R ≫ FixedEdgeTriangle.rightProjection W x y f = C := pullback.lift_snd _ _ _
  have hML : A_L ≫ leftMiddle W x y f = identityPoint W y := by
    apply pullback.hom_ext
    · change (A_L ≫ leftMiddle W x y f) ≫ mappingFibre.fst W y y =
        identityPoint W y ≫ mappingFibre.fst W y y
      rw [leftMiddle, ← Category.assoc, hALf, Category.assoc, triangleMiddle_fst,
        ← Category.assoc, hQLf, hLm]
    · change (A_L ≫ leftMiddle W x y f) ≫ mappingFibre.snd W y y =
        identityPoint W y ≫ mappingFibre.snd W y y
      rw [leftMiddle, ← Category.assoc, hALf, Category.assoc, triangleMiddle_snd,
        ← Category.assoc, hQLp, prod.lift_fst_assoc, hBp, identityPoint_snd]
  have hMR : A_R ≫ rightMiddle W x y f = identityPoint W x := by
    apply pullback.hom_ext
    · change (A_R ≫ rightMiddle W x y f) ≫ mappingFibre.fst W x x =
        identityPoint W x ≫ mappingFibre.fst W x x
      rw [rightMiddle, ← Category.assoc, hARf, Category.assoc, triangleMiddle_fst,
        ← Category.assoc, hQRf, hRm]
    · change (A_R ≫ rightMiddle W x y f) ≫ mappingFibre.snd W x x =
        identityPoint W x ≫ mappingFibre.snd W x x
      rw [rightMiddle, ← Category.assoc, hARf, Category.assoc, triangleMiddle_snd,
        ← Category.assoc, hQRp, prod.lift_fst_assoc, hFp, identityPoint_snd]
  let L : (Δ[0] : SSet.{u}) ⟶ leftSpace W x y f :=
    pullback.lift A_L (𝟙 _) (hML.trans (Category.id_comp _).symm)
  let R : (Δ[0] : SSet.{u}) ⟶ rightSpace W x y f :=
    pullback.lift A_R (𝟙 _) (hMR.trans (Category.id_comp _).symm)
  have hLf' : L ≫ leftToFixed W x y f = A_L := pullback.lift_fst _ _ _
  have hLp' : L ≫ leftToPoint W x y f = 𝟙 (Δ[0] : SSet.{u}) := pullback.lift_snd _ _ _
  have hRf' : R ≫ rightToFixed W x y f = A_R := pullback.lift_fst _ _ _
  have hRp' : R ≫ rightToPoint W x y f = 𝟙 (Δ[0] : SSet.{u}) := pullback.lift_snd _ _ _
  let S : (Δ[0] : SSet.{u}) ⟶ pairedSpace W x y f := prod.lift L R
  have hSp : S ≫ pairedToPoint W x y f = 𝟙 (Δ[0] : SSet.{u}) := by
    dsimp only [S, pairedToPoint, pairedLeft]
    rw [prod.lift_fst_assoc, hLp']
  have hSc : S ≫ pairedCandidates W x y f = prod.lift B C := by
    apply prod.hom_ext
    · rw [Category.assoc, pairedCandidates_fst]
      dsimp only [S, pairedLeft, leftCandidate]
      rw [prod.lift_fst_assoc, ← Category.assoc, hLf', hALp, prod.lift_fst]
    · rw [Category.assoc, pairedCandidates_snd]
      dsimp only [S, pairedRight, rightCandidate]
      rw [prod.lift_snd_assoc, ← Category.assoc, hRf', hARp, prod.lift_snd]
  let point : { s : (Δ[0] : SSet.{u}) ⟶ pairedSpace W x y f //
      s ≫ pairedToPoint W x y f = 𝟙 _ ∧ s ≫ pairedCandidates W x y f = prod.lift B C } :=
    ⟨S, hSp, hSc⟩
  exact ⟨SSet.yonedaEquiv point.val⟩

/-- Nonemptiness of the actual paired inverse space is precisely invertibility of the same original
hom class. -/
theorem pairedSpace_nonempty_iff_isIso
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    (pairedSpace W x y f).Nonempty ↔
      IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk f) := by
  constructor
  · rintro ⟨s⟩
    let sL := (pairedLeft W x y f).app (op ⦋0⦌) s
    let sR := (pairedRight W x y f).app (op ⦋0⦌) s
    let g : (⟨x⟩ : Object W hW) ⟶ ⟨y⟩ := SSet.π₀.mk f
    let l : (⟨y⟩ : Object W hW) ⟶ ⟨x⟩ :=
      SSet.π₀.mk ((leftCandidate W x y f).app (op ⦋0⦌) sL)
    let r : (⟨y⟩ : Object W hW) ⟶ ⟨x⟩ :=
      SSet.π₀.mk ((rightCandidate W x y f).app (op ⦋0⦌) sR)
    have hl : l ≫ g = 𝟙 (⟨y⟩ : Object W hW) := leftCandidate_comp W x y f hW sL
    have hr : g ≫ r = 𝟙 (⟨x⟩ : Object W hW) := comp_rightCandidate W x y f hW sR
    have he : l = r := by
      calc
        l = l ≫ 𝟙 (⟨x⟩ : Object W hW) := (Category.comp_id _).symm
        _ = l ≫ (g ≫ r) := by rw [hr]
        _ = (l ≫ g) ≫ r := (Category.assoc _ _ _).symm
        _ = r := by rw [hl, Category.id_comp]
    exact ⟨⟨l, he.symm ▸ hr, hl⟩⟩
  · intro hf
    let g := (mappingFibre.fst W x y).app (op ⦋0⦌) f
    have hg : IsEquivalenceEdge W hW g :=
      (isEquivalenceEdge_iff_of_fibre W hW g f rfl).mpr hf
    obtain ⟨t, ht⟩ := hasInverseData_of_isEquivalenceEdge W hW g hg
    exact paired_nonempty_of_original_inverseData W x y f t ht

end SimplicialSpace.InverseTriangle
