/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyStructure
public import MathlibExt.CategoryTheory.Reedy.Corner
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory

/-!
# Agreement with the canonical Reedy APIs

The original simplex and opposite-simplex interfaces use the native Mathlib Reedy structure.
Their full boundary categories, caller cones and cocones, relative arrows and morphism classes
agree with the established simplicial-object APIs. The comparison retains the original degree,
source maps and complete chosen factorization records.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC uJ vJ uD

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SimplexCategory.ReedyCanonicalComparison

/-- A canonical latching comparison is itself epi by its complete original epi triangle. -/
theorem latchingComparison_epi {n : ℕ} {a b : SimplicialObject.latchingIndex n} (f : a ⟶ b) :
    Epi f.hom.left.unop := by
  have h : b.obj.hom.unop ≫ f.hom.left.unop = a.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simp
  let : Epi (b.obj.hom.unop ≫ f.hom.left.unop) := h.symm ▸ a.property.1
  exact epi_of_epi b.obj.hom.unop f.hom.left.unop

/-- A canonical matching comparison is itself mono by its complete original mono triangle. -/
theorem matchingComparison_mono {n : ℕ} {a b : SimplicialObject.matchingIndex n} (f : a ⟶ b) :
    Mono f.hom.right.unop := by
  have h : f.hom.right.unop ≫ a.obj.hom.unop = b.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simpa using StructuredArrow.w f.hom
  let : Mono (f.hom.right.unop ≫ a.obj.hom.unop) := h.symm ▸ b.property.1
  exact mono_of_mono f.hom.right.unop a.obj.hom.unop

variable {C : Type uC} [Category.{vC} C]

/-- Caller latching cocones are transported with exactly the same point and injections. -/
abbrev toCanonicalLatchingCocone (X : SimplicialObject C) (n : ℕ)
    (c : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌))) :
    Cocone (SimplicialObject.latchingDiagram X n) :=
  c.whisker (SimplicialObject.reedyOfLatchingIndex n)

/-- The transported caller latching cocone is a colimit whenever the original cocone is. -/
def toCanonicalLatchingIsColimit (X : SimplicialObject C) (n : ℕ)
    (c : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌))) (hc : IsColimit c) :
    IsColimit (toCanonicalLatchingCocone X n c) :=
  hc.whiskerEquivalence (SimplicialObject.latchingEquivalence n).symm

/-- Caller matching cones are transported with exactly the same point and projections. -/
abbrev toCanonicalMatchingCone (X : SimplicialObject C) (n : ℕ)
    (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌))) :
    Cone (SimplicialObject.matchingDiagram X n) :=
  c.whisker (SimplicialObject.reedyOfMatchingIndex n)

/-- The transported caller matching cone is a limit whenever the original cone is. -/
def toCanonicalMatchingIsLimit (X : SimplicialObject C) (n : ℕ)
    (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌))) (hc : IsLimit c) :
    IsLimit (toCanonicalMatchingCone X n c) :=
  hc.whiskerEquivalence (SimplicialObject.matchingEquivalence n).symm


/-- The original incoming arrow is unchanged by the canonical index equivalence. -/
@[simp]
theorem latchingToCanonical_arrow (n : ℕ) (a : reedyOp.Latching (op ⦋n⦌)) :
    ((SimplicialObject.latchingIndexOfReedy n).obj a).obj.hom = reedyOp.latchingArrow a := rfl

/-- The original latching comparison map is unchanged by the canonical index equivalence. -/
@[simp]
theorem latchingToCanonical_comparison (n : ℕ) {a b : reedyOp.Latching (op ⦋n⦌)} (f : a ⟶ b) :
    ((SimplicialObject.latchingIndexOfReedy n).map f).hom.left = reedyOp.latchingComparison f := rfl

/-- The original outgoing arrow is unchanged by the canonical index equivalence. -/
@[simp]
theorem matchingToCanonical_arrow (n : ℕ) (a : reedyOp.Matching (op ⦋n⦌)) :
    ((SimplicialObject.matchingIndexOfReedy n).obj a).obj.hom = reedyOp.matchingArrow a := rfl

/-- The original matching comparison map is unchanged by the canonical index equivalence. -/
@[simp]
theorem matchingToCanonical_comparison (n : ℕ) {a b : reedyOp.Matching (op ⦋n⦌)} (f : a ⟶ b) :
    ((SimplicialObject.matchingIndexOfReedy n).map f).hom.right = reedyOp.matchingComparison f :=
      rfl

section LatchingComparison

variable (X : SimplicialObject C) (n : ℕ)
  [HasColimitsOfShape (SimplicialObject.latchingIndex n) C]

/-- The full caller latching colimit is isomorphic to the established latching object. -/
def latchingPointIsoWith (c : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌))) (hc : IsColimit c) :
    c.pt ≅ SimplicialObject.latchingObject X n :=
  (toCanonicalLatchingIsColimit X n c hc).coconePointUniqueUpToIso
    (colimit.isColimit (SimplicialObject.latchingDiagram X n))

/-- Every caller injection is retained under the complete latching object comparison. -/
@[reassoc]
theorem latchingPointIsoWith_ι (c : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌)))
    (hc : IsColimit c) (a : reedyOp.Latching (op ⦋n⦌)) :
    c.ι.app a ≫ (latchingPointIsoWith X n c hc).hom =
      SimplicialObject.latchingι X n ((SimplicialObject.latchingIndexOfReedy n).obj a) :=
  (toCanonicalLatchingIsColimit X n c hc).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ((SimplicialObject.latchingIndexOfReedy n).obj a)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison retains the entire original caller latching map. -/
theorem latchingMapWith_eq (c : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌)))
    (hc : IsColimit c) :
    reedyOp.latchingMapWith X (op ⦋n⦌) c hc =
      (latchingPointIsoWith X n c hc).hom ≫ SimplicialObject.latchingMap X n := by
  apply hc.hom_ext
  intro a
  rw [reedyOp.latchingMapWith_ι, ← Category.assoc, latchingPointIsoWith_ι,
    SimplicialObject.latchingMap_ι]
  rfl

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison retains the entire original caller latching transformation. -/
theorem latchingComparisonWith_eq
    (cX : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌))) (hX : IsColimit cX)
    (cY : Cocone (reedyOp.latchingDiagram Y (op ⦋n⦌))) (hY : IsColimit cY) :
    reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY ≫ (latchingPointIsoWith Y n cY hY).hom =
      (latchingPointIsoWith X n cX hX).hom ≫ (SimplicialObject.latchingObjectFunctor n).map f := by
  apply hX.hom_ext
  intro a
  rw [← Category.assoc, reedyOp.latchingComparisonWith_ι, Category.assoc,
    latchingPointIsoWith_ι, ← Category.assoc, latchingPointIsoWith_ι,
    SimplicialObject.latchingObjectFunctor_map_ι]
  rfl

end LatchingComparison

section MatchingComparison

variable (X : SimplicialObject C) (n : ℕ)
  [HasLimitsOfShape (SimplicialObject.matchingIndex n) C]

/-- The full caller matching limit is isomorphic to the established matching object. -/
def matchingPointIsoWith (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌))) (hc : IsLimit c) :
    c.pt ≅ SimplicialObject.matchingObject X n :=
  (toCanonicalMatchingIsLimit X n c hc).conePointUniqueUpToIso
    (limit.isLimit (SimplicialObject.matchingDiagram X n))

/-- Every caller projection is retained under the complete matching object comparison. -/
@[reassoc]
theorem matchingPointIsoWith_π (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌)))
    (hc : IsLimit c) (a : reedyOp.Matching (op ⦋n⦌)) :
    (matchingPointIsoWith X n c hc).hom ≫
      SimplicialObject.matchingπ X n ((SimplicialObject.matchingIndexOfReedy n).obj a) = c.π.app a
        :=
  (toCanonicalMatchingIsLimit X n c hc).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) ((SimplicialObject.matchingIndexOfReedy n).obj a)

/-- The inverse comparison retains every caller matching projection. -/
@[reassoc]
theorem matchingPointIsoWith_inv_π (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌)))
    (hc : IsLimit c) (a : reedyOp.Matching (op ⦋n⦌)) :
    (matchingPointIsoWith X n c hc).inv ≫ c.π.app a =
      SimplicialObject.matchingπ X n ((SimplicialObject.matchingIndexOfReedy n).obj a) :=
  (toCanonicalMatchingIsLimit X n c hc).conePointUniqueUpToIso_inv_comp
    (limit.isLimit _) ((SimplicialObject.matchingIndexOfReedy n).obj a)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison retains the entire original caller matching map. -/
theorem matchingMapWith_eq (c : Cone (reedyOp.matchingDiagram X (op ⦋n⦌)))
    (hc : IsLimit c) :
    reedyOp.matchingMapWith X (op ⦋n⦌) c hc ≫ (matchingPointIsoWith X n c hc).hom =
      SimplicialObject.matchingMap X n := by
  apply (cancel_mono (matchingPointIsoWith X n c hc).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply hc.hom_ext
  intro a
  rw [reedyOp.matchingMapWith_π, Category.assoc, matchingPointIsoWith_inv_π,
    SimplicialObject.matchingMap_π]
  rfl

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison retains the entire original caller matching transformation. -/
theorem matchingComparisonWith_eq
    (cX : Cone (reedyOp.matchingDiagram X (op ⦋n⦌))) (hX : IsLimit cX)
    (cY : Cone (reedyOp.matchingDiagram Y (op ⦋n⦌))) (hY : IsLimit cY) :
    reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY ≫ (matchingPointIsoWith Y n cY hY).hom =
      (matchingPointIsoWith X n cX hX).hom ≫ (SimplicialObject.matchingObjectFunctor n).map f := by
  apply (cancel_mono (matchingPointIsoWith Y n cY hY).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply hY.hom_ext
  intro a
  rw [reedyOp.matchingComparisonWith_π, Category.assoc, Category.assoc,
    matchingPointIsoWith_inv_π, SimplicialObject.matchingObjectFunctor_map_π,
    ← Category.assoc, matchingPointIsoWith_π]
  rfl

end MatchingComparison


/-- The simplex compatibility interface is exactly the established native simplex interface. -/
theorem ofCanonical_simplex_eq :
    CategoryTheory.ReedyStructure.ofCanonical reedyStructure = reedy :=
  CategoryTheory.ReedyStructure.ext _ _ rfl rfl rfl

/-- The opposite simplex compatibility interface is exactly the established native opposite
interface. -/
theorem ofCanonical_simplexOp_eq :
    CategoryTheory.ReedyStructure.ofCanonical reedyStructure.op = reedyOp :=
  CategoryTheory.ReedyStructure.ext _ _ rfl rfl rfl

/-- The complete original opposite factor is Mathlib's complete native opposite factor. -/
theorem reedyOpFactor_eq_canonical {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    reedyOp.factor f = reedyStructure.op.mapFactorizationData f := reedyOp.factor_unique f _ _


section RelativeLatching

variable {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
  [HasColimitsOfShape (SimplicialObject.latchingIndex n) C]
  [HasPushout (SimplicialObject.latchingMap X n) ((SimplicialObject.latchingObjectFunctor n).map f)]
  (cX : Cocone (reedyOp.latchingDiagram X (op ⦋n⦌))) (hX : IsColimit cX)
  (cY : Cocone (reedyOp.latchingDiagram Y (op ⦋n⦌))) (hY : IsColimit cY)
  (cP : PushoutCocone (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
    (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY)) (hP : IsColimit cP)

/-- The whole caller relative latching source is the established source under its exact point
comparisons. -/
def relativeLatchingSourceIsoWith : cP.pt ≅ SimplicialObject.relativeLatchingObject f n := by
  letI : HasPushout (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
      (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY) := HasColimit.mk ⟨cP, hP⟩
  exact (colimit.isoColimitCocone ⟨cP, hP⟩).symm ≪≫
    asIso (pushout.map _ _ _ _ (𝟙 (X.obj (op ⦋n⦌)))
      (latchingPointIsoWith Y n cY hY).hom (latchingPointIsoWith X n cX hX).hom
      (by rw [Category.comp_id]; exact latchingMapWith_eq X n cX hX)
      (latchingComparisonWith_eq n f cX hX cY hY))

/-- The original component injection is retained by the whole relative latching source comparison.
-/
@[reassoc]
theorem relativeLatchingSourceIsoWith_inl :
    cP.inl ≫ (relativeLatchingSourceIsoWith f n cX hX cY hY cP hP).hom =
      pushout.inl (SimplicialObject.latchingMap X n) ((SimplicialObject.latchingObjectFunctor n).map
        f) := by
  let : HasPushout (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
      (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY) := HasColimit.mk ⟨cP, hP⟩
  have hp : cP.inl ≫ (colimit.isoColimitCocone ⟨cP, hP⟩).inv =
      pushout.inl (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
        (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY) :=
    colimit.isoColimitCocone_ι_inv ⟨cP, hP⟩ WalkingSpan.left
  rw [relativeLatchingSourceIsoWith, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hp]
  simp only [asIso_hom, pushout.map, pushout.inl_desc, Category.id_comp]

/-- Every caller lower-degree coefficient injection is retained by the relative source comparison.
-/
@[reassoc]
theorem relativeLatchingSourceIsoWith_inr :
    cP.inr ≫ (relativeLatchingSourceIsoWith f n cX hX cY hY cP hP).hom =
      (latchingPointIsoWith Y n cY hY).hom ≫
        pushout.inr (SimplicialObject.latchingMap X n) ((SimplicialObject.latchingObjectFunctor
          n).map f) := by
  let : HasPushout (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
      (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY) := HasColimit.mk ⟨cP, hP⟩
  have hp : cP.inr ≫ (colimit.isoColimitCocone ⟨cP, hP⟩).inv =
      pushout.inr (reedyOp.latchingMapWith X (op ⦋n⦌) cX hX)
        (reedyOp.latchingComparisonWith f (op ⦋n⦌) cX hX cY) :=
    colimit.isoColimitCocone_ι_inv ⟨cP, hP⟩ WalkingSpan.right
  rw [relativeLatchingSourceIsoWith, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hp]
  simp only [asIso_hom, pushout.map, pushout.inr_desc]

/-- The complete caller relative latching arrow agrees with the established relative latching arrow.
-/
theorem relativeLatchingMapWith_eq :
    (relativeLatchingSourceIsoWith f n cX hX cY hY cP hP).hom ≫ SimplicialObject.relativeLatchingMap
      f n =
      reedyOp.latchingCornerWith f (op ⦋n⦌) cX hX cY hY cP hP := by
  apply PushoutCocone.IsColimit.hom_ext hP
  · rw [← Category.assoc, relativeLatchingSourceIsoWith_inl,
    SimplicialObject.relativeLatchingMap_inl,
      reedyOp.latchingCornerWith_inl]
  · rw [← Category.assoc, relativeLatchingSourceIsoWith_inr, Category.assoc,
      SimplicialObject.relativeLatchingMap_inr, reedyOp.latchingCornerWith_inr]
    exact (latchingMapWith_eq Y n cY hY).symm

/-- The whole caller relative latching Arrow, with every original object and map, is the canonical
Arrow. -/
def relativeLatchingArrowIsoWith :
    Arrow.mk (reedyOp.latchingCornerWith f (op ⦋n⦌) cX hX cY hY cP hP) ≅
      Arrow.mk (SimplicialObject.relativeLatchingMap f n) :=
  Arrow.isoMk' _ _ (relativeLatchingSourceIsoWith f n cX hX cY hY cP hP) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact relativeLatchingMapWith_eq f n cX hX cY hY cP hP)

end RelativeLatching

section RelativeMatching

variable {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
  [HasLimitsOfShape (SimplicialObject.matchingIndex n) C]
  [HasPullback (SimplicialObject.matchingMap Y n) ((SimplicialObject.matchingObjectFunctor n).map
    f)]
  (cX : Cone (reedyOp.matchingDiagram X (op ⦋n⦌))) (hX : IsLimit cX)
  (cY : Cone (reedyOp.matchingDiagram Y (op ⦋n⦌))) (hY : IsLimit cY)
  (cP : PullbackCone (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
    (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY)) (hP : IsLimit cP)

/-- The whole caller relative matching target is the established target with its exact projection
order. -/
def relativeMatchingTargetIsoWith : cP.pt ≅ SimplicialObject.relativeMatchingObject f n := by
  letI : HasPullback (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
      (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY) := HasLimit.mk ⟨cP, hP⟩
  letI : HasPullback ((SimplicialObject.matchingObjectFunctor n).map f)
      (SimplicialObject.matchingMap Y n) := hasPullback_symmetry _ _
  exact (limit.isoLimitCone ⟨cP, hP⟩).symm ≪≫
    asIso (pullback.map _ _ _ _ (matchingPointIsoWith X n cX hX).hom (𝟙 (Y.obj (op ⦋n⦌)))
      (matchingPointIsoWith Y n cY hY).hom
      (matchingComparisonWith_eq n f cX hX cY hY)
      (by rw [Category.id_comp]; exact matchingMapWith_eq Y n cY hY)) ≪≫
        pullbackSymmetry ((SimplicialObject.matchingObjectFunctor n).map f)
          (SimplicialObject.matchingMap Y n)

/-- The component projection retains the caller's original component of the simplicial map. -/
@[reassoc]
theorem relativeMatchingTargetIsoWith_fst :
    (relativeMatchingTargetIsoWith f n cX hX cY hY cP hP).hom ≫
      pullback.fst (SimplicialObject.matchingMap Y n) ((SimplicialObject.matchingObjectFunctor
        n).map f) =
        cP.snd := by
  let : HasPullback (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
      (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY) := HasLimit.mk ⟨cP, hP⟩
  let : HasPullback ((SimplicialObject.matchingObjectFunctor n).map f)
      (SimplicialObject.matchingMap Y n) := hasPullback_symmetry _ _
  have hp : (limit.isoLimitCone ⟨cP, hP⟩).inv ≫
      pullback.snd (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
        (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY) = cP.snd :=
    limit.isoLimitCone_inv_π ⟨cP, hP⟩ WalkingCospan.right
  rw [relativeMatchingTargetIsoWith, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [pullbackSymmetry_hom_comp_fst]
  simp only [asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  exact hp

/-- Every caller lower-degree coefficient projection is retained by the whole relative target
comparison. -/
@[reassoc]
theorem relativeMatchingTargetIsoWith_snd :
    (relativeMatchingTargetIsoWith f n cX hX cY hY cP hP).hom ≫
      pullback.snd (SimplicialObject.matchingMap Y n) ((SimplicialObject.matchingObjectFunctor
        n).map f) =
        cP.fst ≫ (matchingPointIsoWith X n cX hX).hom := by
  let : HasPullback (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
      (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY) := HasLimit.mk ⟨cP, hP⟩
  let : HasPullback ((SimplicialObject.matchingObjectFunctor n).map f)
      (SimplicialObject.matchingMap Y n) := hasPullback_symmetry _ _
  have hp : (limit.isoLimitCone ⟨cP, hP⟩).inv ≫
      pullback.fst (reedyOp.matchingComparisonWith f (op ⦋n⦌) cX cY hY)
        (reedyOp.matchingMapWith Y (op ⦋n⦌) cY hY) = cP.fst :=
    limit.isoLimitCone_inv_π ⟨cP, hP⟩ WalkingCospan.left
  rw [relativeMatchingTargetIsoWith, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [pullbackSymmetry_hom_comp_snd]
  simp only [asIso_hom, pullback.map, pullback.lift_fst]
  rw [← Category.assoc, hp]

/-- The complete caller relative matching arrow agrees with the established relative matching arrow.
-/
theorem relativeMatchingMapWith_eq :
    reedyOp.matchingCornerWith f (op ⦋n⦌) cX hX cY hY cP hP ≫
        (relativeMatchingTargetIsoWith f n cX hX cY hY cP hP).hom =
      SimplicialObject.relativeMatchingMap f n := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeMatchingTargetIsoWith_fst, reedyOp.matchingCornerWith_snd,
      SimplicialObject.relativeMatchingMap_fst]
  · rw [Category.assoc, relativeMatchingTargetIsoWith_snd, ← Category.assoc,
      reedyOp.matchingCornerWith_fst, SimplicialObject.relativeMatchingMap_snd]
    exact matchingMapWith_eq X n cX hX

/-- The whole caller relative matching Arrow, with every original object and map, is the canonical
Arrow. -/
def relativeMatchingArrowIsoWith :
    Arrow.mk (reedyOp.matchingCornerWith f (op ⦋n⦌) cX hX cY hY cP hP) ≅
      Arrow.mk (SimplicialObject.relativeMatchingMap f n) :=
  Arrow.isoMk' _ _ (Iso.refl _) (relativeMatchingTargetIsoWith f n cX hX cY hY cP hP)
    (by rw [Iso.refl_hom, Category.id_comp]; exact (relativeMatchingMapWith_eq f n cX hX cY hY cP
      hP).symm)

end RelativeMatching


section StandardLatching

variable [HasPushouts C]
  [∀ j, HasColimitsOfShape (reedyOp.Latching j) C]
  [∀ n : ℕ, HasColimitsOfShape (SimplicialObject.latchingIndex n) C]
  {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)

/-- Every source class respecting Arrow isomorphisms has the same full relative latching test. -/
theorem latchingCorner_mem_iff (P : MorphismProperty C) [P.RespectsIso] :
    P (CategoryTheory.ReedyStructure.latchingCorner reedyOp f (op ⦋n⦌)) ↔
      P (SimplicialObject.relativeLatchingMap f n) :=
  P.arrow_mk_iso_iff (SimplicialObject.latchingCornerArrowIso f n)

end StandardLatching

section StandardMatching

variable [HasPullbacks C]
  [∀ j, HasLimitsOfShape (reedyOp.Matching j) C]
  [∀ n : ℕ, HasLimitsOfShape (SimplicialObject.matchingIndex n) C]
  {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)

/-- Every source class respecting Arrow isomorphisms has the same full relative matching test. -/
theorem matchingCorner_mem_iff (P : MorphismProperty C) [P.RespectsIso] :
    P (CategoryTheory.ReedyStructure.matchingCorner reedyOp f (op ⦋n⦌)) ↔
      P (SimplicialObject.relativeMatchingMap f n) :=
  P.arrow_mk_iso_iff (SimplicialObject.matchingCornerArrowIso f n)

end StandardMatching


section ModelAgreement

open HomotopicalAlgebra CategoryTheory.MorphismProperty

variable [ModelCategory C]

/-- The established simplicial model has precisely the original pointwise weak class. -/
theorem canonical_weakEquivalences_eq :
    letI := SimplicialObject.reedyModelCategory (C := C)
    weakEquivalences (SimplicialObject C) = (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ
      := rfl

/-- The established simplicial cofibrations are the full original latching-corner class. -/
theorem canonical_cofibrations_eq :
    letI := SimplicialObject.reedyModelCategory (C := C)
    cofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass reedyOp (cofibrations C) :=
  (SimplicialObject.reedyLeft_eq_latchingClass (cofibrations C))

/-- The established simplicial fibrations are the full original matching-corner class. -/
theorem canonical_fibrations_eq :
    letI := SimplicialObject.reedyModelCategory (C := C)
    fibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass reedyOp (fibrations C) :=
  (SimplicialObject.reedyRight_eq_matchingClass (fibrations C))

/-- The established simplicial trivial cofibrations retain the full original source class. -/
theorem canonical_trivialCofibrations_eq :
    letI := SimplicialObject.reedyModelCategory (C := C)
    trivialCofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass reedyOp (trivialCofibrations C) := by
  change SimplicialObject.reedyLeft (cofibrations C) ⊓
    (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ = _
  rw [← SimplicialObject.reedyLeft_trivialCofibrations_eq]
  exact (SimplicialObject.reedyLeft_eq_latchingClass (trivialCofibrations C))

/-- The established simplicial trivial fibrations retain the full original source class. -/
theorem canonical_trivialFibrations_eq :
    letI := SimplicialObject.reedyModelCategory (C := C)
    trivialFibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass reedyOp (trivialFibrations C) := by
  change SimplicialObject.reedyRight (fibrations C) ⊓
    (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ = _
  rw [← SimplicialObject.reedyRight_trivialFibrations_eq]
  exact (SimplicialObject.reedyRight_eq_matchingClass (trivialFibrations C))

/-- A model dictionary is determined by its three stored classes; the remaining fields are proofs.
-/
private theorem modelCategory_eq_of_classes {E : Type uJ} [Category.{vJ} E]
    (a b : ModelCategory E)
    (hf : a.categoryWithFibrations = b.categoryWithFibrations)
    (hc : a.categoryWithCofibrations = b.categoryWithCofibrations)
    (hw : a.categoryWithWeakEquivalences = b.categoryWithWeakEquivalences) : a = b := by
  cases a
  cases b
  cases hf
  cases hc
  cases hw
  rfl

variable
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The full general simplex model dictionary agrees with the established canonical dictionary. -/
theorem modelCategory_eq_canonical :
    ReedyModel.modelCategory reedyOp Fc Ff = SimplicialObject.reedyModelCategory (C := C) := by
  apply modelCategory_eq_of_classes
  · exact congrArg CategoryWithFibrations.mk (SimplicialObject.reedyRight_eq_matchingClass
    (fibrations C)).symm
  · exact congrArg CategoryWithCofibrations.mk (SimplicialObject.reedyLeft_eq_latchingClass
    (cofibrations C)).symm
  · rfl

/-- Transport the originally supplied full cofibration factory to the established canonical model
classes. -/
def canonicalCofibrantFactorizationData :
    letI := SimplicialObject.reedyModelCategory (C := C)
    FunctorialFactorizationData (cofibrations (SimplicialObject C))
      (trivialFibrations (SimplicialObject C)) := by
  letI := SimplicialObject.reedyModelCategory (C := C)
  exact (ReedyModel.cofibrantFactorizationData reedyOp Fc Ff).ofLE
    (fun _ _ f h => (canonical_cofibrations_eq (C := C)).symm ▸ h)
    (fun _ _ f h => by
      change SimplicialObject.reedyRight (fibrations C) f ∧
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f
      exact ⟨(SimplicialObject.reedyRight_eq_matchingClass (fibrations C)).symm.le _ h.1, h.2⟩)

/-- Transport the originally supplied full fibration factory to the established canonical model
classes. -/
def canonicalFibrantFactorizationData :
    letI := SimplicialObject.reedyModelCategory (C := C)
    FunctorialFactorizationData (trivialCofibrations (SimplicialObject C))
      (fibrations (SimplicialObject C)) := by
  letI := SimplicialObject.reedyModelCategory (C := C)
  exact (ReedyModel.fibrantFactorizationData reedyOp Fc Ff).ofLE
    (fun _ _ f h => by
      change SimplicialObject.reedyLeft (cofibrations C) f ∧
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ f
      exact ⟨(SimplicialObject.reedyLeft_eq_latchingClass (cofibrations C)).symm.le _ h.1, h.2⟩)
    (fun _ _ f h => (canonical_fibrations_eq (C := C)).symm ▸ h)

/-- The transported cofibration factory retains its entire original middle functor. -/
theorem canonicalCofibrantFactorizationData_Z :
    (canonicalCofibrantFactorizationData Fc Ff).Z =
      (ReedyModel.cofibrantFactorizationData reedyOp Fc Ff).Z := rfl

/-- The transported cofibration factory retains its entire original left natural map. -/
theorem canonicalCofibrantFactorizationData_i :
    (canonicalCofibrantFactorizationData Fc Ff).i =
      (ReedyModel.cofibrantFactorizationData reedyOp Fc Ff).i := rfl

/-- The transported cofibration factory retains its entire original right natural map. -/
theorem canonicalCofibrantFactorizationData_p :
    (canonicalCofibrantFactorizationData Fc Ff).p =
      (ReedyModel.cofibrantFactorizationData reedyOp Fc Ff).p := rfl

/-- The transported fibration factory retains its entire original middle functor. -/
theorem canonicalFibrantFactorizationData_Z :
    (canonicalFibrantFactorizationData Fc Ff).Z =
      (ReedyModel.fibrantFactorizationData reedyOp Fc Ff).Z := rfl

/-- The transported fibration factory retains its entire original left natural map. -/
theorem canonicalFibrantFactorizationData_i :
    (canonicalFibrantFactorizationData Fc Ff).i =
      (ReedyModel.fibrantFactorizationData reedyOp Fc Ff).i := rfl

/-- The transported fibration factory retains its entire original right natural map. -/
theorem canonicalFibrantFactorizationData_p :
    (canonicalFibrantFactorizationData Fc Ff).p =
      (ReedyModel.fibrantFactorizationData reedyOp Fc Ff).p := rfl

/-- The full canonical model and both complete original functorial factories are constructed
together. -/
theorem constructs_canonical :
    letI := SimplicialObject.reedyModelCategory (C := C)
    ∃ (c : FunctorialFactorizationData (cofibrations (SimplicialObject C))
        (trivialFibrations (SimplicialObject C)))
      (f : FunctorialFactorizationData (trivialCofibrations (SimplicialObject C))
        (fibrations (SimplicialObject C))),
      c = canonicalCofibrantFactorizationData Fc Ff ∧
      f = canonicalFibrantFactorizationData Fc Ff ∧
      weakEquivalences (SimplicialObject C) = (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ
        ∧
      cofibrations (SimplicialObject C) =
        CategoryTheory.ReedyStructure.latchingClass reedyOp (cofibrations C) ∧
      fibrations (SimplicialObject C) =
        CategoryTheory.ReedyStructure.matchingClass reedyOp (fibrations C) ∧
      trivialCofibrations (SimplicialObject C) =
        CategoryTheory.ReedyStructure.latchingClass reedyOp (trivialCofibrations C) ∧
      trivialFibrations (SimplicialObject C) =
        CategoryTheory.ReedyStructure.matchingClass reedyOp (trivialFibrations C) :=
  ⟨canonicalCofibrantFactorizationData Fc Ff, canonicalFibrantFactorizationData Fc Ff,
    rfl, rfl, canonical_weakEquivalences_eq, canonical_cofibrations_eq,
    canonical_fibrations_eq, canonical_trivialCofibrations_eq, canonical_trivialFibrations_eq⟩

end ModelAgreement

end SimplexCategory.ReedyCanonicalComparison
