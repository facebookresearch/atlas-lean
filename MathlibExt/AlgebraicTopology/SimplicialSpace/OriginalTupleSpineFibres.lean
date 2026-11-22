/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import Mathlib.Tactic.FinCases
import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Original ambient-prefix edge restrictions

The model-free induction uses the actual prefix pullback;
no caller preservation, cocone, gluing Iso or homotopical outcome is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace SimplicialSpace.FixedTupleSpinePrefix

/-- The actual inner mapping object on the first r edges of the fixed n-simplex. -/
abbrev prefixObject (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) : SSet.{u} :=
  (discreteSourceMapping W).obj
    (op (SSet.Rezk.spinePrefixSubcomplex.{u} n r h : SSet.{u}))


/-- Every selected original consecutive edge enters the same ambient prefix. -/
def edgeInclusion (n r : ℕ) (h : r ≤ n) (i : Fin r) :
    (Δ[1] : SSet.{u}) ⟶ (SSet.Rezk.spinePrefixSubcomplex.{u} n r h : SSet.{u}) :=
  (SSet.Rezk.spinePrefixSubcomplex n r h).lift
    (SSet.Rezk.segalSpineEdgeMap n ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
    (le_iSup (fun j : Fin r => SSet.Rezk.segalSpineEdgeSubcomplex n
      ⟨j.val, lt_of_lt_of_le j.isLt h⟩) i)


/-- Both mapping and inner representable comparison use this literal edge inclusion. -/
def edgeProjection (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (i : Fin r) :
    prefixObject W n r h ⟶ W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).map (edgeInclusion.{u} n r h i).op ≫
    (discreteYonedaIso W 1).hom


private theorem edgeInclusion_previous (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r) :
    edgeInclusion.{u} n r h ⟨r - 1, by omega⟩ =
      SSet.Rezk.spinePrefixPreviousEdge n r h hr := by
  apply (cancel_mono (SSet.Rezk.spinePrefixSubcomplex.{u} n r h).ι).mp
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  rfl


private theorem edgeInclusion_left (n r : ℕ) (h : r + 1 ≤ n) (i : Fin r) :
    edgeInclusion.{u} n r (Nat.le_of_succ_le h) i ≫
      SSet.Rezk.spinePrefixLeft n r h =
        edgeInclusion n (r + 1) h i.castSucc := by
  apply (cancel_mono (SSet.Rezk.spinePrefixSubcomplex.{u} n (r + 1) h).ι).mp
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  rfl


private theorem edgeInclusion_right (n r : ℕ) (h : r + 1 ≤ n) :
    SSet.Subcomplex.toRange
        (SSet.Rezk.segalSpineEdgeMap.{u} n ⟨r, Nat.lt_of_succ_le h⟩) ≫
      SSet.Rezk.spinePrefixRight n r h =
        edgeInclusion n (r + 1) h (Fin.last r) := by
  apply (cancel_mono (SSet.Rezk.spinePrefixSubcomplex.{u} n (r + 1) h).ι).mp
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  rfl


/-- The first prefix projection is the actual original one-edge mapping Iso. -/
theorem edgeProjection_one (W : SimplicialSpace.{u}) (n : ℕ) (h : 1 ≤ n) :
    edgeProjection W n 1 h (0 : Fin 1) = (spinePrefixFirstMappingIso W n h).hom := by
  have he : edgeInclusion.{u} n 1 h (0 : Fin 1) =
      SSet.Rezk.spinePrefixPreviousEdge n 1 h le_rfl :=
    edgeInclusion_previous n 1 h le_rfl
  rw [edgeProjection, he]
  exact (spinePrefixFirstMappingIso_hom W n h).symm


/-- An earlier edge restriction passes through the literal left prefix projection. -/
theorem edgeProjection_left (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r + 1 ≤ n) (i : Fin r) :
    (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft.{u} n r h).op ≫
        edgeProjection W n r (Nat.le_of_succ_le h) i =
      edgeProjection W n (r + 1) h i.castSucc := by
  unfold edgeProjection
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, edgeInclusion_left]


/-- The newest edge restriction passes through the literal right edge projection. -/
theorem edgeProjection_right (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r + 1 ≤ n) :
    (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight.{u} n r h).op ≫
        (spineEdgeMappingIso W n ⟨r, Nat.lt_of_succ_le h⟩).hom =
      edgeProjection W n (r + 1) h (Fin.last r) := by
  unfold spineEdgeMappingIso edgeProjection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, asIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, edgeInclusion_right]


/-- All original edge restrictions jointly determine every map into a nonempty prefix. -/
theorem edgeProjection_hom_ext (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) {Z : SSet.{u}}
    (a b : Z ⟶ prefixObject W n r h)
    (hab : ∀ i : Fin r, a ≫ edgeProjection W n r h i =
      b ≫ edgeProjection W n r h i) : a = b := by
  induction r generalizing Z with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r = 0
    · subst r
      exact (cancel_mono (spinePrefixFirstMappingIso W n h).hom).mp
        (by
          have h0 := hab (0 : Fin 1)
          change a ≫ edgeProjection W n 1 h 0 = b ≫ edgeProjection W n 1 h 0 at h0
          rw [edgeProjection_one] at h0
          exact h0)
    · have hrpos : 1 ≤ r := by omega
      apply (spinePrefixMapping_isPullback W n r h hrpos).hom_ext
      · apply ih (Nat.le_of_succ_le h) hrpos
          (a ≫ (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft.{u} n r h).op)
          (b ≫ (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft.{u} n r h).op)
        intro i
        simpa only [Category.assoc, edgeProjection_left] using hab i.castSucc
      · apply (cancel_mono (spineEdgeMappingIso W n ⟨r, Nat.lt_of_succ_le h⟩).hom).mp
        simpa only [Category.assoc, edgeProjection_right] using hab (Fin.last r)



private theorem edgeProjection_last (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) :
    edgeProjection W n r h ⟨r - 1, by omega⟩ =
      spinePrefixLastEdgeProjection W n r h hr := by
  unfold edgeProjection spinePrefixLastEdgeProjection
  rw [edgeInclusion_previous]


/-- Literal adjacent endpoints of an original finite family, with no chosen lift data. -/
def Adjacent {W : SimplicialSpace.{u}} {Z : SSet.{u}} {r : ℕ}
    (a : Fin r → (Z ⟶ W.diagram _⦋1⦌)) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < r),
    a ⟨j, by omega⟩ ≫ W.diagram.δ (0 : Fin 2) =
      a ⟨j + 1, hj⟩ ≫ W.diagram.δ (1 : Fin 2)


/-- Every original compatible finite edge family is glued internally into the SAME ambient
prefix. -/
theorem exists_prefixLift (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) {Z : SSet.{u}}
    (a : Fin r → (Z ⟶ W.diagram _⦋1⦌)) (ha : Adjacent a) :
    ∃ q : Z ⟶ prefixObject W n r h,
      ∀ i : Fin r, q ≫ edgeProjection W n r h i = a i := by
  induction r generalizing Z with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r = 0
    · subst r
      refine ⟨a 0 ≫ (spinePrefixFirstMappingIso W n h).inv, ?_⟩
      intro i
      have hi : i = (0 : Fin 1) := by
        apply Fin.ext
        have bound := i.isLt
        omega
      subst i
      rw [edgeProjection_one, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · have hrpos : 1 ≤ r := by omega
      let old : Fin r → (Z ⟶ W.diagram _⦋1⦌) := fun i => a i.castSucc
      have hold : Adjacent old := by
        intro j hj
        simpa only [old, Fin.castSucc_mk] using
          ha j (lt_trans hj (Nat.lt_succ_self r))
      obtain ⟨q, hq⟩ := ih (Nat.le_of_succ_le h) hrpos old hold
      let edge : Z ⟶
          (discreteSourceMapping W).obj
            (op (SSet.Rezk.segalSpineEdgeSubcomplex.{u} n
              ⟨r, Nat.lt_of_succ_le h⟩ : SSet.{u})) :=
        a (Fin.last r) ≫ (spineEdgeMappingIso W n ⟨r, Nat.lt_of_succ_le h⟩).inv
      have hs : q ≫
          (discreteSourceMapping W).map
            (SSet.Rezk.spinePrefixVertexLeft.{u} n r h hrpos).op =
        edge ≫ (discreteSourceMapping W).map
          (SSet.Rezk.spinePrefixVertexRight.{u} n r h).op := by
        apply (cancel_mono
          (spineVertexMappingIso W n r (Nat.le_of_succ_le h)).hom).mp
        rw [Category.assoc, spinePrefixMappingCospan_left,
          ← Category.assoc, ← edgeProjection_last, hq,
          Category.assoc, spinePrefixMappingCospan_right]
        dsimp only [edge]
        rw [Category.assoc, Iso.inv_hom_id_assoc]
        have hj : r - 1 + 1 < r + 1 := by omega
        have last_eq : (⟨r - 1 + 1, hj⟩ : Fin (r + 1)) = Fin.last r := by
          apply Fin.ext
          dsimp
          omega
        have cast_eq : (⟨r - 1, by omega⟩ : Fin r).castSucc =
            (⟨r - 1, by omega⟩ : Fin (r + 1)) := by rfl
        simpa only [old, cast_eq, last_eq, SimplicialObject.δ_def] using ha (r - 1) hj
      let sq := spinePrefixMapping_isPullback W n r h hrpos
      refine ⟨sq.lift q edge hs, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [← edgeProjection_right, ← Category.assoc, IsPullback.lift_snd]
        dsimp only [edge]
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · rw [← edgeProjection_left, ← Category.assoc, IsPullback.lift_fst, hq]


/-- The finite prefix gluing map is chosen only from its internally proved universal property. -/
def prefixLift (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) {Z : SSet.{u}}
    (a : Fin r → (Z ⟶ W.diagram _⦋1⦌)) (ha : Adjacent a) :
    Z ⟶ prefixObject W n r h :=
  (exists_prefixLift W n r h hr a ha).choose


/-- Every labelled restriction of that SAME internal lift is its original supplied edge. -/
theorem prefixLift_edge (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) {Z : SSet.{u}}
    (a : Fin r → (Z ⟶ W.diagram _⦋1⦌)) (ha : Adjacent a) (i : Fin r) :
    prefixLift W n r h hr a ha ≫ edgeProjection W n r h i = a i :=
  (exists_prefixLift W n r h hr a ha).choose_spec i


/-- An actual original edge family has exactly one gluing map into the nonempty prefix. -/
theorem prefixLift_unique (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) {Z : SSet.{u}}
    (a : Fin r → (Z ⟶ W.diagram _⦋1⦌)) (ha : Adjacent a)
    (q : Z ⟶ prefixObject W n r h)
    (hq : ∀ i, q ≫ edgeProjection W n r h i = a i) :
    q = prefixLift W n r h hr a ha := by
  apply edgeProjection_hom_ext W n r h hr
  intro i
  exact (hq i).trans (prefixLift_edge W n r h hr a ha i).symm

end SimplicialSpace.FixedTupleSpinePrefix
