/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder

/-!
# Dimension-controlled simplicial mapping cylinders

The small cylinder retains the entire target and copied barycentric source.
Mixed faces have cardinality at most one more than the source-face bound.
Finite increasing-cardinality transfers give a jointly continuous deformation
fixing every target point, with finite-face support control.
-/

public section

noncomputable section
set_option autoImplicit false

open Topology CategoryTheory PreAbstractSimplicialComplex
open scoped Classical unitInterval

universe u v w

namespace PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder

variable {V : Type v} {W : Type w}
variable {P : PreAbstractSimplicialComplex V} {Q : PreAbstractSimplicialComplex W}

/-- The dimension-controlled mapping cylinder of `f`: the faces `s` of `MappingCylinder.complex f`
whose target labels `s.toRight` lie in `f.faceImage a` for every source face `a` in `s.toLeft`. -/
def smallCylinder (f : Morphism P Q) :
    PreAbstractSimplicialComplex (Face P ⊕ W) where
  faces := {s | s ∈ MappingCylinder.complex f ∧
    ∀ a ∈ s.toLeft, s.toRight ⊆ (f.faceImage a).val}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((MappingCylinder.complex f).isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    refine ⟨((MappingCylinder.complex f).isRelLowerSet_faces hs.1).2 hts ht, ?_⟩
    intro a ha
    exact (Finset.toRight_subset_toRight hts).trans
      (hs.2 a (Finset.toLeft_subset_toLeft hts ha))

theorem smallCylinder_le (f : Morphism P Q) :
    smallCylinder f ≤ MappingCylinder.complex f := fun _ h => h.1

private theorem small_target_face (f : Morphism P Q) (s : Face Q) :
    (∅ : Finset (Face P)).disjSum s.val ∈ smallCylinder f := by
  refine ⟨MappingCylinder.target_face_mem f s, ?_⟩
  simp only [Finset.toLeft_disjSum, Finset.notMem_empty, false_implies, implies_true]

private theorem small_domain_face (f : Morphism P Q)
    (s : Face (barycentricSubdivision P)) :
    s.val.disjSum (∅ : Finset W) ∈ smallCylinder f := by
  refine ⟨MappingCylinder.domain_face_mem f s, ?_⟩
  simp only [Finset.toRight_disjSum, Finset.empty_subset, implies_true]

theorem small_target_le (f : Morphism P Q) :
    MappingCylinder.targetComplex P Q ≤ smallCylinder f := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h := small_target_face f ⟨a, ha⟩
  rw [Finset.empty_disjSum, Finset.map_eq_image] at h
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ smallCylinder f
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ smallCylinder f at h
  exact h

theorem small_domain_le (f : Morphism P Q) :
    MappingCylinder.domainComplex P W ≤ smallCylinder f := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h := small_domain_face f ⟨a, ha⟩
  rw [Finset.disjSum_empty, Finset.map_eq_image] at h
  change a.image (Function.Embedding.inl : Face P ↪ Face P ⊕ W) ∈ smallCylinder f
  change a.image (Function.Embedding.inl : Face P ↪ Face P ⊕ W) ∈ smallCylinder f at h
  exact h

private theorem faceImage_card_le (f : Morphism P Q) (a : Face P) :
    (f.faceImage a).val.card ≤ a.val.card := by
  change ((faceVertices P a).image (fun z => (f.vertexMap z).val)).card ≤ _
  exact (Finset.card_image_le).trans_eq (faceVertices_card P a)

/-- Every mixed face has at most `M + 1` vertices when source faces have at most `M`. -/
theorem small_mixed_face_card_le (f : Morphism P Q) (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (s : Face (smallCylinder f)) (hc : s.val.toLeft.Nonempty) :
    s.val.card ≤ M + 1 := by
  let c : Face (barycentricSubdivision P) :=
    ⟨s.val.toLeft, hc, s.property.1.2.1⟩
  let e := OrderComplex.faceEnumeration c
  let k (i : Fin (c.val.card - 1 + 1)) : ℕ := (e i).val.val.card
  have hk : StrictMono k := by
    intro i j hij
    exact Finset.card_lt_card (e.strictMono hij)
  have hchain (i : Fin (c.val.card - 1 + 1)) : i.val + k 0 ≤ k i := by
    refine Fin.induction ?_ ?_ i
    · simpa only [Fin.val_zero, zero_add] using (Nat.le_refl (k 0))
    · intro j hj
      have hstep := hk (Fin.castSucc_lt_succ (i := j))
      change j.val + k 0 ≤ k j.castSucc at hj
      change j.val + 1 + k 0 ≤ k j.succ
      omega
  have hlast : k (Fin.last (c.val.card - 1)) ≤ M :=
    hP (e (Fin.last (c.val.card - 1))).val
  have hright : s.val.toRight.card ≤ k 0 := by
    exact (Finset.card_le_card
      (s.property.2 (e 0).val (e 0).property)).trans (faceImage_card_le f (e 0).val)
  have hlength : c.val.card - 1 + 1 = c.val.card := by
    have hpos : 0 < c.val.card := Finset.card_pos.mpr hc
    omega
  have hbound := hchain (Fin.last (c.val.card - 1))
  change c.val.card - 1 + k 0 ≤ k (Fin.last (c.val.card - 1)) at hbound
  have hsum := Finset.card_toLeft_add_card_toRight (u := s.val)
  change c.val.card + s.val.toRight.card = s.val.card at hsum
  omega

theorem small_all_face_card_le (f : Morphism P Q) (M N : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (hQ : ∀ a : Face Q, a.val.card ≤ N) (s : Face (smallCylinder f)) :
    s.val.card ≤ max (M + 1) N := by
  by_cases hc : s.val.toLeft.Nonempty
  · exact (small_mixed_face_card_le f M hP s hc).trans (le_max_left _ _)
  · have hempty : s.val.toLeft = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
    have hr : s.val.toRight ∈ Q := by
      have h := s.property.1.2.2
      simpa only [MappingCylinder.hull, hempty, Finset.biUnion_empty, Finset.union_empty] using h
    have hcard : s.val.card = s.val.toRight.card := by
      have h := Finset.card_toLeft_add_card_toRight (u := s.val)
      simpa only [hempty, Finset.card_empty, zero_add] using h.symm
    rw [hcard]
    exact (hQ ⟨s.val.toRight, hr⟩).trans (le_max_right _ _)

private def cylinderStage (f : Morphism P Q) (k : ℕ) :
    PreAbstractSimplicialComplex (Face P ⊕ W) where
  faces := {s | s ∈ smallCylinder f ∧ ∀ a ∈ s.toLeft, k ≤ a.val.card}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((smallCylinder f).isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    refine ⟨((smallCylinder f).isRelLowerSet_faces hs.1).2 hts ht, ?_⟩
    intro a ha
    exact hs.2 a (Finset.toLeft_subset_toLeft hts ha)

private theorem cylinderStage_le_small (f : Morphism P Q) (k : ℕ) :
    cylinderStage f k ≤ smallCylinder f := fun _ h => h.1

private theorem cylinderStage_mono (f : Morphism P Q) (k : ℕ) :
    cylinderStage f (k + 1) ≤ cylinderStage f k := by
  intro s hs
  exact ⟨hs.1, fun a ha => (Nat.le_succ k).trans (hs.2 a ha)⟩

private theorem cylinderStage_one (f : Morphism P Q) :
    cylinderStage f 1 = smallCylinder f := by
  apply le_antisymm (cylinderStage_le_small f 1)
  intro s hs
  refine ⟨hs, ?_⟩
  intro a _
  exact Finset.card_pos.mpr (P.isRelLowerSet_faces a.property).1

private theorem cylinderStage_target_le (f : Morphism P Q) (k : ℕ) :
    MappingCylinder.targetComplex P Q ≤ cylinderStage f k := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h : (∅ : Finset (Face P)).disjSum a ∈ cylinderStage f k := by
    refine ⟨small_target_face f ⟨a, ha⟩, ?_⟩
    simp only [Finset.toLeft_disjSum]
    intro b hb
    exact (Finset.notMem_empty b hb).elim
  rw [Finset.empty_disjSum, Finset.map_eq_image] at h
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ cylinderStage f k
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ cylinderStage f k at h
  exact h

private theorem cylinderStage_final (f : Morphism P Q) (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M) :
    cylinderStage f (M + 1) = MappingCylinder.targetComplex P Q := by
  apply le_antisymm
  · intro s hs
    have hc : s.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hlow := hs.2 a ha
      have hhigh := hP a
      omega
    have hr : s.toRight ∈ Q := by
      have h := hs.1.1.2.2
      simpa only [MappingCylinder.hull, hc, Finset.biUnion_empty, Finset.union_empty] using h
    refine ⟨s.toRight, hr, ?_⟩
    have hsum := Finset.toLeft_disjSum_toRight (u := s)
    rw [hc, Finset.empty_disjSum] at hsum
    simpa only [← Finset.map_eq_image] using hsum
  · exact cylinderStage_target_le f (M + 1)


/- Coordinate transfers eliminate one source-face cardinality at each step,
fixing the remaining copied faces and the entire target. -/

private theorem copied_le_of_card_le
    (C : Finset (Face P)) (hC : IsChain (· ≤ ·) (C : Set (Face P)))
    {a b : Face P} (ha : a ∈ C) (hb : b ∈ C)
    (hcard : a.val.card ≤ b.val.card) : a ≤ b := by
  rcases hC.total ha hb with hab | hba
  · exact hab
  · have hEq : b = a := Subtype.ext (Finset.eq_of_subset_of_card_le hba hcard)
    subst b
    exact le_rfl

private def transferCopies (k : ℕ) (s : Finset (Face P ⊕ W)) : Finset (Face P) :=
  s.toLeft.filter (fun a => a.val.card = k)

private def transferRight (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) : Finset W :=
  s.toRight ∪ (transferCopies k s).biUnion (fun a => (f.faceImage a).val)

private def transferCarrierVal (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) : Finset (Face P ⊕ W) :=
  s.toLeft.disjSum (transferRight f k s)

private theorem transferCarrier_contains (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) : s ⊆ transferCarrierVal f k s := by
  intro z hz
  cases z with
  | inl a =>
      have ha : a ∈ s.toLeft := Finset.mem_toLeft.mpr hz
      simpa only [transferCarrierVal, Finset.inl_mem_disjSum] using ha
  | inr b =>
      have hb : b ∈ transferRight f k s :=
        Finset.mem_union_left _ (Finset.mem_toRight.mpr hz)
      simpa only [transferCarrierVal, Finset.inr_mem_disjSum] using hb

private theorem transferCarrier_hull (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) :
    MappingCylinder.hull f (transferCarrierVal f k s) = MappingCylinder.hull f s := by
  apply Finset.Subset.antisymm
  · rw [transferCarrierVal, MappingCylinder.hull_disjSum]
    intro b hb
    change b ∈ s.toRight ∪ s.toLeft.biUnion (fun a => (f.faceImage a).val)
    rcases Finset.mem_union.mp hb with hb | hb
    · change b ∈ s.toRight ∪ (transferCopies k s).biUnion (fun a => (f.faceImage a).val) at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union_left _ hb
      · rcases Finset.mem_biUnion.mp hb with ⟨a, ha, hba⟩
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, (Finset.mem_filter.mp ha).1, hba⟩)
    · exact Finset.mem_union_right _ hb
  · exact MappingCylinder.hull_mono f (transferCarrier_contains f k s)

private def transferCarrier (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) : Face (cylinderStage f k) := by
  have hne : (transferCarrierVal f k s.val).Nonempty :=
    ((MappingCylinder.complex f).isRelLowerSet_faces s.property.1.1).1.mono
      (transferCarrier_contains f k s.val)
  have hchain : IsChain (· ≤ ·) (s.val.toLeft : Set (Face P)) :=
    s.property.1.1.2.1
  refine ⟨transferCarrierVal f k s.val, ⟨⟨hne, ?_, ?_⟩, ?_⟩, ?_⟩
  · simpa only [transferCarrierVal, Finset.toLeft_disjSum] using hchain
  · rw [transferCarrier_hull]
    exact s.property.1.1.2.2
  · intro b hb
    rw [transferCarrierVal, Finset.toLeft_disjSum] at hb
    rw [transferCarrierVal, Finset.toRight_disjSum]
    apply Finset.union_subset
    · exact s.property.1.2 b hb
    · intro w hw
      rcases Finset.mem_biUnion.mp hw with ⟨a, ha, hwa⟩
      have haC : a ∈ s.val.toLeft := (Finset.mem_filter.mp ha).1
      have haK : a.val.card = k := (Finset.mem_filter.mp ha).2
      have hab : a ≤ b := copied_le_of_card_le s.val.toLeft hchain haC hb
        (haK ▸ s.property.2 b hb)
      exact MappingCylinder.faceImage_mono f hab hwa
  · intro a ha
    rw [transferCarrierVal, Finset.toLeft_disjSum] at ha
    exact s.property.2 a ha

private def transferLabel (f : Morphism P Q) (k : ℕ)
    (z : Face P ⊕ W) : Convexity.StdSimplex ℝ (Face P ⊕ W) :=
  match z with
  | Sum.inl a =>
      if a.val.card = k then
        (MappingCylinder.leftPoint f a).point.map (Sum.inr : W → Face P ⊕ W)
      else Convexity.StdSimplex.single (Sum.inl a)
  | Sum.inr b => Convexity.StdSimplex.single (Sum.inr b)

private def transferPoint (f : Morphism P Q) (k : ℕ)
    (p : Convexity.StdSimplex ℝ (Face P ⊕ W)) :
    Convexity.StdSimplex ℝ (Face P ⊕ W) :=
  p.iConvexComb (transferLabel f k)

private theorem transferLabel_support (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (z : Face P ⊕ W) (hz : z ∈ s.val) :
    (transferLabel f k z).weights.support ⊆ (transferCarrier f k s).val := by
  cases z with
  | inl a =>
      by_cases ha : a.val.card = k
      · rw [transferLabel, ite_eq_left ha]
        intro z hz'
        rw [Convexity.StdSimplex.weights_map] at hz'
        rcases Finset.mem_image.mp (Finsupp.mapDomain_support hz') with ⟨b, hb, rfl⟩
        have hcopy : a ∈ transferCopies k s.val :=
          Finset.mem_filter.mpr ⟨Finset.mem_toLeft.mpr hz, ha⟩
        have hright : b ∈ transferRight f k s.val :=
          Finset.mem_union_right _
            (Finset.mem_biUnion.mpr
              ⟨a, hcopy, MappingCylinder.leftPoint_support f a hb⟩)
        simpa only [transferCarrier, transferCarrierVal, Finset.inr_mem_disjSum] using hright
      · rw [transferLabel, ite_eq_right ha]
        rw [show (Convexity.StdSimplex.single (Sum.inl a)).weights.support = {Sum.inl a} from
          Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl]
        exact Finset.singleton_subset_iff.mpr (transferCarrier_contains f k s.val hz)
  | inr b =>
      change (Convexity.StdSimplex.single (Sum.inr b)).weights.support ⊆ _
      rw [show (Convexity.StdSimplex.single (Sum.inr b)).weights.support = {Sum.inr b} from
        Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl]
      exact Finset.singleton_subset_iff.mpr (transferCarrier_contains f k s.val hz)

private theorem mixture_support_subset {A : Type*}
    (p : Convexity.StdSimplex ℝ A) (q : A → Convexity.StdSimplex ℝ A)
    (S : Finset A) (hq : ∀ a ∈ p.weights.support, (q a).weights.support ⊆ S) :
    (p.iConvexComb q).weights.support ⊆ S := by
  intro b hb
  by_contra hbs
  have hzero : (p.iConvexComb q).weights b = 0 := by
    rw [Convexity.StdSimplex.weights_iConvexComb, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hqb : (q a).weights b = 0 := by
      by_contra h
      exact hbs (hq a ha (Finsupp.mem_support_iff.mpr h))
    simp only [Finsupp.smul_apply, hqb, smul_zero]
  exact (Finsupp.mem_support_iff.mp hb) hzero

private theorem transferPoint_support (f : Morphism P Q) (k : ℕ)
    (x : (cylinderStage f k).Realization) :
    (transferPoint f k x.point).weights.support ⊆
      (transferCarrier f k ⟨x.point.weights.support, x.support_mem⟩).val :=
  mixture_support_subset x.point (transferLabel f k) _
    (fun a ha => transferLabel_support f k ⟨x.point.weights.support, x.support_mem⟩ a ha)

private theorem inrPoint_left_zero (p : Convexity.StdSimplex ℝ W) (a : Face P) :
    (p.map (Sum.inr : W → Face P ⊕ W)).weights (Sum.inl a) = 0 := by
  rw [Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

private theorem transferLabel_left_weight (f : Morphism P Q) (k : ℕ)
    (z : Face P ⊕ W) (a : Face P) :
    (transferLabel f k z).weights (Sum.inl a) =
      if a.val.card = k then 0 else
        (Convexity.StdSimplex.single z).weights (Sum.inl a) := by
  cases z with
  | inl b =>
      by_cases hb : b.val.card = k
      · simp only [transferLabel, hb, ite_eq_left, inrPoint_left_zero]
        by_cases ha : a.val.card = k
        · simp only [ha, ite_eq_left]
        · have hab : b ≠ a := fun h => ha (h ▸ hb)
          simp only [ha, Convexity.StdSimplex.weights_single,
            Finsupp.single_apply, Sum.inl.injEq, hab, ite_false]
      · simp only [transferLabel, hb]
        by_cases ha : a.val.card = k
        · have hab : b ≠ a := fun h => hb (h.symm ▸ ha)
          simp only [ha, ite_eq_left, Convexity.StdSimplex.weights_single,
            Finsupp.single_apply, Sum.inl.injEq, hab, ite_false]
        · simp only [ha, ite_false]
  | inr b =>
      simp only [transferLabel, Convexity.StdSimplex.weights_single,
        Finsupp.single_apply, Sum.inr_ne_inl, ite_false, ite_self]

private theorem transferPoint_left_weight (f : Morphism P Q) (k : ℕ)
    (p : Convexity.StdSimplex ℝ (Face P ⊕ W)) (a : Face P) :
    (transferPoint f k p).weights (Sum.inl a) =
      if a.val.card = k then 0 else p.weights (Sum.inl a) := by
  by_cases ha : a.val.card = k
  · rw [transferPoint, Convexity.StdSimplex.weights_iConvexComb, Finsupp.sum_apply]
    simp [transferLabel_left_weight, ha, Finsupp.sum]
  · have hmap :
        (transferPoint f k p).weights (Sum.inl a) =
          (p.iConvexComb Convexity.StdSimplex.single).weights (Sum.inl a) := by
      rw [transferPoint, Convexity.StdSimplex.weights_iConvexComb,
        Convexity.StdSimplex.weights_iConvexComb, Finsupp.sum_apply, Finsupp.sum_apply]
      apply Finset.sum_congr rfl
      intro z _
      change (p.weights z • (transferLabel f k z).weights) (Sum.inl a) =
        (p.weights z • (Convexity.StdSimplex.single z).weights) (Sum.inl a)
      rw [Finsupp.smul_apply, Finsupp.smul_apply, transferLabel_left_weight, ite_eq_right ha]
    rw [hmap, Convexity.StdSimplex.iConvexComb_single, ite_eq_right ha]

private def transferRealization (f : Morphism P Q) (k : ℕ)
    (x : (cylinderStage f k).Realization) :
    (cylinderStage f (k + 1)).Realization where
  point := transferPoint f k x.point
  support_mem := by
    have hcarrier := transferPoint_support f k x
    have hsmall : (transferPoint f k x.point).weights.support ∈ smallCylinder f :=
      ((smallCylinder f).isRelLowerSet_faces
        (transferCarrier f k ⟨x.point.weights.support, x.support_mem⟩).property.1).2
        hcarrier (transferPoint f k x.point).support_weights_nonempty
    refine ⟨hsmall, ?_⟩
    intro a ha
    have haLeft : Sum.inl a ∈ (transferPoint f k x.point).weights.support :=
      Finset.mem_toLeft.mp ha
    have haOld : a ∈ x.point.weights.support.toLeft := by
      have h := hcarrier haLeft
      simpa only [transferCarrier, transferCarrierVal, Finset.inl_mem_disjSum,
          Finset.inr_mem_disjSum] using h
    have hlow : k ≤ a.val.card := x.support_mem.2 a haOld
    have hne : a.val.card ≠ k := by
      intro heq
      have hzero := transferPoint_left_weight f k x.point a
      rw [ite_eq_left heq] at hzero
      exact (Finsupp.mem_support_iff.mp haLeft) hzero
    omega

private theorem transferRealization_fixed (f : Morphism P Q) (k : ℕ)
    (x : (cylinderStage f (k + 1)).Realization) :
    transferRealization f k (Realization.inclusion (cylinderStage_mono f k) x) = x := by
  apply Realization.ext
  change x.point.iConvexComb (transferLabel f k) = x.point
  calc
    x.point.iConvexComb (transferLabel f k) =
        x.point.iConvexComb Convexity.StdSimplex.single := by
      apply Convexity.iConvexComb_congr
      intro z hz
      cases z with
      | inl a =>
          have ha : a ∈ x.point.weights.support.toLeft :=
            Finset.mem_toLeft.mpr (Finsupp.mem_support_iff.mpr hz)
          have hcard := x.support_mem.2 a ha
          have hne : a.val.card ≠ k := by omega
          simp only [transferLabel, hne, ite_false]
      | inr b => rfl
    _ = x.point := Convexity.StdSimplex.iConvexComb_single x.point

private def labelRetraction (f : Morphism P Q) (z : Face P ⊕ W) :
    Convexity.StdSimplex ℝ W :=
  match z with
  | Sum.inl a => (MappingCylinder.leftPoint f a).point
  | Sum.inr b => Convexity.StdSimplex.single b

private def rawRetraction (f : Morphism P Q)
    (p : Convexity.StdSimplex ℝ (Face P ⊕ W)) : Convexity.StdSimplex ℝ W :=
  p.iConvexComb (labelRetraction f)

private theorem rawRetraction_existing (f : Morphism P Q)
    (x : (MappingCylinder.complex f).Realization) :
    rawRetraction f x.point = MappingCylinder.retractionPoint f x := by
  rw [rawRetraction, ← Realization.map_vertexCoordinates x, Convexity.iConvexComb_map]
  change (Realization.vertexCoordinates x).iConvexComb
      (fun z => labelRetraction f z.val) =
    (Realization.vertexCoordinates x).iConvexComb
      (fun z => (MappingCylinder.vertexPoint f z).point)
  apply Convexity.iConvexComb_congr
  rintro ⟨z, hz⟩ _
  cases z <;> rfl

private theorem rawRetraction_inr (f : Morphism P Q) (p : Convexity.StdSimplex ℝ W) :
    rawRetraction f (p.map (Sum.inr : W → Face P ⊕ W)) = p := by
  rw [rawRetraction, Convexity.iConvexComb_map]
  exact Convexity.StdSimplex.iConvexComb_single p

private theorem rawRetraction_transferLabel (f : Morphism P Q) (k : ℕ)
    (z : Face P ⊕ W) :
    rawRetraction f (transferLabel f k z) = labelRetraction f z := by
  cases z with
  | inl a =>
      by_cases ha : a.val.card = k
      · simp only [transferLabel, ha, ite_eq_left, rawRetraction_inr, labelRetraction]
      · simp only [transferLabel, ha, ite_false, rawRetraction,
          Convexity.iConvexComb_single, labelRetraction]
  | inr b =>
      simp only [transferLabel, rawRetraction, Convexity.iConvexComb_single, labelRetraction]

private theorem rawRetraction_transferPoint (f : Morphism P Q) (k : ℕ)
    (p : Convexity.StdSimplex ℝ (Face P ⊕ W)) :
    rawRetraction f (transferPoint f k p) = rawRetraction f p := by
  rw [rawRetraction, transferPoint, ← Convexity.iConvexComb_assoc]
  change p.iConvexComb (fun z => rawRetraction f (transferLabel f k z)) =
    p.iConvexComb (labelRetraction f)
  apply Convexity.iConvexComb_congr
  intro z _
  exact rawRetraction_transferLabel f k z

/- Continuity is proved on finite closed-face charts and then on the ordinary
interval product of the weak cylinder. The target can be an arbitrary weak polyhedron. -/

private def endCarrierVal (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) : Finset (Face P ⊕ W) :=
  (s.toLeft.filter (fun a => a.val.card ≠ k)).disjSum (transferRight f k s)

private theorem endCarrier_subset (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) :
    endCarrierVal f k s ⊆ transferCarrierVal f k s := by
  intro z hz
  cases z with
  | inl a =>
      have ha : a ∈ s.toLeft.filter (fun a => a.val.card ≠ k) := by
        simpa only [endCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using hz
      have ha' := (Finset.mem_filter.mp ha).1
      simpa only [transferCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using ha'
  | inr b =>
      have hb : b ∈ transferRight f k s := by
        simpa only [endCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using hz
      simpa only [transferCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using hb

private theorem transferLabel_support_end (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (z : Face P ⊕ W) (hz : z ∈ s.val) :
    (transferLabel f k z).weights.support ⊆ endCarrierVal f k s.val := by
  intro b hb
  have hcarrier := transferLabel_support f k s z hz hb
  cases b with
  | inl a =>
      have ha : a ∈ s.val.toLeft := by
        simpa only [transferCarrier, transferCarrierVal, Finset.inl_mem_disjSum,
            Finset.inr_mem_disjSum] using hcarrier
      have hne : a.val.card ≠ k := by
        intro h
        have hzero := transferLabel_left_weight f k z a
        rw [ite_eq_left h] at hzero
        exact (Finsupp.mem_support_iff.mp hb) hzero
      have ha' : a ∈ s.val.toLeft.filter (fun a => a.val.card ≠ k) :=
        Finset.mem_filter.mpr ⟨ha, hne⟩
      simpa only [endCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using ha'
  | inr a =>
      have ha : a ∈ transferRight f k s.val := by
        simpa only [transferCarrier, transferCarrierVal, Finset.inl_mem_disjSum,
            Finset.inr_mem_disjSum] using hcarrier
      simpa only [endCarrierVal, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using ha

private def endCarrier (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) : Face (cylinderStage f (k + 1)) := by
  let hnonempty := ((cylinderStage f k).isRelLowerSet_faces s.property).1
  let z := Classical.choose hnonempty
  have hz : z ∈ s.val := Classical.choose_spec hnonempty
  have hne : (endCarrierVal f k s.val).Nonempty :=
    (transferLabel f k z).support_weights_nonempty.mono
      (transferLabel_support_end f k s z hz)
  have hsmall : endCarrierVal f k s.val ∈ smallCylinder f :=
    ((smallCylinder f).isRelLowerSet_faces (transferCarrier f k s).property.1).2
      (endCarrier_subset f k s.val) hne
  refine ⟨endCarrierVal f k s.val, hsmall, ?_⟩
  intro a ha
  have hfilter : a ∈ s.val.toLeft.filter (fun a => a.val.card ≠ k) := by
    simpa only [endCarrierVal, Finset.toLeft_disjSum] using ha
  have haOld := (Finset.mem_filter.mp hfilter).1
  have hneK := (Finset.mem_filter.mp hfilter).2
  have hlow := s.property.2 a haOld
  omega

private def transferVertex (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (a : s.val) :
    (cylinderStage f (k + 1)).Realization :=
  transferRealization f k
    (Realization.vertex (cylinderStage f k) a.val
      (singleton_mem_of_face (cylinderStage f k) s a.property))

private theorem transferVertex_point (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (a : s.val) :
    (transferVertex f k s a).point = transferLabel f k a.val :=
  Convexity.iConvexComb_single a.val (transferLabel f k)

private def transferFaceCoordinates (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) :
    Convexity.ConvexSpace.AffineMap ℝ (Convexity.StdSimplex ℝ s.val)
      (Convexity.StdSimplex ℝ (endCarrier f k s).val) :=
  Convexity.StdSimplex.affineMapMk (fun a : s.val =>
    MappingCylinder.pointInFace (endCarrier f k s) (transferVertex f k s a)
      (by
        rw [transferVertex_point]
        exact transferLabel_support_end f k s a.val a.property))

private theorem transferFaceCoordinates_point (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (q : Convexity.StdSimplex ℝ s.val) :
    (transferFaceCoordinates f k s q).map
        (Subtype.val : (endCarrier f k s).val → Face P ⊕ W) =
      (transferRealization f k (Realization.faceMap (cylinderStage f k) s q)).point := by
  change (q.iConvexComb _ : Convexity.StdSimplex ℝ (endCarrier f k s).val).map _ =
    (q.map (Subtype.val : s.val → Face P ⊕ W)).iConvexComb (transferLabel f k)
  rw [Convexity.map_iConvexComb, Convexity.iConvexComb_map]
  apply Convexity.iConvexComb_congr
  intro a _
  have h := congrArg Realization.point
    (MappingCylinder.pointInFace_map (endCarrier f k s) (transferVertex f k s a)
      (by
        rw [transferVertex_point]
        exact transferLabel_support_end f k s a.val a.property))
  exact h.trans (transferVertex_point f k s a)

private theorem continuous_transferFaceCoordinates (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) :
    Continuous (transferFaceCoordinates f k s) :=
  Realization.continuous_finite_mixture _

private theorem transfer_faceMap (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) (q : Convexity.StdSimplex ℝ s.val) :
    transferRealization f k (Realization.faceMap (cylinderStage f k) s q) =
      Realization.faceMap (cylinderStage f (k + 1)) (endCarrier f k s)
        (transferFaceCoordinates f k s q) :=
  Realization.ext (transferFaceCoordinates_point f k s q).symm

private theorem continuous_transferRealization (f : Morphism P Q) (k : ℕ) :
    Continuous (transferRealization f k) := by
  rw [Realization.continuous_iff]
  intro s
  have h : transferRealization f k ∘ Realization.faceMap (cylinderStage f k) s =
      Realization.faceMap (cylinderStage f (k + 1)) (endCarrier f k s) ∘
        transferFaceCoordinates f k s := funext (transfer_faceMap f k s)
  rw [h]
  exact (Realization.continuous_faceMap _ _).comp (continuous_transferFaceCoordinates f k s)

private def transferMap (f : Morphism P Q) (k : ℕ) :
    C((cylinderStage f k).Realization, (cylinderStage f (k + 1)).Realization) :=
  ⟨transferRealization f k, continuous_transferRealization f k⟩

private def carrierSourceEmbedding (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) : s.val ↪ (transferCarrier f k s).val where
  toFun a := ⟨a.val, transferCarrier_contains f k s.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun z : (transferCarrier f k s).val => z.val) h

private def carrierEndEmbedding (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) :
    (endCarrier f k s).val ↪ (transferCarrier f k s).val where
  toFun a := ⟨a.val, endCarrier_subset f k s.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun z : (transferCarrier f k s).val => z.val) h

private def transferHomotopyCoordinates (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k))
    (p : unitInterval × Convexity.StdSimplex ℝ s.val) :
    Convexity.StdSimplex ℝ (transferCarrier f k s).val :=
  Realization.segmentPoint p.1 (p.2.map (carrierSourceEmbedding f k s))
    ((transferFaceCoordinates f k s p.2).map (carrierEndEmbedding f k s))

private theorem transferHomotopyCoordinates_point (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k))
    (p : unitInterval × Convexity.StdSimplex ℝ s.val) :
    (transferHomotopyCoordinates f k s p).map
      (Subtype.val : (transferCarrier f k s).val → Face P ⊕ W) =
      Realization.segmentPoint p.1 (Realization.faceMap (cylinderStage f k) s p.2).point
        (transferRealization f k (Realization.faceMap (cylinderStage f k) s p.2)).point := by
  rw [transferHomotopyCoordinates, MappingCylinder.map_segmentPoint]
  have hleft : (p.2.map (carrierSourceEmbedding f k s)).map Subtype.val =
      (Realization.faceMap (cylinderStage f k) s p.2).point := by
    rw [Convexity.StdSimplex.map_map]
    rfl
  have hright : ((transferFaceCoordinates f k s p.2).map (carrierEndEmbedding f k s)).map
      Subtype.val = (transferRealization f k
        (Realization.faceMap (cylinderStage f k) s p.2)).point := by
    rw [Convexity.StdSimplex.map_map]
    exact transferFaceCoordinates_point f k s p.2
  rw [hleft, hright]

private theorem continuous_transferHomotopyCoordinates (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k)) :
    Continuous (transferHomotopyCoordinates f k s) := by
  have hleft : Continuous (fun p : unitInterval × Convexity.StdSimplex ℝ s.val =>
      p.2.map (carrierSourceEmbedding f k s)) :=
    (Convexity.StdSimplex.continuous_map ℝ _).comp continuous_snd
  have hright : Continuous (fun p : unitInterval × Convexity.StdSimplex ℝ s.val =>
      (transferFaceCoordinates f k s p.2).map (carrierEndEmbedding f k s)) :=
    (Convexity.StdSimplex.continuous_map ℝ _).comp
      ((continuous_transferFaceCoordinates f k s).comp continuous_snd)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (transferCarrier f k s).val).continuous_iff.mpr
  apply continuous_pi
  intro a
  simp only [transferHomotopyCoordinates, Realization.segmentPoint_weights,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Function.comp_apply]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((Convexity.StdSimplex.continuous_weights_apply ℝ a).comp hleft)).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ a).comp hright))

private def transferHomotopyPoint (f : Morphism P Q) (k : ℕ)
    (p : unitInterval × (cylinderStage f k).Realization) :
    (cylinderStage f k).Realization where
  point := Realization.segmentPoint p.1 p.2.point (transferPoint f k p.2.point)
  support_mem := by
    classical
    let : DecidableEq (Face P ⊕ W) := Classical.decEq _
    let s : Face (cylinderStage f k) := ⟨p.2.point.weights.support, p.2.support_mem⟩
    apply ((cylinderStage f k).isRelLowerSet_faces (transferCarrier f k s).property).2
    · exact (Realization.segmentPoint_support_subset _ _ _).trans
        (Finset.union_subset (transferCarrier_contains f k s.val) (transferPoint_support f k p.2))
    · exact (Realization.segmentPoint _ _ _).support_weights_nonempty

private theorem transferHomotopyPoint_faceMap (f : Morphism P Q) (k : ℕ)
    (s : Face (cylinderStage f k))
    (p : unitInterval × Convexity.StdSimplex ℝ s.val) :
    transferHomotopyPoint f k (p.1, Realization.faceMap (cylinderStage f k) s p.2) =
      Realization.faceMap (cylinderStage f k) (transferCarrier f k s)
        (transferHomotopyCoordinates f k s p) :=
  Realization.ext (transferHomotopyCoordinates_point f k s p).symm

private theorem continuous_transferHomotopyPoint (f : Morphism P Q) (k : ℕ) :
    Continuous (transferHomotopyPoint f k) :=
  MappingCylinder.continuous_interval_product (cylinderStage f k) (transferHomotopyPoint f k)
    (fun s => by
      have h : (fun p : unitInterval × Convexity.StdSimplex ℝ s.val =>
          transferHomotopyPoint f k (p.1, Realization.faceMap (cylinderStage f k) s p.2)) =
          Realization.faceMap (cylinderStage f k) (transferCarrier f k s) ∘
            transferHomotopyCoordinates f k s :=
        funext (transferHomotopyPoint_faceMap f k s)
      rw [h]
      exact (Realization.continuous_faceMap _ _).comp
        (continuous_transferHomotopyCoordinates f k s))

private def transferDeformation (f : Morphism P Q) (k : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (cylinderStage f k).Realization)
      ((⟨Realization.inclusion (cylinderStage_mono f k),
        Realization.continuous_inclusion (cylinderStage_mono f k)⟩ : C(_, _)).comp
          (transferMap f k))
      (Set.range (Realization.inclusion (cylinderStage_mono f k))) where
  toFun := transferHomotopyPoint f k
  continuous_toFun := continuous_transferHomotopyPoint f k
  map_zero_left x :=
    Realization.ext (Realization.segmentPoint_zero x.point (transferPoint f k x.point))
  map_one_left x :=
    Realization.ext (Realization.segmentPoint_one x.point (transferPoint f k x.point))
  prop' t x hx := by
    rcases hx with ⟨y, rfl⟩
    apply Realization.ext
    change Realization.segmentPoint t y.point (transferPoint f k y.point) = y.point
    have h := congrArg Realization.point (transferRealization_fixed f k y)
    change transferPoint f k y.point = y.point at h
    rw [h]
    exact Realization.segmentPoint_self t y.point

/- The collapse composes increasing-cardinality transfers. An explicit face
bound specifies the number of transfers; for finite source faces a bound is derived. -/

private def realizationEqHomeomorph {A : Type*}
    {T U : PreAbstractSimplicialComplex A} (h : T = U) :
    T.Realization ≃ₜ U.Realization := by
  cases h
  exact Homeomorph.refl _

private theorem realizationEqHomeomorph_point {A : Type*}
    {T U : PreAbstractSimplicialComplex A} (h : T = U) (x : T.Realization) :
    (realizationEqHomeomorph h x).point = x.point := by
  cases h
  rfl

private def smallToStageOne (f : Morphism P Q) :
    C((smallCylinder f).Realization, (cylinderStage f 1).Realization) :=
  ⟨realizationEqHomeomorph (cylinderStage_one f).symm,
    (realizationEqHomeomorph (cylinderStage_one f).symm).continuous⟩

private def stageOneToSmall (f : Morphism P Q) :
    C((cylinderStage f 1).Realization, (smallCylinder f).Realization) :=
  ⟨Realization.inclusion (cylinderStage_le_small f 1),
    Realization.continuous_inclusion (cylinderStage_le_small f 1)⟩

private def oldTargetStage (f : Morphism P Q) (k : ℕ) :
    C(Q.Realization, (cylinderStage f k).Realization) :=
  ⟨fun y => Realization.inclusion (cylinderStage_target_le f k)
      (MappingCylinder.relabelHomeomorph Q Function.Embedding.inr y),
    (Realization.continuous_inclusion (cylinderStage_target_le f k)).comp
      (MappingCylinder.relabelHomeomorph Q Function.Embedding.inr).continuous⟩

private theorem oldTargetStage_point (f : Morphism P Q) (k : ℕ) (y : Q.Realization) :
    (oldTargetStage f k y).point = y.point.map (Sum.inr : W → Face P ⊕ W) :=
  MappingCylinder.relabelMorphism_point Q Function.Embedding.inr y

private theorem transfer_oldTarget (f : Morphism P Q) (k : ℕ) (y : Q.Realization) :
    transferMap f k (oldTargetStage f k y) = oldTargetStage f (k + 1) y := by
  have h : oldTargetStage f k y =
      Realization.inclusion (cylinderStage_mono f k) (oldTargetStage f (k + 1) y) := by
    apply Realization.ext
    rw [oldTargetStage_point]
    exact (oldTargetStage_point f (k + 1) y).symm
  rw [h]
  exact transferRealization_fixed f k _

private theorem transferDeformation_oldTarget (f : Morphism P Q) (k : ℕ)
    (t : unitInterval) (y : Q.Realization) :
    transferDeformation f k (t, oldTargetStage f k y) = oldTargetStage f k y := by
  have h : oldTargetStage f k y =
      Realization.inclusion (cylinderStage_mono f k) (oldTargetStage f (k + 1) y) := by
    apply Realization.ext
    rw [oldTargetStage_point]
    exact (oldTargetStage_point f (k + 1) y).symm
  rw [h]
  exact (transferDeformation f k).eq_fst t (Set.mem_range_self _)

private theorem stage_add_le (f : Morphism P Q) (k r : ℕ) :
    cylinderStage f (k + r) ≤ cylinderStage f k := by
  induction r with
  | zero => exact le_refl _
  | succ r ih => exact (cylinderStage_mono f (k + r)).trans ih

private def stageInto (f : Morphism P Q) (k r : ℕ) :
    C((cylinderStage f (k + r)).Realization, (cylinderStage f k).Realization) :=
  ⟨Realization.inclusion (stage_add_le f k r),
      Realization.continuous_inclusion (stage_add_le f k r)⟩

private theorem stageInto_point (f : Morphism P Q) (k r : ℕ)
    (x : (cylinderStage f (k + r)).Realization) :
    (stageInto f k r x).point = x.point := rfl

private theorem stageInto_target (f : Morphism P Q) (k r : ℕ) (y : Q.Realization) :
    stageInto f k r (oldTargetStage f (k + r) y) = oldTargetStage f k y := by
  apply Realization.ext
  rw [stageInto_point, oldTargetStage_point, oldTargetStage_point]

private def finiteTransfer (f : Morphism P Q) (k : ℕ) :
    (r : ℕ) → C((cylinderStage f k).Realization, (cylinderStage f (k + r)).Realization)
  | 0 => ContinuousMap.id _
  | r + 1 => (transferMap f (k + r)).comp (finiteTransfer f k r)

private theorem finiteTransfer_target (f : Morphism P Q) (k r : ℕ)
    (y : Q.Realization) :
    finiteTransfer f k r (oldTargetStage f k y) = oldTargetStage f (k + r) y := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change transferMap f (k + r) (finiteTransfer f k r (oldTargetStage f k y)) = _
      rw [ih]
      exact transfer_oldTarget f (k + r) y

private def nextTransferHomotopy (f : Morphism P Q) (k r : ℕ) :
    ContinuousMap.Homotopy
      ((stageInto f k r).comp (finiteTransfer f k r))
      ((stageInto f k (r + 1)).comp (finiteTransfer f k (r + 1))) := by
  let H := (ContinuousMap.Homotopy.refl (stageInto f k r)).comp
    ((transferDeformation f (k + r)).toHomotopy.compContinuousMap (finiteTransfer f k r))
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    apply Realization.ext
    rfl
  · apply ContinuousMap.ext
    intro x
    apply Realization.ext
    rfl

private def finiteTransferHomotopy (f : Morphism P Q) (k : ℕ) :
    (r : ℕ) → ContinuousMap.Homotopy (ContinuousMap.id (cylinderStage f k).Realization)
      ((stageInto f k r).comp (finiteTransfer f k r))
  | 0 => (ContinuousMap.Homotopy.refl (ContinuousMap.id _)).cast rfl
      (by
        apply ContinuousMap.ext
        intro x
        apply Realization.ext
        rfl)
  | r + 1 => (finiteTransferHomotopy f k r).trans (nextTransferHomotopy f k r)

private theorem nextTransferHomotopy_target (f : Morphism P Q) (k r : ℕ)
    (t : unitInterval) (y : Q.Realization) :
    nextTransferHomotopy f k r (t, oldTargetStage f k y) = oldTargetStage f k y := by
  change stageInto f k r
    (transferDeformation f (k + r) (t, finiteTransfer f k r (oldTargetStage f k y))) = _
  rw [finiteTransfer_target, transferDeformation_oldTarget, stageInto_target]

private theorem finiteTransferHomotopy_target (f : Morphism P Q) (k r : ℕ)
    (t : unitInterval) (y : Q.Realization) :
    finiteTransferHomotopy f k r (t, oldTargetStage f k y) = oldTargetStage f k y := by
  induction r generalizing t y with
  | zero => rfl
  | succ r ih =>
      rw [finiteTransferHomotopy, ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact ih _ y
      · exact nextTransferHomotopy_target f k r _ y

private def stageRetraction (f : Morphism P Q) (k : ℕ) :
    C((cylinderStage f k).Realization, Q.Realization) :=
  (MappingCylinder.retraction f).comp
    ⟨Realization.inclusion ((cylinderStage_le_small f k).trans (smallCylinder_le f)),
      Realization.continuous_inclusion ((cylinderStage_le_small f k).trans (smallCylinder_le f))⟩

private theorem stageRetraction_point (f : Morphism P Q) (k : ℕ)
    (x : (cylinderStage f k).Realization) :
    (stageRetraction f k x).point = rawRetraction f x.point := by
  change MappingCylinder.retractionPoint f
    (Realization.inclusion ((cylinderStage_le_small f k).trans (smallCylinder_le f)) x) =
      rawRetraction f x.point
  exact (rawRetraction_existing f _).symm

private theorem stageRetraction_transfer (f : Morphism P Q) (k : ℕ)
    (x : (cylinderStage f k).Realization) :
    stageRetraction f (k + 1) (transferMap f k x) = stageRetraction f k x := by
  apply Realization.ext
  rw [stageRetraction_point, stageRetraction_point]
  exact rawRetraction_transferPoint f k x.point

private theorem stageRetraction_finite (f : Morphism P Q) (k r : ℕ)
    (x : (cylinderStage f k).Realization) :
    stageRetraction f (k + r) (finiteTransfer f k r x) = stageRetraction f k x := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change stageRetraction f (k + r + 1)
        (transferMap f (k + r) (finiteTransfer f k r x)) = _
      rw [stageRetraction_transfer]
      exact ih

private theorem finalStage_point (f : Morphism P Q) (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (x : (cylinderStage f (M + 1)).Realization) :
    (stageRetraction f (M + 1) x).point.map (Sum.inr : W → Face P ⊕ W) = x.point := by
  let xT : (MappingCylinder.targetComplex P Q).Realization :=
    ⟨x.point, by
      rw [← cylinderStage_final f M hP]
      exact x.support_mem⟩
  let e := MappingCylinder.relabelHomeomorph Q
    (Function.Embedding.inr : W ↪ Face P ⊕ W)
  let y := e.symm xT
  have hy : y.point.map (Sum.inr : W → Face P ⊕ W) = x.point := by
    have h := congrArg Realization.point (e.apply_symm_apply xT)
    change ((MappingCylinder.relabelMorphism Q Function.Embedding.inr).realization y).point =
      x.point at h
    rwa [MappingCylinder.relabelMorphism_point] at h
  rw [stageRetraction_point, ← hy, rawRetraction_inr]

private theorem finalStage_point_general (f : Morphism P Q) (M r : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M) (hr : M < r)
    (x : (cylinderStage f r).Realization) :
    (stageRetraction f r x).point.map (Sum.inr : W → Face P ⊕ W) = x.point := by
  have hleft : x.point.weights.support.toLeft = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hlow := x.support_mem.2 a ha
    have hhigh := hP a
    omega
  have hright : x.point.weights.support.toRight ∈ Q := by
    have h := x.support_mem.1.1.2.2
    simpa only [MappingCylinder.hull, hleft, Finset.biUnion_empty,
      Finset.union_empty] using h
  have htarget : x.point.weights.support ∈ MappingCylinder.targetComplex P Q := by
    refine ⟨x.point.weights.support.toRight, hright, ?_⟩
    have h := Finset.toLeft_disjSum_toRight (u := x.point.weights.support)
    rw [hleft, Finset.empty_disjSum] at h
    simpa only [← Finset.map_eq_image] using h
  let xT : (MappingCylinder.targetComplex P Q).Realization := ⟨x.point, htarget⟩
  let e := MappingCylinder.relabelHomeomorph Q
    (Function.Embedding.inr : W ↪ Face P ⊕ W)
  let y := e.symm xT
  have hy : y.point.map (Sum.inr : W → Face P ⊕ W) = x.point := by
    have h := congrArg Realization.point (e.apply_symm_apply xT)
    change ((MappingCylinder.relabelMorphism Q Function.Embedding.inr).realization y).point =
      x.point at h
    rwa [MappingCylinder.relabelMorphism_point] at h
  rw [stageRetraction_point, ← hy, rawRetraction_inr]

/-- The inclusion of `Q` into the small cylinder, relabelling by `Sum.inr`
(`smallOldTarget_point`). -/
def smallOldTarget (f : Morphism P Q) :
    C(Q.Realization, (smallCylinder f).Realization) :=
  ⟨fun y => Realization.inclusion (small_target_le f)
      (MappingCylinder.relabelHomeomorph Q Function.Embedding.inr y),
    (Realization.continuous_inclusion (small_target_le f)).comp
      (MappingCylinder.relabelHomeomorph Q Function.Embedding.inr).continuous⟩

theorem smallOldTarget_point (f : Morphism P Q) (y : Q.Realization) :
    (smallOldTarget f y).point = y.point.map (Sum.inr : W → Face P ⊕ W) :=
  MappingCylinder.relabelMorphism_point Q Function.Embedding.inr y

/-- The retraction of the small cylinder onto `Q`: `MappingCylinder.retraction f` restricted to
the small cylinder. -/
def smallRetraction (f : Morphism P Q) :
    C((smallCylinder f).Realization, Q.Realization) :=
  (MappingCylinder.retraction f).comp
    ⟨Realization.inclusion (smallCylinder_le f),
      Realization.continuous_inclusion (smallCylinder_le f)⟩

private theorem smallRetraction_point (f : Morphism P Q) (x : (smallCylinder f).Realization) :
    (smallRetraction f x).point = rawRetraction f x.point :=
  (rawRetraction_existing f (Realization.inclusion (smallCylinder_le f) x)).symm

theorem smallRetraction_old (f : Morphism P Q) (y : Q.Realization) :
    smallRetraction f (smallOldTarget f y) = y := by
  apply Realization.ext
  rw [smallRetraction_point, smallOldTarget_point, rawRetraction_inr]

/-- A homotopy from the identity of the small cylinder to `smallOldTarget f ∘ smallRetraction f`,
fixing the image of `Q`, given a bound `M` on the cardinalities of the faces of `P`. -/
def boundedSmallDeformation (f : Morphism P Q) (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallCylinder f).Realization)
      ((smallOldTarget f).comp (smallRetraction f)) (Set.range (smallOldTarget f)) where
  toFun p := stageOneToSmall f
    (finiteTransferHomotopy f 1 M (p.1, smallToStageOne f p.2))
  continuous_toFun := (stageOneToSmall f).continuous.comp
    ((finiteTransferHomotopy f 1 M).continuous.comp
      (continuous_fst.prodMk ((smallToStageOne f).continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [(finiteTransferHomotopy f 1 M).apply_zero]
    apply Realization.ext
    exact realizationEqHomeomorph_point (cylinderStage_one f).symm x
  map_one_left x := by
    rw [(finiteTransferHomotopy f 1 M).apply_one]
    apply Realization.ext
    simp only [ContinuousMap.comp_apply]
    rw [show (stageOneToSmall f (stageInto f 1 M
        (finiteTransfer f 1 M (smallToStageOne f x)))).point =
        (finiteTransfer f 1 M (smallToStageOne f x)).point from
      rfl]
    rw [smallOldTarget_point]
    have h := finalStage_point_general f M (1 + M) hP (by omega)
      (finiteTransfer f 1 M (smallToStageOne f x))
    have hi := stageRetraction_finite f 1 M (smallToStageOne f x)
    have heq : stageRetraction f 1 (smallToStageOne f x) = smallRetraction f x := by
      apply Realization.ext
      rw [stageRetraction_point, smallRetraction_point]
      rw [show (smallToStageOne f x).point = x.point from
        realizationEqHomeomorph_point (cylinderStage_one f).symm x]
    simpa only [hi, heq] using h.symm
  prop' t x hx := by
    rcases hx with ⟨y, rfl⟩
    have heq : smallToStageOne f (smallOldTarget f y) = oldTargetStage f 1 y := by
      apply Realization.ext
      rw [show (smallToStageOne f (smallOldTarget f y)).point =
          (smallOldTarget f y).point from
        realizationEqHomeomorph_point (cylinderStage_one f).symm (smallOldTarget f y)]
      rw [smallOldTarget_point, oldTargetStage_point]
    change stageOneToSmall f
      (finiteTransferHomotopy f 1 M (t, smallToStageOne f (smallOldTarget f y))) =
        smallOldTarget f y
    rw [heq, finiteTransferHomotopy_target]
    apply Realization.ext
    rw [show (stageOneToSmall f (oldTargetStage f 1 y)).point =
        (oldTargetStage f 1 y).point from
      rfl]
    rw [oldTargetStage_point, smallOldTarget_point]

private def chosenSourceBound (P : PreAbstractSimplicialComplex V) [Finite (Face P)] : ℕ :=
  Classical.choose (exists_uniform_subdivisionIter_card_bound P) + 1

private theorem chosenSourceBound_spec (P : PreAbstractSimplicialComplex V) [Finite (Face P)]
    (a : Face P) : a.val.card ≤ chosenSourceBound P :=
  Classical.choose_spec (exists_uniform_subdivisionIter_card_bound P) 0 a

/-- For finite source faces, construct the stationary deformation to the restricted
mapping-cylinder retraction. Every target point is fixed at every time. -/
def smallCylinderDeformation (f : Morphism P Q) [Finite (Face P)] :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallCylinder f).Realization)
      ((smallOldTarget f).comp (smallRetraction f)) (Set.range (smallOldTarget f)) :=
  boundedSmallDeformation f (chosenSourceBound P) (chosenSourceBound_spec P)


private def smallIntoLarge (f : Morphism P Q) :
    C((smallCylinder f).Realization, (MappingCylinder.complex f).Realization) :=
  ⟨Realization.inclusion (smallCylinder_le f),
      Realization.continuous_inclusion (smallCylinder_le f)⟩

private theorem smallIntoLarge_closed (f : Morphism P Q) :
    IsClosedEmbedding (smallIntoLarge f) :=
  Realization.isClosedEmbedding_inclusion (smallCylinder_le f)

private theorem smallOldTarget_closed (f : Morphism P Q) :
    IsClosedEmbedding (smallOldTarget f) :=
  (Realization.isClosedEmbedding_inclusion (small_target_le f)).comp
    (MappingCylinder.relabelHomeomorph Q Function.Embedding.inr).isClosedEmbedding

/-- The inclusion of the copied domain, the barycentric subdivision of `P` relabelled by
`Sum.inl`, into the small cylinder. -/
def smallCopiedDomain (f : Morphism P Q) :
    C((barycentricSubdivision P).Realization, (smallCylinder f).Realization) :=
  ⟨fun x => Realization.inclusion (small_domain_le f)
      (MappingCylinder.relabelHomeomorph (barycentricSubdivision P) Function.Embedding.inl x),
    (Realization.continuous_inclusion (small_domain_le f)).comp
      (MappingCylinder.relabelHomeomorph
          (barycentricSubdivision P) Function.Embedding.inl).continuous⟩

theorem smallCopiedDomain_point (f : Morphism P Q)
    (x : (barycentricSubdivision P).Realization) :
    (smallCopiedDomain f x).point = x.point.map (Sum.inl : Face P → Face P ⊕ W) :=
  MappingCylinder.relabelMorphism_point (barycentricSubdivision P) Function.Embedding.inl x

theorem smallCopiedDomain_closed (f : Morphism P Q) :
    IsClosedEmbedding (smallCopiedDomain f) :=
  (Realization.isClosedEmbedding_inclusion (small_domain_le f)).comp
    (MappingCylinder.relabelHomeomorph (barycentricSubdivision P)
        Function.Embedding.inl).isClosedEmbedding

private theorem smallIntoLarge_old (f : Morphism P Q) (y : Q.Realization) :
    smallIntoLarge f (smallOldTarget f y) = (MappingCylinder.targetMorphism f).realization y := by
  apply Realization.ext
  change (smallOldTarget f y).point = _
  rw [smallOldTarget_point, MappingCylinder.targetMorphism_point]

private theorem smallIntoLarge_copied (f : Morphism P Q)
    (x : (barycentricSubdivision P).Realization) :
    smallIntoLarge f (smallCopiedDomain f x) =
        (MappingCylinder.domainMorphism f).realization x := by
  apply Realization.ext
  change (smallCopiedDomain f x).point = _
  rw [smallCopiedDomain_point, MappingCylinder.domainMorphism_point]

theorem smallCopied_old_disjoint (f : Morphism P Q) :
    Disjoint (Set.range (smallCopiedDomain f)) (Set.range (smallOldTarget f)) := by
  apply Set.disjoint_left.mpr
  intro z hzD hzQ
  rcases hzD with ⟨x, hx⟩
  rcases hzQ with ⟨y, hy⟩
  have hxy : (MappingCylinder.domainMorphism f).realization x =
      (MappingCylinder.targetMorphism f).realization y := by
    rw [← smallIntoLarge_copied, ← smallIntoLarge_old]
    exact congrArg (smallIntoLarge f) (hx.trans hy.symm)
  exact (MappingCylinder.domain_target_disjoint f).notMem_of_mem_left
    (Set.mem_range_self x) ⟨y, hxy.symm⟩

theorem smallRetraction_copied (f : Morphism P Q)
    (x : (barycentricSubdivision P).Realization) :
    smallRetraction f (smallCopiedDomain f x) =
      f.realization (barycentricHomeomorph P x) := by
  change MappingCylinder.retraction f (smallIntoLarge f (smallCopiedDomain f x)) = _
  rw [smallIntoLarge_copied]
  exact MappingCylinder.retraction_domain f x

theorem smallCylinderDeformation_old (f : Morphism P Q) [Finite (Face P)]
    (t : unitInterval) (y : Q.Realization) :
    smallCylinderDeformation f (t, smallOldTarget f y) = smallOldTarget f y :=
  (smallCylinderDeformation f).eq_fst t (Set.mem_range_self y)

private theorem smallCylinderDeformation_copied_terminal (f : Morphism P Q)
    [Finite (Face P)] (x : (barycentricSubdivision P).Realization) :
    smallCylinderDeformation f (1, smallCopiedDomain f x) =
      smallOldTarget f (f.realization (barycentricHomeomorph P x)) := by
  rw [(smallCylinderDeformation f).apply_one, ContinuousMap.comp_apply, smallRetraction_copied]

private theorem relabel_le {A : Type*} {B : Type*}
    {S T : PreAbstractSimplicialComplex A} (h : S ≤ T) (e : A ↪ B) :
    MappingCylinder.relabelComplex S e ≤ MappingCylinder.relabelComplex T e := by
  intro s hs
  rcases hs with ⟨a, ha, rfl⟩
  exact ⟨a, h ha, rfl⟩

private def smallMappedCylinder (f : Morphism P Q) :
    PreAbstractSimplicialComplex ((Face P ⊕ W) ⊕ PUnit.{max v w + 1}) :=
  MappingCylinder.relabelComplex (smallCylinder f) Function.Embedding.inl

private def smallMappedDomain :
    PreAbstractSimplicialComplex ((Face P ⊕ W) ⊕ PUnit.{max v w + 1}) :=
  MappingCylinder.relabelComplex (MappingCylinder.domainComplex P W) Function.Embedding.inl

/-- The small mapping cone of `f`: the small cylinder, relabelled by `Sum.inl`, together with the
cone on the copied domain `MappingCylinder.domainComplex P W`. -/
@[expose] def smallAssociatedCone (f : Morphism P Q) :
    PreAbstractSimplicialComplex ((Face P ⊕ W) ⊕ PUnit.{max v w + 1}) :=
  MappingCylinder.relabelComplex (smallCylinder f)
      (Function.Embedding.inl : Face P ⊕ W ↪ (Face P ⊕ W) ⊕ PUnit.{max v w + 1}) ⊔
    MappingCylinder.coneComplex (MappingCylinder.domainComplex P W)

private theorem smallMappedDomain_le (f : Morphism P Q) :
    smallMappedDomain (P := P) (W := W) ≤ smallMappedCylinder f :=
  relabel_le (small_domain_le f) Function.Embedding.inl

private theorem smallCone_into_large (f : Morphism P Q) :
    smallAssociatedCone f ≤ MappingCylinder.associatedCone f :=
  sup_le_sup (relabel_le (smallCylinder_le f) Function.Embedding.inl) (le_refl _)

private theorem smallCone_intersection (f : Morphism P Q) :
    smallMappedCylinder f ⊓ MappingCylinder.coneComplex (MappingCylinder.domainComplex P W) =
      smallMappedDomain (P := P) (W := W) := by
  apply le_antisymm
  · exact (inf_le_inf
      (relabel_le (smallCylinder_le f) Function.Embedding.inl) (le_refl _)).trans_eq
        (MappingCylinder.attachedCone_intersection f)
  · exact le_inf (smallMappedDomain_le f)
      (MappingCylinder.cone_base_le (MappingCylinder.domainComplex P W))

/-- The inclusion of the copied domain `MappingCylinder.domainComplex P W` into the small
cylinder. -/
def domainIntoSmall (f : Morphism P Q) :
    C((MappingCylinder.domainComplex P W).Realization, (smallCylinder f).Realization) :=
  ⟨Realization.inclusion (small_domain_le f), Realization.continuous_inclusion (small_domain_le f)⟩

/-- The inclusion of the small cylinder into the small mapping cone, relabelling by `Sum.inl`. -/
def smallIntoCone (f : Morphism P Q) :
    C((smallCylinder f).Realization, (smallAssociatedCone f).Realization) :=
  ⟨fun x => Realization.inclusion (le_sup_left : smallMappedCylinder f ≤ smallAssociatedCone f)
      (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl x),
    (Realization.continuous_inclusion le_sup_left).comp
      (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl).continuous⟩

theorem smallIntoCone_point (f : Morphism P Q) (x : (smallCylinder f).Realization) :
    (smallIntoCone f x).point =
      x.point.map (Sum.inl : Face P ⊕ W → (Face P ⊕ W) ⊕ PUnit.{max v w + 1}) :=
  MappingCylinder.relabelMorphism_point (smallCylinder f) Function.Embedding.inl x

private theorem smallIntoCone_closed (f : Morphism P Q) :
    IsClosedEmbedding (smallIntoCone f) :=
  (Realization.isClosedEmbedding_inclusion
      (le_sup_left : smallMappedCylinder f ≤ smallAssociatedCone f)).comp
    (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl).isClosedEmbedding

/-- The topological cone on the copied domain, mapped into the small mapping cone through
`MappingCylinder.ordinaryConeHomeomorph` onto its cone part; needs finitely many faces of `P`. -/
def smallOrdinaryConeAttachment (f : Morphism P Q) [Finite (Face P)] :
    C(TopCat.cone (TopCat.of (MappingCylinder.domainComplex P W).Realization),
      (smallAssociatedCone f).Realization) := by
  letI : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  exact (⟨Realization.inclusion (le_sup_right :
      MappingCylinder.coneComplex (MappingCylinder.domainComplex P W) ≤ smallAssociatedCone f),
      Realization.continuous_inclusion le_sup_right⟩ : C(_, _)).comp
    (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) : C(_, _))

/-- The small attachment preserves the whole barycentric point of the ordinary cone. -/
theorem smallOrdinaryConeAttachment_point (f : Morphism P Q) [Finite (Face P)]
    (x : TopCat.cone (TopCat.of (MappingCylinder.domainComplex P W).Realization)) :
    letI : Finite (Face (MappingCylinder.domainComplex P W)) :=
      MappingCylinder.finiteFaces_domainComplex P W
    (smallOrdinaryConeAttachment f x).point =
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) x).point := by
  let : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  rfl

theorem smallOrdinaryConeAttachment_closed (f : Morphism P Q) [Finite (Face P)] :
    IsClosedEmbedding (smallOrdinaryConeAttachment f) := by
  let : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  exact (Realization.isClosedEmbedding_inclusion (le_sup_right :
    MappingCylinder.coneComplex (MappingCylinder.domainComplex P W) ≤ smallAssociatedCone f)).comp
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W)).isClosedEmbedding

private theorem inclusion_coordinates {A : Type*} {S T : PreAbstractSimplicialComplex A}
    (h : S ≤ T) (x : S.Realization) :
    ((MappingCylinder.inclusionMorphism h).realization x).point = x.point := by
  change ((MappingCylinder.inclusionMorphism h).realizationMap x).point = x.point
  rw [Morphism.realizationMap_point]
  exact Realization.map_vertexCoordinates x

theorem smallOrdinaryConeAttachment_isPushout (f : Morphism P Q) [Finite (Face P)] :
    IsPushout (TopCat.ofHom (domainIntoSmall f))
      (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex P W).Realization))
      (TopCat.ofHom (smallIntoCone f)) (TopCat.ofHom (smallOrdinaryConeAttachment f)) := by
  let : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  let e1 : TopCat.of (MappingCylinder.domainComplex P W).Realization ≅
      TopCat.of (smallMappedDomain (P := P) (W := W)).Realization :=
    TopCat.isoOfHomeo
      (MappingCylinder.relabelHomeomorph (MappingCylinder.domainComplex P W) Function.Embedding.inl)
  let e2 : TopCat.of (smallCylinder f).Realization ≅
      TopCat.of (smallMappedCylinder f).Realization :=
    TopCat.isoOfHomeo (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl)
  let e3 : TopCat.cone (TopCat.of (MappingCylinder.domainComplex P W).Realization) ≅
      TopCat.of (MappingCylinder.coneComplex (MappingCylinder.domainComplex P W)).Realization :=
    TopCat.isoOfHomeo (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W))
  let hraw := MappingCylinder.isPushout_union_of_intersection
    (smallMappedCylinder f) (MappingCylinder.coneComplex (MappingCylinder.domainComplex P W))
    (smallMappedDomain (P := P) (W := W)) (smallCone_intersection f)
    (smallMappedDomain_le f) (MappingCylinder.cone_base_le (MappingCylinder.domainComplex P W))
  refine hraw.of_iso' e1 e2 e3 (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((MappingCylinder.inclusionMorphism (smallMappedDomain_le f)).realization
      (MappingCylinder.relabelHomeomorph
          (MappingCylinder.domainComplex P W) Function.Embedding.inl x)).point =
        (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl
          (domainIntoSmall f x)).point
    have hi := inclusion_coordinates (smallMappedDomain_le f)
      (MappingCylinder.relabelHomeomorph (MappingCylinder.domainComplex P W)
        Function.Embedding.inl x)
    let e : (Face P ⊕ W) ↪ ((Face P ⊕ W) ⊕ PUnit.{max v w + 1}) :=
      Function.Embedding.inl
    have hd := MappingCylinder.relabelMorphism_point
      (MappingCylinder.domainComplex P W) e x
    have hc := MappingCylinder.relabelMorphism_point
      (smallCylinder f) e (domainIntoSmall f x)
    exact hi.trans (hd.trans hc.symm)
  · apply ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((MappingCylinder.inclusionMorphism
      (MappingCylinder.cone_base_le (MappingCylinder.domainComplex P W))).realization
        (MappingCylinder.relabelHomeomorph
            (MappingCylinder.domainComplex P W) Function.Embedding.inl x)).point =
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W)
        (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex P W).Realization) x)).point
    rw [inclusion_coordinates, MappingCylinder.ordinaryConeHomeomorph_base,
      MappingCylinder.coneBaseMorphism_point]
    exact MappingCylinder.relabelMorphism_point _ _ x
  · apply ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((MappingCylinder.inclusionMorphism
      (le_sup_left : smallMappedCylinder f ≤ smallAssociatedCone f)).realization
        (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl x)).point =
          (smallIntoCone f x).point
    have hi := inclusion_coordinates
      (le_sup_left : smallMappedCylinder f ≤ smallAssociatedCone f)
      (MappingCylinder.relabelHomeomorph (smallCylinder f) Function.Embedding.inl x)
    exact hi.trans ((MappingCylinder.relabelMorphism_point
      (smallCylinder f) Function.Embedding.inl x).trans (smallIntoCone_point f x).symm)
  · apply ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((MappingCylinder.inclusionMorphism
      (le_sup_right : MappingCylinder.coneComplex (MappingCylinder.domainComplex P W) ≤
        smallAssociatedCone f)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) x)).point =
      (smallOrdinaryConeAttachment f x).point
    rw [inclusion_coordinates]
    rfl

theorem smallOrdinaryConeAttachment_base (f : Morphism P Q) [Finite (Face P)]
    (x : (MappingCylinder.domainComplex P W).Realization) :
    smallOrdinaryConeAttachment f
      (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex P W).Realization) x) =
        smallIntoCone f (domainIntoSmall f x) :=
  (ConcreteCategory.congr_hom (smallOrdinaryConeAttachment_isPushout f).w x).symm

private def smallConeIntoLarge (f : Morphism P Q) :
    C((smallAssociatedCone f).Realization, (MappingCylinder.associatedCone f).Realization) :=
  ⟨Realization.inclusion (smallCone_into_large f),
      Realization.continuous_inclusion (smallCone_into_large f)⟩

private theorem smallConeIntoLarge_ordinary (f : Morphism P Q) [Finite (Face P)]
    (x : TopCat.cone (TopCat.of (MappingCylinder.domainComplex P W).Realization)) :
    smallConeIntoLarge f (smallOrdinaryConeAttachment f x) =
      MappingCylinder.ordinaryConeAttachment f x := by
  let : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  apply Realization.ext
  change (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) x).point =
    ((MappingCylinder.inclusionMorphism (MappingCylinder.attachedCone_le f)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W) x)).point
  exact (inclusion_coordinates _ _).symm

private theorem smallCone_cover (f : Morphism P Q) [Finite (Face P)] :
    Set.range (smallIntoCone f) ∪ Set.range (smallOrdinaryConeAttachment f) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
      ((smallOrdinaryConeAttachment_isPushout f).map (forget TopCat)) z

private theorem smallCone_cylinder_intersection (f : Morphism P Q) [Finite (Face P)] :
    Set.range (smallIntoCone f) ∩ Set.range (smallOrdinaryConeAttachment f) =
      Set.range (fun x => smallIntoCone f (domainIntoSmall f x)) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let hraw := (smallOrdinaryConeAttachment_isPushout f).map (forget TopCat)
    have hxy : smallIntoCone f x = smallOrdinaryConeAttachment f y := hx.trans hy.symm
    obtain ⟨a, ha, _⟩ :=
      (CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hraw.isColimit
        (Realization.isClosedEmbedding_inclusion (small_domain_le f)).injective x y).mp hxy
    exact ⟨a, (congrArg (smallIntoCone f) ha).trans hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨domainIntoSmall f x, rfl⟩,
      ⟨TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex P W).Realization) x,
        smallOrdinaryConeAttachment_base f x⟩⟩

/- The cone bounds follow from source-face bounds. The apex is retained
when the copied domain is empty. -/

/-- The cone apex, as a vertex of the small mapping cone. -/
def smallConeApex (f : Morphism P Q) : Vertex (smallAssociatedCone f) :=
  ⟨(MappingCylinder.coneApex (MappingCylinder.domainComplex P W)).val,
    (le_sup_right : MappingCylinder.coneComplex (MappingCylinder.domainComplex P W) ≤
      smallAssociatedCone f)
        (MappingCylinder.coneApex (MappingCylinder.domainComplex P W)).property⟩

theorem smallOrdinaryConeAttachment_apex (f : Morphism P Q) [Finite (Face P)] :
    smallOrdinaryConeAttachment f
      (TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex P W).Realization) PUnit.unit) =
        Realization.vertex (smallAssociatedCone f) (smallConeApex f).val
          (smallConeApex f).property := by
  let : Finite (Face (MappingCylinder.domainComplex P W)) :=
    MappingCylinder.finiteFaces_domainComplex P W
  apply Realization.ext
  change (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex P W)
    (TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex P W).Realization)
        PUnit.unit)).point = _
  rw [MappingCylinder.ordinaryConeHomeomorph_apex]
  rfl

private theorem copiedDomain_face_card_le (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (s : Face (MappingCylinder.domainComplex P W)) : s.val.card ≤ M := by
  rcases s.property with ⟨a, ha, he⟩
  have h : a.card ≤ M :=
    (card_subdivisionFace_le_lastFace P ⟨a, ha⟩).trans
      (hP (subdivisionLastFace P ⟨a, ha⟩))
  rw [← he]
  simpa only [← Finset.map_eq_image, Finset.card_map] using h

theorem copiedCone_face_card_le (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (s : Face (MappingCylinder.coneComplex (MappingCylinder.domainComplex P W))) :
    s.val.card ≤ M + 1 := by
  have hr : s.val.toRight.card ≤ 1 := by
    calc
      s.val.toRight.card ≤ (Finset.univ : Finset PUnit.{max v w + 1}).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 1 := by simp only [Finset.card_univ, Fintype.card_punit]
  have hl : s.val.toLeft.card ≤ M := by
    rcases s.property.2 with h | h
    · exact copiedDomain_face_card_le M hP ⟨s.val.toLeft, h⟩
    · simp only [h, Finset.card_empty, Nat.zero_le]
  have hsum := Finset.card_toLeft_add_card_toRight (u := s.val)
  omega

theorem smallAssociatedCone_face_card_le (f : Morphism P Q) (M N : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (hQ : ∀ a : Face Q, a.val.card ≤ N) (s : Face (smallAssociatedCone f)) :
    s.val.card ≤ max (M + 1) N := by
  rcases s.property with h | h
  · rcases h with ⟨a, ha, he⟩
    have hcard := small_all_face_card_le f M N hP hQ ⟨a, ha⟩
    rw [← he]
    simpa only [← Finset.map_eq_image, Finset.card_map] using hcard
  · exact (copiedCone_face_card_le M hP ⟨s.val, h⟩).trans (le_max_left _ _)

/-- The labels controlling a finite label set `s`: the source faces of `s` together with
`MappingCylinder.hull f s`, the target labels of `s` and of the images of its source faces. It
contains `s` (`controlHalo_contains`). -/
def controlHalo (f : Morphism P Q) (s : Finset (Face P ⊕ W)) :
    Finset (Face P ⊕ W) := s.toLeft.disjSum (MappingCylinder.hull f s)

theorem controlHalo_contains (f : Morphism P Q) (s : Finset (Face P ⊕ W)) :
    s ⊆ controlHalo f s := by
  intro z hz
  cases z with
  | inl a =>
      simpa only [controlHalo, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using
          (Finset.mem_toLeft.mpr hz)
  | inr b =>
      have hb : b ∈ MappingCylinder.hull f s :=
        Finset.mem_union_left _ (Finset.mem_toRight.mpr hz)
      simpa only [controlHalo, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using hb

private theorem transferLabel_support_in_controlHalo (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) (z : Face P ⊕ W) (hz : z ∈ controlHalo f s) :
    (transferLabel f k z).weights.support ⊆ controlHalo f s := by
  cases z with
  | inl a =>
      have ha : a ∈ s.toLeft := by
        simpa only [controlHalo, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using hz
      by_cases hk : a.val.card = k
      · rw [transferLabel, ite_eq_left hk]
        intro z hz'
        rw [Convexity.StdSimplex.weights_map] at hz'
        rcases Finset.mem_image.mp (Finsupp.mapDomain_support hz') with ⟨b, hb, rfl⟩
        have htarget : b ∈ MappingCylinder.hull f s :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨a, ha, MappingCylinder.leftPoint_support f a hb⟩)
        simpa only [controlHalo, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] using htarget
      · rw [transferLabel, ite_eq_right hk]
        rw [show (Convexity.StdSimplex.single (Sum.inl a)).weights.support = {Sum.inl a} from
          Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl]
        exact Finset.singleton_subset_iff.mpr hz
  | inr b =>
      change (Convexity.StdSimplex.single (Sum.inr b)).weights.support ⊆ _
      rw [show (Convexity.StdSimplex.single (Sum.inr b)).weights.support = {Sum.inr b} from
        Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl]
      exact Finset.singleton_subset_iff.mpr hz

private theorem transferPoint_support_in_controlHalo (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) (p : Convexity.StdSimplex ℝ (Face P ⊕ W))
    (hp : p.weights.support ⊆ controlHalo f s) :
    (transferPoint f k p).weights.support ⊆ controlHalo f s :=
  mixture_support_subset p (transferLabel f k) _
    (fun z hz => transferLabel_support_in_controlHalo f k s z (hp hz))

private theorem transferHomotopyPoint_support_in_controlHalo (f : Morphism P Q) (k : ℕ)
    (s : Finset (Face P ⊕ W)) (t : unitInterval) (x : (cylinderStage f k).Realization)
    (hx : x.point.weights.support ⊆ controlHalo f s) :
    (transferHomotopyPoint f k (t, x)).point.weights.support ⊆ controlHalo f s := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  exact (Realization.segmentPoint_support_subset t x.point (transferPoint f k x.point)).trans
    (Finset.union_subset hx (transferPoint_support_in_controlHalo f k s x.point hx))

private theorem finiteTransfer_support_in_controlHalo (f : Morphism P Q) (k r : ℕ)
    (s : Finset (Face P ⊕ W)) (x : (cylinderStage f k).Realization)
    (hx : x.point.weights.support ⊆ controlHalo f s) :
    (finiteTransfer f k r x).point.weights.support ⊆ controlHalo f s := by
  induction r with
  | zero => exact hx
  | succ r ih => exact transferPoint_support_in_controlHalo f (k + r) s _ ih

private theorem nextTransferHomotopy_support_in_controlHalo (f : Morphism P Q) (k r : ℕ)
    (s : Finset (Face P ⊕ W)) (t : unitInterval) (x : (cylinderStage f k).Realization)
    (hx : x.point.weights.support ⊆ controlHalo f s) :
    (nextTransferHomotopy f k r (t, x)).point.weights.support ⊆ controlHalo f s := by
  change (transferHomotopyPoint f (k + r) (t, finiteTransfer f k r x)).point.weights.support ⊆ _
  exact transferHomotopyPoint_support_in_controlHalo f (k + r) s t _
    (finiteTransfer_support_in_controlHalo f k r s x hx)

private theorem finiteTransferHomotopy_support_in_controlHalo (f : Morphism P Q) (k r : ℕ)
    (s : Finset (Face P ⊕ W)) (t : unitInterval) (x : (cylinderStage f k).Realization)
    (hx : x.point.weights.support ⊆ controlHalo f s) :
    (finiteTransferHomotopy f k r (t, x)).point.weights.support ⊆ controlHalo f s := by
  induction r generalizing t with
  | zero => exact hx
  | succ r ih =>
      rw [finiteTransferHomotopy, ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact ih _
      · exact nextTransferHomotopy_support_in_controlHalo f k r s _ x hx

theorem boundedSmallDeformation_support_in_controlHalo (f : Morphism P Q) (M : ℕ)
    (hP : ∀ a : Face P, a.val.card ≤ M)
    (s : Finset (Face P ⊕ W)) (t : unitInterval) (x : (smallCylinder f).Realization)
    (hx : x.point.weights.support ⊆ controlHalo f s) :
    (boundedSmallDeformation f M hP (t, x)).point.weights.support ⊆ controlHalo f s := by
  change (finiteTransferHomotopy f 1 M (t, smallToStageOne f x)).point.weights.support ⊆ _
  apply finiteTransferHomotopy_support_in_controlHalo
  rw [show (smallToStageOne f x).point = x.point from
    realizationEqHomeomorph_point (cylinderStage_one f).symm x]
  exact hx

theorem smallCylinderDeformation_face_support (f : Morphism P Q) [Finite (Face P)]
    (s : Face (smallCylinder f)) (t : unitInterval) (q : Convexity.StdSimplex ℝ s.val) :
    (smallCylinderDeformation f (t,
        Realization.faceMap (smallCylinder f) s q)).point.weights.support ⊆
      controlHalo f s.val :=
  boundedSmallDeformation_support_in_controlHalo f (chosenSourceBound P) (chosenSourceBound_spec P)
    s.val t _ ((Realization.support_map_subtype_subset s.val q).trans
        (controlHalo_contains f s.val))

private def smallFaceDeformationInFiniteCarrier (f : Morphism P Q) [Finite (Face P)]
    (s : Face (smallCylinder f)) :
    C(unitInterval × Convexity.StdSimplex ℝ s.val,
      (restrictVertices (smallCylinder f) (controlHalo f s.val)).Realization) := by
  let h := fun p : unitInterval × Convexity.StdSimplex ℝ s.val =>
    smallCylinderDeformation f (p.1, Realization.faceMap (smallCylinder f) s p.2)
  let d := fun p : unitInterval × Convexity.StdSimplex ℝ s.val =>
    (⟨(h p).point, (h p).support_mem,
      smallCylinderDeformation_face_support f s p.1 p.2⟩ :
        (restrictVertices (smallCylinder f) (controlHalo f s.val)).Realization)
  refine ⟨d, ?_⟩
  apply (Realization.isClosedEmbedding_inclusion
    (restrictVertices_le (smallCylinder f) (controlHalo f s.val))).isEmbedding.continuous_iff.mpr
  have heq : Realization.inclusion
      (restrictVertices_le (smallCylinder f) (controlHalo f s.val)) ∘ d = h := by
    funext p
    apply Realization.ext
    rfl
  rw [heq]
  exact (smallCylinderDeformation f).continuous.comp
    (continuous_fst.prodMk ((Realization.continuous_faceMap _ _).comp continuous_snd))

private theorem smallFaceDeformationInFiniteCarrier_whole (f : Morphism P Q) [Finite (Face P)]
    (s : Face (smallCylinder f)) (t : unitInterval) (q : Convexity.StdSimplex ℝ s.val) :
    Realization.inclusion (restrictVertices_le (smallCylinder f) (controlHalo f s.val))
        (smallFaceDeformationInFiniteCarrier f s (t, q)) =
      smallCylinderDeformation f (t, Realization.faceMap (smallCylinder f) s q) :=
  Realization.ext rfl


end PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder

end
