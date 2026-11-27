/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
/-!
# Compact maps into closed T1 sequential colimits

Let F be a natural-number chain of topological spaces with closed T1-embedding transition maps.
A continuous map from any compact space into a colimit of F factors continuously through one
stage. Every singular simplex of the colimit therefore comes from a stage.

A closed T1-embedding is a closed embedding whose codomain singleton is closed at every point
outside the image. The compact source universe w is independent of the space universe u.
-/
@[expose] public section
universe w u
open CategoryTheory Limits Topology
namespace TopCat
/-- Let F:ℕ→TopCat.{u} be a chain whose every transition map is a closed embedding with closed
codomain singletons outside its image. For any colimiting cocone c and compact topological space
K in an independent universe w, each continuous f:K→c.pt factors as a continuous g:K→F(j)
followed by the j-th colimit leg. -/
theorem exists_stage_of_compact
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    {K : Type w} [TopologicalSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : ℕ) (g : C(K, ↥(F.obj j))),
      (c.ι.app j).hom.comp g = f := by
  have hFclosed : ∀ ⦃i j : ℕ⦄ (g : i ⟶ j), IsClosedEmbedding (F.map g).hom :=
    fun _ _ g => closedT1Embeddings_le_isClosedEmbedding _ (hF g)
  have hLeg : ∀ j, IsClosedEmbedding (c.ι.app j).hom := fun j =>
    isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding c hc hFclosed j
  have hInj : ∀ j, Function.Injective (c.ι.app j).hom := fun j => (hLeg j).injective
  have hcType : IsColimit ((forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hc
  have hMono : ∀ ⦃i k : ℕ⦄ (_ : i ≤ k),
      Set.range (c.ι.app i).hom ⊆ Set.range (c.ι.app k).hom := by
    intro i k h y hy; obtain ⟨z, rfl⟩ := hy
    exact ⟨(F.map (homOfLE h)).hom z, ConcreteCategory.congr_hom
      ((forget TopCat).congr_map (c.w (homOfLE h))) z⟩
  have hCover : ∀ x : K, ∃ j, f x ∈ Set.range (c.ι.app j).hom := by
    intro x; obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType (f x)
    exact ⟨j, y, hy⟩
  have hC : IsCompact (Set.range ⇑f) := by simpa [Set.image_univ] using hK.image f.continuous
  have hUni : ∃ N, Set.range ⇑f ⊆ Set.range (c.ι.app N).hom := by
    by_contra hCon; push Not at hCon
    have hChoice : ∀ j, ∃ y : K, f y ∉ Set.range (c.ι.app j).hom := by
      intro j; obtain ⟨z, hzMem, hzNot⟩ := Set.not_subset.mp (hCon j)
      obtain ⟨y, rfl⟩ := hzMem; exact ⟨y, hzNot⟩
    choose x hx using hChoice
    have hPiece : ∀ (m j n : ℕ), j ≤ n ∧ n < m →
        IsClosed ((c.ι.app m).hom ⁻¹' {f (x n)}) := by
      intro m j n hn; by_cases hMem : f (x n) ∈ Set.range (c.ι.app m).hom
      · obtain ⟨z₀, hz₀⟩ := hMem
        have hEqP : (c.ι.app m).hom ⁻¹' {f (x n)} = {z₀} := by
          ext y; rw [Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_singleton_iff]; constructor
          · intro hy; exact hInj m (hy.trans hz₀.symm)
          · intro hy; rw [hy, hz₀]
        rw [hEqP]
        have hT1 : Topology.IsClosedT1Embedding (F.map (homOfLE (le_of_lt hn.2))).hom :=
          (closedT1Embeddings_iff _).mp (hF (homOfLE (le_of_lt hn.2)))
        have hOut : z₀ ∉ Set.range (F.map (homOfLE (le_of_lt hn.2))).hom := by
          intro hOut; obtain ⟨w, hw⟩ := hOut
          have hNat : (c.ι.app n).hom w =
              (c.ι.app m).hom ((F.map (homOfLE (le_of_lt hn.2))).hom w) :=
            (ConcreteCategory.congr_hom ((forget TopCat).congr_map
              (c.w (homOfLE (le_of_lt hn.2)))) w).symm
          have hEq : (c.ι.app m).hom ((F.map (homOfLE (le_of_lt hn.2))).hom w) =
              f (x n) := by rw [hw, hz₀]
          have hInR : f (x n) ∈ Set.range (c.ι.app n).hom :=
            ⟨w, hNat.trans hEq⟩
          exact hx n hInR
        exact hT1.isClosed_singleton_of_notMem_range _ hOut
      · have hEmpty : (c.ι.app m).hom ⁻¹' {f (x n)} = ∅ := by
          ext y; rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          intro hy; exact hMem ⟨y, hy⟩
        rw [hEmpty]; exact isClosed_empty
    have hEclosed : ∀ j, IsClosed ((fun n => f (x n)) '' {n | j ≤ n}) := by
      intro j; rw [isClosed_iff_of_isColimit c hc]; intro m
      have hEq : (c.ι.app m).hom ⁻¹' ((fun n => f (x n)) '' {n | j ≤ n}) =
          ⋃ (n : ℕ), ⋃ (_ : n ∈ {n : ℕ | j ≤ n ∧ n < m}),
            (c.ι.app m).hom ⁻¹' {f (x n)} := by
        ext y; constructor
        · intro hy; rw [Set.mem_preimage] at hy
          obtain ⟨(n : ℕ), hn_mem, hnEq⟩ := hy
          have hnm : n < m := by
            by_contra hCon2; push Not at hCon2; exact hx n (hMono hCon2 ⟨y, hnEq.symm⟩)
          exact Set.mem_biUnion ⟨hn_mem, hnm⟩ (Set.mem_preimage.mpr
            (Set.mem_singleton_iff.mpr hnEq.symm))
        · intro hy
          obtain ⟨(n : ℕ), hn_mem, hy_mem⟩ := Set.mem_iUnion₂.mp hy
          have hYm : (c.ι.app m).hom y = f (x n) :=
            Set.mem_singleton_iff.mp (Set.mem_preimage.mp hy_mem)
          exact Set.mem_preimage.mpr ⟨n, hn_mem.1, hYm.symm⟩
      rw [hEq]
      have hFin : {n : ℕ | j ≤ n ∧ n < m}.Finite := by
        have hSetEq : {n : ℕ | j ≤ n ∧ n < m} = ↑(Finset.Ico j m) := by ext n; simp
        rw [hSetEq]; exact Finset.finite_toSet _
      exact hFin.isClosed_biUnion (fun n hn => hPiece m j n hn)
    have hInter : Set.range ⇑f ∩ ⋂ j, (fun n => f (x n)) '' {n | j ≤ n} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]; intro y hy
      obtain ⟨hyMem, hyAll⟩ := hy
      obtain ⟨x', rfl⟩ := hyMem; obtain ⟨N, z, hz⟩ := hCover x'
      obtain ⟨(n : ℕ), hn_mem, hnEq⟩ := Set.mem_iInter.mp hyAll N
      exact hx n (hMono hn_mem ⟨z, hz.trans hnEq.symm⟩)
    have hDisj : Disjoint (Set.range ⇑f) (⋂ j, (fun n => f (x n)) '' {n | j ≤ n}) :=
      Set.disjoint_iff_inter_eq_empty.mpr hInter
    obtain ⟨u, huDisj⟩ := hC.elim_finite_subfamily_closed _ hEclosed hDisj
    have hu : Set.range ⇑f ∩ ⋂ i ∈ u, (fun n => f (x n)) '' {n | i ≤ n} = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp huDisj
    by_cases hEmpty : u = ∅
    · subst hEmpty; have hUniv : (⋂ i ∈ (∅ : Finset ℕ),
          (fun n => f (x n)) '' {n | i ≤ n}) = Set.univ := by
        ext y; simp [Finset.notMem_empty]
      rw [hUniv, Set.inter_univ] at hu; have hMem : f (x 0) ∈ Set.range ⇑f := ⟨x 0, rfl⟩
      rw [hu] at hMem; exact Set.notMem_empty _ hMem
    · have hNe : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let N := u.sup id
      have hGe : ∀ i ∈ u, i ≤ N := fun i hi => Finset.le_sup (f := id) hi
      have hSubN : (fun n => f (x n)) '' {n | N ≤ n} ⊆
          ⋂ i ∈ u, (fun n => f (x n)) '' {n | i ≤ n} := by
        intro y hy; obtain ⟨(n : ℕ), hn_mem, hnEq⟩ := hy
        exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi =>
          ⟨n, le_trans (hGe i hi) hn_mem, hnEq⟩
      have hSubEmpty : Set.range ⇑f ∩ (fun n => f (x n)) '' {n | N ≤ n} = ∅ :=
        Set.eq_empty_of_subset_empty (hu ▸ Set.inter_subset_inter le_rfl hSubN)
      have hMemN : f (x N) ∈ Set.range ⇑f ∩
          (fun n => f (x n)) '' {n | N ≤ n} :=
        ⟨⟨x N, rfl⟩, ⟨N, show N ≤ N from le_rfl, rfl⟩⟩
      rw [hSubEmpty] at hMemN; exact Set.notMem_empty _ hMemN
  obtain ⟨N, hSub⟩ := hUni
  choose g hg using fun y => hSub ⟨y, rfl⟩
  have hEmb : IsEmbedding (c.ι.app N).hom := (hLeg N).isEmbedding
  have hEqFun : ⇑(c.ι.app N).hom ∘ g = ⇑f := funext fun y => hg y
  have hCont : Continuous g := hEmb.continuous_iff.mpr (hEqFun ▸ f.continuous)
  exact ⟨N, ⟨g, hCont⟩, ContinuousMap.ext fun y => hg y⟩
/-- Let F:ℕ→TopCat.{u} be a chain whose every transition map is a closed embedding with closed
codomain singletons outside its image. In any colimiting cocone c, every singular simplex of
c.pt is the image of a singular simplex of some F(j) under its colimit leg. -/
theorem toSSet_stage_exists
    {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (toSSet.obj c.pt).obj n) :
    ∃ (j : ℕ) (y : (toSSet.obj (F.obj j)).obj n),
      (toSSet.map (c.ι.app j)).app n y = x := by
  obtain ⟨j, g', hg'⟩ := exists_stage_of_compact c hc hF
    isCompact_univ (toSSetObjEquiv c.pt n x)
  refine ⟨j, (toSSetObjEquiv (F.obj j) n).symm g', ?_⟩
  apply (toSSetObjEquiv c.pt n).injective
  have hNat : (toSSetObjEquiv c.pt n) ((toSSet.map (c.ι.app j)).app n
        ((toSSetObjEquiv (F.obj j) n).symm g')) =
      (c.ι.app j).hom.comp g' := by
    have hRfl : (toSSetObjEquiv c.pt n) ((toSSet.map (c.ι.app j)).app n
        ((toSSetObjEquiv (F.obj j) n).symm g')) =
        (c.ι.app j).hom.comp ((toSSetObjEquiv (F.obj j) n)
          ((toSSetObjEquiv (F.obj j) n).symm g')) := rfl
    rwa [Equiv.apply_symm_apply] at hRfl
  rw [hNat]; exact hg'
end TopCat
