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
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.CategoryTheory.Filtered.Final
public import
  MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import
  MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialColimit
/-!
# Compact separable maps into closed T1 linear colimits

Let J be a linear order with a least element, and let F:J→TopCat have closed T1-embedding
transition maps. Each continuous map from a compact separable space into a colimit of F factors
through one stage. In particular every singular simplex of the colimit comes from a stage.

A closed T1-embedding is a closed embedding whose codomain singleton is closed at every point
outside the image. The order universe v, ambient space universe u and compact-source universe w
are independent.
-/
@[expose] public section
universe w v u
open CategoryTheory Limits Topology
namespace TopCat
variable {J : Type v} [LinearOrder J] [OrderBot J]
/-- Let J be a linear order with a least element in universe v, and F:J→TopCat.{u} a diagram whose
every transition map is a closed embedding with closed codomain singletons outside its image.
For any colimiting cocone c and compact separable space K in universe w, each continuous
f:K→c.pt factors continuously through a stage F(j). The three universes u,v,w are independent. -/
theorem exists_stage_of_compact_transfinite
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    {K : Type w} [TopologicalSpace K] [TopologicalSpace.SeparableSpace K]
    (hK : IsCompact (Set.univ : Set K)) (f : C(K, ↥c.pt)) :
    ∃ (j : J) (g : C(K, ↥(F.obj j))),
      (c.ι.app j).hom.comp g = f := by
  have : Nonempty J := ⟨⊥⟩
  have hFclosed : ∀ ⦃i j : J⦄ (g : i ⟶ j), IsClosedEmbedding (F.map g).hom :=
    fun _ _ g => closedT1Embeddings_le_isClosedEmbedding _ (hF g)
  have hLeg : ∀ j, IsClosedEmbedding (c.ι.app j).hom := fun j =>
    isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding c hc hFclosed j
  have hcType : IsColimit ((forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hc
  have hMono : ∀ ⦃i k : J⦄ (_ : i ≤ k),
      Set.range (c.ι.app i).hom ⊆ Set.range (c.ι.app k).hom := by
    intro i k h y hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨(F.map (homOfLE h)).hom z, ConcreteCategory.congr_hom
      ((forget TopCat).congr_map (c.w (homOfLE h))) z⟩
  have hCover : ∀ x : K, ∃ j, f x ∈ Set.range (c.ι.app j).hom := by
    intro x
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType (f x)
    exact ⟨j, y, hy⟩
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense K
  have hStage : ∀ d : D, ∃ j, f d ∈ Set.range (c.ι.app j).hom := fun d => hCover d
  choose sj hsj using hStage
  have : Countable D := (Set.countable_coe_iff).mpr hDcount
  have hScount : (Set.range sj).Countable := Set.countable_range sj
  by_cases hBdd : ∃ β, ∀ s ∈ Set.range sj, s ≤ β
  · obtain ⟨β, hβ⟩ := hBdd
    have hSub : Set.range ⇑f ⊆ Set.range (c.ι.app β).hom := by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      have hx : x ∈ closure D := hDdense x
      have hmem : f x ∈ closure (f '' D) :=
        image_closure_subset_closure_image f.continuous ⟨x, hx, rfl⟩
      have hED : f '' D ⊆ Set.range (c.ι.app β).hom := by
        rintro y ⟨d, hd, rfl⟩
        exact hMono (hβ _ ⟨⟨d, hd⟩, rfl⟩) (hsj ⟨d, hd⟩)
      exact closure_minimal hED (hLeg β).isClosed_range hmem
    choose g hg using fun y => hSub ⟨y, rfl⟩
    have hEmb : IsEmbedding (c.ι.app β).hom := (hLeg β).isEmbedding
    have hEqFun : ⇑(c.ι.app β).hom ∘ g = ⇑f := funext fun y => hg y
    have hCont : Continuous g := hEmb.continuous_iff.mpr (hEqFun ▸ f.continuous)
    exact ⟨β, ⟨g, hCont⟩, ContinuousMap.ext fun y => hg y⟩
  · have hCof : ∀ j, ∃ s ∈ Set.range sj, j ≤ s := by
      intro j
      by_contra hCon
      exact hBdd ⟨j, fun s hs => le_of_not_ge (fun hjs => hCon ⟨s, hs, hjs⟩)⟩
    have hSne : (Set.range sj).Nonempty := by
      by_contra hEmpty
      rw [Set.not_nonempty_iff_eq_empty] at hEmpty
      exact hBdd ⟨⊥, fun s hs => absurd (hEmpty ▸ hs) (Set.notMem_empty s)⟩
    obtain ⟨e, he⟩ := hScount.exists_eq_range hSne
    have hmono : Monotone (fun n => (Finset.range (n + 1)).sup e) := by
      intro a b hab
      change (Finset.range (a + 1)).sup e ≤ (Finset.range (b + 1)).sup e
      apply Finset.sup_mono
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hcofinal : ∀ j, ∃ n, j ≤ (Finset.range (n + 1)).sup e := by
      intro j
      obtain ⟨s, hs, hjs⟩ := hCof j
      rw [he] at hs
      obtain ⟨n, rfl⟩ := hs
      exact ⟨n, hjs.trans (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n)))⟩
    have hFinal : hmono.functor.Final :=
      (Monotone.final_functor_iff hmono).mpr hcofinal
    have hcSeq : IsColimit (c.whisker hmono.functor) :=
      (Functor.Final.isColimitWhiskerEquiv hmono.functor _).2 hc
    obtain ⟨N, g, hg⟩ := TopCat.exists_stage_of_compact (c.whisker hmono.functor)
      hcSeq (fun _ _ g => hF (hmono.functor.map g)) hK f
    exact ⟨_, g, hg⟩
/-- Let J be a linear order with a least element in universe v, and F:J→TopCat.{u} a diagram whose
every transition map is a closed embedding with closed codomain singletons outside its image.
For a colimiting cocone c, every singular simplex of c.pt is the image of one from a stage F(j). -/
theorem toSSet_stage_exists_transfinite
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) (x : (toSSet.obj c.pt).obj n) :
    ∃ (j : J) (y : (toSSet.obj (F.obj j)).obj n),
      (toSSet.map (c.ι.app j)).app n y = x := by
  have : SecondCountableTopology (Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).secondCountableTopology
  obtain ⟨j, g', hg'⟩ := exists_stage_of_compact_transfinite c hc hF
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
  rw [hNat]
  exact hg'
end TopCat
