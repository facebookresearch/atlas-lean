/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationSum
import Code.Onsager.SpinWeightedAffine









namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_decoratedWeightedSpinWeight
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) : ℂ :=
  (ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) *
    ∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge

private theorem sum_finset_eq_sum_subtype
    {alpha R : Type*} [Fintype alpha] [DecidableEq alpha]
    [AddCommMonoid R] (S : Finset alpha) (f : alpha → R) :
    ∑ x ∈ S, f x = ∑ x : {x // x ∈ S}, f x.1 := by
  exact Finset.sum_subtype S (fun _ => Iff.rfl) f


theorem ons_weightedSpinCharacterSum_eq_decorated
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L weight a b =
      ∑ D : ons_DecoratedEvenSubgraph L,
        ons_decoratedWeightedSpinWeight L weight a b D := by
  unfold ons_weightedSpinCharacterSum
  rw [sum_finset_eq_sum_subtype]
  have hsum := Equiv.sum_comp (ons_decorationEquiv L)
    (fun D : ons_DecoratedEvenSubgraph L =>
      ons_decoratedWeightedSpinWeight L weight a b D)
  simpa [ons_decoratedWeightedSpinWeight, ons_originalEdgesOfDecorated] using hsum



theorem ons_portEdge_mem_originalEdgesOfDecorated_iff
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) (e : ons_Dart L) :
    ons_portEdge L e ∈ ons_originalEdgesOfDecorated L D ↔
      s(e, ons_dartRev L e) ∈ D.1 := by
  classical
  rw [← ons_decoratedExternalEdges_image L D, Finset.mem_image]
  constructor
  · rintro ⟨edge, hedge, hproj⟩
    have hdata := Finset.mem_filter.mp hedge
    have heq : edge = s(e, ons_dartRev L e) :=
      ons_decEdgeProjection_injective_of_external L hdata.2 ⟨e, rfl⟩ hproj
    simpa [heq] using hdata.1
  · intro hedge
    refine ⟨s(e, ons_dartRev L e), ?_, ons_decEdgeProjection_external L e⟩
    exact Finset.mem_filter.mpr ⟨hedge, ⟨e, rfl⟩⟩




theorem ons_weightedSpinEdgeCoefficient_eq_decorated
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (e : ons_Dart L) :
    ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) =
      ∑ D : ons_DecoratedEvenSubgraph L,
        if s(e, ons_dartRev L e) ∈ D.1 then
          ons_decoratedWeightedSpinWeight L weight a b D
        else 0 := by
  unfold ons_weightedSpinEdgeCoefficient
  rw [Finset.sum_filter, sum_finset_eq_sum_subtype]
  have hsum := Equiv.sum_comp (ons_decorationEquiv L)
    (fun D : ons_DecoratedEvenSubgraph L =>
      if s(e, ons_dartRev L e) ∈ D.1 then
        ons_decoratedWeightedSpinWeight L weight a b D
      else 0)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro F hF
  have hmem :
      s(e, ons_dartRev L e) ∈ ((ons_decorationEquiv L) F).1 ↔
        ons_portEdge L e ∈ F.1 := by
    rw [← ons_portEdge_mem_originalEdgesOfDecorated_iff L
      ((ons_decorationEquiv L) F) e]
    simp [ons_originalEdgesOfDecorated]
  by_cases hedge : ons_portEdge L e ∈ F.1
  · rw [if_pos hedge, if_pos (hmem.mpr hedge)]
    simp [ons_decoratedWeightedSpinWeight, ons_originalEdgesOfDecorated]
  · rw [if_neg hedge, if_neg (mt hmem.mp hedge)]



theorem ons_decoratedOriginalWeight_biUnion
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) =
      ∏ i, ∏ edge ∈
        (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection,
          weight edge := by
  classical
  have hcoverExt : ons_decoratedExternalEdges D.1 =
      Finset.univ.biUnion (fun i => ons_decoratedExternalEdges (piece i)) := by
    ext edge
    simp only [ons_decoratedExternalEdges, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    rw [hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  have hdisjProj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint
      (fun i => (ons_decoratedExternalEdges (piece i)).image
        ons_decEdgeProjection) := by
    intro i hi j hj hij
    change Disjoint
      ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)
      ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)
    rw [Finset.disjoint_left]
    intro edge hei hej
    rcases Finset.mem_image.mp hei with ⟨di, hdi, rfl⟩
    rcases Finset.mem_image.mp hej with ⟨dj, hdj, hproj⟩
    have hdiData := Finset.mem_filter.mp hdi
    have hdjData := Finset.mem_filter.mp hdj
    have hdart : di = dj :=
      ons_decEdgeProjection_injective_of_external L
        hdiData.2 hdjData.2 hproj.symm
    subst dj
    exact (Finset.disjoint_left.mp (hdisj hi hj hij)) hdiData.1 hdjData.1
  calc
    (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) =
        ∏ edge ∈
          (ons_decoratedExternalEdges D.1).image ons_decEdgeProjection,
            weight edge := by rw [ons_decoratedExternalEdges_image]
    _ = ∏ edge ∈ Finset.univ.biUnion (fun i =>
          (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection),
            weight edge := by rw [hcoverExt, Finset.biUnion_image]
    _ = ∏ i, ∏ edge ∈
          (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection,
            weight edge := by
      simpa using Finset.prod_biUnion hdisjProj



theorem ons_decoratedWeightedSpinWeight_factor_of_isotropic
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece)
    (hisotropic : ∀ i j, i ≠ j →
      ons_homologyIntersection
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection))
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)) = 0) :
    ons_decoratedWeightedSpinWeight L weight a b D =
      ∏ i,
        (ons_spinCharacter a b
          (ons_evenHomology L
            ((ons_decoratedExternalEdges (piece i)).image
              ons_decEdgeProjection)) : ℂ) *
          ∏ edge ∈
            (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection,
              weight edge := by
  let h : iota → Fin 2 × Fin 2 := fun i =>
    ons_evenHomology L
      ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)
  have hcharReal : ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) =
      ∏ i, ons_spinCharacter a b (h i) := by
    rw [ons_originalHomology_biUnion D piece hcover hdisj]
    exact ons_spinCharacter_sum_of_pairwise_intersection_zero
      a b Finset.univ h (by
        intro i _ j _ hij
        exact hisotropic i j hij)
  have hchar :
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) =
        ∏ i, (ons_spinCharacter a b (h i) : ℂ) := by
    exact_mod_cast hcharReal
  have hweight :=
    ons_decoratedOriginalWeight_biUnion weight D piece hcover hdisj
  rw [ons_decoratedWeightedSpinWeight, hchar, hweight,
    Finset.prod_mul_distrib]




theorem ons_decoratedWeightedSpinTerm_cycle_data
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (iota : Type) (_ : Fintype iota) (_ : DecidableEq iota)
      (base : iota → ons_Dart L)
      (p : (i : iota) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) ∧
      (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) =
        ∏ i, ∏ edge ∈ ons_walkOriginalEdges (p i), weight edge := by
  obtain ⟨iota, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  refine ⟨iota, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts, ?_⟩
  simpa only [ons_walkOriginalEdges, ons_walkExternalEdges] using
    ons_decoratedOriginalWeight_biUnion weight D
      (fun i => (p i).edges.toFinset) hcover hdisj

end StatMech.Onsager
