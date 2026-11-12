/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCharacter
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusDecoration

/-!

# Spin-character sums over decorated even subgraphs

The spin-character sums of the torus rewritten as sums over even subgraphs of the decorated graph,
factored over their cycles.

## i. Overview

Through the decoration bijection, each even subgraph `D` of the decorated graph corresponds to an
even subgraph `F` of the torus whose edges are the projections of the external edges of `D`. So the
character sum `∑_F χ_{a,b}(hom F) x^|F|` equals a sum over decorated even subgraphs. A decorated
even subgraph is a disjoint union of simple cycles; the power `x^|F|` factors over the cycles, and
so does the character when the homology classes of the cycles have pairwise zero intersection. This
is the form that the Kac-Ward loop expansion produces.

## ii. Key results

- `ons_originalEdgesOfDecorated` : the torus edge set of a decorated even subgraph
- `ons_decoratedSpinWeight` : the spin-character weight of a decorated even subgraph
- `ons_spinCharacterSum_eq_decorated` : the character sum as a sum over decorated even subgraphs
- `ons_decoratedSpinTerm_cycle_data` : cycle decomposition and weight factorization of each term

## iii. Table of contents

- A. Decorated and torus even subgraphs
- B. External edges and projection
- C. Spin weights
- D. Walks and cycles
- E. The decorated character sum

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- M. E. Fisher, *On the dimer solution of planar Ising models*, J. Math. Phys. 7 (1966) 1776-1781

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators StatMech.Ising

/-! ## A. Decorated and torus even subgraphs -/

/-- Even subgraphs of the `L × L` torus. -/
abbrev ons_TorusEvenSubgraph (L : ℕ) [Fact (2 < L)] :=
  {F : Finset (Sym2 (ZMod L × ZMod L)) //
    F ∈ evenSubgraphs (onsTorusGraph L)}

/-- Even subgraphs of the decorated graph of the torus. -/
abbrev ons_DecoratedEvenSubgraph (L : ℕ) [Fact (2 < L)] :=
  {D : Finset (Sym2 (ons_Dart L)) //
    D ∈ evenSubgraphs (ons_decGraph L)}

/-- The torus even subgraph corresponding to a decorated even subgraph under the decoration
bijection. -/
noncomputable def ons_originalEdgesOfDecorated
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((ons_decorationEquiv L).symm D).1

@[simp] lemma ons_originalEdgesOfDecorated_eq_portPatternEdges
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    ons_originalEdgesOfDecorated L D =
      ons_portPatternEdges L (ons_portPatternOfDecorated L D.1 D.2) :=
  rfl

lemma ons_originalEdgesOfDecorated_even
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    ons_originalEdgesOfDecorated L D ∈ evenSubgraphs (onsTorusGraph L) :=
  ((ons_decorationEquiv L).symm D).2

/-! ## B. External edges and projection -/

/-- An edge of the decorated graph is external if it joins a dart to its reverse. -/
def ons_decIsExternal {L : ℕ} (edge : Sym2 (ons_Dart L)) : Prop :=
  ∃ d : ons_Dart L, edge = s(d, ons_dartRev L d)

/-- The external edges of a decorated edge set. -/
noncomputable def ons_decoratedExternalEdges {L : ℕ}
    (D : Finset (Sym2 (ons_Dart L))) : Finset (Sym2 (ons_Dart L)) := by
  classical
  exact D.filter ons_decIsExternal

/-- The projection of a decorated edge to the torus, taking each dart to its starting site. -/
def ons_decEdgeProjection {L : ℕ}
    (edge : Sym2 (ons_Dart L)) : Sym2 (ZMod L × ZMod L) :=
  Sym2.map Prod.fst edge

@[simp] lemma ons_decEdgeProjection_external (L : ℕ) (d : ons_Dart L) :
    ons_decEdgeProjection s(d, ons_dartRev L d) = ons_portEdge L d :=
  rfl

lemma ons_decEdgeProjection_injective_of_external
    (L : ℕ) [Fact (2 < L)]
    {edge edge' : Sym2 (ons_Dart L)}
    (he : ons_decIsExternal edge) (he' : ons_decIsExternal edge')
    (hproj : ons_decEdgeProjection edge = ons_decEdgeProjection edge') :
    edge = edge' := by
  rcases he with ⟨d, rfl⟩
  rcases he' with ⟨e, rfl⟩
  simp only [ons_decEdgeProjection_external] at hproj
  rcases (ons_portEdge_eq_iff L e d).mp hproj with h | h
  · subst d
    rfl
  · subst d
    rw [ons_dartRev_involutive]
    exact Sym2.eq_swap

lemma ons_decoratedExternalEdges_image
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    (ons_decoratedExternalEdges D.1).image ons_decEdgeProjection =
      ons_originalEdgesOfDecorated L D := by
  classical
  rw [ons_originalEdgesOfDecorated_eq_portPatternEdges]
  ext edge
  constructor
  · rw [Finset.mem_image]
    rintro ⟨edge', hedge', hproj⟩
    rw [ons_decoratedExternalEdges, Finset.mem_filter] at hedge'
    rcases hedge'.2 with ⟨d, rfl⟩
    rw [ons_decEdgeProjection_external] at hproj
    subst edge
    rw [ons_portEdge_mem_portPatternEdges_iff]
    change ons_decoratedPortBit D.1 d = 1
    simp [ons_decoratedPortBit, hedge'.1]
  · intro hedge
    rw [ons_portPatternEdges, Finset.mem_image] at hedge
    rcases hedge with ⟨d, hd, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have hdD : s(d, ons_dartRev L d) ∈ D.1 := by
      change (if s(d, ons_dartRev L d) ∈ D.1 then (1 : Fin 2) else 0) = 1 at hd
      simpa using hd
    rw [Finset.mem_image]
    refine ⟨s(d, ons_dartRev L d), ?_, ons_decEdgeProjection_external L d⟩
    rw [ons_decoratedExternalEdges, Finset.mem_filter]
    exact ⟨hdD, ⟨d, rfl⟩⟩

lemma ons_originalEdgesOfDecorated_card
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    (ons_originalEdgesOfDecorated L D).card =
      (ons_decoratedExternalEdges D.1).card := by
  classical
  rw [← ons_decoratedExternalEdges_image L D]
  apply Finset.card_image_of_injOn
  intro edge hedge edge' hedge' hproj
  have hext := (Finset.mem_filter.mp (Finset.mem_coe.mp hedge)).2
  have hext' := (Finset.mem_filter.mp (Finset.mem_coe.mp hedge')).2
  exact ons_decEdgeProjection_injective_of_external L hext hext' hproj

/-! ## C. Spin weights -/

/-- The weight `χ_{a,b}(hom F) x^|F|` of the torus even subgraph `F` corresponding to a decorated
even subgraph. -/
noncomputable def ons_decoratedSpinWeight
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) : ℝ :=
  let F := ons_originalEdgesOfDecorated L D
  ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

lemma ons_decoratedSpinWeight_eq_external
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) :
    ons_decoratedSpinWeight L x a b D =
      ons_spinCharacter a b
          (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) *
        x ^ (ons_decoratedExternalEdges D.1).card := by
  change ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) *
        x ^ (ons_originalEdgesOfDecorated L D).card = _
  rw [ons_originalEdgesOfDecorated_card]

/-! ## D. Walks and cycles -/

/-- The external edges used by a walk in the decorated graph. -/
noncomputable def ons_walkExternalEdges {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : Finset (Sym2 (ons_Dart L)) :=
  ons_decoratedExternalEdges p.edges.toFinset

/-- The torus edges underlying the external edges of a decorated walk. -/
noncomputable def ons_walkOriginalEdges {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  (ons_walkExternalEdges p).image ons_decEdgeProjection

lemma ons_walkOriginalEdges_even {L : ℕ} [Fact (2 < L)]
    {v : ons_Dart L} (p : (ons_decGraph L).Walk v v)
    (hp : p.IsCycle) :
    ons_walkOriginalEdges p ∈ evenSubgraphs (onsTorusGraph L) := by
  let D : ons_DecoratedEvenSubgraph L :=
    ⟨p.edges.toFinset,
      ons_cycle_edges_evenSubgraph (ons_decGraph L) p hp⟩
  have h := ons_originalEdgesOfDecorated_even L D
  rw [← ons_decoratedExternalEdges_image L D] at h
  simpa only [ons_walkOriginalEdges, ons_walkExternalEdges, D] using h

lemma ons_decoratedExternalEdges_card_biUnion
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : Finset (Sym2 (ons_Dart L)))
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    (ons_decoratedExternalEdges D).card =
      ∑ i, (ons_decoratedExternalEdges (piece i)).card := by
  classical
  have hcoverExt : ons_decoratedExternalEdges D =
      Finset.univ.biUnion (fun i => ons_decoratedExternalEdges (piece i)) := by
    ext edge
    simp only [ons_decoratedExternalEdges, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    rw [hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  rw [hcoverExt]
  exact Finset.card_biUnion (fun i hi j hj hij =>
    (hdisj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))

lemma ons_decoratedExternal_pow_factor
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (x : ℝ) (D : Finset (Sym2 (ons_Dart L)))
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    x ^ (ons_decoratedExternalEdges D).card =
      ∏ i, x ^ (ons_decoratedExternalEdges (piece i)).card := by
  rw [ons_decoratedExternalEdges_card_biUnion D piece hcover hdisj,
    Finset.prod_pow_eq_pow_sum]

lemma ons_originalHomology_biUnion
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
      ∑ i, ons_evenHomology L
        ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection) := by
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
    ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
        ons_evenHomology L
          ((ons_decoratedExternalEdges D.1).image ons_decEdgeProjection) := by
      rw [ons_decoratedExternalEdges_image]
    _ = ons_evenHomology L
        (Finset.univ.biUnion (fun i =>
          (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) := by
      rw [hcoverExt, Finset.biUnion_image]
    _ = ∑ i, ons_evenHomology L
        ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection) :=
      ons_evenHomology_biUnion Finset.univ _ hdisjProj

lemma ons_decoratedSpinWeight_factor_of_isotropic
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (x : ℝ) (a b : Fin 2) (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece)
    (hisotropic : ∀ i j, i ≠ j →
      ons_homologyIntersection
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection))
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)) = 0) :
    ons_decoratedSpinWeight L x a b D =
      ∏ i,
        ons_spinCharacter a b
            (ons_evenHomology L
              ((ons_decoratedExternalEdges (piece i)).image
                ons_decEdgeProjection)) *
          x ^ (ons_decoratedExternalEdges (piece i)).card := by
  let h : iota → Fin 2 × Fin 2 := fun i =>
    ons_evenHomology L
      ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)
  have hchar : ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) =
      ∏ i, ons_spinCharacter a b (h i) := by
    rw [ons_originalHomology_biUnion D piece hcover hdisj]
    exact ons_spinCharacter_sum_of_pairwise_intersection_zero
      a b Finset.univ h (by
        intro i _ j _ hij
        exact hisotropic i j hij)
  have hpow := ons_decoratedExternal_pow_factor x D.1 piece hcover hdisj
  rw [ons_decoratedSpinWeight_eq_external, hchar, hpow,
    Finset.prod_mul_distrib]

/-! ## E. The decorated character sum -/

lemma ons_spinCharacterSum_eq_decorated
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2) :
    ons_spinCharacterSum L x a b =
      ∑ D : ons_DecoratedEvenSubgraph L,
        ons_decoratedSpinWeight L x a b D := by
  unfold ons_spinCharacterSum
  rw [← Finset.sum_coe_sort]
  have hsum := Equiv.sum_comp (ons_decorationEquiv L)
    (fun D : ons_DecoratedEvenSubgraph L =>
      ons_decoratedSpinWeight L x a b D)
  simpa [ons_decoratedSpinWeight, ons_originalEdgesOfDecorated] using hsum

lemma ons_decoratedSpinTerm_cycle_decomposition
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) := by
  exact ons_trivalent_even_cycle_decomposition
    (ons_decGraph L) (ons_decGraph_degree_le_three L) D.1 D.2

lemma ons_decoratedSpinTerm_cycle_weight_factor
    (L : ℕ) [Fact (2 < L)] (x : ℝ)
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) ∧
      x ^ (ons_originalEdgesOfDecorated L D).card =
        ∏ i, x ^ (ons_walkExternalEdges (p i)).card := by
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  refine ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts, ?_⟩
  rw [ons_originalEdgesOfDecorated_card]
  exact ons_decoratedExternal_pow_factor x D.1
    (fun i => (p i).edges.toFinset) hcover hdisj

lemma ons_decoratedSpinTerm_cycle_data
    (L : ℕ) [Fact (2 < L)] (x : ℝ)
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) ∧
      x ^ (ons_originalEdgesOfDecorated L D).card =
        ∏ i, x ^ (ons_walkExternalEdges (p i)).card ∧
      ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
        ∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i)) := by
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  refine ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts, ?_, ?_⟩
  · rw [ons_originalEdgesOfDecorated_card]
    exact ons_decoratedExternal_pow_factor x D.1
      (fun i => (p i).edges.toFinset) hcover hdisj
  · simpa only [ons_walkOriginalEdges, ons_walkExternalEdges] using
      ons_originalHomology_biUnion D
        (fun i => (p i).edges.toFinset) hcover hdisj

end StatMech.Onsager
