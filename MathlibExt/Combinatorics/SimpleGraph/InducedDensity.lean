/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Induced densities and the averaging identity

For graphs `H` on `k` vertices and `G` on `n` vertices, the induced density `p(H, G)` is the
probability that a uniformly random `k`-subset of the vertices of `G` induces a copy of `H`.
These densities are the basic quantities of Razborov's flag algebras (*Flag algebras*,
J. Symbolic Logic 72 (2007), 1239-1282, where they are written `p(M, N)` for finite models of a
universal theory, as in the abstract). Their basic identity is averaging: for `k ≤ l ≤ n`, the
density of `H` in `G` is the average, over the `l`-subsets `L`, of the density of `H` inside
`L` (`inducedDensity_eq_average`). Expanding the inner densities over the isomorphism types of
`G[L]` gives Razborov's chain rule `p(H, G) = ∑_F p(H, F) p(F, G)`, the identity that makes the
densities of the `l`-vertex graphs a linear model of those of the `k`-vertex graphs.

The averaging rests on a double count, valid for any property of `k`-sets
(`sum_card_filter_powersetCard`): each `k`-set lies in `C(n - k, l - k)` sets of size `l`
(`card_superset_powersetCard`).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.InducedDensity

open Finset

variable {V : Type*} [Fintype V]

/-- **Number of `l`-supersets of a `k`-set.** In a finite type with `n` elements, a set `K` with
`k ≤ l` elements is contained in exactly `C(n - k, l - k)` sets with `l` elements. -/
theorem card_superset_powersetCard [DecidableEq V] {K : Finset V} {l : ℕ} (hKl : K.card ≤ l) :
    #{L ∈ (univ : Finset V).powersetCard l | K ⊆ L} =
      (Fintype.card V - K.card).choose (l - K.card) := by
  rw [← card_univ, ← card_sdiff_of_subset (subset_univ K), ← card_powersetCard]
  refine card_nbij' (fun L => L \ K) (fun M => M ∪ K) ?_ ?_ ?_ ?_
  · intro L hL
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hL ⊢
    refine ⟨sdiff_subset_sdiff (subset_univ L) le_rfl, ?_⟩
    rw [card_sdiff_of_subset hL.2, hL.1]
  · intro M hM
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hM ⊢
    have hdisj : Disjoint M K := by
      rw [disjoint_left]; intro x hx hxK
      have := hM.1 hx; simp [hxK] at this
    refine ⟨?_, subset_union_right⟩
    rw [card_union_of_disjoint hdisj, hM.2]; omega
  · intro L hL
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at hL
    exact sdiff_union_of_subset hL.2
  · intro M hM
    simp only [mem_coe, mem_powersetCard] at hM
    have hdisj : Disjoint M K := by
      rw [disjoint_left]; intro x hx hxK
      have := hM.1 hx; simp [hxK] at this
    exact union_sdiff_cancel_right hdisj

/-- **Double counting `k`-sets inside `l`-sets.** For any property `P` of sets and `k ≤ l`,
summing over the `l`-sets `L` the number of `k`-subsets of `L` with property `P` counts every
`k`-set with property `P` exactly `C(n - k, l - k)` times. -/
theorem sum_card_filter_powersetCard (P : Finset V → Prop) [DecidablePred P] {k l : ℕ}
    (hkl : k ≤ l) :
    ∑ L ∈ (univ : Finset V).powersetCard l, #{K ∈ L.powersetCard k | P K} =
      (Fintype.card V - k).choose (l - k) * #{K ∈ (univ : Finset V).powersetCard k | P K} := by
  classical
  have h1 : ∀ L ∈ (univ : Finset V).powersetCard l, #{K ∈ L.powersetCard k | P K} =
      ∑ K ∈ (univ : Finset V).powersetCard k, if K ⊆ L ∧ P K then 1 else 0 := by
    intro L _
    rw [card_filter, ← sum_filter, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext K; simp [mem_powersetCard, and_comm, and_left_comm]
  rw [sum_congr rfl h1, sum_comm, card_filter, mul_sum]
  refine sum_congr rfl fun K hK => ?_
  rw [mem_powersetCard] at hK
  by_cases hP : P K
  · simp only [hP, and_true, ↓reduceIte, mul_one]
    rw [← card_filter, ← hK.2]
    exact card_superset_powersetCard (hK.2 ▸ hkl)
  · simp [hP]

open Classical in
/-- **Induced copies of `H` inside a vertex set.** For a graph `H` on `k` vertices, a graph `G`
on `V` and a finite set `L` of vertices, the number of `k`-subsets `K ⊆ L` such that the
subgraph of `G` induced on `K` is isomorphic to `H`. -/
noncomputable def inducedCountIn {k : ℕ} (H : _root_.SimpleGraph (Fin k))
    (G : _root_.SimpleGraph V) (L : Finset V) : ℕ :=
  #((L.powersetCard k).filter fun K : Finset V => Nonempty (H ≃g G.induce (K : Set V)))

/-- **Induced density of `H` inside a vertex set.** The proportion `p(H, G[L])` of the
`k`-subsets of `L` that induce a copy of `H` in `G`: `inducedCountIn H G L / C(|L|, k)`, the
density `p(H, G[L])` of Razborov's *Flag algebras*, J. Symbolic Logic 72 (2007). When `L` has
fewer than `k` elements there is no `k`-subset and the value is `0` for every `H` (`0 / 0`), which
is not a proportion; it is a probability only when `k ≤ |L|`. -/
noncomputable def inducedDensityIn {k : ℕ} (H : _root_.SimpleGraph (Fin k))
    (G : _root_.SimpleGraph V) (L : Finset V) : ℚ :=
  (inducedCountIn H G L : ℚ) / (L.card.choose k : ℚ)

/-- **Induced density.** For a graph `G` with at least `k` vertices, the probability `p(H, G)`
that a uniformly random `k`-subset of the vertices of `G` induces a copy of the `k`-vertex graph
`H` (Razborov, *Flag algebras*, J. Symbolic Logic 72 (2007), 1239-1282, abstract). When `G` has
fewer than `k` vertices there is no `k`-subset, and the value is `0` for every `H`, which is not a
probability. -/
noncomputable def inducedDensity {k : ℕ} (H : _root_.SimpleGraph (Fin k))
    (G : _root_.SimpleGraph V) : ℚ :=
  inducedDensityIn H G univ

/-- **Averaging identity for induced densities.** For a graph `H` on `k` vertices, a graph `G`
on `n` vertices and `k ≤ l ≤ n`, the induced density of `H` in `G` is the average of its
induced densities in the subgraphs of `G` induced on the `l`-subsets of vertices:
`p(H, G) = C(n, l)⁻¹ ∑_{|L| = l} p(H, G[L])`. Expanding `p(H, G[L])` over the isomorphism types
of `G[L]` gives the chain rule of Razborov's flag algebras (*Flag algebras*, J. Symbolic Logic 72
(2007), 1239-1282). -/
theorem inducedDensity_eq_average {k l : ℕ} (H : _root_.SimpleGraph (Fin k))
    (G : _root_.SimpleGraph V) (hkl : k ≤ l) (hln : l ≤ Fintype.card V) :
    inducedDensity H G =
      (∑ L ∈ (univ : Finset V).powersetCard l, inducedDensityIn H G L) /
        ((Fintype.card V).choose l : ℚ) := by
  classical
  set n := Fintype.card V
  have hsum : ∑ L ∈ (univ : Finset V).powersetCard l, inducedDensityIn H G L =
      ((n - k).choose (l - k) * inducedCountIn H G univ : ℕ) / (l.choose k : ℚ) := by
    have : ∀ L ∈ (univ : Finset V).powersetCard l, inducedDensityIn H G L =
        (inducedCountIn H G L : ℚ) / (l.choose k : ℚ) := by
      intro L hL
      rw [mem_powersetCard] at hL
      simp only [inducedDensityIn, hL.2]
    rw [sum_congr rfl this, ← sum_div]
    congr 1
    unfold inducedCountIn
    rw [← Nat.cast_sum]
    congr 1
    convert sum_card_filter_powersetCard
      (fun K : Finset V => Nonempty (H ≃g G.induce (K : Set V))) hkl using 2
  rw [hsum]
  simp only [inducedDensity, inducedDensityIn, card_univ]
  have hnk : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hkl.trans hln)).ne'
  have hlk : (l.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkl).ne'
  have hnl : (n.choose l : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hln).ne'
  have hmul : (n.choose l : ℚ) * l.choose k = n.choose k * (n - k).choose (l - k) := by
    exact_mod_cast Nat.choose_mul hkl
  have hc : ((Fintype.card V).choose k : ℚ) = n.choose k := rfl
  rw [hc]
  push_cast
  field_simp
  linear_combination (inducedCountIn H G univ : ℚ) * hmul

end MathlibExt.Combinatorics.SimpleGraph.InducedDensity
