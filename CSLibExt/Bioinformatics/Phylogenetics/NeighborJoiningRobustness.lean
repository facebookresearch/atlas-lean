/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Robustness of neighbor joining: the cherry step

Neighbor joining (`NJRun` in `NeighborJoining.lean`) is exact on tree metrics: on the
path-length metric `d` of a binary phylogenetic tree with positive edge lengths, every pair
minimizing the Q-criterion is a cherry (`exists_adj_adj_of_qCriterion_min`). Atteson (1999)
showed that neighbor joining tolerates noise: if a dissimilarity `D` satisfies
`|D x y - d x y| < μ / 2` for all taxa, where `μ` is the shortest internal edge length, then
neighbor joining run on `D` returns the topology of the tree (its `ℓ∞` radius is `1/2`).

This file proves the selection step of that theorem: under the perturbation bound, every pair
of taxa minimizing the Q-criterion of `D` is a cherry of the tree. The induction over the
whole run is recorded in
`WantedExt/Biology/Phylogenetics/NeighborJoiningRobustnessWanted.lean`; it needs an invariant
weaker than the `ℓ∞` bound, which the neighbor-joining update does not preserve in general
(the new errors are only bounded by `3/2` times the old bound), such as the quartet
consistency and quartet additivity conditions of Mihaescu, Levy and Pachter (2009).

Only internal edges enter the bound: pendant edge lengths do not affect which pairs neighbor
joining selects. The dissimilarity `D` is assumed symmetric with zero diagonal, as in the
sources (the Q-criterion sums include the diagonal entries).

## Proof outline

The tree metric is written as a sum over splits (`dist_eq_sum_darts`). For distinct taxa the
Q-criterion differences are sums of four- and six-point terms:
`Q(x,y) - Q(x,k) = ∑_{z ∉ {x,y,k}} (D x y + D k z - D x k - D y z)` and
`Q(x,y) - Q(a,b) = ∑_{z ∉ {x,y,a,b}} (D x y + D a z + D b z - D a b - D x z - D y z)`.
If the minimizing pair `x, y` is not a cherry, either `x` (or `y`) has a sibling leaf `k`,
and every four-point term is at least `2μ` on the tree metric while its error is below `2μ`;
or neither has, and comparing with a cherry `a, b` inside the smaller of the two subtrees
next to `x` and `y`, each six-point term of a taxon outside that subtree is positive, and
the terms of the taxa inside it are dominated by pairing them with the taxa outside
(an averaging argument). Every comparison is a nonnegativity statement for the coefficient
of each split, which follows from the compatibility of the splits.

The two-case structure follows the proof of Theorem 16 of Mihaescu, Levy and Pachter (2009);
the bounds here are carried out directly on the `ℓ∞` hypothesis.

## Main results

* `exists_adj_adj_of_qCriterion_min_of_abs_sub_lt`: on a dissimilarity within `μ / 2` of the
  path-length metric of a binary phylogenetic tree whose internal edges have length at least
  `μ`, a pair of taxa minimizing the Q-criterion is a cherry.
* `NJRun.exists_adj_adj_of_join_init_of_abs_sub_lt`: the first join of neighbor joining on
  such a dissimilarity joins a cherry.
* `exists_eq_pair_of_qCriterion_min_of_abs_sub_lt`: the same statement for compatible binary
  split systems.

## References

* K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*,
  Algorithmica 25 (1999), 251–278.
* R. Mihaescu, D. Levy and L. Pachter, *Why neighbor-joining works*, Algorithmica 54 (2009),
  1–24.
* J. A. Studier and K. J. Keppler, *A note on the neighbor-joining algorithm of Saitou and
  Nei*, Mol. Biol. Evol. 5 (1988), 729–731.
-/
@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoining

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The cut indicator of a set `B`: `1` if `B` separates `u` and `v`, `0` otherwise. -/
private def sep (B : Finset X) (u v : X) : ℝ := if (u ∈ B ↔ v ∈ B) then 0 else 1

/-- The Q-criterion of two taxa (the singleton form of `qCriterion`). -/
private def nj (D : X → X → ℝ) (u v : X) : ℝ :=
  ((Fintype.card X : ℝ) - 2) * D u v - ∑ z, D u z - ∑ z, D v z

private lemma cpt_list {S B : Finset X} (h : Disjoint S B ∨ S ⊆ B ∨ B ⊆ S ∨ S ∪ B = univ)
    (L₁ L₂ : List X) (h₁ : ∀ p ∈ L₁, p ∈ S) (h₂ : ∀ p ∈ L₂, p ∉ S) :
    ¬ ((∃ p ∈ L₁, p ∈ B) ∧ (∃ p ∈ L₁, p ∉ B) ∧ (∃ p ∈ L₂, p ∈ B) ∧ (∃ p ∈ L₂, p ∉ B)) := by
  rintro ⟨⟨p, hp, hpB⟩, ⟨q, hq, hqB⟩, ⟨r, hr, hrB⟩, ⟨t, ht, htB⟩⟩
  rcases h with h | h | h | h
  · exact Finset.disjoint_left.mp h (h₁ p hp) hpB
  · exact hqB (h (h₁ q hq))
  · exact h₂ r hr (h hrB)
  · have : t ∈ S ∪ B := h ▸ Finset.mem_univ t
    rcases Finset.mem_union.mp this with h' | h'
    · exact h₂ t ht h'
    · exact htB h'

private lemma sum_univ_eq_three (f : X → ℝ) {x y k : X} (hxy : x ≠ y) (hxk : x ≠ k)
    (hyk : y ≠ k) :
    ∑ z, f z = f x + f y + f k + ∑ z ∈ ((univ.erase x).erase y).erase k, f z := by
  rw [← add_sum_erase univ f (mem_univ x),
    ← add_sum_erase (univ.erase x) f (mem_erase.mpr ⟨hxy.symm, mem_univ y⟩),
    ← add_sum_erase ((univ.erase x).erase y) f
      (mem_erase.mpr ⟨hyk.symm, mem_erase.mpr ⟨hxk.symm, mem_univ k⟩⟩)]
  ring

private lemma sum_univ_eq_four (f : X → ℝ) {x y a b : X} (hxy : x ≠ y) (hxa : x ≠ a)
    (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b) :
    ∑ z, f z = f x + f y + f a + f b +
      ∑ z ∈ (((univ.erase x).erase y).erase a).erase b, f z := by
  rw [← add_sum_erase univ f (mem_univ x),
    ← add_sum_erase (univ.erase x) f (mem_erase.mpr ⟨hxy.symm, mem_univ y⟩),
    ← add_sum_erase ((univ.erase x).erase y) f
      (mem_erase.mpr ⟨hya.symm, mem_erase.mpr ⟨hxa.symm, mem_univ a⟩⟩),
    ← add_sum_erase (((univ.erase x).erase y).erase a) f
      (mem_erase.mpr ⟨hab.symm, mem_erase.mpr ⟨hyb.symm, mem_erase.mpr ⟨hxb.symm,
        mem_univ b⟩⟩⟩)]
  ring

private lemma card_erase_three {x y k : X} (hxy : x ≠ y) (hxk : x ≠ k) (hyk : y ≠ k) :
    ((((univ.erase x).erase y).erase k).card : ℝ) = Fintype.card X - 3 := by
  have h1 := card_erase_add_one (mem_univ x)
  have h2 := card_erase_add_one (mem_erase.mpr ⟨hxy.symm, mem_univ y⟩)
  have h3 := card_erase_add_one
    (mem_erase.mpr ⟨hyk.symm, mem_erase.mpr ⟨hxk.symm, mem_univ k⟩⟩)
  rw [card_univ] at h1
  have : (((univ.erase x).erase y).erase k).card + 3 = Fintype.card X := by omega
  rw [← this]
  push_cast
  ring

private lemma card_erase_four {x y a b : X} (hxy : x ≠ y) (hxa : x ≠ a)
    (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b) :
    (((((univ.erase x).erase y).erase a).erase b).card : ℝ) = Fintype.card X - 4 := by
  have h1 := card_erase_add_one (mem_univ x)
  have h2 := card_erase_add_one (mem_erase.mpr ⟨hxy.symm, mem_univ y⟩)
  have h3 := card_erase_add_one
    (mem_erase.mpr ⟨hya.symm, mem_erase.mpr ⟨hxa.symm, mem_univ a⟩⟩)
  have h4 := card_erase_add_one
    (mem_erase.mpr ⟨hab.symm, mem_erase.mpr ⟨hyb.symm, mem_erase.mpr ⟨hxb.symm,
        mem_univ b⟩⟩⟩)
  rw [card_univ] at h1
  have : ((((univ.erase x).erase y).erase a).erase b).card + 4 = Fintype.card X := by omega
  rw [← this]
  push_cast
  ring

private lemma nj_sub_nj_three {D : X → X → ℝ} (hDsymm : ∀ x y, D x y = D y x)
    (hD0 : ∀ x, D x x = 0) {x y k : X} (hxy : x ≠ y) (hxk : x ≠ k) (hyk : y ≠ k) :
    nj D x y - nj D x k = ∑ z ∈ ((univ.erase x).erase y).erase k,
      (D x y + D k z - D x k - D y z) := by
  have hs : ∑ z ∈ ((univ.erase x).erase y).erase k, (D x y + D k z - D x k - D y z) =
      ((((univ.erase x).erase y).erase k).card : ℝ) * (D x y - D x k) +
        ∑ z ∈ ((univ.erase x).erase y).erase k, D k z -
        ∑ z ∈ ((univ.erase x).erase y).erase k, D y z := by
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hs, card_erase_three hxy hxk hyk]
  unfold nj
  rw [sum_univ_eq_three (D y) hxy hxk hyk, sum_univ_eq_three (D k) hxy hxk hyk]
  linear_combination (-1 : ℝ) * hDsymm y x + hDsymm k x + hDsymm k y - hD0 y + hD0 k

private lemma nj_sub_nj_four {D : X → X → ℝ} (hDsymm : ∀ x y, D x y = D y x)
    (hD0 : ∀ x, D x x = 0) {x y a b : X} (hxy : x ≠ y) (hxa : x ≠ a)
    (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b) :
    nj D x y - nj D a b = ∑ z ∈ (((univ.erase x).erase y).erase a).erase b,
      (D x y + D a z + D b z - D a b - D x z - D y z) := by
  have hs : ∑ z ∈ (((univ.erase x).erase y).erase a).erase b,
      (D x y + D a z + D b z - D a b - D x z - D y z) =
      (((((univ.erase x).erase y).erase a).erase b).card : ℝ) * (D x y - D a b) +
        ∑ z ∈ (((univ.erase x).erase y).erase a).erase b, D a z +
        ∑ z ∈ (((univ.erase x).erase y).erase a).erase b, D b z -
        ∑ z ∈ (((univ.erase x).erase y).erase a).erase b, D x z -
        ∑ z ∈ (((univ.erase x).erase y).erase a).erase b, D y z := by
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hs, card_erase_four hxy hxa hxb hya hyb hab]
  unfold nj
  rw [sum_univ_eq_four (D x) hxy hxa hxb hya hyb hab,
    sum_univ_eq_four (D y) hxy hxa hxb hya hyb hab,
    sum_univ_eq_four (D a) hxy hxa hxb hya hyb hab,
    sum_univ_eq_four (D b) hxy hxa hxb hya hyb hab]
  linear_combination (-1 : ℝ) * hDsymm y x + hDsymm b a + hDsymm a x + hDsymm b x +
    hDsymm a y + hDsymm b y - hD0 x - hD0 y + hD0 a + hD0 b

omit [Fintype X] in
/-- Every side with at least two taxa contains a two-element side. -/
private lemma exists_pair_side {E : Type*} {A : E → Finset X} (hne : ∀ e, (A e).Nonempty)
    (hbin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e)
    (e : E) (h2 : 2 ≤ (A e).card) :
    ∃ e' a b, a ≠ b ∧ A e' = {a, b} ∧ A e' ⊆ A e := by
  suffices H : ∀ m, ∀ e, (A e).card = m → 2 ≤ m →
      ∃ e' a b, a ≠ b ∧ A e' = {a, b} ∧ A e' ⊆ A e from H _ e rfl h2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro e hm h2
    obtain ⟨e₁, e₂, hd, hu⟩ := hbin e (hm ▸ h2)
    have c := card_union_of_disjoint hd
    rw [hu, hm] at c
    have p₁ := (hne e₁).card_pos
    have p₂ := (hne e₂).card_pos
    by_cases h₁ : 2 ≤ (A e₁).card
    · obtain ⟨e', a, b, hab, he', hsub⟩ := ih _ (by omega) e₁ rfl h₁
      exact ⟨e', a, b, hab, he', hsub.trans (hu ▸ subset_union_left)⟩
    by_cases h₂ : 2 ≤ (A e₂).card
    · obtain ⟨e', a, b, hab, he', hsub⟩ := ih _ (by omega) e₂ rfl h₂
      exact ⟨e', a, b, hab, he', hsub.trans (hu ▸ subset_union_right)⟩
    obtain ⟨a, ha⟩ := card_eq_one.mp (by omega : (A e₁).card = 1)
    obtain ⟨b, hb⟩ := card_eq_one.mp (by omega : (A e₂).card = 1)
    refine ⟨e, a, b, ?_, ?_, subset_rfl⟩
    · rw [ha, hb, disjoint_singleton] at hd
      exact hd
    · rw [← hu, ha, hb]
      exact (insert_eq a {b}).symm

/-- The two branches at the neighbor of the leaf `u`, the one holding `v` being `P`. -/
private lemma decomp {E : Type*} {A : E → Finset X}
    (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hbin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e)
    (hsingle : ∀ z, ∃ e, A e = {z}) (hX : 3 ≤ Fintype.card X) {u v : X} (huv : u ≠ v) :
    ∃ eH eP, v ∈ A eP ∧ u ∉ A eH ∧ u ∉ A eP ∧ Disjoint (A eH) (A eP) ∧
      ∀ z, z = u ∨ z ∈ A eH ∨ z ∈ A eP := by
  obtain ⟨e₀, he₀⟩ := hsingle u
  obtain ⟨e₀', he₀'⟩ := hcompl e₀
  rw [he₀] at he₀'
  have hcard : 2 ≤ (A e₀').card := by
    rw [he₀', card_sdiff_of_subset (subset_univ _), card_univ, card_singleton]
    omega
  obtain ⟨e₁, e₂, hd, hu⟩ := hbin e₀' hcard
  rw [he₀'] at hu
  have hmem : ∀ z, z ≠ u → z ∈ A e₁ ∨ z ∈ A e₂ := by
    intro z hz
    have : z ∈ A e₁ ∪ A e₂ := by rw [hu]; simp [hz]
    exact mem_union.mp this
  have hnot : ∀ e, A e ⊆ univ \ {u} → u ∉ A e := fun e h hu' => by
    have := h hu'
    simp at this
  have h₁ : u ∉ A e₁ := hnot e₁ (hu ▸ subset_union_left)
  have h₂ : u ∉ A e₂ := hnot e₂ (hu ▸ subset_union_right)
  rcases hmem v huv.symm with hv | hv
  · refine ⟨e₂, e₁, hv, h₂, h₁, hd.symm, fun z => ?_⟩
    by_cases hz : z = u
    · exact Or.inl hz
    · rcases hmem z hz with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  · refine ⟨e₁, e₂, hv, h₁, h₂, hd, fun z => ?_⟩
    by_cases hz : z = u
    · exact Or.inl hz
    · exact Or.inr (hmem z hz)

private lemma le_sum_of_two {E : Type*} [Fintype E] (f : E → ℝ) (hf : ∀ e, 0 ≤ f e)
    {e₁ e₂ : E} (h12 : e₁ ≠ e₂) : f e₁ + f e₂ ≤ ∑ e, f e := by
  classical
  have := sum_le_sum_of_subset_of_nonneg (subset_univ {e₁, e₂}) (fun e _ _ => hf e)
  rwa [sum_pair h12] at this

private lemma le_sum_of_four {E : Type*} [Fintype E] (f : E → ℝ) (hf : ∀ e, 0 ≤ f e)
    {e₁ e₂ e₃ e₄ : E} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h14 : e₁ ≠ e₄) (h23 : e₂ ≠ e₃)
    (h24 : e₂ ≠ e₄) (h34 : e₃ ≠ e₄) : f e₁ + f e₂ + f e₃ + f e₄ ≤ ∑ e, f e := by
  classical
  have := sum_le_sum_of_subset_of_nonneg (subset_univ {e₁, e₂, e₃, e₄}) (fun e _ _ => hf e)
  rw [sum_insert (by simp [h12, h13, h14]), sum_insert (by simp [h23, h24]),
    sum_pair h34] at this
  linarith

/-- The four-point coefficient `sep u v + sep k z - sep u k - sep v z` of a split compatible
with the side `{u, k}` is nonnegative. -/
private lemma c4_nonneg {B : Finset X} {u v k z : X}
    (hc : Disjoint ({u, k} : Finset X) B ∨ {u, k} ⊆ B ∨ B ⊆ {u, k} ∨ {u, k} ∪ B = univ)
    (hvu : v ≠ u) (hvk : v ≠ k) (hzu : z ≠ u) (hzk : z ≠ k) :
    0 ≤ sep B u v + sep B k z - sep B u k - sep B v z := by
  have h := cpt_list hc [u, k] [v, z] (by simp) (by simp [hvu, hvk, hzu, hzk])
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    at h
  unfold sep
  by_cases hu : u ∈ B <;> by_cases hk : k ∈ B <;> by_cases hv : v ∈ B <;>
    by_cases hz : z ∈ B <;> simp_all

/-- The coefficient of a split in `h z = D x y + D a z + D b z - D a b - D x z - D y z`. -/
private def c6 (B : Finset X) (x y a b z : X) : ℝ :=
  sep B x y + sep B a z + sep B b z - sep B a b - sep B x z - sep B y z

/-- For `z` on the `y`-branch `P` of `x`, every split compatible with the side `{a, b}`
(off `P`) and with `P` has a nonnegative coefficient. -/
private lemma c6_nonneg {B P : Finset X} {x y a b z : X}
    (hcab : Disjoint ({a, b} : Finset X) B ∨ {a, b} ⊆ B ∨ B ⊆ {a, b} ∨ {a, b} ∪ B = univ)
    (hcP : Disjoint P B ∨ P ⊆ B ∨ B ⊆ P ∨ P ∪ B = univ)
    (haP : a ∉ P) (hbP : b ∉ P) (hxP : x ∉ P) (hyP : y ∈ P) (hzP : z ∈ P)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    0 ≤ c6 B x y a b z := by
  have hya : y ≠ a := fun h => haP (h ▸ hyP)
  have hyb : y ≠ b := fun h => hbP (h ▸ hyP)
  have hza : z ≠ a := fun h => haP (h ▸ hzP)
  have hzb : z ≠ b := fun h => hbP (h ▸ hzP)
  have h₁ := cpt_list hcab [a, b] [x, y, z] (by simp) (by simp [*])
  have h₂ := cpt_list hcP [y, z] [a, b, x] (by simp [*]) (by simp [*])
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    at h₁ h₂
  unfold c6 sep
  by_cases ha : a ∈ B <;> by_cases hb : b ∈ B <;> by_cases hx : x ∈ B <;>
    by_cases hy : y ∈ B <;> by_cases hz : z ∈ B <;> simp_all

/-- For `z` off `P` and `z'` on `P`, the summed coefficient of every compatible split is
nonnegative. -/
private lemma c6_add_nonneg {B P : Finset X} {x y a b z z' : X}
    (hcab : Disjoint ({a, b} : Finset X) B ∨ {a, b} ⊆ B ∨ B ⊆ {a, b} ∨ {a, b} ∪ B = univ)
    (hcP : Disjoint P B ∨ P ⊆ B ∨ B ⊆ P ∨ P ∪ B = univ)
    (haP : a ∉ P) (hbP : b ∉ P) (hxP : x ∉ P) (hyP : y ∈ P) (hzP : z ∉ P) (hz'P : z' ∈ P)
    (hxa : x ≠ a) (hxb : x ≠ b) (hza : z ≠ a) (hzb : z ≠ b) :
    0 ≤ c6 B x y a b z + c6 B x y a b z' := by
  have hya : y ≠ a := fun h => haP (h ▸ hyP)
  have hyb : y ≠ b := fun h => hbP (h ▸ hyP)
  have hz'a : z' ≠ a := fun h => haP (h ▸ hz'P)
  have hz'b : z' ≠ b := fun h => hbP (h ▸ hz'P)
  have h₁ := cpt_list hcab [a, b] [x, y, z, z'] (by simp) (by simp [*])
  have h₂ := cpt_list hcP [y, z'] [a, b, x, z] (by simp [*]) (by simp [*])
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    at h₁ h₂
  unfold c6 sep
  by_cases ha : a ∈ B <;> by_cases hb : b ∈ B <;> by_cases hx : x ∈ B <;>
    by_cases hy : y ∈ B <;> by_cases hz : z ∈ B <;> by_cases hz' : z' ∈ B <;> simp_all

omit [Fintype X] [DecidableEq X] in
private lemma ne_of_mem {E : Type*} {A : E → Finset X} {e e' : E} {z : X} (h : z ∈ A e)
    (h' : z ∉ A e') : e ≠ e' := fun h'' => h' (h'' ▸ h)

omit [Fintype X] [DecidableEq X] in
/-- Averaging: if every element of `J` contributes positively, every cross pair has positive
total, and `|I| ≤ |J|`, then the total over `I` and `J` is positive. -/
private lemma sum_add_sum_pos {I J : Finset X} (f : X → ℝ) (hJ : J.Nonempty)
    (hcard : I.card ≤ J.card) (h₁ : ∀ z ∈ J, 0 < f z)
    (h₂ : ∀ z ∈ I, ∀ z' ∈ J, 0 < f z + f z') : 0 < ∑ z ∈ I, f z + ∑ z ∈ J, f z := by
  have hS₂ : 0 < ∑ z ∈ J, f z := sum_pos h₁ hJ
  rcases I.eq_empty_or_nonempty with hI | hI
  · simp [hI, hS₂]
  have hkey : 0 < ∑ z ∈ I, ∑ z' ∈ J, (f z + f z') :=
    sum_pos (fun z hz => sum_pos (fun z' hz' => h₂ z hz z' hz') hJ) hI
  have heq : ∑ z ∈ I, ∑ z' ∈ J, (f z + f z') =
      (J.card : ℝ) * ∑ z ∈ I, f z + (I.card : ℝ) * ∑ z ∈ J, f z := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
  rw [heq] at hkey
  have hm : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hmk : (I.card : ℝ) ≤ J.card := by exact_mod_cast hcard
  by_cases hS₁ : 0 ≤ ∑ z ∈ I, f z
  · linarith
  · push Not at hS₁
    have : (J.card : ℝ) * ∑ z ∈ I, f z ≤ (I.card : ℝ) * ∑ z ∈ I, f z :=
      mul_le_mul_of_nonpos_right hmk hS₁.le
    have hpos : 0 < (I.card : ℝ) * (∑ z ∈ I, f z + ∑ z ∈ J, f z) := by nlinarith
    exact pos_of_mul_pos_right hpos hm.le

section Main

variable {E : Type*} [Fintype E] {A : E → Finset X} {w : E → ℝ} {μ : ℝ} {d D : X → X → ℝ}

/-- Case 1: if `{u, k}` is a side, then `(u, k)` beats `(u, v)` for every other `v`. -/
private lemma nj_lt_of_side_pair (hw : ∀ e, 0 < w e) (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hcompat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ)
    (hX : 4 ≤ Fintype.card X)
    (hμ : ∀ e, 2 ≤ (A e).card → 2 ≤ (univ \ A e).card → μ ≤ w e)
    (hd : ∀ x y, d x y = (1 / 2) * ∑ e, w e * sep (A e) x y)
    (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2)
    {u k v : X} (huk : u ≠ k) (hvu : v ≠ u) (hvk : v ≠ k) {e₀ : E} (he₀ : A e₀ = {u, k}) :
    nj D u k < nj D u v := by
  have hsub := nj_sub_nj_three hDsymm hD0 hvu.symm huk hvk
  suffices h : 0 < ∑ z ∈ ((univ.erase u).erase v).erase k, (D u v + D k z - D u k - D v z) by
    linarith
  have hne : (((univ.erase u).erase v).erase k).Nonempty := by
    rw [← card_pos]
    have h1 := card_erase_three hvu.symm huk hvk
    have h2 : (4 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
    have : (0 : ℝ) < (((univ.erase u).erase v).erase k).card := by linarith
    exact_mod_cast this
  obtain ⟨e₁, he₁⟩ := hcompl e₀
  rw [he₀] at he₁
  have hcard1 : 2 ≤ (univ \ ({u, k} : Finset X)).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair huk]
    omega
  have hμ0 : μ ≤ w e₀ := hμ e₀ (by rw [he₀, card_pair huk]) (by rw [he₀]; exact hcard1)
  have hμ1 : μ ≤ w e₁ := hμ e₁ (by rw [he₁]; exact hcard1)
    (by rw [he₁, Finset.sdiff_sdiff_eq_self (subset_univ _), card_pair huk])
  have h01 : e₀ ≠ e₁ := ne_of_mem (A := A) (z := u) (by rw [he₀]; simp) (by rw [he₁]; simp)
  refine sum_pos (fun z hz => ?_) hne
  simp only [mem_erase, mem_univ, and_true] at hz
  obtain ⟨hzk, hzv, hzu⟩ := hz
  have hc : ∀ e, 0 ≤ w e * (sep (A e) u v + sep (A e) k z - sep (A e) u k - sep (A e) v z) :=
    fun e => mul_nonneg (hw e).le (by
      have h := hcompat e₀ e
      rw [he₀] at h
      exact c4_nonneg h hvu hvk hzu hzk)
  have hsum := le_sum_of_two _ hc h01
  have hc0 : sep (A e₀) u v + sep (A e₀) k z - sep (A e₀) u k - sep (A e₀) v z = 2 := by
    simp [sep, he₀, hvu, hvk, hzu, hzk, huk.symm]
    norm_num
  have hc1 : sep (A e₁) u v + sep (A e₁) k z - sep (A e₁) u k - sep (A e₁) v z = 2 := by
    simp [sep, he₁, hvu, hvk, hzu, hzk, huk.symm]
    norm_num
  rw [hc0, hc1] at hsum
  have hdd : d u v + d k z - d u k - d v z = 1 / 2 * ∑ e, w e *
      (sep (A e) u v + sep (A e) k z - sep (A e) u k - sep (A e) v z) := by
    rw [hd u v, hd k z, hd u k, hd v z]
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  obtain ⟨l1, -⟩ := abs_lt.mp (hDd u v hvu.symm)
  obtain ⟨l2, -⟩ := abs_lt.mp (hDd k z (Ne.symm hzk))
  obtain ⟨-, u3⟩ := abs_lt.mp (hDd u k huk)
  obtain ⟨-, u4⟩ := abs_lt.mp (hDd v z (Ne.symm hzv))
  linarith

/-- Case 2: if the branch `H` of `x` away from `y` has at least two taxa and at most one more
than the branch `P` towards `y`, then a cherry inside `H` beats `(x, y)`. -/
private lemma exists_nj_lt (hw : ∀ e, 0 < w e) (hne : ∀ e, (A e).Nonempty)
    (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hcompat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ)
    (hbin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e)
    (hμ : ∀ e, 2 ≤ (A e).card → 2 ≤ (univ \ A e).card → μ ≤ w e)
    (hd : ∀ x y, d x y = (1 / 2) * ∑ e, w e * sep (A e) x y)
    (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2)
    {x y : X} (hxy : x ≠ y) (hcon : ∀ e, A e ≠ {x, y}) {eH eP : E} (hyP : y ∈ A eP)
    (hxH : x ∉ A eH) (hxP : x ∉ A eP) (hdisj : Disjoint (A eH) (A eP))
    (hcov : ∀ z, z = x ∨ z ∈ A eH ∨ z ∈ A eP) (hH2 : 2 ≤ (A eH).card)
    (hsize : (A eH).card ≤ (A eP).card + 1) :
    ∃ a b, a ≠ b ∧ nj D a b < nj D x y := by
  obtain ⟨eab, a, b, hab, heab, hsub⟩ := exists_pair_side hne hbin eH hH2
  have haH : a ∈ A eH := hsub (by rw [heab]; simp)
  have hbH : b ∈ A eH := hsub (by rw [heab]; simp)
  have haP : a ∉ A eP := disjoint_left.mp hdisj haH
  have hbP : b ∉ A eP := disjoint_left.mp hdisj hbH
  have hyH : y ∉ A eH := fun h => disjoint_left.mp hdisj h hyP
  have hxa : x ≠ a := fun h => hxH (h ▸ haH)
  have hxb : x ≠ b := fun h => hxH (h ▸ hbH)
  have hya : y ≠ a := fun h => haP (h ▸ hyP)
  have hyb : y ≠ b := fun h => hbP (h ▸ hyP)
  refine ⟨a, b, hab, ?_⟩
  rw [← sub_pos, nj_sub_nj_four hDsymm hD0 hxy hxa hxb hya hyb hab]
  have hsplit : (((univ.erase x).erase y).erase a).erase b =
      ((A eH).erase a).erase b ∪ (A eP).erase y := by
    ext z
    simp only [mem_erase, mem_univ, and_true, mem_union]
    constructor
    · rintro ⟨hzb, hza, hzy, hzx⟩
      rcases hcov z with h' | h' | h'
      · exact absurd h' hzx
      · exact Or.inl ⟨hzb, hza, h'⟩
      · exact Or.inr ⟨hzy, h'⟩
    · rintro (⟨hzb, hza, h'⟩ | ⟨hzy, h'⟩)
      · exact ⟨hzb, hza, fun hzy' => hyH (hzy' ▸ h'), fun hzx => hxH (hzx ▸ h')⟩
      · exact ⟨fun hzb => hbP (hzb ▸ h'), fun hza => haP (hza ▸ h'), hzy,
          fun hzx => hxP (hzx ▸ h')⟩
  have hIJ : Disjoint (((A eH).erase a).erase b) ((A eP).erase y) :=
    disjoint_left.mpr fun z hzI hzJ => disjoint_left.mp hdisj
      (mem_of_mem_erase (mem_of_mem_erase hzI)) (mem_of_mem_erase hzJ)
  rw [hsplit, sum_union hIJ]
  -- the branch towards `y` holds another taxon
  have hJ : ((A eP).erase y).Nonempty := by
    by_contra hJ
    rw [not_nonempty_iff_eq_empty] at hJ
    obtain ⟨e', he'⟩ := hcompl eH
    apply hcon e'
    rw [he']
    ext z
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hz
      rcases hcov z with h' | h' | h'
      · exact Or.inl h'
      · exact absurd h' hz
      · by_contra hzy
        push Not at hzy
        have : z ∈ (A eP).erase y := mem_erase.mpr ⟨hzy.2, h'⟩
        rw [hJ] at this
        simp at this
    · rintro (rfl | rfl)
      · exact hxH
      · exact hyH
  have hcardI : (((A eH).erase a).erase b).card + 2 = (A eH).card := by
    have h1 := card_erase_add_one (mem_erase.mpr ⟨hab.symm, hbH⟩)
    have h2 := card_erase_add_one haH
    omega
  have hcardJ : ((A eP).erase y).card + 1 = (A eP).card := card_erase_add_one hyP
  -- the four splits with positive coefficient
  obtain ⟨eab', heab'⟩ := hcompl eab
  rw [heab] at heab'
  obtain ⟨eQ, heQ⟩ := hcompl eP
  have hab2 : 2 ≤ (univ \ ({a, b} : Finset X)).card :=
    one_lt_card.mpr ⟨x, by simp [hxa, hxb], y, by simp [hya, hyb], hxy⟩
  have hμab : μ ≤ w eab := hμ eab (by rw [heab, card_pair hab]) (by rw [heab]; exact hab2)
  have hμab' : μ ≤ w eab' := hμ eab' (by rw [heab']; exact hab2)
    (by rw [heab', Finset.sdiff_sdiff_eq_self (subset_univ _), card_pair hab])
  have hQ2 : 2 ≤ (univ \ A eP).card :=
    one_lt_card.mpr ⟨x, by simp [hxP], a, by simp [haP], hxa⟩
  have hP2 : ∀ z' ∈ (A eP).erase y, 2 ≤ (A eP).card := fun z' hz' =>
    one_lt_card.mpr ⟨y, hyP, z', mem_of_mem_erase hz', (ne_of_mem_erase hz').symm⟩
  have hμP : ∀ z' ∈ (A eP).erase y, μ ≤ w eP := fun z' hz' => hμ eP (hP2 z' hz') hQ2
  have hμQ : ∀ z' ∈ (A eP).erase y, μ ≤ w eQ := fun z' hz' => hμ eQ (by rw [heQ]; exact hQ2)
    (by rw [heQ, Finset.sdiff_sdiff_eq_self (subset_univ _)]; exact hP2 z' hz')
  have haab : a ∈ A eab := by rw [heab]; simp
  have hxab : x ∉ A eab := by rw [heab]; simp [hxa, hxb]
  have hxab' : x ∈ A eab' := by rw [heab']; simp [hxa, hxb]
  have hyab' : y ∈ A eab' := by rw [heab']; simp [hya, hyb]
  have haab' : a ∉ A eab' := by rw [heab']; simp
  have hxQ : x ∈ A eQ := by rw [heQ]; simp [hxP]
  have hyQ : y ∉ A eQ := by rw [heQ]; simp [hyP]
  have n12 : eab ≠ eab' := ne_of_mem haab haab'
  have n13 : eab ≠ eP := ne_of_mem haab haP
  have n14 : eab ≠ eQ := (ne_of_mem hxQ hxab).symm
  have n23 : eab' ≠ eP := ne_of_mem hxab' hxP
  have n24 : eab' ≠ eQ := ne_of_mem hyab' hyQ
  have n34 : eP ≠ eQ := ne_of_mem hyP hyQ
  have hnn : ∀ z, z ∉ A eP → z ≠ a → z ≠ b → ∀ z', z' ∈ A eP → ∀ e,
      0 ≤ w e * (c6 (A e) x y a b z + c6 (A e) x y a b z') := by
    intro z hzP hza hzb z' hz'P e
    have h := hcompat eab e
    rw [heab] at h
    exact mul_nonneg (hw e).le (c6_add_nonneg h (hcompat eP e) haP hbP hxP hyP hzP hz'P hxa
      hxb hza hzb)
  have hdz : ∀ z, d x y + d a z + d b z - d a b - d x z - d y z =
      1 / 2 * ∑ e, w e * c6 (A e) x y a b z := by
    intro z
    rw [hd x y, hd a z, hd b z, hd a b, hd x z, hd y z]
    simp only [c6, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  have hμpos : 0 < μ := by
    have := hDd x y hxy
    linarith [abs_nonneg (D x y - d x y)]
  refine sum_add_sum_pos _ hJ (by omega) (fun z hz => ?_) (fun z hz z' hz' => ?_)
  · -- a taxon on the branch towards `y`
    have hzP := mem_of_mem_erase hz
    have hzy := ne_of_mem_erase hz
    have hza : z ≠ a := fun h => haP (h ▸ hzP)
    have hzb : z ≠ b := fun h => hbP (h ▸ hzP)
    have hzx : z ≠ x := fun h => hxP (h ▸ hzP)
    have hc : ∀ e, 0 ≤ w e * c6 (A e) x y a b z := fun e => by
      have h := hcompat eab e
      rw [heab] at h
      exact mul_nonneg (hw e).le (c6_nonneg h (hcompat eP e) haP hbP hxP hyP hzP hxa hxb)
    have hsum := le_sum_of_four _ hc n12 n13 n14 n23 n24 n34
    have v1 : c6 (A eab) x y a b z = 2 := by
      simp [c6, sep, heab, hxa, hxb, hya, hyb, hza, hzb]
      norm_num
    have v2 : c6 (A eab') x y a b z = 2 := by
      simp [c6, sep, heab', hxa, hxb, hya, hyb, hza, hzb]
      norm_num
    have v3 : c6 (A eP) x y a b z = 2 := by
      simp [c6, sep, hxP, hyP, haP, hbP, hzP]
      norm_num
    have v4 : c6 (A eQ) x y a b z = 2 := by
      simp [c6, sep, heQ, hxP, hyP, haP, hbP, hzP]
      norm_num
    rw [v1, v2, v3, v4] at hsum
    have := hdz z
    have := hμP z hz
    have := hμQ z hz
    obtain ⟨l1, -⟩ := abs_lt.mp (hDd x y hxy)
    obtain ⟨l2, -⟩ := abs_lt.mp (hDd a z (Ne.symm hza))
    obtain ⟨l3, -⟩ := abs_lt.mp (hDd b z (Ne.symm hzb))
    obtain ⟨-, u4⟩ := abs_lt.mp (hDd a b hab)
    obtain ⟨-, u5⟩ := abs_lt.mp (hDd x z (Ne.symm hzx))
    obtain ⟨-, u6⟩ := abs_lt.mp (hDd y z (Ne.symm hzy))
    linarith
  · -- a taxon of `H` paired with a taxon on the branch towards `y`
    have hzH := mem_of_mem_erase (mem_of_mem_erase hz)
    have hzb := ne_of_mem_erase hz
    have hza := ne_of_mem_erase (mem_of_mem_erase hz)
    have hzP : z ∉ A eP := disjoint_left.mp hdisj hzH
    have hzx : z ≠ x := fun h => hxH (h ▸ hzH)
    have hzy : z ≠ y := fun h => hyH (h ▸ hzH)
    have hz'P := mem_of_mem_erase hz'
    have hz'y := ne_of_mem_erase hz'
    have hz'a : z' ≠ a := fun h => haP (h ▸ hz'P)
    have hz'b : z' ≠ b := fun h => hbP (h ▸ hz'P)
    have hz'x : z' ≠ x := fun h => hxP (h ▸ hz'P)
    have hsum := le_sum_of_four _ (hnn z hzP hza hzb z' hz'P) n12 n13 n14 n23 n24 n34
    have v1 : c6 (A eab) x y a b z + c6 (A eab) x y a b z' = 4 := by
      simp [c6, sep, heab, hxa, hxb, hya, hyb, hza, hzb, hz'a, hz'b]
      norm_num
    have v2 : c6 (A eab') x y a b z + c6 (A eab') x y a b z' = 4 := by
      simp [c6, sep, heab', hxa, hxb, hya, hyb, hza, hzb, hz'a, hz'b]
      norm_num
    have v3 : c6 (A eP) x y a b z + c6 (A eP) x y a b z' = 2 := by
      simp [c6, sep, hxP, hyP, haP, hbP, hzP, hz'P]
      norm_num
    have v4 : c6 (A eQ) x y a b z + c6 (A eQ) x y a b z' = 2 := by
      simp [c6, sep, heQ, hxP, hyP, haP, hbP, hzP, hz'P]
      norm_num
    rw [v1, v2, v3, v4] at hsum
    have hsplit2 : ∑ e, w e * (c6 (A e) x y a b z + c6 (A e) x y a b z') =
        ∑ e, w e * c6 (A e) x y a b z + ∑ e, w e * c6 (A e) x y a b z' := by
      rw [← sum_add_distrib]
      simp only [mul_add]
    have := hdz z
    have := hdz z'
    have := hμP z' hz'
    have := hμQ z' hz'
    obtain ⟨l1, -⟩ := abs_lt.mp (hDd x y hxy)
    obtain ⟨l2, -⟩ := abs_lt.mp (hDd a z (Ne.symm hza))
    obtain ⟨l3, -⟩ := abs_lt.mp (hDd b z (Ne.symm hzb))
    obtain ⟨-, u4⟩ := abs_lt.mp (hDd a b hab)
    obtain ⟨-, u5⟩ := abs_lt.mp (hDd x z (Ne.symm hzx))
    obtain ⟨-, u6⟩ := abs_lt.mp (hDd y z (Ne.symm hzy))
    obtain ⟨l2', -⟩ := abs_lt.mp (hDd a z' (Ne.symm hz'a))
    obtain ⟨l3', -⟩ := abs_lt.mp (hDd b z' (Ne.symm hz'b))
    obtain ⟨-, u5'⟩ := abs_lt.mp (hDd x z' (Ne.symm hz'x))
    obtain ⟨-, u6'⟩ := abs_lt.mp (hDd y z' (Ne.symm hz'y))
    linarith

omit [Fintype E] in
/-- If both branches at `x` and at `y` are too large compared with the opposite branch, the
pair `x, y` would be a cherry. -/
private lemma card_le_or_card_le (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hcompat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ)
    {x y : X} (hxy : x ≠ y) (hcon : ∀ e, A e ≠ {x, y}) {eH eP eH' eP' : E}
    (hyP : y ∈ A eP) (hxH : x ∉ A eH) (hxP : x ∉ A eP) (hdisj : Disjoint (A eH) (A eP))
    (hcov : ∀ z, z = x ∨ z ∈ A eH ∨ z ∈ A eP)
    (hxP' : x ∈ A eP') (hyH' : y ∉ A eH') (hyP' : y ∉ A eP')
    (hdisj' : Disjoint (A eH') (A eP')) (hcov' : ∀ z, z = y ∨ z ∈ A eH' ∨ z ∈ A eP') :
    (A eH).card ≤ (A eP).card + 1 ∨ (A eH').card ≤ (A eP').card + 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hn : (A eH).card + (A eP).card + 1 = Fintype.card X := by
    have : insert x (A eH ∪ A eP) = univ := eq_univ_of_forall fun z => by
      rcases hcov z with h | h | h <;> simp [h]
    rw [← card_univ, ← this, card_insert_of_notMem (by simp [hxH, hxP]),
      card_union_of_disjoint hdisj]
  have hn' : (A eH').card + (A eP').card + 1 = Fintype.card X := by
    have : insert y (A eH' ∪ A eP') = univ := eq_univ_of_forall fun z => by
      rcases hcov' z with h | h | h <;> simp [h]
    rw [← card_univ, ← this, card_insert_of_notMem (by simp [hyH', hyP']),
      card_union_of_disjoint hdisj']
  have hinter : (A eH ∩ A eH').Nonempty := by
    rw [← card_pos]
    have := card_union_add_card_inter (A eH) (A eH')
    have := card_le_univ (A eH ∪ A eH')
    omega
  obtain ⟨t, ht⟩ := hinter
  rw [mem_inter] at ht
  have hxH' : x ∉ A eH' := fun h => disjoint_left.mp hdisj' h hxP'
  have hyH : y ∉ A eH := fun h => disjoint_left.mp hdisj h hyP
  have htP : t ∉ A eP := disjoint_left.mp hdisj ht.1
  have htP' : t ∉ A eP' := disjoint_left.mp hdisj' ht.2
  have key : A eH = A eH' := by
    rcases hcompat eH eH' with h | h | h | h
    · exact absurd ht.2 (disjoint_left.mp h ht.1)
    · refine Subset.antisymm h fun s hs => ?_
      rcases hcov s with rfl | h' | h'
      · exact absurd hs hxH'
      · exact h'
      · exact (cpt_list (hcompat eH' eP) [s, t] [y, x] (by simp [hs, ht.2])
          (by simp [hyH', hxH']) ⟨⟨s, by simp, h'⟩, ⟨t, by simp, htP⟩, ⟨y, by simp, hyP⟩,
            ⟨x, by simp, hxP⟩⟩).elim
    · refine Subset.antisymm (fun s hs => ?_) h
      rcases hcov' s with rfl | h' | h'
      · exact absurd hs hyH
      · exact h'
      · exact (cpt_list (hcompat eH eP') [s, t] [x, y] (by simp [hs, ht.1])
          (by simp [hyH, hxH]) ⟨⟨s, by simp, h'⟩, ⟨t, by simp, htP'⟩, ⟨x, by simp, hxP'⟩,
            ⟨y, by simp, hyP'⟩⟩).elim
    · have : x ∈ A eH ∪ A eH' := h ▸ mem_univ x
      rcases mem_union.mp this with h' | h'
      · exact absurd h' hxH
      · exact absurd h' hxH'
  by_cases hs : ∃ s, s ∉ A eH ∧ s ≠ x ∧ s ≠ y
  · obtain ⟨s, hsH, hsx, hsy⟩ := hs
    obtain ⟨eQ, heQ⟩ := hcompl eP
    obtain ⟨eQ', heQ'⟩ := hcompl eP'
    have hsP : s ∈ A eP := by
      rcases hcov s with h | h | h
      · exact absurd h hsx
      · exact absurd h hsH
      · exact h
    have hsP' : s ∈ A eP' := by
      rcases hcov' s with h | h | h
      · exact absurd h hsy
      · exact absurd (key ▸ h) hsH
      · exact h
    exact cpt_list (hcompat eQ eQ') [t, x] [y, s] (by simp [heQ, htP, hxP])
      (by simp [heQ, hyP, hsP]) ⟨⟨t, by simp, by simp [heQ', htP']⟩,
        ⟨x, by simp, by simp [heQ', hxP']⟩, ⟨y, by simp, by simp [heQ', hyP']⟩,
        ⟨s, by simp, by simp [heQ', hsP']⟩⟩
  · push Not at hs
    obtain ⟨e', he'⟩ := hcompl eH
    apply hcon e'
    rw [he']
    ext z
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (hs z hz hzx)
    · rintro (rfl | rfl)
      · exact hxH
      · exact hyH

end Main

/-! ### Split systems -/

/-- **Robust cherry lemma for split systems**: the selection step of Atteson's theorem
(Atteson 1999), with a proof after Mihaescu, Levy & Pachter (2009, Theorem 16).
Let `A e` (`e : E`) be a compatible binary system of splits with positive weights `w`,
containing every trivial split and closed under complement, on at least four taxa, and let
`d x y` be half the total weight of the indices whose side separates `x` and `y`. Let `μ` be
a lower bound on the weight of every internal split (both sides with at least two taxa). If
`D` is symmetric, vanishes on the diagonal, and `|D x y - d x y| < μ / 2` for all distinct
`x, y`, then a pair of distinct taxa minimizing the Q-criterion
`(|X| - 2) D x y - ∑_z D x z - ∑_z D y z` is a side of the split system. -/
theorem exists_eq_pair_of_qCriterion_min_of_abs_sub_lt {E : Type*} [Fintype E]
    (A : E → Finset X) (w : E → ℝ) (hw : ∀ e, 0 < w e) (hne : ∀ e, (A e).Nonempty)
    (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hcompat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ)
    (hbin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e)
    (hsingle : ∀ z, ∃ e, A e = {z}) (hX : 4 ≤ Fintype.card X)
    {μ : ℝ} (hμ : ∀ e, 2 ≤ (A e).card → 2 ≤ (univ \ A e).card → μ ≤ w e)
    {d D : X → X → ℝ}
    (hd : ∀ x y, d x y = (1 / 2) * ∑ e, w e * (if (x ∈ A e ↔ y ∈ A e) then 0 else 1))
    (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2)
    {x y : X} (hxy : x ≠ y)
    (hmin : ∀ x' y', x' ≠ y' →
      ((Fintype.card X : ℝ) - 2) * D x y - ∑ z, D x z - ∑ z, D y z ≤
        ((Fintype.card X : ℝ) - 2) * D x' y' - ∑ z, D x' z - ∑ z, D y' z) :
    ∃ e, A e = {x, y} := by
  have hd' : ∀ x y, d x y = (1 / 2) * ∑ e, w e * sep (A e) x y := hd
  have hmin' : ∀ x' y', x' ≠ y' → nj D x y ≤ nj D x' y' := hmin
  have hsymm : nj D x y = nj D y x := by
    unfold nj
    rw [hDsymm x y]
    ring
  by_contra hcon
  have hcon' : ∀ e, A e ≠ {x, y} := fun e h => hcon ⟨e, h⟩
  have hX3 : 3 ≤ Fintype.card X := by omega
  obtain ⟨eH, eP, hyP, hxH, hxP, hdisj, hcov⟩ := decomp hcompl hbin hsingle hX3 hxy
  obtain ⟨eH', eP', hxP', hyH', hyP', hdisj', hcov'⟩ := decomp hcompl hbin hsingle hX3 hxy.symm
  -- a branch reduced to one taxon `k` makes `{x, k}` (or `{y, k}`) a cherry
  have case1 : ∀ {u v : X} {eH eP : E}, u ≠ v → v ∈ A eP → u ∉ A eH → u ∉ A eP →
      Disjoint (A eH) (A eP) → (∀ z, z = u ∨ z ∈ A eH ∨ z ∈ A eP) → (A eH).card = 1 →
      ∃ k, k ≠ u ∧ nj D u k < nj D u v := by
    intro u v eH eP huv hvP huH huP hdisj hcov h1
    obtain ⟨k, hk⟩ := card_eq_one.mp h1
    have hkH : k ∈ A eH := by rw [hk]; simp
    have hkP : k ∉ A eP := disjoint_left.mp hdisj hkH
    have huk : u ≠ k := fun h => huH (h ▸ hkH)
    have hvk : v ≠ k := fun h => hkP (h ▸ hvP)
    obtain ⟨eQ, heQ⟩ := hcompl eP
    have hQ : A eQ = {u, k} := by
      rw [heQ]
      ext z
      simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro hz
        rcases hcov z with h | h | h
        · exact Or.inl h
        · rw [hk, mem_singleton] at h
          exact Or.inr h
        · exact absurd h hz
      · rintro (rfl | rfl)
        · exact huP
        · exact hkP
    exact ⟨k, huk.symm,
      nj_lt_of_side_pair hw hcompl hcompat hX hμ hd' hDsymm hD0 hDd huk huv.symm hvk hQ⟩
  by_cases hH1 : (A eH).card = 1
  · obtain ⟨k, hk, hlt⟩ := case1 hxy hyP hxH hxP hdisj hcov hH1
    linarith [hmin' x k hk.symm]
  by_cases hH1' : (A eH').card = 1
  · obtain ⟨k, hk, hlt⟩ := case1 hxy.symm hxP' hyH' hyP' hdisj' hcov' hH1'
    linarith [hmin' y k hk.symm]
  have hH2 : 2 ≤ (A eH).card := by have := (hne eH).card_pos; omega
  have hH2' : 2 ≤ (A eH').card := by have := (hne eH').card_pos; omega
  have hcon'' : ∀ e, A e ≠ {y, x} := fun e h => hcon' e (h.trans (pair_comm y x))
  rcases card_le_or_card_le hcompl hcompat hxy hcon' hyP hxH hxP hdisj hcov hxP' hyH' hyP'
      hdisj' hcov' with hs | hs
  · obtain ⟨a, b, hab, hlt⟩ := exists_nj_lt hw hne hcompl hcompat hbin hμ hd' hDsymm hD0 hDd
      hxy hcon' hyP hxH hxP hdisj hcov hH2 hs
    linarith [hmin' a b hab]
  · obtain ⟨a, b, hab, hlt⟩ := exists_nj_lt hw hne hcompl hcompat hbin hμ hd' hDsymm hD0 hDd
      hxy.symm hcon'' hxP' hyH' hyP' hdisj' hcov' hH2' hs
    linarith [hmin' a b hab]


/-! ### Binary phylogenetic trees -/

/-- The sides of the darts of a binary phylogenetic tree form a compatible binary split
system, closed under complement and containing every trivial split. -/
private lemma side_splitSystem {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι) :
    (∀ t : G.Dart, (side G ι t.fst t.snd).Nonempty) ∧
    (∀ t : G.Dart, ∃ t' : G.Dart, side G ι t'.fst t'.snd = univ \ side G ι t.fst t.snd) ∧
    (∀ t t' : G.Dart, Disjoint (side G ι t.fst t.snd) (side G ι t'.fst t'.snd) ∨
      side G ι t.fst t.snd ⊆ side G ι t'.fst t'.snd ∨
      side G ι t'.fst t'.snd ⊆ side G ι t.fst t.snd ∨
      side G ι t.fst t.snd ∪ side G ι t'.fst t'.snd = univ) ∧
    (∀ t : G.Dart, 2 ≤ (side G ι t.fst t.snd).card → ∃ t₁ t₂ : G.Dart,
      Disjoint (side G ι t₁.fst t₁.snd) (side G ι t₂.fst t₂.snd) ∧
        side G ι t₁.fst t₁.snd ∪ side G ι t₂.fst t₂.snd = side G ι t.fst t.snd) ∧
    (∀ z, ∃ t : G.Dart, side G ι t.fst t.snd = {z}) := by
  have hsw : ∀ t : G.Dart, side G ι t.snd t.fst = univ \ side G ι t.fst t.snd := fun t =>
    side_swap hT.1 t.adj
  refine ⟨fun t => side_nonempty hT t.adj, fun t => ⟨t.symm, hsw t⟩, fun t t' => ?_,
    fun t ht => ?_, fun z => ?_⟩
  · rcases side_compat (ι := ι) hT.1 t.adj t'.adj with h | h | h | h
    · rw [hsw t] at h
      right; right; right
      ext z
      by_cases hz : z ∈ side G ι t.fst t.snd
      · simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        left
        exact hz
      · simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        right
        exact h (by simp [hz])
    · rw [hsw t, hsw t'] at h
      right; right; left
      intro z hz
      by_contra hz'
      have := h (by simp [hz'] : z ∈ univ \ side G ι t.fst t.snd)
      simp [hz] at this
    · right; left
      exact h
    · rw [hsw t'] at h
      left
      rw [Finset.disjoint_left]
      intro z hz hz'
      have := h hz
      simp [hz'] at this
  · have ha : t.fst ∉ Set.range ι := by
      rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj)
      rw [← hz, this, Finset.card_singleton] at ht
      omega
    obtain ⟨c, e, hc, he, -, -, -, hdisj, hunion⟩ := side_eq_union hT ha t.adj
    exact ⟨⟨(c, t.fst), hc.symm⟩, ⟨(e, t.fst), he.symm⟩, hdisj, hunion.symm⟩
  · have h1 : G.degree (ι z) = 1 := (hT.2.2.1 (ι z)).mpr ⟨z, rfl⟩
    obtain ⟨b, hb, -⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp h1
    exact ⟨⟨(ι z, b), hb⟩, side_leaf hT hb⟩

/-- **Robust cherry lemma for neighbor joining**: the selection step of Atteson's theorem
(Atteson 1999), with a proof after Mihaescu, Levy & Pachter (2009, Theorem 16). Let `d` be
the path-length metric of a binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths
`w` and at least four taxa, and let `μ` be a lower bound on the lengths of the internal edges
(edges with no taxon at either end). Let `D` be a symmetric dissimilarity with zero diagonal
such that `|D x y - d x y| < μ / 2` for all distinct taxa.
If the distinct taxa `x, y` minimize the Q-criterion of `D` over all pairs of distinct
singleton clusters at the start of neighbor joining, then `ι x` and `ι y` have a common
neighbor: they form a cherry. The bound is sharp: with `≤ μ / 2` a non-cherry can tie
(see the tests). -/
theorem exists_adj_adj_of_qCriterion_min_of_abs_sub_lt {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e) {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ : ℝ} (hμ : ∀ a b, G.Adj a b → a ∉ Set.range ι → b ∉ Set.range ι → μ ≤ w s(a, b))
    {D : X → X → ℝ} (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2) (hX : 4 ≤ Fintype.card X) {x y : X}
    (hxy : x ≠ y)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset X)),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset X)), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist D) {x} {y} ≤
          qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist D) a' b') :
    ∃ u, G.Adj (ι x) u ∧ G.Adj (ι y) u := by
  obtain ⟨hne, hcompl, hcompat, hbin, hsingle⟩ := side_splitSystem hT
  have hμ' : ∀ t : G.Dart, 2 ≤ (side G ι t.fst t.snd).card →
      2 ≤ (univ \ side G ι t.fst t.snd).card → μ ≤ w t.edge := by
    intro t h1 h2
    have ha : t.fst ∉ Set.range ι := by
      rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj)
      rw [← hz, this, Finset.card_singleton] at h1
      omega
    have hb : t.snd ∉ Set.range ι := by
      rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj.symm)
      rw [← side_swap hT.1 t.adj, ← hz, this, Finset.card_singleton] at h2
      omega
    exact hμ t.fst t.snd t.adj ha hb
  obtain ⟨t, ht⟩ := exists_eq_pair_of_qCriterion_min_of_abs_sub_lt
    (fun t : G.Dart => side G ι t.fst t.snd) (fun t => w t.edge) (fun t => hw _ t.edge_mem)
    hne hcompl hcompat hbin hsingle hX hμ' (fun x y => dist_eq_sum_darts hT.1 hd x y) hDsymm
    hD0 hDd hxy (fun x' y' hne' => by
      have := hmin {x'} (by simp) {y'} (by simp) (by simpa using hne')
      rwa [qCriterion_singleton, qCriterion_singleton] at this)
  exact ⟨t.fst, adj_adj_of_side_eq_pair hT t.adj hxy ht⟩

/-- **The first join of neighbor joining on a perturbed tree metric joins a cherry.** Under the
hypotheses of `exists_adj_adj_of_qCriterion_min_of_abs_sub_lt`, any pair of clusters that
neighbor joining run on `D` may join from the initial singletons consists of two taxa with a
common neighbor. -/
theorem NJRun.exists_adj_adj_of_join_init_of_abs_sub_lt {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e) {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ : ℝ} (hμ : ∀ a b, G.Adj a b → a ∉ Set.range ι → b ∉ Set.range ι → μ ≤ w s(a, b))
    {D : X → X → ℝ} (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2)
    {a b : Finset X} (ha : a ∈ univ.image fun x => ({x} : Finset X))
    (hb : b ∈ univ.image fun x => ({x} : Finset X)) (hab : a ≠ b)
    (h4 : 4 ≤ (univ.image fun x => ({x} : Finset X)).card)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset X)),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset X)), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist D) a b ≤
          qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist D) a' b') :
    ∃ x y u, a = {x} ∧ b = {y} ∧ x ≠ y ∧ G.Adj (ι x) u ∧ G.Adj (ι y) u := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
  have hxy : x ≠ y := fun h => hab (by rw [h])
  rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ] at h4
  obtain ⟨u, hu⟩ := exists_adj_adj_of_qCriterion_min_of_abs_sub_lt hT hw hd hμ hDsymm hD0 hDd
    h4 hxy hmin
  exact ⟨x, y, u, rfl, rfl, hxy, hu⟩

end Cslib.Bioinformatics.Phylogenetics.NeighborJoining
