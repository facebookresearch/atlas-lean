/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ZigZagProduct

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Constant-degree expanders from the zig-zag product

O. Reingold, S. Vadhan and A. Wigderson, *Entropy waves, the zig-zag graph product, and new
constant-degree expanders*, Ann. of Math. 155 (2002), Section 1.2: starting from one
`(D⁴, D, 1/5)`-graph `H`, the sequence `G₁ = H²`, `G_{i+1} = G_i² ⓩ H` consists of
`(D^{4i}, D², 2/5)`-graphs (their Theorem 1.4). The zig-zag product needs the edge labels of
`G_i²`, which are pairs of pairs of labels of `H`, to be the vertices of `H`; this file relabels
them through a fixed bijection `(L × L) × (L × L) ≃ K`, which exists exactly when `|K| = |L|⁴`.

* `RotationMap.relabel`: change the labels of a rotation map along a bijection; the adjacency
  matrix, hence the `(N, D, λ)` property, is unchanged;
* `RotationMap.IsNDLambdaGraph.mono`: the `(N, D, λ)` property is monotone in `λ`;
* `RotationMap.zigzagFamily`: the sequence `G_i`, on the vertex types `K`, `K × K`,
  `(K × K) × K`, …;
* `RotationMap.isNDLambdaGraph_zigzagFamily`: every `G_i` is an `(N_i, D², 2/5)`-graph, and
  `card_zigzagFamilyVertex`: `N_i = |K|^i`.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.RotationMap

open MathlibExt.Combinatorics.SpectralExpander

variable {V L L' : Type*}

/-- **Relabelling the edges of a rotation map.** For a bijection `e : L ≃ L'` of label sets, the
rotation map `(v, i') ↦ (w, e j)` where `(w, j) = Rot (v, e⁻¹ i')` describes the same multigraph
with the labels renamed. -/
def relabel (G : RotationMap V L) (e : L ≃ L') : RotationMap V L' where
  rot p := ((G.rot (p.1, e.symm p.2)).1, e (G.rot (p.1, e.symm p.2)).2)
  rot_rot p := by
    obtain ⟨v, i⟩ := p
    simp [G.rot_rot]

/-- **Relabelling preserves the adjacency matrix.** -/
theorem adjMatrix_relabel [Fintype L] [Fintype L'] [DecidableEq V] (G : RotationMap V L)
    (e : L ≃ L') : (G.relabel e).adjMatrix = G.adjMatrix := by
  funext v w
  unfold adjMatrix
  congr 1
  refine Finset.card_bij (fun i _ => e.symm i) (fun i hi => ?_)
    (fun i _ j _ h => e.symm.injective h) (fun j hj => ⟨e j, ?_, by simp⟩)
  · have h := (Finset.mem_filter.1 hi).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
  · have h := (Finset.mem_filter.1 hj).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    change (G.rot (v, e.symm (e j))).1 = w
    simpa using h

/-- **Relabelling preserves the `(N, D, λ)` property.** -/
theorem IsNDLambdaGraph.relabel [Fintype V] [Fintype L] [Fintype L'] [DecidableEq V]
    {G : RotationMap V L} {lam : ℝ} (h : G.IsNDLambdaGraph lam) (e : L ≃ L') :
    (G.relabel e).IsNDLambdaGraph lam := by
  refine ⟨h.1, ?_⟩
  rw [adjMatrix_relabel, ← Fintype.card_congr e]
  exact h.2

/-- **The `(N, D, λ)` property is monotone in `λ`.** -/
theorem IsNDLambdaGraph.mono [Fintype V] [Fintype L] [DecidableEq V] {G : RotationMap V L}
    {lam lam' : ℝ} (h : G.IsNDLambdaGraph lam) (hle : lam ≤ lam') : G.IsNDLambdaGraph lam' := by
  refine ⟨h.1.trans hle, fun x hx => (h.2 x hx).trans ?_⟩
  have hx0 : 0 ≤ x ⬝ᵥ x := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hD : (0 : ℝ) ≤ Fintype.card L := Nat.cast_nonneg _
  have : ((Fintype.card L : ℝ) * lam) ^ 2 ≤ ((Fintype.card L : ℝ) * lam') ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hD h.1) (mul_le_mul_of_nonneg_left hle hD) 2
  exact mul_le_mul_of_nonneg_right this hx0

/-- **Vertex types of the zig-zag family.** The vertex type of the `t`-th graph of the zig-zag
expander family: `K`, `K × K`, `(K × K) × K`, …, with `|K|^(t + 1)` elements
(`card_zigzagFamilyVertex`). -/
def ZigZagFamilyVertex (K : Type*) : ℕ → Type _
  | 0 => K
  | t + 1 => ZigZagFamilyVertex K t × K

/-- The finite-type structure on the vertex types of the zig-zag family. -/
instance ZigZagFamilyVertex.instFintype {K : Type*} [Fintype K] :
    ∀ t, Fintype (ZigZagFamilyVertex K t)
  | 0 => inferInstanceAs (Fintype K)
  | t + 1 => @instFintypeProd _ _ (ZigZagFamilyVertex.instFintype t) _

/-- Decidable equality on the vertex types of the zig-zag family. -/
instance ZigZagFamilyVertex.instDecidableEq {K : Type*} [DecidableEq K] :
    ∀ t, DecidableEq (ZigZagFamilyVertex K t)
  | 0 => inferInstanceAs (DecidableEq K)
  | t + 1 => @instDecidableEqProd _ _ (ZigZagFamilyVertex.instDecidableEq t) _

variable {K : Type*}

/-- **The zig-zag expander family.** For a rotation map `H` on `K` with labels `L` and a bijection
`e : (L × L) × (L × L) ≃ K`, the sequence `G₀ = H²`, `G_{t+1} = (G_t²)ᵉ ⓩ H`, where `(G_t²)ᵉ` is
`G_t²` with its labels renamed by `e` (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155
(2002), Section 1.2, `G₁ = H²` and `G_{i+1} = G_i² ⓩ H`, indexed here from `0`). Every `G_t` has
labels `L × L`, so it is `|L|²`-regular. -/
def zigzagFamily (H : RotationMap K L) (e : (L × L) × (L × L) ≃ K) :
    (t : ℕ) → RotationMap (ZigZagFamilyVertex K t) (L × L)
  | 0 => H.square
  | t + 1 => ((zigzagFamily H e t).square.relabel e).zigzag H

/-- **Size of the zig-zag expander family.** `G_t` has `|K|^(t + 1)` vertices; with `|K| = D⁴`
this is the `N_i = D^{4i}` of Reingold, Vadhan and Wigderson, Theorem 1.4, for `i = t + 1`. -/
theorem card_zigzagFamilyVertex [Fintype K] (t : ℕ) :
    Fintype.card (ZigZagFamilyVertex K t) = Fintype.card K ^ (t + 1) := by
  induction t with
  | zero => simp only [zero_add, pow_one]; rfl
  | succ t ih =>
    change Fintype.card (ZigZagFamilyVertex K t × K) = _
    rw [Fintype.card_prod, ih]
    ring

/-- **The zig-zag expander family consists of expanders.** If `H` is a `(|K|, |L|, 1/5)`-graph,
then every graph `G_t` of the zig-zag family is an `(|K|^(t + 1), |L|², 2/5)`-graph
(O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Theorem 1.4, for a
`(D⁴, D, 1/5)`-graph `H`; the bijection `e` exists exactly when `|K| = |L|⁴`). The induction:
`λ(G_t²) ≤ (2/5)² = 4/25`, and the zig-zag theorem gives `4/25 + 1/5 + 1/25 = 2/5`. -/
theorem isNDLambdaGraph_zigzagFamily [Fintype K] [DecidableEq K] [Fintype L]
    {H : RotationMap K L} (hH : H.IsNDLambdaGraph (1 / 5)) (e : (L × L) × (L × L) ≃ K)
    (t : ℕ) : (zigzagFamily H e t).IsNDLambdaGraph (2 / 5) := by
  induction t with
  | zero =>
    exact hH.square.mono (by norm_num)
  | succ t ih =>
    have h := (ih.square.relabel e).zigzag hH
    exact h.mono (by norm_num)

end MathlibExt.Combinatorics.RotationMap
