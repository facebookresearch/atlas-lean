/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander
public import Mathlib.Algebra.Order.Chebyshev

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rotation maps, graph squaring and the zig-zag product

O. Reingold, S. Vadhan and A. Wigderson, *Entropy waves, the zig-zag graph product, and new
constant-degree expanders*, Ann. of Math. 155 (2002) 157-187, specify a `D`-regular undirected
multigraph on a vertex set `V` by its *rotation map* `Rot : V × [D] → V × [D]`:
`Rot (v, i) = (w, j)` when the `i`-th edge at `v` leads to `w` and is the `j`-th edge at `w`
(Definition 2.1). A rotation map is an involution. Here the edge labels form any finite type `L`,
so the degree is `|L|`.

This file defines rotation maps, their adjacency matrices, the square (Proposition 2.3 with
`t = 2`) and the zig-zag product (Definition 3.1), and proves:

* `RotationMap.adjMatrix_transpose`: the adjacency matrix of a rotation map is symmetric;
* `RotationMap.adjMatrix_mulVec_one`: every row sums to the degree;
* `RotationMap.isNDLambdaGraph_one`: every rotation map gives an `(N, D, 1)`-graph;
* `RotationMap.adjMatrix_square`: the adjacency matrix of the square is the square of the
  adjacency matrix;
* `RotationMap.IsNDLambdaGraph.square`: squaring an `(N, D, λ)`-graph gives an `(N, D², λ²)`-graph
  (Proposition 2.3 with `t = 2`).

The spectral bounds for the zig-zag product (Theorem 3.2, and the spectral-gap form of Vadhan's
*Pseudorandomness*, Theorem 4.35) are proved in `MathlibExt.Combinatorics.ZigZagProduct`.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.RotationMap

open MathlibExt.Combinatorics.SpectralExpander

/-- **Rotation map of a regular multigraph.** A rotation map on the vertex set `V` with edge labels
`L` is an involution `rot` of `V × L`: `rot (v, i) = (w, j)` means that the edge with label `i` at
`v` leads to `w` and carries label `j` at `w`. It describes an `|L|`-regular undirected multigraph
(loops and parallel edges allowed) (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155
(2002), Definition 2.1). -/
structure _root_.MathlibExt.Combinatorics.RotationMap (V L : Type*) where
  /-- The rotation map `(v, i) ↦ (w, j)`. -/
  rot : V × L → V × L
  /-- Following an edge and then following it back returns to the start. -/
  rot_rot : ∀ p, rot (rot p) = p

variable {V K L : Type*}

/-- **Adjacency matrix of a rotation map.** Its `(v, w)` entry is the number of labels `i` such
that the `i`-th edge at `v` leads to `w`: the number of edges from `v` to `w`, a loop at `v`
counted once for each of its two labels at `v`. -/
noncomputable def adjMatrix [Fintype L] [DecidableEq V] (G : RotationMap V L) : Matrix V V ℝ :=
  fun v w => ((Finset.univ.filter fun i => (G.rot (v, i)).1 = w).card : ℝ)

/-- **Rows of the adjacency matrix sum to the degree.** For a rotation map with label type `L`,
every row of the adjacency matrix sums to `|L|`: `A 1 = |L| 1`. -/
theorem adjMatrix_mulVec_one [Fintype V] [Fintype L] [DecidableEq V] (G : RotationMap V L) :
    G.adjMatrix *ᵥ (1 : V → ℝ) = (Fintype.card L : ℝ) • (1 : V → ℝ) := by
  funext v
  simp only [mulVec, dotProduct, adjMatrix, Pi.one_apply, mul_one, Pi.smul_apply, smul_eq_mul]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (f := fun i => (G.rot (v, i)).1)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp [Finset.card_univ]

/-- **The adjacency matrix of a rotation map is symmetric.** The rotation map itself matches the
labels at `v` of edges to `w` with the labels at `w` of edges to `v`. -/
theorem adjMatrix_transpose [Fintype L] [DecidableEq V] (G : RotationMap V L) :
    G.adjMatrixᵀ = G.adjMatrix := by
  funext w v
  simp only [transpose_apply, adjMatrix]
  congr 1
  refine Finset.card_bij (fun i _ => (G.rot (v, i)).2) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h := G.rot_rot (v, i)
    have e : G.rot (v, i) = (w, (G.rot (v, i)).2) := Prod.ext hi rfl
    rw [e] at h
    rw [h]
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have h1 : G.rot (v, i) = G.rot (v, j) := Prod.ext (hi.trans hj.symm) hij
    have := congrArg G.rot h1
    rw [G.rot_rot, G.rot_rot] at this
    exact (Prod.ext_iff.mp this).2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(G.rot (w, j)).2, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h := G.rot_rot (w, j)
      have e : G.rot (w, j) = (v, (G.rot (w, j)).2) := Prod.ext hj rfl
      rw [e] at h
      rw [h]
    · have h := G.rot_rot (w, j)
      have e : G.rot (w, j) = (v, (G.rot (w, j)).2) := Prod.ext hj rfl
      rw [e] at h
      rw [h]

/-- **Square of a rotation map.** The square `G²` has an edge labelled `(i, j)` from `v` to `u`
for every two-step walk `v → w → u` that leaves `v` along label `i` and `w` along label `j`:
`Rot_{G²}(v, (i, j)) = (u, (j', i'))` where `(w, i') = Rot_G(v, i)` and `(u, j') = Rot_G(w, j)`
(O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Section 2.3, the `t`-th power
with `t = 2`). -/
def square (G : RotationMap V L) : RotationMap V (L × L) where
  rot p :=
    let q := G.rot (p.1, p.2.1)
    let r := G.rot (q.1, p.2.2)
    (r.1, (r.2, q.2))
  rot_rot p := by
    obtain ⟨v, i, j⟩ := p
    simp [G.rot_rot]

/-- **Zig-zag product of rotation maps.** For a rotation map `G` on `V` with labels `K` and a
rotation map `H` on `K` with labels `L`, the zig-zag product `G ⓩ H` is the rotation map on
`V × K` with labels `L × L` given by `Rot((v, k), (i, j)) = ((w, l), (j', i'))`, where
`(k', i') = Rot_H(k, i)`, `(w, l') = Rot_G(v, k')` and `(l, j') = Rot_H(l', j)`: a step in the
small graph `H`, a step in the big graph `G` along the resulting label, and a second step in `H`
(O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 3.1). If `G` is
`|K|`-regular on `N` vertices and `H` is `|L|`-regular on `|K|` vertices, `G ⓩ H` is
`|L|²`-regular on `N |K|` vertices. -/
def zigzag (G : RotationMap V K) (H : RotationMap K L) : RotationMap (V × K) (L × L) where
  rot p :=
    let a := H.rot (p.1.2, p.2.1)
    let b := G.rot (p.1.1, a.1)
    let c := H.rot (b.2, p.2.2)
    ((b.1, c.1), (c.2, a.2))
  rot_rot p := by
    obtain ⟨⟨v, k⟩, i, j⟩ := p
    simp [H.rot_rot, G.rot_rot]

/-- **`(N, D, λ)`-graph given by a rotation map.** The multigraph of the rotation map `G`, which
is `|L|`-regular, is an `(N, |L|, λ)`-graph: `λ ≥ 0` and its normalised adjacency matrix
`A / |L|` satisfies `‖(A / |L|) x‖ ≤ λ ‖x‖` for every `x` orthogonal to the constant vector,
stated without division (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002),
Definition 2.2 and the convention after it). -/
def IsNDLambdaGraph [Fintype V] [Fintype L] [DecidableEq V] (G : RotationMap V L) (lam : ℝ) :
    Prop :=
  0 ≤ lam ∧ IsSpectralBound G.adjMatrix (Fintype.card L * lam)

/-- **Adjacency matrix of the square.** The adjacency matrix of `G²` is the square of the
adjacency matrix of `G`: the number of two-step walks from `v` to `u` is
`∑_w A(v, w) A(w, u)`. -/
theorem adjMatrix_square [Fintype V] [Fintype L] [DecidableEq V] (G : RotationMap V L) :
    G.square.adjMatrix = G.adjMatrix * G.adjMatrix := by
  funext v u
  simp only [adjMatrix, mul_apply]
  simp_rw [← Nat.cast_mul]
  rw [← Nat.cast_sum]
  congr 1
  -- Group the pairs `(i, j)` by the intermediate vertex `w = (G.rot (v, i)).1`.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : L × L => (G.rot (v, p.1)).1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  change (G.rot ((G.rot (v, i)).1, j)).1 = u ∧ (G.rot (v, i)).1 = w ↔
    (G.rot (v, i)).1 = w ∧ (G.rot (w, j)).1 = u
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rw [← h2]; exact h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨by rw [h2]; exact h1, h2⟩

/-- **Squaring squares the spectral parameter.** If the rotation map `G` describes an
`(N, D, λ)`-graph, then its square describes an `(N, D², λ²)`-graph (O. Reingold, S. Vadhan and
A. Wigderson, Ann. of Math. 155 (2002), Proposition 2.3 with `t = 2`). The proof applies the
bound twice, using that `A` maps vectors orthogonal to the constants to such vectors because its
columns also sum to `D`. -/
theorem IsNDLambdaGraph.square [Fintype V] [Fintype L] [DecidableEq V] {G : RotationMap V L}
    {lam : ℝ} (h : G.IsNDLambdaGraph lam) : G.square.IsNDLambdaGraph (lam ^ 2) := by
  obtain ⟨hlam, hb⟩ := h
  refine ⟨by positivity, fun x hx => ?_⟩
  -- `A x` is again orthogonal to the constants.
  have hAx : ∑ i, (G.adjMatrix *ᵥ x) i = 0 := by
    have : ∑ i, (G.adjMatrix *ᵥ x) i = (1 : V → ℝ) ⬝ᵥ (G.adjMatrix *ᵥ x) := by
      simp [dotProduct]
    rw [this, dotProduct_mulVec, ← mulVec_transpose, adjMatrix_transpose, adjMatrix_mulVec_one,
      smul_dotProduct, one_dotProduct, hx, smul_zero]
  have h1 := hb x hx
  have h2 := hb _ hAx
  rw [adjMatrix_square, ← mulVec_mulVec]
  have hcard : (Fintype.card (L × L) : ℝ) = (Fintype.card L : ℝ) ^ 2 := by
    simp [Fintype.card_prod, sq]
  rw [hcard]
  calc _ ≤ ((Fintype.card L : ℝ) * lam) ^ 2 * ((G.adjMatrix *ᵥ x) ⬝ᵥ (G.adjMatrix *ᵥ x)) := h2
    _ ≤ ((Fintype.card L : ℝ) * lam) ^ 2 * (((Fintype.card L : ℝ) * lam) ^ 2 * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = _ := by ring

/-- **The adjacency matrix acts by summing over labels.** `(A x)(v) = ∑_i x(w_i)`, where `w_i` is
the endpoint of the edge with label `i` at `v`. -/
theorem adjMatrix_mulVec_apply [Fintype V] [Fintype L] [DecidableEq V] (G : RotationMap V L)
    (x : V → ℝ) (v : V) : (G.adjMatrix *ᵥ x) v = ∑ i, x (G.rot (v, i)).1 := by
  simp only [mulVec, dotProduct, adjMatrix]
  rw [← Finset.sum_fiberwise' Finset.univ (fun i => (G.rot (v, i)).1) x]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Every rotation map gives an `(N, D, 1)`-graph.** The normalised adjacency matrix of a
regular multigraph has norm at most `1`: `‖A x‖ ≤ |L| ‖x‖` for every `x`, by the Cauchy-Schwarz
inequality and because the rotation map permutes `V × L` (O. Reingold, S. Vadhan and
A. Wigderson, Ann. of Math. 155 (2002), Section 2.2: all eigenvalues of the normalised adjacency
matrix have absolute value at most `1`). -/
theorem isNDLambdaGraph_one [Fintype V] [Fintype L] [DecidableEq V] (G : RotationMap V L) :
    G.IsNDLambdaGraph 1 := by
  refine ⟨zero_le_one, fun x _ => ?_⟩
  have hperm : ∑ p : V × L, x (G.rot p).1 ^ 2 = ∑ p : V × L, x p.1 ^ 2 :=
    Equiv.sum_comp (Function.Involutive.toPerm G.rot G.rot_rot) (fun p => x p.1 ^ 2)
  have hcs : ∀ v, (∑ i, x (G.rot (v, i)).1) ^ 2 ≤ Fintype.card L * ∑ i, x (G.rot (v, i)).1 ^ 2 :=
    fun v => by
      simpa [Finset.card_univ] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => x (G.rot (v, i)).1)
  calc (G.adjMatrix *ᵥ x) ⬝ᵥ (G.adjMatrix *ᵥ x) = ∑ v, (∑ i, x (G.rot (v, i)).1) ^ 2 := by
        simp only [dotProduct, adjMatrix_mulVec_apply, sq]
    _ ≤ ∑ v, Fintype.card L * ∑ i, x (G.rot (v, i)).1 ^ 2 := Finset.sum_le_sum fun v _ => hcs v
    _ = Fintype.card L * ∑ p : V × L, x (G.rot p).1 ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]
    _ = Fintype.card L * ∑ p : V × L, x p.1 ^ 2 := by rw [hperm]
    _ = ((Fintype.card L : ℝ) * 1) ^ 2 * (x ⬝ᵥ x) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct, ← Finset.mul_sum]
        simp only [sq]
        ring

end MathlibExt.Combinatorics.RotationMap
