/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted

open scoped BigOperators

/-!
# Strongly regular graphs

The definition `SimpleGraph.IsSRGWith` and the complement, parameter-count,
adjacency-matrix equation, and diameter results (`IsSRGWith.compl`,
`IsSRGWith.param_eq`, `IsSRGWith.matrix_eq`, `IsSRGWith.ediam_eq_two`) are in
Mathlib; the connected/`μ = 0`, disconnected-component, and non-principal
eigenvalue results are recorded here.

Sources: no `undergrad.yaml` entry (this topic is absent from the
undergraduate list); A. E. Brouwer and W. H. Haemers, Spectra of Graphs,
Springer 2012, Ch. 9 (strongly regular graphs); C. Godsil and G. Royle,
Algebraic Graph Theory, GTM 207, Ch. 10 (strongly regular graphs).
-/

/-- **Two-edge paths close into triangles when μ = 0.** Let $G$ be a finite strongly regular
graph with parameters $(n, k, \ell, \mu)$ where $\mu = 0$: $G$ has $n$ vertices, every vertex
has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any two
distinct nonadjacent vertices have no common neighbor. If $u$, $v$, $w$ are vertices of $G$
such that $u$ is adjacent to $v$, $v$ is adjacent to $w$, and $u \neq w$, then $u$ is adjacent
to $w$. -/
public theorem _root_.SimpleGraph.IsSRGWith.adj_of_adj_of_adj_of_mu_zero
    {V : Type*} [Fintype V] {n k ℓ : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ 0) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w)
    (huw : u ≠ w) : G.Adj u w := by
  by_contra huw'
  have hcard := h.of_not_adj huw huw'
  have hv : v ∈ G.commonNeighbors u w :=
    (G.mem_commonNeighbors).2 ⟨huv, hvw.symm⟩
  exact (Fintype.card_eq_zero_iff.mp hcard).false ⟨v, hv⟩

private theorem srg_walk_eq_or_adj_mu_zero {V : Type*} [Fintype V] {n k ℓ : ℕ}
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith n k ℓ 0)
    {v w : V} (p : G.Walk v w) : v = w ∨ G.Adj v w := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons u v w huv _ ih =>
      rcases ih with rfl | hvw
      · exact Or.inr huv
      · by_cases huw : u = w
        · exact Or.inl huw
        · exact Or.inr (h.adj_of_adj_of_adj_of_mu_zero huv hvw huw)

private theorem srg_eq_top_of_connected_mu_zero
    {V : Type*} [Fintype V] {n k ℓ : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ 0) (hconn : G.Connected) : G = ⊤ := by
  ext v w
  constructor
  · exact fun hvw => hvw.ne
  · intro hvw
    rcases (hconn.preconnected v w).elim (srg_walk_eq_or_adj_mu_zero h) with rfl | hvw'
    · exact (hvw rfl).elim
    · exact hvw'

private theorem srg_sum_eq_zero_of_eigenvector
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hreg : G.IsRegularOfDegree k) {x : ℂ}
    (hx : x ≠ (k : ℂ)) {v : V → ℂ}
    (hv : (G.adjMatrix ℂ).mulVec v = x • v) : (∑ i, v i) = 0 := by
  classical
  have hleft : Matrix.vecMul (fun _ : V => (1 : ℂ)) (G.adjMatrix ℂ) =
      fun _ => (k : ℂ) := by
    funext i
    simp [hreg i]
  have hdot := Matrix.dotProduct_mulVec (fun _ : V => (1 : ℂ)) (G.adjMatrix ℂ) v
  rw [hv, hleft] at hdot
  have hsum : x * (∑ i, v i) = (k : ℂ) * ∑ i, v i := by
    simpa [dotProduct, Finset.mul_sum] using hdot
  have hprod : (x - (k : ℂ)) * (∑ i, v i) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hsum
  rcases mul_eq_zero.mp hprod with h | h
  · exact (sub_ne_zero.mpr hx h).elim
  · exact h

private theorem srg_of_one_mulVec_eq_zero
    {V : Type*} [Fintype V] {v : V → ℂ} (hv : (∑ i, v i) = 0) :
    (Matrix.of (1 : V → V → ℂ)).mulVec v = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, hv]

private theorem srg_compl_mulVec_eq_neg_add
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x : ℂ} {v : V → ℂ} (hvsum : (∑ i, v i) = 0)
    (hv : (G.adjMatrix ℂ).mulVec v = x • v) :
    (Gᶜ.adjMatrix ℂ).mulVec v = -(v + x • v) := by
  have hmat := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℂ
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℂ] at hmat
  have happ := congrArg (fun M : Matrix V V ℂ => M.mulVec v) hmat
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at happ
  rw [hv, srg_of_one_mulVec_eq_zero hvsum] at happ
  simpa only [zero_add] using eq_neg_of_add_eq_zero_right happ

private theorem srg_eigenvector_quadratic
    {V : Type*} [Fintype V] {n k ℓ μ : ℕ}
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith n k ℓ μ)
    {x : ℂ} (hx : x ≠ (k : ℂ)) {v : V → ℂ} (hv0 : v ≠ 0)
    (hv : (G.adjMatrix ℂ).mulVec v = x • v) :
    x ^ 2 = ((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ)) := by
  classical
  have hvsum := srg_sum_eq_zero_of_eigenvector h.regular hx hv
  have hvcompl := srg_compl_mulVec_eq_neg_add hvsum hv
  have hmat := h.matrix_eq (α := ℂ)
  have happ := congrArg (fun M : Matrix V V ℂ => M.mulVec v) hmat
  simp only [pow_two, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at happ
  rw [hvcompl] at happ
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [Pi.zero_apply] using (Function.ne_iff.mp hv0)
  have happi := congrFun happ i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul] at happi
  apply mul_right_cancel₀ hi
  calc
    x ^ 2 * v i = x * (x * v i) := by ring
    _ = (k : ℂ) * v i + (ℓ : ℂ) * (x * v i) +
        (μ : ℂ) * -(v i + x * v i) := happi
    _ = (((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ))) * v i := by ring

/-- **Non-principal eigenvalues of a strongly regular graph.** Let $G$ be a finite strongly
regular graph with parameters $(n, k, \ell, \mu)$: $G$ has $n$ vertices, every vertex has degree
$k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any two distinct
nonadjacent vertices have exactly $\mu$ common neighbors. Let $A$ be the adjacency matrix of $G$
over $\mathbb{C}$. Then every eigenvalue $x \in \mathbb{C}$ of $A$ with $x \neq k$ satisfies
$x^2 = (\ell - \mu) x + (k - \mu)$. -/
public theorem _root_.SimpleGraph.IsSRGWith.nonprincipal_eigenvalue_quadratic
    {V : Type*} [Fintype V] {n k ℓ μ : ℕ} {G : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableEq V] (h : G.IsSRGWith n k ℓ μ) {x : ℂ}
    (hx : x ≠ (k : ℂ))
    (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
    x ^ 2 = ((ℓ : ℂ) - (μ : ℂ)) * x + ((k : ℂ) - (μ : ℂ)) := by
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hvapp := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at hvapp
  exact srg_eigenvector_quadratic h hx hv.2 hvapp

/--
**Connected strongly regular graphs with μ = 0 are complete.** Let $G$ be a finite strongly
regular graph with parameters $(n, k, \ell, \mu)$ where $\mu = 0$: $G$ has $n$ vertices, every
vertex has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any
two distinct nonadjacent vertices have no common neighbor. If $G$ is connected, then $G$ is
complete, that is, any two distinct vertices of $G$ are adjacent.

Proof: The $\mu = 0$ common-neighbor count makes every nontrivial two-edge walk a
triangle, so walk induction makes each component a clique. Connectedness then
gives completeness. Brouwer and Haemers, Section 9.1.4, state the component
fact: $\mu = 0$ makes the graph a disjoint union of complete graphs.

Proves `Wanted` entry `srg_connected_mu_zero_complete`.

Sources: A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012,
Ch. 9 (disconnected and complete strongly regular graphs); C. Godsil and
G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10.
-/
public theorem srg_connected_mu_zero_complete {V : Type*} [Fintype V]
    {n k ℓ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ 0) (hconn : G.Connected) : G = ⊤ := by
  exact srg_eq_top_of_connected_mu_zero h hconn

/--
**Components of a strongly regular graph with μ = 0 are cliques.** Let $G$ be a finite strongly
regular graph with parameters $(n, k, \ell, \mu)$ where $\mu = 0$: $G$ has $n$ vertices, every
vertex has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any
two distinct nonadjacent vertices have no common neighbor. If $v$ and $w$ are vertices of $G$
joined by a walk, then $v = w$ or $v$ and $w$ are adjacent. Thus each connected component of
$G$ is a clique.

Without $\mu = 0$ this is false: two nonadjacent vertices of the 5-cycle, a strongly regular
graph with parameters $(5, 2, 0, 1)$, are joined by a walk but are neither equal nor adjacent.

Proof: Induct on a witnessing walk and close each two-edge segment using the
zero common-neighbor count. Brouwer and Haemers, Section 9.1.4, state the
result: $\mu = 0$ makes the graph a disjoint union of complete graphs.

Proves `Wanted` entry `srg_reachable_eq_or_adj_mu_zero`.

Sources: A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012,
Ch. 9 (a disconnected strongly regular graph is a disjoint union of complete
graphs); C. Godsil and G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10.
-/
public theorem srg_reachable_eq_or_adj_mu_zero {V : Type*} [Fintype V]
    {n k ℓ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ 0) (v w : V) (hre : G.Reachable v w) :
    v = w ∨ G.Adj v w := by
  exact hre.elim (srg_walk_eq_or_adj_mu_zero h)

/--
**Non-principal eigenvalues of a connected non-complete strongly regular graph.** Let $G$ be a
finite strongly regular graph with parameters $(n, k, \ell, \mu)$: $G$ has $n$ vertices, every
vertex has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any
two distinct nonadjacent vertices have exactly $\mu$ common neighbors. Suppose that $G$ is
connected and not complete, and let $A$ be its adjacency matrix over $\mathbb{C}$. Then every
eigenvalue $x \in \mathbb{C}$ of $A$ with $x \neq k$ satisfies $x^2 = (\ell - \mu) x + (k - \mu)$.

Proof: Apply the identity $A^2 = kI + \ell A + \mu \bar{A}$, where $I$ is the identity matrix
and $\bar{A}$ is the adjacency matrix of the complement of $G$, to an eigenvector $v$ for $x$;
regularity makes the coordinate sum of $v$ zero, so $\bar{A} v = -(1 + x) v$, and this gives
the quadratic. This is the proof of Theorem 9.1.2, (ii) ⇒ (iii), in Brouwer and Haemers,
Section 9.1.3.

Proves `Wanted` entry `srg_nonprincipal_eigenvalue_quadratic`.

Sources: A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012,
Ch. 9, eigenvalues of strongly regular graphs; C. Godsil and G. Royle,
Algebraic Graph Theory, GTM 207, Ch. 10 (eigenvalues of strongly regular
graphs).
-/
public theorem srg_nonprincipal_eigenvalue_quadratic {V : Type*}
    [Fintype V] {n k ℓ μ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] (h : G.IsSRGWith n k ℓ μ) (hconn : G.Connected)
    (hncomp : G ≠ ⊤) (x : ℂ) (hx : x ≠ (k : ℂ))
    (hEig : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℂ)) x) :
    x ^ 2 = (((ℓ : ℂ) - (μ : ℂ)) * x + (((k : ℂ) - (μ : ℂ)))) := by
  exact h.nonprincipal_eigenvalue_quadratic hx hEig

end MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted
