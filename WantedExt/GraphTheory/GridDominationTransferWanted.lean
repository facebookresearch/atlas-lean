/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.Combinatorics.SimpleGraph.Domination

/-!
# Transfer matrices for domination polynomials of grids, cylinders and tori

Statements from Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the
Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 2.

A row of width `m` is the path graph `pathGraph m` (grid) or the cycle graph `cycleGraph m`
(cylinder and torus); the `m × n` grid, cylinder and torus are the box products
`pathGraph m □ pathGraph n`, `cycleGraph m □ pathGraph n` and `cycleGraph m □ cycleGraph n`,
with rows indexed by the second coordinate.  Signatures, compatibility and the transfer matrix
are stated for an arbitrary row graph `R`; for `R = pathGraph m` (resp. `R = cycleGraph m`)
they are the paper's (cyclic) signatures, Definitions 3, 5 and 6.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

@[expose] public section

/-- **Domination states.** A domination state is one of three labels: uncovered, covered or
occupied.

Relative to a set $S$ of vertices of a graph, a vertex is occupied if it lies in $S$, covered if
it lies outside $S$ but is adjacent to a vertex of $S$, and uncovered otherwise.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
inductive DominationState
  | uncovered
  | covered
  | occupied
  deriving DecidableEq

open DominationState

/-- The three vertex states form a finite type.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
instance : Fintype DominationState :=
  Fintype.ofList [uncovered, covered, occupied] fun x => by cases x <;> simp

section Defs

variable {V W : Type*}

open scoped Classical in
/-- **Domination polynomial.** For a finite graph $G$, the domination polynomial of $G$ is the
polynomial $\sum_S z^{|S|}$ with integer coefficients, the sum running over the dominating sets
$S$ of $G$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 1. -/
noncomputable def dominationPolynomial [Fintype W] (G : SimpleGraph W) : ℤ[X] :=
  ∑ S ∈ (Finset.univ : Finset (Finset W)).filter (fun S : Finset W => G.IsDominating (↑S : Set W)),
    X ^ S.card

open scoped Classical in
/-- **Domination state of a vertex.** Let $G$ be a simple graph, $S$ a finite set of vertices of
$G$ and $v$ a vertex of $G$. The domination state of $v$ relative to $S$ in $G$ is occupied if
$v \in S$, covered if $v \notin S$ and $v$ is adjacent in $G$ to some vertex of $S$, and
uncovered otherwise.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
noncomputable def vertexDominationState (G : SimpleGraph W) (S : Finset W) (v : W) :
    DominationState :=
  if v ∈ S then occupied else if ∃ u ∈ S, G.Adj u v then covered else uncovered

/-- **Domination signature.** Let $R$ be a simple graph on a vertex set $V$ (the row). A map
$\sigma$ assigning to each vertex of $V$ a domination state (uncovered, covered or occupied) is a
signature for $R$ if no uncovered vertex is adjacent in $R$ to an occupied vertex: for all
vertices $i, j$ adjacent in $R$, it is not the case that $\sigma(i)$ is uncovered and $\sigma(j)$
is occupied.

When $R$ is the path on $m$ vertices, signatures are the strings of length $m$ in which no
uncovered entry is next to an occupied one; when $R$ is the cycle on $m$ vertices the condition
also applies to the first and last entries (the paper's cyclic signatures).

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
def IsDominationSignature (R : SimpleGraph V) (σ : V → DominationState) : Prop :=
  ∀ i j, R.Adj i j → ¬(σ i = uncovered ∧ σ j = occupied)

/-- **Signatures of a row graph.** For a simple graph $R$ on a vertex set $V$ (the row), a
signature of $R$ is a map $\sigma$ assigning to each vertex of $V$ a domination state (uncovered,
covered or occupied) such that $\sigma$ is a domination signature for $R$, that is, no uncovered
vertex is adjacent in $R$ to an occupied vertex. This is the type of all signatures of $R$; when
$R$ is a cycle they are the paper's cyclic signatures.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
def DominationSignature (R : SimpleGraph V) : Type _ :=
  {σ : V → DominationState // IsDominationSignature R σ}

/-- Signatures of a finite row form a finite type.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
noncomputable instance [Fintype V] [DecidableEq V] (R : SimpleGraph V) :
    Fintype (DominationSignature R) := by
  classical
  unfold DominationSignature
  infer_instance

/-- Signatures have decidable equality.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
noncomputable instance [Fintype V] (R : SimpleGraph V) :
    DecidableEq (DominationSignature R) := by
  classical
  unfold DominationSignature
  infer_instance

/-- **All-covered signature.** For a graph $R$ (the row), the all-covered signature
$\sigma_\bullet$ of $R$ is the signature that gives every vertex of $R$ the state covered; it
is a signature because it has no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
def allCoveredSignature (R : SimpleGraph V) : DominationSignature R :=
  ⟨fun _ => covered, fun _ _ _ h => DominationState.noConfusion h.1⟩

/-- **Compatible row signatures.** Let $R$ be a graph (the row) and let $\sigma$ and $\tau$
assign a domination state (uncovered, covered or occupied) to each vertex of $R$. The new row
$\tau$ is compatible with the previous row $\sigma$ when, for every vertex $i$ of $R$: if
$\sigma(i)$ is uncovered then $\tau(i)$ is occupied; if $\sigma(i)$ is occupied then $\tau(i)$
is not uncovered; and if $\tau(i)$ is covered then $\sigma(i)$ is occupied or some neighbour $j$
of $i$ in $R$ has $\tau(j)$ occupied.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 5. -/
def DominationCompatible (R : SimpleGraph V) (τ σ : V → DominationState) : Prop :=
  ∀ i, (σ i = uncovered → τ i = occupied) ∧ (σ i = occupied → τ i ≠ uncovered) ∧
    (τ i = covered → σ i = occupied ∨ ∃ j, R.Adj i j ∧ τ j = occupied)

open scoped Classical in
/-- **Number of occupied vertices.** Let $V$ be a finite set and let $\sigma$ assign a domination
state (uncovered, covered or occupied) to each element of $V$. The occupied count
$\operatorname{occ}(\sigma)$ is the number of elements $i \in V$ such that $\sigma(i)$ is occupied.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 6. -/
noncomputable def occupiedCount [Fintype V] (σ : V → DominationState) : ℕ :=
  ((Finset.univ : Finset V).filter fun i => σ i = occupied).card

open scoped Classical in
/-- **Domination transfer matrix.** Let $R$ be a simple graph on a finite vertex set (the row).
The transfer matrix $A$ of $R$ is the matrix with entries in $\mathbb{Z}[z]$, rows indexed by the
new signature $\tau$ and columns by the old signature $\sigma$, both ranging over the signatures
of $R$, whose entry $A_{\tau\sigma}$ is $z^{\operatorname{occ}(\tau)}$ if $\tau$ is compatible
with $\sigma$ and $0$ otherwise; here $\operatorname{occ}(\tau)$ is the number of occupied
vertices of $\tau$. When $R$ is the cycle on $m$ vertices this is Mertens' matrix $\bar A$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 6. -/
noncomputable def dominationTransferMatrix [Fintype V] (R : SimpleGraph V) :
    Matrix (DominationSignature R) (DominationSignature R) ℤ[X] :=
  fun τ σ => if DominationCompatible R τ.1 σ.1 then X ^ occupiedCount τ.1 else 0

open scoped Classical in
/-- **Almost dominating polynomial.** Let $R$ be a finite graph (the row), $n$ a natural number
and $\sigma$ an assignment of a domination state to each vertex of $R$. Let $H$ be the box
product of $R$ with the path on the vertices $0, \dots, n$, so that the last row of $H$ consists
of the vertices $(i, n)$. Relative to a vertex set $S$ of $H$, a vertex is occupied if it lies in
$S$, covered if it lies outside $S$ but is adjacent to a vertex of $S$, and uncovered otherwise.
The almost dominating polynomial $G^\sigma(z)$ is the polynomial $\sum_S z^{|S|}$ with integer
coefficients, the sum running over the vertex sets $S$ of $H$ such that no vertex of $H$ outside
the last row is uncovered and every vertex $(i, n)$ of the last row has state $\sigma(i)$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 2. -/
noncomputable def almostDominatingPolynomial [Fintype V] (R : SimpleGraph V) (n : ℕ)
    (σ : V → DominationState) : ℤ[X] :=
  ∑ S ∈ (Finset.univ : Finset (Finset (V × Fin (n + 1)))).filter (fun S =>
      (∀ v : V × Fin (n + 1), v.2 ≠ Fin.last n →
        vertexDominationState (R □ pathGraph (n + 1)) S v ≠ uncovered) ∧
      ∀ i, vertexDominationState (R □ pathGraph (n + 1)) S (i, Fin.last n) = σ i),
    X ^ S.card

/-- **A vertex is occupied exactly when it lies in the set.** Let $G$ be a simple graph, $S$ a
finite set of vertices of $G$ and $v$ a vertex of $G$. Then the domination state of $v$ relative
to $S$ in $G$ is occupied if and only if $v \in S$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
theorem vertexDominationState_eq_occupied_iff (G : SimpleGraph W) (S : Finset W) (v : W) :
    vertexDominationState G S v = occupied ↔ v ∈ S := by
  unfold vertexDominationState
  split_ifs <;> simp_all

/-- **Dominating sets have no uncovered vertex.** Let $G$ be a simple graph and $S$ a finite set
of vertices of $G$. Then $S$ dominates $G$ if and only if no vertex of $G$ has domination state
uncovered relative to $S$ in $G$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
theorem isDominating_iff_forall_vertexDominationState_ne_uncovered (G : SimpleGraph W)
    (S : Finset W) :
    G.IsDominating (S : Set W) ↔ ∀ v, vertexDominationState G S v ≠ uncovered := by
  unfold vertexDominationState SimpleGraph.IsDominating
  refine forall_congr' fun v => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- **The domination polynomial at one counts dominating sets.** For every finite graph $G$, the
value at $1$ of the domination polynomial of $G$ equals the number of dominating sets of $G$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 1. -/
theorem dominationPolynomial_eval_one [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidablePred fun S : Finset W => G.IsDominating (S : Set W)] :
    (dominationPolynomial G).eval 1 =
      (((Finset.univ : Finset (Finset W)).filter
        fun S : Finset W => G.IsDominating (↑S : Set W)).card : ℤ) := by
  unfold dominationPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  congr

/-- **The all-covered signature has no occupied vertex.** For every simple graph $R$ on a finite
vertex set, the number of occupied vertices of the all-covered signature of $R$ is $0$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
theorem occupiedCount_allCoveredSignature [Fintype V] (R : SimpleGraph V) :
    occupiedCount (allCoveredSignature R).1 = 0 := by
  simp [occupiedCount, allCoveredSignature]

/-- **Transfer matrix column of the all-covered signature.** Let $R$ be a simple graph on a
finite vertex set (the row), let $A$ be its domination transfer matrix, with entries in
$\mathbb{Z}[z]$, and let $\sigma_\bullet$ be its all-covered signature. For every signature $\tau$
of $R$, the entry $A_{\tau\sigma_\bullet}$ equals $z^{\operatorname{occ}(\tau)}$, where
$\operatorname{occ}(\tau)$ is the number of occupied vertices of $\tau$, if every covered vertex of
$\tau$ is adjacent in $R$ to an occupied vertex of $\tau$, and equals $0$ otherwise.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
theorem dominationTransferMatrix_apply_allCoveredSignature [Fintype V] (R : SimpleGraph V)
    (τ : DominationSignature R)
    [Decidable (∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied)] :
    dominationTransferMatrix R τ (allCoveredSignature R) =
      if ∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied then
        X ^ occupiedCount τ.1 else 0 := by
  unfold dominationTransferMatrix
  have : DominationCompatible R τ.1 (allCoveredSignature R).1 ↔
      ∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied := by
    simp [DominationCompatible, allCoveredSignature]
  simp only [this]

end Defs

open scoped Classical in
/-- **Grid domination polynomial as a sum of almost dominating polynomials.** For all natural
numbers $m$ and $n$, let $P_k$ denote the path on the vertices $0, \dots, k - 1$. Then the
domination polynomial of the grid $P_m \mathbin{\square} P_{n+1}$ equals $\sum_\sigma G^\sigma(z)$,
the sum running over the signatures $\sigma$ of the row graph $P_m$ with no uncovered vertex,
where $G^\sigma(z)$ is the almost dominating polynomial of $P_m$ with $n + 1$ rows and last-row
state $\sigma$.

The grid is taken with at least one row, so that the last row carrying $\sigma$ exists.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Lemma 4
(`jis-2024-24.7.6-lem-4`). -/
public theorem_wanted dominationPolynomial_grid_eq_sum_almostDominatingPolynomial (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph (n + 1)) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        almostDominatingPolynomial (pathGraph m) n σ.1

open scoped Classical in
/-- **Cylinder domination polynomial as a sum of almost dominating polynomials.** For all
natural numbers $m$ and $n$, let $C_m$ be the cycle graph on the vertices $0, \dots, m - 1$, in
which distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod m$, and let $P_{n+1}$ be
the path on the vertices $0, \dots, n$. Then the domination polynomial of the cylinder
$C_m \mathbin{\square} P_{n+1}$ equals $\sum_\sigma G^\sigma(z)$, the sum running over the
signatures $\sigma$ of the row graph $C_m$ with no uncovered vertex, where $G^\sigma(z)$ is the
almost dominating polynomial of $C_m$ with $n + 1$ rows and last-row state $\sigma$.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Lemma 4
(`jis-2024-24.7.6-lem-4`). -/
public theorem_wanted dominationPolynomial_cylinder_eq_sum_almostDominatingPolynomial
    (m n : ℕ) :
    dominationPolynomial (cycleGraph m □ pathGraph (n + 1)) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        almostDominatingPolynomial (cycleGraph m) n σ.1

open scoped Classical in
/-- **Transfer-matrix formula for the domination polynomial of the grid.** For all natural
numbers $m$ and $n$, let $P_k$ denote the path on the vertices $0, \dots, k - 1$, let $A$ be the
domination transfer matrix of the row graph $P_m$, indexed by the signatures of $P_m$, and let
$\sigma_\bullet$ be the all-covered signature. Then the domination polynomial of the grid
$P_m \mathbin{\square} P_n$ is

$$\sum_\sigma (A^n)_{\sigma, \sigma_\bullet},$$

the sum running over the signatures $\sigma$ of $P_m$ with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_grid_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (pathGraph m) ^ n) σ (allCoveredSignature _)

open scoped Classical in
/-- **Transfer-matrix formula for the domination polynomial of the cylinder.** For all natural
numbers $m$ and $n$, let $C_m$ be the cycle graph on the vertices $0, \dots, m - 1$, in which
distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod m$, and let $P_n$ be the path on
the vertices $0, \dots, n - 1$. Let $\bar A$ be the domination transfer matrix of the row graph
$C_m$, indexed by the signatures of $C_m$, and let $\sigma_\bullet$ be the all-covered signature.
Then the domination polynomial of the cylinder $C_m \mathbin{\square} P_n$ is

$$\sum_\sigma (\bar A^n)_{\sigma, \sigma_\bullet},$$

the sum running over the signatures $\sigma$ of $C_m$ with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_cylinder_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (cycleGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (cycleGraph m) ^ n) σ (allCoveredSignature _)

/-- **Transfer-matrix formula for the domination polynomial of the torus.** For all natural
numbers $m$ and $n$ with $n \ge 1$, let $C_k$ denote the cycle graph on the vertices
$0, \dots, k - 1$, in which distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod k$,
and let $\bar A$ be the domination transfer matrix of the row graph $C_m$. Then the domination
polynomial of the torus $C_m \mathbin{\square} C_n$ equals the trace of $\bar A^n$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the trace counts the signatures of $C_m$, while
the torus $C_m \mathbin{\square} C_0$ has no vertices, so its domination polynomial is $1$. For
$n = 1$ and $n = 2$ the cycle $C_n$ is a single vertex and a single edge respectively.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 8
(`jis-2024-24.7.6-thm-8`). -/
public theorem_wanted dominationPolynomial_torus_eq_trace_transferMatrix_pow (m n : ℕ)
    (hn : 1 ≤ n) :
    dominationPolynomial (cycleGraph m □ cycleGraph n) =
      Matrix.trace (dominationTransferMatrix (cycleGraph m) ^ n)

end

end MetaMathlibExt
