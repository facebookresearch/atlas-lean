/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Topology 667, Topology 668, Topology 737, Topology 739

/-!
# `MathlibExt.AlgebraicTopology.Barcodes.Basic`

## References

* https://en.wikipedia.org/wiki/Persistence_barcode (for `Barcode`, `barcodeRank`)
* https://ti.inf.ethz.ch/ew/courses/TDA24/Chapter6.pdf, See Definition 6.2 (for `bottleneckDist`)
* https://ti.inf.ethz.ch/ew/courses/TDA24/Chapter6.pdf, See Definition 6.10 (for
  `wassersteinDist`)
-/

/-! ### Informal statement of `wassersteinDist`

\begin{definition}[Wasserstein distance]
Let $\mathcal{B}$ and $\mathcal{C}$ be finite multisets of persistence bars.
A persistence bar is a triple $x = (k_x, b_x, d_x)$ with
$k_x \in \mathbb{N}$, $b_x \in \mathbb{R}$,
$d_x \in \mathbb{R} \cup \{\infty\}$, and $b_x < d_x$.

For bars $x, y$, define the interval distance by
\[
d(x,y) =
\begin{cases}
\max\{|b_x - b_y|, |d_x - d_y|\} & \text{if } k_x = k_y, \\
\infty & \text{otherwise},
\end{cases}
\]
with the conventions $|\infty - \infty| = 0$ and
$|\infty - a| = \infty$ for $a \in \mathbb{R}$.

For a bar $x$, define its distance to the diagonal by
\[
d_{\Delta}(x) =
\begin{cases}
\infty & \text{if } d_x = \infty, \\
(d_x - b_x)/2 & \text{otherwise}.
\end{cases}
\]

A partial matching $M$ between $\mathcal{B}$ and $\mathcal{C}$ is a
multiset of pairs $(x,y)$ such that
\begin{enumerate}
\item $\pi_1(M) \leq \mathcal{B}$ and $\pi_2(M) \leq \mathcal{C}$ as multisets,
\item $k_x = k_y$ for every $(x,y) \in M$,
\end{enumerate}
where $\pi_1$ and $\pi_2$ are the projections onto the first and
second coordinates. Bars not in $M$ are treated as matched to the diagonal.

Fix $p$ with $1 \le p < \infty$. For a matching $M$, let
\[
S_p(M) =
\sum_{(x,y) \in M} d(x,y)^p +
\sum_{x \in \mathcal{B} \setminus \pi_1(M)} d_{\Delta}(x)^p +
\sum_{y \in \mathcal{C} \setminus \pi_2(M)} d_{\Delta}(y)^p,
\]
where the sum over an empty multiset is $0$.
The cost of $M$ at $p$ is
\[
\operatorname{cost}_p(M) = S_p(M)^{1/p}.
\]

The Wasserstein distance is the infimum of this cost over all
partial matchings:
\[
W_p(\mathcal{B}, \mathcal{C}) = \inf_{M} \operatorname{cost}_p(M).
\]
\end{definition}
-/

namespace MetaMathlibExt

-- Topology 667: Barcode

structure PersistenceBar where
  degree : ℕ
  birth : ℝ
  death : WithTop ℝ
  positive_length : (birth : WithTop ℝ) < death

/-- A barcode is a multi-set of intervals [birth, death), each with a non-negative integer degree
deg, where birth < death, birth is a real number and death is in ℝ ∪ {+ ∞}
-/
abbrev Barcode := Multiset PersistenceBar

-- Topology 668: Number of Bars at Specific Threshold

/-- Given a barcode D, a degree p, and a threshold value s, the barcode rank R(D,p,s,t) computes the
number of degree-p bars in D whose birth-value is at most s and whose death-value is greater than t
(bar still alive at t).
-/
noncomputable def barcodeRank (D : Barcode) (p : ℕ) (s t : ℝ) : ℕ :=
  (D.filter (fun b => b.degree = p ∧ b.birth ≤ s ∧ (t : WithTop ℝ) < b.death)).card

-- Topology 737: Bottleneck Distance between Barcodes

noncomputable instance : DecidableEq PersistenceBar :=
  Classical.decEq _

/-- Distance between endpoints. `none` is `⊤` in `WithTop ℝ`. This is used below to define distance between the death values of two bars, recalling that death values (but not birth values) can be positive infinity -/

noncomputable def withTopDist (x y : WithTop ℝ) : ENNReal :=
  match x, y with
  | none, none => (0 : ENNReal)
  | some a, some b => ENNReal.ofReal |a - b|
  | _, _ => ⊤

/-- Distance to the diagonal, i.e. half the length. -/

noncomputable def PersistenceBar.distToDiagonal (b : PersistenceBar) : ENNReal :=
  match b.death with
  | none => ⊤
  | some d => ENNReal.ofReal ((d - b.birth) / 2)

/-- `L∞` distance between two bars, `⊤` when degrees differ. -/

noncomputable def PersistenceBar.dist (b₁ b₂ : PersistenceBar) : ENNReal :=
  if b₁.degree = b₂.degree then
    ENNReal.ofReal |b₁.birth - b₂.birth| ⊔ withTopDist b₁.death b₂.death
  else ⊤

/-- A partial matching. The two `≤` conditions already control
    multiplicities, so no `Nodup` is needed. -/

structure Matching (B C : Barcode) where
  pairs : Multiset (PersistenceBar × PersistenceBar)
  fst_le : pairs.map Prod.fst ≤ B
  snd_le : pairs.map Prod.snd ≤ C
  degree_eq : ∀ p ∈ pairs, p.1.degree = p.2.degree

/-- Empty matching: use `∅`, not `0`, for the empty multiset. This shows that the set of Matchings is not empty, justifying the later use of sInf -/

def Matching.empty (B C : Barcode) : Matching B C where
  pairs := ∅
  fst_le := by simp
  snd_le := by simp
  degree_eq := by simp

/-- Cost of a matching: max of matched cost and unmatched diagonal cost. -/

noncomputable def Matching.cost {B C : Barcode} (M : Matching B C) : ENNReal :=
  (M.pairs.map (fun p => p.1.dist p.2)).sup ⊔
  ((B - M.pairs.map Prod.fst).map PersistenceBar.distToDiagonal).sup ⊔
  ((C - M.pairs.map Prod.snd).map PersistenceBar.distToDiagonal).sup

/-- Bottleneck distance as an `sInf` over costs, instead of `⨅` over
    the `Matching` type. -/

noncomputable def bottleneckDist (B C : Barcode) : ENNReal :=
  sInf { δ : ENNReal | ∃ M : Matching B C, M.cost ≤ δ }

-- Topology 739: Wasserstein Distance between Barcodes

 /-The definition of the pth Wassterstein cost. Although one only gets a metric for 1 ≤ p, the defintion lets p be any real number.-/

noncomputable def Matching.wassersteinCost (p : ℝ) {B C : Barcode} (M : Matching B C) : ENNReal :=
  (((M.pairs.map (fun pr => (pr.1.dist pr.2) ^ p)).sum +
    (((B - M.pairs.map Prod.fst).map PersistenceBar.distToDiagonal).map (fun x => x ^ p)).sum +
    (((C - M.pairs.map Prod.snd).map PersistenceBar.distToDiagonal).map (fun x => x ^ p)).sum)) ^ (1 / p)

/-! ### Informal statement of `wassersteinDist`

\begin{definition}[Wasserstein distance]
Let $\mathcal{B}$ and $\mathcal{C}$ be finite multisets of persistence bars.
A persistence bar is a triple $x = (k_x, b_x, d_x)$ with
$k_x \in \mathbb{N}$, $b_x \in \mathbb{R}$,
$d_x \in \mathbb{R} \cup \{\infty\}$, and $b_x < d_x$.

For bars $x, y$, define the interval distance by
\[
d(x,y) =
\begin{cases}
\max\{|b_x - b_y|, |d_x - d_y|\} & \text{if } k_x = k_y, \\
\infty & \text{otherwise},
\end{cases}
\]
with the conventions $|\infty - \infty| = 0$ and
$|\infty - a| = \infty$ for $a \in \mathbb{R}$.

For a bar $x$, define its distance to the diagonal by
\[
d_{\Delta}(x) =
\begin{cases}
\infty & \text{if } d_x = \infty, \\
(d_x - b_x)/2 & \text{otherwise}.
\end{cases}
\]

A partial matching $M$ between $\mathcal{B}$ and $\mathcal{C}$ is a
multiset of pairs $(x,y)$ such that
\begin{enumerate}
\item $\pi_1(M) \leq \mathcal{B}$ and $\pi_2(M) \leq \mathcal{C}$ as multisets,
\item $k_x = k_y$ for every $(x,y) \in M$,
\end{enumerate}
where $\pi_1$ and $\pi_2$ are the projections onto the first and
second coordinates. Bars not in $M$ are treated as matched to the diagonal.

Fix $p$ with $1 \le p < \infty$. For a matching $M$, let
\[
S_p(M) =
\sum_{(x,y) \in M} d(x,y)^p +
\sum_{x \in \mathcal{B} \setminus \pi_1(M)} d_{\Delta}(x)^p +
\sum_{y \in \mathcal{C} \setminus \pi_2(M)} d_{\Delta}(y)^p,
\]
where the sum over an empty multiset is $0$.
The cost of $M$ at $p$ is
\[
\operatorname{cost}_p(M) = S_p(M)^{1/p}.
\]

The Wasserstein distance is the infimum of this cost over all
partial matchings:
\[
W_p(\mathcal{B}, \mathcal{C}) = \inf_{M} \operatorname{cost}_p(M).
\]
\end{definition}
-/

/-- \begin{definition}[Wasserstein distance] Let $\mathcal{B}$ and $\mathcal{C}$ be finite multisets
of persistence bars. A persistence bar is a triple $x = (k_x, b_x, d_x)$ with $k_x \in \mathbb{N}$,
$b_x \in \mathbb{R}$, $d_x \in \mathbb{R} \cup \{\infty\}$, and $b_x < d_x$.

The full informal statement is in the module documentation directly above.
-/
noncomputable def wassersteinDist (p : ℝ) (B C : Barcode) : ENNReal :=
  sInf { δ : ENNReal | ∃ M : Matching B C, M.wassersteinCost p ≤ δ }

end MetaMathlibExt

end
