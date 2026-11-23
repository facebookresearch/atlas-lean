/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetricsWanted

/-!
# Asymptotically equivalent cocompact metrics (OWR-1319-022)

Clause list from the source:
(a) `Γ` is a group (domain of the acting group).
(b) `(M, d₁)` is a complete length space (metric axioms via `MetricSpace`,
    completeness via `CompleteSpace`, length via approximate midpoints).
(c) `(M, d₂)` is a complete length space on the same underlying type `M`
    (explicit metric axioms, explicit Cauchy completeness, approximate midpoints).
(d) `Γ` acts on `M` (a `MulAction`).
(e) the action is by isometries for `d₁` and for `d₂`.
(f) the action is cocompact (some compact set meets every `Γ`-orbit).
(g) asymptotic equivalence: `d₁ x y / d₂ x y → 1` as `d₁ x y → ∞`.
(h) question: whether `|d₁ - d₂|` is uniformly bounded over all pairs.
-/

/--
**Cocompact asymptotically equivalent length-space pair.** Let $\Gamma$ be a group acting on a
complete metric space $(M, d_1)$. A cocompact asymptotically equivalent length-space pair on $M$
is a function $d_2 \colon M \times M \to \mathbb{R}$ with the following properties. It is a
metric: $d_2(x, y) \ge 0$, $d_2(x, y) = 0$ if and only if $x = y$, $d_2(x, y) = d_2(y, x)$ and
$d_2(x, z) \le d_2(x, y) + d_2(y, z)$. It is complete: every sequence that is Cauchy for $d_2$
converges for $d_2$ to some point of $M$. Both $d_1$ and $d_2$ have approximate midpoints: for
$i = 1, 2$, all $x, y \in M$ and every $\varepsilon > 0$ there is $z \in M$ with
$\max(d_i(x, z), d_i(z, y)) \le d_i(x, y)/2 + \varepsilon$. The action is by isometries of both:
$d_i(g x, g y) = d_i(x, y)$ for all $g \in \Gamma$, $x, y \in M$ and $i = 1, 2$. The action is
cocompact: some compact set $K \subseteq M$ (compact for $d_1$) contains a point $g x$ of the orbit
of every $x \in M$. The two metrics induce the same topology: for every $x \in M$ and every
$\varepsilon > 0$ there is $\delta > 0$ with $d_2(x, y) < \varepsilon$ whenever
$d_1(x, y) < \delta$, and there is $\delta > 0$ with $d_1(x, y) < \varepsilon$ whenever
$d_2(x, y) < \delta$. Finally, $d_1$ and $d_2$ are asymptotically equivalent: for every
$\varepsilon > 0$ there is a real number $R$ such that
$|d_1(x, y) / d_2(x, y) - 1| < \varepsilon$ for all $x, y \in M$ with $d_1(x, y) \ge R$.

For complete metric spaces the approximate-midpoint property is equivalent to being a length
space.
-/
structure OWR1319022Data (Γ : Type*) (M : Type*) [Group Γ] [MetricSpace M]
    [CompleteSpace M] [MulAction Γ M] where
  d2 : M → M → ℝ
  d2_nonneg : ∀ x y : M, 0 ≤ d2 x y
  d2_eq_zero : ∀ x y : M, d2 x y = 0 ↔ x = y
  d2_symm : ∀ x y : M, d2 x y = d2 y x
  d2_triangle : ∀ x y z : M, d2 x z ≤ d2 x y + d2 y z
  d2_complete : ∀ u : ℕ → M,
    (∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → d2 (u n) (u m) < ε) →
    ∃ x : M, ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d2 (u n) x < ε
  length1 : ∀ (x y : M) (ε : ℝ), 0 < ε →
    ∃ z : M, max (dist x z) (dist z y) ≤ dist x y / 2 + ε
  length2 : ∀ (x y : M) (ε : ℝ), 0 < ε →
    ∃ z : M, max (d2 x z) (d2 z y) ≤ d2 x y / 2 + ε
  act_isom1 : ∀ g : Γ, ∀ x y : M, dist (g • x) (g • y) = dist x y
  act_isom2 : ∀ g : Γ, ∀ x y : M, d2 (g • x) (g • y) = d2 x y
  cocompact : ∃ K : Set M, IsCompact K ∧ ∀ x : M, ∃ g : Γ, g • x ∈ K
  /-- The second metric induces the ambient topology: `d2`-balls and
  `dist`-balls are locally cofinal at every point. Without this, a metric
  transported along a bijection to an unbounded space would make the
  asymptotic premise vacuous on a compact space while the conclusion
  fails. -/
  sameTopology : ∀ x : M, ∀ ε > 0,
    (∃ δ > 0, ∀ y : M, dist x y < δ → d2 x y < ε) ∧
      (∃ δ > 0, ∀ y : M, d2 x y < δ → dist x y < ε)
  asymptotic : ∀ (ε : ℝ), 0 < ε →
    ∃ R : ℝ, ∀ x y : M, R ≤ dist x y → |dist x y / d2 x y - 1| < ε

/--
**Bounded-difference conjecture for cocompact asymptotically equivalent metrics.** The statement
that for every group $\Gamma$, every complete metric space $(M, d_1)$ on which $\Gamma$ acts, and
every cocompact asymptotically equivalent length-space pair on $M$ with second metric $d_2$, there
is a real number $C$ such that $|d_1(x, y) - d_2(x, y)| \le C$ for all $x, y \in M$.

Source: open question of [OWR-1319-022] (Geometric Group Theory, Hyperbolic Dynamics and
Symplectic Geometry (2007), Oberwolfach Reports, DOI 10.4171/owr/2006/33, pp. 1991--2058).
-/
def conjecture : Prop :=
  ∀ (Γ : Type*) (M : Type*) [Group Γ] [MetricSpace M] [CompleteSpace M]
    [MulAction Γ M] (D : OWR1319022Data Γ M),
    ∃ C : ℝ, ∀ x y : M, |dist x y - D.d2 x y| ≤ C
/--
**Negative answer to the cocompact asymptotic-metrics question.** The conjecture is false: there
exist a group $\Gamma$, a complete metric space $(M, d_1)$ on which $\Gamma$ acts, and a cocompact
asymptotically equivalent length-space pair on $M$ with second metric $d_2$, such that for every
real number $C$ there are points $x, y \in M$ with $|d_1(x, y) - d_2(x, y)| > C$.

Counterexample of Le Donne, Nalon, Nicolussi Golo and Ryoo (arXiv:2503.00560, 2025), Example 4.2:
on the Engel group, a left-invariant Riemannian metric and its canonical asymptotic
sub-Riemannian metric are complete, left-invariant (transitive, hence cocompact), asymptotic,
yet their difference is unbounded.

Source: E. Le Donne, L. Nalon, S. Nicolussi Golo, S.-Y.
Ryoo, Asymptotics of Riemannian Lie groups with nilpotency step 2, arXiv preprint (2025),
arXiv:2503.00560, https://arxiv.org/abs/2503.00560. Moved from
`OpenConjectures/Geometry/CocompactAsymptoticallyEquivalentMetrics`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetricsWanted
