/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RSW bounds for critical anisotropic bond percolation (Oberwolfach Reports 48/2007)

Oberwolfach Arbeitsgemeinschaft: Percolation (2007), question of J. E. Björnberg: in critical
anisotropic bond percolation on the square lattice (`p_h + p_v = 1`), does an RSW theorem hold: a
positive a priori bound for crossing squares and an extension bound for crossings `H(kn, n)` of `k ×
1` rectangles for every `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MathlibExt.Probability.AnisotropicPercolationBoxCrossingOWR1731Problem004Wanted

/-!
Source: J. E. Björnberg, in Arbeitsgemeinschaft: Percolation, Oberwolfach Reports 4 (2007), no. 48,
pp. 2828-2829, DOI 10.4171/OWR/2007/48. UnsolvedMath record UM-30000859 (`OWR-1731-004`), dataset
ulamai/UnsolvedMath v1.8.0.

A crossing event of the box `[0, a] × [0, b]` depends only on the box's edges, so its probability is
the finite sum of the product weights of the box configurations with a crossing. The answer is
stated as the box-crossing property for rectangles: for every `k ≥ 1`, `P(H(k n, n))` is bounded
below uniformly in `n ≥ 1`; this gives the a priori square bound (`k = 1`) and the extension bound
unconditionally. The follow-up "is there a class of shapes for which both properties hold" is not
formalized.
-/

/-- The edges of the box `[0, a] × [0, b]` of the square lattice: horizontal edges
`(x, y)–(x + 1, y)` indexed by `Fin a × Fin (b + 1)` and vertical edges `(x, y)–(x, y + 1)`
indexed by `Fin (a + 1) × Fin b`. -/
abbrev BoxEdge (a b : ℕ) : Type := (Fin a × Fin (b + 1)) ⊕ (Fin (a + 1) × Fin b)

/-- The graph on the box's vertices `Fin (a + 1) × Fin (b + 1)` formed by the open edges of the
configuration `ω`. -/
def openGraph (a b : ℕ) (ω : BoxEdge a b → Bool) : SimpleGraph (Fin (a + 1) × Fin (b + 1)) :=
  SimpleGraph.fromRel fun u v =>
    (∃ e : Fin a × Fin (b + 1),
      ω (Sum.inl e) = true ∧ u = (e.1.castSucc, e.2) ∧ v = (e.1.succ, e.2)) ∨
    (∃ e : Fin (a + 1) × Fin b,
      ω (Sum.inr e) = true ∧ u = (e.1, e.2.castSucc) ∧ v = (e.1, e.2.succ))

/-- `H(a, b)`: an open path inside the box joins its left side `x = 0` to its right side
`x = a`. -/
def HasHorizontalCrossing (a b : ℕ) (ω : BoxEdge a b → Bool) : Prop :=
  ∃ y y' : Fin (b + 1), (openGraph a b ω).Reachable (0, y) (Fin.last a, y')

/-- The probability of a configuration of the box's edges when every horizontal edge is open with
probability `ph` and every vertical edge with probability `pv`, independently. -/
noncomputable def configurationWeight (ph pv : ℝ) {a b : ℕ} (ω : BoxEdge a b → Bool) : ℝ :=
  ∏ e : BoxEdge a b, match e with
    | Sum.inl h => if ω (Sum.inl h) then ph else 1 - ph
    | Sum.inr v => if ω (Sum.inr v) then pv else 1 - pv

open Classical in
/-- `P(H(a, b))` in anisotropic bond percolation: the event depends only on the box's edges, so its
probability is the total weight of the box configurations with an open horizontal crossing. -/
noncomputable def horizontalCrossingProbability (ph pv : ℝ) (a b : ℕ) : ℝ :=
  ∑ ω : BoxEdge a b → Bool, if HasHorizontalCrossing a b ω then configurationWeight ph pv ω else 0

/-- Björnberg's question (Oberwolfach Arbeitsgemeinschaft Percolation, 2007), answered: in critical
anisotropic bond percolation on `ℤ²` (`p_h + p_v = 1`, `0 < p_h < 1`) the RSW bounds hold for
rectangles: for every `k ≥ 1` the crossing probabilities `P(H(k n, n))` are bounded below by a
positive constant uniformly in `n ≥ 1` (`k = 1` is the a priori bound for squares). -/
def anisotropicBoxCrossing : Prop :=
  ∀ ph : ℝ, 0 < ph → ph < 1 → ∀ k : ℕ, 1 ≤ k → ∃ δ : ℝ, 0 < δ ∧
    ∀ n : ℕ, 1 ≤ n → δ ≤ horizontalCrossingProbability ph (1 - ph) (k * n) n

/--
Resolved true: Grimmett and Manolescu (Theorem 1.3(a)) prove that for `p = (p_h, p_v)` in `(0, 1)²`
with `p_h + p_v = 1` the measure has the box-crossing property: for every aspect ratio `α` some `δ >
0` bounds the probability of crossing an `α N × N` box from below for all large `N`. For small `N`
the crossing probability is positive (the bottom row is open with probability `p_hᵃ`). Source: J. E.
Björnberg, in Arbeitsgemeinschaft: Percolation, Oberwolfach Reports 4 (2007), no. 48, pp. 2828-2829,
DOI 10.4171/OWR/2007/48; resolution: G. R. Grimmett and I. Manolescu, Inhomogeneous bond percolation
on square, triangular and hexagonal lattices, Ann. Probab. 41 (2013), 2990-3025, arXiv:1105.5535,
Theorem 1.3(a): critical inhomogeneous square-lattice percolation (κ = p_h + p_v - 1 = 0) has the
box-crossing property, https://arxiv.org/abs/1105.5535.
-/
public theorem_wanted anisotropicBoxCrossing_holds : anisotropicBoxCrossing

end MathlibExt.Probability.AnisotropicPercolationBoxCrossingOWR1731Problem004Wanted
