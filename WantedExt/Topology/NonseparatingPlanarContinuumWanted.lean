/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nonseparating planar continuum [OPG-37295]

Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

namespace MathlibExt.Topology.NonseparatingPlanarContinuumWanted

/-!
[OPG-37295] Nonseparating planar continuum.
Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum.

Clause list (every item appears in the formal text below):
- (C1) Domain: `K` is a set in the plane
  (`EuclideanSpace ℝ (Fin 2)`).
- (C2) `K` is compact (`IsCompact`).
- (C3) `K` is path-connected (`IsPathConnected`). Mathlib's
  `IsPathConnected K` asserts a point of `K`, so `K` is nonempty and
  the empty set (which lacks the fixed point property) is excluded.
- (C4) `K` does not separate the plane: its complement is connected
  (`IsConnected Kᶜ`).
- (C5) Claim: every such `K` has the fixed point property, i.e. every
  continuous self-map of `K` has a fixed point.
- Status: posed as a question-Prop; the file asserts no answer.
-/

/-- **Fixed point property.** A subset $K$ of the Euclidean plane $\mathbb{R}^2$ has the fixed
point property when every continuous map $f \colon K \to K$ has a fixed point, that is, a point
$x \in K$ with $f(x) = x$.

Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum. -/
def HasFixedPointProperty (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ f : (↥K → ↥K), Continuous f → ∃ x : ↥K, f x = x

/-- **Nonseparating planar continuum conjecture.** The conjecture asserts that every nonempty,
compact, path-connected subset $K$ of the Euclidean plane $\mathbb{R}^2$ whose complement
$\mathbb{R}^2 \setminus K$ is connected (that is, $K$ does not separate the plane) has the fixed
point property: every continuous map $f \colon K \to K$ has a point $x \in K$ with $f(x) = x$.

Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum. -/
def conjecture : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 2)),
    IsCompact K → IsPathConnected K → IsConnected Kᶜ → HasFixedPointProperty K

/--
**Path-connected nonseparating plane continua have the fixed point property.** Let $K$ be a
nonempty, compact, path-connected subset of the Euclidean plane $\mathbb{R}^2$ whose complement
$\mathbb{R}^2 \setminus K$ is connected. Then $K$ has the fixed point property: every continuous
map $f \colon K \to K$ has a point $x \in K$ with $f(x) = x$.

This answers the nonseparating planar continuum conjecture in the affirmative. Hagopian (A
fixed-point theorem for plane continua, Bull. AMS 77 (1971), 351-354; addendum 1972) proved that
every arcwise connected nonseparating plane continuum has the fixed point property, and compact
path-connected subsets of the plane are arcwise connected.

Source: A. M. Blokh, R. J. Fokkink, J. C. Mayer, L. G. Oversteegen, E. D. Tymchatyn,
Fixed point theorems for plane continua with applications, Mem. Amer. Math. Soc. 224 (2013), no.
1053, arXiv:1004.0214 (citing C. L. Hagopian, Bull. Amer. Math. Soc. 77 (1971), 351-354),
https://arxiv.org/abs/1004.0214. Moved from
`OpenConjectures/Topology/NonseparatingPlanarContinuum`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Topology.NonseparatingPlanarContinuumWanted
