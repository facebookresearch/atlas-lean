/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sticky Cantor sets (Open Problem Garden 37293)

Open Problem Garden, Sticky Cantor sets: an embedded Cantor set in `ℝ^n` is sticky if it cannot be
moved off itself by arbitrarily small motions of `ℝ^n`. For what dimensions `n` do sticky Cantor
sets exist?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Topology.StickyCantorSetOpenGardenProblem37293Wanted

/-!
Source: Open Problem Garden, Sticky Cantor sets (node 37293; posted by porton),
http://www.openproblemgarden.org/op/sticky_cantor_sets. UnsolvedMath record UM-00003422
(`OPG-37293`), dataset ulamai/UnsolvedMath v1.8.0.

A Cantor set is a subset homeomorphic to the Cantor space `ℕ → Bool`. Stickiness follows the
resolving paper: Krushkal calls a set sticky if it cannot be isotoped off itself by any sufficiently
small ambient isotopy, where an ambient isotopy is a continuous family `H t` of homeomorphisms of
`ℝ^d` with `H 0 = id`, and small means that every point moves less than `ε` at every time. The page,
like Daverman's Problem E8 (which Krushkal's introduction cites for the question, next to Wright's
Conjecture 1), speaks of a single small homeomorphism instead; a set that no small homeomorphism
moves off itself is in particular sticky in Krushkal's sense, so the target is Krushkal's statement
and not the homeomorphism version. Only the existence of sticky Cantor sets in every dimension
`d ≥ 4` is formalized; the low dimensions `d ≤ 3` of the question are not.
-/

/-- A subset `C` of `ℝ^d` is sticky (Krushkal): for some `ε > 0`, no ambient isotopy of `ℝ^d` that
starts at the identity and moves every point by less than `ε` at every time carries `C` off
itself. -/
def IsSticky {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ ε > (0 : ℝ), ∀ H : unitInterval → (EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d)),
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × unitInterval => H p.2 p.1) →
      H 0 = Homeomorph.refl _ → (∀ t x, dist (H t x) x < ε) → (H 1 '' C ∩ C).Nonempty

/-- Sticky Cantor sets exist in `ℝ^d` for every `d ≥ 4`: a subset homeomorphic to the Cantor space
`ℕ → Bool` that is sticky. -/
def existsStickyCantorSet : Prop :=
  ∀ d : ℕ, 4 ≤ d → ∃ C : Set (EuclideanSpace ℝ (Fin d)), Nonempty (C ≃ₜ (ℕ → Bool)) ∧ IsSticky C

/--
Resolved true: Krushkal (Theorem 1) constructs, for every `d ≥ 4`, a wild Cantor set in `ℝ^d` that
cannot be isotoped off itself by any sufficiently small ambient isotopy. Source: Open Problem
Garden, Sticky Cantor sets (node 37293; posted by porton),
http://www.openproblemgarden.org/op/sticky_cantor_sets; resolution: V. Krushkal, Sticky Cantor sets
in ℝ^d, J. Topol. Anal. 10 (2018), 477-482; arXiv:1602.01035, Theorem 1: for any d ≥ 4 there exists
a sticky Cantor set in ℝ^d, where a subset of ℝ^d is sticky if it cannot be isotoped off itself by
any sufficiently small ambient isotopy (Introduction, which cites the question as D. G. Wright,
Pushing a Cantor set off itself, Houston J. Math. 2 (1976), Conjecture 1, and R. J. Daverman,
Problems about finite-dimensional manifolds, Open problems in topology (1990), Problem E8),
https://arxiv.org/abs/1602.01035.
-/
public theorem_wanted existsStickyCantorSet_holds : existsStickyCantorSet

end MathlibExt.Topology.StickyCantorSetOpenGardenProblem37293Wanted
