/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A holomorphic self-map of ℙᵏ with a wandering Fatou component (SCV problem list, Problem 70)

Several Complex Variables Problem List, Problem 70: does there exist a holomorphic map `F : ℙᵏ → ℙᵏ`
with a wandering Fatou component `U`, i.e. `Fⁿ(U) ∩ Fᵐ(U) = ∅` for all `n ≠ m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import WantedExt.Dynamics.RepellingPeriodicPointsProjectiveSpaceAMR119Problem0065Wanted

@[expose] public section

namespace MathlibExt.Dynamics.WanderingFatouComponentProjectiveSpaceAMR119Problem0067Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 70. UnsolvedMath record UM-00800271
(`AMR-119-0067`), dataset ulamai/UnsolvedMath v1.8.0.

Maps are holomorphic self-maps of degree `d ≥ 2`, the setting of the list's section on dynamics on
`ℙᵏ` (degree one maps are automorphisms), given by lifts as in the Problem 68 module. The Fatou set
is the largest open set on which the iterates are locally equicontinuous (normal) for the chordal
(Fubini–Study) distance. It is described through lifts as a cone in `ℂᵏ⁺¹ \ {0}`: its connected
components are the cones over the Fatou components, and the image of a cone component under the
`n`-th iterate of the lift is the cone over the image of the Fatou component (every nonzero complex
number is a `dⁿ`-th power), so disjointness is checked on the cones.
-/

open MathlibExt.Dynamics.RepellingPeriodicPointsProjectiveSpaceAMR119Problem0065Wanted

/-- The chordal (Fubini–Study) distance between the points `[u]` and `[v]` of `ℙᵏ`, computed on
nonzero representatives: `√(1 - |⟨u, v⟩|² / (|u|² |v|²))`, the sine of the angle between the
lines `ℂ u` and `ℂ v`. -/
noncomputable def chordal {k : ℕ} (u v : Fin (k + 1) → ℂ) : ℝ :=
  Real.sqrt (1 - ‖∑ i, star (u i) * v i‖ ^ 2 / ((∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2)))

/-- The Fatou set of the self-map of `ℙᵏ` with lift `P`, as a cone in `ℂᵏ⁺¹ \ {0}`: the points
`u ≠ 0` with an open neighbourhood `N ∌ 0` on which the iterates, as maps of `ℙᵏ` measured in the
chordal distance, are equicontinuous at every point (local equicontinuity, i.e. normality). -/
def fatouCone {k : ℕ} (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ) :
    Set (Fin (k + 1) → ℂ) :=
  {u | u ≠ 0 ∧ ∃ N : Set (Fin (k + 1) → ℂ), IsOpen N ∧ u ∈ N ∧ 0 ∉ N ∧
    ∀ w ∈ N, ∀ ε > 0, ∃ δ > 0, ∀ v ∈ N, chordal v w < δ →
      ∀ n : ℕ, chordal ((liftMap P)^[n] v) ((liftMap P)^[n] w) < ε}

/-- SCV Problem List, Problem 70: some holomorphic self-map of some `ℙᵏ` of degree at least two
has a wandering Fatou component `U`, i.e. `Fⁿ(U) ∩ Fᵐ(U) = ∅` for all `n ≠ m` (stated for the cone
over `U`, a connected component of `fatouCone P`). -/
def existsWanderingFatouComponent : Prop :=
  ∃ (k d : ℕ) (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ), 2 ≤ d ∧
    IsHolomorphicSelfMapLift P d ∧ ∃ u ∈ fatouCone P, ∀ n m : ℕ, n ≠ m →
      Disjoint ((liftMap P)^[n] '' connectedComponentIn (fatouCone P) u)
        ((liftMap P)^[m] '' connectedComponentIn (fatouCone P) u)

/--
Resolved true: Astorg, Buff, Dujardin, Peters and Raissy construct polynomial skew products of ℂ²
that extend to holomorphic endomorphisms of ℙ² with a wandering Fatou component. Source: G. Buzzard,
J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables Problem List,
arXiv:math/9509202 (1995), Problem 70; resolution: M. Astorg, X. Buff, R. Dujardin, H. Peters, J.
Raissy, A two-dimensional polynomial mapping with a wandering Fatou component, Ann. of Math. 184
(2016), 263-313, arXiv:1411.1188, Main Theorem (an endomorphism of ℙ²(ℂ) induced by a polynomial
skew-product ℂ² → ℂ² possesses a wandering Fatou component, with bounded orbits), the Fatou set
being defined in §1 as the largest open subset of ℙᵏ(ℂ) where the iterates are locally
equicontinuous; P. Berger, S. Biebler, arXiv:2001.08649, §1.1, record it as answering the question
of Fornæss and Sibony, https://arxiv.org/abs/1411.1188.
-/
public theorem_wanted existsWanderingFatouComponent_holds : existsWanderingFatouComponent

end MathlibExt.Dynamics.WanderingFatouComponentProjectiveSpaceAMR119Problem0067Wanted
