/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wandering components of the interior of K⁺ for polynomial diffeomorphisms of ℂ² (Milnor)

Bielefeld (ed.), Conformal Dynamics Problem List (Stony Brook, 1990), §4 Stable regions for complex
Hénon type maps (Milnor), Question 1: for a polynomial diffeomorphism `f` of `ℂ²` with Jacobian `δ`,
a component `U` of the interior of the set `K⁺(f)` of points with bounded forward orbit, and a limit
`g` of a convergent subsequence of iterates on `U`: can `U` be a wandering component (then `|δ| <
1`)? Can the rank of `g` be zero or one? Can `U` be bounded, unbounded of finite volume, or of
infinite volume?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Dynamics.HenonWanderingStableComponentAMR52Problem0079Wanted

/-!
Source: B. Bielefeld (ed.), Conformal Dynamics Problem List (Stony Brook, 1990), arXiv:math/9201271,
§4 Stable regions for complex Hénon type maps (J. Milnor), Question 1,
https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record UM-05300079
(`AMR-052-0079`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂ²` is `Fin 2 → ℂ`. A polynomial diffeomorphism is a polynomial map with a polynomial inverse.
`K⁺(f)` is the set of points with bounded forward orbit; a wandering component is a connected
component of its interior whose forward images are pairwise disjoint (Berger and Biebler: a Fatou
component of a polynomial automorphism of `ℂ²` is either the escaping set or a component of the
interior of `K⁺`). The rank-zero case is stated as the cited property `diam fⁿ(K) → 0` for every
compact `K ⊆ U`, which makes every limit `g` of a convergent subsequence constant on the connected
set `U`. The rank-one case and the questions on boundedness and volume are not settled by the cited
work and are not formalized.
-/

open Filter Topology

/-- `f : ℂ² → ℂ²` is a polynomial map: each coordinate of `f x` is a polynomial in `x 0, x 1`. -/
def IsPolynomialMap (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) : Prop :=
  ∃ F : Fin 2 → MvPolynomial (Fin 2) ℂ, ∀ x i, f x i = MvPolynomial.eval x (F i)

/-- `f` is a polynomial diffeomorphism (polynomial automorphism) of `ℂ²`: a polynomial map with a
polynomial inverse. -/
def IsPolynomialAutomorphism (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) : Prop :=
  IsPolynomialMap f ∧ ∃ g, IsPolynomialMap g ∧ g ∘ f = id ∧ f ∘ g = id

/-- `K⁺(f)`, the set of points with bounded forward orbit. -/
def boundedForwardOrbitSet (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) : Set (Fin 2 → ℂ) :=
  {x | Bornology.IsBounded (Set.range fun n : ℕ => f^[n] x)}

/-- `U` is a connected component of the interior of `K⁺(f)` whose forward images are pairwise
disjoint, i.e. a wandering component. -/
def IsWanderingComponent (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) (U : Set (Fin 2 → ℂ)) : Prop :=
  (∃ x ∈ interior (boundedForwardOrbitSet f),
      U = connectedComponentIn (interior (boundedForwardOrbitSet f)) x) ∧
    ∀ m n : ℕ, m ≠ n → Disjoint (f^[m] '' U) (f^[n] '' U)

/-- Milnor, Question 1, first part: some polynomial diffeomorphism of `ℂ²` has a wandering component
of the interior of `K⁺`. -/
def existsWanderingComponent : Prop :=
  ∃ f U, IsPolynomialAutomorphism f ∧ IsWanderingComponent f U

/-- Milnor, Question 1, rank-zero case: some polynomial diffeomorphism of `ℂ²` has a wandering
component `U` of the interior of `K⁺` on which the iterates shrink every compact set to diameter
`0`, so that every limit `g` of a convergent subsequence of `(f^[n])` on `U` is constant (rank
zero). -/
def existsWanderingComponentRankZero : Prop :=
  ∃ f U, IsPolynomialAutomorphism f ∧ IsWanderingComponent f U ∧
    ∀ K ⊆ U, IsCompact K → Tendsto (fun n => Metric.diam (f^[n] '' K)) atTop (𝓝 0)

/--
Resolved true: Berger and Biebler (Theorem A) construct polynomial automorphisms `(z, w) ↦ (z⁶ +
Σ_{i≤4} p_i z^i - w, b z)` of `ℂ²` with a wandering Fatou component, which is a wandering component
of the interior of `K⁺`. Source: B. Bielefeld (ed.), Conformal Dynamics Problem List (Stony Brook,
1990), arXiv:math/9201271, §4 Stable regions for complex Hénon type maps (J. Milnor), Question 1,
https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: P. Berger and S.
Biebler, Emergence of wandering stable components, J. Amer. Math. Soc. 36 (2023), 397-482;
arXiv:2001.08649, Theorem A: for every sufficiently small real b ≠ 0 there is a nonempty open P_b ⊂
ℝ⁵ such that for a dense set of p ∈ P_b the polynomial automorphism f_p(z, w) = (z⁶ + Σ_{i≤4} p_i
z^i - w, b z) of ℂ² has a wandering Fatou component C, and (2) diam f_p^n(C') → 0 for every compact
C' ⋐ C; §0.1 notes that such a Fatou component is a component of the interior of K⁺ and that Theorem
A answers the existence problem of Bedford and Smillie (1991), https://doi.org/10.1090/jams/1005.
-/
public theorem_wanted existsWanderingComponent_holds : existsWanderingComponent

/--
Resolved true: in Berger and Biebler's examples (Theorem A, property (2)) the iterates shrink every
compact subset of the wandering component to diameter `0`, so every limit map has rank zero. Source:
B. Bielefeld (ed.), Conformal Dynamics Problem List (Stony Brook, 1990), arXiv:math/9201271, §4
Stable regions for complex Hénon type maps (J. Milnor), Question 1,
https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: P. Berger and S.
Biebler, Emergence of wandering stable components, J. Amer. Math. Soc. 36 (2023), 397-482;
arXiv:2001.08649, Theorem A: for every sufficiently small real b ≠ 0 there is a nonempty open P_b ⊂
ℝ⁵ such that for a dense set of p ∈ P_b the polynomial automorphism f_p(z, w) = (z⁶ + Σ_{i≤4} p_i
z^i - w, b z) of ℂ² has a wandering Fatou component C, and (2) diam f_p^n(C') → 0 for every compact
C' ⋐ C; §0.1 notes that such a Fatou component is a component of the interior of K⁺ and that Theorem
A answers the existence problem of Bedford and Smillie (1991), https://doi.org/10.1090/jams/1005.
-/
public theorem_wanted existsWanderingComponentRankZero_holds : existsWanderingComponentRankZero

end MathlibExt.Dynamics.HenonWanderingStableComponentAMR52Problem0079Wanted
