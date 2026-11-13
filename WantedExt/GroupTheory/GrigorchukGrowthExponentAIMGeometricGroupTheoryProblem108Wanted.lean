/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Grigorchuk group has a volume growth exponent (AimPL Amenability of discrete groups, 3.6)

AimPL, Amenability of discrete groups, Problem 3.6: does the limit `lim_{n → ∞} log log (B_G(n)) /
log n` exist for the Grigorchuk group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.GrigorchukGrowthExponentAIMGeometricGroupTheoryProblem108Wanted

/-!
Source: AimPL: Amenability of discrete groups, Problem 3.6, http://aimpl.org/amenablediscrete/3/.
UnsolvedMath record UM-20001599 (`AIM-GEOMETRIC_GROUP_THEORY-0108`), dataset ulamai/UnsolvedMath
v1.8.0.

The Grigorchuk group is the first Grigorchuk group `G = ⟨a, b, c, d⟩` acting on the binary rooted
tree (finite words over `Bool`), with `a` swapping the two subtrees, `b = (a, c)`, `c = (a, d)`, `d
= (1, b)`. `B_G(n)` is read as the size of the ball of radius `n` of the word metric for `{a, b, c,
d}`, counted as distinct tree maps (the action is faithful). The answer is stated with its value:
the limit exists and equals `log 2 / log r₀`, `r₀` the positive root of `X³ - X² - 2X - 4`.
(OpenConjectures defines `G_ω` as a quotient of `FreeGroup (Fin 4)` for its own Grigorchuk
statements; WantedExt cannot import OpenConjectures, so the group is given here by its action.)
-/

open Filter Topology

/-- The generator `a` of the first Grigorchuk group, acting on the vertices of the binary rooted
tree (finite words over `Bool`): it flips the first letter. -/
def grigA : List Bool → List Bool
  | [] => []
  | x :: w => (!x) :: w

mutual
/-- The generator `b = (a, c)`: it fixes the first letter and acts as `a` after `false` and as `c`
after `true`. -/
def grigB : List Bool → List Bool
  | [] => []
  | false :: w => false :: grigA w
  | true :: w => true :: grigC w

/-- The generator `c = (a, d)`. -/
def grigC : List Bool → List Bool
  | [] => []
  | false :: w => false :: grigA w
  | true :: w => true :: grigD w

/-- The generator `d = (1, b)`. -/
def grigD : List Bool → List Bool
  | [] => []
  | false :: w => false :: w
  | true :: w => true :: grigB w
end

/-- The standard generating set `{a, b, c, d}` of the first Grigorchuk group, all involutions. -/
def grigGen : Fin 4 → List Bool → List Bool
  | 0 => grigA
  | 1 => grigB
  | 2 => grigC
  | 3 => grigD

/-- The ball of radius `n` of the first Grigorchuk group in the word metric of `{a, b, c, d}`: the
tree maps that are composites of at most `n` generators (the action on finite words is faithful,
so distinct maps are distinct group elements). -/
def grigBall (n : ℕ) : Set (List Bool → List Bool) :=
  {f | ∃ w : List (Fin 4), w.length ≤ n ∧ f = (w.map grigGen).foldr (· ∘ ·) id}

/-- AimPL Problem 3.6 (Amenability of discrete groups) with the Erschler-Zheng answer: the limit of
`log log |B(n)| / log n` exists for the first Grigorchuk group and equals `log 2 / log r₀`, where
`r₀` is the positive root of `X³ - X² - 2X - 4`. -/
def grigorchukGrowthExponent : Prop :=
  ∀ r₀ : ℝ, 0 < r₀ → r₀ ^ 3 - r₀ ^ 2 - 2 * r₀ - 4 = 0 →
    Tendsto (fun n : ℕ => Real.log (Real.log ((grigBall n).ncard)) / Real.log n) atTop
      (𝓝 (Real.log 2 / Real.log r₀))

/--
Resolved true, with the value: Erschler and Zheng proved that the volume growth `v_{G,S}(n)` of the
first Grigorchuk group satisfies `lim log log v_{G,S}(n) / log n = α₀ = log 2 / log λ₀ ≈ 0.7674`,
where `λ₀` is the positive root of `X³ - X² - 2X - 4`. Source: AimPL: Amenability of discrete
groups, Problem 3.6, http://aimpl.org/amenablediscrete/3/; resolution: A. Erschler and T. Zheng,
Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020), 1069-1155, arXiv:1802.09077,
abstract and Section 1 (Theorem A, the matching lower bound, with Bartholdi's upper bound): for the
first Grigorchuk group G, lim_{n→∞} log log v_{G,S}(n) / log n = α₀ = log 2 / log λ₀ ≈ 0.7674, λ₀
the positive root of X³ - X² - 2X - 4, https://doi.org/10.1007/s00222-019-00922-0.
-/
public theorem_wanted grigorchukGrowthExponent_holds : grigorchukGrowthExponent

end MathlibExt.GroupTheory.GrigorchukGrowthExponentAIMGeometricGroupTheoryProblem108Wanted
