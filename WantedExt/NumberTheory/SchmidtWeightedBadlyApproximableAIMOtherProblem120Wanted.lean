/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schmidt's conjecture on weighted badly approximable pairs (AIM measure rigidity, Conjecture 32)

AIM workshop Emerging applications of measure rigidity, open problems, Conjecture 32 (W. Schmidt):
with `C_s = {(α, β) ∈ ℝ² | inf_{q ≥ 1} max {q^s ⟨qα⟩, q^{1-s} ⟨qβ⟩} > 0}` for `0 ≤ s ≤ 1` (`⟨x⟩` the
distance to the nearest integer), `C_s ∩ C_t ≠ ∅` for any `s, t ∈ [0, 1]`. Schmidt stated it for `s
= 1/3`, `t = 2/3`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.DiophantineApproximation.DistToNearestInt

@[expose] public section

namespace MathlibExt.NumberTheory.SchmidtWeightedBadlyApproximableAIMOtherProblem120Wanted

/-!
Source: AIM workshop Emerging applications of measure rigidity (June 2004), open problems,
Conjecture 32 (W. M. Schmidt), https://aimath.org/WWN/measrigid/measrigid.pdf. UnsolvedMath record
UM-20003313 (`AIM-OTHER-0120`), dataset ulamai/UnsolvedMath v1.8.0.

The sets are Badziahin, Pollington and Velani's `Bad(i, j)`, `0 ≤ i, j ≤ 1`, `i + j = 1`: points
`(x, y)` with `max {‖qx‖^{1/i}, ‖qy‖^{1/j}} > c / q` for some `c > 0` and every integer `q ≥ 1`,
with their convention `t^{1/0} = 0`, so `Bad(0, 1) = ℝ × Bad`. For `0 < s < 1` the list's `C_s` is
`Bad(s, 1 - s)` (raise the two terms to the powers `1/s` and `1/(1 - s)`); at `s = 0` the list's
literal `C_0` contains `Bad(0, 1)`, so the statement implies the list's form. `‖x‖` is
`MetaMathlibExt.distToNearestInt`.
-/

open MetaMathlibExt (distToNearestInt)

/-- `t ^ (1 / i)`, with the convention `t ^ (1 / 0) = 0` of Badziahin, Pollington and Velani. -/
noncomputable def weightedRoot (i t : ℝ) : ℝ :=
  if i = 0 then 0 else t ^ (1 / i)

/-- `(x, y) ∈ Bad(i, j)`: some `c > 0` has `max {‖q x‖^{1/i}, ‖q y‖^{1/j}} > c / q` for every
integer `q ≥ 1`, where `‖·‖` is the distance to the nearest integer and `t^{1/0} = 0`. -/
def IsWeightedBadlyApproximable (i j : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ c > 0, ∀ q : ℕ, 1 ≤ q →
    c / q < max (weightedRoot i (distToNearestInt (q * p.1)))
      (weightedRoot j (distToNearestInt (q * p.2)))

/-- Schmidt's conjecture (AIM Emerging applications of measure rigidity, Conjecture 32) as a claim:
for any two weight pairs `(i₁, j₁)`, `(i₂, j₂)` with `0 ≤ i, j` and `i + j = 1`, the sets
`Bad(i₁, j₁)` and `Bad(i₂, j₂)` intersect. -/
def schmidtWeightedBadIntersect : Prop :=
  ∀ i₁ j₁ i₂ j₂ : ℝ, 0 ≤ i₁ → 0 ≤ j₁ → i₁ + j₁ = 1 → 0 ≤ i₂ → 0 ≤ j₂ → i₂ + j₂ = 1 →
    ∃ p : ℝ × ℝ, IsWeightedBadlyApproximable i₁ j₁ p ∧ IsWeightedBadlyApproximable i₂ j₂ p

/--
Resolved true: Badziahin, Pollington and Velani proved that any finite intersection of the sets
`Bad(i, j)` (`0 ≤ i, j ≤ 1`, `i + j = 1`) has full Hausdorff dimension `2`, in particular `Bad(i₁,
j₁) ∩ Bad(i₂, j₂) ≠ ∅`, which is Schmidt's conjecture. Source: AIM workshop Emerging applications of
measure rigidity (June 2004), open problems, Conjecture 32 (W. M. Schmidt),
https://aimath.org/WWN/measrigid/measrigid.pdf; resolution: D. Badziahin, A. Pollington and S.
Velani, On a problem in simultaneous Diophantine approximation: Schmidt's conjecture, Ann. of Math.
(2) 174 (2011), no. 3, 1837-1883, arXiv:1001.2694, Theorem 1: for finitely many pairs (i_t, j_t)
with 0 ≤ i_t, j_t ≤ 1, i_t + j_t = 1, the intersection of the sets Bad(i_t, j_t) has Hausdorff
dimension 2 (with x^{1/0} := 0), which the paper states establishes Schmidt's conjecture Bad(i₁, j₁)
∩ Bad(i₂, j₂) ≠ ∅, https://doi.org/10.4007/annals.2011.174.3.9.
-/
public theorem_wanted schmidtWeightedBadIntersect_holds : schmidtWeightedBadIntersect

end MathlibExt.NumberTheory.SchmidtWeightedBadlyApproximableAIMOtherProblem120Wanted
