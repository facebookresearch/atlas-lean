/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The total variation distance between `t_r` and `N(0, 1)` is of exact order `1/r` (AimPL, 1.25)

AimPL Stein's method and applications in high-dimensional statistics, Problem 1.25: let `t_r`
denote the `t` distribution with `r` degrees of freedom; as `r → ∞`, `t_r → Z` in distribution,
where `Z ∼ N(0, 1)`. (a) Show that there exists a constant `c > 0` for which `d_TV(t_r, Z) ≤ c/r`.
(b) Find the best such constant. (c) Does there exist a constant `c'` for which
`d_TV(t_r, Z) ≥ c'/r`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace MathlibExt.Probability.StudentTNormalTotalVariationAIMProbabilityProblem25Wanted

/-!
Source: AimPL: Stein's method and applications in high-dimensional statistics, Section 1, Problem
1.25, https://aimpl.org/steinhd/1/. UnsolvedMath record UM-20002583 (`AIM-PROBABILITY-0025`),
dataset ulamai/UnsolvedMath v1.8.0.

`t_r` has Student's density `f_r(x) = Γ((r + 1)/2) / (√(r π) Γ(r/2)) · (1 + x²/r)^{-(r+1)/2}` for
real `r > 0` (Pinelis's (1.1)), `Z` has density `ProbabilityTheory.gaussianPDFReal 0 1`, and
`d_TV(t_r, Z) = (1/2) ∫ |f_r - φ|` (Pinelis's (1.3); Mathlib's `MeasureTheory.tvDist` takes values
in `[0, 2]` and is twice this distance, so the density formula is kept). The two targets are
Pinelis's Theorem 1.2, rewritten through his identity `(1/2) d_TV = d_Ko`: `d_TV(t_r, Z) < κ/r` for
every real `r ≥ 4`, with `κ = (1/2) √((7 + 5√2)/(π e^{1+√2})) ≈ 0.3165` (twice Pinelis's `C`), which
answers (a), and `r · d_TV(t_r, Z) → κ`, so that `κ` is the best constant (b) and, for every `c' <
κ`, `d_TV(t_r, Z) ≥ c'/r` for all large `r` (c). The forms of (a)-(c) for every `r ≥ 1` (in
particular the best constant when `r = 1, 2, 3` are included) are not stated by the source and are
not formalized.
-/

open MeasureTheory Filter Topology

/-- The density of Student's `t` distribution with `r > 0` degrees of freedom,
`Γ((r + 1)/2) / (√(r π) Γ(r/2)) · (1 + x²/r)^{-(r+1)/2}`. -/
noncomputable def studentTDensity (r x : ℝ) : ℝ :=
  Real.Gamma ((r + 1) / 2) / (Real.sqrt (r * Real.pi) * Real.Gamma (r / 2)) *
    (1 + x ^ 2 / r) ^ (-(r + 1) / 2)

/-- The total variation distance `d_TV(t_r, Z) = (1/2) ∫ |f_r - φ|` between Student's `t_r` and the
standard normal law `Z ∼ N(0, 1)` (density `ProbabilityTheory.gaussianPDFReal 0 1`). -/
noncomputable def tvStudentNormal (r : ℝ) : ℝ :=
  (1 / 2) * ∫ x, |studentTDensity r x - ProbabilityTheory.gaussianPDFReal 0 1 x|

/-- Pinelis's sharp constant for the total variation distance,
`κ = (1/2) √((7 + 5√2)/(π e^{1+√2})) = 0.3164…` (twice the constant `C` of his Theorem 1.2,
which bounds `d_Ko = (1/2) d_TV`). -/
noncomputable def pinelisConstant : ℝ :=
  Real.sqrt ((7 + 5 * Real.sqrt 2) / (Real.pi * Real.exp (1 + Real.sqrt 2))) / 2

/-- AimPL Problem 1.25 (a), with the sharp constant: `d_TV(t_r, Z) < κ / r` for every real
`r ≥ 4`. -/
def tvStudentNormalUpperBound : Prop :=
  ∀ r : ℝ, 4 ≤ r → tvStudentNormal r < pinelisConstant / r

/-- AimPL Problem 1.25 (b) and (c): `r · d_TV(t_r, Z) → κ` as `r → ∞`, so `κ` is the best
constant in (a) and `d_TV(t_r, Z)` is eventually at least `c' / r` for every `c' < κ`. -/
def tvStudentNormalAsymptotic : Prop :=
  Tendsto (fun r : ℝ => r * tvStudentNormal r) atTop (𝓝 pinelisConstant)

/--
Resolved true: Pinelis proves `(1/2) d_TV(t_p, Z) = d_Ko(t_p, Z) < C/p` for every real `p ≥ 4` with
`C = κ/2`, that is `d_TV(t_r, Z) < κ/r`. Source: AimPL: Stein's method and applications in
high-dimensional statistics, Section 1, Problem 1.25, https://aimpl.org/steinhd/1/; resolution: I.
Pinelis, Exact bounds on the closeness between the Student and standard normal distributions, ESAIM:
Probab. Stat. 19 (2015), 24-27 (full version arXiv:1101.3328), Proposition 1.1(i): (1/2) d_TV(p, q)
= d_Ko(p, q) for 0 < p < q ≤ ∞, with d_TV(p) = (1/2) ∫ |f_p − φ| (1.3); Theorem 1.2: for every real
p ≥ 4, (1/2) d_TV(p) = d_Ko(p) < C/p (1.6) with C = (1/4) √((7 + 5√2)/(π e^{1+√2})) = 0.158…, and
lim_{p→∞} p d_Ko(p) = C (1.8), 'so that the constant C is the best possible one in (1.6)',
https://doi.org/10.1051/ps/2014014.
-/
public theorem_wanted tvStudentNormalUpperBound_holds : tvStudentNormalUpperBound

/--
Resolved true: Pinelis proves `p·d_Ko(t_p, Z) → C` with `d_Ko = (1/2) d_TV`, that is `r·d_TV(t_r, Z)
→ κ = 2C`. Source: AimPL: Stein's method and applications in high-dimensional statistics, Section 1,
Problem 1.25, https://aimpl.org/steinhd/1/; resolution: I. Pinelis, Exact bounds on the closeness
between the Student and standard normal distributions, ESAIM: Probab. Stat. 19 (2015), 24-27 (full
version arXiv:1101.3328), Proposition 1.1(i): (1/2) d_TV(p, q) = d_Ko(p, q) for 0 < p < q ≤ ∞, with
d_TV(p) = (1/2) ∫ |f_p − φ| (1.3); Theorem 1.2: for every real p ≥ 4, (1/2) d_TV(p) = d_Ko(p) < C/p
(1.6) with C = (1/4) √((7 + 5√2)/(π e^{1+√2})) = 0.158…, and lim_{p→∞} p d_Ko(p) = C (1.8), 'so that
the constant C is the best possible one in (1.6)', https://doi.org/10.1051/ps/2014014.
-/
public theorem_wanted tvStudentNormalAsymptotic_holds : tvStudentNormalAsymptotic

end MathlibExt.Probability.StudentTNormalTotalVariationAIMProbabilityProblem25Wanted
