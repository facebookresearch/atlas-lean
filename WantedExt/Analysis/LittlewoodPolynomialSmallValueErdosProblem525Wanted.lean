/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small values of `±1` polynomials on the unit circle (Erdős Problem 525)

Erdős Problem 525: do all but `o(2 ^ n)` of the degree-`n` polynomials with coefficients `±1`
satisfy `|f(z)| < 1` for some `|z| = 1`? What is the behaviour of `min_{|z| = 1} |f(z)|`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Analysis.LittlewoodPolynomialSmallValueErdosProblem525Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #525, https://www.erdosproblems.com/525 (status
PROVED). UnsolvedMath record UM-30006917 (`EP-525`), dataset ulamai/UnsolvedMath v1.8.0.

Only the first question is stated; the second asks for a description. A polynomial is its
coefficient vector in `{±1} ^ (n + 1)`; `o(2 ^ n)` is the exceptional count divided by `2 ^ n`
tending to `0`. Compared with the formal-conjectures statement `ErdosProblems/525.lean` (equivalent
to `erdos_525.parts.i`; no code imported).
-/

/-- The polynomial `∑_{j ≤ n} εⱼ z ^ j` with coefficients `εⱼ = ±1` (`true ↦ 1`, `false ↦ -1`),
evaluated at `z`. -/
def signPolynomialEval {n : ℕ} (ε : Fin (n + 1) → Bool) (z : ℂ) : ℂ :=
  ∑ j, (if ε j then (1 : ℂ) else -1) * z ^ (j : ℕ)

/-- Erdős Problem 525, first question: all but `o(2 ^ n)` of the degree-`n` polynomials with
coefficients `±1` satisfy `|f(z)| < 1` for some `|z| = 1`. -/
def almostAllSignPolynomialsSmallOnCircle : Prop :=
  Filter.Tendsto (fun n : ℕ =>
      ({ε : Fin (n + 1) → Bool | ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖signPolynomialEval ε z‖}.ncard : ℝ) /
        2 ^ n)
    Filter.atTop (nhds 0)

/--
Resolved true: Kashin proved that `min_{|z| = 1} |f(z)| → 0` in probability for random `±1`
coefficients, so the proportion with `min |f| ≥ 1` tends to `0`; Konyagin sharpened this to `n ^
(-1/2 + o(1))`. Source: T. F. Bloom, Erdős Problems, Problem #525, https://www.erdosproblems.com/525
(status PROVED); resolution: B. S. Kashin, The properties of random trigonometric polynomials with
±1 coefficients, Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1987), 40-46, erdosproblems.com/525: yes;
Kashin proved min |f| = o(1) in probability (Littlewood's conjecture), Konyagin min |f| ≤ n^{-1/2 +
o(1)} in probability, https://www.erdosproblems.com/525.
-/
public theorem_wanted almostAllSignPolynomialsSmallOnCircle_holds :
    almostAllSignPolynomialsSmallOnCircle

end MathlibExt.Analysis.LittlewoodPolynomialSmallValueErdosProblem525Wanted
