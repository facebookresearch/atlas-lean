/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

namespace MetaMathlibExt

@[expose] public section

open MetaMathlibExt.QPochhammer

/-! Notation of the source, on the open unit disk `‖q‖ < 1`:
* `f(-q^m) = (q^m; q^m)_∞` is `qPochhammerInfRaw (q ^ m) (q ^ m)`, and `f(q^m) = f(-(-q^m))` is
  `qPochhammerInfRaw (-q ^ m) (-q ^ m)` (Euler: `f(-x) = f(-x, -x²) = (x; x)_∞`);
* `φ(q) = f(q, q) = ∑_{n ∈ ℤ} q^{n²}` is `ramanujanThetaRaw q q`;
* `ψ(q) = f(q, q³) = ∑_{n ≥ 0} q^{n(n+1)/2}` is `ramanujanThetaRaw q (q ^ 3)`.
All raw sums and products converge on the disk, where they equal the canonical values. -/

/-- Ramanujan's function `k(q) = r(q) r²(q²)`, through its product representation
`k(q) = q (q, q², q⁸, q⁹; q¹⁰)_∞ / (q³, q⁴, q⁶, q⁷; q¹⁰)_∞`.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
noncomputable def ramanujanK (q : ℂ) : ℂ :=
  q * (qPochhammerInfRaw q (q ^ 10) * qPochhammerInfRaw (q ^ 2) (q ^ 10) *
        qPochhammerInfRaw (q ^ 8) (q ^ 10) * qPochhammerInfRaw (q ^ 9) (q ^ 10)) /
    (qPochhammerInfRaw (q ^ 3) (q ^ 10) * qPochhammerInfRaw (q ^ 4) (q ^ 10) *
        qPochhammerInfRaw (q ^ 6) (q ^ 10) * qPochhammerInfRaw (q ^ 7) (q ^ 10))

/-- `k(0) = 0`.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
theorem ramanujanK_zero : ramanujanK 0 = 0 := by
  simp [ramanujanK]

/-- Three eta-quotient expressions for `k(q)`: for `0 < ‖q‖ < 1`, with `k = k(q)`,
`f(-q²) f⁵(-q⁵) / (q f(-q) f⁵(-q¹⁰)) = 1/k - k`,
`f⁴(-q²) f²(-q⁵) / (q f²(-q) f⁴(-q¹⁰)) = 1/k + 1 - k`, and
`f³(-q) f(-q⁵) / (q f(-q²) f³(-q¹⁰)) = 1/k - 4 - k`.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Lemma 2, Equations (5)-(7)
(`integers-2026-A41-lem-2`). -/
public theorem_wanted ramanujanK_eta_quotients (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    qPochhammerInfRaw (q ^ 2) (q ^ 2) * qPochhammerInfRaw (q ^ 5) (q ^ 5) ^ 5 /
        (q * qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 5) =
      1 / ramanujanK q - ramanujanK q ∧
    qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 4 * qPochhammerInfRaw (q ^ 5) (q ^ 5) ^ 2 /
        (q * qPochhammerInfRaw q q ^ 2 * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 4) =
      1 / ramanujanK q + 1 - ramanujanK q ∧
    qPochhammerInfRaw q q ^ 3 * qPochhammerInfRaw (q ^ 5) (q ^ 5) /
        (q * qPochhammerInfRaw (q ^ 2) (q ^ 2) * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 3) =
      1 / ramanujanK q - 4 - ramanujanK q

/-- For `0 < ‖q‖ < 1`: `k(q)/k(q²) - k(q²)/k(q) = f(-q) f³(-q⁵) / (q f⁴(-q¹⁰))`. The
hypothesis `q ≠ 0` excludes the point where the divisions by `q` and `k(q)` are undefined.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Lemma 3 (`integers-2026-A41-lem-3`). -/
public theorem_wanted ramanujanK_div_sub_div_sq (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ramanujanK q / ramanujanK (q ^ 2) - ramanujanK (q ^ 2) / ramanujanK q =
      qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 5) (q ^ 5) ^ 3 /
        (q * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 4)

/-- Polynomial relation between `X = k(q)` and `Y = k(q²)` on the unit disk:
`X² - Y + 2XY + X²Y + Y² = 0`.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Theorem 4 (`integers-2026-A41-thm-4`). -/
public theorem_wanted ramanujanK_sq_relation (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanK q ^ 2 - ramanujanK (q ^ 2) + 2 * ramanujanK q * ramanujanK (q ^ 2) +
        ramanujanK q ^ 2 * ramanujanK (q ^ 2) + ramanujanK (q ^ 2) ^ 2 = 0

/-- Ramanujan's level-10 theta identities: on the unit disk,
`φ⁵(q)/φ(q⁵) + φ⁵(-q²)/φ(-q¹⁰) + 2 f⁵(q)/f(q⁵) = 4 ψ⁵(q)/ψ(q⁵)` and
`φ²(q)φ²(q⁵) - φ²(-q)φ²(-q⁵) - 16 q³ ψ²(q²)ψ²(q¹⁰) = 8 q f²(-q²) f²(-q¹⁰)`.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Theorem 1, Equations (3) and (4)
(`integers-2026-A41-thm-1`). -/
public theorem_wanted ramanujan_theta_level_ten (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q q ^ 5 / ramanujanThetaRaw (q ^ 5) (q ^ 5) +
        ramanujanThetaRaw (-q ^ 2) (-q ^ 2) ^ 5 / ramanujanThetaRaw (-q ^ 10) (-q ^ 10) +
        2 * (qPochhammerInfRaw (-q) (-q) ^ 5 / qPochhammerInfRaw (-q ^ 5) (-q ^ 5)) =
      4 * (ramanujanThetaRaw q (q ^ 3) ^ 5 / ramanujanThetaRaw (q ^ 5) ((q ^ 5) ^ 3)) ∧
    ramanujanThetaRaw q q ^ 2 * ramanujanThetaRaw (q ^ 5) (q ^ 5) ^ 2 -
        ramanujanThetaRaw (-q) (-q) ^ 2 * ramanujanThetaRaw (-q ^ 5) (-q ^ 5) ^ 2 -
        16 * q ^ 3 * ramanujanThetaRaw (q ^ 2) ((q ^ 2) ^ 3) ^ 2 *
          ramanujanThetaRaw (q ^ 10) ((q ^ 10) ^ 3) ^ 2 =
      8 * q * qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 2

end

end MetaMathlibExt
