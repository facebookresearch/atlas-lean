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

/-- **Ramanujan's function $k(q)$.** For a complex number $q$, Ramanujan's function is
$$
k(q) = \frac{q\,(q;q^{10})_\infty (q^2;q^{10})_\infty (q^8;q^{10})_\infty (q^9;q^{10})_\infty}
{(q^3;q^{10})_\infty (q^4;q^{10})_\infty (q^6;q^{10})_\infty (q^7;q^{10})_\infty},
$$
where $(a;x)_\infty$ is the raw infinite q-Pochhammer product $\prod_{n \ge 0} (1 - a x^n)$
(equal to $1$ by convention when this product does not converge unconditionally), and a
quotient by $0$ is read as $0$.

For $|q| < 1$ this is the product representation of $k(q) = r(q)\,r(q^2)^2$, where $r$ is the
Rogers–Ramanujan continued fraction.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
noncomputable def ramanujanK (q : ℂ) : ℂ :=
  q * (qPochhammerInfRaw q (q ^ 10) * qPochhammerInfRaw (q ^ 2) (q ^ 10) *
        qPochhammerInfRaw (q ^ 8) (q ^ 10) * qPochhammerInfRaw (q ^ 9) (q ^ 10)) /
    (qPochhammerInfRaw (q ^ 3) (q ^ 10) * qPochhammerInfRaw (q ^ 4) (q ^ 10) *
        qPochhammerInfRaw (q ^ 6) (q ^ 10) * qPochhammerInfRaw (q ^ 7) (q ^ 10))

/-- **Ramanujan's function $k$ vanishes at $0$.** Ramanujan's function satisfies $k(0) = 0$.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
theorem ramanujanK_zero : ramanujanK 0 = 0 := by
  simp [ramanujanK]

/-- **Eta-quotient expressions for Ramanujan's function $k$.** Let $q$ be a complex number with
$0 < |q| < 1$, write $f_m = (q^m;q^m)_\infty = \prod_{n \ge 1} (1 - q^{mn})$ for $m \ge 1$, and let
$k = k(q)$ be the value of Ramanujan's function. Then
$$
\frac{f_2 f_5^5}{q f_1 f_{10}^5} = \frac{1}{k} - k, \qquad
\frac{f_2^4 f_5^2}{q f_1^2 f_{10}^4} = \frac{1}{k} + 1 - k, \qquad
\frac{f_1^3 f_5}{q f_2 f_{10}^3} = \frac{1}{k} - 4 - k.
$$

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

/-- **Ramanujan's function $k$ at $q$ and $q^2$ as an eta quotient.** For every complex number
$q$ with $0 < |q| < 1$, Ramanujan's function $k$ satisfies
$$
\frac{k(q)}{k(q^2)} - \frac{k(q^2)}{k(q)} =
\frac{(q;q)_\infty (q^5;q^5)_\infty^3}{q\,(q^{10};q^{10})_\infty^4},
$$
where $(a;x)_\infty = \prod_{n \ge 0} (1 - a x^n)$ is the infinite q-Pochhammer product.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Lemma 3 (`integers-2026-A41-lem-3`). -/
public theorem_wanted ramanujanK_div_sub_div_sq (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ramanujanK q / ramanujanK (q ^ 2) - ramanujanK (q ^ 2) / ramanujanK q =
      qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 5) (q ^ 5) ^ 3 /
        (q * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 4)

/-- **Modular equation of degree 2 for Ramanujan's function $k$.** For every complex number $q$
with $|q| < 1$, the values $X = k(q)$ and $Y = k(q^2)$ of Ramanujan's function satisfy
$X^2 - Y + 2XY + X^2 Y + Y^2 = 0$.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Theorem 4 (`integers-2026-A41-thm-4`). -/
public theorem_wanted ramanujanK_sq_relation (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanK q ^ 2 - ramanujanK (q ^ 2) + 2 * ramanujanK q * ramanujanK (q ^ 2) +
        ramanujanK q ^ 2 * ramanujanK (q ^ 2) + ramanujanK (q ^ 2) ^ 2 = 0

/-- **Ramanujan's level-10 theta function identities.** For complex $x$ with $|x| < 1$, let
$\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$, $\psi(x) = \sum_{n \ge 0} x^{n(n+1)/2}$ and
$f(-x) = \prod_{n \ge 1} (1 - x^n)$, so that $f(x) = \prod_{n \ge 1} (1 - (-x)^n)$. Then for
every complex number $q$ with $|q| < 1$,
$$
\frac{\varphi(q)^5}{\varphi(q^5)} + \frac{\varphi(-q^2)^5}{\varphi(-q^{10})} +
2\,\frac{f(q)^5}{f(q^5)} = 4\,\frac{\psi(q)^5}{\psi(q^5)}
$$
and
$$
\varphi(q)^2 \varphi(q^5)^2 - \varphi(-q)^2 \varphi(-q^5)^2 - 16 q^3 \psi(q^2)^2 \psi(q^{10})^2 =
8 q\, f(-q^2)^2 f(-q^{10})^2.
$$

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
