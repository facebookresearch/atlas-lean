/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Data.Nat.Prime.Defs

/-!
# A quadratic sum over congruent pairs modulo a prime

Statement from Brahim Mittou, *Explicit Evaluation of a Quadratic Sum Over Congruent Pairs
Modulo a Prime*, INTEGERS 25 (2025), Article A85.

For a prime `p` and a positive integer `l` coprime to `p`,
`F(p, l) = ∑_{1 ≤ a, b ≤ p-1, b ≡ a l (mod p)} (a/p - 1/2)(b/p - 1/2)`, and
`s(p, l) = (1/(4l)) ∑_{a=1}^{l-1} cot(πa/l) cot(πap/l)` is the Dedekind sum.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Mittou's evaluation of a quadratic sum over congruent pairs.** Let $p$ be a prime and $l$ a
positive integer with $\gcd(p, l) = 1$. Let $F(p, l)$ be the sum of
$\left(\frac{a}{p} - \frac{1}{2}\right)\left(\frac{b}{p} - \frac{1}{2}\right)$ over all pairs of
integers $a, b$ with $1 \le a, b \le p - 1$ and $b \equiv a l \pmod{p}$, and let
$$s(p, l) = \frac{1}{4l} \sum_{a=1}^{l-1} \cot\left(\frac{\pi a}{l}\right)
\cot\left(\frac{\pi a p}{l}\right)$$
be the Dedekind sum. Then
$$F(p, l) = \frac{p^2 - 3lp + l^2 + 1}{12 l p} - s(p, l).$$

Domain extension: the paper assumes $p \ge 3$; the identity also holds for $p = 2$ (then $l$ is
odd and both sides vanish), so that hypothesis is dropped. The paper's remark that $s(p, l)$
depends only on $p \bmod l$ is not restated.

Source: Brahim Mittou, *Explicit Evaluation of a Quadratic Sum Over Congruent Pairs Modulo a
Prime*, INTEGERS 25 (2025), Article A85, Theorem 1 (`integers-2025-A85-thm-1`). -/
public theorem_wanted congruentPairQuadraticSum_eq_sub_dedekindSum {p l : ℕ} (hp : p.Prime)
    (hl : 0 < l) (hpl : p.Coprime l) :
    (∑ a ∈ Finset.Icc 1 (p - 1),
        ∑ b ∈ (Finset.Icc 1 (p - 1)).filter (fun b => b ≡ a * l [MOD p]),
          ((a : ℝ) / p - 1 / 2) * ((b : ℝ) / p - 1 / 2)) =
      ((p : ℝ) ^ 2 - 3 * l * p + l ^ 2 + 1) / (12 * l * p) -
        1 / (4 * l) * ∑ a ∈ Finset.Icc 1 (l - 1),
          Real.cot (Real.pi * a / l) * Real.cot (Real.pi * a * p / l)

end

end MetaMathlibExt
