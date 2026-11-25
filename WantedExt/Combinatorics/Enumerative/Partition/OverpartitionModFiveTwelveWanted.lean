/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

/-- **Liang's congruences modulo 512 for overpartitions.** For all natural numbers $\alpha$ and $n$,
the number $\overline{p}(m)$ of overpartitions of $m$ satisfies
$\overline{p}(3^{8\alpha+7}(24n+5)) \equiv 0 \pmod{512}$ and
$\overline{p}(3^{8\alpha+7}(24n+13)) \equiv 0 \pmod{512}$.

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Theorem 1 (`integers-2025-A76-thm-1`). -/
public theorem_wanted overpartition_three_pow_congr_zero_mod_512 (α n : ℕ) :
    512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 5))) ∧
      512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 13)))

/-- **Eta-quotient identity in the powers $q^3$, $q^6$, $q^9$ and $q^{18}$.** Let $q$ be a complex
number with $|q| < 1$, and for each integer $k \ge 1$ write $E_k = (q^k; q^k)_\infty$, the
infinite q-Pochhammer symbol $\prod_{n=0}^{\infty} (1 - q^{k(n+1)})$. Then

$$
\frac{E_6^3 E_9^6}{E_3^3 E_{18}^3} =
  \frac{E_6^8 E_9}{E_3^4 E_{18}^2} - q^3 \, \frac{E_{18}^6}{E_9^3}.
$$

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (10) (`integers-2025-A76-lem-1`). Identity (9) of the same
lemma is `ramanujanPsi_three_dissection` (`OverpartitionSpt2CongruencesWanted`). -/
public theorem_wanted eulerFunction_six_cube_nine_six_div_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) =
      E 6 ^ 8 * E 9 / (E 3 ^ 4 * E 18 ^ 2) - q ^ 3 * (E 18 ^ 6 / E 9 ^ 3)

/-- **Three-dissection of $(q;q)_\infty / (q^2;q^2)_\infty^2$.** Let $q$ be a complex number
with $|q| < 1$, and for each integer $k \ge 1$ write $E_k = (q^k; q^k)_\infty$, the infinite
q-Pochhammer symbol $\prod_{n=0}^{\infty} (1 - q^{k(n+1)})$. Then

$$
\frac{E_1}{E_2^2} = \frac{E_3^2 E_9^3}{E_6^6} - q \, \frac{E_3^3 E_{18}^3}{E_6^7} +
  q^2 \, \frac{E_3^4 E_{18}^6}{E_6^8 E_9^3}.
$$

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (11) (`integers-2025-A76-lem-1`). -/
public theorem_wanted eulerFunction_one_div_two_sq_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 1 / E 2 ^ 2 =
      E 3 ^ 2 * E 9 ^ 3 / E 6 ^ 6 - q * (E 3 ^ 3 * E 18 ^ 3 / E 6 ^ 7) +
        q ^ 2 * (E 3 ^ 4 * E 18 ^ 6 / (E 6 ^ 8 * E 9 ^ 3))

end

end MetaMathlibExt
