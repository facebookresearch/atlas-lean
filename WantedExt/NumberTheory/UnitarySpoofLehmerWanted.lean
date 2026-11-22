/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import WantedExt.NumberTheory.SpoofLehmerFactorizationWanted

/-!
# Unitary spoof Lehmer factorizations (wanted statements)

Statements from Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26
(2026), Article A100. Hasanalizade's spoof factorization `x_1 ⋯ x_r` is a multiset of positive
integers; it is encoded as `spoofOfBases x` (all exponents `1`) from the Molnar–Singh module, so
that the spoof evaluation `ε̃(x_1 ⋯ x_r) = ∏ x_i` is `spoofEval (spoofOfBases x)` and the spoof
unitary totient `φ̃*(x_1 ⋯ x_r) = ∏ (x_i - 1)` is `spoofTotient (spoofOfBases x)`
(`spoofTotient_spoofOfBases`). A unitary `k`-Lehmer factorization (Equation (2)) is then
`IsSpoofLehmer k (spoofOfBases x)`: `k φ̃*(F) = ε̃(F) - 1` with at least two factors.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Spoof totient of a unitary factorization.** For natural numbers $x_1, \dots, x_r$, the spoof
totient of the spoof factorization $x_1 \cdots x_r$ with every exponent $1$ is
$\prod_{i=1}^{r} (x_i - 1)$, computed in the integers. This is Hasanalizade's spoof unitary
totient $\tilde{\varphi}^*(x_1 \cdots x_r)$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Section 1 (definition of `φ̃*`). -/
theorem spoofTotient_spoofOfBases (x : Multiset ℕ) :
    spoofTotient (spoofOfBases x) = (x.map fun a : ℕ => (a : ℤ) - 1).prod := by
  simp [spoofTotient, spoofOfBases, Multiset.map_map]

/-- **Nielsen's bound.** Let $r$, $a$ and $b$ be natural numbers and let $x_1 \le \dots \le x_r$ be
integers with every $x_j > 1$. If
$\prod_{j=1}^{r} (1 - 1/x_j) \le a/b < \prod_{j=1}^{r-1} (1 - 1/x_j)$, then
$a \prod_{j=1}^{r} x_j \le (a + 1)^{2^r} - (a + 1)^{2^{r-1}}$.

The paper assumes $r$, $a$ and $b$ positive; this follows from the hypotheses, since the left-hand
product is positive (so $a > 0$ and $b > 0$, reading $a/0$ as $0$) and both products equal $1$
when $r = 0$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Lemma 1 (`integers-2026-A100-lem-1`), citing P. Nielsen, Math. Comp. 84 (2015),
Lemma 1.4. -/
public theorem_wanted nielsen_prod_one_sub_inv_bound (r a b : ℕ) (x : Fin r → ℕ)
    (hmono : Monotone x) (hx : ∀ j, 1 < x j)
    (hlow : ∏ j, (1 - 1 / (x j : ℚ)) ≤ (a : ℚ) / b)
    (hup : (a : ℚ) / b <
      ∏ j ∈ Finset.univ.filter (fun j : Fin r => j.val + 1 < r), (1 - 1 / (x j : ℚ))) :
    a * ∏ j, x j ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1)

/-- **Bound on unitary Lehmer factorizations.** Let $k$ be an integer and let $x_1, \dots, x_r$ be
natural numbers. If the spoof factorization $x_1 \cdots x_r$ with every exponent $1$ is a spoof
$k$-Lehmer factorization (a unitary $k$-Lehmer factorization), then its spoof evaluation
$\tilde{e}(x_1 \cdots x_r) = \prod_{i=1}^{r} x_i$ is at most $2^{2^r} - 2^{2^{r-1}}$.

The paper takes $k > 0$; here $k$ is any integer. For $k \le 0$ the hypothesis forces the spoof
evaluation to be $1$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 1 (`integers-2026-A100-thm-1`). -/
public theorem_wanted spoofEval_le_of_isSpoofLehmer_spoofOfBases (k : ℤ) (x : Multiset ℕ)
    (h : IsSpoofLehmer k (spoofOfBases x)) :
    spoofEval (spoofOfBases x) ≤
      2 ^ 2 ^ Multiset.card x - 2 ^ 2 ^ (Multiset.card x - 1)

/-- **Repeated unitary Lehmer factorizations.** Let $k$ be an integer and let $x \ge 2$ and $s$ be
natural numbers. If the spoof factorization $x \cdots x$ with $s$ factors, each with base $x$ and
exponent $1$, is a spoof $k$-Lehmer factorization (a unitary $k$-Lehmer factorization), then
either $x = 2$ and $s \ge 2$, or $x = 3$ and $s \in \{2, 4\}$.

The paper assumes $k \ge 2$ instead of $x \ge 2$; as printed the statement fails for $x = 1$:
for every $s \ge 2$ the factorization $1 \cdots 1$ with $s$ factors has spoof totient $0$ and
spoof evaluation $1$, so it is a spoof $k$-Lehmer factorization for every $k$. The paper's proof
treats only $x = 2$, $x = 3$ and $x \ge 4$. When $x \ge 2$, the hypothesis forces $k \ge 2$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 2 (`integers-2026-A100-thm-2`). -/
public theorem_wanted eq_two_or_eq_three_of_isSpoofLehmer_replicate (k : ℤ) (x s : ℕ)
    (hx : 2 ≤ x) (h : IsSpoofLehmer k (spoofOfBases (Multiset.replicate s x))) :
    (x = 2 ∧ 2 ≤ s) ∨ (x = 3 ∧ (s = 2 ∨ s = 4))

/-- **Lehmer's lemma for unitary spoof factorizations.** Let $F$ be a finite multiset of integers,
write $E = \prod_{f \in F} f$ and $P = \prod_{f \in F} (f - 1)$, and let $k$, $\alpha$, $x$ and $y$
be integers with $\alpha = \pm 1$. If $k P = E + \alpha$ and $k P (x - 1)(y - 1) = E x y - 1$,
then $(\alpha x - E - \alpha)(\alpha y - E - \alpha) - (E^2 + \alpha E - \alpha) = 0$.

The second equation says that $F \cdot x \cdot y$ satisfies the unitary $k$-Lehmer equation
(Equation (3)). The paper takes $F$ with positive entries and $k \ge 2$; the identity holds for
every finite multiset of integers and every integer $k$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 3 (`integers-2026-A100-thm-3`). -/
public theorem_wanted unitary_spoof_lehmer_lemma (F : Multiset ℤ) (k α x y : ℤ)
    (hα : α = 1 ∨ α = -1)
    (hF : k * (F.map fun f => f - 1).prod = F.prod + α)
    (hxy : k * ((F.map fun f => f - 1).prod * (x - 1) * (y - 1)) = F.prod * x * y - 1) :
    (α * x - F.prod - α) * (α * y - F.prod - α) - (F.prod ^ 2 + α * F.prod - α) = 0

end

end MetaMathlibExt
