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

/-- On a factorization with all exponents `1`, the Molnar–Singh spoof totient is Hasanalizade's
spoof unitary totient `φ̃*(x_1 ⋯ x_r) = ∏ (x_i - 1)`.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Section 1 (definition of `φ̃*`). -/
theorem spoofTotient_spoofOfBases (x : Multiset ℕ) :
    spoofTotient (spoofOfBases x) = (x.map fun a : ℕ => (a : ℤ) - 1).prod := by
  simp [spoofTotient, spoofOfBases, Multiset.map_map]

/-- **Nielsen's bound** (quoted as Lemma 1): if `1 < x_1 ≤ ⋯ ≤ x_r` are integers and
`∏_{j=1}^{r} (1 - 1/x_j) ≤ a/b < ∏_{j=1}^{r-1} (1 - 1/x_j)`, then
`a ∏_{j=1}^{r} x_j ≤ (a + 1)^{2^r} - (a + 1)^{2^{r-1}}`. The paper's positivity of `r, a, b` is
implied by the hypotheses (an empty product is `1`, and `a/0 = 0` in Lean) and is not stated.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Lemma 1 (`integers-2026-A100-lem-1`), citing P. Nielsen, Math. Comp. 84 (2015),
Lemma 1.4. -/
public theorem_wanted nielsen_prod_one_sub_inv_bound (r a b : ℕ) (x : Fin r → ℕ)
    (hmono : Monotone x) (hx : ∀ j, 1 < x j)
    (hlow : ∏ j, (1 - 1 / (x j : ℚ)) ≤ (a : ℚ) / b)
    (hup : (a : ℚ) / b <
      ∏ j ∈ Finset.univ.filter (fun j : Fin r => j.val + 1 < r), (1 - 1 / (x j : ℚ))) :
    a * ∏ j, x j ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1)

/-- **Bound on unitary Lehmer factorizations**: if `x_1 ⋯ x_r` is a unitary `k`-Lehmer
factorization, then `ε̃(x_1 ⋯ x_r) ≤ 2^{2^r} - 2^{2^{r-1}}`. The paper takes `k ∈ ℤ_{>0}`; the
statement here allows every integer `k` (for `k ≤ 0` the equation forces `ε̃ = 1`).

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 1 (`integers-2026-A100-thm-1`). -/
public theorem_wanted spoofEval_le_of_isSpoofLehmer_spoofOfBases (k : ℤ) (x : Multiset ℕ)
    (h : IsSpoofLehmer k (spoofOfBases x)) :
    spoofEval (spoofOfBases x) ≤
      2 ^ 2 ^ Multiset.card x - 2 ^ 2 ^ (Multiset.card x - 1)

/-- **Repeated unitary Lehmer factorizations**: if `[x]_s = x ⋯ x` (`s` copies) is a unitary
`k`-Lehmer factorization with `x ≥ 2`, then `x = 2` and `s ≥ 2`, or `x = 3` and `s ∈ {2, 4}`.

The paper assumes `k ≥ 2` instead of `x ≥ 2`; as printed the statement fails for `x = 1`, since
`[1]_s` satisfies `k φ̃*([1]_s) = 0 = ε̃([1]_s) - 1` for every `k` and `s ≥ 2`. The paper's proof
treats only `x = 2`, `x = 3` and `x ≥ 4`. With `x ≥ 2` the hypothesis `k ≥ 2` is implied and is
not stated.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 2 (`integers-2026-A100-thm-2`). -/
public theorem_wanted eq_two_or_eq_three_of_isSpoofLehmer_replicate (k : ℤ) (x s : ℕ)
    (hx : 2 ≤ x) (h : IsSpoofLehmer k (spoofOfBases (Multiset.replicate s x))) :
    (x = 2 ∧ 2 ≤ s) ∨ (x = 3 ∧ (s = 2 ∨ s = 4))

/-- **Lehmer's lemma for unitary spoof factorizations**: write `E = ∏ F` and `P = ∏ (f - 1)` over
`f ∈ F`. If `k P = E + α` with `α = ±1` and the integers `x, y` satisfy
`k P (x - 1)(y - 1) = E x y - 1` (that is, `F ⋅ x ⋅ y` is unitary `k`-Lehmer, Equation (3)), then
`(α x - E - α)(α y - E - α) - (E^2 + α E - α) = 0`. The paper takes `F` with positive entries and
`k ≥ 2`; the identity holds for every multiset of integers and every integer `k`, so these
hypotheses are not stated.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 3 (`integers-2026-A100-thm-3`). -/
public theorem_wanted unitary_spoof_lehmer_lemma (F : Multiset ℤ) (k α x y : ℤ)
    (hα : α = 1 ∨ α = -1)
    (hF : k * (F.map fun f => f - 1).prod = F.prod + α)
    (hxy : k * ((F.map fun f => f - 1).prod * (x - 1) * (y - 1)) = F.prod * x * y - 1) :
    (α * x - F.prod - α) * (α * y - F.prod - α) - (F.prod ^ 2 + α * F.prod - α) = 0

end

end MetaMathlibExt
