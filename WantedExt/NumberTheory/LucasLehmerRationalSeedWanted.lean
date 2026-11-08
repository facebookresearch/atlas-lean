/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Pell

/-!
# The Lucas–Lehmer test with the rational seed `6/5`

Statement from E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer
Primality Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5.

The sequence is `s_{i+1} = s_i² - 2` computed modulo `M_n = 2ⁿ - 1`, so `s_{k}` is the
`(k - 1)`-fold iterate of `x ↦ x² - 2` from the seed `s_1`. The rational seed `6/5` is read in
`ZMod M_n` as `6 · 5⁻¹`; `5` is a unit modulo `M_n` for odd `n`, since `5 ∣ 2ⁿ - 1` only when
`4 ∣ n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- For odd `n ≥ 3` (oddness is carried by the two residue cases) and the rational seed
`s_1 = 6/5`, `M_n` is prime if and only if `s_{n-1} ≡ 0 (mod M_n)` when `n ≡ 3 (mod 4)`, and if
and only if `s_{n-2} ≡ 0 (mod M_n)` when `n ≡ 1 (mod 4)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 17. -/
theorem_wanted mersenne_prime_iff_lucasLehmer_six_div_five {n : ℕ} (h3 : 3 ≤ n) :
    (n % 4 = 3 → ((mersenne n).Prime ↔
      (fun x : ZMod (mersenne n) => x ^ 2 - 2)^[n - 2] (6 * 5⁻¹) = 0)) ∧
    (n % 4 = 1 → ((mersenne n).Prime ↔
      (fun x : ZMod (mersenne n) => x ^ 2 - 2)^[n - 3] (6 * 5⁻¹) = 0))

/-! ### Lehmer sequences and the general test -/

/-- Lehmer's companion sequence `V̄_k(R, Q)` (for `P = √R`): `V̄_0 = 2`, `V̄_1 = 1`,
`V̄_2 = R - 2Q`, `V̄_3 = R - 3Q`, and `X_{k+4} = (R - 2Q) X_{k+2} - Q² X_k`; it equals
`V_k(√R, Q)` for even `k` and `V_k(√R, Q)/√R` for odd `k`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2 (definition of `V̄_n` and recurrence (4thLehmer)). -/
def lehmerV (R Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | 2 => R - 2 * Q
  | 3 => R - 3 * Q
  | k + 4 => (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k

/-- The fourth-order recurrence of `V̄_k(R, Q)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2, recurrence (4thLehmer). -/
theorem lehmerV_add_four (R Q : ℤ) (k : ℕ) :
    lehmerV R Q (k + 4) = (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k :=
  rfl

/-- For `R = 2`, `Q = -1` (the parameters giving the seed `4`), `V̄_2 = 4`, `V̄_4 = 14 = 4² - 2`
and `V̄_8 = 194 = 14² - 2`, as the doubling formula (LehmerV2n) predicts.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2 (formula (LehmerV2n) and the case `R = 2`, `Q = -1` after Theorem 6). -/
theorem lehmerV_two_neg_one :
    lehmerV 2 (-1) 2 = 4 ∧ lehmerV 2 (-1) 4 = 14 ∧ lehmerV 2 (-1) 8 = 194 := by
  decide

/-- Let `n ≥ 3` be odd. If `gcd(M_n, Q) = 1` and `M_n ∣ V̄_{(M_n+1)/2}(R, Q)`, then `M_n` is
prime. Here `(M_n + 1)/2 = 2^{n-1}`; `R`, `Q` are arbitrary integers (no coprimality or
`D ≠ 0` hypothesis is needed for the statement).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 4. -/
public theorem_wanted mersenne_prime_of_dvd_lehmerV {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (R Q : ℤ) (hQ : Int.gcd (mersenne n) Q = 1)
    (hV : (mersenne n : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))) :
    (mersenne n).Prime

/-- Let `n ≥ 3` be odd and `M_n` prime, and let `D = R - 4Q`. If the Legendre symbols
`(DR | M_n)` and `(QR | M_n)` are both `-1`, then `M_n ∣ V̄_{(M_n+1)/2}(R, Q)`. The Legendre
symbols are written as Jacobi symbols (equal, `M_n` being prime).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 5. -/
public theorem_wanted mersenne_dvd_lehmerV_of_jacobi {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hp : (mersenne n).Prime) (R Q : ℤ)
    (hDR : jacobiSym ((R - 4 * Q) * R) (mersenne n) = -1)
    (hQR : jacobiSym (Q * R) (mersenne n) = -1) :
    (mersenne n : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))

/-- Let `n ≥ 3` be odd and `M_n` prime. If `r, d, q, X, Y, Z` are integers with
`gcd(M_n, Y) = 1`, `4qY² = rX² - dZ²` and Legendre symbols `(rd | M_n) = (qr | M_n) = -1`, then
`M_n ∣ V̄_{(M_n+1)/2}(R, Q)` for `R = rX²`, `Q = qY²` (so `D = R - 4Q = dZ²`). The Legendre
symbols are written as Jacobi symbols.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 7. -/
public theorem_wanted mersenne_dvd_lehmerV_of_diophantine {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hp : (mersenne n).Prime) (r d q X Y Z : ℤ) (hY : Int.gcd (mersenne n) Y = 1)
    (hdio : 4 * q * Y ^ 2 = r * X ^ 2 - d * Z ^ 2)
    (hrd : jacobiSym (r * d) (mersenne n) = -1) (hqr : jacobiSym (q * r) (mersenne n) = -1) :
    (mersenne n : ℤ) ∣ lehmerV (r * X ^ 2) (q * Y ^ 2) (2 ^ (n - 1))

/-- Euler's observation: let `ab > 1` not be a perfect square and let `(x_k, y_k)`, with
`x_k + √(ab) y_k = (x_1 + √(ab) y_1)^k`, be the powers of the fundamental solution of
`x² - ab y² = 1`. If `(T_1, U_1)` solves `aT² - bU² = c`, then
`T_k = T_1 x_{k-1} + b U_1 y_{k-1}`, `U_k = a T_1 y_{k-1} + U_1 x_{k-1}` (`k ≥ 1`) are
infinitely many distinct solutions; here indexed by `j = k - 1 ≥ 0`. Added hypothesis `c ≠ 0`:
for `c = 0` the only solution is `(0, 0)`, since `ab` is not a square.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 8. -/
public theorem_wanted pell_euler_solutions (a b c T₁ U₁ : ℤ) (hab : 1 < a * b)
    (hsq : ¬ IsSquare (a * b)) (hc : c ≠ 0) (h₁ : a * T₁ ^ 2 - b * U₁ ^ 2 = c)
    (ε : Pell.Solution₁ (a * b)) (hε : Pell.IsFundamental ε) :
    (∀ j : ℕ, a * (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y) ^ 2 -
        b * (a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x) ^ 2 = c) ∧
      Function.Injective fun j : ℕ =>
        (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y, a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x)

/-! ### Squarefree parts, the order of `2`, and condition (etar) -/

/-- `k` is the odd squarefree part `N^*` of `N`: `k` is odd and squarefree and
`N = 2^a m² k`. For positive `N` this `k` is unique: it is `sqf(N)` when that is odd and
`sqf(N)/2` otherwise.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (definition of `N^*`). -/
def IsOddSquarefreePart (N : ℤ) (k : ℕ) : Prop :=
  Odd k ∧ Squarefree k ∧ ∃ a : ℕ, ∃ m : ℤ, N = 2 ^ a * m ^ 2 * k

/-- `360^* = 5` (`sqf(360) = 10`).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example `10 = sqf(360)`). -/
theorem isOddSquarefreePart_360 : IsOddSquarefreePart 360 5 :=
  ⟨by decide, Nat.prime_five.prime.squarefree, 1, 6, by norm_num⟩

/-- `Ω(m)`: the order `ω(m)` of `2` modulo `m`, doubled when it is odd.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (definitions of `ω(m)` and `Ω(m)`). -/
noncomputable def mersenneOmega (m : ℕ) : ℕ :=
  if Odd (orderOf (2 : ZMod m)) then 2 * orderOf (2 : ZMod m) else orderOf (2 : ZMod m)

/-- `Ω(35 · 39) = 12`, the value for the seed `s_1 = 37`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example `s_1 = 37`). -/
theorem mersenneOmega_1365 : mersenneOmega 1365 = 12 := by
  have h : orderOf (2 : ZMod 1365) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  rw [mersenneOmega, h]
  decide

/-- Condition (etar) for `n`, in terms of `s_1^- = ∏ r_i` and `s_1^+ = ∏ q_i` (odd squarefree):
`s_1^- = 1` or `∏ η_n(r_i) = (-1)^{(s_1^- - 1)/2}`, and `∏ η_n(q_i) = (-1)^{(s_1^+ + 1)/2}`,
where `η_n(p) = (M_n | p)`. For squarefree `s` the product `∏_{p ∣ s} η_n(p)` is the Jacobi
symbol `(M_n | s)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7, condition (etar). -/
def MersenneEtaCondition (sm sp n : ℕ) : Prop :=
  (sm = 1 ∨ jacobiSym (mersenne n) sm = (-1) ^ ((sm - 1) / 2)) ∧
    jacobiSym (mersenne n) sp = (-1) ^ ((sp + 1) / 2)

/-- For `s_1 = 37` (`s_1^- = 35`, `s_1^+ = 39`), condition (etar) holds for `n = 7` and fails for
`n = 1`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example `s_1 = 37`, `𝒜(37) = {7}`). -/
theorem mersenneEtaCondition_37 :
    MersenneEtaCondition 35 39 7 ∧ ¬ MersenneEtaCondition 35 39 1 := by
  norm_num [MersenneEtaCondition, mersenne]

/-- Let `s_1 ≥ 3` be an acceptable seed for `M_n` (`n ≥ 3`): `M_n` is prime iff
`M_n ∣ s_{n-1}`. Then there are infinitely many acceptable seeds `S_1 ≥ 3` for `M_n` with
`S_1^- = s_1^-` and `S_1^+ = s_1^+`, where `s^- = (s - 2)^*`, `s^+ = (s + 2)^*`. Seeds are
taken `≥ 3` (the paper's seeds are nonnegative and `s^∓` needs `s ± 2 > 0`).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 10. -/
public theorem_wanted infinite_acceptableSeeds_same_parts {n : ℕ} (h3 : 3 ≤ n) (s₁ : ℤ)
    (hs₁ : 3 ≤ s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hacc : (mersenne n).Prime ↔
      (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] s₁) :
    {S : ℤ | 3 ≤ S ∧ IsOddSquarefreePart (S - 2) sm ∧ IsOddSquarefreePart (S + 2) sp ∧
      ((mersenne n).Prime ↔ (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] S)}.Infinite

/-- For coprime odd `m_1`, `m_2`, the order of `2` modulo `m_1 m_2` is the lcm of the orders
modulo `m_1` and `m_2`. The printed `lcm(ω(m_1)ω(m_2))` is read as `lcm(ω(m_1), ω(m_2))` (the
product reading fails: `ω(15) = 4`, `ω(3)ω(5) = 8`); `m_i` natural.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Proposition 11. -/
public theorem_wanted orderOf_two_mul_coprime {m₁ m₂ : ℕ} (h₁ : Odd m₁) (h₂ : Odd m₂)
    (hc : m₁.Coprime m₂) :
    orderOf (2 : ZMod (m₁ * m₂)) =
      Nat.lcm (orderOf (2 : ZMod m₁)) (orderOf (2 : ZMod m₂))

/-- Let `p` be one of the primes `r_i`, `q_i` of `s_1^- s_1^+`. If `η_n(p) = (M_n | p) = 0`, then
`gcd(n, Ω) > 1` with `Ω = Ω(s_1^- s_1^+)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Proposition 12. -/
public theorem_wanted one_lt_gcd_mersenneOmega_of_legendreSym_eq_zero (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (p : ℕ) [Fact p.Prime] (hp : p ∣ sm * sp) (n : ℕ)
    (h : legendreSym p (mersenne n) = 0) :
    1 < Nat.gcd n (mersenneOmega (sm * sp))

/-- If `s_1^- ≡ -1 (mod 4)`, then condition (etar) fails for some `n ∈ ℛ(Ω)`, the reduced residues
`1 ≤ n < Ω` with `gcd(n, Ω) = 1`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 13. -/
public theorem_wanted exists_not_mersenneEtaCondition_of_minus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sm % 4 = 3) :
    ∃ n, 1 ≤ n ∧ n < mersenneOmega (sm * sp) ∧ n.Coprime (mersenneOmega (sm * sp)) ∧
      ¬ MersenneEtaCondition sm sp n

/-- If `s_1^+ ≡ 1 (mod 4)`, then condition (etar) fails for some `n ∈ ℛ(Ω)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 14. -/
public theorem_wanted exists_not_mersenneEtaCondition_of_plus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sp % 4 = 1) :
    ∃ n, 1 ≤ n ∧ n < mersenneOmega (sm * sp) ∧ n.Coprime (mersenneOmega (sm * sp)) ∧
      ¬ MersenneEtaCondition sm sp n

/-- If `q'(s_1) = 1`, i.e. condition (etar) holds for all `φ(Ω)` reduced residues `n` modulo `Ω`,
then `s_1^- ≡ 1 (mod 4)` and `s_1^+ ≡ -1 (mod 4)`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 15. -/
public theorem_wanted minus_mod_four_of_mersenneEtaCondition_all (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hq : {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard =
      Nat.totient (mersenneOmega (sm * sp))) :
    sm % 4 = 1 ∧ sp % 4 = 3

/-- If `s_1` is odd, then `q'(s_1) ≠ 1`: condition (etar) fails for some reduced residue modulo
`Ω`.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Corollary 16. -/
public theorem_wanted mersenneEtaCondition_not_all_of_odd (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (hodd : Odd s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp) :
    {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard ≠
      Nat.totient (mersenneOmega (sm * sp))

end

end MetaMathlibExt
