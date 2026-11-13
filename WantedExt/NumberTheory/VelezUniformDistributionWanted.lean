/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Subsequences of a second-order linear recurrence are again
second-order: if `w (n + 2) = P * w (n + 1) - Q * w n` for all `n`,
then for positive `t` and any shift `r` the subsequence
`n ↦ w (t * n + r)` satisfies the recurrence with coefficients
`V_t` and `Q ^ t`, and the discriminants are related by
`V_t ^ 2 - 4 * Q ^ t = U_t ^ 2 * (P ^ 2 - 4 * Q)`, where `U` and `V`
are the Lucas sequences `lucasU` and `lucasV` for the parameters.

The paper writes the recurrence as `w_{n+2} = a w_{n+1} + b w_n`
with subsequence coefficients `a' = v_t(a, b)` and
`b' = (-1) ^ (t + 1) * b ^ t` and discriminant
`D(a, b) = a ^ 2 + 4 * b`; this is the same statement in the
repository convention `P = a`, `Q = -b` (so `b' = -Q ^ t` in the
`signed` position). The paper's sentence identifying the new
characteristic roots as `α ^ t` and `β ^ t` is not formalized.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.4 (`integers-2025-A1-thm-2-4`). -/
public theorem_wanted subsequence_secondOrderRecurrence
    (params : LucasSequenceParams) (w : ℕ → ℤ)
    (hw : ∀ n : ℕ, w (n + 2) = params.p * w (n + 1) - params.q * w n)
    (t r : ℕ) (ht : 0 < t) :
    (∀ n : ℕ, w (t * (n + 2) + r)
      = lucasV params t * w (t * (n + 1) + r)
        - params.q ^ t * w (t * n + r)) ∧
    (lucasV params t) ^ 2 - 4 * params.q ^ t
      = (lucasU params t) ^ 2 * (params.p ^ 2 - 4 * params.q)

/-- The period length `λ_w(m)`: the least positive `ℓ` with `w (n + ℓ) ≡ w n (mod m)` for all
`n` (`0` if there is none).

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1. -/
public noncomputable def recurrencePeriodMod (w : ℕ → ℤ) (m : ℕ) : ℕ :=
  sInf {ℓ | 0 < ℓ ∧ ∀ n : ℕ, w (n + ℓ) ≡ w n [ZMOD m]}

/-- The restricted period `h_w(m)`: the least positive `f` such that
`w (n + f) ≡ M * w n (mod m)` for all `n`, for some multiplier `M` coprime to `m` (`0` if there
is none).

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1, (1.1). -/
public noncomputable def recurrenceRestrictedPeriodMod (w : ℕ → ℤ) (m : ℕ) : ℕ :=
  sInf {f | 0 < f ∧ ∃ M : ℤ, IsCoprime M m ∧ ∀ n : ℕ, w (n + f) ≡ M * w n [ZMOD m]}

/-- The number of `n < L` with `w n ≡ x (mod m)`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1. -/
public def residueCount (w : ℕ → ℤ) (m L : ℕ) (x : ℤ) : ℕ :=
  ((Finset.range L).filter fun n => w n ≡ x [ZMOD m]).card

/-- `w` is uniformly distributed modulo `m`: it is purely periodic modulo `m` and each residue
modulo `m` appears exactly the same number `E = λ_w(m)/m ≥ 1` of times in a least period.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1. -/
public def IsUniformlyDistributedMod (w : ℕ → ℤ) (m : ℕ) : Prop :=
  0 < recurrencePeriodMod w m ∧
    ∀ x : ℤ, m * residueCount w m (recurrencePeriodMod w m) x = recurrencePeriodMod w m

/-- `w` is regular modulo `p` (`p`-regular): `w₀ w₂ - w₁² ≢ 0 (mod p)`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 2. -/
public def IsRegularMod (w : ℕ → ℤ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ w 0 * w 2 - w 1 ^ 2

/-- A constant sequence has period length `1` modulo every `m`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1. -/
public theorem recurrencePeriodMod_const (c : ℤ) (m : ℕ) :
    recurrencePeriodMod (fun _ => c) m = 1 := by
  have hmem : 1 ∈ {ℓ | 0 < ℓ ∧ ∀ n : ℕ, (fun _ : ℕ => c) (n + ℓ) ≡ (fun _ : ℕ => c) n [ZMOD m]} :=
    ⟨one_pos, fun _ => Int.ModEq.refl _⟩
  apply le_antisymm (Nat.sInf_le hmem)
  refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
  rcases Nat.sInf_eq_zero.mp h with h0 | h0
  · exact lt_irrefl 0 h0.1
  · exact (Set.eq_empty_iff_forall_notMem.mp h0) 1 hmem

/-- A constant sequence has restricted period `1` modulo every `m` (multiplier `1`).

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Section 1. -/
public theorem recurrenceRestrictedPeriodMod_const (c : ℤ) (m : ℕ) :
    recurrenceRestrictedPeriodMod (fun _ => c) m = 1 := by
  have hmem : 1 ∈ {f | 0 < f ∧ ∃ M : ℤ, IsCoprime M m ∧
      ∀ n : ℕ, (fun _ : ℕ => c) (n + f) ≡ M * (fun _ : ℕ => c) n [ZMOD m]} :=
    ⟨one_pos, 1, isCoprime_one_left, fun _ => by simp [Int.ModEq.refl]⟩
  apply le_antisymm (Nat.sInf_le hmem)
  refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
  rcases Nat.sInf_eq_zero.mp h with h0 | h0
  · exact lt_irrefl 0 h0.1
  · exact (Set.eq_empty_iff_forall_notMem.mp h0) 1 hmem

/-- **Theorem 1.3.** Let `w(a, b)` be uniformly distributed modulo `pᵉ` (`e ≥ 1`,
`p ∤ b`) with `λ_w(pᵉ) = pᵉ E`. For `g > 0` coprime to `p`, `d = gcd(g, E)`, `r = E/d`, and any
`s ≥ 0`, each residue modulo `pᵉ` appears exactly `r` times among `w_{s + n g}`,
`0 ≤ n < pᵉ r`. Further, if `p ≥ 3` then `a ≢ 0 (mod p)` and `E = ord_p(a/2)`, while `E = 1` if
`p = 2`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 1.3 (`integers-2025-A1-thm-1-3`). -/
public theorem_wanted uniformlyDistributed_subsequence_residueCount
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p e : ℕ}
        [Fact p.Prime] (he : 1 ≤ e)
    (hb : ¬ (p : ℤ) ∣ b) (hud : IsUniformlyDistributedMod w (p ^ e)) {g : ℕ} (hg : 0 < g)
    (hgp : Nat.Coprime g p) (s : ℕ) :
    let E := recurrencePeriodMod w (p ^ e) / p ^ e
    let r := E / Nat.gcd g E
    (∀ x : ℤ, residueCount (fun n => w (s + n * g)) (p ^ e) (p ^ e * r) x = r) ∧
      (3 ≤ p → ¬ (p : ℤ) ∣ a ∧ E = orderOf ((a : ZMod p) * (2 : ZMod p)⁻¹)) ∧
      (p = 2 → E = 1)

/-- **Theorem 1.1** (Vélez). Let `w(a, b)` be uniformly distributed modulo `pᵉ` (`e ≥ 1`,
`p ∤ b`) with `λ_w(pᵉ) = pᵉ E`. For every `s ≥ 0`, each residue modulo `pᵉ` appears exactly once
among `w_{s + n E}`, `0 ≤ n < pᵉ`. Moreover, if `p ≥ 3` then `a ≢ 0 (mod p)` and
`E = ord_p(a/2)`, while `E = 1` if `p = 2`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 1.1, quoting Vélez (`integers-2025-A1-thm-1-1`). -/
public theorem_wanted velez_uniformlyDistributed_subsequence
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p e : ℕ}
        [Fact p.Prime] (he : 1 ≤ e)
    (hb : ¬ (p : ℤ) ∣ b) (hud : IsUniformlyDistributedMod w (p ^ e)) (s : ℕ) :
    let E := recurrencePeriodMod w (p ^ e) / p ^ e
    (∀ x : ℤ, residueCount (fun n => w (s + n * E)) (p ^ e) (p ^ e) x = 1) ∧
      (3 ≤ p → ¬ (p : ℤ) ∣ a ∧ E = orderOf ((a : ZMod p) * (2 : ZMod p)⁻¹)) ∧
      (p = 2 → E = 1)

/-- **Theorem 1.2** (Bumby). Let `w(a, b)` be uniformly distributed modulo `p` (`p ∤ b`) with
`λ_w(p) = p E`. If `c` is a multiple of `E` with `gcd(c, p) = 1`, then for every `s ≥ 0` the
terms `w_s, w_{s+c}, …, w_{s+(p-1)c}` are congruent modulo `p` to an arithmetic progression with
nonzero difference.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 1.2, quoting Bumby (`integers-2025-A1-thm-1-2`). -/
public theorem_wanted bumby_uniformlyDistributed_arithmeticProgression
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hb : ¬ (p : ℤ) ∣ b)
    (hud : IsUniformlyDistributedMod w p) {c : ℕ} (hc : recurrencePeriodMod w p / p ∣ c)
    (hcp : Nat.Coprime c p) (s : ℕ) :
    ∃ A B : ℤ, ¬ (p : ℤ) ∣ B ∧ ∀ i < p, w (s + i * c) ≡ A + i * B [ZMOD p]

/-- **Theorem 2.3 (i).** With `p ∤ b` and `D = a² + 4b`: `w(a, b)` is uniformly distributed
modulo `p` iff `p ∣ D` and `w` is `p`-regular. In this case `h(p) = p`; if `p ≥ 3` then
`a ≢ 0 (mod p)` and `E(p) = λ(p)/p = ord_p(a/2)`; if `p = 2` then `E(p) = 1`; and `E(p) ∣ p - 1`.
(The equalities `E(p) = ord_p(M_w(p)) = ord_p(α)` and `α ≡ β ≡ a/2` are not formalized.)

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.3 (i) (`integers-2025-A1-thm-2-3`). -/
public theorem_wanted uniformlyDistributedMod_prime_iff
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hb : ¬ (p : ℤ) ∣ b) :
    let E := recurrencePeriodMod w p / p
    (IsUniformlyDistributedMod w p ↔ (p : ℤ) ∣ a ^ 2 + 4 * b ∧ IsRegularMod w p) ∧
      (IsUniformlyDistributedMod w p →
        recurrenceRestrictedPeriodMod w p = p ∧
          (3 ≤ p → ¬ (p : ℤ) ∣ a ∧ E = orderOf ((a : ZMod p) * (2 : ZMod p)⁻¹)) ∧
          (p = 2 → E = 1) ∧ E ∣ p - 1)

/-- **Theorem 2.3 (ii).** For `p ≥ 5`, `e ≥ 2`, `p ∤ b`: `w(a, b)` is uniformly distributed
modulo `pᵉ` iff `p ∣ D` and `w` is `p`-regular. In this case `a ≢ 0 (mod p)`, `h(pᵉ) = pᵉ`,
`E(p) = λ(p)/p = ord_p(a/2)`, `λ(pᵉ) = pᵉ E(p)`, and `E(p) ∣ p - 1`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.3 (ii) (`integers-2025-A1-thm-2-3`). -/
public theorem_wanted uniformlyDistributedMod_prime_pow_iff_of_five_le
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p e : ℕ}
        [Fact p.Prime] (hp : 5 ≤ p) (he : 2 ≤ e)
    (hb : ¬ (p : ℤ) ∣ b) :
    let E := recurrencePeriodMod w p / p
    (IsUniformlyDistributedMod w (p ^ e) ↔ (p : ℤ) ∣ a ^ 2 + 4 * b ∧ IsRegularMod w p) ∧
      (IsUniformlyDistributedMod w (p ^ e) →
        ¬ (p : ℤ) ∣ a ∧ recurrenceRestrictedPeriodMod w (p ^ e) = p ^ e ∧
          E = orderOf ((a : ZMod p) * (2 : ZMod p)⁻¹) ∧
          recurrencePeriodMod w (p ^ e) = p ^ e * E ∧ E ∣ p - 1)

/-- **Theorem 2.3 (iii).** For `e ≥ 2` and `3 ∤ b`: `w(a, b)` is uniformly distributed modulo
`3ᵉ` iff `3 ∣ D`, `D ≢ 6 (mod 9)`, and `w` is `3`-regular. In this case `a ≢ 0 (mod 3)`,
`h(3ᵉ) = 3ᵉ`, `E(3) = λ(3)/3 = ord_3(a/2)`, `λ(3ᵉ) = 3ᵉ E(3)`, and `E(3) ∣ 2`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.3 (iii) (`integers-2025-A1-thm-2-3`). -/
public theorem_wanted uniformlyDistributedMod_three_pow_iff
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {e : ℕ} (he : 2 ≤ e)
        (hb : ¬ (3 : ℤ) ∣ b) :
    let E := recurrencePeriodMod w 3 / 3
    (IsUniformlyDistributedMod w (3 ^ e) ↔
        (3 : ℤ) ∣ a ^ 2 + 4 * b ∧ ¬ a ^ 2 + 4 * b ≡ 6 [ZMOD 9] ∧ IsRegularMod w 3) ∧
      (IsUniformlyDistributedMod w (3 ^ e) →
        ¬ (3 : ℤ) ∣ a ∧ recurrenceRestrictedPeriodMod w (3 ^ e) = 3 ^ e ∧
          E = orderOf ((a : ZMod 3) * (2 : ZMod 3)⁻¹) ∧
          recurrencePeriodMod w (3 ^ e) = 3 ^ e * E ∧ E ∣ 2)

/-- **Theorem 2.3 (iv).** For `e ≥ 2` and `b` odd: `w(a, b)` is uniformly distributed modulo
`2ᵉ` iff `2 ∣ D`, `a ≡ 2 (mod 4)`, `b ≡ 3 (mod 4)`, `w₀ ≢ w₁ (mod 2)`, and `w` is `2`-regular.
In this case `h(2ᵉ) = 2ᵉ`, `E(2) = λ(2)/2 = 1`, and `λ(2ᵉ) = 2ᵉ`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.3 (iv) (`integers-2025-A1-thm-2-3`). -/
public theorem_wanted uniformlyDistributedMod_two_pow_iff
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {e : ℕ} (he : 2 ≤ e)
        (hb : ¬ (2 : ℤ) ∣ b) :
    (IsUniformlyDistributedMod w (2 ^ e) ↔
        (2 : ℤ) ∣ a ^ 2 + 4 * b ∧ a ≡ 2 [ZMOD 4] ∧ b ≡ 3 [ZMOD 4] ∧ ¬ w 0 ≡ w 1 [ZMOD 2] ∧
          IsRegularMod w 2) ∧
      (IsUniformlyDistributedMod w (2 ^ e) →
        recurrenceRestrictedPeriodMod w (2 ^ e) = 2 ^ e ∧ recurrencePeriodMod w 2 / 2 = 1 ∧
          recurrencePeriodMod w (2 ^ e) = 2 ^ e)

/-- **Theorem 2.3 (v), second sentence.** If `b` is odd and `2 ∣ D`, then `a` is even and `w` is
`2`-regular iff `w₀ ≢ w₁ (mod 2)`. (The first sentence, for odd `p`, is false as printed and is
not formalized; see the audit row.)

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.3 (v) (`integers-2025-A1-thm-2-3`). -/
public theorem_wanted isRegularMod_two_iff_of_two_dvd_discr
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) (hb : ¬ (2 : ℤ) ∣ b)
        (hD : (2 : ℤ) ∣ a ^ 2 + 4 * b) :
    (2 : ℤ) ∣ a ∧ (IsRegularMod w 2 ↔ ¬ w 0 ≡ w 1 [ZMOD 2])

/-- **Lemma 2.2 (i).** If `p ∤ b` and `w₀ ≡ 0 (mod p)`, then `w` is `p`-irregular iff
`w₁ ≡ 0 (mod p)`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (i) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted not_isRegularMod_iff_of_dvd_zero
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hb : ¬ (p : ℤ) ∣ b) (h0 : (p : ℤ) ∣ w 0) :
    ¬ IsRegularMod w p ↔ (p : ℤ) ∣ w 1

/-- **Lemma 2.2 (ii).** If `p` is odd, `p ∤ b`, `p ∤ gcd(w₀, w₁)`, and `(D/p) = -1`, then `w`
is `p`-regular.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (ii) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted isRegularMod_of_legendreSym_eq_neg_one
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b)
    (hw01 : ¬ ((p : ℤ) ∣ w 0 ∧ (p : ℤ) ∣ w 1)) (hD : legendreSym p (a ^ 2 + 4 * b) = -1) :
    IsRegularMod w p

/-- **Lemma 2.2 (iii).** If `p` is odd, `p ∤ b`, `p ∤ gcd(w₀, w₁)`, and `(D/p) = 1`, then the
characteristic roots `α, β` (with `α + β = a`, `αβ = -b`) lie in `ℤ/pℤ`, `αβ ≠ 0`, `w` is
`p`-irregular iff `w₁ ≡ α w₀` or `w₁ ≡ β w₀`, and `w₁ ≡ α w₀` implies `w_n ≡ αⁿ w₀` for all `n`
(the `β` case is the same statement with the roots swapped).

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (iii) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted not_isRegularMod_iff_of_legendreSym_eq_one
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b)
    (hw01 : ¬ ((p : ℤ) ∣ w 0 ∧ (p : ℤ) ∣ w 1)) (hD : legendreSym p (a ^ 2 + 4 * b) = 1) :
    (∃ α β : ZMod p, α + β = a ∧ α * β = -b) ∧
      ∀ α β : ZMod p, α + β = a → α * β = -b →
        α * β ≠ 0 ∧
          (¬ IsRegularMod w p ↔ (w 1 : ZMod p) = α * w 0 ∨ (w 1 : ZMod p) = β * w 0) ∧
          ((w 1 : ZMod p) = α * w 0 → ∀ n : ℕ, (w n : ZMod p) = α ^ n * w 0)

/-- **Lemma 2.2 (iv).** If `p` is odd, `p ∤ b`, `p ∤ gcd(w₀, w₁)`, and `p ∣ D`, then
`a ≢ 0 (mod p)`, `w` is `p`-irregular iff `w₁ ≡ (a/2) w₀ (mod p)`, and in that case
`w_n ≡ (a/2)ⁿ w₀` for all `n`. (The congruence `α ≡ β ≡ a/2` for the characteristic roots is
not formalized.)

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (iv) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted not_isRegularMod_iff_of_dvd_discr
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hp2 : p ≠ 2) (hb : ¬ (p : ℤ) ∣ b)
    (hw01 : ¬ ((p : ℤ) ∣ w 0 ∧ (p : ℤ) ∣ w 1)) (hD : (p : ℤ) ∣ a ^ 2 + 4 * b) :
    ¬ (p : ℤ) ∣ a ∧
      (¬ IsRegularMod w p ↔ (w 1 : ZMod p) = (a : ZMod p) * (2 : ZMod p)⁻¹ * w 0) ∧
      (¬ IsRegularMod w p →
        ∀ n : ℕ, (w n : ZMod p) = ((a : ZMod p) * (2 : ZMod p)⁻¹) ^ n * w 0)

/-- **Lemma 2.2 (v).** If `b` is odd and `w₀, w₁` are not both even, then `w` is `2`-irregular
iff `a` is even, `b` is odd and `w₀, w₁` are odd; in that case `2 ∣ D` and every `w_n` is odd.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (v) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted not_isRegularMod_two_iff
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) (hb : ¬ (2 : ℤ) ∣ b)
        (hw01 : ¬ ((2 : ℤ) ∣ w 0 ∧ (2 : ℤ) ∣ w 1)) :
    (¬ IsRegularMod w 2 ↔ (2 : ℤ) ∣ a ∧ ¬ (2 : ℤ) ∣ b ∧ ¬ (2 : ℤ) ∣ w 0 ∧ ¬ (2 : ℤ) ∣ w 1) ∧
      (¬ IsRegularMod w 2 → (2 : ℤ) ∣ a ^ 2 + 4 * b ∧ ∀ n : ℕ, ¬ (2 : ℤ) ∣ w n)

/-- **Lemma 2.2 (vi).** If `p ∤ b` and `w` is `p`-irregular, then either `p ∣ w_n` for all `n`
or `p ∤ w_n` for all `n`.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (vi) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted dvd_all_or_not_dvd_all_of_not_isRegularMod
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {p : ℕ} [Fact p.Prime]
        (hb : ¬ (p : ℤ) ∣ b) (hirr : ¬ IsRegularMod w p) :
    (∀ n : ℕ, (p : ℤ) ∣ w n) ∨ ∀ n : ℕ, ¬ (p : ℤ) ∣ w n

/-- **Lemma 2.2 (vii)**, without the multiplier. If `p ∤ b` and two recurrences `w, w'` with the
same parameters `(a, b)` are both `p`-regular, then for every `e ≥ 1` they have the same period
length `λ(pᵉ)` and the same restricted period `h(pᵉ)`, hence the same `E(pᵉ) = λ(pᵉ)/h(pᵉ)`.
(The congruence `M_w(pᵉ) ≡ M_{w'}(pᵉ)` of multipliers is not formalized.)

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Lemma 2.2 (vii) (`integers-2025-A1-lem-2-2`). -/
public theorem_wanted recurrencePeriodMod_eq_of_isRegularMod
    {a b : ℤ} {w : ℕ → ℤ} (hw : ∀ n : ℕ, w (n + 2) = a * w (n + 1) + b * w n) {w' : ℕ → ℤ}
        (hw' : ∀ n : ℕ, w' (n + 2) = a * w' (n + 1) + b * w' n)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hb : ¬ (p : ℤ) ∣ b)
    (hreg : IsRegularMod w p) (hreg' : IsRegularMod w' p) :
    recurrencePeriodMod w (p ^ e) = recurrencePeriodMod w' (p ^ e) ∧
      recurrenceRestrictedPeriodMod w (p ^ e) = recurrenceRestrictedPeriodMod w' (p ^ e)

end

end MetaMathlibExt
