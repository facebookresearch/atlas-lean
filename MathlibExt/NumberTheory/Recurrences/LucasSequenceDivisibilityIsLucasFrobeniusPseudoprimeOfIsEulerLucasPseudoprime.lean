/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.Recurrences.LucasDiscriminantGcd
public import MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility
public import MathlibExt.NumberTheory.Recurrences.LucasSequenceFirstKind
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import MathlibExt.NumberTheory.Recurrences.LucasCompanionSquare
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # From Euler–Lucas to Frobenius pseudoprimes

This module proves that an Euler–Lucas pseudoprime which is also an Euler
pseudoprime to the base `Q` is a Frobenius pseudoprime
(`isLucasFrobeniusPseudoprime_of_isEulerLucasPseudoprime`). It also holds the
pseudoprime notions of Section 3 of the source that the statement uses: the Lucas
pseudoprime index (`lucasPseudoprimeIndex`), Lucas pseudoprimes
(`IsLucasPseudoprime`), Lucas pseudoprimes of the second kind
(`IsLucasPseudoprimeSecondKind`), Dickson pseudoprimes (`IsDicksonPseudoprime`),
Dickson pseudoprimes of the second kind (`IsDicksonPseudoprimeSecondKind`),
Frobenius pseudoprimes (`IsLucasFrobeniusPseudoprime`), Euler pseudoprimes
(`IsEulerPseudoprime`) and Euler–Lucas pseudoprimes
(`IsEulerLucasPseudoprime`).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.18.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Index of the Lucas pseudoprime congruences.** Let $P, Q$ be integers with $Q \neq 0$ and
$D = P^2 - 4Q$. For a natural number $N$, the index is $N - (D/N)$, where $(D/N)$ is the Jacobi
symbol, replaced by $0$ when this difference is negative. For $N > 1$ the difference is positive.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, congruences (3.1), (3.4). -/
public def lucasPseudoprimeIndex (L : LucasSequenceParams) (N : ℕ) : ℕ :=
  ((N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N).toNat

/-- **Lucas pseudoprimes.** Let $P, Q$ be integers with $Q \neq 0$, let $U_n$ be the Lucas
sequence of $(P, Q)$ and let $D = P^2 - 4Q$. A natural number $N$ is a Lucas pseudoprime with
parameters $P, Q$ if $N$ is odd and composite, $\gcd(N, QD) = 1$ and $N$ divides
$U_{N - (D/N)}$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.1. -/
public def IsLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N)

/-- **Lucas pseudoprimes of the second kind.** Let $P, Q$ be integers with $Q \neq 0$, let $U_n$
be the Lucas sequence of $(P, Q)$ and let $D = P^2 - 4Q$. A natural number $N$ is a Lucas
pseudoprime of the second kind with parameters $P, Q$ if $N$ is odd and composite,
$\gcd(N, QD) = 1$ and $U_N \equiv (D/N) \pmod{N}$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.2. -/
public def IsLucasPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasU L N ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD N]

/-- **Dickson pseudoprimes.** Let $P$ and $Q \ne 0$ be integers with discriminant
$D = P^2 - 4Q$, and let $(V_n)$ be the companion Lucas sequence $V(P, Q)$. A natural number $N$
is a Dickson pseudoprime with parameters $P$ and $Q$ if $N$ is odd, $N > 1$, $N$ is not prime,
$\gcd(N, QD) = 1$, and $V_N \equiv P \pmod N$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.3. -/
public def IsDicksonPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L N ≡ L.p [ZMOD N]

/-- **Dickson pseudoprimes of the second kind.** Let $P$ and $Q \ne 0$ be integers with
discriminant $D = P^2 - 4Q$, and let $(V_n)$ be the companion Lucas sequence $V(P, Q)$. A
natural number $N$ is a Dickson pseudoprime of the second kind with parameters $P$ and $Q$ if
$N$ is odd, $N > 1$, $N$ is not prime, $\gcd(N, QD) = 1$, and
$V_{N - (D/N)} \equiv 2Q^{(1 - (D/N))/2} \pmod N$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.4. -/
public def IsDicksonPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L (lucasPseudoprimeIndex L N) ≡
      2 * L.q ^ ((1 - jacobiSym (L.p ^ 2 - 4 * L.q) N) / 2).toNat [ZMOD N]

/-- **Frobenius pseudoprime for Lucas parameters.** Let $U$ and $V$ be the Lucas sequences with
integer parameters $P$ and $Q \neq 0$, and let $D = P^2 - 4Q$. A natural number $N$ is a
Frobenius pseudoprime with parameters $P, Q$ when $\gcd(N, PQD) = 1$ and $N$ is a Lucas
pseudoprime, a Lucas pseudoprime of the second kind, a Dickson pseudoprime and a Dickson
pseudoprime of the second kind with parameters $P, Q$. Equivalently, $\gcd(N, PQD) = 1$, $N$ is
odd and composite, and, writing $\varepsilon = (D/N)$ for the Jacobi symbol, $N$ satisfies the
congruences $U_{N-\varepsilon} \equiv 0$, $U_N \equiv \varepsilon$, $V_N \equiv P$ and
$V_{N-\varepsilon} \equiv 2Q^{(1-\varepsilon)/2}$ modulo $N$.

This is the notion of the source, not Grantham's Frobenius pseudoprime defined through quotient
rings of polynomials.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.5. -/
public def IsLucasFrobeniusPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧ IsLucasPseudoprime L N ∧
    IsLucasPseudoprimeSecondKind L N ∧ IsDicksonPseudoprime L N ∧
      IsDicksonPseudoprimeSecondKind L N

/-- **Euler pseudoprime.** Let $a$ be an integer. A natural number $N$ is an Euler pseudoprime to
the base $a$ when $N$ is odd and composite, $\gcd(a, N) = 1$, and
$a^{(N-1)/2} \equiv (a/N) \pmod N$, where $(a/N)$ is the Jacobi symbol.

The source states the definition for positive odd $a$ and applies it to the base $Q$ (for
example $Q = -1$ in Remark 3.8); here $a$ is any integer.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.7. -/
public def IsEulerPseudoprime (a : ℤ) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd a N = 1 ∧ a ^ ((N - 1) / 2) ≡ jacobiSym a N [ZMOD N]

/-- **Euler–Lucas pseudoprime.** Let $U$ and $V$ be the Lucas sequences with integer parameters
$P$ and $Q \neq 0$, and let $D = P^2 - 4Q$. A natural number $N$ is an Euler–Lucas pseudoprime
with parameters $P, Q$ when $N$ is odd and composite, $\gcd(N, QD) = 1$, and, writing
$\varepsilon = (D/N)$ for the Jacobi symbol, $N \mid U_{(N-\varepsilon)/2}$ if the Jacobi symbol
$(Q/N)$ equals $1$, and $N \mid V_{(N-\varepsilon)/2}$ if $(Q/N) = -1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.9. -/
public def IsEulerLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (jacobiSym L.q N = 1 → (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N / 2)) ∧
    (jacobiSym L.q N = -1 → (N : ℤ) ∣ lucasV L (lucasPseudoprimeIndex L N / 2))

/-! ### Proof helpers

Doubling formulas for the Lucas sequences and cancellation lemmas for
congruences, used to derive the four Frobenius congruences below. -/

/-- The companion Lucas sequence in terms of the first one:
$V_n = 2U_{n+1} - P U_n$. -/
private theorem lucasV_eq_two_mul_lucasU_succ_sub (L : LucasSequenceParams) (n : ℕ) :
    lucasV L n = 2 * lucasU L (n + 1) - L.p * lucasU L n := by
  have h :=
    MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted.two_mul_lucasU_add
      L n 1
  simp only [lucasU, lucasV] at h
  linear_combination -h

/-- Addition formula $2V_{m+n} = V_m V_n + D U_m U_n$ for Lucas sequences, where
$D = P^2 - 4Q$ is the discriminant. -/
private theorem two_mul_lucasV_add (L : LucasSequenceParams) (m n : ℕ) :
    2 * lucasV L (m + n) =
      lucasV L m * lucasV L n + (L.p ^ 2 - 4 * L.q) * lucasU L m * lucasU L n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [lucasU, lucasV, Nat.add_zero]; ring
  | one =>
    have h0 := lucasV_eq_two_mul_lucasU_succ_sub L m
    have h1 := lucasV_eq_two_mul_lucasU_succ_sub L (m + 1)
    have hr := lucasU_add_two L m
    simp only [lucasU, lucasV]
    linear_combination 2 * h1 - L.p * h0 + 4 * hr
  | more n ih0 ih1 =>
    have hVm : lucasV L (m + n + 2) =
        L.p * lucasV L (m + n + 1) - L.q * lucasV L (m + n) := rfl
    have hVn : lucasV L (n + 2) =
        L.p * lucasV L (n + 1) - L.q * lucasV L n := rfl
    rw [show m + (n + 1) = m + n + 1 by omega] at ih1
    rw [show m + (n + 2) = m + n + 2 by omega, hVm, hVn, lucasU_add_two L n]
    linear_combination L.p * ih1 - L.q * ih0

/-- Doubling formula $V_{2n} = V_n^2 - 2Q^n$ for Lucas sequences. -/
private theorem lucasV_two_mul (L : LucasSequenceParams) (n : ℕ) :
    lucasV L (2 * n) = lucasV L n ^ 2 - 2 * L.q ^ n := by
  have h := two_mul_lucasV_add L n n
  rw [show n + n = 2 * n by omega] at h
  have hsq := lucasV_sq_eq L n
  have h2 : 2 * lucasV L (2 * n) = 2 * (lucasV L n ^ 2 - 2 * L.q ^ n) := by
    linear_combination h - hsq
  omega

/-- Cancellation of the factor `2` in a congruence modulo an odd number. -/
private theorem modeq_of_two_mul_modeq (N : ℕ) (hN : Odd ((N : ℕ) : ℤ)) (a b : ℤ)
    (h : 2 * a ≡ 2 * b [ZMOD (N : ℤ)]) : a ≡ b [ZMOD (N : ℤ)] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  have hfactor : 2 * b - 2 * a = 2 * (b - a) := by ring
  rw [hfactor] at h
  exact hN.isCoprime_two.dvd_of_dvd_mul_left h

/-- Cancellation of a factor coprime to the modulus in a congruence. -/
private theorem modeq_of_mul_cancel_of_coprime (N : ℕ) (Q : ℤ)
    (hcop : IsCoprime ((N : ℕ) : ℤ) Q) (a b : ℤ)
    (h : Q * a ≡ Q * b [ZMOD (N : ℤ)]) : a ≡ b [ZMOD (N : ℤ)] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  have hfactor : Q * b - Q * a = Q * (b - a) := by ring
  rw [hfactor] at h
  exact hcop.dvd_of_dvd_mul_left h

/-- The Frobenius congruences from Euler–Lucas and Euler data. Let $M = N - (D/N)$
and $E = (1 - (D/N))/2$, where $(D/N)$ is the Jacobi symbol. The Euler–Lucas
divisibilities at $M/2$ and the Euler congruence for $Q$ imply the four
congruences $U_M \equiv 0$, $U_N \equiv (D/N)$, $V_N \equiv P$ and
$V_M \equiv 2Q^E$ modulo $N$. -/
private theorem frobenius_congs_of_euler_data
    (L : LucasSequenceParams) (N M E : ℕ)
    (hM : ((M : ℕ) : ℤ) = (N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N)
    (hE : E = ((1 - jacobiSym (L.p ^ 2 - 4 * L.q) N) / 2).toNat)
    (hNodd : Odd N) (hN1 : 1 < N) (hNprime : ¬N.Prime)
    (hgcdQD : Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (hUhalf : jacobiSym L.q N = 1 → (N : ℤ) ∣ lucasU L (M / 2))
    (hVhalf : jacobiSym L.q N = -1 → (N : ℤ) ∣ lucasV L (M / 2))
    (hgcdQN : Int.gcd L.q N = 1)
    (hEuler : L.q ^ ((N - 1) / 2) ≡ jacobiSym L.q N [ZMOD (N : ℤ)])
    (hcop : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (hδ : jacobiSym (L.p ^ 2 - 4 * L.q) N = 1 ∨
      jacobiSym (L.p ^ 2 - 4 * L.q) N = -1) :
    Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
      (Odd N ∧ 1 < N ∧ ¬N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
        (N : ℤ) ∣ lucasU L M) ∧
      (Odd N ∧ 1 < N ∧ ¬N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
        lucasU L N ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD (N : ℤ)]) ∧
      (Odd N ∧ 1 < N ∧ ¬N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
        lucasV L N ≡ L.p [ZMOD (N : ℤ)]) ∧
      (Odd N ∧ 1 < N ∧ ¬N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
        lucasV L M ≡ 2 * L.q ^ E [ZMOD (N : ℤ)]) := by
  have hlam : jacobiSym L.q N = 1 ∨ jacobiSym L.q N = -1 :=
    jacobiSym.eq_one_or_neg_one hgcdQN
  have hNoddZ : Odd ((N : ℕ) : ℤ) := (Int.odd_natCast N).mpr hNodd
  have hMeven : Even M := by
    have hδodd : Odd (jacobiSym (L.p ^ 2 - 4 * L.q) N) := by
      rcases hδ with h | h
      · rw [h]; exact ⟨0, by norm_num⟩
      · rw [h]; exact ⟨-1, by norm_num⟩
    have hevenZ : Even ((N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N) :=
      hNoddZ.sub_odd hδodd
    rw [← hM] at hevenZ
    exact (Int.even_natCast M).mp hevenZ
  have hM2 : 2 * (M / 2) = M := Nat.two_mul_div_two_of_even hMeven
  have hUd := lucasU_two_mul_eq_lucasU_mul_lucasV L (M / 2)
  rw [hM2] at hUd
  have hVd := lucasV_two_mul L (M / 2)
  rw [hM2] at hVd
  have hKsplit : M / 2 = (N - 1) / 2 + E := by
    rcases hδ with hδ1 | hδ_1
    · have he0 : E = 0 := by rw [hE, hδ1]; decide
      have hK : M / 2 = (N - 1) / 2 := by omega
      rw [he0, add_zero]
      exact hK
    · have he1 : E = 1 := by rw [hE, hδ_1]; decide
      have hK : M / 2 = (N - 1) / 2 + 1 := by omega
      rw [he1]
      exact hK
  have hQpow : L.q ^ (M / 2) ≡ jacobiSym L.q N * L.q ^ E [ZMOD (N : ℤ)] := by
    rw [hKsplit, pow_add]
    exact hEuler.mul (Int.ModEq.refl _)
  have h31 : (N : ℤ) ∣ lucasU L M := by
    rcases hlam with hlam1 | hlamNeg
    · have hU := hUhalf hlam1
      rw [hUd]
      exact dvd_mul_of_dvd_left hU _
    · have hV := hVhalf hlamNeg
      rw [hUd]
      exact dvd_mul_of_dvd_right hV _
  have hUM0 : lucasU L M ≡ 0 [ZMOD (N : ℤ)] := Int.modEq_zero_iff_dvd.mpr h31
  have h34 : lucasV L M ≡ 2 * L.q ^ E [ZMOD (N : ℤ)] := by
    rcases hlam with hlam1 | hlamNeg
    · have hU0 : lucasU L (M / 2) ≡ 0 [ZMOD (N : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (hUhalf hlam1)
      have hU2 : lucasU L (M / 2) ^ 2 ≡ 0 [ZMOD (N : ℤ)] := by
        simpa using hU0.pow 2
      have hDU : (L.p ^ 2 - 4 * L.q) * lucasU L (M / 2) ^ 2 ≡ 0 [ZMOD (N : ℤ)] := by
        simpa using hU2.mul_left _
      have hVsq : lucasV L (M / 2) ^ 2 ≡ 4 * L.q ^ (M / 2) [ZMOD (N : ℤ)] := by
        have hsq := lucasV_sq_eq L (M / 2)
        rw [hsq]
        have hadd := hDU.add (Int.ModEq.refl (4 * L.q ^ (M / 2)))
        simpa using hadd
      have hVM : lucasV L M ≡ 4 * L.q ^ (M / 2) - 2 * L.q ^ (M / 2)
          [ZMOD (N : ℤ)] := by
        rw [hVd]
        exact hVsq.sub (Int.ModEq.refl _)
      have hstep : 4 * L.q ^ (M / 2) - 2 * L.q ^ (M / 2) ≡ 2 * L.q ^ E
          [ZMOD (N : ℤ)] := by
        have h4 := hQpow.mul_left 4
        have h2 := hQpow.mul_left 2
        have hs := h4.sub h2
        rw [hlam1] at hs
        have hring : 4 * ((1 : ℤ) * L.q ^ E) - 2 * (1 * L.q ^ E) = 2 * L.q ^ E := by
          ring
        rw [hring] at hs
        exact hs
      exact hVM.trans hstep
    · have hV0 : lucasV L (M / 2) ≡ 0 [ZMOD (N : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (hVhalf hlamNeg)
      have hVsq0 : lucasV L (M / 2) ^ 2 ≡ 0 [ZMOD (N : ℤ)] := by
        simpa using hV0.pow 2
      have hVM : lucasV L M ≡ 0 - 2 * L.q ^ (M / 2) [ZMOD (N : ℤ)] := by
        rw [hVd]
        exact hVsq0.sub (Int.ModEq.refl _)
      have hstep : (0 : ℤ) - 2 * L.q ^ (M / 2) ≡ 2 * L.q ^ E [ZMOD (N : ℤ)] := by
        have h2 := hQpow.mul_left 2
        have hs := (Int.ModEq.refl (0 : ℤ)).sub h2
        rw [hlamNeg] at hs
        have hring : (0 : ℤ) - 2 * ((-1) * L.q ^ E) = 2 * L.q ^ E := by ring
        rw [hring] at hs
        exact hs
      exact hVM.trans hstep
  have hU1 : lucasU L (M + 1) ≡ L.q ^ E [ZMOD (N : ℤ)] := by
    have h4a :=
      MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted.two_mul_lucasU_add
        L M 1
    simp only [lucasU, lucasV] at h4a
    have h2U : 2 * lucasU L (M + 1) ≡ 2 * L.q ^ E [ZMOD (N : ℤ)] := by
      rw [h4a]
      have h1 := hUM0.mul (Int.ModEq.refl L.p)
      have h2 := h34.mul (Int.ModEq.refl (1 : ℤ))
      have hs := h1.add h2
      have hring : (0 : ℤ) * L.p + 2 * L.q ^ E * 1 = 2 * L.q ^ E := by ring
      rw [hring] at hs
      exact hs
    exact modeq_of_two_mul_modeq N hNoddZ _ _ h2U
  have hV1 : lucasV L (M + 1) ≡ L.p * L.q ^ E [ZMOD (N : ℤ)] := by
    have h4b := two_mul_lucasV_add L M 1
    simp only [lucasU, lucasV] at h4b
    have h2V : 2 * lucasV L (M + 1) ≡ 2 * (L.p * L.q ^ E) [ZMOD (N : ℤ)] := by
      rw [h4b]
      have h1 := h34.mul (Int.ModEq.refl L.p)
      have h2a := hUM0.mul_left (L.p ^ 2 - 4 * L.q)
      have h2 := h2a.mul_right 1
      have hs := h1.add h2
      have hring : 2 * L.q ^ E * L.p + (L.p ^ 2 - 4 * L.q) * 0 * 1 =
          2 * (L.p * L.q ^ E) := by
        ring
      rw [hring] at hs
      exact hs
    exact modeq_of_two_mul_modeq N hNoddZ _ _ h2V
  have h32 : lucasU L N ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD (N : ℤ)] := by
    rcases hδ with hδ1 | hδ_1
    · have hNM : N = M + 1 := by omega
      rw [hδ1]
      have he0 : E = 0 := by rw [hE, hδ1]; decide
      rw [he0, ← hNM] at hU1
      simpa using hU1
    · have hM1 : 1 ≤ M := by omega
      have hNM : N = M - 1 := by omega
      rw [hδ_1]
      have he1 : E = 1 := by rw [hE, hδ_1]; decide
      rw [he1] at hU1
      have hUrec : lucasU L (M + 1) = L.p * lucasU L M - L.q * lucasU L (M - 1) := by
        have h := lucasU_add_two L (M - 1)
        rw [show M - 1 + 2 = M + 1 by omega, show M - 1 + 1 = M by omega] at h
        exact h
      have hEq : L.q * lucasU L (M - 1) = L.p * lucasU L M - lucasU L (M + 1) := by
        linear_combination hUrec
      have hQU : L.q * lucasU L (M - 1) ≡ L.q * (-1) [ZMOD (N : ℤ)] := by
        rw [hEq]
        have h1 := hUM0.mul_left L.p
        have hs := h1.sub hU1
        have hring : L.p * (0 : ℤ) - L.q ^ 1 = L.q * -1 := by ring
        rw [hring] at hs
        exact hs
      have hcopQ : IsCoprime ((N : ℕ) : ℤ) L.q :=
        (Int.isCoprime_iff_gcd_eq_one.mpr hgcdQN).symm
      have hdone := modeq_of_mul_cancel_of_coprime N L.q hcopQ _ _ hQU
      rw [← hNM] at hdone
      exact hdone
  have h33 : lucasV L N ≡ L.p [ZMOD (N : ℤ)] := by
    rcases hδ with hδ1 | hδ_1
    · have hNM : N = M + 1 := by omega
      have he0 : E = 0 := by rw [hE, hδ1]; decide
      rw [he0, ← hNM] at hV1
      simpa using hV1
    · have hM1 : 1 ≤ M := by omega
      have hNM : N = M - 1 := by omega
      have he1 : E = 1 := by rw [hE, hδ_1]; decide
      rw [he1] at hV1
      have hVrec : lucasV L (M + 1) = L.p * lucasV L M - L.q * lucasV L (M - 1) := by
        have h : lucasV L (M - 1 + 2) =
            L.p * lucasV L (M - 1 + 1) - L.q * lucasV L (M - 1) := rfl
        rw [show M - 1 + 2 = M + 1 by omega, show M - 1 + 1 = M by omega] at h
        exact h
      have hEq : L.q * lucasV L (M - 1) = L.p * lucasV L M - lucasV L (M + 1) := by
        linear_combination hVrec
      rw [he1] at h34
      have hQV : L.q * lucasV L (M - 1) ≡ L.q * L.p [ZMOD (N : ℤ)] := by
        rw [hEq]
        have h1 := h34.mul_left L.p
        have hs := h1.sub hV1
        have hring : L.p * (2 * L.q ^ 1) - L.p * L.q ^ 1 = L.q * L.p := by ring
        rw [hring] at hs
        exact hs
      have hcopQ : IsCoprime ((N : ℕ) : ℤ) L.q :=
        (Int.isCoprime_iff_gcd_eq_one.mpr hgcdQN).symm
      have hdone := modeq_of_mul_cancel_of_coprime N L.q hcopQ _ _ hQV
      rw [← hNM] at hdone
      exact hdone
  exact ⟨hcop, ⟨hNodd, hN1, hNprime, hgcdQD, h31⟩,
    ⟨hNodd, hN1, hNprime, hgcdQD, h32⟩, ⟨hNodd, hN1, hNprime, hgcdQD, h33⟩,
    ⟨hNodd, hN1, hNprime, hgcdQD, h34⟩⟩

/-! ### Statements -/

/-- **From Euler–Lucas to Frobenius pseudoprimes.** Let $P$ and $Q \neq 0$ be integers forming a
nondegenerate Lucas pair, and let $D = P^2 - 4Q$. If $N$ is an Euler–Lucas pseudoprime with
parameters $P, Q$ and an Euler pseudoprime to the base $Q$, and $\gcd(N, PQD) = 1$, then $N$ is a
Frobenius pseudoprime with parameters $P, Q$.

The base $Q$ is any nonzero integer; the source's Definition 3.7 is stated for positive odd bases.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.18 (`integers-2025-A107-thm-3-18`). -/
public theorem isLucasFrobeniusPseudoprime_of_isEulerLucasPseudoprime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hEL : IsEulerLucasPseudoprime L N) (hE : IsEulerPseudoprime L.q N)
    (hcop : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1) :
    IsLucasFrobeniusPseudoprime L N := by
  have _ := hL
  obtain ⟨hNodd, hN1, hNprime, hgcdQD, hUhalf, hVhalf⟩ := hEL
  obtain ⟨-, -, -, hgcdQN, hEuler⟩ := hE
  have hgcdND : Int.gcd N (L.p ^ 2 - 4 * L.q) = 1 := by
    have hDvd : (L.p ^ 2 - 4 * L.q) ∣ L.p * L.q * (L.p ^ 2 - 4 * L.q) :=
      ⟨L.p * L.q, by ring⟩
    have h := Int.gcd_dvd_gcd_of_dvd_right (N : ℤ) hDvd
    rw [hcop] at h
    exact Nat.dvd_one.mp h
  have hδ : jacobiSym (L.p ^ 2 - 4 * L.q) N = 1 ∨
      jacobiSym (L.p ^ 2 - 4 * L.q) N = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_comm]
    exact hgcdND
  have hnonneg : 0 ≤ (N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N := by
    rcases hδ with h | h <;> omega
  have hM : ((lucasPseudoprimeIndex L N : ℕ) : ℤ) =
      (N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N :=
    Int.toNat_of_nonneg hnonneg
  have h := frobenius_congs_of_euler_data L N (lucasPseudoprimeIndex L N)
    (((1 - jacobiSym (L.p ^ 2 - 4 * L.q) N) / 2).toNat) hM rfl hNodd hN1 hNprime
    hgcdQD hUhalf hVhalf hgcdQN hEuler hcop hδ
  exact h

end

end MetaMathlibExt
