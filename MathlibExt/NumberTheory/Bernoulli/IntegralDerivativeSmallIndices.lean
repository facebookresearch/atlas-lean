/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Bernoulli.DerivativeDenominator
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff

/-!
# Small indices of Bernoulli polynomials with integral derivative

If $n \ge 1$ and $B_n'(x)$ has integer coefficients, then $n+1$ is prime. For
$n \le 10^7$, the index must lie in $\{1,2,4,6,10,12,28,30,36,60\}$.

The primality assertion uses the integral-derivative criterion (Theorem 9). For the
bound, the paper cites a computation of the large-prime part; here we check a finite
sieve using the coprime part instead. For each prime $p$, either $p$ divides the index
or its base-$p$ digit sum is less than $p$. We enumerate short expansions with small
digit sums in bases $2,3,5,7$, cover the remaining multiples of $210$ in blocks, and
check the condition for the primes through $23$.

## References

* Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
  Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, pp. 1–11,
  Theorem 5, Theorem 9 and equation (13).
* Bernd C. Kellner, *On a product of certain primes*, Journal of Number Theory 179 (2017),
  pp. 126–141, Figure B1, the computation cited in the proof of Theorem 5(ii).
* Bernd C. Kellner and Jonathan Sondow, *On Carmichael and polygonal numbers, Bernoulli
  polynomials, and sums of base-p digits*, INTEGERS 21 (2021), Article A52, pp. 1–21,
  Theorem 3.1, the denominator formula underlying the integral-derivative criterion.
-/

namespace MetaMathlibExt

/-- Values of base-`p` expansions with `places` digits and total digit budget `budget`.
The enumeration allows leading zeros; in the sieve `budget < p`. -/
private def digitCandidates (p : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | places + 1, budget =>
    (List.range (budget + 1)).flatMap fun d =>
      (digitCandidates p places (budget - d)).map fun m => d + p * m

private theorem ofDigits_mem_digitCandidates (p : ℕ) (ds : List ℕ) {places budget : ℕ}
    (hl : ds.length ≤ places) (hs : ds.sum ≤ budget) :
    Nat.ofDigits p ds ∈ digitCandidates p places budget := by
  induction places generalizing ds budget with
  | zero =>
    have hnil : ds = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    simp [hnil, digitCandidates]
  | succ places ih =>
    cases ds with
    | nil =>
      have ht : 0 ∈ digitCandidates p places budget := by
        simpa only [Nat.ofDigits_nil] using ih (ds := []) (budget := budget) (by simp) (by simp)
      rw [digitCandidates, List.mem_flatMap]
      refine ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), List.mem_map.mpr ⟨0, ht, ?_⟩⟩
      simp
    | cons d ds =>
      simp only [List.length_cons, List.sum_cons] at hl hs
      rw [digitCandidates, List.mem_flatMap]
      refine ⟨d, List.mem_range.mpr (by omega), List.mem_map.mpr ?_⟩
      exact ⟨_, ih ds (by omega) (by omega), by rw [Nat.ofDigits_cons]⟩

private def digitSearchBases : List (ℕ × ℕ) := [(2, 24), (3, 15), (5, 11), (7, 9)]

-- Check the larger primes first: their expansions are shorter, and the multiples of 210
-- already satisfy the conditions at 2, 3, 5 and 7.
private def screeningPrimes : List ℕ := [23, 19, 17, 13, 11, 7, 5, 3, 2]

-- If 2, 3, 5 and 7 all divide the index, it is a multiple of 210. The 187 blocks of
-- 256 consecutive multiples cover the cutoff while keeping kernel reductions separate.
private def multipleBlock (block : ℕ) : List ℕ :=
  (List.range 256).map fun i => 210 * (256 * block + i)

private def candidateBlocks : List (List ℕ) :=
  (digitSearchBases.map fun (p, places) => digitCandidates p places (p - 1)) ++
    (List.range 187).map multipleBlock

private theorem exists_mem_candidateBlocks {n : ℕ} (hle : n ≤ 10 ^ 7)
    (h : ∀ p ∈ screeningPrimes, p ∣ n ∨ (p.digits n).sum < p) :
    ∃ block ∈ candidateBlocks, n ∈ block := by
  by_cases hdvd : ∀ b ∈ digitSearchBases, b.1 ∣ n
  · have h6 : 6 ∣ n := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd
      (hdvd (2, 24) (by decide)) (hdvd (3, 15) (by decide))
    have h30 : 30 ∣ n := (by decide : Nat.Coprime 6 5).mul_dvd_of_dvd_of_dvd
      h6 (hdvd (5, 11) (by decide))
    have h210 : 210 ∣ n := (by decide : Nat.Coprime 30 7).mul_dvd_of_dvd_of_dvd
      h30 (hdvd (7, 9) (by decide))
    obtain ⟨m, rfl⟩ := h210
    refine ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨m / 256, ?_, rfl⟩), ?_⟩
    · exact List.mem_range.mpr (by omega)
    · exact List.mem_map.mpr ⟨m % 256, List.mem_range.mpr (Nat.mod_lt _ (by decide)), by omega⟩
  · simp only [not_forall] at hdvd
    obtain ⟨⟨p, places⟩, hbase, hndvd⟩ := hdvd
    have hdata : digitSearchBases.all (fun (p, places) =>
        decide (1 < p ∧ (10 : ℕ) ^ 7 < p ^ places ∧ p ∈ screeningPrimes)) = true := by
      decide +kernel
    obtain ⟨hp, hpow, hscreen⟩ := of_decide_eq_true (List.all_eq_true.mp hdata _ hbase)
    have hs := (h p hscreen).resolve_left hndvd
    refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨(p, places), hbase, rfl⟩), ?_⟩
    rw [← Nat.ofDigits_digits p n]
    exact ofDigits_mem_digitCandidates p _
      ((Nat.digits_length_le_iff hp n).mpr (hle.trans_lt hpow)) (by omega)

private def knownIndices : List ℕ := [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]

-- Use structural recursion and stop as soon as a digit exceeds the remaining budget.
private def digitSumAtMost (p : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, n, _ => n == 0
  | places + 1, n, budget =>
    if n = 0 then true else
      decide (n % p ≤ budget) && digitSumAtMost p places (n / p) (budget - n % p)

private theorem digitSumAtMost_iff {p places n budget : ℕ} (hp : 1 < p) (hn : n < p ^ places) :
    digitSumAtMost p places n budget = true ↔ (p.digits n).sum ≤ budget := by
  induction places generalizing n budget with
  | zero =>
    have hn₀ : n = 0 := by simpa using hn
    simp [digitSumAtMost, hn₀]
  | succ places ih =>
    obtain rfl | hn₀ := eq_or_ne n 0
    · simp [digitSumAtMost]
    have hdiv : n / p < p ^ places :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rwa [← pow_succ])
    simp only [digitSumAtMost, hn₀, ite_false, Bool.and_eq_true, decide_eq_true_eq, ih hdiv,
      Nat.digits_def' hp (Nat.pos_of_ne_zero hn₀), List.sum_cons]
    omega

private def passesScreen (n : ℕ) : Bool :=
  screeningPrimes.all fun p => decide (p ∣ n) || digitSumAtMost p 24 n (p - 1)

private def checkBlock (block : List ℕ) : Bool :=
  block.all fun n => !(decide (0 < n ∧ n ≤ 10 ^ 7) && passesScreen n) || knownIndices.contains n

set_option maxHeartbeats 1200000 in
-- The kernel reduces the digit-budget checks on each of the 187 blocks separately.
private theorem sieveCertificate (block : List ℕ) (hblock : block ∈ candidateBlocks) :
    checkBlock block = true := by
  rw [candidateBlocks, List.mem_append] at hblock
  rcases hblock with hbase | hmultiple
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hbase
    simp only [digitSearchBases, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmultiple
    have hi' := List.mem_range.mp hi
    interval_cases i <;> decide +kernel

private theorem mem_knownIndices_of_small {n : ℕ} (hn : 1 ≤ n) (hle : n ≤ 10 ^ 7)
    (h : ∀ p ∈ screeningPrimes, p ∣ n ∨ (p.digits n).sum < p) : n ∈ knownIndices := by
  obtain ⟨block, hblock, hmem⟩ := exists_mem_candidateBlocks hle h
  have hp₂ : screeningPrimes.all (fun p => decide (1 < p)) = true := by decide
  have hpass : passesScreen n = true := by
    apply List.all_eq_true.mpr
    intro p hp
    apply Bool.or_eq_true_iff.mpr
    rcases h p hp with hdiv | hsum
    · exact Or.inl (decide_eq_true hdiv)
    · have hbase := of_decide_eq_true (List.all_eq_true.mp hp₂ p hp)
      have hbound := (hle.trans_lt (by decide : (10 : ℕ) ^ 7 < 2 ^ 24)).trans_le
        (Nat.pow_le_pow_left hbase 24)
      exact Or.inr ((digitSumAtMost_iff hbase hbound).mpr (by omega))
  have hcheck := List.all_eq_true.mp (sieveCertificate block hblock) n hmem
  have hwindow : decide (0 < n ∧ n ≤ 10 ^ 7) = true := decide_eq_true ⟨hn, hle⟩
  exact List.contains_iff_mem.mp (by simpa only [hwindow, hpass, Bool.and_self, Bool.not_true,
    Bool.false_or] using hcheck)

/-- **Constraints on Bernoulli polynomials with integral derivative.** Let $n \ge 1$ be such that
the derivative $B_n'(x)$ of the Bernoulli polynomial $B_n(x)$ has integer coefficients. Then
$n + 1$ is prime, and if $n \notin \{1, 2, 4, 6, 10, 12, 28, 30, 36, 60\}$, then $n > 10^7$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 5
(`jis-2024-24.2.8-thm-5`). -/
public theorem bernoulli_integral_derivative_succ_prime_and_large :
    (∀ n ∈ bernoulliIntegralDerivativeIndices 1, (n + 1).Prime) ∧
    ∀ n ∈ bernoulliIntegralDerivativeIndices 1,
      n ∉ ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Set ℕ) → 10 ^ 7 < n := by
  constructor
  · intro n hn
    exact (bernoulli_derivative_integral_iff n
      (mem_bernoulliIntegralDerivativeIndices_iff.mp hn).1).2.2 hn
  · intro n hn hnot
    by_contra! hle
    have hn₁ := (mem_bernoulliIntegralDerivativeIndices_iff.mp hn).1
    have hpart := (bernoulli_derivative_integral_iff n hn₁).1.mp hn
    have hprimes : screeningPrimes.all (fun p => decide p.Prime) = true := by decide +kernel
    have hconstraints : ∀ p ∈ screeningPrimes, p ∣ n ∨ (p.digits n).sum < p := by
      intro p hp
      by_contra! h
      have hprime := of_decide_eq_true (List.all_eq_true.mp hprimes p hp)
      have hd := (prime_dvd_bernoulliDiffDenominatorCoprimePart_iff hprime).mpr h
      exact hprime.ne_one (Nat.dvd_one.mp (hpart ▸ hd))
    have hmem := mem_knownIndices_of_small hn₁ hle hconstraints
    exact hnot (by simpa [knownIndices] using hmem)

end MetaMathlibExt
