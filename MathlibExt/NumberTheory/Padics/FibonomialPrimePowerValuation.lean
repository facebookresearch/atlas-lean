/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility

@[expose] public section

/-!
Zero-valued branch of the corrected Fibonacci specialization in
Phakhinkon Phunphayap and Prapanpong Pongsriiam,
“Explicit Formulas for the p-adic Valuations of Fibonomial Coefficients,”
Journal of Integer Sequences 21 (2018), Article 18.3.1,
URL: `https://cs.uwaterloo.ca/journals/JIS/VOL21/Pongsriiam/pong12.tex`,
source-file SHA-256:
`f46bbde8ca65fdc11e7de74b3e9788420fb3d8111906d4b0cb8a1a6a46a3c1df`.

Controlling statement: Example `rem18`, equation `eq1remark2`, lines 1262–1275;
exact-span SHA-256 (LF-joined without terminal LF):
`c0ae246a57849caad94bf0e915ce089f18a4e5a5dbfda95ae31e8c4d3293543d`.
Inherited positivity/range context: Example `example2`, lines 1199–1200;
exact-span SHA-256:
`2dbc84fc9c8d41821a77e4b05f6ef1cddb3da308269a4c4614f6f13c16f9f9f4`.
Fibonomial/Fibonacci definitions: lines 91–96; exact-span SHA-256:
`3c22626288d1b40027ae2bc4504ba5ea895102e13516600e2d92f723eaf7dc99`.
Archive task id:
`jis_grounded_7eac3f623dce1f22cadb0392__ballot_fibonomial_prime_power_val_zero`.
-/

namespace MetaMathlibExt

private theorem fib_rank_of_dvd {p : ℕ} [Fact (Nat.Prime p)] (t : ℕ)
    (ht : 0 < t) (hdiv : p ∣ Nat.fib t) :
    ∃ z : ℕ, 1 < z ∧ z ∣ t ∧ ∀ n : ℕ, p ∣ Nat.fib n ↔ z ∣ n := by
  have hp : Nat.Prime p := Fact.out
  have hex : ∃ n : ℕ, 0 < n ∧ p ∣ Nat.fib n := ⟨t, ht, hdiv⟩
  obtain ⟨z, hzspec, hzmin⟩ :
      ∃ z : ℕ, (0 < z ∧ p ∣ Nat.fib z)
        ∧ ∀ m : ℕ, 0 < m ∧ p ∣ Nat.fib m → z ≤ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩
  have hz1 : 1 < z := by
    by_contra h
    simp only [not_lt] at h
    have hzeq : z = 1 := by have := hzspec.1; omega
    rw [hzeq, Nat.fib_one] at hzspec
    have hle := Nat.le_of_dvd (by omega) hzspec.2
    have := hp.one_lt
    omega
  have hiff : ∀ n : ℕ, p ∣ Nat.fib n ↔ z ∣ n := by
    intro n
    constructor
    · intro hdn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · set g := Nat.gcd n z with hg
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hzspec.1
        have hgdvd : p ∣ Nat.fib g := by
          have h1 : p ∣ Nat.gcd (Nat.fib n) (Nat.fib z) := Nat.dvd_gcd hdn hzspec.2
          rwa [← Nat.fib_gcd] at h1
        have hzg : z ≤ g := hzmin g ⟨hgpos, hgdvd⟩
        have hgz : g ≤ z := Nat.le_of_dvd hzspec.1 (Nat.gcd_dvd_right n z)
        have hgz' : g = z := le_antisymm hgz hzg
        rw [← hgz']
        exact Nat.gcd_dvd_left n z
    · intro hzn
      obtain ⟨c, rfl⟩ := hzn
      exact hzspec.2.trans (Nat.fib_dvd z _ (dvd_mul_right z c))
  exact ⟨z, hz1, (hiff t).mp hdiv, hiff⟩

private theorem exists_fib_rank {p : ℕ} [Fact (Nat.Prime p)] (hp2 : 2 < p) (hp5 : p ≠ 5) :
    ∃ z : ℕ, 1 < z ∧ z ∣ (if legendreSym p (5 : ℤ) = 1 then p - 1 else p + 1) ∧
      ∀ n : ℕ, p ∣ Nat.fib n ↔ z ∣ n := by
  have hdiv := fib_prime_dvd_fib_of_legendre_sub p hp5 hp2
  by_cases hleg : legendreSym p (5 : ℤ) = 1
  · obtain ⟨z, hz1, hzt, hiff⟩ :=
      fib_rank_of_dvd (p - 1) (by omega) (by simpa [hleg] using hdiv)
    exact ⟨z, hz1, by simpa [hleg] using hzt, hiff⟩
  · obtain ⟨z, hz1, hzt, hiff⟩ :=
      fib_rank_of_dvd (p + 1) (by omega) (by simpa [hleg] using hdiv)
    exact ⟨z, hz1, by simpa [hleg] using hzt, hiff⟩

/-- N1: Fibonomial integrality. -/
private theorem fib_prod_range_mul_dvd (K N : ℕ) (hKN : K ≤ N) :
    (∏ i ∈ Finset.range K, Nat.fib (i + 1)) *
      ((∏ i ∈ Finset.range (N - K), Nat.fib (i + 1))) ∣
      ∏ i ∈ Finset.range N, Nat.fib (i + 1) := by
  induction N generalizing K with
  | zero =>
    interval_cases K; simp
  | succ N ih =>
    rcases eq_or_ne K 0 with rfl | hK0
    · simp
    · rcases eq_or_ne K (N + 1) with rfl | hKN'
      · simp
      · have hKN : K ≤ N := by omega
        have hK1 : 1 ≤ K := by omega
        -- Split F_{N+1} = F_K * F_{N+2-K} + F_{K-1} * F_{N+1-K}
        have hfib : Nat.fib (N + 1) =
            Nat.fib K * Nat.fib (N + 2 - K) + Nat.fib (K - 1) * Nat.fib (N + 1 - K) := by
          have h := Nat.fib_add (K - 1) (N + 1 - K)
          have e1 : K - 1 + (N + 1 - K) + 1 = N + 1 := by omega
          rw [e1] at h
          have e2 : K - 1 + 1 = K := by omega
          rw [e2] at h
          have e3 : N + 1 - K + 1 = N + 2 - K := by omega
          rw [e3] at h
          linear_combination h
        -- Peel the top factors
        have hK : K = (K - 1) + 1 := by omega
        have hNK : N + 1 - K = (N - K) + 1 := by omega
        have hFFK : (∏ i ∈ Finset.range K, Nat.fib (i + 1))
            = (∏ i ∈ Finset.range (K - 1), Nat.fib (i + 1)) * Nat.fib K := by
          conv_lhs => rw [hK, Finset.prod_range_succ]
          congr 1
          congr 1
          omega
        have hFFNK : (∏ i ∈ Finset.range (N + 1 - K), Nat.fib (i + 1))
            = (∏ i ∈ Finset.range (N - K), Nat.fib (i + 1)) * Nat.fib (N + 1 - K) := by
          conv_lhs => rw [hNK, Finset.prod_range_succ]
          congr 1
          congr 1
          omega
        have hFFN : (∏ i ∈ Finset.range (N + 1), Nat.fib (i + 1))
            = (∏ i ∈ Finset.range N, Nat.fib (i + 1)) * Nat.fib (N + 1) := by
          rw [Finset.prod_range_succ]
        have hNK1 : N - (K - 1) = N + 1 - K := by omega
        obtain ⟨C1, hC1⟩ := ih (K - 1) (by omega)
        obtain ⟨C2, hC2⟩ := ih K hKN
        rw [hNK1, hFFNK] at hC1
        rw [hFFK] at hC2
        rw [hFFK, hFFNK, hFFN, hfib, mul_add]
        apply dvd_add
        · exact ⟨C1 * Nat.fib (N + 2 - K), by rw [hC1]; ring⟩
        · exact ⟨C2 * Nat.fib (K - 1), by rw [hC2]; ring⟩

/-- N3: quadratic character of 5 at p with p mod 5 = 1 or 4. -/
private theorem legendreSym_five_eq_one_of_mod_five (p : ℕ) [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hmod : p % 5 = 1 ∨ p % 5 = 4) : legendreSym p (5 : ℤ) = 1 := by
  have _h5 : Fact (Nat.Prime 5) := Fact.mk Nat.prime_five
  have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) hp2
  simp only [Nat.cast_ofNat] at hrec
  rw [hrec, legendreSym.mod, ← Int.natCast_mod]
  rcases hmod with h1 | h4
  · rw [h1]
    norm_cast
  · rw [h4]
    norm_cast

/-- N4: rank is coprime to p and divides p^b - p^a. -/
private theorem rank_coprime_and_dvd_pow_sub_pow (p : ℕ) [Fact (Nat.Prime p)]
    (hp2lt : 2 < p) (_hp5 : p ≠ 5) (z : ℕ) (_hz0 : 0 < z)
    (hzdvd : z ∣ (if legendreSym p 5 = 1 then p - 1 else p + 1))
    (a b : ℕ) (hab : a ≤ b)
    (hbranch : (p % 5 = 1 ∨ p % 5 = 4) ∨ a % 2 = b % 2) :
    Nat.Coprime z p ∧ z ∣ p ^ b - p ^ a := by
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hz2 : z ∣ p ^ 2 - 1 := by
    have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      have h := Nat.sq_sub_sq p 1
      simpa using h
    by_cases hleg : legendreSym p 5 = 1
    · have h1 : z ∣ p - 1 := by simpa [hleg] using hzdvd
      rw [hsq]
      exact Dvd.dvd.mul_left h1 _
    · have h1 : z ∣ p + 1 := by simpa [hleg] using hzdvd
      rw [hsq]
      exact Dvd.dvd.mul_right h1 _
  have hcop : Nat.Coprime z p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hpdvd
    have h1 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    have h2 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h1 (hpdvd.trans hz2)
    have h3 : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have hle : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
      omega
    rw [h3] at h2
    have h4 : p = 1 := Nat.dvd_one.mp h2
    omega
  refine ⟨hcop, ?_⟩
  have hdecomp : p ^ b - p ^ a = p ^ a * (p ^ (b - a) - 1) := by
    have hb : b = a + (b - a) := by omega
    conv_lhs => rw [hb, pow_add]
    rw [Nat.mul_sub_one]
  have hbase : z ∣ p ^ (b - a) - 1 := by
    rcases hbranch with hb | hpar
    · have hleg := legendreSym_five_eq_one_of_mod_five p hp2 hb
      have h1 : z ∣ p - 1 := by simpa [hleg] using hzdvd
      exact h1.trans (Nat.sub_one_dvd_pow_sub_one p (b - a))
    · have hev : Even (b - a) := by
        rw [Nat.even_iff]
        omega
      obtain ⟨k, hk⟩ := hev
      have h2k : b - a = 2 * k := by omega
      have hpdvd : p ^ 2 - 1 ∣ (p ^ 2) ^ k - 1 := Nat.sub_one_dvd_pow_sub_one _ _
      rw [← pow_mul] at hpdvd
      rw [← h2k] at hpdvd
      exact hz2.trans hpdvd
  rw [hdecomp]
  exact Dvd.dvd.mul_left hbase _

/-- N5: Fibonacci multiplication formula via the golden ratio. -/
private theorem fib_mul_eq_sum_choose (m u : ℕ) (hm : 1 ≤ m) :
    Nat.fib (m * u) =
      ∑ i ∈ Finset.range (u + 1),
        u.choose i * Nat.fib m ^ i * Nat.fib (m - 1) ^ (u - i) * Nat.fib i := by
  -- Remainder function: φ^n = F_n * φ + c_n.
  set c : ℕ → ℤ := fun n => (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) with hc
  have hstar : ∀ n : ℕ, (Real.goldenRatio : ℝ) ^ n
      = ((Nat.fib n : ℕ) : ℝ) * Real.goldenRatio + ((c n : ℤ) : ℝ) := by
    intro n
    have h := Real.fib_succ_sub_goldenConj_mul_fib n
    rw [← Real.one_sub_goldenConj] at h
    simp only [hc, Int.cast_sub, Int.cast_natCast]
    linarith
  -- φ^m in terms of F_m and F_{m-1}.
  have hphi_m : (Real.goldenRatio : ℝ) ^ m
      = ((Nat.fib m : ℕ) : ℝ) * Real.goldenRatio + ((Nat.fib (m - 1) : ℕ) : ℝ) := by
    have h := Real.goldenRatio_mul_fib_succ_add_fib (m - 1)
    rw [show m - 1 + 1 = m from by omega] at h
    linarith
  -- The target sum and the integer remainder sum.
  set S : ℕ := ∑ i ∈ Finset.range (u + 1),
    u.choose i * Nat.fib m ^ i * Nat.fib (m - 1) ^ (u - i) * Nat.fib i with hS
  set T : ℤ := ∑ i ∈ Finset.range (u + 1),
    ((u.choose i * Nat.fib m ^ i * Nat.fib (m - 1) ^ (u - i) : ℕ) : ℤ) * c i with hT
  -- Per-term expansion.
  have term_eq : ∀ k ∈ Finset.range (u + 1),
      (((Nat.fib m : ℕ) : ℝ) * Real.goldenRatio) ^ k * ((Nat.fib (m - 1) : ℕ) : ℝ) ^ (u - k) *
        ((u.choose k : ℕ) : ℝ)
      = (((u.choose k * Nat.fib m ^ k * Nat.fib (m - 1) ^ (u - k) * Nat.fib k : ℕ)) : ℝ) *
          Real.goldenRatio +
        ((((u.choose k * Nat.fib m ^ k * Nat.fib (m - 1) ^ (u - k) : ℕ) : ℤ) * c k : ℤ) : ℝ) := by
    intro k _
    rw [mul_pow, hstar k]
    push_cast
    ring
  -- Claim A: (φ^m)^u = S * φ + T.
  have hA : ((Real.goldenRatio : ℝ) ^ m) ^ u
      = ((S : ℕ) : ℝ) * Real.goldenRatio + ((T : ℤ) : ℝ) := by
    rw [hphi_m, add_pow]
    rw [Finset.sum_congr rfl term_eq, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Nat.cast_sum, ← Int.cast_sum]
  -- Combine with (star) at m * u.
  have hmu : (Real.goldenRatio : ℝ) ^ (m * u)
      = ((Nat.fib (m * u) : ℕ) : ℝ) * Real.goldenRatio + ((c (m * u) : ℤ) : ℝ) := hstar (m * u)
  have hpow : (Real.goldenRatio : ℝ) ^ (m * u) = ((Real.goldenRatio : ℝ) ^ m) ^ u := pow_mul _ _ _
  -- The difference is an integer multiple of φ equal to an integer.
  set d : ℤ := (S : ℤ) - (Nat.fib (m * u) : ℤ) with hd
  set K : ℤ := c (m * u) - T with hK
  have hdeq : ((d : ℤ) : ℝ) * Real.goldenRatio = ((K : ℤ) : ℝ) := by
    simp only [hd, hK, Int.cast_sub, Int.cast_natCast]
    linear_combination hmu - hA
  -- Irrationality forces d = 0.
  by_cases hd0 : d = 0
  · have hSeq : (S : ℤ) = ((Nat.fib (m * u) : ℕ) : ℤ) := by
      simp only [hd] at hd0
      exact sub_eq_zero.mp hd0
    have hnat : S = Nat.fib (m * u) := Int.ofNat_inj.mp hSeq
    omega
  · have hirr := Irrational.intCast_mul Real.goldenRatio_irrational (m := d) hd0
    rw [hdeq] at hirr
    exact absurd hirr (Int.not_irrational K)

/-- N6: first-order Fibonacci LTE shape. -/
private theorem fib_mul_eq_fib_mul_add (m u : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) :
    ∃ W : ℕ, Nat.fib (m * u)
      = Nat.fib m * (u * Nat.fib (m - 1) ^ (u - 1) + Nat.fib m * W) := by
  rw [fib_mul_eq_sum_choose m u hm]
  have hu1 : u + 1 = (u - 1) + 1 + 1 := by omega
  rw [hu1, Finset.sum_range_succ', Finset.sum_range_succ']
  refine ⟨∑ j ∈ Finset.range (u - 1),
    u.choose (j + 1 + 1) * Nat.fib m ^ j * Nat.fib (m - 1) ^ (u - (j + 1 + 1)) *
      Nat.fib (j + 1 + 1), ?_⟩
  have hf0 : u.choose 0 * Nat.fib m ^ 0 * Nat.fib (m - 1) ^ (u - 0) * Nat.fib 0 = 0 := by
    simp
  have hf1 : u.choose (0 + 1) * Nat.fib m ^ (0 + 1) * Nat.fib (m - 1) ^ (u - (0 + 1)) *
      Nat.fib (0 + 1) = u * Nat.fib m * Nat.fib (m - 1) ^ (u - 1) := by
    change u.choose 1 * Nat.fib m ^ 1 * Nat.fib (m - 1) ^ (u - 1) * Nat.fib 1 = _
    rw [Nat.choose_one_right, Nat.fib_one]
    ring
  have htail : (∑ k ∈ Finset.range (u - 1),
      u.choose (k + 1 + 1) * Nat.fib m ^ (k + 1 + 1) * Nat.fib (m - 1) ^ (u - (k + 1 + 1)) *
        Nat.fib (k + 1 + 1))
      = Nat.fib m ^ 2 * (∑ j ∈ Finset.range (u - 1),
        u.choose (j + 1 + 1) * Nat.fib m ^ j * Nat.fib (m - 1) ^ (u - (j + 1 + 1)) *
          Nat.fib (j + 1 + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hjj : j + 1 + 1 = 2 + j := by ring
    rw [hjj, pow_add]
    ring
  rw [htail, hf0, hf1]
  ring

/-- N7: second-order Fibonacci LTE shape. -/
private theorem fib_mul_prime_eq (m p : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime p)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.fib m) :
    ∃ W : ℕ, Nat.fib (m * p)
      = p * Nat.fib m * (Nat.fib (m - 1) ^ (p - 1) + p * W) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  obtain ⟨v, hv⟩ := hdvd
  rw [fib_mul_eq_sum_choose m p hm]
  have hp1 : p + 1 = (p - 1) + 1 + 1 := by omega
  rw [hp1, Finset.sum_range_succ', Finset.sum_range_succ']
  have hf0 : p.choose 0 * Nat.fib m ^ 0 * Nat.fib (m - 1) ^ (p - 0) * Nat.fib 0 = 0 := by
    simp
  have hf1 : p.choose (0 + 1) * Nat.fib m ^ (0 + 1) * Nat.fib (m - 1) ^ (p - (0 + 1)) *
      Nat.fib (0 + 1) = p * Nat.fib m * Nat.fib (m - 1) ^ (p - 1) := by
    change p.choose 1 * Nat.fib m ^ 1 * Nat.fib (m - 1) ^ (p - 1) * Nat.fib 1 = _
    rw [Nat.choose_one_right, Nat.fib_one]
    ring
  have htail : p ^ 2 * Nat.fib m ∣ (∑ k ∈ Finset.range (p - 1),
      p.choose (k + 1 + 1) * Nat.fib m ^ (k + 1 + 1) * Nat.fib (m - 1) ^ (p - (k + 1 + 1)) *
        Nat.fib (k + 1 + 1)) := by
    apply Finset.dvd_sum
    intro j hj
    have hjp : j + 2 ≤ p := by
      have := Finset.mem_range.mp hj
      omega
    by_cases h : j + 1 + 1 < p
    · obtain ⟨c1, hc1⟩ := hp.dvd_choose_self (show j + 1 + 1 ≠ 0 by omega) h
      have hpow : Nat.fib m ^ (j + 1 + 1) = Nat.fib m ^ 2 * Nat.fib m ^ j := by
        rw [show j + 1 + 1 = 2 + j from by ring, pow_add]
      refine ⟨c1 * v * Nat.fib m ^ j
        * Nat.fib (m - 1) ^ (p - (j + 1 + 1)) * Nat.fib (j + 1 + 1), ?_⟩
      rw [hc1, hpow, hv]
      ring
    · have hjjp : j + 1 + 1 = p := by omega
      have e1 : p = 2 + (p - 2) := by omega
      have e2 : p - 2 = 1 + (p - 3) := by omega
      refine ⟨v ^ 2 * Nat.fib m ^ (p - 3) * Nat.fib p, ?_⟩
      rw [hjjp]
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, one_mul, mul_one]
      have hpw1 : Nat.fib m ^ p = Nat.fib m ^ 2 * Nat.fib m ^ (p - 2) := by
        conv_lhs => rw [e1, pow_add]
      have hpw2 : Nat.fib m ^ (p - 2) = Nat.fib m * Nat.fib m ^ (p - 3) := by
        conv_lhs => rw [e2, pow_add, pow_one]
      rw [hpw1, hpw2, hv]
      ring
  obtain ⟨W, hW⟩ := htail
  exact ⟨W, by rw [hW, hf0, hf1]; ring⟩

/-- **Lifting the exponent for Fibonacci numbers.** Let $p$ be an odd prime and $m \ge 1$ an
integer such that $p$ divides the Fibonacci number $F_m$, and write $v_p$ for the $p$-adic
valuation. Then $v_p(F_{mj}) = v_p(F_m) + v_p(j)$ for every integer $j \ge 1$. -/
theorem padicValNat_fib_mul (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (m : ℕ) (hm : 1 ≤ m) (hdvd : p ∣ Nat.fib m) (j : ℕ) (hj : 1 ≤ j) :
    padicValNat p (Nat.fib (m * j)) = padicValNat p (Nat.fib m) + padicValNat p j := by
  have hp : Nat.Prime p := Fact.out
  -- Facts about m' := m * p ^ s for any s.
  have hm's : ∀ s : ℕ, 1 ≤ m * p ^ s := fun s => by
    calc 1 = 1 * 1 := by ring
    _ ≤ m * p ^ s := Nat.mul_le_mul hm (Nat.one_le_pow s p hp.pos)
  have hdvd' : ∀ s : ℕ, p ∣ Nat.fib (m * p ^ s) := fun s =>
    hdvd.trans (Nat.fib_dvd _ _ (dvd_mul_right m _))
  have hm'2 : ∀ s : ℕ, 2 ≤ m * p ^ s := fun s => by
    have hne : m * p ^ s ≠ 1 := by
      intro h
      have hds := hdvd' s
      rw [h, Nat.fib_one] at hds
      have h1 : p = 1 := Nat.dvd_one.mp hds
      have := hp.one_lt
      omega
    have := hm's s
    omega
  have hFpos : ∀ s : ℕ, 0 < Nat.fib (m * p ^ s - 1) :=
    fun s => Nat.fib_pos.mpr (by have := hm'2 s; omega)
  have hnot : ∀ s : ℕ, ¬ p ∣ Nat.fib (m * p ^ s - 1) := fun s => by
    intro hd
    have hcop := Nat.fib_coprime_fib_succ (m * p ^ s - 1)
    rw [show m * p ^ s - 1 + 1 = m * p ^ s from by have := hm'2 s; omega] at hcop
    have hgcd : p ∣ Nat.gcd (Nat.fib (m * p ^ s - 1)) (Nat.fib (m * p ^ s)) :=
      Nat.dvd_gcd hd (hdvd' s)
    rw [hcop.gcd_eq_one] at hgcd
    have h1 : p = 1 := Nat.dvd_one.mp hgcd
    have := hp.one_lt
    omega
  -- Step 1: pure prime powers.
  have step1 : ∀ s : ℕ,
      padicValNat p (Nat.fib (m * p ^ s)) = padicValNat p (Nat.fib m) + s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      obtain ⟨W, hW⟩ := fib_mul_prime_eq (m * p ^ s) p (hm's s) hp (by omega) (hdvd' s)
      have hexp : m * p ^ (s + 1) = (m * p ^ s) * p := by rw [pow_succ]; ring
      have hBpos : 0 < Nat.fib (m * p ^ s - 1) ^ (p - 1) + p * W := by
        have h1 : 1 ≤ Nat.fib (m * p ^ s - 1) ^ (p - 1) :=
          Nat.one_le_pow _ _ (hFpos s)
        omega
      have hBnot : ¬ p ∣ (Nat.fib (m * p ^ s - 1) ^ (p - 1) + p * W) := by
        intro hd
        have h1 : p ∣ p * W := dvd_mul_right p W
        have h2 : p ∣ Nat.fib (m * p ^ s - 1) ^ (p - 1) := by
          have hsub : p ∣ (Nat.fib (m * p ^ s - 1) ^ (p - 1) + p * W) - p * W :=
            Nat.dvd_sub hd h1
          rwa [Nat.add_sub_cancel] at hsub
        exact hnot s (hp.prime.dvd_of_dvd_pow h2)
      have hB0 : padicValNat p (Nat.fib (m * p ^ s - 1) ^ (p - 1) + p * W) = 0 :=
        padicValNat.eq_zero_of_not_dvd hBnot
      have hFne : Nat.fib (m * p ^ s) ≠ 0 :=
        (Nat.fib_pos.mpr (hm's s)).ne'
      rw [hexp, hW, padicValNat.mul (mul_ne_zero hp.ne_zero hFne) hBpos.ne',
        padicValNat.mul hp.ne_zero hFne, padicValNat_self, hB0, ih]
      omega
  -- Step 2: general j.
  obtain ⟨s, t, ht, hjst⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show j ≠ 0 by omega) p hp.one_lt.ne'
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hjst
    omega
  have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht0
  obtain ⟨W, hW⟩ := fib_mul_eq_fib_mul_add (m * p ^ s) t (hm's s) ht1
  have hexp : m * j = (m * p ^ s) * t := by rw [hjst]; ring
  have hBpos : 0 < t * Nat.fib (m * p ^ s - 1) ^ (t - 1) + Nat.fib (m * p ^ s) * W := by
    have h1 : 1 ≤ t * Nat.fib (m * p ^ s - 1) ^ (t - 1) := by
      have h2 := Nat.mul_le_mul ht1 (Nat.one_le_pow (t - 1) _ (hFpos s))
      simpa using h2
    omega
  have hBnot : ¬ p ∣ (t * Nat.fib (m * p ^ s - 1) ^ (t - 1) + Nat.fib (m * p ^ s) * W) := by
    intro hd
    have h1 : p ∣ Nat.fib (m * p ^ s) * W := (hdvd' s).trans (dvd_mul_right _ _)
    have h2 : p ∣ t * Nat.fib (m * p ^ s - 1) ^ (t - 1) := by
      have hsub := Nat.dvd_sub hd h1
      rwa [Nat.add_sub_cancel] at hsub
    rcases hp.dvd_mul.mp h2 with h3 | h3
    · exact ht h3
    · exact hnot s (hp.prime.dvd_of_dvd_pow h3)
  have hB0 : padicValNat p
      (t * Nat.fib (m * p ^ s - 1) ^ (t - 1) + Nat.fib (m * p ^ s) * W) = 0 :=
    padicValNat.eq_zero_of_not_dvd hBnot
  have hFne : Nat.fib (m * p ^ s) ≠ 0 := (Nat.fib_pos.mpr (hm's s)).ne'
  have hjv : padicValNat p j = s := by
    rw [hjst, padicValNat.mul (pow_ne_zero s hp.ne_zero) ht0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ht, add_zero]
  rw [hexp, hW, padicValNat.mul hFne hBpos.ne', step1 s, hB0, hjv, add_zero]

/-- N9: Legendre-type formula for Fibonacci factorials. -/
private theorem padicValNat_fib_prod_range (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (z : ℕ) (hz : 0 < z) (hiff : ∀ n : ℕ, p ∣ Nat.fib n ↔ z ∣ n) (N : ℕ) :
    padicValNat p (∏ i ∈ Finset.range N, Nat.fib (i + 1))
      = padicValNat p (Nat.fib z) * (N / z) + padicValNat p (N / z).factorial := by
  have hp : Nat.Prime p := Fact.out
  have hv1 : padicValNat p 1 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by
      intro h
      have h1 := Nat.dvd_one.mp h
      have := hp.one_lt
      omega)
  induction N with
  | zero => simp [hv1]
  | succ N ih =>
    have hFF : (∏ i ∈ Finset.range (N + 1), Nat.fib (i + 1))
        = (∏ i ∈ Finset.range N, Nat.fib (i + 1)) * Nat.fib (N + 1) := by
      rw [Finset.prod_range_succ]
    have hFFne : (∏ i ∈ Finset.range N, Nat.fib (i + 1)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact (Nat.fib_pos.mpr (Nat.succ_pos i)).ne'
    have hFne : Nat.fib (N + 1) ≠ 0 := (Nat.fib_pos.mpr (Nat.succ_pos N)).ne'
    by_cases hzdvd : z ∣ N + 1
    · set q := N / z with hq
      have hdiv : (N + 1) / z = q + 1 := Nat.succ_div_of_dvd hzdvd
      have hmul : z * (q + 1) = N + 1 := by
        rw [← hdiv]
        exact Nat.mul_div_cancel' hzdvd
      have hN8 := padicValNat_fib_mul p hp2 z (by omega) ((hiff z).mpr dvd_rfl) (q + 1)
        (Nat.succ_pos q)
      rw [hmul] at hN8
      have hfact : padicValNat p (q + 1).factorial
          = padicValNat p (q + 1) + padicValNat p q.factorial := by
        rw [Nat.factorial_succ,
          padicValNat.mul (Nat.succ_ne_zero q) (Nat.factorial_ne_zero q)]
      rw [hFF, padicValNat.mul hFFne hFne, ih, hdiv, hfact, hN8, mul_add, mul_one]
      omega
    · have hdiv : (N + 1) / z = N / z := Nat.succ_div_of_not_dvd hzdvd
      have hnot : ¬ p ∣ Nat.fib (N + 1) := fun h => hzdvd ((hiff (N + 1)).mp h)
      have hF0 : padicValNat p (Nat.fib (N + 1)) = 0 :=
        padicValNat.eq_zero_of_not_dvd hnot
      rw [hFF, padicValNat.mul hFFne hFne, ih, hdiv, hF0, add_zero]

/-- N10: no-carry addition in base p for factorials. -/
private theorem padicValNat_factorial_add_pow_mul (p : ℕ) [Fact (Nat.Prime p)]
    (a A B : ℕ) (hA : A < p ^ a) :
    padicValNat p (A + p ^ a * B).factorial =
      padicValNat p A.factorial + padicValNat p (p ^ a * B).factorial := by
  induction a generalizing A with
  | zero =>
    have hA0 : A = 0 := by simpa using hA
    simp [hA0]
  | succ a ih =>
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    set A1 := A / p with hA1def
    set r := A % p with hrdef
    have hAeq : A = p * A1 + r := (Nat.div_add_mod A p).symm
    have hr : r < p := Nat.mod_lt _ hp0
    have hB : p ^ (a + 1) * B = p * (p ^ a * B) := by rw [pow_succ]; ring
    have hpow : p ^ (a + 1) = p * p ^ a := by rw [pow_succ]; ring
    have hA1 : A1 < p ^ a := by
      have hAlt : p * A1 ≤ A := by omega
      have h1 : p * A1 < p * p ^ a := by rw [← hpow]; omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have ihA := ih A1 hA1
    have hsplit : A + p ^ (a + 1) * B = p * (A1 + p ^ a * B) + r := by
      rw [hAeq, hB]; ring
    have e1 : padicValNat p (A + p ^ (a + 1) * B).factorial
        = padicValNat p (A1 + p ^ a * B).factorial + (A1 + p ^ a * B) := by
      rw [hsplit, padicValNat_factorial_mul_add _ hr, padicValNat_factorial_mul]
    have e2 : padicValNat p A.factorial = padicValNat p A1.factorial + A1 := by
      rw [hAeq, padicValNat_factorial_mul_add _ hr, padicValNat_factorial_mul]
    have e3 : padicValNat p (p ^ (a + 1) * B).factorial
        = padicValNat p (p ^ a * B).factorial + p ^ a * B := by
      rw [hB, padicValNat_factorial_mul]
    omega

/-- N11: division split. -/
private theorem div_rank_split (p z a b : ℕ) (hp0 : 0 < p) (hz1 : 1 < z)
    (hcop : Nat.Coprime z p) (hab : a ≤ b) (hdvd : z ∣ p ^ b - p ^ a) :
    (p ^ b / z = p ^ a / z + (p ^ b - p ^ a) / z) ∧
    (p ^ a / z < p ^ a) ∧
    ((p ^ b - p ^ a) / z = p ^ a * ((p ^ (b - a) - 1) / z)) := by
  have hle : p ^ a ≤ p ^ b := Nat.pow_le_pow_right (by omega) hab
  have hcop_pow : Nat.Coprime z (p ^ a) := hcop.pow_right a
  refine ⟨?_, Nat.div_lt_self (Nat.pow_pos hp0) hz1, ?_⟩
  · have h2 : p ^ b = (p ^ b - p ^ a) + p ^ a := by omega
    conv_lhs => rw [h2]
    rw [Nat.add_div_of_dvd_right hdvd, add_comm]
  · have hdecomp : p ^ b - p ^ a = p ^ a * (p ^ (b - a) - 1) := by
      have hb : b = a + (b - a) := by omega
      conv_lhs => rw [hb, pow_add]
      rw [Nat.mul_sub_one]
    have hdvd2 : z ∣ p ^ (b - a) - 1 :=
      hcop_pow.dvd_of_dvd_mul_left (by rw [← hdecomp]; exact hdvd)
    rw [hdecomp, Nat.mul_div_assoc _ hdvd2]

/-- N12: valuation splits over the Fibonomial factors at prime powers. -/
private theorem padicValNat_fib_prod_prime_pow_split (p a b : ℕ) [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hab : a ≤ b)
    (hbranch : (p % 5 = 1 ∨ p % 5 = 4) ∨ a % 2 = b % 2) :
    padicValNat p (∏ i ∈ Finset.range (p ^ b), Nat.fib (i + 1))
      = padicValNat p (∏ i ∈ Finset.range (p ^ a), Nat.fib (i + 1))
        + padicValNat p (∏ i ∈ Finset.range (p ^ b - p ^ a), Nat.fib (i + 1)) := by
  have hp : Nat.Prime p := Fact.out
  have hp2lt : 2 < p := by have h2 := hp.two_le; omega
  obtain ⟨z, hz1, hzdvd, hiff⟩ := exists_fib_rank hp2lt hp5
  obtain ⟨hcop, hdvd⟩ :=
    rank_coprime_and_dvd_pow_sub_pow p hp2lt hp5 z (by omega) hzdvd a b hab hbranch
  obtain ⟨hsplit, hAlt, hB⟩ := div_rank_split p z a b hp.pos hz1 hcop hab hdvd
  have h9b := padicValNat_fib_prod_range p hp2 z (by omega) hiff (p ^ b)
  have h9a := padicValNat_fib_prod_range p hp2 z (by omega) hiff (p ^ a)
  have h9d := padicValNat_fib_prod_range p hp2 z (by omega) hiff (p ^ b - p ^ a)
  have hN10 := padicValNat_factorial_add_pow_mul p a (p ^ a / z) ((p ^ (b - a) - 1) / z) hAlt
  rw [h9b, h9a, h9d, hsplit, hB, hN10]
  ring
/-- **Vanishing $p$-adic valuation of Fibonomial coefficients at prime powers.** Let $p$ be a
prime with $p \ne 2$ and $p \ne 5$, and let $a, b$ be integers with $0 < a \le b$ such that
$p \equiv \pm 1 \pmod 5$ or $a \equiv b \pmod 2$. Write $F_n$ for the $n$-th Fibonacci number
and $F_n! = F_1 F_2 \cdots F_n$ for the Fibonacci factorial, with $F_0! = 1$. Then the $p$-adic
valuation of the Fibonomial coefficient
$$\binom{p^b}{p^a}_F = \frac{F_{p^b}!}{F_{p^a}! \, F_{p^b - p^a}!},$$
where the quotient is taken by division of natural numbers, is $0$.

Proves `Wanted` entry `fibonomial_primePower_padicVal_eq_zero`.

Source: Phunphayap–Pongsriiam, Example `rem18`, equation `eq1remark2`.
-/
theorem fibonomial_primePower_padicVal_eq_zero
    (p a b : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (ha : 0 < a) (hab : a ≤ b)
    (hbranch : (p % 5 = 1 ∨ p % 5 = 4) ∨ a % 2 = b % 2) :
    padicValNat p
      ((∏ i ∈ Finset.range (p ^ b), Nat.fib (i + 1)) /
        ((∏ i ∈ Finset.range (p ^ a), Nat.fib (i + 1)) *
          ∏ i ∈ Finset.range (p ^ b - p ^ a), Nat.fib (i + 1))) = 0 := by
  have _ : 0 < a := ha
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hle : p ^ a ≤ p ^ b := Nat.pow_le_pow_right hp.pos hab
  have hdvd := fib_prod_range_mul_dvd (p ^ a) (p ^ b) hle
  have hne1 : (∏ i ∈ Finset.range (p ^ a), Nat.fib (i + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (Nat.fib_pos.mpr (Nat.succ_pos i)).ne'
  have hne2 : (∏ i ∈ Finset.range (p ^ b - p ^ a), Nat.fib (i + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (Nat.fib_pos.mpr (Nat.succ_pos i)).ne'
  have hsplit := padicValNat_fib_prod_prime_pow_split p a b hp2 hp5 hab hbranch
  rw [padicValNat.div_of_dvd hdvd, padicValNat.mul hne1 hne2, hsplit, Nat.sub_self]

end MetaMathlibExt
