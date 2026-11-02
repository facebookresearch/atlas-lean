/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selberg sieve level weights

This module defines the optimal level-`R` Selberg weights for an arbitrary
`BoundingSieve` and proves their diagonalization, support, and error bounds.
-/

@[expose] public section

namespace MathlibExt.SelbergSieve

/-- **Selberg level set.** For a bounding sieve whose sifting primes have product $P$ and a
natural number $R$, the level-$R$ set is the set of divisors $l$ of $P$ with $l \le R$. -/
def levelSet (s : BoundingSieve) (R : ℕ) : Finset ℕ :=
  s.prodPrimes.divisors.filter fun l ↦ l ≤ R

/-- **Selberg level sum.** For a bounding sieve whose sifting primes have product $P$, with
multiplicative density function $\nu$, and a natural number $R$, the level-$R$ Selberg sum is
$G = \sum_{l \mid P,\ l \le R} g(l)$, where $g(l) = \nu(l) \prod_{p \mid l} (1 - \nu(p))^{-1}$,
the product running over the primes $p$ dividing $l$. -/
noncomputable def levelSum (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ l ∈ levelSet s R, s.selbergTerms l

/-- **Normalized Selberg coefficients.** Let $s$ be a bounding sieve with density function $\nu$
and Selberg terms $g(l) = \nu(l) \prod_{p \mid l} (1 - \nu(p))^{-1}$, the product running over
the primes $p$ dividing $l$, and let $R$ be a natural number. Write $D_R$ for the level set of $s$
at level $R$ (the divisors of the sifting product of $s$ that are at most $R$) and
$G(R) = \sum_{l \in D_R} g(l)$ for the level sum. The normalized Selberg coefficient of $s$ at
level $R$ is the function on natural numbers given by $y_l = \mu(l)\, g(l) / G(R)$ for
$l \in D_R$ and $y_l = 0$ otherwise, where $\mu$ is the Möbius function. -/
noncomputable def levelY
    (s : BoundingSieve) (R l : ℕ) : ℝ :=
  if l ∈ levelSet s R then
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) * s.selbergTerms l /
      levelSum s R
  else 0

/-- **Selberg sieve weights.** Let $s$ be a bounding sieve with sifting product $P$ (the product
of its sifting primes) and density function $\nu$, let $R$ be a natural number, and let $y_m$
denote the normalized Selberg coefficients of $s$ at level $R$. For a natural number $d$, the
level-$R$ Selberg weight of $s$ at $d$ is
$$\lambda_d = \nu(d)^{-1} \sum_{m \mid P,\ d \mid m} \mu(m/d)\, y_m,$$
where $\mu$ is the Möbius function, $m$ runs over the divisors of $P$, and $\nu(d)^{-1}$ is read
as $0$ when $\nu(d) = 0$. -/
noncomputable def levelWeights
    (s : BoundingSieve) (R d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * ∑ m ∈ s.prodPrimes.divisors,
    if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
      levelY s R m else 0

/-- **The Selberg level sum is at least one.** For every bounding sieve and every natural number
$R \ge 1$, the level-$R$ Selberg sum is at least $1$. -/
theorem levelSum_ge_one (s : BoundingSieve) (R : ℕ)
    (hR : 1 ≤ R) : 1 ≤ levelSum s R := by
  have hP0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have h1mem : 1 ∈ levelSet s R := by
    simp only [levelSet, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, hP0⟩, hR⟩
  have hg1 : s.selbergTerms 1 = 1 := by
    rw [BoundingSieve.selbergTerms_apply]
    rw [s.nu_mult.map_one]
    simp
  have hnonneg : ∀ l ∈ levelSet s R, 0 ≤ s.selbergTerms l := by
    intro l hl
    simp only [levelSet, Finset.mem_filter, Nat.mem_divisors] at hl
    exact (BoundingSieve.selbergTerms_pos (s := s) hl.1.1).le
  calc
    1 = s.selbergTerms 1 := hg1.symm
    _ ≤ ∑ l ∈ levelSet s R, s.selbergTerms l :=
      Finset.single_le_sum hnonneg h1mem
    _ = levelSum s R := rfl

open ArithmeticFunction in
private theorem sum_moebius_div_filter_dvd (m l : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ m.divisors.filter (fun d ↦ l ∣ d),
      ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) =
      (if m = l then 1 else 0) := by
  by_cases hlm : l ∣ m
  · obtain ⟨k, hk⟩ := hlm
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hk
      exact hm hk
    subst m
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hm (by simp)
    have hlk0 : l * k ≠ 0 := mul_ne_zero hl0 hk0
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hbij : ∑ d ∈ (l * k).divisors.filter (fun d ↦ l ∣ d),
          ((moebius ((l * k) / d) : ℤ) : ℝ) =
        ∑ e ∈ k.divisors, ((moebius (k / e) : ℤ) : ℝ) := by
      apply Finset.sum_nbij' (fun d ↦ d / l) (fun e ↦ l * e)
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdvd, _⟩, hld⟩ := hd
        have hddvd : d / l ∣ k := by
          have hmul : l * (d / l) = d := Nat.mul_div_cancel' hld
          have hmulDvd : l * (d / l) ∣ l * k := by
            rw [hmul]
            exact hdvd
          exact (Nat.mul_dvd_mul_iff_left hlpos).mp hmulDvd
        exact Nat.mem_divisors.mpr ⟨hddvd, hk0⟩
      · intro e he
        simp only [Nat.mem_divisors] at he
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨Nat.mul_dvd_mul_left l he.1, hlk0⟩, Nat.dvd_mul_right l e⟩
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        exact Nat.mul_div_cancel' hd.2
      · intro e _
        rw [mul_comm l e]
        exact Nat.mul_div_cancel e hlpos
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        have hdc : d = l * (d / l) := (Nat.mul_div_cancel' hd.2).symm
        have heq : (l * k) / d = k / (d / l) := by
          conv_lhs => rw [hdc]
          exact Nat.mul_div_mul_left k (d / l) hlpos
        rw [heq]
    rw [hbij]
    rw [Nat.sum_div_divisors k (fun e ↦ ((moebius e : ℤ) : ℝ))]
    have hzetaK : (↑moebius * ↑zeta : ArithmeticFunction ℝ) k =
        (1 : ArithmeticFunction ℝ) k := by
      rw [coe_moebius_mul_coe_zeta]
    rw [coe_mul_zeta_apply] at hzetaK
    simp only [one_apply] at hzetaK
    have hagree : ∀ e : ℕ, ((↑moebius : ArithmeticFunction ℝ) e) =
        ((moebius e : ℤ) : ℝ) := by
      intro e
      rw [intCoe_apply]
    have hsum : (∑ e ∈ k.divisors, ((moebius e : ℤ) : ℝ)) =
        (if k = 1 then 1 else 0) := by
      simpa [hagree] using hzetaK
    rw [hsum]
    by_cases hk1 : k = 1
    · subst k
      simp
    · have hne : ¬l * k = l := by
        intro hcon
        apply hk1
        exact Nat.mul_left_cancel hlpos (by simpa using hcon)
      simp [hk1, hne]
  · have hempty : m.divisors.filter (fun d ↦ l ∣ d) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact hlm (hd.2.trans hd.1.1)
    rw [hempty, Finset.sum_empty]
    have hne : m ≠ l := by
      rintro rfl
      exact hlm dvd_rfl
    simp [hne]

/-- **Inversion formula for the Selberg level weights.** For a bounding sieve whose sifting primes
have product $P$, with density function $\nu$, a natural number $R$ and a divisor $l$ of $P$, the
level-$R$ Selberg weights $\lambda_d$ satisfy $\sum_{d \mid P,\ l \mid d} \nu(d)\,\lambda_d = y_l$,
where $y_l$ is the normalized level-$R$ Selberg $y$-coefficient at $l$. -/
theorem levelWeights_inner (s : BoundingSieve) (R l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * levelWeights s R d else 0) =
      levelY s R l := by
  have hP0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hlD : l ∈ s.prodPrimes.divisors := Nat.mem_divisors.mpr ⟨hl, hP0⟩
  have hcancel : ∀ d ∈ s.prodPrimes.divisors,
      s.nu d * levelWeights s R d =
        ∑ m ∈ s.prodPrimes.divisors,
          if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            levelY s R m else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hne := BoundingSieve.nu_ne_zero (s := s) hd.1
    unfold levelWeights
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hdouble : (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * levelWeights s R d else 0) =
      ∑ d ∈ s.prodPrimes.divisors, ∑ m ∈ s.prodPrimes.divisors,
        if l ∣ d ∧ d ∣ m then
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            levelY s R m else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · rw [ite_eq_left hld, hcancel d hd]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hdm : d ∣ m
      · rw [ite_eq_left hdm, ite_eq_left ⟨hld, hdm⟩]
      · rw [ite_eq_right hdm, ite_eq_right (fun h ↦ hdm h.2)]
    · rw [ite_eq_right hld]
      symm
      apply Finset.sum_eq_zero
      intro m _
      rw [ite_eq_right (fun h ↦ hld h.1)]
  rw [hdouble, Finset.sum_comm]
  have hinner : ∀ m ∈ s.prodPrimes.divisors,
      (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d ∧ d ∣ m then
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            levelY s R m else 0) =
        (if m = l then levelY s R m else 0) := by
    intro m hm
    rw [Nat.mem_divisors] at hm
    have hm0 : m ≠ 0 := by
      intro h0
      subst m
      exact hP0 (by simpa only [zero_dvd_iff] using hm.1)
    have hset : s.prodPrimes.divisors.filter (fun d ↦ l ∣ d ∧ d ∣ m) =
        m.divisors.filter (fun d ↦ l ∣ d) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨-, -⟩, hld, hdm⟩
        exact ⟨⟨hdm, hm0⟩, hld⟩
      · rintro ⟨⟨hdm, -⟩, hld⟩
        exact ⟨⟨hdm.trans hm.1, hP0⟩, hld, hdm⟩
    rw [← Finset.sum_filter, hset]
    have hfactor : (∑ d ∈ m.divisors.filter (fun d ↦ l ∣ d),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            levelY s R m) =
        (∑ d ∈ m.divisors.filter (fun d ↦ l ∣ d),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) *
            levelY s R m := by
      rw [Finset.sum_mul]
    rw [hfactor, sum_moebius_div_filter_dvd m l hm0]
    by_cases hml : m = l
    · subst m
      simp
    · simp [hml]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  simp [hlD]

/-- **The Selberg level weight at one.** For every bounding sieve and every natural number
$R \ge 1$, the level-$R$ Selberg weight at $1$ equals $1$. -/
theorem levelWeights_one (s : BoundingSieve) (R : ℕ)
    (hR : 1 ≤ R) : levelWeights s R 1 = 1 := by
  have hG1 := levelSum_ge_one s R hR
  have hG0 : levelSum s R ≠ 0 := by linarith
  have hnu1 : s.nu 1 = 1 := s.nu_mult.map_one
  have hw1 : levelWeights s R 1 =
      ∑ m ∈ s.prodPrimes.divisors,
        ((ArithmeticFunction.moebius m : ℤ) : ℝ) * levelY s R m := by
    unfold levelWeights
    rw [hnu1, inv_one, one_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [ite_eq_left (one_dvd m), Nat.div_one]
  rw [hw1]
  have hterm : ∀ m ∈ s.prodPrimes.divisors,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) * levelY s R m =
        (if m ∈ levelSet s R then
          s.selbergTerms m / levelSum s R else 0) := by
    intro m hm
    unfold levelY
    by_cases hmem : m ∈ levelSet s R
    · rw [ite_eq_left hmem, ite_eq_left hmem]
      rw [Nat.mem_divisors] at hm
      have hsq := BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hm.1
      have hmu : ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius m : ℤ) : ℝ) = 1 := by
        have h1 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        have h2 : ((ArithmeticFunction.moebius m ^ 2 : ℤ) : ℝ) = 1 := by
          exact_mod_cast h1
        rw [Int.cast_pow] at h2
        simpa only [pow_two] using h2
      calc
        ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) * s.selbergTerms m /
              levelSum s R) =
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius m : ℤ) : ℝ) * s.selbergTerms m) /
                levelSum s R := by ring
        _ = s.selbergTerms m / levelSum s R := by rw [hmu, one_mul]
    · rw [ite_eq_right hmem, ite_eq_right hmem, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hfilter : (∑ m ∈ s.prodPrimes.divisors,
        if m ∈ levelSet s R then
          s.selbergTerms m / levelSum s R else 0) =
      ∑ m ∈ levelSet s R,
        s.selbergTerms m / levelSum s R := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hm
      refine ⟨?_, hm⟩
      unfold levelSet at hm
      simp only [Finset.mem_filter] at hm
      exact hm.1
  rw [hfilter, ← Finset.sum_div]
  change levelSum s R / levelSum s R = 1
  exact div_self hG0

/-- **Main term of the Selberg level weights.** For a bounding sieve whose sifting primes have
product $P$, with density function $\nu$, and a natural number $R \ge 1$, let $\lambda_d$ be the
level-$R$ Selberg weights and
$\Lambda_d = \sum_{d_1, d_2 \mid d,\ \operatorname{lcm}(d_1, d_2) = d} \lambda_{d_1} \lambda_{d_2}$
their $\Lambda^2$ coefficients. Then $\sum_{d \mid P} \Lambda_d\,\nu(d) = 1/G$, where $G$ is the
level-$R$ Selberg sum. -/
theorem levelWeights_mainSum (s : BoundingSieve) (R : ℕ)
    (hR : 1 ≤ R) :
    s.mainSum (BoundingSieve.lambdaSquared (levelWeights s R)) =
      1 / levelSum s R := by
  have hG1 := levelSum_ge_one s R hR
  have hG0 : levelSum s R ≠ 0 := by linarith
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then s.nu d * levelWeights s R d else 0) ^ 2 =
        (if l ∈ levelSet s R then
          s.selbergTerms l / (levelSum s R) ^ 2 else 0) := by
    intro l hl
    rw [Nat.mem_divisors] at hl
    rw [levelWeights_inner s R l hl.1]
    unfold levelY
    by_cases hmem : l ∈ levelSet s R
    · rw [ite_eq_left hmem, ite_eq_left hmem]
      have hsq := BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hl.1
      have hpos := BoundingSieve.selbergTerms_pos (s := s) hl.1
      have hmu : ((ArithmeticFunction.moebius l : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius l : ℤ) : ℝ) = 1 := by
        have h1 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        have h2 : ((ArithmeticFunction.moebius l ^ 2 : ℤ) : ℝ) = 1 := by
          exact_mod_cast h1
        rw [Int.cast_pow] at h2
        simpa only [pow_two] using h2
      calc
        (s.selbergTerms l)⁻¹ *
            (((ArithmeticFunction.moebius l : ℤ) : ℝ) * s.selbergTerms l /
              levelSum s R) ^ 2 =
            (((ArithmeticFunction.moebius l : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius l : ℤ) : ℝ)) * s.selbergTerms l /
                (levelSum s R) ^ 2 := by
          field_simp
        _ = s.selbergTerms l / (levelSum s R) ^ 2 := by
          rw [hmu, one_mul]
    · rw [ite_eq_right hmem, ite_eq_right hmem]
      simp
  rw [Finset.sum_congr rfl hterm]
  have hfilter : (∑ l ∈ s.prodPrimes.divisors,
        if l ∈ levelSet s R then
          s.selbergTerms l / (levelSum s R) ^ 2 else 0) =
      ∑ l ∈ levelSet s R,
        s.selbergTerms l / (levelSum s R) ^ 2 := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hl
      refine ⟨?_, hl⟩
      unfold levelSet at hl
      exact (Finset.mem_filter.mp hl).1
  rw [hfilter, ← Finset.sum_div]
  change levelSum s R / levelSum s R ^ 2 =
    1 / levelSum s R
  field_simp

/-- **Weighted bound for the Selberg level weights.** For a bounding sieve whose sifting primes
have product $P$, with density function $\nu$, a natural number $R \ge 1$ and a divisor $d$ of
$P$, the level-$R$ Selberg weight $\lambda_d$ at $d$ satisfies $|\nu(d)\,\lambda_d| \le 1$. -/
theorem levelWeights_nu_mul_abs_le
    (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    |s.nu d * levelWeights s R d| ≤ 1 := by
  have hG1 := levelSum_ge_one s R hR
  have hGpos : 0 < levelSum s R := lt_of_lt_of_le zero_lt_one hG1
  have hG0 := hGpos.ne'
  have hnu := BoundingSieve.nu_ne_zero (s := s) hd
  have hcancel : s.nu d * levelWeights s R d =
      ∑ m ∈ s.prodPrimes.divisors,
        if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
          levelY s R m else 0 := by
    unfold levelWeights
    rw [← mul_assoc, mul_inv_cancel₀ hnu, one_mul]
  rw [hcancel]
  have hmu : ∀ n : ℕ, |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
    intro n
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hterm : ∀ m ∈ s.prodPrimes.divisors,
      |if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
        levelY s R m else 0| ≤
        if m ∈ levelSet s R then
          s.selbergTerms m / levelSum s R else 0 := by
    intro m hm
    by_cases hdm : d ∣ m
    · rw [ite_eq_left hdm, abs_mul]
      have hY : |levelY s R m| ≤
          if m ∈ levelSet s R then
            s.selbergTerms m / levelSum s R else 0 := by
        unfold levelY
        by_cases hmem : m ∈ levelSet s R
        · rw [ite_eq_left hmem, ite_eq_left hmem, abs_div, abs_mul,
            abs_of_nonneg hGpos.le]
          rw [Nat.mem_divisors] at hm
          have hg := (BoundingSieve.selbergTerms_pos (s := s) hm.1).le
          rw [abs_of_nonneg hg]
          calc
            |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * s.selbergTerms m /
                levelSum s R ≤
                1 * s.selbergTerms m / levelSum s R := by
              gcongr
              exact hmu m
            _ = s.selbergTerms m / levelSum s R := by ring
        · rw [ite_eq_right hmem, ite_eq_right hmem, abs_zero]
      calc
        |((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)| *
            |levelY s R m| ≤
            1 * |levelY s R m| := by
          gcongr
          exact hmu (m / d)
        _ ≤ if m ∈ levelSet s R then
            s.selbergTerms m / levelSum s R else 0 := by
          simpa using hY
    · rw [ite_eq_right hdm, abs_zero]
      by_cases hmem : m ∈ levelSet s R
      · rw [ite_eq_left hmem]
        rw [Nat.mem_divisors] at hm
        exact div_nonneg (BoundingSieve.selbergTerms_pos (s := s) hm.1).le hGpos.le
      · rw [ite_eq_right hmem]
  calc
    |∑ m ∈ s.prodPrimes.divisors, if d ∣ m then
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
          levelY s R m else 0| ≤
        ∑ m ∈ s.prodPrimes.divisors, |if d ∣ m then
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            levelY s R m else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s.prodPrimes.divisors,
        if m ∈ levelSet s R then
          s.selbergTerms m / levelSum s R else 0 :=
      Finset.sum_le_sum hterm
    _ = 1 := by
      rw [← Finset.sum_filter]
      have hfilter : s.prodPrimes.divisors.filter
          (fun m ↦ m ∈ levelSet s R) = levelSet s R := by
        ext m
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hm
          exact ⟨(Finset.mem_filter.mp hm).1, hm⟩
      rw [hfilter, ← Finset.sum_div]
      change levelSum s R / levelSum s R = 1
      exact div_self hG0

private theorem sum_divisors_selbergTerms_eq
    (s : BoundingSieve) (d : ℕ) (hd : d ∣ s.prodPrimes) :
    ∑ e ∈ d.divisors, s.selbergTerms e = s.selbergTerms d * (s.nu d)⁻¹ := by
  have h := BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv
    (s := s) hd
  rwa [← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd (BoundingSieve.prodPrimes_ne_zero (s := s)) hd] at h

private theorem mem_levelSet_filter_dvd {s : BoundingSieve} {R d m : ℕ}
    (hm : m ∈ (levelSet s R).filter (fun n ↦ d ∣ n)) :
    d ∣ m ∧ m ∣ s.prodPrimes ∧ m ≤ R := by
  simp only [levelSet, Finset.mem_filter, Nat.mem_divisors] at hm
  exact ⟨hm.2, hm.1.1.1, hm.1.2⟩

private theorem div_coprime_of_mem_levelSet_filter_dvd
    {s : BoundingSieve} {R d m : ℕ}
    (hm : m ∈ (levelSet s R).filter (fun n ↦ d ∣ n)) :
    (m / d).Coprime d := by
  have hdata := mem_levelSet_filter_dvd hm
  have hsq := BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hdata.2.1
  exact Nat.coprime_of_squarefree_mul ((Nat.div_mul_cancel hdata.1).symm ▸ hsq)

private theorem sum_divisors_selbergTerms_mul_div
    (s : BoundingSieve) (R d m : ℕ)
    (hm : m ∈ (levelSet s R).filter (fun n ↦ d ∣ n)) :
    ∑ e ∈ d.divisors, s.selbergTerms (m / d * e) =
      (s.nu d)⁻¹ * s.selbergTerms m := by
  have hdata := mem_levelSet_filter_dvd hm
  have hcop := div_coprime_of_mem_levelSet_filter_dvd hm
  calc
    ∑ e ∈ d.divisors, s.selbergTerms (m / d * e) =
        ∑ e ∈ d.divisors, s.selbergTerms (m / d) * s.selbergTerms e := by
      apply Finset.sum_congr rfl
      intro e he
      apply BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
      exact hcop.of_dvd_right (Nat.mem_divisors.mp he).1
    _ = s.selbergTerms (m / d) * ∑ e ∈ d.divisors, s.selbergTerms e := by
      rw [Finset.mul_sum]
    _ = s.selbergTerms (m / d) * (s.selbergTerms d * (s.nu d)⁻¹) := by
      rw [sum_divisors_selbergTerms_eq s d (hdata.1.trans hdata.2.1)]
    _ = (s.nu d)⁻¹ * s.selbergTerms m := by
      rw [← mul_assoc,
        ← BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hcop,
        Nat.div_mul_cancel hdata.1]
      ring

private theorem levelSet_product_injective
    (s : BoundingSieve) (R d : ℕ) :
    Set.InjOn (fun x : ℕ × ℕ ↦ x.1 / d * x.2)
      ↑((levelSet s R).filter (fun n ↦ d ∣ n) ×ˢ d.divisors) := by
  rintro ⟨m, e⟩ hme ⟨n, f⟩ hnf heq
  change (m, e) ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ×ˢ d.divisors at hme
  change (n, f) ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ×ˢ d.divisors at hnf
  change m / d * e = n / d * f at heq
  have hme' : m ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ∧ e ∈ d.divisors := by
    exact Finset.mem_product.mp hme
  have hnf' : n ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ∧ f ∈ d.divisors := by
    exact Finset.mem_product.mp hnf
  have hmdata := mem_levelSet_filter_dvd hme'.1
  have hndata := mem_levelSet_filter_dvd hnf'.1
  have hm_coprime := div_coprime_of_mem_levelSet_filter_dvd hme'.1
  have hn_coprime := div_coprime_of_mem_levelSet_filter_dvd hnf'.1
  have he_dvd := (Nat.mem_divisors.mp hme'.2).1
  have hf_dvd := (Nat.mem_divisors.mp hnf'.2).1
  have hm_gcd : (m / d * e).gcd d = e :=
    Nat.gcd_mul_of_coprime_of_dvd hm_coprime he_dvd
  have hn_gcd : (n / d * f).gcd d = f :=
    Nat.gcd_mul_of_coprime_of_dvd hn_coprime hf_dvd
  have hef : e = f := by rw [← hm_gcd, heq, hn_gcd]
  subst f
  have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.mem_divisors.mp hme'.2).2 he_dvd
  have hdiv : m / d = n / d := Nat.mul_right_cancel (Nat.pos_of_ne_zero he0) heq
  apply Prod.ext
  · rw [← Nat.div_mul_cancel hmdata.1, ← Nat.div_mul_cancel hndata.1, hdiv]
  · rfl

private theorem levelSet_product_image_subset
    (s : BoundingSieve) (R d : ℕ) :
    Finset.image (fun x : ℕ × ℕ ↦ x.1 / d * x.2)
      ((levelSet s R).filter (fun n ↦ d ∣ n) ×ˢ d.divisors) ⊆ levelSet s R := by
  intro a ha
  obtain ⟨⟨m, e⟩, hme, rfl⟩ := Finset.mem_image.mp ha
  have hme' : m ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ∧ e ∈ d.divisors :=
    Finset.mem_product.mp hme
  have hdata := mem_levelSet_filter_dvd hme'.1
  have he_dvd := (Nat.mem_divisors.mp hme'.2).1
  have hdiv : m / d * e ∣ m := by
    conv_rhs => rw [← Nat.div_mul_cancel hdata.1]
    exact Nat.mul_dvd_mul_left (m / d) he_dvd
  have hm0 := ne_zero_of_dvd_ne_zero (BoundingSieve.prodPrimes_ne_zero (s := s)) hdata.2.1
  have hle : m / d * e ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdiv
  simp only [levelSet, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨hdiv.trans hdata.2.1, BoundingSieve.prodPrimes_ne_zero⟩,
    hle.trans hdata.2.2⟩

private theorem inv_nu_mul_levelSet_filter_sum_le_levelSum
    (s : BoundingSieve) (R d : ℕ) :
    (s.nu d)⁻¹ *
        ∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n), s.selbergTerms m ≤
      levelSum s R := by
  have hexpand :
      (s.nu d)⁻¹ *
          ∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n), s.selbergTerms m =
        ∑ x ∈ (levelSet s R).filter (fun n ↦ d ∣ n) ×ˢ d.divisors,
          s.selbergTerms (x.1 / d * x.2) := by
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (sum_divisors_selbergTerms_mul_div s R d m hm).symm
  change (s.nu d)⁻¹ *
      ∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n), s.selbergTerms m ≤
    ∑ m ∈ levelSet s R, s.selbergTerms m
  rw [hexpand]
  apply Finset.sum_le_sum_of_injOn (fun x : ℕ × ℕ ↦ x.1 / d * x.2)
  · exact levelSet_product_injective s R d
  · exact levelSet_product_image_subset s R d
  · intro x _
    exact le_rfl
  · intro m hm _
    simp only [levelSet, Finset.mem_filter, Nat.mem_divisors] at hm
    exact (BoundingSieve.selbergTerms_pos (s := s) hm.1.1).le

private theorem levelY_abs_le
    (s : BoundingSieve) (R m : ℕ) (hR : 1 ≤ R) (hm : m ∣ s.prodPrimes) :
    |levelY s R m| ≤
      if m ∈ levelSet s R then s.selbergTerms m / levelSum s R else 0 := by
  have hGpos : 0 < levelSum s R :=
    lt_of_lt_of_le zero_lt_one (levelSum_ge_one s R hR)
  unfold levelY
  by_cases hmem : m ∈ levelSet s R
  · rw [ite_eq_left hmem, ite_eq_left hmem, abs_div, abs_mul,
      abs_of_nonneg hGpos.le]
    rw [abs_of_nonneg (BoundingSieve.selbergTerms_pos (s := s) hm).le]
    calc
      |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * s.selbergTerms m /
          levelSum s R ≤ 1 * s.selbergTerms m / levelSum s R := by
        apply div_le_div_of_nonneg_right _ hGpos.le
        apply mul_le_mul_of_nonneg_right _
          (BoundingSieve.selbergTerms_pos (s := s) hm).le
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = s.selbergTerms m / levelSum s R := by ring
  · rw [ite_eq_right hmem, ite_eq_right hmem, abs_zero]

private theorem levelWeights_nu_mul_abs_le_filter
    (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    |s.nu d * levelWeights s R d| ≤
      (∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n), s.selbergTerms m) /
        levelSum s R := by
  have hcancel : s.nu d * levelWeights s R d =
      ∑ m ∈ s.prodPrimes.divisors,
        if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
          levelY s R m else 0 := by
    unfold levelWeights
    rw [← mul_assoc, mul_inv_cancel₀ (BoundingSieve.nu_ne_zero (s := s) hd), one_mul]
  rw [hcancel]
  have hterm : ∀ m ∈ s.prodPrimes.divisors,
      |if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
        levelY s R m else 0| ≤
        if m ∈ (levelSet s R).filter (fun n ↦ d ∣ n) then
          s.selbergTerms m / levelSum s R else 0 := by
    intro m hm
    have hmP := (Nat.mem_divisors.mp hm).1
    by_cases hdm : d ∣ m
    · rw [ite_eq_left hdm, abs_mul]
      have hY := levelY_abs_le s R m hR hmP
      calc
        |((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)| * |levelY s R m| ≤
            1 * |levelY s R m| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        _ ≤ if m ∈ levelSet s R then
            s.selbergTerms m / levelSum s R else 0 := by simpa using hY
        _ = if m ∈ (levelSet s R).filter (fun n ↦ d ∣ n) then
            s.selbergTerms m / levelSum s R else 0 := by
          simp only [Finset.mem_filter, hdm, and_true]
    · rw [ite_eq_right hdm, abs_zero]
      simp only [Finset.mem_filter, hdm, and_false, ↓reduceIte]
      exact le_rfl
  calc
    |∑ m ∈ s.prodPrimes.divisors, if d ∣ m then
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * levelY s R m else 0| ≤
        ∑ m ∈ s.prodPrimes.divisors, |if d ∣ m then
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * levelY s R m else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s.prodPrimes.divisors,
        if m ∈ (levelSet s R).filter (fun n ↦ d ∣ n) then
          s.selbergTerms m / levelSum s R else 0 := Finset.sum_le_sum hterm
    _ = ∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n),
        s.selbergTerms m / levelSum s R := by
      rw [← Finset.sum_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hm
        exact ⟨(Finset.mem_filter.mp hm.1).1, hm⟩
    _ = (∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n),
        s.selbergTerms m) / levelSum s R := by rw [Finset.sum_div]

/-- **Selberg level weights are bounded by one.** For a bounding sieve whose sifting primes have
product $P$, a natural number $R \ge 1$ and a divisor $d$ of $P$, the level-$R$ Selberg weight
$\lambda_d$ at $d$ satisfies $|\lambda_d| \le 1$. -/
theorem levelWeights_abs_le
    (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    |levelWeights s R d| ≤ 1 := by
  have hnupos := BoundingSieve.nu_pos_of_dvd_prodPrimes (s := s) hd
  have hGpos : 0 < levelSum s R :=
    lt_of_lt_of_le zero_lt_one (levelSum_ge_one s R hR)
  have hweighted := levelWeights_nu_mul_abs_le_filter s R d hR hd
  have hsubset := inv_nu_mul_levelSet_filter_sum_le_levelSum s R d
  calc
    |levelWeights s R d| = |s.nu d * levelWeights s R d| / s.nu d := by
      rw [eq_div_iff hnupos.ne']
      rw [abs_mul, abs_of_pos hnupos, mul_comm]
    _ ≤ ((∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n),
        s.selbergTerms m) / levelSum s R) / s.nu d :=
      div_le_div_of_nonneg_right hweighted hnupos.le
    _ = ((s.nu d)⁻¹ *
        ∑ m ∈ (levelSet s R).filter (fun n ↦ d ∣ n),
          s.selbergTerms m) / levelSum s R := by
      field_simp
    _ ≤ levelSum s R / levelSum s R :=
      div_le_div_of_nonneg_right hsubset hGpos.le
    _ = 1 := div_self hGpos.ne'

/-- If `1 ≤ d * s.nu d`, then the absolute value of the level weight at `d` is at most `d`. -/
private theorem levelWeights_abs_le_nat
    (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes)
    (hnu : 1 ≤ (d : ℝ) * s.nu d) :
    |levelWeights s R d| ≤ d := by
  have hnupos := BoundingSieve.nu_pos_of_dvd_prodPrimes (s := s) hd
  have hnuw := levelWeights_nu_mul_abs_le s R d hR hd
  have hnuabs : |s.nu d| = s.nu d := abs_of_pos hnupos
  have hinv : (s.nu d)⁻¹ ≤ (d : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hnupos]
    exact hnu
  calc
    |levelWeights s R d| =
        |s.nu d * levelWeights s R d| / s.nu d := by
      rw [eq_div_iff hnupos.ne']
      rw [abs_mul, hnuabs, mul_comm]
    _ ≤ 1 / s.nu d := div_le_div_of_nonneg_right hnuw hnupos.le
    _ = (s.nu d)⁻¹ := one_div _
    _ ≤ (d : ℝ) := hinv

/-- **Support of the Selberg level weights.** For every bounding sieve and all natural numbers $R$
and $d$, if the level-$R$ Selberg weight $\lambda_d$ at $d$ is nonzero, then $d \le R$. -/
theorem levelWeights_support
    (s : BoundingSieve) (R d : ℕ)
    (hd : levelWeights s R d ≠ 0) : d ≤ R := by
  have hP0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hsum : (∑ m ∈ s.prodPrimes.divisors,
      if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
        levelY s R m else 0) ≠ 0 := by
    intro hzero
    apply hd
    unfold levelWeights
    rw [hzero, mul_zero]
  have hex : ∃ m ∈ s.prodPrimes.divisors,
      (if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
        levelY s R m else 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (Finset.sum_eq_zero h)
  obtain ⟨m, hm, hterm⟩ := hex
  by_cases hdm : d ∣ m
  · rw [ite_eq_left hdm] at hterm
    have hY : levelY s R m ≠ 0 := by
      intro hzero
      exact hterm (by rw [hzero, mul_zero])
    unfold levelY at hY
    by_cases hmem : m ∈ levelSet s R
    · have hmR := (Finset.mem_filter.mp hmem).2
      rw [Nat.mem_divisors] at hm
      have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hm.1
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm).trans hmR
    · rw [ite_eq_right hmem] at hY
      exact (hY rfl).elim
  · rw [ite_eq_right hdm] at hterm
    exact (hterm rfl).elim

private theorem lambdaSquared_abs_le
    (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R)
    (hnu : ∀ e : ℕ, e ∣ s.prodPrimes → 1 ≤ (e : ℝ) * s.nu e)
    (hd : d ∣ s.prodPrimes) :
    |BoundingSieve.lambdaSquared (levelWeights s R) d| ≤ (d : ℝ) ^ 4 := by
  have hP0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hd0 := ne_zero_of_dvd_ne_zero hP0 hd
  have hdpos := Nat.pos_of_ne_zero hd0
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = Nat.lcm d1 d2 then levelWeights s R d1 *
          levelWeights s R d2 else 0| ≤
        ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then levelWeights s R d1 *
            levelWeights s R d2 else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        |if d = Nat.lcm d1 d2 then levelWeights s R d1 *
          levelWeights s R d2 else 0| :=
      Finset.sum_le_sum fun d1 _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d1 ∈ d.divisors, ∑ _d2 ∈ d.divisors, (d : ℝ) * d := by
      apply Finset.sum_le_sum
      intro d1 hd1
      apply Finset.sum_le_sum
      intro d2 hd2
      by_cases heq : d = Nat.lcm d1 d2
      · rw [ite_eq_left heq, abs_mul]
        rw [Nat.mem_divisors] at hd1 hd2
        have hd1P := hd1.1.trans hd
        have hd2P := hd2.1.trans hd
        have hw1 := levelWeights_abs_le_nat s R d1 hR hd1P (hnu d1 hd1P)
        have hw2 := levelWeights_abs_le_nat s R d2 hR hd2P (hnu d2 hd2P)
        have hd1d : (d1 : ℝ) ≤ d := by
          exact_mod_cast Nat.le_of_dvd hdpos hd1.1
        have hd2d : (d2 : ℝ) ≤ d := by
          exact_mod_cast Nat.le_of_dvd hdpos hd2.1
        exact mul_le_mul (hw1.trans hd1d) (hw2.trans hd2d)
          (abs_nonneg _) (Nat.cast_nonneg _)
      · rw [ite_eq_right heq, abs_zero]
        positivity
    _ = ((d.divisors.card : ℝ) * d.divisors.card) * ((d : ℝ) * d) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((d : ℝ) * d) * ((d : ℝ) * d) := by
      have hcard : (d.divisors.card : ℝ) ≤ d := by
        exact_mod_cast Nat.card_divisors_le_self d
      have hsq : (d.divisors.card : ℝ) * d.divisors.card ≤ (d : ℝ) * d := by
        exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (d : ℝ) ^ 4 := by ring

private theorem lambdaSquared_support
    (s : BoundingSieve) (R d : ℕ)
    (hd : BoundingSieve.lambdaSquared (levelWeights s R) d ≠ 0) :
    d ≤ R ^ 2 := by
  unfold BoundingSieve.lambdaSquared at hd
  have hex : ∃ d1 ∈ d.divisors, ∃ d2 ∈ d.divisors,
      (if d = Nat.lcm d1 d2 then levelWeights s R d1 *
        levelWeights s R d2 else 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hd
    apply Finset.sum_eq_zero
    intro d1 hd1
    exact Finset.sum_eq_zero fun d2 hd2 ↦ h d1 hd1 d2 hd2
  obtain ⟨d1, -, d2, -, hterm⟩ := hex
  by_cases heq : d = Nat.lcm d1 d2
  · rw [ite_eq_left heq] at hterm
    have hw1 : levelWeights s R d1 ≠ 0 := by
      intro hzero
      exact hterm (by rw [hzero, zero_mul])
    have hw2 : levelWeights s R d2 ≠ 0 := by
      intro hzero
      exact hterm (by rw [hzero, mul_zero])
    have hd1R := levelWeights_support s R d1 hw1
    have hd2R := levelWeights_support s R d2 hw2
    have hd10 : d1 ≠ 0 := by
      intro hzero
      subst d1
      have hnu0 : s.nu 0 = 0 := s.nu.map_zero'
      unfold levelWeights at hw1
      rw [hnu0, inv_zero, zero_mul] at hw1
      exact hw1 rfl
    have hd20 : d2 ≠ 0 := by
      intro hzero
      subst d2
      have hnu0 : s.nu 0 = 0 := s.nu.map_zero'
      unfold levelWeights at hw2
      rw [hnu0, inv_zero, zero_mul] at hw2
      exact hw2 rfl
    have hlcm : d ∣ d1 * d2 := by
      rw [heq]
      exact Nat.lcm_dvd_mul d1 d2
    calc
      d ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hd10.bot_lt hd20.bot_lt) hlcm
      _ ≤ R * R := Nat.mul_le_mul hd1R hd2R
      _ = R ^ 2 := by ring
  · rw [ite_eq_right heq] at hterm
    exact (hterm rfl).elim

/-- **Error bound for the Selberg level weights.** Take a bounding sieve whose sifting primes have
product $P$, with density function $\nu$ and remainders $r_d = A_d - \nu(d) X$, where $A_d$ is the
total weight of the multiples of $d$ in the set to be sifted and $X$ approximates its total
weight. Let $R \ge 1$ be a natural number and suppose that $d\,\nu(d) \ge 1$ and $|r_d| \le d$ for
every divisor $d$ of $P$. Let $\lambda_d$ be the level-$R$ Selberg weights and
$\Lambda_d = \sum_{d_1, d_2 \mid d,\ \operatorname{lcm}(d_1, d_2) = d} \lambda_{d_1} \lambda_{d_2}$
their $\Lambda^2$ coefficients. Then $\sum_{d \mid P} |\Lambda_d|\,|r_d| \le R^{12}$. -/
theorem levelWeights_errSum_le
    (s : BoundingSieve) (R : ℕ) (hR : 1 ≤ R)
    (hnu : ∀ d : ℕ, d ∣ s.prodPrimes → 1 ≤ (d : ℝ) * s.nu d)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
    s.errSum (BoundingSieve.lambdaSquared (levelWeights s R)) ≤
      (R : ℝ) ^ 12 := by
  have hP0 := BoundingSieve.prodPrimes_ne_zero (s := s)
  have heach : ∀ d ∈ s.prodPrimes.divisors,
      |BoundingSieve.lambdaSquared (levelWeights s R) d| *
          |s.rem d| ≤
        if d ≤ R ^ 2 then (d : ℝ) ^ 4 * d else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    by_cases hdR : d ≤ R ^ 2
    · rw [ite_eq_left hdR]
      exact mul_le_mul (lambdaSquared_abs_le s R d hR hnu hd.1)
        (hrem d hd.1) (abs_nonneg _) (by positivity)
    · rw [ite_eq_right hdR]
      have hlam : BoundingSieve.lambdaSquared
          (levelWeights s R) d = 0 := by
        by_contra hzero
        exact hdR (lambdaSquared_support s R d hzero)
      rw [hlam, abs_zero, zero_mul]
  calc
    s.errSum (BoundingSieve.lambdaSquared (levelWeights s R)) =
        ∑ d ∈ s.prodPrimes.divisors,
          |BoundingSieve.lambdaSquared (levelWeights s R) d| *
            |s.rem d| := rfl
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ R ^ 2 then (d : ℝ) ^ 4 * d else 0 := Finset.sum_le_sum heach
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ R ^ 2),
        (d : ℝ) ^ 4 * d := by rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.Icc 1 (R ^ 2), (d : ℝ) ^ 4 * d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
        exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hd.1.1), hd.2⟩
      · intro d _ _
        positivity
    _ ≤ ((Finset.Icc 1 (R ^ 2)).card : ℝ) *
        (((R ^ 2 : ℕ) : ℝ) ^ 4 * (R ^ 2 : ℕ)) := by
      have hle : ∀ d ∈ Finset.Icc 1 (R ^ 2),
          (d : ℝ) ^ 4 * d ≤ (((R ^ 2 : ℕ) : ℝ) ^ 4 * (R ^ 2 : ℕ)) := by
        intro d hd
        have hdR : (d : ℝ) ≤ (R ^ 2 : ℕ) := by
          exact_mod_cast (Finset.mem_Icc.mp hd).2
        exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg d) hdR 4) hdR
          (Nat.cast_nonneg _) (by positivity)
      have h := Finset.sum_le_card_nsmul (Finset.Icc 1 (R ^ 2))
        (fun d ↦ (d : ℝ) ^ 4 * d)
        (((R ^ 2 : ℕ) : ℝ) ^ 4 * (R ^ 2 : ℕ)) hle
      rw [nsmul_eq_mul] at h
      exact h
    _ = (R : ℝ) ^ 12 := by
      rw [Nat.card_Icc]
      simp only [Nat.add_sub_cancel, Nat.cast_pow]
      ring

end MathlibExt.SelbergSieve
