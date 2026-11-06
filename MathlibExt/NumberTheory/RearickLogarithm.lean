/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.IntervalCases

/-! Source: Rearick logarithm support characterization of multiplicative
arithmetic functions, after Huilan Li and Trueman MacHenry,
arXiv:1009.1892v1, <https://arxiv.org/abs/1009.1892>, lines 444-450
(Rearick logarithm definition) and 706-708 (Rearick Theorem 4). Real-valued
domain closure with `f 1 > 0` after Pong, arXiv:1504.03263v2,
<https://arxiv.org/abs/1504.03263>, lines 174-195; positivity also supplies
the nonzero premise for the Dirichlet inverse. -/

@[expose] public section

namespace MetaMathlibExt

set_option backward.proofsInPublic true in
/-- **Rearick logarithm.** Let $f$ be a real-valued arithmetic function with $f(1) > 0$, and let
$f^{-1}$ be its Dirichlet inverse. The Rearick logarithm of $f$ is the arithmetic function $L(f)$
with $L(f)(0) = 0$, $L(f)(1) = \log f(1)$, and
$L(f)(n) = \sum_{d \mid n} f(d) \, f^{-1}(n/d) \log d$ for $n > 1$. -/
noncomputable def rearickLog (f : ArithmeticFunction ℝ) (hf : 0 < f 1) :
    ArithmeticFunction ℝ :=
  ⟨fun n =>
    if n = 0 then 0
    else if n = 1 then Real.log (f 1)
    else
      ∑ d ∈ n.divisors,
        f d *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) (n / d) *
          Real.log (d : ℝ),
    by simp⟩

@[simp]
theorem rearickLog_zero (f : ArithmeticFunction ℝ) (hf : 0 < f 1) : rearickLog f hf 0 = 0 := rfl

@[simp]
theorem rearickLog_one (f : ArithmeticFunction ℝ) (hf : 0 < f 1) :
    rearickLog f hf 1 = Real.log (f 1) := rfl

theorem rearickLog_apply_of_one_lt (f : ArithmeticFunction ℝ) (hf : 0 < f 1) {n : ℕ}
    (hn : 1 < n) :
    rearickLog f hf n =
      ∑ d ∈ n.divisors,
        f d *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) (n / d) *
          Real.log (d : ℝ) := by
  change (if n = 0 then (0 : ℝ) else if n = 1 then _ else _) = _
  simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, ↓reduceIte]

private theorem pp_dvd_or (d a b : ℕ) (hdiv : d ∣ a * b) (hpp : IsPrimePow d)
    (hcop : Nat.Coprime a b) : d ∣ a ∨ d ∣ b := by
  obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff d).mp hpp
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [pow_zero] at heq
    rw [← heq]
    exact Or.inl (one_dvd a)
  · have hpdvd : p ∣ d := heq ▸ dvd_pow_self p hk0
    have hpab : p ∣ a * b := dvd_trans hpdvd hdiv
    rw [hp.dvd_mul] at hpab
    rcases hpab with hpa | hpb
    · have hpcop : Nat.Coprime p b :=
        Nat.Coprime.coprime_dvd_left hpa hcop
      have hdcop : Nat.Coprime d b := heq ▸ hpcop.pow_left k
      exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right hdcop hdiv)
    · have hpcop : Nat.Coprime p a :=
        Nat.Coprime.coprime_dvd_left hpb hcop.symm
      have hdcop : Nat.Coprime d a := heq ▸ hpcop.pow_left k
      exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left hdcop hdiv)

private theorem pp_divisors_union (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) :
    (a * b).divisors.filter IsPrimePow =
      (a.divisors.filter IsPrimePow) ∪ (b.divisors.filter IsPrimePow) := by
  have hN : a * b ≠ 0 := mul_ne_zero ha hb
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_union]
  constructor
  · rintro ⟨⟨hdiv, -⟩, hpp⟩
    rcases pp_dvd_or d a b hdiv hpp hcop with hda | hdb
    · exact Or.inl ⟨⟨hda, ha⟩, hpp⟩
    · exact Or.inr ⟨⟨hdb, hb⟩, hpp⟩
  · rintro (⟨⟨hda, -⟩, hpp⟩ | ⟨⟨hdb, -⟩, hpp⟩)
    · exact ⟨⟨dvd_trans hda (dvd_mul_right a b), hN⟩, hpp⟩
    · exact ⟨⟨dvd_trans hdb (dvd_mul_left b a), hN⟩, hpp⟩

private theorem not_pp_mul (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hcop : Nat.Coprime a b) : ¬ IsPrimePow (a * b) := by
  rintro hpp
  obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff (a * b)).mp hpp
  have haN : a ∣ p ^ k := heq ▸ dvd_mul_right a b
  have hbN : b ∣ p ^ k := heq ▸ dvd_mul_left b a
  rw [Nat.dvd_prime_pow hp] at haN hbN
  obtain ⟨j, hjk, haj⟩ := haN
  obtain ⟨l, hlk, hbj⟩ := hbN
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at haj
      omega
    · exact h
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with rfl | h
    · simp at hbj
      omega
    · exact h
  have hpa : p ∣ a := haj ▸ dvd_pow_self p (ne_of_gt hj)
  have hpb : p ∣ b := hbj ▸ dvd_pow_self p (ne_of_gt hl)
  have hpgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [hcop.gcd_eq_one] at hpgcd
  exact hp.ne_one (Nat.dvd_one.mp hpgcd)

private theorem exists_coprime_mul (N : ℕ) (hN1 : 1 < N) (hpp : ¬ IsPrimePow N) :
    ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ Nat.Coprime a b ∧ a * b = N := by
  have hNe1 : N ≠ 1 := ne_of_gt hN1
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hN1)
  set p := N.minFac with hpdef
  have hp : Nat.Prime p := Nat.minFac_prime hNe1
  have hdvd : p ∣ N := Nat.minFac_dvd N
  have hkpos : 0 < N.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hN0 hdvd
  set k := N.factorization p with hkdef
  set a := p ^ k with hadef
  set b := N / a with hbdef
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have ha1 : 1 < a := Nat.one_lt_pow hkne hp.one_lt
  have hadvd : a ∣ N := Nat.ordProj_dvd N p
  have hab : a * b = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop_base : Nat.Coprime p b := Nat.coprime_ordCompl hp hN0
  have hcop : Nat.Coprime a b := hcop_base.pow_left k
  have hb1 : 1 < b := by
    by_contra hbcon
    push Not at hbcon
    interval_cases b
    · omega
    · simp only [mul_one] at hab
      have heq : p ^ k = N := by rw [← hab, hadef]
      exact hpp ((isPrimePow_nat_iff N).mpr ⟨p, k, hp, hkpos, heq⟩)
  exact ⟨a, b, ha1, hb1, hcop, hab⟩

/-- **The Rearick logarithm as a Dirichlet convolution.** Let $f$ be a real-valued arithmetic
function with $f(1) = 1$, and let $f^{-1}$ be its Dirichlet inverse. Then the Rearick logarithm
of $f$ is the Dirichlet convolution of the pointwise product $n \mapsto f(n) \log n$ with
$f^{-1}$. -/
theorem rearickLog_eq_pmul_log_mul_dirichletInverse (f : ArithmeticFunction ℝ) (hf : 0 < f 1)
    (h1 : f 1 = 1) :
    rearickLog f hf =
      f.pmul ArithmeticFunction.log *
        ArithmeticFunction.dirichletInverse (⇑f) (invertibleOfNonzero (ne_of_gt hf)) := by
  ext n
  by_cases hn0 : n = 0
  · subst hn0
    have hL0 : rearickLog f hf 0 = 0 := rfl
    rw [hL0]
    rw [ArithmeticFunction.mul_apply]
    simp
  by_cases hn1 : n = 1
  · subst hn1
    have hlog : Real.log (f 1) = 0 := by rw [h1, Real.log_one]
    have hL1 : rearickLog f hf 1 = 0 := by
      have h : rearickLog f hf 1 = Real.log (f 1) := rfl
      rw [h, hlog]
    rw [hL1]
    rw [ArithmeticFunction.mul_apply_one]
    have hH1 : (f.pmul ArithmeticFunction.log) 1 = 0 := by
      simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
    rw [hH1, zero_mul]
  · have hL : rearickLog f hf n =
      ∑ d ∈ n.divisors,
        f d *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) (n / d) *
          Real.log (d : ℝ) := by
      change (if n = 0 then (0 : ℝ) else if n = 1 then _ else _) = _
      simp only [hn0, hn1, ↓reduceIte]
    rw [hL]
    have hR : (f.pmul ArithmeticFunction.log *
        ArithmeticFunction.dirichletInverse (⇑f) (invertibleOfNonzero (ne_of_gt hf))) n =
      ∑ d ∈ n.divisors,
        (f.pmul ArithmeticFunction.log) d *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) (n / d) := by
      rw [ArithmeticFunction.mul_apply]
      exact Nat.sum_divisorsAntidiagonal (fun x y =>
        (f.pmul ArithmeticFunction.log) x *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) y)
    rw [hR]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
    ring

private theorem rearickLog_conv_mul (f : ArithmeticFunction ℝ) (hf : 0 < f 1) (h1 : f 1 = 1) :
    rearickLog f hf * f = f.pmul ArithmeticFunction.log := by
  rw [rearickLog_eq_pmul_log_mul_dirichletInverse f hf h1, mul_assoc,
    ArithmeticFunction.dirichletInverse_mul_self f
      (invertibleOfNonzero (ne_of_gt hf)), mul_one]

private theorem rearickLog_sum_eq (f : ArithmeticFunction ℝ) (hf : 0 < f 1) (h1 : f 1 = 1) (n : ℕ) :
    f n * Real.log (n : ℝ) =
      ∑ d ∈ n.divisors, rearickLog f hf d * f (n / d) := by
  have h : (f.pmul ArithmeticFunction.log) n = (rearickLog f hf * f) n := by
    rw [rearickLog_conv_mul f hf h1]
  have hpmul : (f.pmul ArithmeticFunction.log) n = f n * Real.log (n : ℝ) := by
    simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
  rw [hpmul] at h
  rw [h]
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun x y => rearickLog f hf x * f y)

private theorem f1_of_hL (f : ArithmeticFunction ℝ) (hf : 0 < f 1)
    (hL : ∀ m : ℕ, ¬ IsPrimePow m → rearickLog f hf m = 0) : f 1 = 1 := by
  have h1 : ¬ IsPrimePow (1 : ℕ) := not_isPrimePow_one
  have hL1 : rearickLog f hf 1 = 0 := hL 1 h1
  have hlog : Real.log (f 1) = 0 := hL1
  have hexp : Real.exp (Real.log (f 1)) = f 1 := Real.exp_log hf
  rw [hlog, Real.exp_zero] at hexp
  exact hexp.symm

private theorem div_mul_right_eq (a b d : ℕ) (hda : d ∣ a) :
    (a * b) / d = (a / d) * b := by
  rw [mul_comm a b, Nat.mul_div_assoc b hda, mul_comm b (a / d)]

private theorem div_mul_left_eq (a b d : ℕ) (hdb : d ∣ b) :
    (a * b) / d = a * (b / d) :=
  Nat.mul_div_assoc a hdb

private theorem lt_of_mul_right (a b : ℕ) (haPos : 0 < a) (hb1 : 1 < b) (N : ℕ) (hab : a * b = N) :
    a < N := by
  rw [← hab]
  exact lt_mul_of_one_lt_right haPos hb1

private theorem lt_of_mul_left (a b : ℕ) (hbPos : 0 < b) (ha1 : 1 < a) (N : ℕ) (hab : a * b = N) :
    b < N := by
  rw [← hab, mul_comm a b]
  exact lt_mul_of_one_lt_right hbPos ha1

private theorem forward_vanish (f : ArithmeticFunction ℝ) (hf : 0 < f 1)
    (hmult : f.IsMultiplicative) (N : ℕ) (hN : ¬ IsPrimePow N) :
    rearickLog f hf N = 0 := by
  have h1 : f 1 = 1 := hmult.1
  suffices h : ∀ N, ¬ IsPrimePow N → rearickLog f hf N = 0 from h N hN
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hNpp
    rcases eq_or_ne N 0 with rfl | hN0
    · rfl
    rcases eq_or_ne N 1 with rfl | hN1
    · have hlog : rearickLog f hf 1 = Real.log (f 1) := rfl
      rw [hlog, h1, Real.log_one]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hN1lt : 1 < N := by omega
      obtain ⟨a, b, ha1, hb1, hcop, hab⟩ := exists_coprime_mul N hN1lt hNpp
      have haPos : 0 < a := lt_trans Nat.zero_lt_one ha1
      have hbPos : 0 < b := lt_trans Nat.zero_lt_one hb1
      have ha0 : a ≠ 0 := ne_of_gt haPos
      have hb0 : b ≠ 0 := ne_of_gt hbPos
      have haN : a < N := lt_of_mul_right a b haPos hb1 N hab
      have hbN : b < N := lt_of_mul_left a b hbPos ha1 N hab
      have hE := rearickLog_sum_eq f hf h1 N
      have hNmem : N ∈ N.divisors := Nat.mem_divisors_self N hN0
      have hNN : N / N = 1 := Nat.div_self hNpos
      have hsplit : ∑ d ∈ N.divisors, rearickLog f hf d * f (N / d) =
          rearickLog f hf N + ∑ d ∈ N.divisors.erase N, rearickLog f hf d * f (N / d) := by
        have h := Finset.add_sum_erase N.divisors (fun d => rearickLog f hf d * f (N / d)) hNmem
        rw [hNN, h1, mul_one] at h
        exact h.symm
      rw [hsplit] at hE
      have hS : ∑ d ∈ N.divisors.erase N, rearickLog f hf d * f (N / d)
          = f N * Real.log (N : ℝ) := by
        have hsub1 : N.divisors.filter IsPrimePow ⊆ N.divisors.erase N := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors] at hd ⊢
          obtain ⟨⟨hdiv, hNne⟩, hpp⟩ := hd
          refine ⟨?_, ⟨hdiv, hNne⟩⟩
          intro hdeq
          rw [hdeq] at hpp
          exact hNpp hpp
        have hvan1 : ∀ x ∈ N.divisors.erase N,
            x ∉ N.divisors.filter IsPrimePow → rearickLog f hf x * f (N / x) = 0 := by
          intro x hx hx_not
          have hx_mem : x ∈ N.divisors := Finset.mem_of_mem_erase hx
          have hx_pp : ¬ IsPrimePow x := by
            intro hpp
            exact hx_not (Finset.mem_filter.mpr ⟨hx_mem, hpp⟩)
          have hx_dvd : x ∣ N := (Nat.mem_divisors.mp hx_mem).1
          have hx_le : x ≤ N := Nat.le_of_dvd hNpos hx_dvd
          have hx_ne : x ≠ N := (Finset.mem_erase.mp hx).1
          have hx_lt : x < N := lt_of_le_of_ne hx_le hx_ne
          have hLx : rearickLog f hf x = 0 := ih x hx_lt hx_pp
          rw [hLx, zero_mul]
        have hfilter_eq : ∑ d ∈ N.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
            ∑ d ∈ N.divisors.erase N, rearickLog f hf d * f (N / d) :=
          Finset.sum_subset hsub1 hvan1
        have hunion : N.divisors.filter IsPrimePow =
            (a.divisors.filter IsPrimePow) ∪ (b.divisors.filter IsPrimePow) := by
          have h := pp_divisors_union a b ha0 hb0 hcop
          rw [hab] at h
          exact h
        have hdisj := Nat.disjoint_divisors_filter_isPrimePow hcop
        have hEa := rearickLog_sum_eq f hf h1 a
        have hEb := rearickLog_sum_eq f hf h1 b
        have hfab : f N = f a * f b := hab ▸ hmult.2 hcop
        have haNe : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
        have hbNe : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
        have hcast : (N : ℝ) = (a : ℝ) * (b : ℝ) := by rw [← hab, Nat.cast_mul]
        have hlogN : Real.log (N : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
          rw [hcast, Real.log_mul haNe hbNe]
        have hA_eq : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (a / d) =
            f a * Real.log (a : ℝ) := by
          have hsubA : a.divisors.filter IsPrimePow ⊆ a.divisors := Finset.filter_subset _ _
          have hvanA : ∀ x ∈ a.divisors, x ∉ a.divisors.filter IsPrimePow →
              rearickLog f hf x * f (a / x) = 0 := by
            intro x hx hx_not
            have hx_pp : ¬ IsPrimePow x := by
              intro hpp
              exact hx_not (Finset.mem_filter.mpr ⟨hx, hpp⟩)
            have hx_dvd : x ∣ a := (Nat.mem_divisors.mp hx).1
            have hx_le : x ≤ a := Nat.le_of_dvd haPos hx_dvd
            have hx_lt : x < N := lt_of_le_of_lt hx_le haN
            have hLx : rearickLog f hf x = 0 := ih x hx_lt hx_pp
            rw [hLx, zero_mul]
          have hsub_eq : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (a / d) =
              ∑ d ∈ a.divisors, rearickLog f hf d * f (a / d) :=
            Finset.sum_subset hsubA hvanA
          rw [hsub_eq]
          exact hEa.symm
        have hB_eq : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (b / d) =
            f b * Real.log (b : ℝ) := by
          have hsubB : b.divisors.filter IsPrimePow ⊆ b.divisors := Finset.filter_subset _ _
          have hvanB : ∀ x ∈ b.divisors, x ∉ b.divisors.filter IsPrimePow →
              rearickLog f hf x * f (b / x) = 0 := by
            intro x hx hx_not
            have hx_pp : ¬ IsPrimePow x := by
              intro hpp
              exact hx_not (Finset.mem_filter.mpr ⟨hx, hpp⟩)
            have hx_dvd : x ∣ b := (Nat.mem_divisors.mp hx).1
            have hx_le : x ≤ b := Nat.le_of_dvd hbPos hx_dvd
            have hx_lt : x < N := lt_of_le_of_lt hx_le hbN
            have hLx : rearickLog f hf x = 0 := ih x hx_lt hx_pp
            rw [hLx, zero_mul]
          have hsub_eq : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (b / d) =
              ∑ d ∈ b.divisors, rearickLog f hf d * f (b / d) :=
            Finset.sum_subset hsubB hvanB
          rw [hsub_eq]
          exact hEb.symm
        have hA_rw : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
            (f a * Real.log (a : ℝ)) * f b := by
          have hstep : ∀ d ∈ a.divisors.filter IsPrimePow,
              rearickLog f hf d * f (N / d) = (rearickLog f hf d * f (a / d)) * f b := by
            intro d hd
            have hd_mem : d ∈ a.divisors := Finset.mem_of_mem_filter d hd
            have hda : d ∣ a := (Nat.mem_divisors.mp hd_mem).1
            have hNd : N / d = (a / d) * b := by
              rw [← hab]
              exact div_mul_right_eq a b d hda
            have hdiv : (a / d) ∣ a := Nat.div_dvd_of_dvd hda
            have hcopd : Nat.Coprime (a / d) b :=
              Nat.Coprime.coprime_dvd_left hdiv hcop
            have hmultd : f ((a / d) * b) = f (a / d) * f b := hmult.2 hcopd
            rw [hNd, hmultd]
            ring
          rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hA_eq]
        have hB_rw : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
            f a * (f b * Real.log (b : ℝ)) := by
          have hstep : ∀ d ∈ b.divisors.filter IsPrimePow,
              rearickLog f hf d * f (N / d) = f a * (rearickLog f hf d * f (b / d)) := by
            intro d hd
            have hd_mem : d ∈ b.divisors := Finset.mem_of_mem_filter d hd
            have hdb : d ∣ b := (Nat.mem_divisors.mp hd_mem).1
            have hNd : N / d = a * (b / d) := by
              rw [← hab]
              exact div_mul_left_eq a b d hdb
            have hdiv : (b / d) ∣ b := Nat.div_dvd_of_dvd hdb
            have hcopd : Nat.Coprime a (b / d) :=
              (Nat.Coprime.coprime_dvd_left hdiv hcop.symm).symm
            have hmultd : f (a * (b / d)) = f a * f (b / d) := hmult.2 hcopd
            rw [hNd, hmultd]
            ring
          have hsum : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
              ∑ d ∈ b.divisors.filter IsPrimePow, f a * (rearickLog f hf d * f (b / d)) :=
            Finset.sum_congr rfl hstep
          rw [hsum, ← Finset.mul_sum, hB_eq]
        rw [← hfilter_eq, hunion, Finset.sum_union hdisj, hA_rw, hB_rw, hfab, hlogN]
        ring
      rw [hS] at hE
      linarith

private theorem reverse_mult_aux (f : ArithmeticFunction ℝ) (hf : 0 < f 1)
    (hL : ∀ m, ¬ IsPrimePow m → rearickLog f hf m = 0)
    (h1 : f 1 = 1) (N : ℕ) :
    ∀ a b, a * b = N → Nat.Coprime a b → f N = f a * f b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b hab hcop
    rcases eq_or_ne N 0 with rfl | hN0
    · rcases Nat.mul_eq_zero.mp hab with rfl | rfl
      · simp [ArithmeticFunction.map_zero]
      · simp [ArithmeticFunction.map_zero]
    rcases eq_or_ne N 1 with rfl | hN1
    · have ha1 : a = 1 := Nat.eq_one_of_dvd_one (hab ▸ dvd_mul_right a b)
      have hb1 : b = 1 := Nat.eq_one_of_dvd_one (hab ▸ dvd_mul_left b a)
      simp [ha1, hb1, h1]
    · rcases eq_or_ne a 1 with rfl | ha1ne
      · have hbN : b = N := by rw [← hab, one_mul]
        rw [hbN, h1, one_mul]
      · rcases eq_or_ne b 1 with rfl | hb1ne
        · have haN : a = N := by rw [← hab, mul_one]
          rw [haN, h1, mul_one]
        · have ha0 : a ≠ 0 := by
            intro ha0
            rw [ha0, zero_mul] at hab
            exact hN0 hab.symm
          have hb0 : b ≠ 0 := by
            intro hb0
            rw [hb0, mul_zero] at hab
            exact hN0 hab.symm
          have haPos : 0 < a := Nat.pos_of_ne_zero ha0
          have hbPos : 0 < b := Nat.pos_of_ne_zero hb0
          have ha1 : 1 < a := by omega
          have hb1 : 1 < b := by omega
          have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
          have hN1lt : 1 < N := hab ▸ one_lt_mul (le_of_lt ha1) hb1
          have hNpp : ¬ IsPrimePow N := hab ▸ not_pp_mul a b ha1 hb1 hcop
          have hE := rearickLog_sum_eq f hf h1 N
          have hEa := rearickLog_sum_eq f hf h1 a
          have hEb := rearickLog_sum_eq f hf h1 b
          have haNe : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
          have hbNe : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
          have hNNe : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
          have hcast : (N : ℝ) = (a : ℝ) * (b : ℝ) := by rw [← hab, Nat.cast_mul]
          have hlogN : Real.log (N : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
            rw [hcast, Real.log_mul haNe hbNe]
          have hNcast1 : (1 : ℝ) < (N : ℝ) := by
            rw [← Nat.cast_one]
            exact Nat.cast_lt.mpr hN1lt
          have hlogPos : 0 < Real.log (N : ℝ) := Real.log_pos hNcast1
          have hlogNe : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogPos
          have hAllFilter : ∑ d ∈ N.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
              ∑ d ∈ N.divisors, rearickLog f hf d * f (N / d) :=
            Finset.sum_subset (Finset.filter_subset _ _) (by
              intro x hx hx_not
              have hx_pp : ¬ IsPrimePow x := by
                intro hpp
                exact hx_not (Finset.mem_filter.mpr ⟨hx, hpp⟩)
              have hLx : rearickLog f hf x = 0 := hL x hx_pp
              rw [hLx, zero_mul])
          have hunion : N.divisors.filter IsPrimePow =
              (a.divisors.filter IsPrimePow) ∪ (b.divisors.filter IsPrimePow) := by
            have h := pp_divisors_union a b ha0 hb0 hcop
            rw [hab] at h
            exact h
          have hdisj := Nat.disjoint_divisors_filter_isPrimePow hcop
          have hA_eq : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (a / d) =
              f a * Real.log (a : ℝ) := by
            have hsubA : a.divisors.filter IsPrimePow ⊆ a.divisors := Finset.filter_subset _ _
            have hvanA : ∀ x ∈ a.divisors, x ∉ a.divisors.filter IsPrimePow →
                rearickLog f hf x * f (a / x) = 0 := by
              intro x hx hx_not
              have hx_pp : ¬ IsPrimePow x := by
                intro hpp
                exact hx_not (Finset.mem_filter.mpr ⟨hx, hpp⟩)
              have hLx : rearickLog f hf x = 0 := hL x hx_pp
              rw [hLx, zero_mul]
            have hsub_eq : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (a / d) =
                ∑ d ∈ a.divisors, rearickLog f hf d * f (a / d) :=
              Finset.sum_subset hsubA hvanA
            rw [hsub_eq]
            exact hEa.symm
          have hB_eq : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (b / d) =
              f b * Real.log (b : ℝ) := by
            have hsubB : b.divisors.filter IsPrimePow ⊆ b.divisors := Finset.filter_subset _ _
            have hvanB : ∀ x ∈ b.divisors, x ∉ b.divisors.filter IsPrimePow →
                rearickLog f hf x * f (b / x) = 0 := by
              intro x hx hx_not
              have hx_pp : ¬ IsPrimePow x := by
                intro hpp
                exact hx_not (Finset.mem_filter.mpr ⟨hx, hpp⟩)
              have hLx : rearickLog f hf x = 0 := hL x hx_pp
              rw [hLx, zero_mul]
            have hsub_eq : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (b / d) =
                ∑ d ∈ b.divisors, rearickLog f hf d * f (b / d) :=
              Finset.sum_subset hsubB hvanB
            rw [hsub_eq]
            exact hEb.symm
          have hA_rw : ∑ d ∈ a.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
              (f a * Real.log (a : ℝ)) * f b := by
            have hstep : ∀ d ∈ a.divisors.filter IsPrimePow,
                rearickLog f hf d * f (N / d) = (rearickLog f hf d * f (a / d)) * f b := by
              intro d hd
              have hd_mem : d ∈ a.divisors := Finset.mem_of_mem_filter d hd
              have hda : d ∣ a := (Nat.mem_divisors.mp hd_mem).1
              have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
              have hd_ne1 : d ≠ 1 := by
                intro hdeq
                rw [hdeq] at hd
                simp only [Finset.mem_filter, Nat.mem_divisors, isUnit_iff_eq_one, IsUnit.dvd,
                  ne_eq, true_and] at hd
                exact not_isPrimePow_one hd.2
              have hd1 : 1 < d := by omega
              have hNd : N / d = (a / d) * b := by
                rw [← hab]
                exact div_mul_right_eq a b d hda
              have hdiv : (a / d) ∣ a := Nat.div_dvd_of_dvd hda
              have hcopd : Nat.Coprime (a / d) b :=
                Nat.Coprime.coprime_dvd_left hdiv hcop
              have hNd_lt : N / d < N := Nat.div_lt_self hNpos hd1
              have hdivd_pos : 0 < a / d := Nat.div_pos (Nat.le_of_dvd haPos hda) hd_pos
              have hNd_eq : (a / d) * b = N / d := hNd.symm
              have hmultd : f (N / d) = f (a / d) * f b :=
                hNd ▸ ih (N / d) hNd_lt (a / d) b hNd_eq hcopd
              rw [hmultd]
              ring
            rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hA_eq]
          have hB_rw : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
              f a * (f b * Real.log (b : ℝ)) := by
            have hstep : ∀ d ∈ b.divisors.filter IsPrimePow,
                rearickLog f hf d * f (N / d) = f a * (rearickLog f hf d * f (b / d)) := by
              intro d hd
              have hd_mem : d ∈ b.divisors := Finset.mem_of_mem_filter d hd
              have hdb : d ∣ b := (Nat.mem_divisors.mp hd_mem).1
              have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
              have hd_ne1 : d ≠ 1 := by
                intro hdeq
                rw [hdeq] at hd
                simp only [Finset.mem_filter, Nat.mem_divisors, isUnit_iff_eq_one, IsUnit.dvd,
                  ne_eq, true_and] at hd
                exact not_isPrimePow_one hd.2
              have hd1 : 1 < d := by omega
              have hNd : N / d = a * (b / d) := by
                rw [← hab]
                exact div_mul_left_eq a b d hdb
              have hdiv : (b / d) ∣ b := Nat.div_dvd_of_dvd hdb
              have hcopd : Nat.Coprime a (b / d) :=
                (Nat.Coprime.coprime_dvd_left hdiv hcop.symm).symm
              have hNd_lt : N / d < N := Nat.div_lt_self hNpos hd1
              have hNd_eq : a * (b / d) = N / d := hNd.symm
              have hmultd : f (N / d) = f a * f (b / d) :=
                hNd ▸ ih (N / d) hNd_lt a (b / d) hNd_eq hcopd
              rw [hmultd]
              ring
            have hsum : ∑ d ∈ b.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
                ∑ d ∈ b.divisors.filter IsPrimePow, f a * (rearickLog f hf d * f (b / d)) :=
              Finset.sum_congr rfl hstep
            rw [hsum, ← Finset.mul_sum, hB_eq]
          have hS : ∑ d ∈ N.divisors.filter IsPrimePow, rearickLog f hf d * f (N / d) =
              (f a * f b) * Real.log (N : ℝ) := by
            rw [hunion, Finset.sum_union hdisj, hA_rw, hB_rw, hlogN]
            ring
          rw [← hAllFilter, hS] at hE
          exact mul_right_cancel₀ hlogNe hE

/--
**Rearick's characterization of multiplicative functions.** Let $f$ be a real-valued arithmetic
function with $f(1) > 0$, and let $L(f)$ be its Rearick logarithm. Then $f$ is multiplicative
(that is, $f(1) = 1$ and $f(mn) = f(m) f(n)$ whenever $m$ and $n$ are coprime) if and only if
$L(f)(m) = 0$ for every natural number $m$ that is not a prime power, including $m = 0$ and
$m = 1$.

Source: Rearick logarithm support characterization of multiplicative
arithmetic functions, after Huilan Li and Trueman MacHenry,
arXiv:1009.1892v1, <https://arxiv.org/abs/1009.1892>, lines 444-450
(Rearick logarithm definition) and 706-708 (Rearick Theorem 4). Real-valued
domain closure with `f 1 > 0` after Pong, arXiv:1504.03263v2,
<https://arxiv.org/abs/1504.03263>, lines 174-195; positivity also supplies
the nonzero premise for the Dirichlet inverse.
Proves `Wanted` entry `rearick_log_eq_zero_iff_isMultiplicative`.
-/
theorem rearick_log_eq_zero_iff_isMultiplicative
    (f : ArithmeticFunction ℝ) (hf : 0 < f 1) :
    f.IsMultiplicative ↔ ∀ m : ℕ, ¬ IsPrimePow m → rearickLog f hf m = 0 := by
  constructor
  · intro hmult m hm
    exact forward_vanish f hf hmult m hm
  · intro hL
    have h1 : f 1 = 1 := f1_of_hL f hf hL
    refine ⟨h1, fun {m n} hcop => ?_⟩
    have h := reverse_mult_aux f hf hL h1 (m * n) m n rfl hcop
    exact h

end MetaMathlibExt
