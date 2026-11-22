/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Combinatorics.AssociatedStirlingSecond
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Cast.Field
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Module

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This file proves Entry 10's general Poisson asymptotic expansion.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10PoissonAsymptotic

/-- **2-associated Stirling numbers in Ramanujan's Entry 10.** For natural numbers $n$ and $k$,
$S_2(n, k)$ is the integer $\sum_{j=0}^{k} (-1)^j \binom{n}{j} S(n - j, k - j)$, where $S$
denotes the Stirling numbers of the second kind.

$S_2(n, k)$ is the number of partitions of an $n$-element set into $k$ blocks, each containing at
least two elements. -/
def twoAssocStirlingSecond (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (Nat.choose n j : ℤ) *
      (Nat.stirlingSecond (n - j) (k - j) : ℤ)

-- Poisson moment identities used by Entry 10: the Poisson weights `x ^ j / j !`
-- sum to `exp x`, and the first and factorial moments give `x * exp x` and
-- `x ^ k * exp x`.  Together with `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial`
-- these yield the raw Poisson moments whose coefficients are the associated
-- Stirling numbers appearing in the correction terms below.

private lemma poisson_mass_aux (x : ℝ) :
    HasSum (fun j : ℕ => ((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ)) ((Real.exp x : ℝ) : ℂ) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) ((x : ℝ) : ℂ)
  have hexp : NormedSpace.exp ((x : ℝ) : ℂ) = ((Real.exp x : ℝ) : ℂ) := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  rw [hexp] at h
  refine h.congr_fun fun j => ?_
  push_cast
  ring

private lemma poisson_descFactorial_moment_aux (x : ℝ) (k : ℕ) :
    HasSum (fun j : ℕ => Complex.ofReal (((j.descFactorial k) : ℝ) *
      (x ^ j / (Nat.factorial j : ℝ)))) ((x : ℂ) ^ k * ((Real.exp x : ℝ) : ℂ)) := by
  have hmass := poisson_mass_aux x
  have hreal : ∀ n : ℕ, ((((n + k).descFactorial k) : ℝ) *
      (x ^ (n + k) / (Nat.factorial (n + k) : ℝ))) = x ^ k * (x ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    have hle : k ≤ n + k := Nat.le_add_left k n
    have hdiv := Nat.descFactorial_eq_div hle
    rw [Nat.add_sub_cancel] at hdiv
    have hdvd : Nat.factorial n ∣ Nat.factorial (n + k) :=
      Nat.factorial_dvd_factorial (Nat.le_add_right n k)
    have hne : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hcast : ((((n + k).descFactorial k) : ℝ))
        = ((Nat.factorial (n + k) : ℕ) : ℝ) / ((Nat.factorial n : ℕ) : ℝ) := by
      rw [hdiv, Nat.cast_div hdvd hne]
    have h1 : ((Nat.factorial (n + k) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [hcast]
    field_simp
    ring
  have hshift : HasSum (fun n : ℕ => Complex.ofReal ((((n + k).descFactorial k) : ℝ) *
      (x ^ (n + k) / (Nat.factorial (n + k) : ℝ)))) ((x : ℂ) ^ k * ((Real.exp x : ℝ) : ℂ)) := by
    have hfun : (fun n : ℕ => Complex.ofReal ((((n + k).descFactorial k) : ℝ) *
        (x ^ (n + k) / (Nat.factorial (n + k) : ℝ))))
        = (fun n : ℕ => (x : ℂ) ^ k * ((x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ)) := by
      funext n
      rw [hreal n, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [hfun]
    exact hmass.mul_left ((x : ℂ) ^ k)
  have hfin : (∑ i ∈ Finset.range k, (fun j : ℕ => Complex.ofReal ((((j.descFactorial k) : ℝ)) *
      (x ^ j / (Nat.factorial j : ℝ)))) i) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have h0 : j.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hjk
    simp [h0]
  have hadd : (x : ℂ) ^ k * ((Real.exp x : ℝ) : ℂ) +
      (∑ i ∈ Finset.range k, (fun j : ℕ => Complex.ofReal ((((j.descFactorial k) : ℝ)) *
        (x ^ j / (Nat.factorial j : ℝ)))) i)
      = (x : ℂ) ^ k * ((Real.exp x : ℝ) : ℂ) := by rw [hfin, add_zero]
  rw [← hadd]
  exact (hasSum_nat_add_iff (f := fun j : ℕ => Complex.ofReal ((((j.descFactorial k) : ℝ)) *
      (x ^ j / (Nat.factorial j : ℝ)))) k).mp hshift

private lemma poisson_raw_moment (x : ℝ) (m : ℕ) :
    HasSum
      (fun j : ℕ => (j : ℂ) ^ m *
        (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ)))
      ((∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℂ) * (x : ℂ) ^ k) *
        (((Real.exp x : ℝ) : ℂ))) := by
  have hdesc : ∀ k ∈ Finset.range (m + 1),
      HasSum
        (fun j : ℕ => (Nat.stirlingSecond m k : ℂ) *
          Complex.ofReal (((j.descFactorial k) : ℝ) *
            (x ^ j / (Nat.factorial j : ℝ))))
        ((Nat.stirlingSecond m k : ℂ) * (x : ℂ) ^ k *
          (((Real.exp x : ℝ) : ℂ))) := by
    intro k _
    have h := poisson_descFactorial_moment_aux x k
    have hmul := h.mul_left (Nat.stirlingSecond m k : ℂ)
    rwa [← mul_assoc] at hmul
  have hsum := hasSum_sum hdesc
  have hval : (∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℂ) * (x : ℂ) ^ k *
          (((Real.exp x : ℝ) : ℂ)))
      = (∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℂ) * (x : ℂ) ^ k) *
        (((Real.exp x : ℝ) : ℂ)) := by
    rw [Finset.sum_mul]
  rw [hval] at hsum
  refine hsum.congr_fun fun j => ?_
  have hpow := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial
    j m
  have hcast : ((j : ℂ) ^ m)
      = ∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℂ) *
          ((j.descFactorial k : ℕ) : ℂ) := by
    have h1 : ((j ^ m : ℕ) : ℂ)
        = ((∑ k ∈ Finset.range (m + 1),
          Nat.stirlingSecond m k * j.descFactorial k :
          ℕ) : ℂ) := by
      exact_mod_cast hpow
    push_cast at h1 ⊢
    exact h1
  have hw : ∀ k : ℕ,
      (Nat.stirlingSecond m k : ℂ) *
          Complex.ofReal (((j.descFactorial k) : ℝ) *
            (x ^ j / (Nat.factorial j : ℝ)))
        = (Nat.stirlingSecond m k : ℂ) *
          ((j.descFactorial k : ℕ) : ℂ) *
          (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ)) := by
    intro k
    push_cast
    ring
  have heq : (∑ k ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m k : ℂ) *
          Complex.ofReal (((j.descFactorial k) : ℝ) *
            (x ^ j / (Nat.factorial j : ℝ))))
      = (j : ℂ) ^ m *
        (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ)) := by
    simp only [hw]
    rw [← Finset.sum_mul, ← hcast]
  exact heq.symm

private lemma central_coeff_identity (n : ℕ)
    (x : ℂ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℂ) * (-x) ^ (n - i) *
        (∑ k ∈ Finset.range (i + 1),
          (Nat.stirlingSecond i k : ℂ) * x ^ k))
      = ∑ j ∈ Finset.range (n + 1),
        (((twoAssocStirlingSecond n j : ℤ) : ℂ) *
          x ^ j) := by
  have hRHS : (∑ j ∈ Finset.range (n + 1),
        (((twoAssocStirlingSecond n j : ℤ) : ℂ) *
          x ^ j))
      = ∑ p ∈ (Finset.range (n + 1)).sigma
        (fun j => Finset.range (j + 1)),
        ((-1 : ℂ) ^ p.2 *
          (Nat.choose n p.2 : ℂ) *
          (Nat.stirlingSecond (n - p.2)
            (p.1 - p.2) : ℂ) * x ^ p.1) := by
    have h1 : (∑ j ∈ Finset.range (n + 1),
          (((twoAssocStirlingSecond n j : ℤ) : ℂ) *
            x ^ j))
        = ∑ j ∈ Finset.range (n + 1),
          ∑ u ∈ Finset.range (j + 1),
            ((-1 : ℂ) ^ u *
              (Nat.choose n u : ℂ) *
              (Nat.stirlingSecond (n - u)
                (j - u) : ℂ) * x ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [twoAssocStirlingSecond]
      push_cast
      rw [Finset.sum_mul]
    rw [h1, Finset.sum_sigma']
  have hLHS : (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * (-x) ^ (n - i) *
          (∑ k ∈ Finset.range (i + 1),
            (Nat.stirlingSecond i k : ℂ) * x ^ k))
      = ∑ p ∈ (Finset.range (n + 1)).sigma
        (fun i => Finset.range (i + 1)),
        ((Nat.choose n p.1 : ℂ) *
          (Nat.stirlingSecond p.1 p.2 : ℂ) *
          (-x) ^ (n - p.1) * x ^ p.2) := by
    have h1 : (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℂ) * (-x) ^ (n - i) *
            (∑ k ∈ Finset.range (i + 1),
              (Nat.stirlingSecond i k : ℂ) * x ^ k))
        = ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (i + 1),
            ((Nat.choose n i : ℂ) *
              (Nat.stirlingSecond i k : ℂ) *
              (-x) ^ (n - i) * x ^ k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [h1, Finset.sum_sigma']
  rw [hLHS, hRHS]
  refine Finset.sum_bij'
    (fun p _ => ⟨n - p.1 + p.2, n - p.1⟩)
    (fun q _ => ⟨n - q.2, q.1 - q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    simp only [Finset.mem_range] at hp1 hp2 ⊢
    constructor
    · omega
    · omega
  · intro q hq
    rw [Finset.mem_sigma] at hq ⊢
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Finset.mem_range] at hq1 hq2 ⊢
    constructor
    · omega
    · omega
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_range] at hp1 hp2
    have e1 : n - (n - p.1) = p.1 := by omega
    have e2 : (n - p.1 + p.2) - (n - p.1)
        = p.2 := by omega
    simp only [e1, e2]
  · intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Finset.mem_range] at hq1 hq2
    have e1 : n - (n - q.2) = q.2 := by omega
    have e2 : q.2 + (q.1 - q.2) = q.1 := by omega
    simp only [e1, e2]
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_range] at hp1 hp2
    have h1 : p.1 ≤ n := by omega
    have e1 : n - (n - p.1) = p.1 := by omega
    have e2 : (n - p.1 + p.2) - (n - p.1)
        = p.2 := by omega
    have e3 : Nat.choose n (n - p.1)
        = Nat.choose n p.1 :=
      Nat.choose_symm h1
    have e3c : (Nat.choose n (n - p.1) : ℂ)
        = (Nat.choose n p.1 : ℂ) := by
      rw [e3]
    have hneg : (-x) ^ (n - p.1)
        = (-1 : ℂ) ^ (n - p.1) * x ^ (n - p.1) := by
      rw [show (-x : ℂ) = (-1) * x from by ring,
        mul_pow]
    simp only [e1, e2, e3c]
    rw [hneg, pow_add]
    ring

private noncomputable def taylorPoly
    (φ : ℝ → ℂ) (N : ℕ) (c t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    (((t - c) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) *
      iteratedDeriv k φ c

private lemma taylorPoly_at_center (φ : ℝ → ℂ)
    (N : ℕ) (c : ℝ) :
    taylorPoly φ N c c = φ c := by
  simp only [taylorPoly]
  have h0 : ∀ k ∈ Finset.range (N + 1),
      k = 0 ∨
        ((((c - c) ^ k / (Nat.factorial k : ℝ) :
          ℝ) : ℂ) *
          iteratedDeriv k φ c) = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · apply Or.inr
      have hcc : c - c = (0 : ℝ) := sub_self c
      rw [hcc, zero_pow hk0]
      simp
  have hsum := Finset.sum_eq_single 0
    (fun k hk hk0 => Or.resolve_left (h0 k hk) hk0)
    (by simp)
  rw [hsum]
  simp

private lemma sum_shift_zero
    (d e : ℕ → ℂ) (hd0 : d 0 = 0)
    (hde : ∀ j, d (j + 1) = e j) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 2), d k
      = ∑ j ∈ Finset.range (N + 1), e j := by
  induction N with
  | zero =>
    simp [Finset.sum_range_succ, hd0, hde 0]
  | succ N ih =>
    have h1 : ∑ k ∈ Finset.range (N + 1 + 2), d k
        = (∑ k ∈ Finset.range (N + 2), d k)
          + d (N + 2) := by
      rw [show N + 1 + 2 = (N + 2) + 1 from by omega]
      rw [Finset.sum_range_succ]
    have h2 : ∑ j ∈ Finset.range (N + 1 + 1), e j
        = (∑ j ∈ Finset.range (N + 1), e j)
          + e (N + 1) := by
      rw [Finset.sum_range_succ]
    rw [h1, h2, ih]
    rw [show N + 2 = (N + 1) + 1 from by omega]
    rw [hde]

private lemma hasDerivAt_taylorPoly_succ
    (φ : ℝ → ℂ) (N : ℕ) (c t : ℝ) :
    HasDerivAt (fun t => taylorPoly φ (N + 1) c t)
      (taylorPoly (deriv φ) N c t) t := by
  have hterm : ∀ k ∈ Finset.range (N + 1 + 1),
      HasDerivAt
        (fun u : ℝ => (((u - c) ^ k /
          (Nat.factorial k : ℝ) : ℝ) : ℂ) *
          iteratedDeriv k φ c)
        ((if k = 0 then (0 : ℂ) else
          (((t - c) ^ (k - 1) /
            (Nat.factorial (k - 1) : ℝ) : ℝ) : ℂ) *
            iteratedDeriv k φ c)) t := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have hconst : (fun u : ℝ =>
            (((u - c) ^ 0 /
              (Nat.factorial 0 : ℝ) : ℝ) : ℂ) *
              iteratedDeriv 0 φ c)
          = fun _ => iteratedDeriv 0 φ c := by
        funext u
        simp
      rw [hconst]
      exact hasDerivAt_const t _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        hk0
      simp only [ite_eq_right (by omega : ¬m + 1 = 0)]
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub]
      have hbase : HasDerivAt (fun u : ℝ => u - c)
          (1 : ℝ) t :=
        (hasDerivAt_id t).sub_const c
      have hpow : HasDerivAt
          (fun u : ℝ => (u - c) ^ (m + 1))
          ((m + 1 : ℝ) * (t - c) ^ m) t := by
        have houter : HasDerivAt (fun y : ℝ => y ^ (m+1))
            ((m + 1 : ℝ) * (t - c) ^ m) (t - c) := by
          have h := hasDerivAt_pow (m + 1) (t - c)
          simpa [hsub] using h
        have hcomp : HasDerivAt
            (fun u : ℝ => (u - c) ^ (m + 1))
            ((((m + 1 : ℝ) * (t - c) ^ m)) * 1) t :=
          HasDerivAt.comp
            (h₂ := fun y : ℝ => y ^ (m + 1))
            (h := fun u : ℝ => u - c) (x := t)
            houter hbase
        simpa using hcomp
      have hdiv : HasDerivAt
          (fun u : ℝ => (u - c) ^ (m + 1) /
            (Nat.factorial (m + 1) : ℝ))
          (((m + 1 : ℝ) * (t - c) ^ m) /
            (Nat.factorial (m + 1) : ℝ)) t :=
        hpow.div_const _
      have hfact : ((Nat.factorial (m + 1) : ℕ) : ℝ)
          = (m + 1 : ℝ) *
            ((Nat.factorial m : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hm1 : (m + 1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero m
      have hderiv_eq : (((m + 1 : ℝ) * (t - c) ^ m) /
            (Nat.factorial (m + 1) : ℝ))
          = (t - c) ^ m / (Nat.factorial m : ℝ) := by
        rw [hfact]
        field_simp
      rw [hderiv_eq] at hdiv
      have hC := hdiv.ofReal_comp
      have hmul := hC.mul_const
        (iteratedDeriv (m + 1) φ c)
      exact hmul
  have hd0 : (if (0 : ℕ) = 0 then (0 : ℂ) else
      (((t - c) ^ (0 - 1) /
        (Nat.factorial (0 - 1) : ℝ) : ℝ) : ℂ) *
        iteratedDeriv 0 φ c) = 0 := by
    simp
  have hde : ∀ j : ℕ,
      (if j + 1 = 0 then (0 : ℂ) else
        (((t - c) ^ (j + 1 - 1) /
          (Nat.factorial (j + 1 - 1) : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (j + 1) φ c)
      = (((t - c) ^ j / (Nat.factorial j : ℝ) :
        ℝ) : ℂ) *
        iteratedDeriv j (deriv φ) c := by
    intro j
    simp only [ite_eq_right (by omega : ¬j + 1 = 0)]
    have hsub : j + 1 - 1 = j := by omega
    rw [hsub]
    have hiter : iteratedDeriv j (deriv φ) c
        = iteratedDeriv (j + 1) φ c := by
      rw [← iteratedDeriv_succ']
    rw [hiter]
  have hshift := sum_shift_zero
    (fun k => if k = 0 then (0 : ℂ) else
      (((t - c) ^ (k - 1) /
        (Nat.factorial (k - 1) : ℝ) : ℝ) : ℂ) *
        iteratedDeriv k φ c)
    (fun j => (((t - c) ^ j /
      (Nat.factorial j : ℝ) : ℝ) : ℂ) *
      iteratedDeriv j (deriv φ) c)
    hd0 hde N
  have hsum := HasDerivAt.fun_sum hterm
  simp only [taylorPoly] at hsum ⊢
  rw [hshift] at hsum
  exact hsum

private lemma taylor_remainder_bound
    (φ : ℝ → ℂ) (L R c : ℝ) (hLR : L ≤ R)
    (hc : c ∈ Set.Icc L R) (N : ℕ)
    (hdiff : ∀ k ≤ N, ∀ x ∈ Set.Icc L R,
      DifferentiableAt ℝ (iteratedDeriv k φ) x)
    (C : ℝ) (hC : ∀ x ∈ Set.Icc L R,
      ‖iteratedDeriv (N + 1) φ x‖ ≤ C) :
    ∀ t ∈ Set.Icc L R,
      ‖φ t - taylorPoly φ N c t‖
        ≤ C * |t - c| ^ (N + 1) := by
  induction N generalizing φ L R c C with
  | zero =>
    intro t ht
    have hT0 : taylorPoly φ 0 c t = φ c := by
      simp only [taylorPoly]
      simp
    rw [hT0]
    by_cases htc : t ≤ c
    · have hsub : Set.Icc t c ⊆ Set.Icc L R := by
        intro x hx
        simp only [Set.mem_Icc] at hx hc ht ⊢
        obtain ⟨hxt1, hxt2⟩ := hx
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨ht1, ht2⟩ := ht
        constructor
        · linarith
        · linarith
      have hdiff0 : ∀ x ∈ Set.Icc t c,
          HasDerivWithinAt φ
            (iteratedDeriv 1 φ x)
            (Set.Icc t c) x := by
        intro x hx
        have hxR : x ∈ Set.Icc L R := hsub hx
        have hda := hdiff 0 (by omega) x hxR
        rw [iteratedDeriv_zero] at hda
        have hHas := hda.hasDerivAt
        rw [← iteratedDeriv_one] at hHas
        exact hHas.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Ico t c,
          ‖iteratedDeriv 1 φ x‖ ≤ C := by
        intro x hx
        have hxIcc : x ∈ Set.Icc t c :=
          Set.Ico_subset_Icc_self hx
        have hxR : x ∈ Set.Icc L R :=
          hsub hxIcc
        simpa using hC x hxR
      have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
        hdiff0 hbound c
        (Set.mem_Icc.mpr ⟨htc, le_refl _⟩)
      have hneg : ‖φ t - φ c‖
          = ‖φ c - φ t‖ := by
        rw [← norm_neg, neg_sub]
      have habs : |t - c| = c - t := by
        rw [abs_of_nonpos (sub_nonpos.mpr htc)]
        ring
      rw [hneg, habs]
      simpa using hMVT
    · push Not at htc
      have hsub : Set.Icc c t ⊆ Set.Icc L R := by
        intro x hx
        simp only [Set.mem_Icc] at hx hc ht ⊢
        obtain ⟨hxc1, hxc2⟩ := hx
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨ht1, ht2⟩ := ht
        constructor
        · linarith
        · linarith
      have hdiff0 : ∀ x ∈ Set.Icc c t,
          HasDerivWithinAt φ
            (iteratedDeriv 1 φ x)
            (Set.Icc c t) x := by
        intro x hx
        have hxR : x ∈ Set.Icc L R := hsub hx
        have hda := hdiff 0 (by omega) x hxR
        rw [iteratedDeriv_zero] at hda
        have hHas := hda.hasDerivAt
        rw [← iteratedDeriv_one] at hHas
        exact hHas.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Ico c t,
          ‖iteratedDeriv 1 φ x‖ ≤ C := by
        intro x hx
        have hxIcc : x ∈ Set.Icc c t :=
          Set.Ico_subset_Icc_self hx
        have hxR : x ∈ Set.Icc L R :=
          hsub hxIcc
        simpa using hC x hxR
      have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
        hdiff0 hbound t
        (Set.mem_Icc.mpr
          ⟨le_of_lt htc, le_refl _⟩)
      have habs : |t - c| = t - c := by
        rw [abs_of_nonneg
          (sub_nonneg.mpr (le_of_lt htc))]
      rw [habs]
      simpa using hMVT
  | succ N ih =>
    intro t ht
    have hc0 : φ c - taylorPoly φ (N + 1) c c = 0 := by
      rw [taylorPoly_at_center]
      simp
    have hdiff' : ∀ k ≤ N, ∀ x ∈ Set.Icc L R,
        DifferentiableAt ℝ
          (iteratedDeriv k (deriv φ)) x := by
      intro k hk x hx
      have hle : k + 1 ≤ N + 1 := by omega
      have h := hdiff (k + 1) hle x hx
      rwa [iteratedDeriv_succ'] at h
    have hC' : ∀ x ∈ Set.Icc L R,
        ‖iteratedDeriv (N + 1) (deriv φ) x‖
          ≤ C := by
      intro x hx
      have h := hC x hx
      rwa [iteratedDeriv_succ'] at h
    have ih' := ih (deriv φ) L R c hLR hc
      hdiff' C hC'
    have hC0 : 0 ≤ C := by
      have hx0 : L ∈ Set.Icc L R :=
        Set.mem_Icc.mpr ⟨le_refl _, hLR⟩
      have hle := hC L hx0
      exact le_trans (norm_nonneg _) hle
    by_cases htc : t ≤ c
    · have hsub : Set.Icc t c ⊆ Set.Icc L R := by
        intro x hx
        simp only [Set.mem_Icc] at hx hc ht ⊢
        obtain ⟨hxt1, hxt2⟩ := hx
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨ht1, ht2⟩ := ht
        constructor
        · linarith
        · linarith
      have hdiffH : ∀ x ∈ Set.Icc t c,
          HasDerivWithinAt
            (fun u => φ u - taylorPoly φ (N+1) c u)
            ((deriv φ x) -
              taylorPoly (deriv φ) N c x)
            (Set.Icc t c) x := by
        intro x hx
        have hxR : x ∈ Set.Icc L R := hsub hx
        have hda0 := hdiff 0 (by omega) x hxR
        rw [iteratedDeriv_zero] at hda0
        have hHasφ := hda0.hasDerivAt
        have hHasT := hasDerivAt_taylorPoly_succ
          φ N c x
        have hHas := hHasφ.sub hHasT
        exact hHas.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Ico t c,
          ‖(deriv φ x) -
            taylorPoly (deriv φ) N c x‖
            ≤ C * |t - c| ^ (N + 1) := by
        intro x hx
        have hxIcc : x ∈ Set.Icc t c :=
          Set.Ico_subset_Icc_self hx
        have hxR : x ∈ Set.Icc L R :=
          hsub hxIcc
        have hib := ih' x hxR
        have hle : |x - c| ≤ |t - c| := by
          have hxIcc' := hxIcc
          simp only [Set.mem_Icc] at hxIcc'
          obtain ⟨hxt1, hxt2⟩ := hxIcc'
          have habsx : |x - c| = c - x := by
            rw [abs_of_nonpos
              (sub_nonpos.mpr hxt2)]
            ring
          have habst : |t - c| = c - t := by
            rw [abs_of_nonpos (sub_nonpos.mpr htc)]
            ring
          rw [habsx, habst]
          linarith
        have hpow : |x - c| ^ (N + 1)
            ≤ |t - c| ^ (N + 1) :=
          pow_le_pow_left₀ (abs_nonneg _)
            hle _
        have hmul := mul_le_mul_of_nonneg_left
          hpow hC0
        exact hib.trans hmul
      have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
        hdiffH hbound c
        (Set.mem_Icc.mpr ⟨htc, le_refl _⟩)
      rw [hc0, zero_sub, norm_neg] at hMVT
      have habs : |t - c| = c - t := by
        rw [abs_of_nonpos (sub_nonpos.mpr htc)]
        ring
      rw [← habs, mul_assoc, ← pow_succ] at hMVT
      exact hMVT
    · push Not at htc
      have hsub : Set.Icc c t ⊆ Set.Icc L R := by
        intro x hx
        simp only [Set.mem_Icc] at hx hc ht ⊢
        obtain ⟨hxc1, hxc2⟩ := hx
        obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨ht1, ht2⟩ := ht
        constructor
        · linarith
        · linarith
      have hdiffH : ∀ x ∈ Set.Icc c t,
          HasDerivWithinAt
            (fun u => φ u - taylorPoly φ (N+1) c u)
            ((deriv φ x) -
              taylorPoly (deriv φ) N c x)
            (Set.Icc c t) x := by
        intro x hx
        have hxR : x ∈ Set.Icc L R := hsub hx
        have hda0 := hdiff 0 (by omega) x hxR
        rw [iteratedDeriv_zero] at hda0
        have hHasφ := hda0.hasDerivAt
        have hHasT := hasDerivAt_taylorPoly_succ
          φ N c x
        have hHas := hHasφ.sub hHasT
        exact hHas.hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Ico c t,
          ‖(deriv φ x) -
            taylorPoly (deriv φ) N c x‖
            ≤ C * |t - c| ^ (N + 1) := by
        intro x hx
        have hxIcc : x ∈ Set.Icc c t :=
          Set.Ico_subset_Icc_self hx
        have hxR : x ∈ Set.Icc L R :=
          hsub hxIcc
        have hib := ih' x hxR
        have hle : |x - c| ≤ |t - c| := by
          have hxIcc' := hxIcc
          simp only [Set.mem_Icc] at hxIcc'
          obtain ⟨hxc1, hxc2⟩ := hxIcc'
          have habsx : |x - c| = x - c := by
            rw [abs_of_nonneg
              (sub_nonneg.mpr hxc1)]
          have habst : |t - c| = t - c := by
            rw [abs_of_nonneg
              (sub_nonneg.mpr (le_of_lt htc))]
          rw [habsx, habst]
          linarith
        have hpow : |x - c| ^ (N + 1)
            ≤ |t - c| ^ (N + 1) :=
          pow_le_pow_left₀ (abs_nonneg _)
            hle _
        have hmul := mul_le_mul_of_nonneg_left
          hpow hC0
        exact hib.trans hmul
      have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
        hdiffH hbound t
        (Set.mem_Icc.mpr
          ⟨le_of_lt htc, le_refl _⟩)
      rw [hc0, sub_zero] at hMVT
      have habs : |t - c| = t - c := by
        rw [abs_of_nonneg
          (sub_nonneg.mpr (le_of_lt htc))]
      conv at hMVT =>
        rhs
        rw [habs]
        rw [mul_assoc, ← pow_succ]
        rw [← habs]
      exact hMVT

private lemma poisson_central_moment (x : ℝ)
    (n : ℕ) :
    HasSum
      (fun j : ℕ => (((((j : ℝ) - x) ^ n *
        (x ^ j / (Nat.factorial j : ℝ)) : ℝ) : ℂ)))
      ((∑ j0 ∈ Finset.range (n + 1),
        (((twoAssocStirlingSecond n j0 : ℤ) : ℂ) *
          (x : ℂ) ^ j0)) *
        (((Real.exp x : ℝ) : ℂ))) := by
  have hraw : ∀ i ∈ Finset.range (n + 1),
      HasSum
        (fun j : ℕ =>
          (Nat.choose n i : ℂ) * (-(x : ℂ)) ^ (n - i) *
            ((j : ℂ) ^ i *
              (((x ^ j / (Nat.factorial j : ℝ) :
                ℝ) : ℂ))))
        ((Nat.choose n i : ℂ) * (-(x : ℂ)) ^ (n - i) *
          ((∑ k ∈ Finset.range (i + 1),
            (Nat.stirlingSecond i k : ℂ) *
              (x : ℂ) ^ k) *
            (((Real.exp x : ℝ) : ℂ)))) := by
    intro i _
    have h := poisson_raw_moment x i
    exact h.mul_left
      ((Nat.choose n i : ℂ) * (-(x : ℂ)) ^ (n - i))
  have hsum := hasSum_sum hraw
  have hval : (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * (-(x : ℂ)) ^ (n - i) *
          ((∑ k ∈ Finset.range (i + 1),
            (Nat.stirlingSecond i k : ℂ) *
              (x : ℂ) ^ k) *
            (((Real.exp x : ℝ) : ℂ))))
      = (∑ j0 ∈ Finset.range (n + 1),
        (((twoAssocStirlingSecond n j0 : ℤ) : ℂ) *
          (x : ℂ) ^ j0)) *
        (((Real.exp x : ℝ) : ℂ)) := by
    have hid := central_coeff_identity n (x : ℂ)
    simp only [← mul_assoc] at hid ⊢
    rw [← Finset.sum_mul, hid]
  rw [hval] at hsum
  refine hsum.congr_fun fun j => ?_
  have hbin : (((j : ℂ) - (x : ℂ)) ^ n)
      = ∑ i ∈ Finset.range (n + 1),
        (j : ℂ) ^ i * (-(x : ℂ)) ^ (n - i) *
          (Nat.choose n i : ℂ) := by
    have h := add_pow (j : ℂ) (-(x : ℂ)) n
    rwa [← sub_eq_add_neg] at h
  have hcast : (((((j : ℝ) - x) ^ n *
        (x ^ j / (Nat.factorial j : ℝ)) : ℝ) : ℂ))
      = (((j : ℂ) - (x : ℂ)) ^ n) *
        (((x ^ j / (Nat.factorial j : ℝ) :
          ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hcast, hbin, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **The Entry 10 Stirling numbers are the 2-associated Stirling numbers.** For all natural
numbers $n$ and $k$, the integer $\sum_{j=0}^{k} (-1)^j \binom{n}{j} S(n - j, k - j)$ used in
Ramanujan's Entry 10, where $S$ denotes the Stirling numbers of the second kind, equals the
2-associated Stirling number of the second kind $S_2(n, k)$. -/
theorem twoAssocStirlingSecond_eq_canonical (n k : ℕ) :
    twoAssocStirlingSecond n k = MetaMathlibExt.twoAssocStirlingSecond n k := by
  rfl

private lemma twoAssoc_succ_zero (n : ℕ) :
    twoAssocStirlingSecond (n + 1) 0 = 0 := by
  rw [twoAssocStirlingSecond_eq_canonical]
  simp [MetaMathlibExt.twoAssocStirlingSecond]

private lemma twoAssocStirlingSecond_eq_zero_of_lt_two_mul (n k : ℕ) (hnk : n < 2 * k) :
    twoAssocStirlingSecond n k = 0 := by
  rw [twoAssocStirlingSecond_eq_canonical]
  exact MetaMathlibExt.twoAssocStirlingSecond_eq_zero_of_lt_two_mul n k hnk

private lemma poisson_taylor_hasSum (φ : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    HasSum
      (fun j : ℕ => (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ)) *
        taylorPoly φ N x (j : ℝ))
      ((((Real.exp x : ℝ) : ℂ)) *
        ∑ n ∈ Finset.range (N + 1),
          (∑ r ∈ Finset.range (n + 1),
            ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
  have hterm : ∀ n ∈ Finset.range (N + 1),
      HasSum
        (fun j : ℕ => (((((j : ℝ) - x) ^ n *
          (x ^ j / (Nat.factorial j : ℝ)) : ℝ) : ℂ)) *
            (iteratedDeriv n φ x / (Nat.factorial n : ℂ)))
        (((∑ r ∈ Finset.range (n + 1),
          ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
            (((Real.exp x : ℝ) : ℂ))) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
    intro n hn
    exact (poisson_central_moment x n).mul_right
      (iteratedDeriv n φ x / (Nat.factorial n : ℂ))
  have hsum := hasSum_sum hterm
  have hval :
      (∑ n ∈ Finset.range (N + 1),
        (((∑ r ∈ Finset.range (n + 1),
          ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
            (((Real.exp x : ℝ) : ℂ))) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ)))) =
        (((Real.exp x : ℝ) : ℂ)) *
          ∑ n ∈ Finset.range (N + 1),
            (∑ r ∈ Finset.range (n + 1),
              ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
                (iteratedDeriv n φ x / (Nat.factorial n : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hval] at hsum
  refine hsum.congr_fun fun j => ?_
  simp only [taylorPoly]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

private noncomputable def poisson_taylorTerm (φ : ℝ → ℂ) (x : ℝ)
    (p : Sigma fun _ : ℕ => ℕ) : ℂ :=
  ((twoAssocStirlingSecond p.1 p.2 : ℤ) : ℂ) * (x : ℂ) ^ p.2 *
    (iteratedDeriv p.1 φ x / (Nat.factorial p.1 : ℂ))

private def poisson_taylorPairs (N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.range (N + 1)).sigma fun n => Finset.range (n + 1)

private def poisson_correctionSource (M : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.Icc 2 M).sigma fun k => Finset.Icc k (2 * k - 2)

private def poisson_correctionPair (p : Sigma fun _ : ℕ => ℕ) :
    Sigma fun _ : ℕ => ℕ :=
  ⟨p.2, p.2 + 1 - p.1⟩

private lemma poisson_correctionPair_injOn (M : ℕ) :
    Set.InjOn poisson_correctionPair ↑(poisson_correctionSource M) := by
  rintro ⟨k, n⟩ hk ⟨l, m⟩ hl h
  change ⟨k, n⟩ ∈ poisson_correctionSource M at hk
  change ⟨l, m⟩ ∈ poisson_correctionSource M at hl
  rw [poisson_correctionSource, Finset.mem_sigma] at hk hl
  obtain ⟨hk, hkn⟩ := hk
  obtain ⟨hl, hlm⟩ := hl
  rw [Finset.mem_Icc] at hk hkn hl hlm
  have hnm : n = m := congrArg Sigma.fst h
  subst m
  have hsub : n + 1 - k = n + 1 - l :=
    congrArg (fun p : (Sigma fun _ : ℕ => ℕ) => p.2) h
  have hkl : k = l :=
    tsub_inj_right (hkn.1.trans (Nat.le_succ n))
      (hlm.1.trans (Nat.le_succ n)) hsub
  subst l
  rfl

private lemma poisson_correction_sum_eq (φ : ℝ → ℂ) (x : ℝ) (M : ℕ) :
    (∑ p ∈ (poisson_correctionSource M).image poisson_correctionPair,
      poisson_taylorTerm φ x p) =
      ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
        (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
          (x : ℂ) ^ (n - k + 1) *
            (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
  rw [Finset.sum_image (poisson_correctionPair_injOn M)]
  rw [poisson_correctionSource, Finset.sum_sigma']
  apply Finset.sum_congr rfl
  rintro ⟨k, n⟩ hn
  rw [Finset.mem_sigma] at hn
  obtain ⟨_, hn⟩ := hn
  simp only [poisson_correctionPair, poisson_taylorTerm]
  have hsub : n + 1 - k = n - k + 1 := by
    rw [Finset.mem_Icc] at hn
    exact Nat.sub_add_comm hn.1
  rw [hsub]

private def poisson_lowPairs (M N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (poisson_taylorPairs N).filter fun p => p.1 + 1 - p.2 ≤ M

private def poisson_highPairs (M N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (poisson_taylorPairs N).filter fun p => M < p.1 + 1 - p.2

private def poisson_leadingPairs (M : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  insert ⟨0, 0⟩ ((poisson_correctionSource M).image poisson_correctionPair)

private lemma poisson_leadingPairs_subset_low (M N : ℕ) (hM : 0 < M)
    (hN : 2 * M - 2 ≤ N) :
    poisson_leadingPairs M ⊆ poisson_lowPairs M N := by
  intro p hp
  rw [poisson_leadingPairs, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · simp [poisson_lowPairs, poisson_taylorPairs, hM]
  · rw [Finset.mem_image] at hp
    obtain ⟨⟨k, n⟩, hkn, rfl⟩ := hp
    rw [poisson_correctionSource, Finset.mem_sigma] at hkn
    obtain ⟨hk, hn⟩ := hkn
    change k ∈ Finset.Icc 2 M at hk
    change n ∈ Finset.Icc k (2 * k - 2) at hn
    rw [Finset.mem_Icc] at hk hn
    rw [poisson_lowPairs, Finset.mem_filter]
    constructor
    · rw [poisson_taylorPairs, Finset.mem_sigma]
      simp only [poisson_correctionPair, Finset.mem_range]
      constructor <;> omega
    · simp only [poisson_correctionPair]
      rw [Nat.sub_sub_self (by omega : k ≤ n + 1)]
      exact hk.2

private lemma poisson_low_not_leading_zero (φ : ℝ → ℂ) (x : ℝ) (M N : ℕ)
    (p : Sigma fun _ : ℕ => ℕ) (hp : p ∈ poisson_lowPairs M N)
    (hnot : p ∉ poisson_leadingPairs M) :
    poisson_taylorTerm φ x p = 0 := by
  obtain ⟨n, r⟩ := p
  rw [poisson_lowPairs, Finset.mem_filter] at hp
  obtain ⟨hp, hlow⟩ := hp
  change n + 1 - r ≤ M at hlow
  rw [poisson_taylorPairs, Finset.mem_sigma] at hp
  obtain ⟨hn, hr⟩ := hp
  change n ∈ Finset.range (N + 1) at hn
  change r ∈ Finset.range (n + 1) at hr
  rw [Finset.mem_range] at hn hr
  by_cases hr0 : r = 0
  · subst r
    by_cases hn0 : n = 0
    · subst n
      exfalso
      apply hnot
      simp [poisson_leadingPairs]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      simp [poisson_taylorTerm, twoAssoc_succ_zero]
  · by_cases hsupport : n < 2 * r
    · simp [poisson_taylorTerm,
        twoAssocStirlingSecond_eq_zero_of_lt_two_mul n r hsupport]
    · push Not at hsupport
      exfalso
      apply hnot
      rw [poisson_leadingPairs, Finset.mem_insert]
      apply Or.inr
      rw [Finset.mem_image]
      refine ⟨⟨n + 1 - r, n⟩, ?_, ?_⟩
      · rw [poisson_correctionSource, Finset.mem_sigma]
        change n + 1 - r ∈ Finset.Icc 2 M ∧
          n ∈ Finset.Icc (n + 1 - r) (2 * (n + 1 - r) - 2)
        constructor
        · rw [Finset.mem_Icc]
          constructor
          · omega
          · exact hlow
        · rw [Finset.mem_Icc]
          constructor <;> omega
      · change (⟨n, n + 1 - (n + 1 - r)⟩ : Sigma fun _ : ℕ => ℕ) = ⟨n, r⟩
        rw [Nat.sub_sub_self (by omega : r ≤ n + 1)]

private lemma poisson_low_sum_eq (φ : ℝ → ℂ) (x : ℝ) (M N : ℕ)
    (hM : 0 < M) (hN : 2 * M - 2 ≤ N) :
    (∑ p ∈ poisson_lowPairs M N, poisson_taylorTerm φ x p) =
      φ x + ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
        (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
          (x : ℂ) ^ (n - k + 1) *
            (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
  have hsubset := poisson_leadingPairs_subset_low M N hM hN
  have hsum :
      (∑ p ∈ poisson_leadingPairs M, poisson_taylorTerm φ x p) =
        ∑ p ∈ poisson_lowPairs M N, poisson_taylorTerm φ x p :=
    Finset.sum_subset hsubset fun p hp hnot =>
      poisson_low_not_leading_zero φ x M N p hp hnot
  have hbase : (⟨0, 0⟩ : Sigma fun _ : ℕ => ℕ) ∉
      (poisson_correctionSource M).image poisson_correctionPair := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨⟨k, n⟩, hkn, heq⟩ := h
    rw [poisson_correctionSource, Finset.mem_sigma] at hkn
    obtain ⟨hk, hn⟩ := hkn
    change k ∈ Finset.Icc 2 M at hk
    change n ∈ Finset.Icc k (2 * k - 2) at hn
    rw [Finset.mem_Icc] at hk hn
    have hn0 : n = 0 := congrArg Sigma.fst heq
    omega
  calc
    (∑ p ∈ poisson_lowPairs M N, poisson_taylorTerm φ x p) =
        ∑ p ∈ poisson_leadingPairs M, poisson_taylorTerm φ x p := hsum.symm
    _ = poisson_taylorTerm φ x ⟨0, 0⟩ +
        ∑ p ∈ (poisson_correctionSource M).image poisson_correctionPair,
          poisson_taylorTerm φ x p := by
      rw [poisson_leadingPairs, Finset.sum_insert hbase]
    _ = _ := by
      rw [poisson_correction_sum_eq]
      simp [poisson_taylorTerm, twoAssocStirlingSecond]

private lemma poisson_taylor_sum_split (φ : ℝ → ℂ) (x : ℝ) (M N : ℕ) :
    (∑ p ∈ poisson_taylorPairs N, poisson_taylorTerm φ x p) =
      (∑ p ∈ poisson_lowPairs M N, poisson_taylorTerm φ x p) +
        ∑ p ∈ poisson_highPairs M N, poisson_taylorTerm φ x p := by
  have h := Finset.sum_filter_add_sum_filter_not
    (poisson_taylorPairs N) (fun p => p.1 + 1 - p.2 ≤ M)
      (poisson_taylorTerm φ x)
  rw [poisson_lowPairs, poisson_highPairs]
  simpa only [not_le] using h.symm

private lemma poisson_taylor_coeff_sum_eq (φ : ℝ → ℂ) (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      (∑ r ∈ Finset.range (n + 1),
        ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
          (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) =
      ∑ p ∈ poisson_taylorPairs N, poisson_taylorTerm φ x p := by
  rw [poisson_taylorPairs]
  calc
    _ = ∑ n ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (n + 1),
        poisson_taylorTerm φ x ⟨n, r⟩ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [poisson_taylorTerm]
    _ = _ := Finset.sum_sigma' (Finset.range (N + 1))
      (fun n => Finset.range (n + 1))
      (fun n r => poisson_taylorTerm φ x ⟨n, r⟩)

private lemma poisson_highTerm_isBigO (M N : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m)
    (p : Sigma fun _ : ℕ => ℕ) (hp : p ∈ poisson_highPairs M N) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => poisson_taylorTerm φ x p)
      (fun x : ℝ => G x / x ^ M) := by
  obtain ⟨n, r⟩ := p
  rw [poisson_highPairs, Finset.mem_filter] at hp
  obtain ⟨hp, hhigh⟩ := hp
  change M < n + 1 - r at hhigh
  rw [poisson_taylorPairs, Finset.mem_sigma] at hp
  obtain ⟨hn, hr⟩ := hp
  change n ∈ Finset.range (N + 1) at hn
  change r ∈ Finset.range (n + 1) at hr
  rw [Finset.mem_range] at hn hr
  have hnpos : 0 < n := by omega
  have hrn : r ≤ n := by omega
  have hMnr : M ≤ n - r := by omega
  refine Asymptotics.IsBigO.of_bound
    (‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * A ^ n) ?_
  filter_upwards [h_deriv n hnpos, hG_ge,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hder hG hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hG0 : 0 ≤ G x := le_trans (by norm_num) hG
  have hratio : x ^ r / x ^ n = 1 / x ^ (n - r) := by
    have hpow : x ^ n = x ^ (n - r) * x ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrn]
    rw [hpow]
    field_simp
  have hden : x ^ M ≤ x ^ (n - r) :=
    pow_le_pow_right₀ hx hMnr
  have hratio_le : x ^ r / x ^ n ≤ 1 / x ^ M := by
    rw [hratio]
    exact one_div_le_one_div_of_le (pow_pos hxpos M) hden
  have htarget : ‖G x / x ^ M‖ = G x / x ^ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg hG0 (pow_nonneg (le_of_lt hxpos) M)
  simp only [poisson_taylorTerm]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (le_of_lt hxpos)]
  calc
    ‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * x ^ r *
        ‖iteratedDeriv n φ x / (Nat.factorial n : ℂ)‖ ≤
      ‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * x ^ r *
        (G x * (A / x) ^ n) := by
      gcongr
      exact hder.2
    _ = (‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * A ^ n) * G x *
        (x ^ r / x ^ n) := by
      rw [div_pow]
      ring
    _ ≤ (‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * A ^ n) * G x *
        (1 / x ^ M) := by
      gcongr
    _ = (‖((twoAssocStirlingSecond n r : ℤ) : ℂ)‖ * A ^ n) *
        ‖G x / x ^ M‖ := by
      rw [htarget]
      ring

private lemma poisson_highSum_isBigO (M N : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑ p ∈ poisson_highPairs M N, poisson_taylorTerm φ x p)
      (fun x : ℝ => G x / x ^ M) := by
  have h :
      (∑ p ∈ poisson_highPairs M N, fun x : ℝ => poisson_taylorTerm φ x p) =O[Filter.atTop]
        (fun x : ℝ => G x / x ^ M) := by
    apply Asymptotics.IsBigO.sum
    intro p hp
    exact poisson_highTerm_isBigO M N hM φ G A hA hG_ge h_deriv p hp
  refine h.congr_left fun x => ?_
  simp only [Finset.sum_apply]

private lemma poisson_evenMoment_hasSum (x : ℝ) (q : ℕ) :
    HasSum
      (fun j : ℕ => Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
        (x ^ j / (Nat.factorial j : ℝ)))
      (∑ r ∈ Finset.range (2 * q + 1),
        (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r) := by
  have hmul := (poisson_central_moment x (2 * q)).mul_left
    (((Real.exp (-x) : ℝ) : ℂ))
  have hpoly :
      (((∑ r ∈ Finset.range (2 * q + 1),
        (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r) : ℝ) : ℂ) =
        ∑ r ∈ Finset.range (2 * q + 1),
          ((twoAssocStirlingSecond (2 * q) r : ℤ) : ℂ) * (x : ℂ) ^ r := by
    push_cast
    rfl
  have hval :
      (((Real.exp (-x) : ℝ) : ℂ)) *
        (((∑ r ∈ Finset.range (2 * q + 1),
          ((twoAssocStirlingSecond (2 * q) r : ℤ) : ℂ) * (x : ℂ) ^ r) *
            (((Real.exp x : ℝ) : ℂ)))) =
        (((∑ r ∈ Finset.range (2 * q + 1),
          (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r) : ℝ) : ℂ) := by
    rw [← hpoly]
    push_cast
    calc
      Complex.exp (-(x : ℂ)) *
          (((∑ r ∈ Finset.range (2 * q + 1),
            ((twoAssocStirlingSecond (2 * q) r : ℤ) : ℂ) * (x : ℂ) ^ r)) *
              Complex.exp (x : ℂ)) =
        (∑ r ∈ Finset.range (2 * q + 1),
          ((twoAssocStirlingSecond (2 * q) r : ℤ) : ℂ) * (x : ℂ) ^ r) *
            (Complex.exp (-(x : ℂ)) * Complex.exp (x : ℂ)) := by ring
      _ = _ := by rw [← Complex.exp_add]; simp
  rw [hval] at hmul
  have hc :
      HasSum
        (fun j : ℕ => (((Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
          (x ^ j / (Nat.factorial j : ℝ))) : ℝ) : ℂ))
        (((∑ r ∈ Finset.range (2 * q + 1),
          (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r) : ℝ) : ℂ) := by
    refine hmul.congr_fun fun j => ?_
    have heven : 0 ≤ ((j : ℝ) - x) ^ (2 * q) := by
      rw [mul_comm 2 q, pow_mul]
      positivity
    have habs : |(j : ℝ) - x| ^ (2 * q) = ((j : ℝ) - x) ^ (2 * q) := by
      rw [← abs_pow, abs_of_nonneg heven]
    rw [habs]
    push_cast
    ring
  have hr := hc.mapL Complex.reCLM
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hr

private lemma poisson_evenMoment_le (x : ℝ) (hx : 1 ≤ x) (q : ℕ) :
    (∑ r ∈ Finset.range (2 * q + 1),
      (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r) ≤
      (∑ r ∈ Finset.range (2 * q + 1),
        |(twoAssocStirlingSecond (2 * q) r : ℝ)|) * x ^ q := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hrq : r ≤ q
  · have hpow : x ^ r ≤ x ^ q := pow_le_pow_right₀ hx hrq
    calc
      (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r ≤
          |(twoAssocStirlingSecond (2 * q) r : ℝ)| * x ^ r := by
        gcongr
        exact le_abs_self _
      _ ≤ |(twoAssocStirlingSecond (2 * q) r : ℝ)| * x ^ q := by
        gcongr
  · push Not at hrq
    have hzero : twoAssocStirlingSecond (2 * q) r = 0 :=
      twoAssocStirlingSecond_eq_zero_of_lt_two_mul (2 * q) r (by omega)
    simp [hzero]

private lemma poisson_tsum_norm_le_evenMoment (x K : ℝ) (q : ℕ) (f : ℕ → ℂ)
    (hf : ∀ j : ℕ, ‖f j‖ ≤ K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
      (x ^ j / (Nat.factorial j : ℝ)))) :
    Summable f ∧
      ‖∑' j : ℕ, f j‖ ≤ K *
        ∑ r ∈ Finset.range (2 * q + 1),
          (twoAssocStirlingSecond (2 * q) r : ℝ) * x ^ r := by
  have hmajor := (poisson_evenMoment_hasSum x q).mul_left K
  have hsum : Summable f := hmajor.summable.of_norm_bounded hf
  refine ⟨hsum, (norm_tsum_le_tsum_norm hsum.norm).trans ?_⟩
  exact (hsum.norm.tsum_le_tsum hf hmajor.summable).trans_eq hmajor.tsum_eq

private lemma poisson_taylor_remainder_eventually (M p : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A C : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hG_poly : ∀ᶠ x in Filter.atTop, ‖G x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    ∀ᶠ x in Filter.atTop, ∀ j : ℕ, x / 2 ≤ (j : ℝ) →
      ‖φ (j : ℝ) - taylorPoly φ (2 * (p + M) - 1) x (j : ℝ)‖ ≤
        (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C * A ^ (2 * (p + M)) *
          2 ^ (2 * (p + M) - p) / x ^ (2 * (p + M) - p)) *
            |(j : ℝ) - x| ^ (2 * (p + M)) := by
  have hq := h_deriv (2 * (p + M)) (by omega)
  rw [Filter.eventually_atTop] at hq hG_poly hG_ge ⊢
  obtain ⟨bq, hq⟩ := hq
  obtain ⟨bpoly, hpoly⟩ := hG_poly
  obtain ⟨bG, hG⟩ := hG_ge
  let b := max 1 (max bq (max bpoly bG))
  refine ⟨2 * b, fun x hx j hj => ?_⟩
  have hb1 : 1 ≤ b := le_max_left _ _
  have hbq : bq ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hbpoly : bpoly ≤ b := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hbG : bG ≤ b := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hx1 : 1 ≤ x := by nlinarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hhalf : b ≤ x / 2 := by nlinarith
  let d := 2 * (p + M) - p
  let D := (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C * A ^ (2 * (p + M)) *
    2 ^ d) / x ^ d
  have hdiff : ∀ k ≤ 2 * (p + M) - 1, ∀ y ∈ Set.Icc (x / 2) (max x (j : ℝ)),
      DifferentiableAt ℝ (iteratedDeriv k φ) y := by
    intro k hk y hy
    have hyb : b ≤ y := le_trans hhalf hy.1
    have hyq := (hq y (le_trans hbq hyb)).1 (k + 1)
    have hmem : k + 1 ∈ Finset.Icc 1 (2 * (p + M)) := by
      rw [Finset.mem_Icc]
      omega
    simpa only [Nat.add_sub_cancel] using hyq hmem
  have htop : ∀ y ∈ Set.Icc (x / 2) (max x (j : ℝ)),
      ‖iteratedDeriv (2 * (p + M)) φ y‖ ≤ D := by
    intro y hy
    have hyb : b ≤ y := le_trans hhalf hy.1
    have hypos : 0 < y := lt_of_lt_of_le (by nlinarith [hb1]) hyb
    have hy0 : y ≠ 0 := ne_of_gt hypos
    have hqy := (hq y (le_trans hbq hyb)).2
    have hGy : G y ≤ C * y ^ p :=
      (Real.le_norm_self (G y)).trans (hpoly y (le_trans hbpoly hyb))
    have hquot :
        ‖iteratedDeriv (2 * (p + M)) φ y‖ ≤
          (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C * A ^ (2 * (p + M))) /
            y ^ d := by
      have hfact : (0 : ℝ) < (Nat.factorial (2 * (p + M)) : ℝ) := by positivity
      rw [norm_div, Complex.norm_natCast] at hqy
      calc
        ‖iteratedDeriv (2 * (p + M)) φ y‖ =
            (Nat.factorial (2 * (p + M)) : ℝ) *
              (‖iteratedDeriv (2 * (p + M)) φ y‖ /
                (Nat.factorial (2 * (p + M)) : ℝ)) := by field_simp
        _ ≤ (Nat.factorial (2 * (p + M)) : ℝ) *
            (G y * (A / y) ^ (2 * (p + M))) := by gcongr
        _ ≤ (Nat.factorial (2 * (p + M)) : ℝ) *
            ((C * y ^ p) * (A / y) ^ (2 * (p + M))) := by
          gcongr
        _ = (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C *
            A ^ (2 * (p + M))) / y ^ d := by
          simp only [d]
          rw [div_pow]
          field_simp
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
    have hpow : (x / 2) ^ d ≤ y ^ d :=
      pow_le_pow_left₀ (by positivity) hy.1 d
    have hinv : 1 / y ^ d ≤ 2 ^ d / x ^ d := by
      calc
        1 / y ^ d ≤ 1 / (x / 2) ^ d :=
          one_div_le_one_div_of_le (pow_pos (by positivity) d) hpow
        _ = 2 ^ d / x ^ d := by
          rw [div_pow]
          field_simp
    calc
      ‖iteratedDeriv (2 * (p + M)) φ y‖ ≤
          (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C * A ^ (2 * (p + M))) /
            y ^ d := hquot
      _ ≤ (((Nat.factorial (2 * (p + M)) : ℕ) : ℝ) * C *
          A ^ (2 * (p + M))) * (2 ^ d / x ^ d) := by
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [one_div] using hinv
      _ = D := by
        simp only [D]
        ring
  have htop' : ∀ y ∈ Set.Icc (x / 2) (max x (j : ℝ)),
      ‖iteratedDeriv (2 * (p + M) - 1 + 1) φ y‖ ≤ D := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * (p + M))] using htop
  have hrem := taylor_remainder_bound φ (x / 2) (max x (j : ℝ)) x
    (by exact le_trans (by linarith) (le_max_left _ _))
    (Set.mem_Icc.mpr ⟨by linarith, le_max_left _ _⟩)
    (2 * (p + M) - 1) hdiff D htop' (j : ℝ)
    (Set.mem_Icc.mpr ⟨hj, le_max_right _ _⟩)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * (p + M)), D, d] using hrem

private noncomputable def poisson_weight (x : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-x) * (x ^ j / (Nat.factorial j : ℝ))

private noncomputable def poisson_centralError (p M : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if x / 2 ≤ (j : ℝ) then
    (poisson_weight x j : ℂ) *
      (φ (j : ℝ) - taylorPoly φ (2 * (p + M) - 1) x (j : ℝ))
  else 0

private lemma poisson_centralError_isBigO (M p : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A C : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hG_poly : ∀ᶠ x in Filter.atTop, ‖G x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ, poisson_centralError p M φ x j)
      (fun x : ℝ => G x / x ^ M) := by
  let q := p + M
  let d := 2 * q - p
  let K := (Nat.factorial (2 * q) : ℝ) * C * A ^ (2 * q) * 2 ^ d
  let B := ∑ r ∈ Finset.range (2 * q + 1),
    |(twoAssocStirlingSecond (2 * q) r : ℝ)|
  have hK : 0 ≤ K := by positivity
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Asymptotics.IsBigO.of_bound (K * B) ?_
  filter_upwards [poisson_taylor_remainder_eventually M p hM φ G A C hA hC
      hG_poly hG_ge h_deriv, hG_ge, Filter.eventually_ge_atTop (1 : ℝ)] with
      x hrem hG hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hxd : 0 ≤ K / x ^ d := div_nonneg hK (pow_nonneg hxpos.le d)
  have hterm : ∀ j : ℕ, ‖poisson_centralError p M φ x j‖ ≤
      (K / x ^ d) * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
        (x ^ j / (Nat.factorial j : ℝ))) := by
    intro j
    by_cases hj : x / 2 ≤ (j : ℝ)
    · have hw : 0 ≤ poisson_weight x j := by
        exact mul_nonneg (Real.exp_pos _).le
          (div_nonneg (pow_nonneg hxpos.le j) (Nat.cast_nonneg _))
      have hr := hrem j hj
      have hr' :
          ‖φ (j : ℝ) - taylorPoly φ (2 * (p + M) - 1) x (j : ℝ)‖ ≤
            (K / x ^ d) * |(j : ℝ) - x| ^ (2 * q) := by
        simpa only [K, d, q] using hr
      simp only [poisson_centralError, hj, ↓reduceIte]
      rw [norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        poisson_weight x j *
            ‖φ (j : ℝ) - taylorPoly φ (2 * (p + M) - 1) x (j : ℝ)‖ ≤
          poisson_weight x j * ((K / x ^ d) * |(j : ℝ) - x| ^ (2 * q)) := by
            gcongr
        _ = (K / x ^ d) * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
            (x ^ j / (Nat.factorial j : ℝ))) := by
          simp only [poisson_weight]
          ring
    · simp only [poisson_centralError, hj, ↓reduceIte, norm_zero]
      positivity
  have hsum := poisson_tsum_norm_le_evenMoment x (K / x ^ d) q
    (poisson_centralError p M φ x) hterm
  have hmoment := poisson_evenMoment_le x hx q
  have hbound : ‖∑' j : ℕ, poisson_centralError p M φ x j‖ ≤
      (K / x ^ d) * (B * x ^ q) := hsum.2.trans (mul_le_mul_of_nonneg_left hmoment hxd)
  have hd : d = q + M := by simp only [d, q]; omega
  have htarget : ‖G x / x ^ M‖ = G x / x ^ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (by linarith) (pow_nonneg hxpos.le M)
  calc
    ‖∑' j : ℕ, poisson_centralError p M φ x j‖ ≤
        (K / x ^ d) * (B * x ^ q) := hbound
    _ = (K * B) * (1 / x ^ M) := by
      rw [hd, pow_add]
      field_simp
    _ ≤ (K * B) * (G x / x ^ M) := by
      gcongr
    _ = (K * B) * ‖G x / x ^ M‖ := by rw [htarget]

private lemma poisson_global_nat_bound (p : ℕ) (φ : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j : ℕ, ‖φ (j : ℝ)‖ ≤ L * ((j : ℝ) + 1) ^ p := by
  rw [Filter.eventually_atTop] at hφ
  obtain ⟨b, hb⟩ := hφ
  let N := Nat.ceil b
  let E := ∑ i ∈ Finset.range N, ‖φ (i : ℝ)‖
  refine ⟨C + E, add_nonneg hC (Finset.sum_nonneg fun _ _ => norm_nonneg _), fun j => ?_⟩
  have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hbase : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    linarith
  have hpow : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ p := one_le_pow₀ hbase
  by_cases hj : N ≤ j
  · have hbj : b ≤ (j : ℝ) :=
      (Nat.le_ceil b).trans (Nat.cast_le.mpr hj)
    calc
      ‖φ (j : ℝ)‖ ≤ C * (j : ℝ) ^ p := hb _ hbj
      _ ≤ C * ((j : ℝ) + 1) ^ p := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (a := (j : ℝ)) (b := (j : ℝ) + 1)
            hjnonneg (by linarith) p) hC
      _ ≤ (C + E) * ((j : ℝ) + 1) ^ p := by
        gcongr
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  · have hjN : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hjE : ‖φ (j : ℝ)‖ ≤ E := by
      simpa only [E] using
        Finset.single_le_sum (s := Finset.range N)
          (f := fun i : ℕ => ‖φ (i : ℝ)‖) (fun i _ => norm_nonneg (φ (i : ℝ))) hjN
    calc
      ‖φ (j : ℝ)‖ ≤ E := hjE
      _ ≤ C + E := by linarith
      _ ≤ (C + E) * ((j : ℝ) + 1) ^ p := by
        calc
          C + E = (C + E) * 1 := by ring
          _ ≤ (C + E) * ((j : ℝ) + 1) ^ p :=
            mul_le_mul_of_nonneg_left hpow
              (add_nonneg hC (Finset.sum_nonneg fun i _ => norm_nonneg (φ (i : ℝ))))

private noncomputable def poisson_leftPhi (F : Finset ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    if j ∈ F then 0 else (poisson_weight x j : ℂ) * φ (j : ℝ)
  else 0

private lemma poisson_leftPhi_isBigO (M p : ℕ) (_hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (F : Finset ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hφ : ∀ j : ℕ, ‖φ (j : ℝ)‖ ≤ L * ((j : ℝ) + 1) ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ, poisson_leftPhi F φ x j)
      (fun x : ℝ => G x / x ^ M) := by
  let q := p + M
  let B := ∑ r ∈ Finset.range (2 * q + 1),
    |(twoAssocStirlingSecond (2 * q) r : ℝ)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Asymptotics.IsBigO.of_bound (L * B * 2 ^ (2 * q)) ?_
  filter_upwards [hG_ge, Filter.eventually_ge_atTop (2 : ℝ)] with x hG hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  let K := L * x ^ p * (2 / x) ^ (2 * q)
  have hK : 0 ≤ K := by positivity
  have hterm : ∀ j : ℕ, ‖poisson_leftPhi F φ x j‖ ≤
      K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
        (x ^ j / (Nat.factorial j : ℝ))) := by
    intro j
    by_cases hj : (j : ℝ) < x / 2
    · have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjx : (j : ℝ) + 1 ≤ x := by linarith
      have hhalf : x / 2 ≤ |(j : ℝ) - x| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hpow : (x / 2) ^ (2 * q) ≤ |(j : ℝ) - x| ^ (2 * q) :=
        pow_le_pow_left₀ (by positivity) hhalf (2 * q)
      have hmarkov : (1 : ℝ) ≤
          (2 / x) ^ (2 * q) * |(j : ℝ) - x| ^ (2 * q) := by
        calc
          (1 : ℝ) = (2 / x) ^ (2 * q) * (x / 2) ^ (2 * q) := by
            rw [← mul_pow]
            have : 2 / x * (x / 2) = (1 : ℝ) := by field_simp
            rw [this, one_pow]
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      have hw : 0 ≤ poisson_weight x j := by
        exact mul_nonneg (Real.exp_pos _).le
          (div_nonneg (pow_nonneg hxpos.le j) (Nat.cast_nonneg _))
      have hφj : ‖φ (j : ℝ)‖ ≤ L * x ^ p :=
        (hφ j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hjx p) hL)
      by_cases hjF : j ∈ F
      · simp only [poisson_leftPhi, hj, hjF, ↓reduceIte, norm_zero]
        positivity
      · simp only [poisson_leftPhi, hj, hjF, ↓reduceIte]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
        calc
          poisson_weight x j * ‖φ (j : ℝ)‖ ≤
              poisson_weight x j * (L * x ^ p) := by gcongr
          _ ≤ poisson_weight x j * (L * x ^ p) *
              ((2 / x) ^ (2 * q) * |(j : ℝ) - x| ^ (2 * q)) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hmarkov
              (mul_nonneg hw (mul_nonneg hL (pow_nonneg hxpos.le p)))
          _ = K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
              (x ^ j / (Nat.factorial j : ℝ))) := by
            simp only [K, poisson_weight]
            ring
    · simp only [poisson_leftPhi, hj, ↓reduceIte, norm_zero]
      positivity
  have hsum := poisson_tsum_norm_le_evenMoment x K q (poisson_leftPhi F φ x) hterm
  have hmoment := poisson_evenMoment_le x (by linarith) q
  have hbound : ‖∑' j : ℕ, poisson_leftPhi F φ x j‖ ≤
      K * (B * x ^ q) := hsum.2.trans (mul_le_mul_of_nonneg_left hmoment hK)
  have htarget : ‖G x / x ^ M‖ = G x / x ^ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (by linarith) (pow_nonneg hxpos.le M)
  calc
    ‖∑' j : ℕ, poisson_leftPhi F φ x j‖ ≤ K * (B * x ^ q) := hbound
    _ = (L * B * 2 ^ (2 * q)) * (1 / x ^ M) := by
      simp only [K, q]
      rw [div_pow]
      field_simp
      ring
    _ ≤ (L * B * 2 ^ (2 * q)) * (G x / x ^ M) := by gcongr
    _ = (L * B * 2 ^ (2 * q)) * ‖G x / x ^ M‖ := by rw [htarget]

private noncomputable def poisson_leftTaylorTerm (n : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    (poisson_weight x j : ℂ) * ((((j : ℝ) - x) ^ n : ℝ) : ℂ) *
      (iteratedDeriv n φ x / (Nat.factorial n : ℂ))
  else 0

private lemma poisson_leftTaylorTerm_zero_isBigO (M p : ℕ)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hφ_poly : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ, poisson_leftTaylorTerm 0 φ x j)
      (fun x : ℝ => G x / x ^ M) := by
  let q := p + M
  let B := ∑ r ∈ Finset.range (2 * q + 1),
    |(twoAssocStirlingSecond (2 * q) r : ℝ)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Asymptotics.IsBigO.of_bound (C * B * 2 ^ (2 * q)) ?_
  filter_upwards [hφ_poly, hG_ge, Filter.eventually_ge_atTop (2 : ℝ)] with x hφ hG hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  let K := C * x ^ p * (2 / x) ^ (2 * q)
  have hK : 0 ≤ K := by positivity
  have hterm : ∀ j : ℕ, ‖poisson_leftTaylorTerm 0 φ x j‖ ≤
      K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
        (x ^ j / (Nat.factorial j : ℝ))) := by
    intro j
    by_cases hj : (j : ℝ) < x / 2
    · have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hhalf : x / 2 ≤ |(j : ℝ) - x| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hpow : (x / 2) ^ (2 * q) ≤ |(j : ℝ) - x| ^ (2 * q) :=
        pow_le_pow_left₀ (by positivity) hhalf (2 * q)
      have hmarkov : (1 : ℝ) ≤
          (2 / x) ^ (2 * q) * |(j : ℝ) - x| ^ (2 * q) := by
        calc
          (1 : ℝ) = (2 / x) ^ (2 * q) * (x / 2) ^ (2 * q) := by
            rw [← mul_pow]
            have : 2 / x * (x / 2) = (1 : ℝ) := by field_simp
            rw [this, one_pow]
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      have hw : 0 ≤ poisson_weight x j := by
        exact mul_nonneg (Real.exp_pos _).le
          (div_nonneg (pow_nonneg hxpos.le j) (Nat.cast_nonneg _))
      simp only [poisson_leftTaylorTerm, hj, ↓reduceIte, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, iteratedDeriv_zero, Complex.ofReal_one, mul_one]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        poisson_weight x j * ‖φ x‖ ≤ poisson_weight x j * (C * x ^ p) := by gcongr
        _ ≤ poisson_weight x j * (C * x ^ p) *
            ((2 / x) ^ (2 * q) * |(j : ℝ) - x| ^ (2 * q)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hmarkov
            (mul_nonneg hw (mul_nonneg hC (pow_nonneg hxpos.le p)))
        _ = K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
            (x ^ j / (Nat.factorial j : ℝ))) := by
          simp only [K, poisson_weight]
          ring
    · simp only [poisson_leftTaylorTerm, hj, ↓reduceIte, norm_zero]
      positivity
  have hsum := poisson_tsum_norm_le_evenMoment x K q
    (poisson_leftTaylorTerm 0 φ x) hterm
  have hmoment := poisson_evenMoment_le x (by linarith) q
  have hbound : ‖∑' j : ℕ, poisson_leftTaylorTerm 0 φ x j‖ ≤
      K * (B * x ^ q) := hsum.2.trans (mul_le_mul_of_nonneg_left hmoment hK)
  have htarget : ‖G x / x ^ M‖ = G x / x ^ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (by linarith) (pow_nonneg hxpos.le M)
  calc
    ‖∑' j : ℕ, poisson_leftTaylorTerm 0 φ x j‖ ≤ K * (B * x ^ q) := hbound
    _ = (C * B * 2 ^ (2 * q)) * (1 / x ^ M) := by
      simp only [K, q]
      rw [div_pow]
      field_simp
      ring
    _ ≤ (C * B * 2 ^ (2 * q)) * (G x / x ^ M) := by gcongr
    _ = (C * B * 2 ^ (2 * q)) * ‖G x / x ^ M‖ := by rw [htarget]

private lemma poisson_leftTaylorTerm_pos_isBigO (M p n : ℕ) (hn : 0 < n)
    (hnq : n ≤ 2 * (p + M)) (φ : ℝ → ℂ) (G : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ, poisson_leftTaylorTerm n φ x j)
      (fun x : ℝ => G x / x ^ M) := by
  let q := p + M
  let r := 2 * q - n
  let B := ∑ s ∈ Finset.range (2 * q + 1),
    |(twoAssocStirlingSecond (2 * q) s : ℝ)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Asymptotics.IsBigO.of_bound (A ^ n * 2 ^ r * B) ?_
  filter_upwards [h_deriv n hn, hG_ge, Filter.eventually_ge_atTop (2 : ℝ)] with
      x hder hG hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hG0 : 0 ≤ G x := by linarith
  have hnr : n + r = 2 * q := by simp only [r, q]; omega
  let K := G x * (A / x) ^ n * (2 / x) ^ r
  have hK : 0 ≤ K := by positivity
  have hterm : ∀ j : ℕ, ‖poisson_leftTaylorTerm n φ x j‖ ≤
      K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
        (x ^ j / (Nat.factorial j : ℝ))) := by
    intro j
    by_cases hj : (j : ℝ) < x / 2
    · have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hhalf : x / 2 ≤ |(j : ℝ) - x| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hpow : (x / 2) ^ r ≤ |(j : ℝ) - x| ^ r :=
        pow_le_pow_left₀ (by positivity) hhalf r
      have hmarkov : |(j : ℝ) - x| ^ n ≤
          (2 / x) ^ r * |(j : ℝ) - x| ^ (2 * q) := by
        have hone : (1 : ℝ) ≤ (2 / x) ^ r * |(j : ℝ) - x| ^ r := by
          calc
            (1 : ℝ) = (2 / x) ^ r * (x / 2) ^ r := by
              rw [← mul_pow]
              have : 2 / x * (x / 2) = (1 : ℝ) := by field_simp
              rw [this, one_pow]
            _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
        calc
          |(j : ℝ) - x| ^ n = |(j : ℝ) - x| ^ n * 1 := by ring
          _ ≤ |(j : ℝ) - x| ^ n *
              ((2 / x) ^ r * |(j : ℝ) - x| ^ r) := by gcongr
          _ = (2 / x) ^ r * |(j : ℝ) - x| ^ (2 * q) := by
            calc
              |(j : ℝ) - x| ^ n *
                  ((2 / x) ^ r * |(j : ℝ) - x| ^ r) =
                (2 / x) ^ r *
                  (|(j : ℝ) - x| ^ n * |(j : ℝ) - x| ^ r) := by ring
              _ = _ := by rw [← pow_add, hnr]
      have hw : 0 ≤ poisson_weight x j := by
        exact mul_nonneg (Real.exp_pos _).le
          (div_nonneg (pow_nonneg hxpos.le j) (Nat.cast_nonneg _))
      have hwnorm : ‖(poisson_weight x j : ℂ)‖ = poisson_weight x j := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      have hpownorm : ‖((((j : ℝ) - x) ^ n : ℝ) : ℂ)‖ =
          |(j : ℝ) - x| ^ n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]
      simp only [poisson_leftTaylorTerm, hj, ↓reduceIte]
      rw [norm_mul, norm_mul, hwnorm, hpownorm]
      calc
        poisson_weight x j * |(j : ℝ) - x| ^ n *
            ‖iteratedDeriv n φ x / (Nat.factorial n : ℂ)‖ ≤
          poisson_weight x j * |(j : ℝ) - x| ^ n *
            (G x * (A / x) ^ n) := by gcongr; exact hder.2
        _ ≤ poisson_weight x j *
            ((2 / x) ^ r * |(j : ℝ) - x| ^ (2 * q)) *
              (G x * (A / x) ^ n) := by gcongr
        _ = K * (Real.exp (-x) * |(j : ℝ) - x| ^ (2 * q) *
            (x ^ j / (Nat.factorial j : ℝ))) := by
          simp only [K, poisson_weight]
          ring
    · simp only [poisson_leftTaylorTerm, hj, ↓reduceIte, norm_zero]
      positivity
  have hsum := poisson_tsum_norm_le_evenMoment x K q
    (poisson_leftTaylorTerm n φ x) hterm
  have hmoment := poisson_evenMoment_le x (by linarith) q
  have hbound : ‖∑' j : ℕ, poisson_leftTaylorTerm n φ x j‖ ≤
      K * (B * x ^ q) := hsum.2.trans (mul_le_mul_of_nonneg_left hmoment hK)
  have hqM : M ≤ q := by simp only [q]; omega
  have hratio : G x / x ^ q ≤ G x / x ^ M :=
    div_le_div_of_nonneg_left hG0 (pow_pos hxpos M) (pow_le_pow_right₀ (by linarith) hqM)
  have htarget : ‖G x / x ^ M‖ = G x / x ^ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg hG0 (pow_nonneg hxpos.le M)
  calc
    ‖∑' j : ℕ, poisson_leftTaylorTerm n φ x j‖ ≤ K * (B * x ^ q) := hbound
    _ = (A ^ n * 2 ^ r * B) * (G x / x ^ q) := by
      simp only [K]
      rw [div_pow, div_pow]
      field_simp
      rw [← pow_add, hnr]
      ring
    _ ≤ (A ^ n * 2 ^ r * B) * (G x / x ^ M) := by gcongr
    _ = (A ^ n * 2 ^ r * B) * ‖G x / x ^ M‖ := by rw [htarget]

private lemma poisson_leftTaylorTerm_summable (n : ℕ) (φ : ℝ → ℂ) (x : ℝ) :
    Summable (poisson_leftTaylorTerm n φ x) := by
  have hfull := ((poisson_central_moment x n).mul_left ((Real.exp (-x) : ℝ) : ℂ)).mul_right
    (iteratedDeriv n φ x / (Nat.factorial n : ℂ))
  have hfull' : Summable (fun j : ℕ =>
      (poisson_weight x j : ℂ) * ((((j : ℝ) - x) ^ n : ℝ) : ℂ) *
        (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
    refine (hfull.congr_fun fun j => ?_).summable
    simp only [poisson_weight]
    push_cast
    ring
  apply Summable.of_norm_bounded hfull'.norm
  intro j
  by_cases hj : (j : ℝ) < x / 2
  · simp only [poisson_leftTaylorTerm, hj, ↓reduceIte]
    exact le_rfl
  · simp only [poisson_leftTaylorTerm, hj, ↓reduceIte, norm_zero]
    exact norm_nonneg _

private noncomputable def poisson_leftTaylor (p M : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    (poisson_weight x j : ℂ) * taylorPoly φ (2 * (p + M) - 1) x (j : ℝ)
  else 0

private lemma poisson_leftTaylor_eq_sum (p M : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (x : ℝ) (j : ℕ) :
    poisson_leftTaylor p M φ x j =
      ∑ n ∈ Finset.range (2 * (p + M)), poisson_leftTaylorTerm n φ x j := by
  by_cases hj : (j : ℝ) < x / 2
  · simp only [poisson_leftTaylor, hj, ↓reduceIte, poisson_leftTaylorTerm]
    rw [taylorPoly, Finset.mul_sum]
    have horder : 2 * (p + M) - 1 + 1 = 2 * (p + M) :=
      Nat.sub_add_cancel (by omega)
    rw [horder]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  · simp only [poisson_leftTaylor, hj, ↓reduceIte, poisson_leftTaylorTerm]
    exact (Finset.sum_eq_zero fun _ _ => rfl).symm

private lemma poisson_leftTaylor_isBigO (M p : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A C : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hφ_poly : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ, poisson_leftTaylor p M φ x j)
      (fun x : ℝ => G x / x ^ M) := by
  have hsum :
      (∑ n ∈ Finset.range (2 * (p + M)),
        fun x : ℝ => ∑' j : ℕ, poisson_leftTaylorTerm n φ x j) =O[Filter.atTop]
          (fun x : ℝ => G x / x ^ M) := by
    apply Asymptotics.IsBigO.sum
    intro n hn
    rw [Finset.mem_range] at hn
    by_cases hn0 : n = 0
    · subst n
      exact poisson_leftTaylorTerm_zero_isBigO M p φ G C hC hφ_poly hG_ge
    · exact poisson_leftTaylorTerm_pos_isBigO M p n (Nat.pos_of_ne_zero hn0)
        (by omega) φ G A hA hG_ge h_deriv
  refine hsum.congr_left fun x => ?_
  simp only [Finset.sum_apply]
  have hs := hasSum_sum fun n (_ : n ∈ Finset.range (2 * (p + M))) =>
    (poisson_leftTaylorTerm_summable n φ x).hasSum
  have hs' : HasSum (poisson_leftTaylor p M φ x)
      (∑ n ∈ Finset.range (2 * (p + M)),
        ∑' j : ℕ, poisson_leftTaylorTerm n φ x j) :=
    hs.congr_fun fun j => poisson_leftTaylor_eq_sum p M hM φ x j
  exact hs'.tsum_eq.symm

private noncomputable def poisson_selected (F : Finset ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if j ∈ F then 0 else (poisson_weight x j : ℂ) * φ (j : ℝ)

private noncomputable def poisson_normalizedTaylor (φ : ℝ → ℂ) (N : ℕ)
    (x : ℝ) (j : ℕ) : ℂ :=
  (poisson_weight x j : ℂ) * taylorPoly φ N x (j : ℝ)

private lemma poisson_selected_summable_eventually (p : ℕ) (φ : ℝ → ℂ)
    (F : Finset ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hφ_poly : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p) :
    ∀ᶠ x in Filter.atTop, Summable (poisson_selected F φ x) := by
  obtain ⟨L, hL, hφnat⟩ := poisson_global_nat_bound p φ C hC hφ_poly
  apply Filter.Eventually.of_forall
  intro x
  let R := |x| * (2 : ℝ) ^ p
  let D := Real.exp (-x) * L * (2 : ℝ) ^ p
  have hmajor : Summable (fun j : ℕ => D * R ^ j / (Nat.factorial j : ℝ)) := by
    have h := (Real.summable_pow_div_factorial R).mul_left D
    refine h.congr fun j => ?_
    ring
  apply Summable.of_norm_bounded hmajor
  intro j
  have hjNat : j + 1 ≤ 2 ^ (j + 1) := Nat.le_of_lt (j + 1).lt_two_pow_self
  have hjReal : (j : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast hjNat
  have hjpow : ((j : ℝ) + 1) ^ p ≤
      (2 : ℝ) ^ p * ((2 : ℝ) ^ p) ^ j := by
    calc
      ((j : ℝ) + 1) ^ p ≤ ((2 : ℝ) ^ (j + 1)) ^ p :=
        pow_le_pow_left₀ (by positivity) hjReal p
      _ = ((2 : ℝ) ^ p) ^ (j + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (j + 1) p]
      _ = (2 : ℝ) ^ p * ((2 : ℝ) ^ p) ^ j := by
        rw [pow_succ]
        ring
  have hD : 0 ≤ D := by positivity
  by_cases hjF : j ∈ F
  · simp only [poisson_selected, hjF, ↓reduceIte, norm_zero]
    positivity
  · have hweightNorm : ‖(poisson_weight x j : ℂ)‖ =
        Real.exp (-x) * (|x| ^ j / (Nat.factorial j : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp only [poisson_weight, abs_mul, abs_div, abs_pow, Real.abs_exp]
      have hfactabs : |(Nat.factorial j : ℝ)| = (Nat.factorial j : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [hfactabs]
    simp only [poisson_selected, hjF, ↓reduceIte, norm_mul, hweightNorm]
    calc
      Real.exp (-x) * (|x| ^ j / (Nat.factorial j : ℝ)) * ‖φ (j : ℝ)‖ ≤
          Real.exp (-x) * (|x| ^ j / (Nat.factorial j : ℝ)) *
            (L * ((j : ℝ) + 1) ^ p) := by
        gcongr
        exact hφnat j
      _ ≤ Real.exp (-x) * (|x| ^ j / (Nat.factorial j : ℝ)) *
            (L * ((2 : ℝ) ^ p * ((2 : ℝ) ^ p) ^ j)) := by
        gcongr
      _ = D * R ^ j / (Nat.factorial j : ℝ) := by
        simp only [D, R, mul_pow]
        ring

private lemma poisson_normalizedTaylor_hasSum (φ : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    HasSum (poisson_normalizedTaylor φ N x)
      (∑ n ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (n + 1),
          ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
            (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
  have h := (poisson_taylor_hasSum φ N x).mul_left (((Real.exp (-x) : ℝ) : ℂ))
  have hval :
      (((Real.exp (-x) : ℝ) : ℂ) *
        (((Real.exp x : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1),
            (∑ r ∈ Finset.range (n + 1),
              ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
                (iteratedDeriv n φ x / (Nat.factorial n : ℂ)))) =
        ∑ n ∈ Finset.range (N + 1),
          (∑ r ∈ Finset.range (n + 1),
            ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ)) := by
    push_cast
    calc
      Complex.exp (-(x : ℂ)) *
          (Complex.exp (x : ℂ) *
            ∑ n ∈ Finset.range (N + 1),
              (∑ r ∈ Finset.range (n + 1),
                ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
                  (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) =
        (∑ n ∈ Finset.range (N + 1),
          (∑ r ∈ Finset.range (n + 1),
            ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) *
            (Complex.exp (-(x : ℂ)) * Complex.exp (x : ℂ)) := by ring
      _ = _ := by rw [← Complex.exp_add]; simp
  rw [hval] at h
  refine h.congr_fun fun j => ?_
  simp only [poisson_normalizedTaylor, poisson_weight]
  push_cast
  ring

private lemma poisson_leftPhi_summable (F : Finset ℕ) (φ : ℝ → ℂ) (x : ℝ)
    (h : Summable (poisson_selected F φ x)) :
    Summable (poisson_leftPhi F φ x) := by
  apply Summable.of_norm_bounded h.norm
  intro j
  by_cases hj : (j : ℝ) < x / 2
  · simp only [poisson_leftPhi, poisson_selected, hj, ↓reduceIte]
    exact le_rfl
  · simp only [poisson_leftPhi, hj, ↓reduceIte, norm_zero]
    exact norm_nonneg _

private lemma poisson_error_term_eq (p M : ℕ) (F : Finset ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (hxF : ((F.sup id : ℕ) : ℝ) < x / 2) (j : ℕ) :
    poisson_selected F φ x j - poisson_normalizedTaylor φ (2 * (p + M) - 1) x j =
      poisson_centralError p M φ x j + poisson_leftPhi F φ x j -
        poisson_leftTaylor p M φ x j := by
  by_cases hj : (j : ℝ) < x / 2
  · have hj' : ¬x / 2 ≤ (j : ℝ) := not_le.mpr hj
    simp only [poisson_selected, poisson_normalizedTaylor, poisson_centralError,
      poisson_leftPhi, poisson_leftTaylor, hj, hj', ↓reduceIte]
    by_cases hjF : j ∈ F <;> simp [hjF]
  · have hj' : x / 2 ≤ (j : ℝ) := le_of_not_gt hj
    have hjF : j ∉ F := by
      intro hjmem
      have hle : j ≤ F.sup id := by
        simpa only [id_eq] using
          (Finset.le_sup (f := (id : ℕ → ℕ)) hjmem)
      have hle' : (j : ℝ) ≤ ((F.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hle
      linarith
    simp only [poisson_selected, poisson_normalizedTaylor, poisson_centralError,
      poisson_leftPhi, poisson_leftTaylor, hj, hj', hjF, ↓reduceIte]
    ring

private lemma poisson_seriesError_isBigO (M p : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (A C : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (F : Finset ℕ)
    (hφ_poly : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p)
    (hG_poly : ∀ᶠ x in Filter.atTop, ‖G x‖ ≤ C * x ^ p)
    (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
    (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
        ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => ∑' j : ℕ,
        (poisson_selected F φ x j -
          poisson_normalizedTaylor φ (2 * (p + M) - 1) x j))
      (fun x : ℝ => G x / x ^ M) := by
  obtain ⟨L, hL, hφnat⟩ := poisson_global_nat_bound p φ C hC hφ_poly
  have hc := poisson_centralError_isBigO M p hM φ G A C hA hC
    hG_poly hG_ge h_deriv
  have hφleft := poisson_leftPhi_isBigO M p hM φ G F L hL hφnat hG_ge
  have htleft := poisson_leftTaylor_isBigO M p hM φ G A C hA hC
    hφ_poly hG_ge h_deriv
  have hparts := hc.add hφleft |>.sub htleft
  apply hparts.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [poisson_selected_summable_eventually p φ F C hC hφ_poly,
    Filter.eventually_ge_atTop (2 * ((F.sup id : ℕ) : ℝ) + 1)] with x hselected hxF
  have hxF' : ((F.sup id : ℕ) : ℝ) < x / 2 := by linarith
  have htaylor := (poisson_normalizedTaylor_hasSum φ (2 * (p + M) - 1) x).summable
  have hleftPhi := poisson_leftPhi_summable F φ x hselected
  have hleftTaylor : Summable (poisson_leftTaylor p M φ x) := by
    rw [show poisson_leftTaylor p M φ x = fun j =>
        ∑ n ∈ Finset.range (2 * (p + M)), poisson_leftTaylorTerm n φ x j by
      funext j
      exact poisson_leftTaylor_eq_sum p M hM φ x j]
    exact summable_sum fun n _ => poisson_leftTaylorTerm_summable n φ x
  have htotal := hselected.sub htaylor
  have hcentral : Summable (poisson_centralError p M φ x) := by
    have h := htotal.sub hleftPhi |>.add hleftTaylor
    refine h.congr fun j => ?_
    have heq := poisson_error_term_eq p M F φ x hxF' j
    linear_combination heq
  have hs := (hcentral.hasSum.add hleftPhi.hasSum).sub hleftTaylor.hasSum
  have hs' : HasSum
      (fun j : ℕ => poisson_selected F φ x j -
        poisson_normalizedTaylor φ (2 * (p + M) - 1) x j)
      ((∑' j : ℕ, poisson_centralError p M φ x j) +
        (∑' j : ℕ, poisson_leftPhi F φ x j) -
          ∑' j : ℕ, poisson_leftTaylor p M φ x j) :=
    hs.congr_fun fun j => poisson_error_term_eq p M F φ x hxF' j
  exact hs'.tsum_eq.symm

private lemma poisson_normalizedTaylor_tsum_eq (M p : ℕ) (hM : 0 < M)
    (φ : ℝ → ℂ) (x : ℝ) :
    (∑' j : ℕ, poisson_normalizedTaylor φ (2 * (p + M) - 1) x j) =
      φ x +
        ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
          (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
            (x : ℂ) ^ (n - k + 1) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) +
        ∑ s ∈ poisson_highPairs M (2 * (p + M) - 1), poisson_taylorTerm φ x s := by
  let N := 2 * (p + M) - 1
  have hN : 2 * M - 2 ≤ N := by simp only [N]; omega
  calc
    (∑' j : ℕ, poisson_normalizedTaylor φ (2 * (p + M) - 1) x j) =
        ∑ n ∈ Finset.range (N + 1),
          (∑ r ∈ Finset.range (n + 1),
            ((twoAssocStirlingSecond n r : ℤ) : ℂ) * (x : ℂ) ^ r) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ)) := by
        simpa only [N] using (poisson_normalizedTaylor_hasSum φ N x).tsum_eq
    _ = ∑ s ∈ poisson_taylorPairs N, poisson_taylorTerm φ x s :=
      poisson_taylor_coeff_sum_eq φ x N
    _ = (∑ s ∈ poisson_lowPairs M N, poisson_taylorTerm φ x s) +
        ∑ s ∈ poisson_highPairs M N, poisson_taylorTerm φ x s :=
      poisson_taylor_sum_split φ x M N
    _ = φ x +
        ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
          (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
            (x : ℂ) ^ (n - k + 1) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) +
        ∑ s ∈ poisson_highPairs M N, poisson_taylorTerm φ x s := by
      rw [poisson_low_sum_eq φ x M N hM hN]
    _ = _ := by simp only [N]

private lemma poisson_selected_tsum_eq (F : Finset ℕ) (φ : ℝ → ℂ) (x : ℝ) :
    ((Real.exp (-x) : ℂ)) *
        (∑' j : ℕ, if j ∈ F then (0 : ℂ) else
          (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ) * φ (j : ℝ))) =
      ∑' j : ℕ, poisson_selected F φ x j := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases hj : j ∈ F
  · simp [poisson_selected, hj]
  · simp only [poisson_selected, hj, ↓reduceIte, poisson_weight]
    push_cast
    ring

/-- **Ramanujan's asymptotic expansion of Poisson averages.** Let $M \ge 1$ be an integer,
$\varphi : \mathbb{R} \to \mathbb{C}$ and $G : \mathbb{R} \to \mathbb{R}$ functions, $A \ge 1$ a
real number and $F$ a finite set of natural numbers. Write $\varphi^{(n)}$ for the $n$-th
iterated derivative of $\varphi$ and $S_2(n, k)$ for the 2-associated Stirling numbers of the
second kind. Assume that there are $C \ge 0$ and $p \in \mathbb{N}$ such that
$|\varphi(x)| \le C x^p$ and $|G(x)| \le C x^p$ for all sufficiently large $x$; that $G(x) \ge 1$
for all sufficiently large $x$; and that for every integer $m \ge 1$ and all sufficiently large
$x$, the derivatives $\varphi^{(0)}, \dots, \varphi^{(m-1)}$ are differentiable at $x$ and
$|\varphi^{(m)}(x)| / m! \le G(x) (A / x)^m$. Then, as $x \to \infty$,
$$e^{-x} \sum_{j \in \mathbb{N} \setminus F} \frac{x^j}{j!} \varphi(j) - \varphi(x) -
\sum_{k=2}^{M} \sum_{n=k}^{2k-2} S_2(n, n + 1 - k) \, x^{n-k+1} \frac{\varphi^{(n)}(x)}{n!}
= O\left(\frac{G(x)}{x^M}\right).$$

Proof: Taylor expansion on the central Poisson range is combined with the associated-Stirling
central-moment identity from Comtet; Berndt's route and even-moment tails control the remainder.

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_poisson_asymptotic`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, printed pp. 57-58 / PDF
    pp. 67-68.
-/
theorem ramanujan_part1_ch3_entry10_poisson_asymptotic
  (M : ℕ) (hM : 0 < M)
  (φ : ℝ → ℂ) (G : ℝ → ℝ) (A : ℝ) (hA : 1 ≤ A)
  (F : Finset ℕ)
  (h_poly : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p ∧ ‖G x‖ ≤ C * x ^ p)
  (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
  (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop,
      (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧
          ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
    Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ =>
      ((Real.exp (-x) : ℂ)) *
          (∑' j : ℕ, if j ∈ F then (0 : ℂ) else
              (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ) * φ (j : ℝ)))
      - φ x
      - ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
          (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) * ((x : ℂ) ^ (n - k + 1)) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))))
    (fun x : ℝ => G x / (x : ℝ) ^ M) := by
  obtain ⟨C, hC, p, hp⟩ := h_poly
  have hφ_poly : ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p :=
    hp.mono fun _ hx => hx.1
  have hG_poly : ∀ᶠ x in Filter.atTop, ‖G x‖ ≤ C * x ^ p :=
    hp.mono fun _ hx => hx.2
  let N := 2 * (p + M) - 1
  have herr := poisson_seriesError_isBigO M p hM φ G A C hA hC F
    hφ_poly hG_poly hG_ge h_deriv
  have hhigh := poisson_highSum_isBigO M N hM φ G A hA hG_ge h_deriv
  have hsum := herr.add hhigh
  apply hsum.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [poisson_selected_summable_eventually p φ F C hC hφ_poly] with x hselected
  have htaylor := (poisson_normalizedTaylor_hasSum φ N x).summable
  have hsub := hselected.tsum_sub htaylor
  have htaylorEq := poisson_normalizedTaylor_tsum_eq M p hM φ x
  have hselectedEq := poisson_selected_tsum_eq F φ x
  calc
    (∑' j : ℕ, (poisson_selected F φ x j - poisson_normalizedTaylor φ N x j)) +
        ∑ s ∈ poisson_highPairs M N, poisson_taylorTerm φ x s =
      ((∑' j : ℕ, poisson_selected F φ x j) -
        ∑' j : ℕ, poisson_normalizedTaylor φ N x j) +
          ∑ s ∈ poisson_highPairs M N, poisson_taylorTerm φ x s := by
        rw [hsub]
    _ = (∑' j : ℕ, poisson_selected F φ x j) - φ x -
        ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
          (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
            (x : ℂ) ^ (n - k + 1) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
      rw [htaylorEq]
      ring
    _ = ((Real.exp (-x) : ℂ)) *
          (∑' j : ℕ, if j ∈ F then (0 : ℂ) else
            (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ) * φ (j : ℝ))) -
        φ x -
        ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
          (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) *
            (x : ℂ) ^ (n - k + 1) *
              (iteratedDeriv n φ x / (Nat.factorial n : ℂ))) := by
      rw [hselectedEq]

end Entry10PoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
