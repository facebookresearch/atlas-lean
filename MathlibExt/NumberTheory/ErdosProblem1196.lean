/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/1196.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definitions `IsPrimitive` and `conjecture` and the statement of
`conjecture_holds`.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős Problem 1196

This file proves the asymptotic upper bound for the reciprocal-logarithmic sum of a
primitive set of natural numbers.

Source record `FC-ErdosProblem1196`, ported from FormalConjectures
`ErdosProblems/1196.lean` (`theorem erdos_1196`) and checked against
erdosproblems.com/1196. The `answer(True)` wrapper is elaborated to the
direct claim. Status: resolved true (site: PROVED (LEAN)).
-/

open scoped Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem1196Wanted

@[expose] public section

/-- **Primitive set in a commutative monoid.** A subset $A$ of a commutative monoid $M$ is
primitive if for all $x, y \in A$ with $x \mid y$, the elements $x$ and $y$ are associated,
that is, $x u = y$ for some unit $u$ of $M$. In $\mathbb{N}$, where $1$ is the only unit, this
says that no element of $A$ divides a different element of $A$. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ∣ y → Associated x y

/-- **Asymptotic primitive set bound.** The statement that there is a function
$o : \mathbb{N} \to \mathbb{R}$ with $o(x) \to 0$ as $x \to \infty$ such that for every natural
number $x > 0$ and every primitive set $A$ of natural numbers contained in $[x, \infty)$, the
series $\sum_{a \in A} \frac{1}{a \log a}$ is summable and
$\sum_{a \in A} \frac{1}{a \log a} < 1 + o(x)$. Here a set of natural numbers is primitive if
no element divides a different element, and the term for $a = 1$, where $\log a = 0$, is taken
to be $0$. -/
def conjecture : Prop :=
  ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x,
    IsPrimitive A →
    Summable (fun a : A => 1 / ((a.val : ℝ).log * a)) ∧
      ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x

end

open Finset Real Filter
open ArithmeticFunction hiding log
open scoped Topology

private noncomputable def mangoldtSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, vonMangoldt d / (d : ℝ)

private noncomputable def shift : ℝ := log 4 + 6

private theorem shift_pos : 0 < shift := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  unfold shift
  linarith

-- Mertens' first estimate, from the divisor expansion of the log factorial.
private theorem mangoldtSum_bounds {n : ℕ} (hn : 0 < n) :
    log (n : ℝ) - 1 ≤ mangoldtSum n ∧ mangoldtSum n ≤ log (n : ℝ) + (shift - 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactorial : log (n.factorial : ℝ) =
      ∑ d ∈ Ioc 0 n, vonMangoldt d * (↑(n / d) : ℝ) := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    have hprod : n.factorial = ∏ d ∈ Ioc 0 n, d := by
      rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ico_add_one_right_eq_Icc,
        Nat.zero_add, Finset.prod_Ico_id_eq_factorial]
    rw [hprod, Nat.cast_prod, Real.log_prod]
    · simp only [ArithmeticFunction.log_apply]
    · exact fun d hd ↦ Nat.cast_ne_zero.mpr (ne_of_gt (mem_Ioc.mp hd).1)
  have hupper : log (n.factorial : ℝ) ≤ (n : ℝ) * log n := by
    have hpow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow
  have hlower : (n : ℝ) * (log n - 1) ≤ log (n.factorial : ℝ) := by
    have hexp := Real.pow_div_factorial_le_exp (n : ℝ) hnR.le n
    have hlog := Real.log_le_log (by positivity) hexp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
    linarith
  have hψ : ∑ d ∈ Ioc 0 n, vonMangoldt d ≤ (log 4 + 4) * (n : ℝ) := by
    refine le_trans ?_ (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    exact sum_le_sum_of_subset_of_nonneg Ioc_subset_Icc_self (fun _ _ _ ↦ vonMangoldt_nonneg)
  constructor
  · apply le_of_mul_le_mul_left _ hnR
    refine hlower.trans ?_
    rw [hfactorial, mangoldtSum, mul_sum]
    refine sum_le_sum fun d _ ↦ ?_
    rw [mul_div_left_comm]
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
  · apply le_of_mul_le_mul_left _ hnR
    have hfloor : (n : ℝ) * mangoldtSum n ≤
        log (n.factorial : ℝ) + ∑ d ∈ Ioc 0 n, vonMangoldt d := by
      rw [hfactorial, mangoldtSum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun d hd ↦ ?_
      have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hlt : (n : ℝ) < ((↑(n / d) : ℝ) + 1) * d := by
        exact_mod_cast Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) (mem_Ioc.mp hd).1
      rw [mul_div_left_comm, ← mul_add_one]
      exact mul_le_mul_of_nonneg_left ((div_lt_iff₀ hdR).2 hlt).le vonMangoldt_nonneg
    unfold shift
    linarith

private theorem mangoldtSum_interval {y z : ℕ} (hy : 0 < y) (hyz : y ≤ z) :
    ∑ q ∈ Icc y z, vonMangoldt q / (q : ℝ) ≤ log (z : ℝ) - log y + shift := by
  have hsplit : (∑ q ∈ Icc y z, vonMangoldt q / (q : ℝ)) + mangoldtSum y =
      mangoldtSum z + vonMangoldt y / (y : ℝ) := by
    rw [mangoldtSum, mangoldtSum, ← sum_Ioc_consecutive _ (Nat.zero_le y) hyz,
      ← Finset.insert_left_Ioc hyz, sum_insert (by simp)]
    ring
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hb : vonMangoldt y / (y : ℝ) ≤ 1 := by
    rw [div_le_one hyR]
    linarith [vonMangoldt_le_log (n := y), Real.log_le_sub_one_of_pos hyR]
  linarith [(mangoldtSum_bounds hy).1, (mangoldtSum_bounds (hy.trans_le hyz)).2]

private noncomputable def tailBound (u : ℝ) : ℝ := u⁻¹ + shift / u ^ 2

private theorem tailBound_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ tailBound u := by
  have := shift_pos
  unfold tailBound
  positivity

private theorem tailBound_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    tailBound v ≤ tailBound u := by
  have := shift_pos
  unfold tailBound
  gcongr

-- Discrete partial summation. The logarithmic increments are dominated by the
-- telescoping differences of the reciprocal of the shifted logarithm.
private theorem sum_mangoldt_weighted_le {L : ℝ} {y z : ℕ}
    (hy : 0 < y) (hyz : y ≤ z) (hL : 0 < L + log (y : ℝ)) :
    ∑ q ∈ Icc y z, (vonMangoldt q / (q : ℝ)) * ((L + log (q : ℝ)) ^ 2)⁻¹ ≤
      tailBound (L + log (y : ℝ)) := by
  let u (q : ℕ) := L + log (q : ℝ)
  let g (q : ℕ) := (u q ^ 2)⁻¹
  let a (q : ℕ) := vonMangoldt q / (q : ℝ)
  let E (z : ℕ) := (∑ q ∈ Icc y z, a q) - (log (z : ℝ) - log y + shift)
  have hu {q : ℕ} (hq : y ≤ q) : 0 < u q := by
    have hlog := Real.log_le_log (show (0 : ℝ) < y by exact_mod_cast hy)
      (show (y : ℝ) ≤ (q : ℝ) by exact_mod_cast hq)
    dsimp [u]
    linarith
  have hmain (z : ℕ) (hz : y ≤ z) :
      ∑ q ∈ Icc y z, a q * g q ≤ E z * g z + tailBound (u y) - (u z)⁻¹ := by
    induction z, hz using Nat.le_induction with
    | base =>
      simp [E, tailBound, g, div_eq_mul_inv]
      ring_nf
      exact le_rfl
    | succ z hz ih =>
      have huz := hu hz
      have huz' := hu (Nat.le_succ_of_le hz)
      have hmono : u z ≤ u (z + 1) := by
        dsimp [u]
        exact add_le_add_right
          (Real.log_le_log (show (0 : ℝ) < z by exact_mod_cast hy.trans_le hz)
            (show (z : ℝ) ≤ ((z + 1 : ℕ) : ℝ) by exact_mod_cast z.le_succ)) L
      have hg : g (z + 1) ≤ g z := by
        dsimp [g]
        gcongr
      have hE : E z ≤ 0 := sub_nonpos.mpr (mangoldtSum_interval hy hz)
      have hE' : E (z + 1) = E z + a (z + 1) - (u (z + 1) - u z) := by
        simp only [E, u, sum_Icc_succ_top (Nat.le_succ_of_le hz)]
        ring
      have hstep : (u (z + 1) - u z) * g (z + 1) ≤ (u z)⁻¹ - (u (z + 1))⁻¹ := by
        dsimp [g]
        field_simp
        nlinarith [sq_nonneg (u (z + 1) - u z)]
      rw [sum_Icc_succ_top (Nat.le_succ_of_le hz), hE']
      have hEg := mul_le_mul_of_nonpos_left hg hE
      linarith
  have he : E z ≤ 0 := sub_nonpos.mpr (mangoldtSum_interval hy hyz)
  refine (hmain z hyz).trans ?_
  have hprod : E z * g z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he (by dsimp [g]; positivity)
  linarith [inv_nonneg.mpr (hu hyz).le]

-- Finite flow form of the downward-chain argument. The set of multiples of the
-- antichain is closed under taking incoming edges. Every edge out of an
-- antichain element leaves that set, up to its zero-weight diagonal edge.
private theorem sum_weight_le_boundary {A I F : Finset ℕ} {e : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    (hAI : A ⊆ I) (hIF : I ⊆ F)
    (hnonneg : ∀ n m, 0 ≤ e n m) (hsupp : ∀ n m, ¬ m ∣ n → e n m = 0)
    (hdiag : ∀ n, e n n = 0) (hA : ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b)
    (hout : ∀ n ∈ I, ∑ m ∈ F, e n m = w n)
    (hin : ∀ m ∈ I, ∑ n ∈ I, e n m ≤ w m) :
    ∑ a ∈ A, w a ≤ ∑ m ∈ F \ I, ∑ n ∈ I, e n m := by
  classical
  let b (m : ℕ) := w m - ∑ n ∈ I, e n m
  let U := I.filter (fun n ↦ ∃ a ∈ A, a ∣ n)
  have hUI : U ⊆ I := filter_subset _ _
  have hAU : A ⊆ U := fun a ha ↦ mem_filter.mpr ⟨hAI ha, a, ha, dvd_rfl⟩
  have hclosed {n m : ℕ} (hn : n ∈ I) (hm : m ∈ U) (hdvd : m ∣ n) : n ∈ U := by
    obtain ⟨a, ha, ham⟩ := (mem_filter.mp hm).2
    exact mem_filter.mpr ⟨hn, a, ha, ham.trans hdvd⟩
  have balance (S : Finset ℕ) (hSI : S ⊆ I)
      (hS : ∀ {n m : ℕ}, n ∈ I → m ∈ S → m ∣ n → n ∈ S) :
      ∑ m ∈ S, b m = ∑ n ∈ S, ∑ m ∈ F \ S, e n m := by
    have henter (m : ℕ) (hm : m ∈ S) : ∑ n ∈ I, e n m = ∑ n ∈ S, e n m := by
      symm
      exact sum_subset hSI fun n hn hnot ↦ hsupp n m (fun hdvd ↦ hnot (hS hn hm hdvd))
    calc
      ∑ m ∈ S, b m = (∑ m ∈ S, w m) - ∑ m ∈ S, ∑ n ∈ S, e n m := by
        simp only [b, sum_sub_distrib, sum_congr rfl henter]
      _ = ∑ n ∈ S, (w n - ∑ m ∈ S, e n m) := by rw [sum_sub_distrib, sum_comm]
      _ = ∑ n ∈ S, ∑ m ∈ F \ S, e n m := by
        refine sum_congr rfl fun n hn ↦ ?_
        rw [← hout n (hSI hn), ← sum_sdiff (hSI.trans hIF)]
        exact add_sub_cancel_right _ _
  have hleave (a : ℕ) (ha : a ∈ A) : ∑ m ∈ F \ U, e a m = w a := by
    have hzero : ∑ m ∈ U, e a m = 0 := by
      apply sum_eq_zero
      intro m hm
      by_cases hdvd : m ∣ a
      · obtain ⟨a', ha', ha'm⟩ := (mem_filter.mp hm).2
        have hsame := hA a' ha' a ha (ha'm.trans hdvd)
        have : m = a := Nat.dvd_antisymm hdvd (hsame ▸ ha'm)
        simpa [this] using hdiag a
      · exact hsupp a m hdvd
    have hsplit := sum_sdiff (hUI.trans hIF) (f := e a)
    simpa [hzero, hout a (hAI ha)] using hsplit
  calc
    ∑ a ∈ A, w a = ∑ a ∈ A, ∑ m ∈ F \ U, e a m := sum_congr rfl fun a ha ↦ (hleave a ha).symm
    _ ≤ ∑ n ∈ U, ∑ m ∈ F \ U, e n m :=
      sum_le_sum_of_subset_of_nonneg hAU fun n _ _ ↦ sum_nonneg fun m _ ↦ hnonneg n m
    _ = ∑ m ∈ U, b m := (balance U hUI hclosed).symm
    _ ≤ ∑ m ∈ I, b m :=
      sum_le_sum_of_subset_of_nonneg hUI fun m hm _ ↦ sub_nonneg.mpr (hin m hm)
    _ = ∑ m ∈ F \ I, ∑ n ∈ I, e n m := by
      rw [balance I (Subset.rfl) (fun hn _ _ ↦ hn), sum_comm]

private noncomputable def edge (n m : ℕ) : ℝ :=
  if m ∣ n then vonMangoldt (n / m) / ((n : ℝ) * (log (n : ℝ) - shift) ^ 2) else 0

private noncomputable def weight (n : ℕ) : ℝ :=
  log (n : ℝ) / ((n : ℝ) * (log (n : ℝ) - shift) ^ 2)

private noncomputable def erdosTerm (n : ℕ) : ℝ := 1 / (log (n : ℝ) * n)

private theorem edge_nonneg (n m : ℕ) : 0 ≤ edge n m := by
  unfold edge
  split
  · exact div_nonneg vonMangoldt_nonneg (by positivity)
  · exact le_rfl

private theorem sum_edge_eq_weight {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    ∑ m ∈ Icc 1 N, edge n m = weight n := by
  have hsub : n.divisors ⊆ Icc 1 N := by
    intro m hm
    have h := (Nat.mem_divisors.mp hm).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h hn, (Nat.le_of_dvd hn h).trans hnN⟩
  calc
    ∑ m ∈ Icc 1 N, edge n m = ∑ m ∈ n.divisors, edge n m := by
      symm
      refine sum_subset hsub fun m _ hm ↦ ite_eq_right (fun hd ↦ hm ?_)
      exact Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩
    _ = weight n := by
      have h (m : ℕ) (hm : m ∈ n.divisors) :
          edge n m = vonMangoldt (n / m) / ((n : ℝ) * (log (n : ℝ) - shift) ^ 2) :=
        ite_eq_left (Nat.mem_divisors.mp hm).1
      rw [sum_congr rfl h, ← sum_div, Nat.sum_div_divisors, vonMangoldt_sum, weight]

private theorem erdosTerm_nonneg (n : ℕ) : 0 ≤ erdosTerm n :=
  div_nonneg zero_le_one (mul_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))

private theorem erdosTerm_le_weight {n : ℕ} (hn : shift < log (n : ℝ)) :
    erdosTerm n ≤ weight n := by
  have hlog := shift_pos.trans hn
  have hsub : 0 < log (n : ℝ) - shift := sub_pos.mpr hn
  have hpos : (0 : ℝ) < n := by
    by_contra! hz
    have : n = 0 := by exact_mod_cast (le_antisymm hz (Nat.cast_nonneg n))
    simp [this] at hlog
  rw [erdosTerm, weight, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    1 * ((n : ℝ) * (log (n : ℝ) - shift) ^ 2) ≤ (n : ℝ) * log (n : ℝ) ^ 2 := by
      rw [one_mul]
      gcongr
      exact sub_le_self _ shift_pos.le
    _ = log (n : ℝ) * (log (n : ℝ) * n) := by ring

private theorem sum_edge_le {S : Finset ℕ} {m y N : ℕ}
    (hm : 0 < m) (hy : 0 < y) (hL : 0 < log (m : ℝ) - shift + log (y : ℝ))
    (hS : ∀ n ∈ S, m ∣ n → m * y ≤ n ∧ n ≤ N) :
    ∑ n ∈ S, edge n m ≤ (m : ℝ)⁻¹ * tailBound (log (m : ℝ) - shift + log (y : ℝ)) := by
  let T := S.filter (fun n ↦ m ∣ n)
  let f (q : ℕ) := (vonMangoldt q / (q : ℝ)) * ((log (m : ℝ) - shift + log (q : ℝ)) ^ 2)⁻¹
  have hfilter : ∑ n ∈ S, edge n m = ∑ n ∈ T, edge n m := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnT
    exact ite_eq_right (fun hd ↦ hnT (mem_filter.mpr ⟨hn, hd⟩))
  have hq {n : ℕ} (hn : n ∈ T) : y ≤ n / m := by
    rw [Nat.le_div_iff_mul_le hm, mul_comm]
    exact (hS n (mem_filter.mp hn).1 (mem_filter.mp hn).2).1
  have hsub : T.image (fun n ↦ n / m) ⊆ Icc y (max y N) := by
    intro q hq'
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hq'
    exact mem_Icc.mpr ⟨hq hn, (Nat.div_le_self ..).trans
      ((hS n (mem_filter.mp hn).1 (mem_filter.mp hn).2).2.trans (le_max_right _ _))⟩
  have hinj : Set.InjOn (fun n ↦ n / m) ↑T := by
    intro n hn r hr h
    change n / m = r / m at h
    rw [← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hn)).2,
      ← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hr)).2, h]
  have hfactor (n : ℕ) (hn : n ∈ T) : edge n m = (m : ℝ)⁻¹ * f (n / m) := by
    have hd := (mem_filter.mp hn).2
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hqR : (↑(n / m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hy.trans_le (hq hn)).ne'
    have hcast : (n : ℝ) = (↑(n / m) : ℝ) * m := by exact_mod_cast (Nat.div_mul_cancel hd).symm
    rw [edge, ite_eq_left hd, hcast, Real.log_mul hqR hmR]
    dsimp [f]
    rw [show log (↑(n / m) : ℝ) + log (m : ℝ) - shift =
      log (m : ℝ) - shift + log (↑(n / m) : ℝ) by ring]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hnonneg (q : ℕ) : 0 ≤ f q := by
    exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg q)) (by positivity)
  rw [hfilter, sum_congr rfl hfactor, ← mul_sum, ← sum_image hinj]
  gcongr
  exact (sum_le_sum_of_subset_of_nonneg hsub fun q _ _ ↦ hnonneg q).trans
    (sum_mangoldt_weighted_le hy (le_max_left _ _) hL)

private noncomputable def largeBound (x : ℕ) : ℝ :=
  (1 + log (x : ℝ)) * tailBound (log (x : ℝ) - shift)

private theorem sum_erdosTerm_le {A : Finset ℕ} {x N : ℕ} (hx : 0 < x) (hxN : x ≤ N)
    (hlog : shift < log (x : ℝ)) (hA : A ⊆ Icc x N)
    (hprim : ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) :
    ∑ a ∈ A, erdosTerm a ≤ largeBound x := by
  have hpos : 0 < log (x : ℝ) - shift := sub_pos.mpr hlog
  have hI : Icc x N ⊆ Icc 1 N :=
    fun _ hn ↦ mem_Icc.mpr ⟨hx.trans_le (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩
  have hlog_le {m : ℕ} (hm : x ≤ m) : log (x : ℝ) ≤ log (m : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr hx) (Nat.cast_le.mpr hm)
  have hin (m : ℕ) (hm : m ∈ Icc x N) : ∑ n ∈ Icc x N, edge n m ≤ weight m := by
    have hmpos : 0 < m := hx.trans_le (mem_Icc.mp hm).1
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
    have hmL : 0 < log (m : ℝ) - shift := sub_pos.mpr (hlog.trans_le (hlog_le (mem_Icc.mp hm).1))
    have h := sum_edge_le (S := Icc x N) (y := 1) hmpos Nat.one_pos (by simpa using hmL)
      (fun n hn hd ↦ ⟨by simpa using Nat.le_of_dvd (hx.trans_le (mem_Icc.mp hn).1) hd,
        (mem_Icc.mp hn).2⟩)
    refine h.trans_eq ?_
    rw [Nat.cast_one, log_one, add_zero, tailBound, weight]
    field_simp
    ring
  have hout (n : ℕ) (hn : n ∈ Icc x N) : ∑ m ∈ Icc 1 N, edge n m = weight n :=
    sum_edge_eq_weight (hx.trans_le (mem_Icc.mp hn).1) (mem_Icc.mp hn).2
  have hcut := sum_weight_le_boundary hA hI edge_nonneg (fun _ _ h ↦ ite_eq_right h)
    (fun n ↦ by
      rw [edge, ite_eq_left dvd_rfl]
      by_cases hn : n = 0
      · simp [hn]
      · rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
        simp) hprim hout hin
  have hdiff : Icc 1 N \ Icc x N = Ico 1 x := by
    ext n
    simp only [Finset.mem_sdiff, mem_Icc, mem_Ico]
    omega
  have hboundary (m : ℕ) (hm : m ∈ Ico 1 x) :
      ∑ n ∈ Icc x N, edge n m ≤ (m : ℝ)⁻¹ * tailBound (log (x : ℝ) - shift) := by
    have hmpos : 0 < m := (mem_Ico.mp hm).1
    let y := (x - 1) / m + 1
    have hy : 0 < y := Nat.succ_pos _
    have hxy : x ≤ m * y := by
      have h := (Nat.div_lt_iff_lt_mul hmpos).mp (show (x - 1) / m < y from Nat.lt_succ_self _)
      rw [mul_comm]
      omega
    have hmy (n : ℕ) (hn : n ∈ Icc x N) (hd : m ∣ n) : m * y ≤ n := by
      have hqn : y ≤ n / m := by
        apply Nat.succ_le_of_lt
        apply (Nat.div_lt_iff_lt_mul hmpos).mpr
        rw [Nat.div_mul_cancel hd]
        have := (mem_Icc.mp hn).1
        omega
      have hmul := Nat.mul_le_mul_left m hqn
      rwa [mul_comm m (n / m), Nat.div_mul_cancel hd] at hmul
    have hlogxy : log (x : ℝ) - shift ≤ log (m : ℝ) - shift + log (y : ℝ) := by
      have h := hlog_le hxy
      rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hmpos.ne')
        (Nat.cast_ne_zero.mpr hy.ne')] at h
      linarith
    refine (sum_edge_le (N := N) hmpos hy (hpos.trans_le hlogxy) (fun n hn hd ↦ ?_)).trans ?_
    · exact ⟨hmy n hn hd, (mem_Icc.mp hn).2⟩
    · exact mul_le_mul_of_nonneg_left (tailBound_antitone hpos hlogxy) (by positivity)
  calc
    ∑ a ∈ A, erdosTerm a ≤ ∑ a ∈ A, weight a :=
      sum_le_sum fun a ha ↦ erdosTerm_le_weight (hlog.trans_le (hlog_le (mem_Icc.mp (hA ha)).1))
    _ ≤ ∑ m ∈ Ico 1 x, ∑ n ∈ Icc x N, edge n m := by rwa [hdiff] at hcut
    _ ≤ ∑ m ∈ Ico 1 x, (m : ℝ)⁻¹ * tailBound (log (x : ℝ) - shift) :=
      sum_le_sum hboundary
    _ ≤ largeBound x := by
      rw [← sum_mul, largeBound]
      apply mul_le_mul_of_nonneg_right _ (tailBound_nonneg hpos)
      refine (sum_le_sum_of_subset_of_nonneg Ico_subset_Icc_self
        (fun _ _ _ ↦ by positivity)).trans ?_
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        harmonic_le_one_add_log x

private theorem tendsto_log_nat : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_largeBound_sub_one :
    Tendsto (fun n ↦ largeBound n - 1) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ log (n : ℝ) - shift) atTop atTop := by
    refine tendsto_atTop.mpr fun b ↦ (tendsto_log_nat.eventually_ge_atTop (b + shift)).mono ?_
    intro n hn
    exact le_sub_iff_add_le.mpr hn
  have hinv : Tendsto (fun n : ℕ ↦ (log (n : ℝ) - shift)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hpoly : Tendsto (fun n : ℕ ↦ (2 * shift + 1) * (log (n : ℝ) - shift)⁻¹ +
      (1 + shift) * shift * ((log (n : ℝ) - shift)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (hinv.const_mul (2 * shift + 1)).add ((hinv.pow 2).const_mul ((1 + shift) * shift))
  refine hpoly.congr' ?_
  filter_upwards [hshift.eventually_gt_atTop 0] with n hn
  have hn' : log (n : ℝ) - shift ≠ 0 := (show 0 < log (n : ℝ) - shift from hn).ne'
  unfold largeBound tailBound
  field_simp
  ring

private theorem sum_finite_le {A : Set ℕ} (hprim : IsPrimitive A) {x M : ℕ}
    (hx : A ⊆ Set.Ici x) (hxpos : 0 < x) (hM : 0 < M) (hlog : shift < log (M : ℝ)) (s : Finset A) :
    (∑ a ∈ s, erdosTerm a.val) ≤
      largeBound (max x M) + (if x < M then ∑ n ∈ Ico 1 M, erdosTerm n else 0) := by
  classical
  let t := s.map (⟨Subtype.val, Subtype.val_injective⟩ : A ↪ ℕ)
  let z := max x M
  have ht (n : ℕ) (hn : n ∈ t) : n ∈ A := by
    obtain ⟨a, _, rfl⟩ := mem_map.mp hn
    exact a.property
  have hz : 0 < z := hM.trans_le (le_max_right _ _)
  have hlarge : ∑ a ∈ t.filter (z ≤ ·), erdosTerm a ≤ largeBound z := by
    let N := max z (t.sup id)
    refine sum_erdosTerm_le (N := N) hz (le_max_left _ _) ?_ ?_ ?_
    · exact hlog.trans_le (Real.log_le_log (Nat.cast_pos.mpr hM)
        (Nat.cast_le.mpr (le_max_right _ _)))
    · intro n hn
      obtain ⟨hnt, hnz⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨hnz, (Finset.le_sup (f := id) hnt).trans (le_max_right _ _)⟩
    · intro a ha b hb hab
      exact associated_iff_eq.mp
        (hprim a (ht a (mem_filter.mp ha).1) b (ht b (mem_filter.mp hb).1) hab)
  have hsmall : (∑ a ∈ t.filter (fun n ↦ ¬ z ≤ n), erdosTerm a) ≤
      if x < M then ∑ n ∈ Ico 1 M, erdosTerm n else 0 := by
    by_cases h : x < M
    · rw [ite_eq_left h]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ ↦ erdosTerm_nonneg n)
      intro n hn
      have hn' := (mem_filter.mp hn).2
      dsimp [z] at hn'
      rw [max_eq_right h.le] at hn'
      exact mem_Ico.mpr ⟨hxpos.trans_le (hx (ht n (mem_filter.mp hn).1)), lt_of_not_ge hn'⟩
    · rw [ite_eq_right h]
      apply le_of_eq
      apply sum_eq_zero
      intro n hn
      obtain ⟨hnt, hnz⟩ := mem_filter.mp hn
      exfalso
      exact hnz (max_le (hx (ht n hnt)) ((le_of_not_gt h).trans (hx (ht n hnt))))
  calc
    (∑ a ∈ s, erdosTerm a.val) = ∑ n ∈ t, erdosTerm n :=
      (sum_map s (⟨Subtype.val, Subtype.val_injective⟩ : A ↪ ℕ) erdosTerm).symm
    _ = (∑ n ∈ t.filter (z ≤ ·), erdosTerm n) +
          ∑ n ∈ t.filter (fun n ↦ ¬ z ≤ n), erdosTerm n :=
      (sum_filter_add_sum_filter_not t (z ≤ ·) erdosTerm).symm
    _ ≤ _ := add_le_add hlarge hsmall

public section

/-- **Erdős Problem 1196 on primitive sets.** There is a function $o : \mathbb{N} \to \mathbb{R}$
with $o(x) \to 0$ as $x \to \infty$ such that for every natural number $x > 0$ and every
primitive set $A$ of natural numbers contained in $[x, \infty)$, the series
$\sum_{a \in A} \frac{1}{a \log a}$ is summable and $\sum_{a \in A} \frac{1}{a \log a} < 1 + o(x)$.
Here a set of natural numbers is primitive if no element divides a different element, and the
term for $a = 1$, where $\log a = 0$, is taken to be $0$.

Resolved true: Resolved affirmatively (GPT-5.4 Pro prompted by Price; account [ABLLPSTT26]), per
erdosproblems.com/1196. Source: B. Alexeev, K. Barreto, Y. Li, J. D. Lichtman, L. Price, J. I.
Shah, Q. Tang, T. Tao, Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond,
arXiv:2605.00301 (2026), https://arxiv.org/abs/2605.00301. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1196`.
-/
theorem conjecture_holds : conjecture := by
  obtain ⟨M, hM⟩ := ((tendsto_log_nat.eventually_gt_atTop shift).and
    (eventually_gt_atTop (0 : ℕ))).exists
  let o (x : ℕ) := largeBound (max x M) - 1 +
    (if x < M then ∑ n ∈ Ico 1 M, erdosTerm n else 0) + (x : ℝ)⁻¹
  refine ⟨o, (Asymptotics.isLittleO_one_iff ℝ).mpr ?_, fun x hx A hA hprim ↦ ?_⟩
  · have hinv : Tendsto (fun x : ℕ ↦ (x : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    refine (show Tendsto (fun x ↦ largeBound x - 1 + (x : ℝ)⁻¹) atTop (𝓝 0) by
      simpa only [add_zero] using tendsto_largeBound_sub_one.add hinv).congr' ?_
    filter_upwards [eventually_ge_atTop M] with x hx
    simp [o, max_eq_left hx, not_lt_of_ge hx]
  · have hnonneg : 0 ≤ fun a : A ↦ erdosTerm a.val := fun a ↦ erdosTerm_nonneg a.val
    have hsum := summable_of_sum_le hnonneg (sum_finite_le hprim hA hx hM.2 hM.1)
    refine ⟨hsum, (hsum.tsum_le_of_sum_le (sum_finite_le hprim hA hx hM.2 hM.1)).trans_lt ?_⟩
    have hinv : 0 < (x : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hx)
    dsimp [o]
    linarith

end

end MathlibExt.NumberTheory.ErdosProblem1196Wanted
