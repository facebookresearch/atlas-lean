/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import MathlibExt.NumberTheory.PrimeNumberTheorem

namespace MetaMathlibExt

/-- The `n`th prime tends to infinity. -/
private lemma ppr_tendsto_nth_prime_atTop :
    Filter.Tendsto (Nat.nth Nat.Prime) Filter.atTop Filter.atTop :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- The cast `n`th prime tends to infinity in `ℝ`. -/
private lemma ppr_tendsto_nth_prime_cast_atTop :
    Filter.Tendsto (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_iff.mpr ppr_tendsto_nth_prime_atTop

/-- The prime-counting function undoes `Nat.nth Nat.Prime`. -/
private lemma ppr_primeCounting_nth_prime (k : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime k) = k + 1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k

/-- Composing the PNT with the `n`th prime: `k + 1 ~ p k / log (p k)`. -/
private lemma ppr_natCast_add_one_isEquivalent_nth_prime_div_log :
    Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => ((k : ℕ) : ℝ) + 1)
      (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ) /
        Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)) := by
  have hcomp :=
    MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem.comp_tendsto
      ppr_tendsto_nth_prime_atTop
  have hev : ((fun n : ℕ => ((Nat.primeCounting n : ℕ) : ℝ)) ∘ Nat.nth Nat.Prime)
      =ᶠ[Filter.atTop] (fun k : ℕ => ((k : ℕ) : ℝ) + 1) := by
    filter_upwards with k
    change (((Nat.primeCounting (Nat.nth Nat.Prime k) : ℕ)) : ℝ) = _
    rw [ppr_primeCounting_nth_prime k, Nat.cast_add_one]
  have hev2 : ((fun n : ℕ => ((n : ℕ) : ℝ) / Real.log ((n : ℕ) : ℝ)) ∘
      Nat.nth Nat.Prime) =ᶠ[Filter.atTop]
      (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ) /
        Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)) :=
    Filter.Eventually.of_forall fun k => rfl
  exact (hcomp.congr_left hev).congr_right hev2

/-- `log (x / log x) ~ log x` along `atTop` on `ℝ`. -/
private lemma ppr_log_div_log_isEquivalent_log :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℝ => Real.log (x / Real.log x)) Real.log := by
  have ho : (fun x : ℝ => Real.log (Real.log x)) =o[Filter.atTop] Real.log :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hsub := Asymptotics.IsEquivalent.refl.sub_isLittleO ho
  have hev : (Real.log - fun x : ℝ => Real.log (Real.log x)) =ᶠ[Filter.atTop]
      (fun x : ℝ => Real.log (x / Real.log x)) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans one_pos hx)
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    simp only [Pi.sub_apply]
    rw [Real.log_div hx0 hlog]
  exact hsub.congr_left hev

/-- `log (p k) ~ log (k + 1)`. -/
private lemma ppr_log_nth_prime_isEquivalent_log_add_one :
    Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ))
      (fun k : ℕ => Real.log (((k : ℕ) : ℝ) + 1)) := by
  have hg : Filter.Tendsto (fun k : ℕ => ((k : ℕ) : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop
  have hlog1 := ppr_natCast_add_one_isEquivalent_nth_prime_div_log.symm.log hg
  have hcomp := ppr_log_div_log_isEquivalent_log.comp_tendsto
    ppr_tendsto_nth_prime_cast_atTop
  have e1 : ((fun x : ℝ => Real.log (x / Real.log x)) ∘
      (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ))) =ᶠ[Filter.atTop]
      (fun k : ℕ => Real.log (((Nat.nth Nat.Prime k : ℕ) : ℝ) /
        Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ))) :=
    Filter.Eventually.of_forall fun k => rfl
  have e2 : (Real.log ∘ (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ)))
      =ᶠ[Filter.atTop]
      (fun k : ℕ => Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)) :=
    Filter.Eventually.of_forall fun k => rfl
  have hcomp' := (hcomp.congr_left e1).congr_right e2
  exact hcomp'.symm.trans hlog1

/-- Multiplying an equivalence by its own log preserves it. -/
private lemma ppr_isEquivalent_mul_log {α : Type} {l : Filter α} {u v : α → ℝ}
    (h : Asymptotics.IsEquivalent l u v)
    (hv : Filter.Tendsto v l Filter.atTop) :
    Asymptotics.IsEquivalent l (fun i => u i * Real.log (u i))
      (fun i => v i * Real.log (v i)) :=
  h.mul (h.log hv)

/-- The `n`th prime is asymptotic to `n log n`. -/
private lemma ppr_nth_prime_isEquivalent_mul_log :
    Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ))
      (fun k : ℕ => ((k : ℕ) : ℝ) * Real.log ((k : ℕ) : ℝ)) := by
  have hid : ∀ k : ℕ, ((Nat.nth Nat.Prime k : ℕ) : ℝ) =
      (((Nat.nth Nat.Prime k : ℕ) : ℝ) /
        Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)) *
      Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ) := by
    intro k
    have hprime : (Nat.nth Nat.Prime k).Prime := Nat.prime_nth_prime k
    have h2 : 2 ≤ Nat.nth Nat.Prime k := hprime.two_le
    have h1 : (1 : ℝ) < ((Nat.nth Nat.Prime k : ℕ) : ℝ) :=
      Nat.one_lt_cast.mpr (by omega : 1 < Nat.nth Nat.Prime k)
    have hlog : Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos h1)
    exact (div_mul_cancel₀ _ hlog).symm
  have h7a : Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ))
      (fun k : ℕ => (((k : ℕ) : ℝ) + 1) *
        Real.log (((k : ℕ) : ℝ) + 1)) := by
    have hev : ((fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ) /
        Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)) *
        (fun k : ℕ => Real.log ((Nat.nth Nat.Prime k : ℕ) : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ)) := by
      filter_upwards with k
      simp only [Pi.mul_apply]
      exact (hid k).symm
    exact (ppr_natCast_add_one_isEquivalent_nth_prime_div_log.symm.mul
      ppr_log_nth_prime_isEquivalent_log_add_one).congr_left hev
  have hbase : Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => ((k : ℕ) : ℝ) + 1) (fun k : ℕ => ((k : ℕ) : ℝ)) := by
    have hnorm : Filter.Tendsto (norm ∘ (fun k : ℕ => ((k : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
      tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop
    exact Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
  have h7b : Asymptotics.IsEquivalent Filter.atTop
      (fun k : ℕ => (((k : ℕ) : ℝ) + 1) * Real.log (((k : ℕ) : ℝ) + 1))
      (fun k : ℕ => ((k : ℕ) : ℝ) * Real.log ((k : ℕ) : ℝ)) :=
    ppr_isEquivalent_mul_log hbase tendsto_natCast_atTop_atTop
  exact h7a.trans h7b

/-- Transfer: `m' ~ m` with `m → ∞` implies `p (m' ·) ~ p (m ·)`. -/
private lemma ppr_nth_prime_isEquivalent_of_isEquivalent {ι : Type} {l : Filter ι}
    {m m' : ι → ℕ} (hm : Filter.Tendsto m l Filter.atTop)
    (h : Asymptotics.IsEquivalent l (fun i => (((m' i : ℕ)) : ℝ))
      (fun i => (((m i : ℕ)) : ℝ))) :
    Asymptotics.IsEquivalent l
      (fun i => (((Nat.nth Nat.Prime (m' i) : ℕ)) : ℝ))
      (fun i => (((Nat.nth Nat.Prime (m i) : ℕ)) : ℝ)) := by
  have hmR : Filter.Tendsto (fun i => (((m i : ℕ)) : ℝ)) l Filter.atTop :=
    tendsto_natCast_atTop_iff.mpr hm
  have hm'R : Filter.Tendsto (fun i => (((m' i : ℕ)) : ℝ)) l Filter.atTop :=
    h.symm.tendsto_atTop hmR
  have hm' : Filter.Tendsto m' l Filter.atTop :=
    tendsto_natCast_atTop_iff.mp hm'R
  have hc1 := ppr_nth_prime_isEquivalent_mul_log.comp_tendsto hm'
  have hc2 := ppr_nth_prime_isEquivalent_mul_log.comp_tendsto hm
  have hmul := ppr_isEquivalent_mul_log h hmR
  have e1 : ((fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ)) ∘ m')
      =ᶠ[l] (fun i => (((Nat.nth Nat.Prime (m' i) : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun i => rfl
  have e2 : ((fun k : ℕ => ((k : ℕ) : ℝ) * Real.log ((k : ℕ) : ℝ)) ∘ m')
      =ᶠ[l] (fun i => (((m' i : ℕ)) : ℝ) * Real.log (((m' i : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun i => rfl
  have e3 : ((fun k : ℕ => ((Nat.nth Nat.Prime k : ℕ) : ℝ)) ∘ m)
      =ᶠ[l] (fun i => (((Nat.nth Nat.Prime (m i) : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun i => rfl
  have e4 : ((fun k : ℕ => ((k : ℕ) : ℝ) * Real.log ((k : ℕ) : ℝ)) ∘ m)
      =ᶠ[l] (fun i => (((m i : ℕ)) : ℝ) * Real.log (((m i : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun i => rfl
  exact (((hc1.congr_left e1).congr_right e2).trans hmul).trans
    ((hc2.congr_left e3).congr_right e4).symm

/-- Consecutive `n`th primes are asymptotically equal. -/
private lemma ppr_nth_prime_succ_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ))
      (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ)) := by
  have hbase : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ((((n + 1 : ℕ))) : ℝ)) (fun n : ℕ => (((n : ℕ)) : ℝ)) := by
    have hnorm : Filter.Tendsto (norm ∘ (fun n : ℕ => (((n : ℕ)) : ℝ)))
        Filter.atTop Filter.atTop :=
      tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop
    have h : Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (((n : ℕ)) : ℝ) + 1) (fun n : ℕ => (((n : ℕ)) : ℝ)) :=
      Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
    have hev : (fun n : ℕ => (((n : ℕ)) : ℝ) + 1) =ᶠ[Filter.atTop]
        (fun n : ℕ => ((((n + 1 : ℕ))) : ℝ)) :=
      Filter.Eventually.of_forall fun n => (Nat.cast_add_one n).symm
    exact h.congr_left hev
  exact ppr_nth_prime_isEquivalent_of_isEquivalent Filter.tendsto_id hbase

/-- The shifted index `Nat.nth Nat.Prime n - 1` tends to infinity. -/
private lemma ppr_tendsto_nth_prime_sub_one_atTop :
    Filter.Tendsto (fun n : ℕ => Nat.nth Nat.Prime n - 1)
      Filter.atTop Filter.atTop :=
  (Filter.tendsto_sub_atTop_nat 1).comp ppr_tendsto_nth_prime_atTop

/-- Cast of the shifted index equals the cast minus one. -/
private lemma ppr_cast_nth_prime_sub_one (n : ℕ) :
    (((Nat.nth Nat.Prime n - 1 : ℕ)) : ℝ) =
      (((Nat.nth Nat.Prime n : ℕ)) : ℝ) - 1 := by
  have h2 := (Nat.prime_nth_prime n).two_le
  have hle : 1 ≤ Nat.nth Nat.Prime n := by omega
  rw [Nat.cast_sub hle, Nat.cast_one]

/-- Consecutive shifted indices are asymptotically equal as reals. -/
private lemma ppr_nth_prime_sub_one_succ_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) - 1 : ℕ)) : ℝ))
      (fun n : ℕ => (((Nat.nth Nat.Prime n - 1 : ℕ)) : ℝ)) := by
  have hnorm : Filter.Tendsto (norm ∘ (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ)))
      Filter.atTop Filter.atTop :=
    tendsto_norm_atTop_atTop.comp ppr_tendsto_nth_prime_cast_atTop
  have hsucc_cast : Filter.Tendsto
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ))
      Filter.atTop Filter.atTop :=
    ppr_tendsto_nth_prime_cast_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hnorm_succ : Filter.Tendsto
      (norm ∘ (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ)))
      Filter.atTop Filter.atTop :=
    tendsto_norm_atTop_atTop.comp hsucc_cast
  have hsub : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ) - 1)
      (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ)) := by
    have hadd : Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ) + (-1))
        (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ)) :=
      Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
    simpa [sub_eq_add_neg] using hadd
  have hsub_succ : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ) - 1)
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ)) := by
    have hadd : Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ) + (-1))
        (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ)) :=
      Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm_succ
    simpa [sub_eq_add_neg] using hadd
  have hev1 : (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) : ℕ)) : ℝ) - 1)
      =ᶠ[Filter.atTop]
      (fun n : ℕ => (((Nat.nth Nat.Prime (n + 1) - 1 : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun n => (ppr_cast_nth_prime_sub_one (n + 1)).symm
  have hev2 : (fun n : ℕ => (((Nat.nth Nat.Prime n : ℕ)) : ℝ) - 1)
      =ᶠ[Filter.atTop]
      (fun n : ℕ => (((Nat.nth Nat.Prime n - 1 : ℕ)) : ℝ)) :=
    Filter.Eventually.of_forall fun n => (ppr_cast_nth_prime_sub_one n).symm
  exact (hsub_succ.congr_left hev1).trans
    (ppr_nth_prime_succ_isEquivalent.trans (hsub.symm.congr_right hev2))

end MetaMathlibExt

@[expose] public section

namespace MetaMathlibExt

/-- **Ratio of consecutive zero-based prime-indexed primes tends to one.** Let
$p_0 = 2$, $p_1 = 3$, $p_2 = 5$, $\dots$ be the primes in increasing order, indexed from zero,
and let $q_n = p_{p_n}$. Then $q_n / q_{n+1} \to 1$ as $n \to \infty$. -/
public theorem primePrimes_ratio_tendsto_one' :
    Filter.Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime n) : ℕ) : ℝ) /
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
  have hequiv := (ppr_nth_prime_isEquivalent_of_isEquivalent
    ppr_tendsto_nth_prime_atTop ppr_nth_prime_succ_isEquivalent).symm
  have hne : ∀ᶠ n : ℕ in Filter.atTop,
      (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ)) : ℝ) ≠ 0 := by
    filter_upwards with n
    have hprime : (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1))).Prime :=
      Nat.prime_nth_prime _
    have hpos : (0 : ℝ) < (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr hprime.pos
    exact ne_of_gt hpos
  have hlim := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hequiv
  have heq : ((fun n : ℕ => (((Nat.nth Nat.Prime (Nat.nth Nat.Prime n) : ℕ)) : ℝ)) /
      (fun n : ℕ => (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ)) : ℝ)))
      = (fun n : ℕ => (((Nat.nth Nat.Prime (Nat.nth Nat.Prime n) : ℕ)) : ℝ) /
        (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ)) : ℝ)) :=
    funext fun n => Pi.div_apply _ _ n
  rw [heq] at hlim
  exact hlim

/--
**Ratio of consecutive prime-indexed primes tends to one.** Let $p_1 = 2$, $p_2 = 3$, $p_3 = 5$,
$\dots$ be the primes in increasing order and let $q_n = p_{p_n}$. Then $q_n / q_{n+1} \to 1$ as
$n \to \infty$.

This is part (c) of the Broughan–Barnett corollary, in the source's one-based indexing.
-/
public theorem primePrimes_oneBased_ratio_tendsto_one :
    Filter.Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime n - 1) : ℕ) : ℝ) /
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1) : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
  have hequiv := (ppr_nth_prime_isEquivalent_of_isEquivalent
    ppr_tendsto_nth_prime_sub_one_atTop
    ppr_nth_prime_sub_one_succ_isEquivalent).symm
  have hne : ∀ᶠ n : ℕ in Filter.atTop,
      (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1) : ℕ)) : ℝ) ≠ 0 := by
    filter_upwards with n
    have hprime : (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1)).Prime :=
      Nat.prime_nth_prime _
    have hpos : (0 : ℝ) <
        (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1) : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr hprime.pos
    exact ne_of_gt hpos
  have hlim := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hequiv
  have heq : ((fun n : ℕ =>
      (((Nat.nth Nat.Prime (Nat.nth Nat.Prime n - 1) : ℕ)) : ℝ)) /
      (fun n : ℕ =>
        (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1) : ℕ)) : ℝ)))
      = (fun n : ℕ => (((Nat.nth Nat.Prime (Nat.nth Nat.Prime n - 1) : ℕ)) : ℝ) /
        (((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1) - 1) : ℕ)) : ℝ)) :=
    funext fun n => Pi.div_apply _ _ n
  rw [heq] at hlim
  exact hlim

/--
**Broughan–Barnett ratio limit, zero-based form.** Assume that there are infinitely many primes
(which always holds). Let $p_0 = 2$, $p_1 = 3$, $p_2 = 5$, $\dots$ be the primes in increasing
order, indexed from zero, and let $q_n = p_{p_n}$. Then $q_n / q_{n+1} \to 1$ as $n \to \infty$.

In the source's one-based indexing $p'_1 = 2$, $p'_2 = 3$, $\dots$, this $q_n$ equals
$p'_{p'_{n+1} + 1}$ rather than the source's prime-indexed prime $p'_{p'_{n+1}}$; the source
states the same limit for its sequence.

Source: Kevin A. Broughan and A. Ross Barnett, "On the Subsequence of Primes
Having Prime Subscripts," Journal of Integer Sequences 12 (2009),
Article 09.2.3, Corollary to the Theorem (label thm:bounds), part (c),
lines 193–199,
https://cs.uwaterloo.ca/journals/JIS/VOL12/Broughan/broughan16.tex
-/
public theorem primePrimes_ratio_tendsto_one
    [Infinite { n : ℕ // n.Prime }] :
    Filter.Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime n) : ℕ) : ℝ) /
      ((Nat.nth Nat.Prime (Nat.nth Nat.Prime (n + 1)) : ℕ) : ℝ))
      Filter.atTop (nhds 1) :=
  primePrimes_ratio_tendsto_one'

end MetaMathlibExt
