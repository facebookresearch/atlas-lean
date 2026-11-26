/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments of a finite aggregation-breakage model

The mass-weighted sum is conserved, and the particle count is nonincreasing under pure
aggregation and nondecreasing under pure breakage. The aggregation gain sums over ordered
pairs, halved even on the diagonal; symmetry rewrites the loss as a sum with the same factor.
In breakage, the mass constraint cancels the weighted gain against the loss, and the constraint
that all daughters are smaller than their parent forces more than one daughter in total.

The model is finite and conditional on a given solution. See S. Kumar and D. Ramkrishna,
*On the solution of population balance equations by discretization—I. A fixed pivot technique*,
Chemical Engineering Science 51 (1996), 1311–1332, Sections 3.2–3.4.
-/

open scoped BigOperators

namespace Chemistry.ParticleBalances

private theorem sum_weighted_aggregation_gain {M : ℕ} (w : ℕ → ℝ) (q : Fin M → Fin M → ℝ)
    (hcut : ∀ i j, M < (i.val + 1) + (j.val + 1) → q i j = 0) :
    (∑ k : Fin M, w (k.val + 1) *
      ((∑ i : Fin M, ∑ j : Fin M,
        if (i.val + 1) + (j.val + 1) = k.val + 1 then q i j else 0) / 2)) =
      (∑ i : Fin M, ∑ j : Fin M, w ((i.val + 1) + (j.val + 1)) * q i j) / 2 := by
  simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul, Finset.mul_sum, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : (i.val + 1) + (j.val + 1) ≤ M
  · let k : Fin M := ⟨i.val + j.val + 1, by omega⟩
    have hk : (i.val + 1) + (j.val + 1) = k.val + 1 := by dsimp [k]; omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro l _ hl
      have hne : k.val + 1 ≠ l.val + 1 := by
        intro he
        exact hl (Fin.ext (by omega))
      rw [hk, ite_eq_right hne]
    · simp
  · simp [hcut i j (by omega)]

private theorem sum_weighted_aggregation_loss {M : ℕ} (w : Fin M → ℝ) (q : Fin M → Fin M → ℝ)
    (hsymm : ∀ i j, q i j = q j i) :
    (∑ k, w k * ∑ j, q k j) = (∑ i, ∑ j, (w i + w j) * q i j) / 2 := by
  have hswap : (∑ i, ∑ j, w j * q i j) = ∑ i, ∑ j, w i * q i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hsymm j i]
  simp_rw [Finset.mul_sum, add_mul, Finset.sum_add_distrib, hswap]
  ring

private theorem sum_weighted_breakage {M : ℕ} (w : Fin M → ℝ) (d : Fin M → Fin M → ℝ)
    (r : Fin M → ℝ) :
    (∑ k, w k * ((∑ i, d k i * r i) - r k)) =
      ∑ i, ((∑ k, w k * d k i) - w i) * r i := by
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, ← mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

private theorem one_lt_sum_daughters {M : ℕ} (i : Fin M) (d : Fin M → ℝ)
    (hnonneg : ∀ j, 0 ≤ d j) (hsupport : ∀ j, i ≤ j → d j = 0)
    (hmass : ∑ j, (↑(j.val + 1 : ℕ) : ℝ) * d j = ↑(i.val + 1 : ℕ)) : 1 < ∑ j, d j := by
  have hbound : (↑(i.val + 1 : ℕ) : ℝ) ≤ (i.val : ℝ) * ∑ j, d j := by
    rw [← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j < i
    · have hle : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hj
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hnonneg j)
    · simp [hsupport j (le_of_not_gt hj)]
  by_contra! h
  have hle := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) i.val)
  push_cast at hbound
  linarith

/-- For bins `k : Fin M` of mass `k.val + 1`, a nonnegative solution of the finite
aggregation-breakage equations conserves total mass on the real time interval `s`.
With all breakage rates zero its total count is antitone on `s`; with the kernel zero
its total count is monotone on `s`.

The solution is continuous on `s`, and the equations specify its derivative within the
interior of `s`. The kernel is symmetric and zero for pairs whose combined mass exceeds `M`.
The daughter coefficient `d j i` is for daughters in bin `j` from a breakage in bin `i`.
Only active parents (`0 < b i`) require nonnegative, mass-preserving daughter coefficients
supported at strictly smaller masses. The full daughter sum in the derivative therefore
agrees with a sum over larger parent bins: all other terms vanish by support or by `b i = 0`.
In particular, the bin of mass one cannot be active. -/
public theorem mass_conservation_and_particle_count_monotonicity
    {M : ℕ} {s : Set ℝ} (hs : Convex ℝ s) (n : Fin M → ℝ → ℝ)
    (K : Fin M → Fin M → ℝ) (b : Fin M → ℝ) (d : Fin M → Fin M → ℝ)
    (hn : ∀ k t, t ∈ s → 0 ≤ n k t) (hcont : ∀ k, ContinuousOn (n k) s)
    (hK_nonneg : ∀ i j, 0 ≤ K i j) (hK_symm : ∀ i j, K i j = K j i)
    (hK_cutoff : ∀ i j, M < (i.val + 1) + (j.val + 1) → K i j = 0)
    (hb : ∀ i, 0 ≤ b i)
    (hd_nonneg : ∀ i, 0 < b i → ∀ j, 0 ≤ d j i)
    (hd_support : ∀ i, 0 < b i → ∀ j, i ≤ j → d j i = 0)
    (hd_mass : ∀ i, 0 < b i → ∑ j, (↑(j.val + 1 : ℕ) : ℝ) * d j i = ↑(i.val + 1 : ℕ))
    (hsolution : ∀ t ∈ interior s, ∀ k, HasDerivWithinAt (n k)
      ((∑ i : Fin M, ∑ j : Fin M,
        if (i.val + 1) + (j.val + 1) = k.val + 1 then K i j * n i t * n j t else 0) / 2 -
        (∑ j, K k j * n k t * n j t) +
        ((∑ i, d k i * (b i * n i t)) - b k * n k t)) (interior s) t) :
    (∀ t ∈ s, ∀ u ∈ s,
      (∑ k, (↑(k.val + 1 : ℕ) : ℝ) * n k t) = ∑ k, (↑(k.val + 1 : ℕ) : ℝ) * n k u) ∧
      ((∀ i, b i = 0) → AntitoneOn (fun t ↦ ∑ k, n k t) s) ∧
      ((∀ i j, K i j = 0) → MonotoneOn (fun t ↦ ∑ k, n k t) s) := by
  let w (k : Fin M) : ℝ := ↑(k.val + 1)
  let q (t : ℝ) (i j : Fin M) := K i j * n i t * n j t
  let r (t : ℝ) (i : Fin M) := b i * n i t
  let gain (t : ℝ) (k : Fin M) :=
    (∑ i : Fin M, ∑ j : Fin M,
      if (i.val + 1) + (j.val + 1) = k.val + 1 then q t i j else 0) / 2
  let loss (t : ℝ) (k : Fin M) := ∑ j, q t k j
  let breakage (t : ℝ) (k : Fin M) := (∑ i, d k i * r t i) - r t k
  let rate (t : ℝ) (k : Fin M) := gain t k - loss t k + breakage t k
  have hmoment (a : Fin M → ℝ) (t : ℝ) (ht : t ∈ interior s) :
      HasDerivWithinAt (fun u ↦ ∑ k, a k * n k u) (∑ k, a k * rate t k) (interior s) t :=
    HasDerivWithinAt.fun_sum fun k _ ↦ (hsolution t ht k).const_mul (a k)
  have hsplit (a : Fin M → ℝ) (t : ℝ) :
      (∑ k, a k * rate t k) =
        (∑ k, a k * gain t k) - (∑ k, a k * loss t k) + (∑ k, a k * breakage t k) := by
    simp_rw [rate, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hq_cutoff (t : ℝ) (i j : Fin M) (hij : M < (i.val + 1) + (j.val + 1)) :
      q t i j = 0 := by simp [q, hK_cutoff i j hij]
  have hq_symm (t : ℝ) (i j : Fin M) : q t i j = q t j i := by
    dsimp [q]
    rw [hK_symm i j]
    ring
  have hmass_rate (t : ℝ) : ∑ k, w k * rate t k = 0 := by
    have hgain : (∑ k, w k * gain t k) =
        (∑ i, ∑ j, (w i + w j) * q t i j) / 2 := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, w, gain] using
        sum_weighted_aggregation_gain (fun m ↦ (m : ℝ)) (q t) (hq_cutoff t)
    have hloss : (∑ k, w k * loss t k) =
        (∑ i, ∑ j, (w i + w j) * q t i j) / 2 :=
      sum_weighted_aggregation_loss w (q t) (hq_symm t)
    have hbreak : ∑ k, w k * breakage t k = 0 := by
      change (∑ k, w k * ((∑ i, d k i * r t i) - r t k)) = 0
      rw [sum_weighted_breakage]
      apply Finset.sum_eq_zero
      intro i _
      rcases (hb i).eq_or_lt with hi | hi
      · simp [r, ← hi]
      · have hd : (∑ k, w k * d k i) = w i := hd_mass i hi
        rw [hd, sub_self, zero_mul]
    rw [hsplit, hgain, hloss, hbreak, sub_self, add_zero]
  have hmass_deriv (t : ℝ) (ht : t ∈ interior s) :
      HasDerivWithinAt (fun u ↦ ∑ k, w k * n k u) 0 (interior s) t :=
    hmass_rate t ▸ hmoment w t ht
  have hmass_cont : ContinuousOn (fun t ↦ ∑ k, w k * n k t) s :=
    continuousOn_finsetSum _ fun k _ ↦ continuousOn_const.mul (hcont k)
  have hcount_cont : ContinuousOn (fun t ↦ ∑ k, n k t) s :=
    continuousOn_finsetSum _ fun k _ ↦ hcont k
  have hcount_deriv (t : ℝ) (ht : t ∈ interior s) :
      HasDerivWithinAt (fun u ↦ ∑ k, n k u) (∑ k, rate t k) (interior s) t :=
    HasDerivWithinAt.fun_sum fun k _ ↦ hsolution t ht k
  refine ⟨?_, ?_, ?_⟩
  · have hm := monotoneOn_of_hasDerivWithinAt_nonneg hs hmass_cont hmass_deriv fun _ _ ↦ le_rfl
    have ha := antitoneOn_of_hasDerivWithinAt_nonpos hs hmass_cont hmass_deriv fun _ _ ↦ le_rfl
    intro t ht u hu
    rcases le_total t u with htu | hut
    · exact le_antisymm (hm ht hu htu) (ha ht hu htu)
    · exact le_antisymm (ha hu ht hut) (hm hu ht hut)
  · intro hb_zero
    refine antitoneOn_of_hasDerivWithinAt_nonpos hs hcount_cont hcount_deriv fun t ht ↦ ?_
    have hsplit' := hsplit (fun _ ↦ 1) t
    simp only [one_mul] at hsplit'
    have hgain : (∑ k, gain t k) = (∑ i, ∑ j, q t i j) / 2 := by
      simpa only [gain, one_mul] using
        sum_weighted_aggregation_gain (fun _ ↦ 1) (q t) (hq_cutoff t)
    have hbreak : ∑ k, breakage t k = 0 := by simp [breakage, r, hb_zero]
    rw [hsplit', hgain, hbreak, add_zero]
    have hq_nonneg : 0 ≤ ∑ i, ∑ j, q t i j :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
        mul_nonneg (mul_nonneg (hK_nonneg i j) (hn i t (interior_subset ht)))
          (hn j t (interior_subset ht))
    change (∑ i, ∑ j, q t i j) / 2 - (∑ i, ∑ j, q t i j) ≤ 0
    linarith
  · intro hK_zero
    refine monotoneOn_of_hasDerivWithinAt_nonneg hs hcount_cont hcount_deriv fun t ht ↦ ?_
    have hsplit' := hsplit (fun _ ↦ 1) t
    simp only [one_mul] at hsplit'
    rw [hsplit']
    have hgain : ∑ k, gain t k = 0 := by simp [gain, q, hK_zero]
    have hloss : ∑ k, loss t k = 0 := by simp [loss, q, hK_zero]
    rw [hgain, hloss, sub_self, zero_add]
    have hbreak := sum_weighted_breakage (fun _ ↦ 1) d (r t)
    simp only [one_mul] at hbreak
    change 0 ≤ ∑ k, ((∑ i, d k i * r t i) - r t k)
    rw [hbreak]
    apply Finset.sum_nonneg
    intro i _
    rcases (hb i).eq_or_lt with hi | hi
    · simp [r, ← hi]
    · have hd := one_lt_sum_daughters i (fun j ↦ d j i)
        (hd_nonneg i hi) (hd_support i hi) (hd_mass i hi)
      exact mul_nonneg (sub_nonneg.mpr hd.le) (mul_nonneg hi.le (hn i t (interior_subset ht)))

end Chemistry.ParticleBalances
