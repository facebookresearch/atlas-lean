/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.AkraBazzi.AkraBazzi
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The standard master theorem

The three polynomial-toll cases of the master theorem follow from the existing
Akra–Bazzi theorem. The coefficient is allowed to be any positive real number,
including one smaller than one. `ofFloor` and `ofCeil` construct the required
one-branch recurrence, including the rounding-error and shrink obligations.

The toll is a real function, nonnegative on nonnegative inputs, and is Theta of
a real power at infinity. No continuity, monotonicity, or one-step regularity of
the toll is assumed. The cost has a strictly positive finite base prefix.

In the ceiling version the cutoff must be at least `b / (b - 1)`; a cutoff of
one is sufficient for floor rounding. The comparison is on all natural inputs,
not just powers of the division factor.

The proof uses the actual Akra–Bazzi sum with summand `g u / u ^ (p + 1)`.
Its initial `1` and finite prefix are retained, and identities requiring
positive bases are applied only to positive indices.
-/

public section

open Filter Asymptotics Finset Real
open scoped Topology

namespace AkraBazziRecurrence

/-! ## Nonnegative partial sums and their finite prefixes -/

private lemma isBigO_of_nonneg_le {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : f =O[atTop] g := by
  apply IsBigO.of_bound'
  filter_upwards [hf, hg, h] with n hfn hgn hn
  simpa only [Real.norm_of_nonneg hfn, Real.norm_of_nonneg hgn] using hn

private lemma isBigO_one_add_sum_Ico {f g : ℕ → ℝ} (k : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (h : f =O[atTop] g) :
    (fun n => 1 + ∑ i ∈ Ico k n, f i) =O[atTop]
      (fun n => 1 + ∑ i ∈ Ico k n, g i) := by
  obtain ⟨C, hC, hfg⟩ := h.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfg.bound
  let M := max k N
  let A := 1 + ∑ i ∈ Ico k M, f i
  have hA : 0 ≤ A := add_nonneg zero_le_one (sum_nonneg fun i _ => hf i)
  refine IsBigO.of_bound (A + C) ?_
  filter_upwards [eventually_ge_atTop M] with n hn
  have hs : 0 ≤ ∑ i ∈ Ico k n, g i := sum_nonneg fun i _ => hg i
  have htail : (∑ i ∈ Ico M n, f i) ≤ C * ∑ i ∈ Ico M n, g i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiN : N ≤ i := (le_max_right k N).trans (mem_Ico.1 hi).1
    simpa only [Real.norm_of_nonneg (hf i), Real.norm_of_nonneg (hg i)] using hN i hiN
  have hsub : (∑ i ∈ Ico M n, g i) ≤ ∑ i ∈ Ico k n, g i := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact Ico_subset_Ico (le_max_left k N) le_rfl
    · intro i _ _; exact hg i
  have hsplit := sum_Ico_consecutive f (le_max_left k N) hn
  have hbound : 1 + ∑ i ∈ Ico k n, f i ≤ A + C * ∑ i ∈ Ico k n, g i := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hsub hC.le]
  rw [Real.norm_of_nonneg (add_nonneg zero_le_one (sum_nonneg fun i _ => hf i)),
    Real.norm_of_nonneg (add_nonneg zero_le_one (sum_nonneg fun i _ => hg i))]
  nlinarith [mul_nonneg hA hs]

private lemma isTheta_one_add_sum_Ico {f g : ℕ → ℝ} (k : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (h : f =Θ[atTop] g) :
    (fun n => 1 + ∑ i ∈ Ico k n, f i) =Θ[atTop]
      (fun n => 1 + ∑ i ∈ Ico k n, g i) :=
  ⟨isBigO_one_add_sum_Ico k hf hg h.1, isBigO_one_add_sum_Ico k hg hf h.2⟩

private lemma isTheta_one_add_sum_range_Ico {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    (fun n => 1 + ∑ i ∈ range n, f i) =Θ[atTop]
      (fun n => 1 + ∑ i ∈ Ico 1 n, f i) := by
  constructor
  · refine IsBigO.of_bound (1 + f 0) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hs : 0 ≤ ∑ i ∈ Ico 1 n, f i := sum_nonneg fun i _ => hf i
    rw [Real.norm_of_nonneg (add_nonneg zero_le_one (sum_nonneg fun i _ => hf i)),
      Real.norm_of_nonneg (add_nonneg zero_le_one hs), sum_range_eq_add_Ico f hn]
    nlinarith [mul_nonneg (hf 0) hs]
  · apply isBigO_of_nonneg_le
      (Eventually.of_forall fun n => add_nonneg zero_le_one (sum_nonneg fun i _ => hf i))
      (Eventually.of_forall fun n => add_nonneg zero_le_one (sum_nonneg fun i _ => hf i))
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [sum_range_eq_add_Ico f hn]
    linarith [hf 0]

private lemma isTheta_nat_rpow_succ (q : ℝ) :
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ q) =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ q) := by
  have h : (fun n : ℕ => (n : ℝ) + 1) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
    simpa only [Pi.add_def, id_eq] using
      ((isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop.right_isTheta_add').symm
  simpa only [Nat.cast_add, Nat.cast_one] using
    Asymptotics.IsTheta.rpow (r := q)
      (Eventually.of_forall fun n => by positivity)
      (Eventually.of_forall fun n => Nat.cast_nonneg n) h

/-! ## The three regimes of the power sum -/

private lemma isTheta_power_sum_of_lt {q : ℝ} (hq : q < -1) :
    (fun n : ℕ => 1 + ∑ i ∈ range n, (i : ℝ) ^ q) =Θ[atTop] (fun _ => (1 : ℝ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ q) := Real.summable_nat_rpow.2 hq
  have ht : Tendsto (fun n : ℕ => 1 + ∑ i ∈ range n, (i : ℝ) ^ q)
      atTop (𝓝 (1 + ∑' i : ℕ, (i : ℝ) ^ q)) :=
    tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
  have hp : 0 < 1 + ∑' i : ℕ, (i : ℝ) ^ q :=
    add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg fun n => rpow_nonneg (Nat.cast_nonneg n) q)
  exact (isTheta_of_div_tendsto_nhds_ne_zero (by simpa only [div_one] using ht) hp.ne').symm

private lemma isTheta_power_sum_neg_one :
    (fun n : ℕ => 1 + ∑ i ∈ range n, (i : ℝ) ^ (-1 : ℝ)) =Θ[atTop]
      (fun n : ℕ => log n) := by
  have hshift := isTheta_one_add_sum_Ico 0
    (fun n => rpow_nonneg (Nat.cast_nonneg n) (-1))
    (fun n => rpow_nonneg (Nat.cast_nonneg (n + 1)) (-1))
    (isTheta_nat_rpow_succ (-1)).symm
  simp only [Nat.Ico_zero_eq_range, rpow_neg_one] at hshift
  have hhar : (fun n : ℕ => 1 + (harmonic n : ℝ)) =Θ[atTop] (fun n : ℕ => log n) := by
    have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ log n :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    constructor
    · refine IsBigO.of_bound 3 ?_
      filter_upwards [hlog] with n hn
      have hh := harmonic_le_one_add_log n
      have hh0 : 0 ≤ (harmonic n : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        positivity
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)]
      linarith
    · apply isBigO_of_nonneg_le
        (hlog.mono fun n hn => le_trans zero_le_one hn)
        (Eventually.of_forall fun n => by
          simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          positivity)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hl : log (n : ℝ) ≤ log (n + 1 : ℕ) := by
        apply Real.log_le_log hnpos
        exact_mod_cast Nat.le_succ n
      linarith [log_add_one_le_harmonic n]
  have hhar' : (fun n : ℕ => 1 + ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹) =Θ[atTop]
      (fun n : ℕ => log n) := by
    simpa only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using hhar
  simpa only [rpow_neg_one] using hshift.trans hhar'

private lemma isTheta_power_sum_of_gt {q : ℝ} (hq : -1 < q) :
    (fun n : ℕ => 1 + ∑ i ∈ range n, (i : ℝ) ^ q) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (q + 1)) := by
  have hs : 0 < q + 1 := by linarith
  have hshift := isTheta_one_add_sum_Ico 1
    (fun n => rpow_nonneg (Nat.cast_nonneg n) q)
    (fun n => rpow_nonneg (Nat.cast_nonneg (n + 1)) q)
    (isTheta_nat_rpow_succ q).symm
  have hJnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 + ∫ x in (1 : ℝ)..n, x ^ q := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [integral_rpow (Or.inl hq), one_rpow]
    have hp : 1 ≤ (n : ℝ) ^ (q + 1) := one_le_rpow (by exact_mod_cast hn) hs.le
    positivity
  have hFnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 + ∑ i ∈ Ico 1 n, (i : ℝ) ^ q :=
    Eventually.of_forall fun n => by positivity
  have hGnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 + ∑ i ∈ Ico 1 n, ((i + 1 : ℕ) : ℝ) ^ q :=
    Eventually.of_forall fun n => by positivity
  have hcompare : (fun n : ℕ => 1 + ∑ i ∈ Ico 1 n, (i : ℝ) ^ q) =Θ[atTop]
      (fun n : ℕ => 1 + ∫ x in (1 : ℝ)..n, x ^ q) := by
    rcases le_total 0 q with hq0 | hq0
    · have hmono (n : ℕ) : MonotoneOn (fun x : ℝ => x ^ q) (Set.Icc (↑(1 : ℕ) : ℝ) n) := by
        intro x hx y _ hxy
        simp only [Nat.cast_one] at hx
        exact rpow_le_rpow (by linarith [hx.1]) hxy hq0
      have hFJ : ∀ᶠ n : ℕ in atTop,
          1 + ∑ i ∈ Ico 1 n, (i : ℝ) ^ q ≤ 1 + ∫ x in (1 : ℝ)..n, x ^ q := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa only [Nat.cast_one, add_comm] using add_le_add_left ((hmono n).sum_le_integral_Ico hn) 1
      have hJG : ∀ᶠ n : ℕ in atTop,
          1 + ∫ x in (1 : ℝ)..n, x ^ q ≤ 1 + ∑ i ∈ Ico 1 n, ((i + 1 : ℕ) : ℝ) ^ q := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa only [Nat.cast_one, add_comm] using add_le_add_left ((hmono n).integral_le_sum_Ico hn) 1
      exact ⟨isBigO_of_nonneg_le hFnonneg hJnonneg hFJ,
        (isBigO_of_nonneg_le hJnonneg hGnonneg hJG).trans hshift.2⟩
    · have hanti (n : ℕ) : AntitoneOn (fun x : ℝ => x ^ q) (Set.Icc (↑(1 : ℕ) : ℝ) n) := by
        intro x hx y _ hxy
        simp only [Nat.cast_one] at hx
        exact rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy hq0
      have hGJ : ∀ᶠ n : ℕ in atTop,
          1 + ∑ i ∈ Ico 1 n, ((i + 1 : ℕ) : ℝ) ^ q ≤ 1 + ∫ x in (1 : ℝ)..n, x ^ q := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa only [Nat.cast_one, add_comm] using add_le_add_left ((hanti n).sum_le_integral_Ico hn) 1
      have hJF : ∀ᶠ n : ℕ in atTop,
          1 + ∫ x in (1 : ℝ)..n, x ^ q ≤ 1 + ∑ i ∈ Ico 1 n, (i : ℝ) ^ q := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa only [Nat.cast_one, add_comm] using add_le_add_left ((hanti n).integral_le_sum_Ico hn) 1
      exact ⟨hshift.1.trans (isBigO_of_nonneg_le hGnonneg hJnonneg hGJ),
        isBigO_of_nonneg_le hJnonneg hFnonneg hJF⟩
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (q + 1)) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have hconst : (fun _ : ℕ => 1 - (q + 1)⁻¹) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (q + 1)) := by
    apply isLittleO_const_left.2
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)] using hpow
  have hmain : (fun n : ℕ => (q + 1)⁻¹ * (n : ℝ) ^ (q + 1)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (q + 1)) := isTheta_rfl.const_mul_left (inv_ne_zero hs.ne')
  have hJ : (fun n : ℕ => 1 + ∫ x in (1 : ℝ)..n, x ^ q) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (q + 1)) := by
    convert hmain.add_isLittleO hconst using 1
    ext n
    rw [integral_rpow (Or.inl hq), one_rpow]
    simp only [Pi.add_apply]
    ring
  exact (isTheta_one_add_sum_range_Ico
    (fun n => rpow_nonneg (Nat.cast_nonneg n) q)).trans (hcompare.trans hJ)

private lemma isTheta_normalized_toll {g : ℝ → ℝ} {c : ℝ} (p : ℝ)
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) :
    (fun n : ℕ => g n / (n : ℝ) ^ (p + 1)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (c - p - 1)) := by
  have hn : (fun n : ℕ => g n) =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ c) :=
    ⟨hg.1.natCast_atTop, hg.2.natCast_atTop⟩
  refine (hn.div (isTheta_refl (fun n : ℕ => (n : ℝ) ^ (p + 1)) atTop)).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← rpow_sub hn']
  congr 1
  ring

section GeneralRecurrence

variable {α : Type*} [Fintype α] [Nonempty α]
variable {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

private lemma isTheta_asympBound_power_sum (R : AkraBazziRecurrence T g a b r) {c : ℝ}
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) :
    asympBound g a b =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ p a b * (1 + ∑ i ∈ range n, (i : ℝ) ^ (c - p a b - 1))) := by
  have hs := isTheta_one_add_sum_Ico 0
    (fun n => div_nonneg (R.g_nonneg n (Nat.cast_nonneg n)) (rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => rpow_nonneg (Nat.cast_nonneg n) _)
    (isTheta_normalized_toll (p a b) hg)
  change (fun n => asympBound g a b n) =Θ[atTop] _
  simpa only [asympBound_def', Nat.Ico_zero_eq_range] using
    (isTheta_refl (fun n : ℕ => (n : ℝ) ^ p a b) atTop).mul hs

private lemma isTheta_rpow_of_exponent_lt (R : AkraBazziRecurrence T g a b r) {c : ℝ}
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) (hc : c < p a b) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p a b) := by
  have hq : c - p a b - 1 < -1 := by linarith
  have h := (isTheta_refl (fun n : ℕ => (n : ℝ) ^ p a b) atTop).mul
    (isTheta_power_sum_of_lt hq)
  simpa only [mul_one] using R.isTheta_asympBound.trans ((isTheta_asympBound_power_sum R hg).trans h)

private lemma isTheta_rpow_mul_log_of_exponent_eq (R : AkraBazziRecurrence T g a b r) {c : ℝ}
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) (hc : c = p a b) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ c * log n) := by
  have hq : c - p a b - 1 = -1 := by rw [hc]; ring
  have h := isTheta_asympBound_power_sum R hg
  rw [hq] at h
  simpa only [hc] using R.isTheta_asympBound.trans
    (h.trans ((isTheta_refl (fun n : ℕ => (n : ℝ) ^ p a b) atTop).mul isTheta_power_sum_neg_one))

private lemma isTheta_rpow_of_exponent_gt (R : AkraBazziRecurrence T g a b r) {c : ℝ}
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) (hc : p a b < c) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ c) := by
  have hq : -1 < c - p a b - 1 := by linarith
  refine (R.isTheta_asympBound.trans ((isTheta_asympBound_power_sum R hg).trans
    ((isTheta_refl (fun n : ℕ => (n : ℝ) ^ p a b) atTop).mul
      (isTheta_power_sum_of_gt hq)))).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [← rpow_add (by exact_mod_cast hn : 0 < (n : ℝ))]
  congr 1
  ring

end GeneralRecurrence

/-! ## Singleton exponent and the three standard cases -/

section Singleton

variable {T : ℕ → ℝ} {g : ℝ → ℝ} {a b c : ℝ} {r : ℕ → ℕ}

private lemma p_singleton (R : AkraBazziRecurrence T g
    (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ => r)) (hb : 1 < b) :
    p (fun _ : Unit => a) (fun _ => b⁻¹) = logb b a := by
  apply R.injective_sumCoeffsExp
  dsimp only
  rw [R.sumCoeffsExp_p_eq_one]
  simp only [Fintype.sum_unique]
  rw [inv_rpow (by linarith : 0 ≤ b), rpow_logb (by linarith) (ne_of_gt hb) (R.a_pos ())]
  exact (mul_inv_cancel₀ (ne_of_gt (R.a_pos ()))).symm

/-- **Master theorem, recursive-dominant case.** A polynomial toll of exponent
`c < logb b a` gives the two-sided order `n ^ logb b a`. -/
theorem master_lt (R : AkraBazziRecurrence T g
    (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ => r))
    (hb : 1 < b) (_hc : 0 ≤ c) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c))
    (h : c < logb b a) : T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a) := by
  have hp := p_singleton R hb
  simpa only [hp] using isTheta_rpow_of_exponent_lt R hg (by rwa [hp])

/-- **Master theorem, critical case.** Equality of the toll and branching
exponents contributes a logarithmic factor, including when both exponents are zero. -/
theorem master_eq (R : AkraBazziRecurrence T g
    (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ => r))
    (hb : 1 < b) (_hc : 0 ≤ c) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c))
    (h : c = logb b a) : T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ c * log n) := by
  exact isTheta_rpow_mul_log_of_exponent_eq R hg (h.trans (p_singleton R hb).symm)

/-- **Master theorem, toll-dominant case.** A polynomial toll of exponent
`logb b a < c` gives the two-sided order `n ^ c`; no one-step toll regularity is needed. -/
theorem master_gt (R : AkraBazziRecurrence T g
    (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ => r))
    (hb : 1 < b) (_hc : 0 ≤ c) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c))
    (h : logb b a < c) : T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ c) := by
  exact isTheta_rpow_of_exponent_gt R hg (by rwa [p_singleton R hb])

end Singleton

/-! ## Floor and ceiling adapters -/

private lemma bounded_rounding_error {e : ℕ → ℝ} (he : ∀ n, |e n| ≤ 1) :
    e =o[atTop] (fun n : ℕ => (n : ℝ) / (log n) ^ 2) := by
  have hlog : (fun n : ℕ => (log n) ^ 2 * (1 : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    simpa only [rpow_two, rpow_one, mul_one] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).natCast_atTop
  have hne : ∀ᶠ n : ℕ in atTop, (log n) ^ 2 ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact pow_ne_zero _ (ne_of_gt (log_pos (by exact_mod_cast hn)))
  have hsmall := (isLittleO_mul_iff_isLittleO_div hne).1 hlog
  apply (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)).trans_isLittleO hsmall
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using he n

/-- Construct a one-branch Akra–Bazzi recurrence with natural floor division.
The positive cutoff suffices for strict shrink; all rounding and growth
obligations are discharged from the polynomial toll hypothesis. -/
noncomputable def ofFloor {T : ℕ → ℝ} {g : ℝ → ℝ} {a b c : ℝ} (n₀ : ℕ)
    (ha : 0 < a) (hb : 1 < b) (hn₀ : 0 < n₀)
    (hg0 : ∀ x ≥ 0, 0 ≤ g x) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c))
    (hbase : ∀ n < n₀, 0 < T n)
    (hrec : ∀ n, n₀ ≤ n → T n = a * T ⌊(n : ℝ) / b⌋₊ + g n) :
    AkraBazziRecurrence T g (fun _ : Unit => a) (fun _ => b⁻¹)
      (fun _ n => ⌊(n : ℝ) / b⌋₊) where
  n₀ := n₀
  n₀_gt_zero := hn₀
  a_pos _ := ha
  b_pos _ := inv_pos.2 (by linarith)
  b_lt_one _ := (inv_lt_one₀ (by linarith)).2 hb
  g_nonneg := hg0
  g_grows_poly := (growsPolynomially_rpow c).of_isTheta hg
    ((eventually_ge_atTop 0).mono fun x hx => hg0 x hx)
  h_rec n hn := by simpa only [Fintype.sum_unique] using hrec n hn
  T_gt_zero' := hbase
  r_lt_n _ n hn := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn₀.trans_le hn
    apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg n) (by linarith))).2
    exact (div_lt_self hnpos hb)
  dist_r_b _ := by
    apply bounded_rounding_error
    intro n
    simpa only [div_eq_mul_inv, mul_comm] using
      Nat.abs_floor_sub_le (div_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ b))

/-- Construct a one-branch Akra–Bazzi recurrence with natural ceiling division.
The cutoff `b / (b - 1) ≤ n₀` is the sharp uniform shrink threshold, also for
`1 < b < 2`. The coefficient `a` need not be at least one. -/
noncomputable def ofCeil {T : ℕ → ℝ} {g : ℝ → ℝ} {a b c : ℝ} (n₀ : ℕ)
    (ha : 0 < a) (hb : 1 < b) (hn₀ : 0 < n₀) (hcut : b / (b - 1) ≤ (n₀ : ℝ))
    (hg0 : ∀ x ≥ 0, 0 ≤ g x) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c))
    (hbase : ∀ n < n₀, 0 < T n)
    (hrec : ∀ n, n₀ ≤ n → T n = a * T ⌈(n : ℝ) / b⌉₊ + g n) :
    AkraBazziRecurrence T g (fun _ : Unit => a) (fun _ => b⁻¹)
      (fun _ n => ⌈(n : ℝ) / b⌉₊) where
  n₀ := n₀
  n₀_gt_zero := hn₀
  a_pos _ := ha
  b_pos _ := inv_pos.2 (by linarith)
  b_lt_one _ := (inv_lt_one₀ (by linarith)).2 hb
  g_nonneg := hg0
  g_grows_poly := (growsPolynomially_rpow c).of_isTheta hg
    ((eventually_ge_atTop 0).mono fun x hx => hg0 x hx)
  h_rec n hn := by simpa only [Fintype.sum_unique] using hrec n hn
  T_gt_zero' := hbase
  r_lt_n _ n hn := by
    have hnpos : 0 < n := hn₀.trans_le hn
    have hbn : b ≤ (n : ℝ) * (b - 1) :=
      (div_le_iff₀ (by linarith : 0 < b - 1)).1 (hcut.trans (by exact_mod_cast hn))
    have hchild : ⌈(n : ℝ) / b⌉₊ ≤ n - 1 := by
      rw [Nat.ceil_le, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hnpos.ne'), Nat.cast_one]
      apply (div_le_iff₀ (by linarith : 0 < b)).2
      nlinarith
    exact hchild.trans_lt (Nat.sub_lt hnpos (by decide))
  dist_r_b _ := by
    apply bounded_rounding_error
    intro n
    simpa only [div_eq_mul_inv, mul_comm] using
      Nat.abs_ceil_sub_le (div_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ b))

end AkraBazziRecurrence
