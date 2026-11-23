/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Hedge
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Hedge: the Hoeffding regret bound

For losses in `[0, 1]`, Hedge (`CSLibExt.MachineLearning.Hedge`) started from unit weights with
learning rate `η > 0` pays at most `L_i + log n / η + η T / 8` over `T` rounds, against every
expert `i`. For such losses this sharpens `algLoss_le_sq`, whose second-order term can be as
large as `η T`. The one-step bound is Hoeffding's lemma for the round's weighted average loss.

Main results:

* `total_update_le_hoeffding`: a round multiplies the total weight by at most
  `exp (-η roundLoss + η² / 8)`.
* `total_weights_le_hoeffding`: over `T` rounds, by at most `exp (-η L + T η² / 8)`.
* `algLoss_le_hoeffding`: **the regret bound** `L ≤ L_i + log n / η + η T / 8`.

## References

* N. Cesa-Bianchi and G. Lugosi, *Prediction, Learning, and Games*, Cambridge University Press,
  2006, Chapter 2.
* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Amer. Statist.
  Assoc. 58, 1963.
-/

@[expose] public section

namespace Cslib.MachineLearning.Hedge

open Finset Real

variable {n : ℕ}

/-- The `1 + μ * (exp s - 1)` expression in Hoeffding's core inequality. -/
private noncomputable def hD (μ : ℝ) (s : ℝ) : ℝ := 1 + μ * (Real.exp s - 1)

/-- Gap function: `s ^ 2 / 8 - (log (hD μ s) - s * μ)`. -/
private noncomputable def hpsi (μ : ℝ) (s : ℝ) : ℝ :=
  s ^ 2 / 8 - (Real.log (hD μ s) - s * μ)

private lemma hD_pos (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    0 < hD μ s := by
  have he : (0 : ℝ) < Real.exp s := Real.exp_pos s
  by_cases hμ0 : μ = 0
  · subst hμ0; simp [hD]
  · have hμpos : (0 : ℝ) < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
    have h2 : (0 : ℝ) < μ * Real.exp s := mul_pos hμpos he
    have h3 : (0 : ℝ) ≤ 1 - μ := by linarith [hμ.2]
    have h4 : hD μ s = (1 - μ) + μ * Real.exp s := by simp only [hD]; ring
    rw [h4]; linarith

private lemma hD_deriv (μ : ℝ) (s : ℝ) :
    HasDerivAt (hD μ) (μ * Real.exp s) s := by
  change HasDerivAt (fun s => 1 + μ * (Real.exp s - 1)) (μ * Real.exp s) s
  exact (((Real.hasDerivAt_exp s).sub_const 1).const_mul μ).const_add 1

private lemma hpsi_deriv1 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    HasDerivAt (hpsi μ) (s / 4 - (μ * Real.exp s / hD μ s - μ)) s := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 8) (s / 4) s := by
    have h2 := (hasDerivAt_pow 2 s).div_const 8
    have hval : (Nat.cast 2 * s ^ (2 - 1)) / 8 = s / 4 := by
      have e1 : ((2 : ℕ) - 1) = 1 := rfl
      rw [e1, pow_one]
      ring
    rw [hval] at h2
    exact h2
  have hlog : HasDerivAt (fun s : ℝ => Real.log (hD μ s))
      (μ * Real.exp s / hD μ s) s :=
    (hD_deriv μ s).log (ne_of_gt (hD_pos μ hμ s))
  have hlin : HasDerivAt (fun s : ℝ => s * μ) μ s := by
    simpa using (hasDerivAt_id s).mul_const μ
  change HasDerivAt (fun s => s ^ 2 / 8 - (Real.log (hD μ s) - s * μ)) _ s
  exact hsq.fun_sub (hlog.fun_sub hlin)

private lemma hpsi_deriv2 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    HasDerivAt (deriv (hpsi μ))
      (1 / 4 - μ * (1 - μ) * Real.exp s / (hD μ s) ^ 2) s := by
  have heq : deriv (hpsi μ) =
      fun s => s / 4 - (μ * Real.exp s / hD μ s - μ) :=
    funext (fun s => (hpsi_deriv1 μ hμ s).deriv)
  rw [heq]
  have hDne : hD μ s ≠ 0 := ne_of_gt (hD_pos μ hμ s)
  have ha : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) s := by
    simpa using (hasDerivAt_id s).div_const 4
  have hnum : HasDerivAt (fun s : ℝ => μ * Real.exp s) (μ * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul μ
  have hquot : HasDerivAt (fun y : ℝ => μ * Real.exp y / hD μ y)
      ((μ * Real.exp s * hD μ s - μ * Real.exp s * (μ * Real.exp s)) /
        (hD μ s) ^ 2) s :=
    hnum.fun_div (hD_deriv μ s) hDne
  have hnum_eq : (μ * Real.exp s * hD μ s - μ * Real.exp s * (μ * Real.exp s)) =
      μ * (1 - μ) * Real.exp s := by
    simp only [hD]; ring
  have hb : HasDerivAt (fun s : ℝ => μ * Real.exp s / hD μ s - μ)
      (μ * (1 - μ) * Real.exp s / (hD μ s) ^ 2) s := by
    have h := hquot.sub_const μ
    rw [hnum_eq] at h
    exact h
  exact ha.fun_sub hb

private lemma hpsi_mono (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (deriv (hpsi μ)) := by
  apply monotone_of_deriv_nonneg
      (fun x => (hpsi_deriv2 μ hμ x).differentiableAt)
  intro x
  rw [(hpsi_deriv2 μ hμ x).deriv]
  have hDne : hD μ x ≠ 0 := ne_of_gt (hD_pos μ hμ x)
  have hpp : μ * (1 - μ) * Real.exp x / (hD μ x) ^ 2 =
      (μ * Real.exp x / hD μ x) * (1 - μ * Real.exp x / hD μ x) := by
    field_simp
    simp only [hD]
    ring
  rw [hpp]
  have hid : (μ * Real.exp x / hD μ x) * (1 - μ * Real.exp x / hD μ x) =
      1 / 4 - (μ * Real.exp x / hD μ x - 1 / 2) ^ 2 := by ring
  rw [hid]
  linarith [sq_nonneg (μ * Real.exp x / hD μ x - 1 / 2)]

private lemma hD_zero (μ : ℝ) : hD μ 0 = 1 := by simp [hD, Real.exp_zero]

private lemma hpsi_deriv0 (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    deriv (hpsi μ) 0 = 0 := by
  rw [(hpsi_deriv1 μ hμ 0).deriv, hD_zero]
  simp [Real.exp_zero]

private lemma hpsi_zero (μ : ℝ) : hpsi μ 0 = 0 := by
  simp [hpsi, hD_zero, Real.log_one]

private lemma hpsi_nonneg (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ)
    (hs : s ≤ 0) : 0 ≤ hpsi μ s := by
  have hdiff : Differentiable ℝ (hpsi μ) :=
    fun x => (hpsi_deriv1 μ hμ x).differentiableAt
  have hderiv : ∀ x ∈ interior (Set.Iic 0), deriv (hpsi μ) x ≤ 0 := by
    intro x hx
    have hxIic : x ∈ Set.Iic 0 := interior_subset hx
    have hx0 : x ≤ 0 := Set.mem_Iic.mp hxIic
    have hle := hpsi_mono μ hμ hx0
    rw [hpsi_deriv0 μ hμ] at hle
    exact hle
  have hanti : AntitoneOn (hpsi μ) (Set.Iic 0) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
      (hdiff.differentiableOn.mono interior_subset) hderiv
  have hsIic : s ∈ Set.Iic 0 := Set.mem_Iic.mpr hs
  have h0Iic : (0 : ℝ) ∈ Set.Iic 0 := Set.mem_Iic.mpr (le_refl 0)
  have h := hanti hsIic h0Iic hs
  rw [hpsi_zero] at h
  exact h

/-- Hoeffding's lemma, core inequality: for `μ ∈ [0, 1]` and `s ≤ 0`,
`1 + μ (e ^ s - 1) ≤ e ^ (s * μ + s ^ 2 / 8)`. -/
private lemma hoeffding_core (μ s : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ≤ 0) :
    1 + μ * (Real.exp s - 1) ≤ Real.exp (s * μ + s ^ 2 / 8) := by
  have hpos1 : (0 : ℝ) < hD μ s := hD_pos μ hμ s
  have hpos2 : (0 : ℝ) < Real.exp (s * μ + s ^ 2 / 8) := Real.exp_pos _
  have hlog : Real.log (hD μ s) ≤ s * μ + s ^ 2 / 8 := by
    have h := hpsi_nonneg μ hμ s hs
    simp only [hpsi] at h
    linarith
  have hiff := (Real.log_le_log_iff hpos1 hpos2).mp
  rw [Real.log_exp] at hiff
  have hle : hD μ s ≤ Real.exp (s * μ + s ^ 2 / 8) := hiff hlog
  simpa [hD] using hle

/-- **A round costs weight in proportion to the algorithm's loss, up to `η² / 8`**: for losses in
`[0, 1]` and `η ≥ 0`, `total' ≤ total * exp (-η * roundLoss + η² / 8)`. -/
theorem total_update_le_hoeffding {η : ℝ} {w ℓ : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hn : 0 < n)
    (hη : 0 ≤ η) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) :
    total (update η w ℓ) ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 / 8) := by
  have hW : 0 < total w := sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, mem_univ _⟩
  have hS0 : 0 ≤ ∑ i, w i * ℓ i := sum_nonneg fun i _ => mul_nonneg (hw i).le (hℓ0 i)
  have hS1 : ∑ i, w i * ℓ i ≤ total w :=
    sum_le_sum fun i _ => mul_le_of_le_one_right (hw i).le (hℓ1 i)
  have hμ : roundLoss w ℓ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hS0 hW.le, (div_le_one hW).2 hS1⟩
  have h1 : total (update η w ℓ) ≤ total w - (1 - exp (-η)) * ∑ i, w i * ℓ i := by
    unfold total update
    calc ∑ i, w i * exp (-η * ℓ i) ≤ ∑ i, w i * (1 - (1 - exp (-η)) * ℓ i) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (exp_neg_mul_le (hℓ0 i) (hℓ1 i))
            (hw i).le
      _ = ∑ i, w i - (1 - exp (-η)) * ∑ i, w i * ℓ i := by
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun i _ => by ring
  have h2 : total w - (1 - exp (-η)) * ∑ i, w i * ℓ i =
      total w * (1 + roundLoss w ℓ * (exp (-η) - 1)) := by
    unfold roundLoss
    field_simp
    ring
  have hcore := hoeffding_core (roundLoss w ℓ) (-η) hμ (neg_nonpos.2 hη)
  rw [neg_sq] at hcore
  calc total (update η w ℓ) ≤ total w * (1 + roundLoss w ℓ * (exp (-η) - 1)) := h2 ▸ h1
    _ ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hcore hW.le

/-- Over `T` rounds with losses in `[0, 1]`, the final total weight is at most
`total * exp (-η L + T η² / 8)`, where `L` is the algorithm's loss. -/
theorem total_weights_le_hoeffding {η : ℝ} (hn : 0 < n) (hη : 0 ≤ η) :
    ∀ (ls : List (Fin n → ℝ)) (w : Fin n → ℝ), (∀ i, 0 < w i) → Bounded ls →
    total (weights η ls w) ≤ total w * exp (-η * algLoss η ls w + ls.length * (η ^ 2 / 8))
  | [], w, _, _ => by simp [weights, algLoss]
  | ℓ :: ls, w, hw, hb => by
      have hb' : Bounded ls := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
      have hℓ := hb ℓ List.mem_cons_self
      have ih := total_weights_le_hoeffding hn hη ls (update η w ℓ) (update_pos hw ℓ) hb'
      have hstep := total_update_le_hoeffding hw hn hη (fun i => (hℓ i).1) (fun i => (hℓ i).2)
      simp only [weights, algLoss, List.length_cons]
      calc total (weights η ls (update η w ℓ))
          ≤ total (update η w ℓ) *
              exp (-η * algLoss η ls (update η w ℓ) + ls.length * (η ^ 2 / 8)) := ih
        _ ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 / 8) *
              exp (-η * algLoss η ls (update η w ℓ) + ls.length * (η ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_right hstep (exp_pos _).le
        _ = total w * exp (-η * (roundLoss w ℓ + algLoss η ls (update η w ℓ)) +
              ((ls.length + 1 : ℕ) : ℝ) * (η ^ 2 / 8)) := by
          rw [mul_assoc, ← exp_add]; push_cast; ring_nf

/-- **The Hoeffding regret bound for Hedge** (Cesa-Bianchi and Lugosi, Chapter 2): starting from
unit weights with losses in `[0, 1]` and learning rate `η > 0`, the algorithm's loss over `T`
rounds satisfies `L ≤ L_i + log n / η + η T / 8` against every expert `i`. -/
theorem algLoss_le_hoeffding {η : ℝ} (hη : 0 < η) (ls : List (Fin n → ℝ)) (hb : Bounded ls)
    (i : Fin n) :
    algLoss η ls (fun _ => 1) ≤ expertLoss i ls + log n / η + η * ls.length / 8 := by
  have hn : 0 < n := Fin.pos i
  have hup := total_weights_le_hoeffding hn hη.le ls (fun _ => 1) (fun _ => one_pos) hb
  have htot : total (fun _ : Fin n => (1 : ℝ)) = n := by simp [total]
  rw [htot] at hup
  have hlow : weights η ls (fun _ => 1) i ≤ total (weights η ls fun _ => 1) :=
    single_le_sum (fun j _ => by rw [weights_apply]; positivity) (mem_univ i)
  rw [weights_apply, one_mul] at hlow
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have := log_le_log (exp_pos _) (hlow.trans hup)
  rw [log_exp, log_mul hnpos.ne' (exp_pos _).ne', log_exp] at this
  have hT : η * (η * ls.length / 8) = ls.length * (η ^ 2 / 8) := by ring
  have key : η * algLoss η ls (fun _ => 1) ≤
      η * (expertLoss i ls + log n / η + η * ls.length / 8) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hη.ne', hT]
    linarith
  exact le_of_mul_le_mul_left key hη

end Cslib.MachineLearning.Hedge
