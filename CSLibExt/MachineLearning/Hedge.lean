/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.SpecialFunctions.Log.Inequalities

/-!
# Hedge (multiplicative weights): the loss bound

Hedge (Freund and Schapire, *A decision-theoretic generalization of on-line learning and an
application to boosting*, J. Comput. Syst. Sci. 55, 1997), the multiplicative-weights form of
Littlestone and Warmuth's weighted majority: in each round the algorithm spreads its bet over `n`
experts in proportion to their weights, the round's losses `ℓ i ∈ [0, 1]` are revealed, it pays
the weighted average loss (`roundLoss`), and each weight is multiplied by `exp (-η ℓ i)`
(`update`).

Main results:

* `exp_neg_mul_le`: on `[0, 1]`, `exp (-η x) ≤ 1 - (1 - exp (-η)) x` (convexity of `exp`).
* `total_update_le`: a round multiplies the total weight by at most
  `exp (-(1 - exp (-η)) roundLoss)`; `total_weights_le`: over all rounds.
* `weights_apply`: expert `i` ends with weight `exp (-η L_i)` (from unit weights).
* `algLoss_le`: **the loss bound** `(1 - exp (-η)) L ≤ η L_i + log n` for every expert `i`, i.e.
  Freund and Schapire's `L ≤ (log n + η L_i) / (1 - exp (-η))` for `η > 0`.
* `total_update_le_sq`, `total_weights_le_sq`, `algLoss_le_sq`: **the second-order bound**
  `L ≤ L_i + η Q + log n / η` for nonnegative (not necessarily bounded) losses, where `Q`
  (`algSq`) sums the rounds' weighted second moments `∑ x_t(i) ℓ_t(i)²` (Hazan, *Introduction to
  Online Convex Optimization*, Theorem 1.3).
* `weights_append`, `algLoss_append`, `algSq_append`: a run splits at any round.

## Relation to `FormalizedTextbooks`

`FormalizedTextbooks/IntroductionToOnlineConvexOptimization/OnlineLearning/Hedge.lean` treats the
same algorithm (weights multiplied by `exp (-ε ℓ i)`, indexed by rounds `t : ℕ`) and derives
Hazan's Theorem 1.3, `hedgeRegret`, and its one-step lemma `hedgeOnestep` from `algLoss_le_sq`
and `total_update_le_sq`.

## Cost model

The cost is the algorithm's (expected) loss; weights are real numbers.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Hedge

open Finset Real

variable {n : ℕ}

/-- After a round with losses `ℓ`, each expert's weight is multiplied by `exp (-η ℓ i)`. -/
noncomputable def update (η : ℝ) (w ℓ : Fin n → ℝ) : Fin n → ℝ := fun i => w i * exp (-η * ℓ i)

/-- The weights after a sequence of rounds. -/
noncomputable def weights (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
  | [], w => w
  | ℓ :: ls, w => weights η ls (update η w ℓ)

/-- The total weight. -/
def total (w : Fin n → ℝ) : ℝ := ∑ i, w i

/-- The algorithm's loss in a round: the loss of the weighted average of the experts (its expected
loss when it follows expert `i` with probability `w i / total w`). -/
noncomputable def roundLoss (w ℓ : Fin n → ℝ) : ℝ := (∑ i, w i * ℓ i) / total w

/-- The algorithm's total loss over a sequence of rounds. -/
noncomputable def algLoss (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | ℓ :: ls, w => roundLoss w ℓ + algLoss η ls (update η w ℓ)

/-- Expert `i`'s total loss. -/
def expertLoss (i : Fin n) (ls : List (Fin n → ℝ)) : ℝ := (ls.map fun ℓ => ℓ i).sum

/-- On `[0, 1]`, `exp (-η x)` lies below its chord: `exp (-η x) ≤ 1 - (1 - exp (-η)) x`. -/
theorem exp_neg_mul_le {η x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp (-η * x) ≤ 1 - (1 - exp (-η)) * x := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-η)) (sub_nonneg.2 hx1) hx0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  calc exp (-η * x) = exp (x * -η) := by ring_nf
    _ ≤ 1 - x + x * exp (-η) := h
    _ = 1 - (1 - exp (-η)) * x := by ring

theorem update_pos {η : ℝ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (ℓ : Fin n → ℝ) (i : Fin n) :
    0 < update η w ℓ i := mul_pos (hw i) (exp_pos _)

/-- **A round costs weight in proportion to the algorithm's loss**:
`total' ≤ total * exp (-(1 - exp (-η)) * roundLoss)`. -/
theorem total_update_le {η : ℝ} {w ℓ : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hn : 0 < n)
    (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) :
    total (update η w ℓ) ≤ total w * exp (-(1 - exp (-η)) * roundLoss w ℓ) := by
  have hW : 0 < total w := sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, mem_univ _⟩
  have h1 : total (update η w ℓ) ≤ total w - (1 - exp (-η)) * ∑ i, w i * ℓ i := by
    unfold total update
    calc ∑ i, w i * exp (-η * ℓ i) ≤ ∑ i, w i * (1 - (1 - exp (-η)) * ℓ i) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (exp_neg_mul_le (hℓ0 i) (hℓ1 i))
            (hw i).le
      _ = ∑ i, w i - (1 - exp (-η)) * ∑ i, w i * ℓ i := by
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun i _ => by ring
  have h2 : total w - (1 - exp (-η)) * ∑ i, w i * ℓ i =
      total w * (1 + -(1 - exp (-η)) * roundLoss w ℓ) := by
    unfold roundLoss
    field_simp
    ring
  rw [h2] at h1
  calc total (update η w ℓ) ≤ total w * (-(1 - exp (-η)) * roundLoss w ℓ + 1) := by linarith
    _ ≤ total w * exp (-(1 - exp (-η)) * roundLoss w ℓ) :=
        mul_le_mul_of_nonneg_left (add_one_le_exp _) hW.le

/-- Losses in `[0, 1]`. -/
def Bounded (ls : List (Fin n → ℝ)) : Prop := ∀ ℓ ∈ ls, ∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ 1

/-- Over all rounds, the total weight shrinks by `exp (-(1 - exp (-η)))` per unit of the
algorithm's loss. -/
theorem total_weights_le {η : ℝ} (hn : 0 < n) : ∀ (ls : List (Fin n → ℝ)) (w : Fin n → ℝ),
    (∀ i, 0 < w i) → Bounded ls →
    total (weights η ls w) ≤ total w * exp (-(1 - exp (-η)) * algLoss η ls w)
  | [], w, _, _ => by simp [weights, algLoss]
  | ℓ :: ls, w, hw, hb => by
      have hb' : Bounded ls := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
      have hℓ := hb ℓ List.mem_cons_self
      have ih := total_weights_le (η := η) hn ls (update η w ℓ) (update_pos hw ℓ) hb'
      have hstep := total_update_le hw hn (fun i => (hℓ i).1) (fun i => (hℓ i).2) (η := η)
      simp only [weights, algLoss]
      calc total (weights η ls (update η w ℓ))
          ≤ total (update η w ℓ) * exp (-(1 - exp (-η)) * algLoss η ls (update η w ℓ)) := ih
        _ ≤ total w * exp (-(1 - exp (-η)) * roundLoss w ℓ) *
            exp (-(1 - exp (-η)) * algLoss η ls (update η w ℓ)) :=
          mul_le_mul_of_nonneg_right hstep (exp_pos _).le
        _ = total w * exp (-(1 - exp (-η)) * (roundLoss w ℓ + algLoss η ls (update η w ℓ))) := by
          rw [mul_assoc, ← exp_add]; ring_nf

/-- Expert `i`'s final weight is `w i * exp (-η L_i)`. -/
theorem weights_apply (η : ℝ) : ∀ (ls : List (Fin n → ℝ)) (w : Fin n → ℝ) (i : Fin n),
    weights η ls w i = w i * exp (-η * expertLoss i ls)
  | [], w, i => by simp [weights, expertLoss]
  | ℓ :: ls, w, i => by
      rw [weights, weights_apply η ls _ i, update, mul_assoc, ← exp_add]
      simp only [expertLoss, List.map_cons, List.sum_cons]
      ring_nf

/-- **The Hedge loss bound** (Freund and Schapire; Littlestone and Warmuth): starting from unit
weights with losses in `[0, 1]` and learning rate `η`, the algorithm's loss `L` satisfies
`(1 - exp (-η)) L ≤ η L_i + log n` against every expert `i`. -/
theorem algLoss_le {η : ℝ} (ls : List (Fin n → ℝ)) (hb : Bounded ls) (i : Fin n) :
    (1 - exp (-η)) * algLoss η ls (fun _ => 1) ≤ η * expertLoss i ls + log n := by
  have hn : 0 < n := Fin.pos i
  have hup := total_weights_le hn ls (fun _ => 1) (fun _ => one_pos) hb (η := η)
  have htot : total (fun _ : Fin n => (1 : ℝ)) = n := by simp [total]
  rw [htot] at hup
  have hlow : weights η ls (fun _ => 1) i ≤ total (weights η ls fun _ => 1) :=
    single_le_sum (fun j _ => by rw [weights_apply]; positivity) (mem_univ i)
  rw [weights_apply, one_mul] at hlow
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have key : exp (-η * expertLoss i ls) ≤ n * exp (-(1 - exp (-η)) * algLoss η ls fun _ => 1) :=
    hlow.trans hup
  have := log_le_log (exp_pos _) key
  rw [log_exp, log_mul hnpos.ne' (exp_pos _).ne', log_exp] at this
  linarith

/-! ## The second-order bound -/

/-- The weighted second moment of a round's losses, `∑ x(i) ℓ(i)²` for the played distribution
`x = w / total w`. -/
noncomputable def roundSq (w ℓ : Fin n → ℝ) : ℝ := (∑ i, w i * ℓ i ^ 2) / total w

/-- The rounds' weighted second moments, summed over a sequence of rounds. -/
noncomputable def algSq (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | ℓ :: ls, w => roundSq w ℓ + algSq η ls (update η w ℓ)

/-- Nonnegative losses. -/
def Nonneg (ls : List (Fin n → ℝ)) : Prop := ∀ ℓ ∈ ls, ∀ i, 0 ≤ ℓ i

/-- **A round costs weight in proportion to the algorithm's loss, up to a second-order term**:
for nonnegative losses and `η ≥ 0`,
`total' ≤ total * exp (-η * roundLoss + η² * roundSq)`. -/
theorem total_update_le_sq {η : ℝ} {w ℓ : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hn : 0 < n)
    (hη : 0 ≤ η) (hℓ : ∀ i, 0 ≤ ℓ i) :
    total (update η w ℓ) ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 * roundSq w ℓ) := by
  have hW : 0 < total w := sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, mem_univ _⟩
  have h1 : total (update η w ℓ) ≤
      total w - η * ∑ i, w i * ℓ i + η ^ 2 * ∑ i, w i * ℓ i ^ 2 := by
    unfold total update
    calc ∑ i, w i * exp (-η * ℓ i) ≤ ∑ i, w i * (1 - η * ℓ i + (η * ℓ i) ^ 2) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
            rw [neg_mul]; exact exp_neg_le_one_sub_add_sq _ (mul_nonneg hη (hℓ i))) (hw i).le
      _ = ∑ i, w i - η * ∑ i, w i * ℓ i + η ^ 2 * ∑ i, w i * ℓ i ^ 2 := by
          rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring
  have h2 : total w - η * ∑ i, w i * ℓ i + η ^ 2 * ∑ i, w i * ℓ i ^ 2 =
      total w * (1 + (-η * roundLoss w ℓ + η ^ 2 * roundSq w ℓ)) := by
    unfold roundLoss roundSq
    field_simp
    ring
  rw [h2] at h1
  calc total (update η w ℓ)
      ≤ total w * ((-η * roundLoss w ℓ + η ^ 2 * roundSq w ℓ) + 1) := by linarith
    _ ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 * roundSq w ℓ) :=
        mul_le_mul_of_nonneg_left (add_one_le_exp _) hW.le

/-- Over all rounds, `total_final ≤ total_initial * exp (-η L + η² Q)` with `Q = algSq`. -/
theorem total_weights_le_sq {η : ℝ} (hn : 0 < n) (hη : 0 ≤ η) :
    ∀ (ls : List (Fin n → ℝ)) (w : Fin n → ℝ), (∀ i, 0 < w i) → Nonneg ls →
    total (weights η ls w) ≤ total w * exp (-η * algLoss η ls w + η ^ 2 * algSq η ls w)
  | [], w, _, _ => by simp [weights, algLoss, algSq]
  | ℓ :: ls, w, hw, hb => by
      have hb' : Nonneg ls := fun ℓ' h => hb ℓ' (List.mem_cons_of_mem _ h)
      have ih := total_weights_le_sq hn hη ls (update η w ℓ) (update_pos hw ℓ) hb'
      have hstep := total_update_le_sq hw hn hη (hb ℓ List.mem_cons_self)
      simp only [weights, algLoss, algSq]
      calc total (weights η ls (update η w ℓ))
          ≤ total (update η w ℓ) *
              exp (-η * algLoss η ls (update η w ℓ) + η ^ 2 * algSq η ls (update η w ℓ)) := ih
        _ ≤ total w * exp (-η * roundLoss w ℓ + η ^ 2 * roundSq w ℓ) *
              exp (-η * algLoss η ls (update η w ℓ) + η ^ 2 * algSq η ls (update η w ℓ)) :=
          mul_le_mul_of_nonneg_right hstep (exp_pos _).le
        _ = total w * exp (-η * (roundLoss w ℓ + algLoss η ls (update η w ℓ)) +
              η ^ 2 * (roundSq w ℓ + algSq η ls (update η w ℓ))) := by
          rw [mul_assoc, ← exp_add]; ring_nf

/-- **The second-order Hedge bound** (Hazan, *Introduction to Online Convex Optimization*,
Theorem 1.3): starting from unit weights with nonnegative losses and learning rate `η > 0`, the
algorithm's loss satisfies `L ≤ L_i + η Q + log n / η` against every expert `i`, where `Q`
(`algSq`) sums the rounds' weighted second moments. Unlike `algLoss_le`, the losses need not be
bounded by `1`. -/
theorem algLoss_le_sq {η : ℝ} (hη : 0 < η) (ls : List (Fin n → ℝ)) (hb : Nonneg ls)
    (i : Fin n) :
    algLoss η ls (fun _ => 1) ≤ expertLoss i ls + η * algSq η ls (fun _ => 1) + log n / η := by
  have hn : 0 < n := Fin.pos i
  have hup := total_weights_le_sq hn hη.le ls (fun _ => 1) (fun _ => one_pos) hb
  have htot : total (fun _ : Fin n => (1 : ℝ)) = n := by simp [total]
  rw [htot] at hup
  have hlow : weights η ls (fun _ => 1) i ≤ total (weights η ls fun _ => 1) :=
    single_le_sum (fun j _ => by rw [weights_apply]; positivity) (mem_univ i)
  rw [weights_apply, one_mul] at hlow
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have := log_le_log (exp_pos _) (hlow.trans hup)
  rw [log_exp, log_mul hnpos.ne' (exp_pos _).ne', log_exp] at this
  have key : η * algLoss η ls (fun _ => 1) ≤
      η * (expertLoss i ls + η * algSq η ls (fun _ => 1) + log n / η) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hη.ne']
    nlinarith
  exact le_of_mul_le_mul_left key hη

/-! ## Splitting a run -/

/-- The weights after `ls ++ ls'` are the weights after `ls'`, started from those after `ls`. -/
theorem weights_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    weights η (ls ++ ls') w = weights η ls' (weights η ls w)
  | [], _, _ => rfl
  | ℓ :: ls, ls', w => weights_append η ls ls' (update η w ℓ)

/-- The loss over `ls ++ ls'` is the loss over `ls` plus the loss over `ls'` from the weights
after `ls`. -/
theorem algLoss_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    algLoss η (ls ++ ls') w = algLoss η ls w + algLoss η ls' (weights η ls w)
  | [], _, _ => by simp [algLoss, weights]
  | ℓ :: ls, ls', w => by
      simp only [List.cons_append, algLoss, weights, algLoss_append η ls ls' (update η w ℓ)]
      ring

/-- The second moments over `ls ++ ls'` split the same way. -/
theorem algSq_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    algSq η (ls ++ ls') w = algSq η ls w + algSq η ls' (weights η ls w)
  | [], _, _ => by simp [algSq, weights]
  | ℓ :: ls, ls', w => by
      simp only [List.cons_append, algSq, weights, algSq_append η ls ls' (update η w ℓ)]
      ring

end Cslib.MachineLearning.Hedge
