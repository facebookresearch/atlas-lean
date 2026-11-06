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

/-- **Hedge weights after a sequence of rounds.** Let $\eta \in \mathbb{R}$ be a learning rate,
let $w \in \mathbb{R}^n$ be initial weights on $n$ experts, and let $\ell_1, \dots, \ell_T \in
\mathbb{R}^n$ be the loss vectors of $T$ rounds, given as a list. The weights after these rounds
are obtained from $w$ by applying the Hedge update once per round, in the order of the list:
round $t$ multiplies the weight of each expert $i$ by $e^{-\eta \ell_t(i)}$. For the empty list
of rounds the weights are $w$. -/
noncomputable def weights (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
  | [], w => w
  | ℓ :: ls, w => weights η ls (update η w ℓ)

/-- **Total weight of the Hedge experts.** The total weight of weights $w$ on $n$ experts is
$\sum_i w_i$. -/
def total (w : Fin n → ℝ) : ℝ := ∑ i, w i

/-- **Loss of a Hedge round.** For weights $w$ and losses $\ell$ on $n$ experts, the algorithm's
loss in the round is $\left(\sum_i w_i \ell_i\right) / W$, where $W = \sum_i w_i$ is the total
weight. This is its expected loss when it follows expert $i$ with probability $w_i / W$. -/
noncomputable def roundLoss (w ℓ : Fin n → ℝ) : ℝ := (∑ i, w i * ℓ i) / total w

/-- **Loss of the Hedge algorithm.** Let $\eta$ be a learning rate, $w \in \mathbb{R}^n$ initial
weights on $n$ experts and $\ell_1, \dots, \ell_T \in \mathbb{R}^n$ the losses of $T$ rounds. Set
$w_1 = w$ and $w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$. The algorithm's total loss is
$\sum_{t=1}^T \bigl(\sum_j w_t(j) \ell_t(j)\bigr) / \sum_j w_t(j)$, the sum over the rounds of
the weighted average of that round's losses; a round whose total weight is $0$ contributes
$0$. -/
noncomputable def algLoss (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | ℓ :: ls, w => roundLoss w ℓ + algLoss η ls (update η w ℓ)

/-- **Total loss of an expert.** For an expert $i$ among $n$ experts and a finite sequence of loss
vectors $\ell_1, \dots, \ell_T \in \mathbb{R}^n$, the total loss of expert $i$ is
$\sum_{t=1}^T \ell_t(i)$. -/
def expertLoss (i : Fin n) (ls : List (Fin n → ℝ)) : ℝ := (ls.map fun ℓ => ℓ i).sum

/-- **The exponential lies below its chord on the unit interval.** For every real $\eta$ and
every $x \in [0, 1]$, $e^{-\eta x} \le 1 - (1 - e^{-\eta}) x$. -/
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

/-- **A round costs weight in proportion to the algorithm's loss.** Let $n > 0$, let $w$ be
positive weights on $n$ experts, let $\ell$ be losses with $0 \le \ell_i \le 1$ for every $i$, and
let $\eta$ be a real number. Let $w'$ be the Hedge update of $w$ with learning rate $\eta$, so that
$w'_i = w_i e^{-\eta \ell_i}$, and let $W$ and $W'$ be the total weights of $w$ and $w'$. Then
$W' \le W \exp(-(1 - e^{-\eta}) L)$, where $L$ is the round's loss under the weights $w$. -/
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

/-- **Losses in the unit interval.** A finite sequence of loss vectors
$\ell_1, \dots, \ell_T \in \mathbb{R}^n$ on $n$ experts has losses in $[0, 1]$ when
$0 \le \ell_t(i) \le 1$ for every round $t$ and every expert $i$. -/
def Bounded (ls : List (Fin n → ℝ)) : Prop := ∀ ℓ ∈ ls, ∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ 1

/-- **Weight decay over a Hedge run.** Let $n > 0$ and let $\eta$ be a real number. For every
sequence of rounds with losses in $[0, 1]$ and all positive initial weights $w$ on $n$ experts,
the total weight after running Hedge with learning rate $\eta$ from $w$ is at most
$W \exp(-(1 - e^{-\eta}) L)$, where $W$ is the total weight of $w$ and $L$ is the algorithm's
total loss over the rounds for the run from $w$ with learning rate $\eta$. -/
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

/-- **Closed form of the Hedge weights.** For every learning rate $\eta$, sequence of rounds,
initial weights $w$ and expert $i$, the weight of expert $i$ after running Hedge on the rounds from
$w$ is $w_i e^{-\eta L_i}$, where $L_i$ is expert $i$'s total loss over the rounds. -/
theorem weights_apply (η : ℝ) : ∀ (ls : List (Fin n → ℝ)) (w : Fin n → ℝ) (i : Fin n),
    weights η ls w i = w i * exp (-η * expertLoss i ls)
  | [], w, i => by simp [weights, expertLoss]
  | ℓ :: ls, w, i => by
      rw [weights, weights_apply η ls _ i, update, mul_assoc, ← exp_add]
      simp only [expertLoss, List.map_cons, List.sum_cons]
      ring_nf

/-- **The Hedge loss bound.** Let $\eta$ be a real number, and let $\ell_1, \dots, \ell_T$ be loss
vectors in $[0, 1]^n$ for $n$ experts. Run Hedge with learning rate $\eta$ from unit weights, that
is $w_1(j) = 1$ and $w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$, and let
$x_t(j) = w_t(j) / \sum_k w_t(k)$ be the distribution played in round $t$. Then for every
expert $i$,

$$(1 - e^{-\eta}) \sum_{t=1}^T \sum_j x_t(j) \ell_t(j) \le \eta \sum_{t=1}^T \ell_t(i) + \log n.$$

For $\eta > 0$, writing $L$ for the algorithm's loss and $L_i$ for expert $i$'s loss, this is
the bound $L \le (\log n + \eta L_i) / (1 - e^{-\eta})$ of Freund and Schapire (after
Littlestone and Warmuth). -/
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

/-- **Weighted second moment of a Hedge round.** For weights $w$ and losses $\ell$ on $n$
experts, the round's weighted second moment is $\left(\sum_i w_i \ell_i^2\right) / W$, where
$W = \sum_i w_i$ is the total weight; that is, $\sum_i x_i \ell_i^2$ for the played distribution
$x = w / W$. -/
noncomputable def roundSq (w ℓ : Fin n → ℝ) : ℝ := (∑ i, w i * ℓ i ^ 2) / total w

/-- **Summed second moments of the Hedge losses.** Let $\eta$ be a learning rate,
$w \in \mathbb{R}^n$ initial weights on $n$ experts and $\ell_1, \dots, \ell_T \in \mathbb{R}^n$
the losses of $T$ rounds. Set $w_1 = w$ and $w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$. The summed
second moment is $\sum_{t=1}^T \bigl(\sum_j w_t(j) \ell_t(j)^2\bigr) / \sum_j w_t(j)$, the sum over
the rounds of the weighted second moment of that round's losses; a round whose total weight is
$0$ contributes $0$. -/
noncomputable def algSq (η : ℝ) : List (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | ℓ :: ls, w => roundSq w ℓ + algSq η ls (update η w ℓ)

/-- **Nonnegative losses.** A finite sequence of loss vectors
$\ell_1, \dots, \ell_T \in \mathbb{R}^n$ on $n$ experts has nonnegative losses when
$\ell_t(i) \ge 0$ for every round $t$ and every expert $i$. -/
def Nonneg (ls : List (Fin n → ℝ)) : Prop := ∀ ℓ ∈ ls, ∀ i, 0 ≤ ℓ i

/-- **A round costs weight in proportion to the algorithm's loss, up to a second-order term.**
Let $n > 0$, let $w$ be positive weights on $n$ experts, let $\ell$ be nonnegative losses, and let
$\eta \ge 0$. Let $w'$ be the Hedge update of $w$ with learning rate $\eta$, so that
$w'_i = w_i e^{-\eta \ell_i}$, and let $W$ and $W'$ be the total weights of $w$ and $w'$. Then
$W' \le W \exp(-\eta L + \eta^2 Q)$, where $L$ is the round's loss and $Q$ its weighted second
moment under the weights $w$. -/
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

/-- **Weight decay over a Hedge run, second-order form.** Let $n > 0$ and $\eta \ge 0$. For every
sequence of rounds with nonnegative losses and all positive initial weights $w$ on $n$ experts,
the total weight after running Hedge with learning rate $\eta$ from $w$ is at most
$W \exp(-\eta L + \eta^2 Q)$. Here $W$ is the total weight of $w$, $L$ is the algorithm's total
loss over the rounds and $Q$ is the sum of the rounds' weighted second moments, both for the run
from $w$ with learning rate $\eta$. -/
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

/-- **The second-order Hedge bound.** Let $\eta > 0$, and let $\ell_1, \dots, \ell_T$ be loss
vectors in $\mathbb{R}^n$ for $n$ experts with $\ell_t(j) \ge 0$ for all $t$ and $j$. Run Hedge
with learning rate $\eta$ from unit weights, that is $w_1(j) = 1$ and
$w_{t+1}(j) = w_t(j) e^{-\eta \ell_t(j)}$, and let $x_t(j) = w_t(j) / \sum_k w_t(k)$ be the
distribution played in round $t$. Then for every expert $i$,

$$\sum_{t=1}^T \sum_j x_t(j) \ell_t(j) \le \sum_{t=1}^T \ell_t(i) +
\eta \sum_{t=1}^T \sum_j x_t(j) \ell_t(j)^2 + \frac{\log n}{\eta}.$$

This is Theorem 1.3 of Hazan, *Introduction to Online Convex Optimization*. Unlike the
first-order Hedge loss bound, the losses need not be at most $1$. -/
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

/-- **A Hedge run splits at any round.** For every learning rate $\eta$, sequences of rounds
$\lambda$ and $\lambda'$, and initial weights $w$, the weights after running Hedge on the rounds of
$\lambda$ followed by those of $\lambda'$, starting from $w$, equal the weights after running it on
$\lambda'$ starting from the weights reached after $\lambda$ from $w$. -/
theorem weights_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    weights η (ls ++ ls') w = weights η ls' (weights η ls w)
  | [], _, _ => rfl
  | ℓ :: ls, ls', w => weights_append η ls ls' (update η w ℓ)

/-- **The Hedge loss splits at any round.** Fix a learning rate $\eta$ and $n$ experts. For a
finite sequence $\sigma$ of loss vectors in $\mathbb{R}^n$ and weights $w \in \mathbb{R}^n$, write
$L(\sigma, w)$ for the algorithm's total loss over $\sigma$ started from $w$, and $W(\sigma, w)$
for the weights after the rounds of $\sigma$ started from $w$. Then for all such sequences
$\sigma, \sigma'$ and all weights $w$, the loss over the concatenation $\sigma\sigma'$ satisfies
$L(\sigma\sigma', w) = L(\sigma, w) + L(\sigma', W(\sigma, w))$. -/
theorem algLoss_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    algLoss η (ls ++ ls') w = algLoss η ls w + algLoss η ls' (weights η ls w)
  | [], _, _ => by simp [algLoss, weights]
  | ℓ :: ls, ls', w => by
      simp only [List.cons_append, algLoss, weights, algLoss_append η ls ls' (update η w ℓ)]
      ring

/-- **The summed second moments split at any round.** Fix a learning rate $\eta$ and $n$ experts.
For a finite sequence $\sigma$ of loss vectors in $\mathbb{R}^n$ and weights $w \in \mathbb{R}^n$,
write $Q(\sigma, w)$ for the sum over the rounds of $\sigma$ of the weighted second moments of the
losses, started from $w$, and $W(\sigma, w)$ for the weights after the rounds of $\sigma$ started
from $w$. Then for all such sequences $\sigma, \sigma'$ and all weights $w$,
$Q(\sigma\sigma', w) = Q(\sigma, w) + Q(\sigma', W(\sigma, w))$. -/
theorem algSq_append (η : ℝ) : ∀ (ls ls' : List (Fin n → ℝ)) (w : Fin n → ℝ),
    algSq η (ls ++ ls') w = algSq η ls w + algSq η ls' (weights η ls w)
  | [], _, _ => by simp [algSq, weights]
  | ℓ :: ls, ls', w => by
      simp only [List.cons_append, algSq, weights, algSq_append η ls ls' (update η w ℓ)]
      ring

end Cslib.MachineLearning.Hedge
