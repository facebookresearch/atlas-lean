/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Baum-Welch is EM for hidden Markov models

The Baum-Welch algorithm (Rabiner, *A tutorial on hidden Markov models and selected applications
in speech recognition*, Proc. IEEE 77, 1989; Bishop, *Pattern Recognition and Machine Learning*,
Section 13.2.1) as an instance of the generic EM of
`LatentVariable/ExpectationMaximization.lean`. The latent variable is the state path of length
`T + 1`, the data are `N` observation sequences, and the joint is the path weight of
`Sequence/HiddenMarkov.lean` (`marginal_joint`, `logLik_eq`: the EM likelihood is the HMM
likelihood).

Main results:

* `pathProb_eq_prod`, `log_joint`: the path weight factorizes, and its log is linear in the path's
  counts (`pInit`, `pTrans`, `pEmit`).
* `initCount`, `transCount`, `emitCount`: expected counts under the posterior over paths;
  `emQ_eq`: **`Q(h' | h)` is linear in the expected counts**.
* `mStep`: **the Baum-Welch update** (normalized expected counts), valid on data with a sequence,
  at least one transition, and every symbol observed (`Rich`, `mStep_valid`, `emStep`).
* `emQ_le_emStep`: **the update maximizes `Q(· | h)`** over all valid HMMs;
  `logLik_le_emStep`, `logLik_iterate_emStep_monotone`: **Baum-Welch never decreases the
  likelihood**.

The expected counts are defined here as posterior sums over paths, the specification. Computing
them with forward-backward variables (Rabiner's `γ` and `ξ`) is not formalized in this module.

## Cost model

None: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.BaumWelch

open Real
open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.LatentVariable.BernoulliMixture (sum_mul_log_le_sum_mul_log_div)

variable {S O R : Type*}

/-- The path weight as a product: the initial weight, the `T` transitions and the `T + 1`
emissions. -/
theorem pathProb_eq_prod [CommSemiring R] (h : HMM S O R) (x : ℕ → O) :
    ∀ (T : ℕ) (z : Fin (T + 1) → S), pathProb h x T z =
      h.init (z 0) * (∏ t : Fin T, h.trans (z t.castSucc) (z t.succ)) *
        ∏ t : Fin (T + 1), h.emit (z t) (x t)
  | 0, z => by simp [pathProb]
  | T + 1, z => by
      rw [Fin.prod_univ_castSucc (f := fun t : Fin (T + 1) => h.trans (z t.castSucc) (z t.succ)),
        Fin.prod_univ_castSucc (f := fun t : Fin (T + 2) => h.emit (z t) (x t)), pathProb,
        pathProb_eq_prod h x T]
      simp only [Fin.init, Fin.succ_castSucc, Fin.val_castSucc, Fin.castSucc_zero, Fin.succ_last,
        Fin.val_last]
      ring

/-! ## The EM model of an HMM -/

variable [Fintype S] [Fintype O]

/-- Valid HMM parameters: positive initial, transition and emission distributions. -/
structure Valid (h : HMM S O ℝ) : Prop where
  init_pos : ∀ s, 0 < h.init s
  init_sum : ∑ s, h.init s = 1
  trans_pos : ∀ s s', 0 < h.trans s s'
  trans_sum : ∀ s, ∑ s', h.trans s s' = 1
  emit_pos : ∀ s o, 0 < h.emit s o
  emit_sum : ∀ s, ∑ o, h.emit s o = 1

/-- The valid parameters, the parameter space of Baum-Welch. -/
abbrev ValidHMM (S O : Type*) [Fintype S] [Fintype O] := {h : HMM S O ℝ // Valid h}

variable (T : ℕ)

/-- The EM model of an HMM: the latent variable is the state path of length `T + 1`, the
observation a sequence, and the joint the path weight. -/
noncomputable def joint (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) : ℝ :=
  pathProb h.1 x T z

theorem joint_pos (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) : 0 < joint T h x z := by
  rw [joint, pathProb_eq_prod]
  exact mul_pos (mul_pos (h.2.init_pos _) (Finset.prod_pos fun t _ => h.2.trans_pos _ _))
    (Finset.prod_pos fun t _ => h.2.emit_pos _ _)

/-- The EM marginal of the model is the HMM likelihood. -/
theorem marginal_joint (h : ValidHMM S O) (x : ℕ → O) :
    marginal (joint T) h x = likelihood h.1 x T := rfl

theorem nonempty_of_valid (h : ValidHMM S O) : Nonempty S := by
  by_contra hS
  have : IsEmpty S := not_nonempty_iff.1 hS
  have := h.2.init_sum
  simp at this

variable [DecidableEq S] [DecidableEq O]

/-- Whether the path starts in `s`. -/
def pInit (z : Fin (T + 1) → S) (s : S) : ℝ := if z 0 = s then 1 else 0

/-- The number of transitions `s → s'` along the path. -/
def pTrans (z : Fin (T + 1) → S) (s s' : S) : ℝ :=
  ∑ t : Fin T, if z t.castSucc = s ∧ z t.succ = s' then 1 else 0

/-- The number of times the path emits `o` from `s` on the observations `x`. -/
def pEmit (x : ℕ → O) (z : Fin (T + 1) → S) (s : S) (o : O) : ℝ :=
  ∑ t : Fin (T + 1), if z t = s ∧ x t = o then 1 else 0

private theorem sum_sum_ite_and {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (a : α) (b : β) (f : α → β → ℝ) :
    ∑ s, ∑ s', (if a = s ∧ b = s' then (1 : ℝ) else 0) * f s s' = f a b := by
  simp only [ite_and, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

/-- The log of the path weight in terms of the path's counts. -/
theorem log_joint (h : ValidHMM S O) (x : ℕ → O) (z : Fin (T + 1) → S) :
    log (joint T h x z) = ∑ s, pInit T z s * log (h.1.init s) +
      ∑ s, ∑ s', pTrans T z s s' * log (h.1.trans s s') +
      ∑ s, ∑ o, pEmit T x z s o * log (h.1.emit s o) := by
  rw [joint, pathProb_eq_prod, log_mul (mul_pos (h.2.init_pos _)
      (Finset.prod_pos fun t _ => h.2.trans_pos _ _)).ne'
      (Finset.prod_pos fun t _ => h.2.emit_pos _ _).ne',
    log_mul (h.2.init_pos _).ne' (Finset.prod_pos fun t _ => h.2.trans_pos _ _).ne',
    log_prod fun t _ => (h.2.trans_pos _ _).ne', log_prod fun t _ => (h.2.emit_pos _ _).ne']
  congr 1
  · congr 1
    · simp [pInit]
    · simp only [pTrans, Finset.sum_mul]
      conv_rhs => enter [2, s]; rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ =>
        (sum_sum_ite_and _ _ fun s s' => log (h.1.trans s s')).symm
  · simp only [pEmit, Finset.sum_mul]
    conv_rhs => enter [2, s]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (sum_sum_ite_and _ _ fun s o => log (h.1.emit s o)).symm

omit [Fintype S] [Fintype O] in
theorem pInit_nonneg (z : Fin (T + 1) → S) (s : S) : 0 ≤ pInit T z s := by
  unfold pInit; split_ifs <;> norm_num

omit [Fintype S] [Fintype O] in
theorem pTrans_nonneg (z : Fin (T + 1) → S) (s s' : S) : 0 ≤ pTrans T z s s' :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num

omit [Fintype S] [Fintype O] in
theorem pEmit_nonneg (x : ℕ → O) (z : Fin (T + 1) → S) (s : S) (o : O) : 0 ≤ pEmit T x z s o :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num

/-! ## Expected counts and the M-step -/

variable {N : ℕ} (xs : Fin N → ℕ → O)

/-- The posterior weight of the path `z` for the sequence `xs n`. -/
noncomputable def post (h : ValidHMM S O) (n : Fin N) (z : Fin (T + 1) → S) : ℝ :=
  posterior (joint T) h (xs n) z

/-- The expected number of sequences starting in `s`. -/
noncomputable def initCount (h : ValidHMM S O) (s : S) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pInit T z s

/-- The expected number of transitions `s → s'`. -/
noncomputable def transCount (h : ValidHMM S O) (s s' : S) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pTrans T z s s'

/-- The expected number of emissions of `o` from `s`. -/
noncomputable def emitCount (h : ValidHMM S O) (s : S) (o : O) : ℝ :=
  ∑ n, ∑ z, post T xs h n z * pEmit T (xs n) z s o

/-- **The Baum-Welch M-step**: normalized expected counts. -/
noncomputable def mStep (h : ValidHMM S O) : HMM S O ℝ where
  init s := initCount T xs h s / N
  trans s s' := transCount T xs h s s' / ∑ s'', transCount T xs h s s''
  emit s o := emitCount T xs h s o / ∑ o', emitCount T xs h s o'

private theorem sum_sum_mul_sum {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    (r : ι → κ → ℝ) (g : ι → κ → σ → ℝ) :
    ∑ n, ∑ z, r n z * ∑ s, g n z s = ∑ s, ∑ n, ∑ z, r n z * g n z s := by
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_comm

private theorem sum_sum_mul_mul {ι κ : Type*} [Fintype ι] [Fintype κ] (r c : ι → κ → ℝ) (L : ℝ) :
    ∑ n, ∑ z, r n z * (c n z * L) = (∑ n, ∑ z, r n z * c n z) * L := by
  simp only [Finset.sum_mul, mul_assoc]

/-- `Q(h' | h)` in terms of the expected counts. -/
theorem emQ_eq (h' h : ValidHMM S O) :
    emQ (joint T) xs h' h = ∑ s, initCount T xs h s * log (h'.1.init s) +
      ∑ s, ∑ s', transCount T xs h s s' * log (h'.1.trans s s') +
      ∑ s, ∑ o, emitCount T xs h s o * log (h'.1.emit s o) := by
  simp only [emQ, log_joint, mul_add, Finset.sum_add_distrib]
  simp only [sum_sum_mul_sum, sum_sum_mul_mul, initCount, transCount, emitCount, post]

/-- Data on which the M-step is valid: a sequence, a transition, and every symbol observed. -/
structure Rich (xs : Fin N → ℕ → O) : Prop where
  pos : 0 < N
  len : 0 < T
  covers : ∀ o, ∃ n, ∃ t : Fin (T + 1), xs n t = o

variable {T xs}

omit [DecidableEq S] [DecidableEq O] in
theorem post_pos (h : ValidHMM S O) (n : Fin N) (z : Fin (T + 1) → S) : 0 < post T xs h n z :=
  div_pos (joint_pos T h _ z) (Finset.sum_pos (fun z _ => joint_pos T h _ z) ⟨z, Finset.mem_univ z⟩)

private theorem sum_sum_pos {ι κ : Type*} [Fintype ι] [Fintype κ] {f : ι → κ → ℝ}
    (hf : ∀ n z, 0 ≤ f n z) (n₀ : ι) (z₀ : κ) (h₀ : 0 < f n₀ z₀) : 0 < ∑ n, ∑ z, f n z :=
  lt_of_lt_of_le h₀ <| le_trans (Finset.single_le_sum (fun z _ => hf n₀ z) (Finset.mem_univ z₀))
    (Finset.single_le_sum (f := fun n => ∑ z, f n z)
      (fun n _ => Finset.sum_nonneg fun z _ => hf n z) (Finset.mem_univ n₀))

omit [DecidableEq O] in
theorem initCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s : S) : 0 < initCount T xs h s := by
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pInit_nonneg T z s))
    ⟨0, hx.pos⟩ (fun _ => s) (mul_pos (post_pos h _ _) ?_)
  simp [pInit]

omit [DecidableEq O] in
theorem transCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s s' : S) :
    0 < transCount T xs h s s' := by
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pTrans_nonneg T z s s'))
    ⟨0, hx.pos⟩ (fun i => if i = 0 then s else s') (mul_pos (post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun t : Fin T =>
    if (fun i : Fin (T + 1) => if i = 0 then s else s') t.castSucc = s ∧
      (fun i : Fin (T + 1) => if i = 0 then s else s') t.succ = s' then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ ⟨0, hx.len⟩))
  simp

theorem emitCount_pos (hx : Rich T xs) (h : ValidHMM S O) (s : S) (o : O) :
    0 < emitCount T xs h s o := by
  obtain ⟨n, t, ht⟩ := hx.covers o
  refine sum_sum_pos (fun n z => mul_nonneg (post_pos h n z).le (pEmit_nonneg T _ z s o))
    n (fun _ => s) (mul_pos (post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun t : Fin (T + 1) =>
    if (fun _ : Fin (T + 1) => s) t = s ∧ xs n t = o then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
  simp [ht]

omit [DecidableEq O] in
theorem sum_initCount (h : ValidHMM S O) : ∑ s, initCount T xs h s = N := by
  have := nonempty_of_valid h
  simp only [initCount]
  rw [← sum_sum_mul_sum]
  have hp : ∀ z : Fin (T + 1) → S, ∑ s, pInit T z s = 1 := fun z => by simp [pInit]
  simp only [hp, mul_one, post]
  simp [(isDist_posterior (fun h x z => joint_pos T h x z) h _).2]

theorem mStep_valid (hx : Rich T xs) (h : ValidHMM S O) : Valid (mStep T xs h) where
  init_pos s := div_pos (initCount_pos hx h s) (by exact_mod_cast hx.pos)
  init_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_initCount, div_self (by exact_mod_cast hx.pos.ne')]
  trans_pos s s' := div_pos (transCount_pos hx h s s')
    (Finset.sum_pos (fun s' _ => transCount_pos hx h s s') ⟨s', Finset.mem_univ _⟩)
  trans_sum s := by
    simp only [mStep]
    rw [← Finset.sum_div, div_self (Finset.sum_pos (fun s' _ => transCount_pos hx h s s')
      ⟨s, Finset.mem_univ _⟩).ne']
  emit_pos s o := div_pos (emitCount_pos hx h s o)
    (Finset.sum_pos (fun o _ => emitCount_pos hx h s o) ⟨o, Finset.mem_univ _⟩)
  emit_sum s := by
    obtain ⟨o⟩ : Nonempty O := by
      obtain ⟨n, t, _⟩ := hx.covers (xs ⟨0, hx.pos⟩ 0)
      exact ⟨xs n t⟩
    simp only [mStep]
    rw [← Finset.sum_div, div_self (Finset.sum_pos (fun o _ => emitCount_pos hx h s o)
      ⟨o, Finset.mem_univ _⟩).ne']

variable (T xs) in
/-- One Baum-Welch step, on rich data. -/
noncomputable def emStep (hx : Rich T xs) (h : ValidHMM S O) : ValidHMM S O :=
  ⟨mStep T xs h, mStep_valid hx h⟩

/-! ## Baum-Welch is an EM algorithm -/

variable (T xs) in
/-- **The Baum-Welch M-step maximizes `Q(· | h)`**: no valid HMM `h'` has a larger `Q(h' | h)`
than the Baum-Welch update. -/
theorem emQ_le_emStep (hx : Rich T xs) (h' h : ValidHMM S O) :
    emQ (joint T) xs h' h ≤ emQ (joint T) xs (emStep T xs hx h) h := by
  rw [emQ_eq, emQ_eq]
  have hN : (0 : ℝ) < N := by exact_mod_cast hx.pos
  refine add_le_add (add_le_add ?_ (Finset.sum_le_sum fun s _ => ?_))
    (Finset.sum_le_sum fun s _ => ?_)
  · have hg := sum_mul_log_le_sum_mul_log_div
      (fun s => (initCount_pos hx h s).le) (by rw [sum_initCount]; exact hN) h'.2.init_pos
      h'.2.init_sum
    rw [sum_initCount] at hg
    exact hg
  · exact sum_mul_log_le_sum_mul_log_div (fun s' => (transCount_pos hx h s s').le)
      (Finset.sum_pos (fun s' _ => transCount_pos hx h s s') ⟨s, Finset.mem_univ _⟩)
      (h'.2.trans_pos s) (h'.2.trans_sum s)
  · obtain ⟨o⟩ : Nonempty O := by
      obtain ⟨n, t, _⟩ := hx.covers (xs ⟨0, hx.pos⟩ 0)
      exact ⟨xs n t⟩
    exact sum_mul_log_le_sum_mul_log_div (fun o => (emitCount_pos hx h s o).le)
      (Finset.sum_pos (fun o _ => emitCount_pos hx h s o) ⟨o, Finset.mem_univ _⟩)
      (h'.2.emit_pos s) (h'.2.emit_sum s)

variable (T xs) in
/-- **Each Baum-Welch step does not decrease the log-likelihood** `∑ n, log p(xs n)`. -/
theorem logLik_le_emStep (hx : Rich T xs) (h : ValidHMM S O) :
    logLik (joint T) xs h ≤ logLik (joint T) xs (emStep T xs hx h) := by
  have := nonempty_of_valid h
  exact logLik_le_of_emQ_le (fun h x z => joint_pos T h x z) xs (emQ_le_emStep T xs hx h h)

variable (T xs) in
/-- **The log-likelihood is monotone along the Baum-Welch iterates.** -/
theorem logLik_iterate_emStep_monotone (hx : Rich T xs) (h₀ : ValidHMM S O) :
    Monotone fun t => logLik (joint T) xs ((emStep T xs hx)^[t] h₀) := by
  have := nonempty_of_valid h₀
  exact logLik_iterate_monotone (fun h x z => joint_pos T h x z) xs
    (fun h => emQ_le_emStep T xs hx h h) h₀

omit [DecidableEq S] [DecidableEq O] in
/-- The EM log-likelihood is the sum of the HMM log-likelihoods of the sequences. -/
theorem logLik_eq (h : ValidHMM S O) :
    logLik (joint T) xs h = ∑ n, log (likelihood h.1 (xs n) T) := rfl

end Cslib.MachineLearning.Sequence.BaumWelch
