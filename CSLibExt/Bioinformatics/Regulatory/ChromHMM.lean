/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.BaumWelch
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# ChromHMM: a hidden Markov model with product-Bernoulli emissions

ChromHMM (Ernst and Kellis 2010, 2012) segments a genome into chromatin states with a hidden
Markov model whose observation at each genomic bin is the binary vector `o : Fin d → Bool` of the
presence calls of `d` chromatin marks, and whose emission distribution in state `s` is a product
of independent Bernoulli distributions, `bernPMF (prob s) o = ∏ j, prob s j ^ o j (1 - prob s
j) ^ (1 - o j)`. It fits the model with Baum-Welch.

Because the emission family is constrained to products of Bernoulli distributions, the
emission update is not the categorical Baum-Welch update of `Sequence/BaumWelch.lean` (which would
need every one of the `2 ^ d` vectors to be observed): it is the **factored update**
`prob s j = (expected number of bins in state s with mark j present) /
(expected number of bins in state s)` (`mStep`, `markOnes_eq`). We prove that this is the exact
M-step over the product-Bernoulli family, so the algorithm is an EM algorithm and never decreases
the likelihood.

## Main results

* `sum_bernPMF`: a product of Bernoulli distributions sums to one.
* `sum_mul_log_bernPMF`, `sum_mul_log_bernPMF_le_factoredUpdate`: the expected emission
  log-likelihood splits over the marks, and the factored update maximizes it.
* `markOnes_eq`: the factored update in posterior form.
* `mStep_valid`: on data where every mark is both present and absent somewhere (`Rich`), the
  update is a valid parameter.
* `emQ_le_emStep`: **the update maximizes `Q(· | θ)`** over all valid product-Bernoulli HMMs.
* `logLik_le_emStep`, `logLik_iterate_emStep_monotone`: **the likelihood never decreases**
  along the ChromHMM iterates; `logLik_eq`: it is the HMM likelihood of the sequences.

## References

* J. Ernst and M. Kellis, *Discovery and characterization of chromatin states for systematic
  annotation of the human genome*, Nat. Biotechnol. 28 (2010), 817–825.
* J. Ernst and M. Kellis, *ChromHMM: automating chromatin-state discovery and
  characterization*, Nat. Methods 9 (2012), 215–216.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Regulatory.ChromHMM

open Real Finset
open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence
open Cslib.MachineLearning.Sequence.BaumWelch (ValidHMM emitCount initCount transCount post pEmit
  pInit pTrans)
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.LatentVariable.BernoulliMixture (bernPMF bernPMF_pos
  sum_mul_log_le_sum_mul_log_div)

variable {d : ℕ}

/-! ## The factored emission update -/

/-- The weight `∑ o with o j = true, c o` of the binary vectors with mark `j` present. -/
noncomputable def onesCount (c : (Fin d → Bool) → ℝ) (j : Fin d) : ℝ :=
  ∑ o, if o j then c o else 0

/-- The weight `∑ o with o j = false, c o` of the binary vectors with mark `j` absent. -/
noncomputable def zerosCount (c : (Fin d → Bool) → ℝ) (j : Fin d) : ℝ :=
  ∑ o, if o j then 0 else c o

/-- The factored (per-mark) update `ones j / (ones j + zeros j)`. -/
noncomputable def factoredUpdate (c : (Fin d → Bool) → ℝ) (j : Fin d) : ℝ :=
  onesCount c j / (onesCount c j + zerosCount c j)

/-- A product of Bernoulli distributions sums to one over the binary vectors, for every
parameter vector `p` (the identity is algebraic: `∏ j, (p j + (1 - p j)) = 1`). -/
theorem sum_bernPMF (p : Fin d → ℝ) : ∑ x, bernPMF p x = 1 := by
  classical
  unfold bernPMF
  rw [← Fintype.prod_sum (fun j (b : Bool) => if b then p j else 1 - p j)]
  simp

/-- The expected log-likelihood of weighted binary vectors under a product of Bernoulli
distributions with parameters in `(0, 1)` splits over the marks. -/
theorem sum_mul_log_bernPMF (c : (Fin d → Bool) → ℝ) {p : Fin d → ℝ} (hp0 : ∀ j, 0 < p j)
    (hp1 : ∀ j, p j < 1) :
    ∑ o, c o * log (bernPMF p o) =
      ∑ j, (onesCount c j * log (p j) + zerosCount c j * log (1 - p j)) := by
  classical
  have hlog (o : Fin d → Bool) :
      log (bernPMF p o) = ∑ j, if o j then log (p j) else log (1 - p j) := by
    unfold bernPMF
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j _
      cases o j <;> rfl
    · intro j _
      cases o j
      · exact (sub_pos.mpr (hp1 j)).ne'
      · exact (hp0 j).ne'
  simp_rw [hlog, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold onesCount zerosCount
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  cases o j <;> simp

private theorem bernoulli_log_le {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq0 : 0 < q) (hq1 : q < 1) :
    a * log q + b * log (1 - q) ≤
      a * log (a / (a + b)) + b * log (b / (a + b)) := by
  have hab : 0 < a + b := add_pos ha hb
  have hr : 0 < a / (a + b) := div_pos ha hab
  have hs : 0 < b / (a + b) := div_pos hb hab
  have hq : 0 < 1 - q := sub_pos.mpr hq1
  have hleft : a * (log q - log (a / (a + b))) ≤ q * (a + b) - a := by
    rw [← Real.log_div hq0.ne' hr.ne']
    calc
      a * log (q / (a / (a + b))) ≤ a * (q / (a / (a + b)) - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hq0 hr)) ha.le
      _ = q * (a + b) - a := by
        field_simp [ha.ne', hb.ne', hab.ne']
  have hright : b * (log (1 - q) - log (b / (a + b))) ≤
      (1 - q) * (a + b) - b := by
    rw [← Real.log_div hq.ne' hs.ne']
    calc
      b * log ((1 - q) / (b / (a + b))) ≤ b * ((1 - q) / (b / (a + b)) - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hq hs)) hb.le
      _ = (1 - q) * (a + b) - b := by
        field_simp [ha.ne', hb.ne', hab.ne']
  linarith

/-- **The factored update maximizes the expected log-likelihood** over all products of
Bernoulli distributions with parameters in `(0, 1)`, for nonnegative weights `c` in which every
mark is both present and absent with positive weight. -/
theorem sum_mul_log_bernPMF_le_factoredUpdate {c : (Fin d → Bool) → ℝ} (hc : ∀ o, 0 ≤ c o)
    (h1 : ∀ j, 0 < onesCount c j) (h0 : ∀ j, 0 < zerosCount c j) {p : Fin d → ℝ}
    (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j < 1) :
    ∑ o, c o * log (bernPMF p o) ≤ ∑ o, c o * log (bernPMF (factoredUpdate c) o) := by
  have hsum (j : Fin d) : 0 < onesCount c j + zerosCount c j := by
    apply add_pos_of_nonneg_of_pos ?_ (h0 j)
    exact Finset.sum_nonneg fun o _ => by
      cases o j <;> simp [hc o]
  have hu0 (j : Fin d) : 0 < factoredUpdate c j :=
    div_pos (h1 j) (hsum j)
  have hu1 (j : Fin d) : factoredUpdate c j < 1 := by
    exact (div_lt_one (hsum j)).mpr (by linarith [h0 j])
  rw [sum_mul_log_bernPMF c hp0 hp1, sum_mul_log_bernPMF c hu0 hu1]
  apply Finset.sum_le_sum
  intro j _
  have hcompl : 1 - factoredUpdate c j =
      zerosCount c j / (onesCount c j + zerosCount c j) := by
    unfold factoredUpdate
    field_simp [(hsum j).ne']
    ring
  rw [hcompl]
  exact bernoulli_log_le (h1 j) (h0 j) (hp0 j) (hp1 j)

/-- The factored update is positive when both counts are. -/
theorem factoredUpdate_pos {c : (Fin d → Bool) → ℝ} (h1 : ∀ j, 0 < onesCount c j)
    (h0 : ∀ j, 0 < zerosCount c j) (j : Fin d) : 0 < factoredUpdate c j :=
  div_pos (h1 j) (add_pos (h1 j) (h0 j))

/-- The factored update is below one when both counts are positive. -/
theorem factoredUpdate_lt_one {c : (Fin d → Bool) → ℝ} (h1 : ∀ j, 0 < onesCount c j)
    (h0 : ∀ j, 0 < zerosCount c j) (j : Fin d) : factoredUpdate c j < 1 :=
  (div_lt_one (add_pos (h1 j) (h0 j))).2 (lt_add_of_pos_right _ (h0 j))

/-! ## The model -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- ChromHMM parameters: initial and transition weights, and the presence probability of each
mark in each state. -/
structure Params (S : Type*) (d : ℕ) where
  /-- The initial weight of each state. -/
  init : S → ℝ
  /-- The transition weights. -/
  trans : S → S → ℝ
  /-- The probability that mark `j` is present in state `s`. -/
  prob : S → Fin d → ℝ

/-- The HMM of ChromHMM parameters: emissions are products of Bernoulli distributions. -/
noncomputable def Params.toHMM (θ : Params S d) : HMM S (Fin d → Bool) ℝ where
  init := θ.init
  trans := θ.trans
  emit s o := bernPMF (θ.prob s) o

/-- Valid parameters: positive initial and transition distributions, mark probabilities in
`(0, 1)`. -/
structure Params.Valid (θ : Params S d) : Prop where
  init_pos : ∀ s, 0 < θ.init s
  init_sum : ∑ s, θ.init s = 1
  trans_pos : ∀ s s', 0 < θ.trans s s'
  trans_sum : ∀ s, ∑ s', θ.trans s s' = 1
  prob_pos : ∀ s j, 0 < θ.prob s j
  prob_lt_one : ∀ s j, θ.prob s j < 1

/-- The parameter space of ChromHMM. -/
abbrev ValidParams (S : Type*) [Fintype S] (d : ℕ) := {θ : Params S d // θ.Valid}

omit [DecidableEq S] in
/-- A valid ChromHMM parameter is a valid HMM. -/
theorem Params.Valid.toHMM {θ : Params S d} (h : θ.Valid) : BaumWelch.Valid θ.toHMM where
  init_pos := h.init_pos
  init_sum := h.init_sum
  trans_pos := h.trans_pos
  trans_sum := h.trans_sum
  emit_pos s o := bernPMF_pos (h.prob_pos s) (h.prob_lt_one s) o
  emit_sum s := sum_bernPMF (θ.prob s)

/-- The valid HMM of a valid ChromHMM parameter. -/
noncomputable def toValidHMM (θ : ValidParams S d) : ValidHMM S (Fin d → Bool) :=
  ⟨θ.1.toHMM, θ.2.toHMM⟩

variable (T : ℕ)

/-- The EM model of ChromHMM: the joint weight of a state path and a sequence of mark vectors. -/
noncomputable def joint (θ : ValidParams S d) (x : ℕ → Fin d → Bool) (z : Fin (T + 1) → S) :
    ℝ :=
  BaumWelch.joint T (toValidHMM θ) x z

variable {N : ℕ} (xs : Fin N → ℕ → Fin d → Bool)

/-- The expected number of bins in state `s` with mark `j` present. -/
noncomputable def markOnes (θ : ValidParams S d) (s : S) (j : Fin d) : ℝ :=
  onesCount (emitCount T xs (toValidHMM θ) s) j

/-- The expected number of bins in state `s` with mark `j` absent. -/
noncomputable def markZeros (θ : ValidParams S d) (s : S) (j : Fin d) : ℝ :=
  zerosCount (emitCount T xs (toValidHMM θ) s) j

/-- **The ChromHMM M-step**: the Baum-Welch initial and transition updates, and the factored
emission update `prob s j = markOnes / (markOnes + markZeros)`. -/
noncomputable def mStep (θ : ValidParams S d) : Params S d where
  init := (BaumWelch.mStep T xs (toValidHMM θ)).init
  trans := (BaumWelch.mStep T xs (toValidHMM θ)).trans
  prob s := factoredUpdate (emitCount T xs (toValidHMM θ) s)

/-- **The factored update in posterior form**: `markOnes s j` is the posterior expected number
of bins in state `s` at which mark `j` is present. -/
theorem markOnes_eq (θ : ValidParams S d) (s : S) (j : Fin d) :
    markOnes T xs θ s j = ∑ n, ∑ z, post T xs (toValidHMM θ) n z *
      ∑ t : Fin (T + 1), if z t = s ∧ xs n t j = true then 1 else 0 := by
  have key : markOnes T xs θ s j = ∑ o, (if o j = true then (1 : ℝ) else 0) *
      emitCount T xs (toValidHMM θ) s o :=
    sum_congr rfl fun o _ => by split_ifs <;> simp
  rw [key]
  simp only [emitCount, pEmit, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_eq_single (xs n t)]
  · by_cases hz : z t = s <;> by_cases hj : xs n t j = true <;> simp [hz, hj]
  · intro o _ ho; simp [Ne.symm ho]
  · simp

/-- Data on which the ChromHMM M-step is valid: a sequence, a transition, and every mark both
present and absent somewhere. -/
structure Rich (xs : Fin N → ℕ → Fin d → Bool) : Prop where
  pos : 0 < N
  len : 0 < T
  marks : ∀ j b, ∃ n, ∃ t : Fin (T + 1), xs n t j = b

variable {T xs}

private theorem sum_sum_pos {ι κ : Type*} [Fintype ι] [Fintype κ] {f : ι → κ → ℝ}
    (hf : ∀ n z, 0 ≤ f n z) (n₀ : ι) (z₀ : κ) (h₀ : 0 < f n₀ z₀) : 0 < ∑ n, ∑ z, f n z :=
  lt_of_lt_of_le h₀ <| le_trans (single_le_sum (fun z _ => hf n₀ z) (mem_univ z₀))
    (single_le_sum (f := fun n => ∑ z, f n z)
      (fun n _ => sum_nonneg fun z _ => hf n z) (mem_univ n₀))

private theorem initCount_pos' (hx : Rich T xs) (h : ValidHMM S (Fin d → Bool)) (s : S) :
    0 < initCount T xs h s := by
  refine sum_sum_pos (fun n z => mul_nonneg (BaumWelch.post_pos h n z).le
    (BaumWelch.pInit_nonneg T z s)) ⟨0, hx.pos⟩ (fun _ => s)
    (mul_pos (BaumWelch.post_pos h _ _) ?_)
  simp [pInit]

private theorem transCount_pos' (hx : Rich T xs) (h : ValidHMM S (Fin d → Bool)) (s s' : S) :
    0 < transCount T xs h s s' := by
  refine sum_sum_pos (fun n z => mul_nonneg (BaumWelch.post_pos h n z).le
    (BaumWelch.pTrans_nonneg T z s s')) ⟨0, hx.pos⟩ (fun i => if i = 0 then s else s')
    (mul_pos (BaumWelch.post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun t : Fin T =>
    if (fun i : Fin (T + 1) => if i = 0 then s else s') t.castSucc = s ∧
      (fun i : Fin (T + 1) => if i = 0 then s else s') t.succ = s' then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (mem_univ ⟨0, hx.len⟩))
  simp

private theorem emitCount_nonneg (h : ValidHMM S (Fin d → Bool)) (s : S) (o : Fin d → Bool) :
    0 ≤ emitCount T xs h s o :=
  sum_nonneg fun n _ => sum_nonneg fun z _ =>
    mul_nonneg (BaumWelch.post_pos h n z).le (BaumWelch.pEmit_nonneg T _ z s o)

private theorem emitCount_pos_of (h : ValidHMM S (Fin d → Bool)) (s : S) (n : Fin N)
    (t : Fin (T + 1)) : 0 < emitCount T xs h s (xs n t) := by
  refine sum_sum_pos (fun n z => mul_nonneg (BaumWelch.post_pos h n z).le
    (BaumWelch.pEmit_nonneg T _ z s _)) n (fun _ => s) (mul_pos (BaumWelch.post_pos h _ _) ?_)
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun t' : Fin (T + 1) =>
    if (fun _ : Fin (T + 1) => s) t' = s ∧ xs n t' = xs n t then (1 : ℝ) else 0)
    (fun t _ => by split_ifs <;> norm_num) (mem_univ t))
  simp

private theorem onesCount_pos (hx : Rich T xs) (h : ValidHMM S (Fin d → Bool)) (s : S)
    (j : Fin d) : 0 < onesCount (emitCount T xs h s) j := by
  obtain ⟨n, t, ht⟩ := hx.marks j true
  have hnn : ∀ o ∈ univ, 0 ≤ if o j = true then emitCount T xs h s o else 0 := fun o _ => by
    split_ifs
    exacts [emitCount_nonneg h s o, le_rfl]
  refine lt_of_lt_of_le ?_ (single_le_sum hnn (mem_univ (xs n t)))
  simp only [ht, ite_true]
  exact emitCount_pos_of h s n t

private theorem zerosCount_pos (hx : Rich T xs) (h : ValidHMM S (Fin d → Bool)) (s : S)
    (j : Fin d) : 0 < zerosCount (emitCount T xs h s) j := by
  obtain ⟨n, t, ht⟩ := hx.marks j false
  have hnn : ∀ o ∈ univ, 0 ≤ if o j = true then 0 else emitCount T xs h s o := fun o _ => by
    split_ifs
    exacts [le_rfl, emitCount_nonneg h s o]
  refine lt_of_lt_of_le ?_ (single_le_sum hnn (mem_univ (xs n t)))
  simp only [ht, Bool.false_eq_true, ite_false]
  exact emitCount_pos_of h s n t

/-- **The ChromHMM update is a valid parameter** on rich data. -/
theorem mStep_valid (hx : Rich T xs) (θ : ValidParams S d) : (mStep T xs θ).Valid where
  init_pos s := div_pos (initCount_pos' hx _ s) (by exact_mod_cast hx.pos)
  init_sum := by
    simp only [mStep, BaumWelch.mStep]
    rw [← sum_div, BaumWelch.sum_initCount, div_self (by exact_mod_cast hx.pos.ne')]
  trans_pos s s' := div_pos (transCount_pos' hx _ s s')
    (sum_pos (fun s' _ => transCount_pos' hx _ s s') ⟨s', mem_univ _⟩)
  trans_sum s := by
    simp only [mStep, BaumWelch.mStep]
    rw [← sum_div, div_self (sum_pos (fun s' _ => transCount_pos' hx _ s s')
      ⟨s, mem_univ _⟩).ne']
  prob_pos s := factoredUpdate_pos (onesCount_pos hx _ s) (zerosCount_pos hx _ s)
  prob_lt_one s := factoredUpdate_lt_one (onesCount_pos hx _ s) (zerosCount_pos hx _ s)

variable (T xs) in
/-- One ChromHMM step, on rich data. -/
noncomputable def emStep (hx : Rich T xs) (θ : ValidParams S d) : ValidParams S d :=
  ⟨mStep T xs θ, mStep_valid hx θ⟩

omit [DecidableEq S] in
/-- The ChromHMM joint weight is positive. -/
theorem joint_pos (θ : ValidParams S d) (x : ℕ → Fin d → Bool) (z : Fin (T + 1) → S) :
    0 < joint T θ x z :=
  BaumWelch.joint_pos T (toValidHMM θ) x z

omit [DecidableEq S] in
private theorem emQ_joint (θ' θ : ValidParams S d) :
    emQ (joint T) xs θ' θ = emQ (BaumWelch.joint T) xs (toValidHMM θ') (toValidHMM θ) := rfl

variable (T xs) in
/-- **The ChromHMM update maximizes `Q(· | θ)`** over all valid product-Bernoulli HMMs. -/
theorem emQ_le_emStep (hx : Rich T xs) (θ' θ : ValidParams S d) :
    emQ (joint T) xs θ' θ ≤ emQ (joint T) xs (emStep T xs hx θ) θ := by
  rw [emQ_joint, emQ_joint, BaumWelch.emQ_eq, BaumWelch.emQ_eq]
  have hN : (0 : ℝ) < N := by exact_mod_cast hx.pos
  refine add_le_add (add_le_add ?_ (sum_le_sum fun s _ => ?_)) (sum_le_sum fun s _ => ?_)
  · have hg := sum_mul_log_le_sum_mul_log_div
      (fun s => (initCount_pos' hx (toValidHMM θ) s).le)
      (by rw [BaumWelch.sum_initCount]; exact hN) θ'.2.init_pos θ'.2.init_sum
    rw [BaumWelch.sum_initCount] at hg
    exact hg
  · exact sum_mul_log_le_sum_mul_log_div (fun s' => (transCount_pos' hx _ s s').le)
      (sum_pos (fun s' _ => transCount_pos' hx _ s s') ⟨s, mem_univ _⟩)
      (θ'.2.trans_pos s) (θ'.2.trans_sum s)
  · exact sum_mul_log_bernPMF_le_factoredUpdate (fun o => emitCount_nonneg _ s o)
      (onesCount_pos hx _ s) (zerosCount_pos hx _ s) (θ'.2.prob_pos s) (θ'.2.prob_lt_one s)

omit [DecidableEq S] in
private theorem nonempty_of_valid (θ : ValidParams S d) : Nonempty S :=
  BaumWelch.nonempty_of_valid (toValidHMM θ)

variable (T xs) in
/-- **Each ChromHMM step does not decrease the log-likelihood.** -/
theorem logLik_le_emStep (hx : Rich T xs) (θ : ValidParams S d) :
    logLik (joint T) xs θ ≤ logLik (joint T) xs (emStep T xs hx θ) := by
  have := nonempty_of_valid θ
  exact logLik_le_of_emQ_le (fun θ x z => joint_pos θ x z) xs (emQ_le_emStep T xs hx θ θ)

variable (T xs) in
/-- **The log-likelihood is monotone along the ChromHMM iterates.** -/
theorem logLik_iterate_emStep_monotone (hx : Rich T xs) (θ₀ : ValidParams S d) :
    Monotone fun k => logLik (joint T) xs ((emStep T xs hx)^[k] θ₀) := by
  have := nonempty_of_valid θ₀
  exact logLik_iterate_monotone (fun θ x z => joint_pos θ x z) xs
    (fun θ => emQ_le_emStep T xs hx θ θ) θ₀

variable (T xs) in
omit [DecidableEq S] in
/-- The EM log-likelihood is the sum of the HMM log-likelihoods of the sequences. -/
theorem logLik_eq (θ : ValidParams S d) :
    logLik (joint T) xs θ = ∑ n, log (likelihood θ.1.toHMM (xs n) T) := rfl

end Cslib.Bioinformatics.Regulatory.ChromHMM
