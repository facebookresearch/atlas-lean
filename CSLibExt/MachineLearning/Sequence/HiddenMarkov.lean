/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Hidden Markov models: the forward algorithm and Viterbi

A hidden Markov model (Rabiner, *A tutorial on hidden Markov models and selected applications in
speech recognition*, Proc. IEEE 77, 1989; Bishop, *Pattern Recognition and Machine Learning*,
Section 13.2) has hidden states `S`, observations `O`, initial weights `init`, transition weights
`trans` and emission weights `emit`. `pathProb t z` is the joint weight of a state path
`z : Fin (t + 1) → S` and the observations `x 0, …, x t`, and `likelihood t` is the total weight
of all paths. The weights live in any semiring for the forward algorithm, which keeps the order of
multiplication along a path (with probabilities in `ℝ` or `ℚ`, `likelihood` is `p(x 0, …, x t)`),
and in a linearly ordered commutative one, nonnegative (`HMM.Nonneg`), for Viterbi.

Main results:

* `forward_eq`: the forward variables are the path sums ending in each state;
  `likelihood_eq_sum_forward`: **the forward algorithm computes the likelihood**.
* `pathProb_le_viterbi`, `exists_pathProb_eq_viterbi`: the Viterbi variables are the largest path
  weights ending in each state; `sup'_viterbi_eq`: **Viterbi computes the MAP value**.
* On `Fin n`, tabulated: `forwardTab`, `likelihoodTab_eq` (`O(t n²)` operations); `viterbiTab`,
  backpointers `back`, `bestPath` (`pathProb_bestPath`), and `viterbiPath` (via `argmaxVec`) with
  `pathProb_le_viterbiPath`: **the backtracked Viterbi path is a most probable path**.

## Cost model

The cost is the number of semiring operations. `forwardTab` and `viterbiTab` do `O(n²)` per step,
`O(t n²)` in total (each step takes the previous table as an argument, so no value is
recomputed). `bestPath` recomputes the table at each backtracking step, `O(t² n²)` in total; a
single forward pass storing the backpointers would give `O(t n²)`. The untabulated `forward`,
`viterbi` and `likelihood` are specifications: evaluating them directly takes exponential time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.HiddenMarkov

variable {S O R : Type*}

/-- A hidden Markov model with states `S`, observations `O` and weights in `R`: initial weights,
transition weights and emission weights. -/
structure HMM (S O R : Type*) where
  /-- The initial weight of each state. -/
  init : S → R
  /-- The weight of a transition from the first state to the second. -/
  trans : S → S → R
  /-- The weight of emitting an observation from a state. -/
  emit : S → O → R

section Forward

variable [Fintype S] [Semiring R] (h : HMM S O R) (x : ℕ → O)

/-- The joint weight of a state path `z` of length `t + 1` and the observations `x 0, …, x t`:
`init (z 0) emit (z 0) (x 0) ∏ trans (z (i - 1)) (z i) emit (z i) (x i)`. -/
def pathProb : (t : ℕ) → (Fin (t + 1) → S) → R
  | 0, z => h.init (z 0) * h.emit (z 0) (x 0)
  | t + 1, z => pathProb t (Fin.init z) * h.trans (z (Fin.last t).castSucc) (z (Fin.last (t + 1))) *
      h.emit (z (Fin.last (t + 1))) (x (t + 1))

/-- The likelihood of the observations `x 0, …, x t`: the total weight of all state paths. -/
def likelihood (t : ℕ) : R := ∑ z : Fin (t + 1) → S, pathProb h x t z

/-- The forward variables: `forward t s` is the weight of the observations up to time `t` with
the state at time `t` equal to `s`. -/
def forward : ℕ → S → R
  | 0, s => h.init s * h.emit s (x 0)
  | t + 1, s => (∑ s', forward t s' * h.trans s' s) * h.emit s (x (t + 1))

omit [Fintype S] in
theorem pathProb_snoc (t : ℕ) (z : Fin (t + 1) → S) (s : S) :
    pathProb h x (t + 1) (Fin.snoc z s) = pathProb h x t z * h.trans (z (Fin.last t)) s *
      h.emit s (x (t + 1)) := by
  simp [pathProb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]

theorem sum_snoc {M : Type*} [AddCommMonoid M] {t : ℕ} (f : (Fin (t + 2) → S) → M) :
    ∑ z, f z = ∑ z : Fin (t + 1) → S, ∑ s, f (Fin.snoc z s) := by
  rw [← (Fin.snocEquiv fun _ => S).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- **The forward variables are path sums**: `forward t s` is the total weight of the paths of
length `t + 1` ending in `s`. -/
theorem forward_eq [DecidableEq S] : ∀ (t : ℕ) (s : S),
    forward h x t s = ∑ z : Fin (t + 1) → S, if z (Fin.last t) = s then pathProb h x t z else 0
  | 0, s => by
      rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
      simp [forward, pathProb, Fin.last]
  | t + 1, s => by
      rw [sum_snoc]
      simp only [Fin.snoc_last, pathProb_snoc, forward, forward_eq t]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
      simp

/-- **The forward algorithm computes the likelihood**: `likelihood t = ∑ s, forward t s`. -/
theorem likelihood_eq_sum_forward (t : ℕ) :
    likelihood h x t = ∑ s, forward h x t s := by
  classical
  simp only [forward_eq, likelihood]
  rw [Finset.sum_comm]
  simp

end Forward

/-! ## Viterbi -/

section Viterbi

variable [Fintype S] [Nonempty S] [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
  (h : HMM S O R) (x : ℕ → O)

/-- The Viterbi variables: `viterbi t s` is the largest weight of a path of length `t + 1` ending
in `s` (`pathProb_le_viterbi`, `exists_pathProb_eq_viterbi`). -/
def viterbi : ℕ → S → R
  | 0, s => h.init s * h.emit s (x 0)
  | t + 1, s => Finset.univ.sup' Finset.univ_nonempty (fun s' => viterbi t s' * h.trans s' s) *
      h.emit s (x (t + 1))

/-- Nonnegative weights. -/
structure HMM.Nonneg (h : HMM S O R) : Prop where
  /-- Initial weights are nonnegative. -/
  init : ∀ s, 0 ≤ h.init s
  /-- Transition weights are nonnegative. -/
  trans : ∀ s s', 0 ≤ h.trans s s'
  /-- Emission weights are nonnegative. -/
  emit : ∀ s o, 0 ≤ h.emit s o

variable {h}

omit [Fintype S] [Nonempty S] in
theorem pathProb_nonneg (hn : h.Nonneg) : ∀ (t : ℕ) (z : Fin (t + 1) → S), 0 ≤ pathProb h x t z
  | 0, _ => mul_nonneg (hn.init _) (hn.emit _ _)
  | t + 1, _ => mul_nonneg (mul_nonneg (pathProb_nonneg hn t _) (hn.trans _ _)) (hn.emit _ _)

/-- Every path weighs at most the Viterbi variable of its last state. -/
theorem pathProb_le_viterbi (hn : h.Nonneg) :
    ∀ (t : ℕ) (z : Fin (t + 1) → S), pathProb h x t z ≤ viterbi h x t (z (Fin.last t))
  | 0, z => le_of_eq (by simp [pathProb, viterbi, Fin.last])
  | t + 1, z => by
      simp only [pathProb, viterbi]
      refine mul_le_mul_of_nonneg_right ?_ (hn.emit _ _)
      refine le_trans (mul_le_mul_of_nonneg_right (pathProb_le_viterbi hn t _) (hn.trans _ _)) ?_
      exact Finset.le_sup' (fun s' => viterbi h x t s' * h.trans s' (z (Fin.last (t + 1))))
        (Finset.mem_univ _)

omit [IsOrderedRing R] in
/-- The Viterbi variable is attained by a path ending in that state. -/
theorem exists_pathProb_eq_viterbi :
    ∀ (t : ℕ) (s : S),
      ∃ z : Fin (t + 1) → S, z (Fin.last t) = s ∧ pathProb h x t z = viterbi h x t s
  | 0, s => ⟨fun _ => s, rfl, by simp [pathProb, viterbi]⟩
  | t + 1, s => by
      obtain ⟨s', -, hs'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun s' => viterbi h x t s' * h.trans s' s)
      obtain ⟨z, hz, hzv⟩ := exists_pathProb_eq_viterbi t s'
      refine ⟨Fin.snoc z s, by simp, ?_⟩
      rw [pathProb_snoc, hz, hzv, viterbi, hs']

/-- **Viterbi computes the MAP value**: the largest weight of a path of length `t + 1` is the
largest Viterbi variable at time `t`. -/
theorem sup'_viterbi_eq (hn : h.Nonneg) (t : ℕ) :
    (Finset.univ : Finset S).sup' Finset.univ_nonempty (viterbi h x t) =
      (Finset.univ : Finset (Fin (t + 1) → S)).sup' Finset.univ_nonempty (pathProb h x t) := by
  refine le_antisymm (Finset.sup'_le _ _ fun s _ => ?_) (Finset.sup'_le _ _ fun z _ => ?_)
  · obtain ⟨z, -, hz⟩ := exists_pathProb_eq_viterbi (h := h) x t s
    rw [← hz]
    exact Finset.le_sup' _ (Finset.mem_univ z)
  · exact le_trans (pathProb_le_viterbi x hn t z) (Finset.le_sup' _ (Finset.mem_univ _))

end Viterbi

/-! ## Tabulated algorithms on `Fin n` -/

section Tabulated

variable {n : ℕ} (x : ℕ → O)

/-- The sum of a table's entries (the table is passed as an argument, so it is computed once). -/
def sumVec [AddCommMonoid R] (v : Vector R n) : R := ∑ s : Fin n, v[s]

section ForwardTab

variable [Semiring R] (h : HMM (Fin n) O R)

/-- One forward step on a table of the previous step's values. -/
def forwardStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => (∑ s', v[s'] * h.trans s' s) * h.emit s (x (t + 1))

/-- The forward variables, tabulated step by step: `O(n²)` operations per step. -/
def forwardTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => h.init s * h.emit s (x 0)
  | t + 1 => forwardStep x h (forwardTab t) t

theorem forwardTab_get : ∀ (t : ℕ) (s : Fin n), (forwardTab x h t)[s] = forward h x t s
  | 0, s => by simp [forwardTab, forward]
  | t + 1, s => by simp [forwardTab, forwardStep, forward, forwardTab_get t]

/-- **The tabulated forward algorithm**: the likelihood in `O(t n²)` operations. -/
def likelihoodTab (t : ℕ) : R := sumVec (forwardTab x h t)

theorem likelihoodTab_eq (t : ℕ) : likelihoodTab x h t = likelihood h x t := by
  rw [likelihood_eq_sum_forward, likelihoodTab, sumVec]
  exact Finset.sum_congr rfl fun s _ => forwardTab_get x h t s

end ForwardTab

section ViterbiTab

variable [NeZero n] [CommSemiring R] [LinearOrder R] [IsOrderedRing R] (h : HMM (Fin n) O R)

omit [IsOrderedRing R] in
/-- A maximizer over `Fin n` (the first one). -/
def argmaxFin (f : Fin n → R) : Fin n := ((List.finRange n).argmax f).getD 0

omit [CommSemiring R] [IsOrderedRing R] in
theorem le_argmaxFin (f : Fin n → R) (i : Fin n) : f i ≤ f (argmaxFin f) := by
  unfold argmaxFin
  cases hm : (List.finRange n).argmax f with
  | none =>
      rw [List.argmax_eq_none] at hm
      exact absurd hm (List.ne_nil_of_mem (List.mem_finRange (0 : Fin n)))
  | some m => exact List.le_of_mem_argmax (List.mem_finRange i) hm

omit [CommSemiring R] [IsOrderedRing R] in
theorem sup'_eq_argmaxFin (f : Fin n → R) :
    Finset.univ.sup' Finset.univ_nonempty f = f (argmaxFin f) :=
  le_antisymm (Finset.sup'_le _ _ fun i _ => le_argmaxFin f i)
    (Finset.le_sup' f (Finset.mem_univ _))

/-- One Viterbi step on a table of the previous step's values. -/
def viterbiStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => Finset.univ.sup' Finset.univ_nonempty (fun s' => v[s'] * h.trans s' s) *
    h.emit s (x (t + 1))

/-- The Viterbi variables, tabulated step by step. -/
def viterbiTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => h.init s * h.emit s (x 0)
  | t + 1 => viterbiStep x h (viterbiTab t) t

omit [IsOrderedRing R] in
theorem viterbiTab_get : ∀ (t : ℕ) (s : Fin n), (viterbiTab x h t)[s] = viterbi h x t s
  | 0, s => by simp [viterbiTab, viterbi]
  | t + 1, s => by simp [viterbiTab, viterbiStep, viterbi, viterbiTab_get t]

/-- The backpointer: the best predecessor of `s`, given the previous step's table. -/
def back (v : Vector R n) (s : Fin n) : Fin n := argmaxFin fun s' => v[s'] * h.trans s' s

/-- The best path of length `t + 1` ending in `s`, following the backpointers. -/
def bestPath : (t : ℕ) → Fin n → Fin (t + 1) → Fin n
  | 0, s => fun _ => s
  | t + 1, s => Fin.snoc (bestPath t (back h (viterbiTab x h t) s)) s

omit [IsOrderedRing R] in
theorem bestPath_last : ∀ (t : ℕ) (s : Fin n), bestPath x h t s (Fin.last t) = s
  | 0, _ => rfl
  | t + 1, s => by simp [bestPath]

omit [IsOrderedRing R] in
/-- The backtracked path attains the Viterbi variable. -/
theorem pathProb_bestPath : ∀ (t : ℕ) (s : Fin n),
    pathProb h x t (bestPath x h t s) = viterbi h x t s
  | 0, s => by simp [bestPath, pathProb, viterbi]
  | t + 1, s => by
      have hf : (fun s' => (viterbiTab x h t)[s'] * h.trans s' s) =
          fun s' => viterbi h x t s' * h.trans s' s := funext fun s' => by rw [viterbiTab_get]
      rw [bestPath, pathProb_snoc, bestPath_last, pathProb_bestPath t, viterbi,
        sup'_eq_argmaxFin, back, hf]

omit [CommSemiring R] [IsOrderedRing R] in
/-- A maximizing entry of a table (the table is passed as an argument, so it is computed once). -/
def argmaxVec (v : Vector R n) : Fin n := argmaxFin fun s => v[s]

/-- **Viterbi's MAP path**: backtracked from the best final state. -/
def viterbiPath (t : ℕ) : Fin (t + 1) → Fin n :=
  bestPath x h t (argmaxVec (viterbiTab x h t))

/-- **The Viterbi path is a most probable path**: no path weighs more. -/
theorem pathProb_le_viterbiPath (hn : h.Nonneg) (t : ℕ) (z : Fin (t + 1) → Fin n) :
    pathProb h x t z ≤ pathProb h x t (viterbiPath x h t) := by
  rw [viterbiPath, argmaxVec, pathProb_bestPath]
  refine le_trans (pathProb_le_viterbi x hn t z) ?_
  have := le_argmaxFin (fun s => (viterbiTab x h t)[s]) (z (Fin.last t))
  simpa only [viterbiTab_get] using this

end ViterbiTab

end Tabulated

end Cslib.MachineLearning.Sequence.HiddenMarkov
