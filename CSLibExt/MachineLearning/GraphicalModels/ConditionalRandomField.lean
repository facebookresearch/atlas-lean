/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Linear-chain conditional random fields: forward algorithm and Viterbi

A linear-chain conditional random field (Lafferty, McCallum, and Pereira, *Conditional random
fields: Probabilistic models for segmenting and labeling sequence data*, ICML 2001; Sutton and
McCallum, *An introduction to conditional random fields*, FNT-ML 2012) models the conditional
distribution `p(y | x)` of a label sequence `y` given an input sequence `x` directly, as a
normalized product of position-dependent potentials. Unlike a hidden Markov model
(`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`), whose potentials are
position-independent and normalize per transition, a CRF's potentials may depend on the whole
input at each position and need only normalize globally, over all label sequences.

A chain CRF has states `S`, inputs `O`, and weights in `R` (typically
`ℝ` or `ℚ`): unary potentials `unary x t s` and transition potentials `trans x t s s'`, each
taking the whole observation sequence `x`, so edge features may depend jointly on the two
states, the full input, and the position. The
`logScore` of a label path is the sum of the log-potentials; here we work with the potentials
themselves. The log-linear parametrization `unary = exp (∑ wₖ fₖ)`, `trans = exp (∑ wₖ gₖ)`
is the special case obtained by instantiating the potentials with exponentials.
`pathWeight t z` is the unnormalized weight of a label path `z : Fin (t + 1) → S` given the
whole observation stream `x` (as in the standard definition, `p(y | x)` conditions on the
entire observation sequence, not just its prefix), `partition t` is the total weight of
all paths, and
`condProb t z = pathWeight t z / partition t` is the conditional probability of the path.

Main results:

* `forward_eq`: the forward variables are the path weights ending in each state;
  `partition_eq_sum_forward`: **the forward algorithm computes the partition function**.
* `pathWeight_le_viterbi`, `exists_pathWeight_eq_viterbi`: the Viterbi variables are the largest
  path weights ending in each state; `sup'_viterbi_eq`: **Viterbi computes the MAP value**.
* `sum_condProb_eq_one`: under `0 < partition t`, the conditional probabilities sum to `1`.
* `hmmToCRF_pathWeight`: every hidden Markov model embeds as a chain CRF with the same path
  weights, so a CRF generalizes an HMM.
* On `Fin n`, tabulated: `forwardTab`, `partitionTab_eq`; `viterbiTab`, backpointers `back`,
  `bestPath` (`pathWeight_bestPath`), and `crfPath` with `pathWeight_le_crfPath`: **the
  backtracked Viterbi path is a most probable label sequence**.

## Cost model

As in the HMM file: `forwardTab` and `viterbiTab` do `O(n²)` operations per step, `O(t n²)`
in total. The untabulated `forward`, `viterbi`, and `partition` are specifications.
Backtracking (`bestPath` / `crfPath`) recomputes `viterbiTab` from time zero at each level,
so reconstructing a path of length `t + 1` costs `O(t² n²)`, not one `O(t n²)` tabulated
pass; the tables themselves are computed once per `viterbiTab` call.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GraphicalModels.ConditionalRandomField

/-- A linear-chain conditional random field with states `S`, inputs `O`, and weights in `R`:
potentials depending on the whole observation sequence. Nonnegativity is part of the
definition: potentials are (unnormalized) probabilities, so `condProb` is a genuine
conditional probability whenever the partition function is positive. `x : ℕ → O` is
the whole (potentially infinite) observation stream; `pathWeight t` conditions on all
of `x`, as `p(y | x)` does in the standard definition. -/
structure ChainCRF (S O R : Type*) [Zero R] [LE R] where
  /-- The unary potential of a state at a position, as a function of the whole
  observation sequence. -/
  unary : (ℕ → O) → ℕ → S → R
  /-- The transition potential from the first state to the second at a step, as a function
  of the whole observation sequence (so edge features may depend jointly on the two
  states, the full input, and the position). -/
  trans : (ℕ → O) → ℕ → S → S → R
  /-- Unary potentials are nonnegative. -/
  unary_nonneg : ∀ (x : ℕ → O) (t : ℕ) (s : S), 0 ≤ unary x t s
  /-- Transition potentials are nonnegative. -/
  trans_nonneg : ∀ (x : ℕ → O) (t : ℕ) (s s' : S), 0 ≤ trans x t s s'

section Forward

variable {S O R : Type*} [Semiring R] [LE R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- The unnormalized weight of a label path `z` of length `t + 1` given the whole
observation stream `x`. -/
def pathWeight : (t : ℕ) → (Fin (t + 1) → S) → R
  | 0, z => c.unary x 0 (z 0)
  | t + 1, z => pathWeight t (Fin.init z) * c.trans x t (z (Fin.last t).castSucc)
      (z (Fin.last (t + 1))) * c.unary x (t + 1) (z (Fin.last (t + 1)))

/-- The partition function: the total weight of all label paths. -/
def partition (t : ℕ) : R := ∑ z : Fin (t + 1) → S, pathWeight c x t z

/-- The forward variables: `forward t s` is the total weight of the label paths of length
`t + 1` ending in `s`. -/
def forward : ℕ → S → R
  | 0, s => c.unary x 0 s
  | t + 1, s => (∑ s', forward t s' * c.trans x t s' s) * c.unary x (t + 1) s

omit [Fintype S] in
theorem pathWeight_snoc (t : ℕ) (z : Fin (t + 1) → S) (s : S) :
    pathWeight c x (t + 1) (Fin.snoc z s) = pathWeight c x t z * c.trans x t (z (Fin.last t)) s *
      c.unary x (t + 1) s := by
  simp [pathWeight, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]

/-- **The forward variables are path weights**: `forward t s` is the total weight of the paths
of length `t + 1` ending in `s`. -/
theorem forward_eq [DecidableEq S] : ∀ (t : ℕ) (s : S),
    forward c x t s = ∑ z : Fin (t + 1) → S,
      if z (Fin.last t) = s then pathWeight c x t z else 0
  | 0, s => by
      rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
      simp [forward, pathWeight, Fin.last]
  | t + 1, s => by
      rw [Cslib.MachineLearning.Sequence.HiddenMarkov.sum_snoc]
      simp only [Fin.snoc_last, pathWeight_snoc, forward, forward_eq t]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
      simp

/-- **The forward algorithm computes the partition function**:
`partition t = ∑ s, forward t s`. -/
theorem partition_eq_sum_forward (t : ℕ) :
    partition c x t = ∑ s, forward c x t s := by
  classical
  simp only [forward_eq, partition]
  rw [Finset.sum_comm]
  simp

end Forward

/-! ## Viterbi -/

section Viterbi

variable {S O R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable [Fintype S] [Nonempty S] (c : ChainCRF S O R) (x : ℕ → O)

/-- The Viterbi variables: `viterbi t s` is the largest weight of a path of length `t + 1`
ending in `s` (`pathWeight_le_viterbi`, `exists_pathWeight_eq_viterbi`). -/
def viterbi : ℕ → S → R
  | 0, s => c.unary x 0 s
  | t + 1, s => Finset.univ.sup' Finset.univ_nonempty
      (fun s' => viterbi t s' * c.trans x t s' s) * c.unary x (t + 1) s

variable {c}

omit [Fintype S] [Nonempty S] in
theorem pathWeight_nonneg :
    ∀ (t : ℕ) (z : Fin (t + 1) → S), 0 ≤ pathWeight c x t z
  | 0, _ => c.unary_nonneg _ _ _
  | t + 1, _ => mul_nonneg
      (mul_nonneg (pathWeight_nonneg t _) (c.trans_nonneg _ _ _ _)) (c.unary_nonneg _ _ _)

omit [Nonempty S] in
theorem partition_nonneg (t : ℕ) : 0 ≤ partition c x t := by
  refine Finset.sum_nonneg fun z _ => pathWeight_nonneg x t z

/-- Every path weighs at most the Viterbi variable of its last state. -/
theorem pathWeight_le_viterbi :
    ∀ (t : ℕ) (z : Fin (t + 1) → S),
      pathWeight c x t z ≤ viterbi c x t (z (Fin.last t))
  | 0, z => le_of_eq (by simp [pathWeight, viterbi, Fin.last])
  | t + 1, z => by
      simp only [pathWeight, viterbi]
      refine mul_le_mul_of_nonneg_right ?_ (c.unary_nonneg _ _ _)
      refine le_trans
        (mul_le_mul_of_nonneg_right (pathWeight_le_viterbi t _) (c.trans_nonneg _ _ _ _)) ?_
      exact Finset.le_sup' (fun s' => viterbi c x t s' * c.trans x t s' (z (Fin.last (t + 1))))
        (Finset.mem_univ _)

/-- The Viterbi variable is attained by a path ending in that state. -/
theorem exists_pathWeight_eq_viterbi :
    ∀ (t : ℕ) (s : S),
      ∃ z : Fin (t + 1) → S, z (Fin.last t) = s ∧ pathWeight c x t z = viterbi c x t s
  | 0, s => ⟨fun _ => s, rfl, by simp [pathWeight, viterbi]⟩
  | t + 1, s => by
      obtain ⟨s', -, hs'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun s' => viterbi c x t s' * c.trans x t s' s)
      obtain ⟨z, hz, hzv⟩ := exists_pathWeight_eq_viterbi t s'
      refine ⟨Fin.snoc z s, by simp, ?_⟩
      rw [pathWeight_snoc, hz, hzv, viterbi, hs']

/-- **Viterbi computes the MAP value**: the largest weight of a path of length `t + 1` is the
largest Viterbi variable at time `t`. -/
theorem sup'_viterbi_eq (t : ℕ) :
    (Finset.univ : Finset S).sup' Finset.univ_nonempty (viterbi c x t) =
      (Finset.univ : Finset (Fin (t + 1) → S)).sup' Finset.univ_nonempty (pathWeight c x t) := by
  refine le_antisymm (Finset.sup'_le _ _ fun s _ => ?_) (Finset.sup'_le _ _ fun z _ => ?_)
  · obtain ⟨z, -, hz⟩ := exists_pathWeight_eq_viterbi (c := c) x t s
    rw [← hz]
    exact Finset.le_sup' _ (Finset.mem_univ z)
  · exact le_trans (pathWeight_le_viterbi x t z) (Finset.le_sup' _ (Finset.mem_univ _))

end Viterbi

/-! ## Conditional probabilities -/

section Probabilities

variable {S O R : Type*} [Semifield R] [PartialOrder R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- The conditional probability of a label path given the inputs. Division is the
only operation needing a semifield, so `condProb` lives in this section while
`pathWeight` / `partition` / `forward` need only a semiring. -/
def condProb (t : ℕ) (z : Fin (t + 1) → S) : R := pathWeight c x t z / partition c x t

/-- **The conditional probabilities sum to `1`** when the partition function is positive. -/
theorem sum_condProb_eq_one (t : ℕ) (hpos : 0 < partition c x t) :
    ∑ z : Fin (t + 1) → S, condProb c x t z = 1 := by
  simp only [condProb, ← Finset.sum_div]
  rw [show (∑ z : Fin (t + 1) → S, pathWeight c x t z) = partition c x t from rfl]
  exact div_self (ne_of_gt hpos)

end Probabilities

section ProbabilitiesNonneg

variable {S O R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype S] (c : ChainCRF S O R) (x : ℕ → O)

/-- Conditional probabilities are nonnegative (nonnegativity is part of `ChainCRF`). -/
theorem condProb_nonneg (t : ℕ) (z : Fin (t + 1) → S) :
    0 ≤ condProb c x t z :=
  div_nonneg (pathWeight_nonneg x t z) (partition_nonneg x t)

end ProbabilitiesNonneg

/-! ## Every HMM embeds as a CRF -/

section Embedding

variable {S O R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable (h : Cslib.MachineLearning.Sequence.HiddenMarkov.HMM S O R) (x : ℕ → O)

/-- The chain CRF induced by a hidden Markov model with nonnegative weights: unary
potentials absorb the initial and emission weights, transition potentials are the HMM
transitions. -/
def hmmToCRF (hn : h.Nonneg) : ChainCRF S O R where
  unary x t s := if t = 0 then h.init s * h.emit s (x t) else h.emit s (x t)
  trans _x _t s s' := h.trans s s'
  unary_nonneg x t s := by
    by_cases ht : t = 0
    · subst ht
      simp only [ite_true]
      exact mul_nonneg (hn.init _) (hn.emit _ _)
    · simp only [ht, ite_false]
      exact hn.emit _ _
  trans_nonneg _x _t s s' := hn.trans _ _

/-- The embedded CRF has the same path weights as the HMM. -/
theorem hmmToCRF_pathWeight (hn : h.Nonneg) :
    ∀ (t : ℕ) (z : Fin (t + 1) → S),
      pathWeight (hmmToCRF h hn) x t z =
        Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb h x t z
  | 0, z => by simp [pathWeight, Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb, hmmToCRF]
  | t + 1, z => by
      have hz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) :=
        (Fin.snoc_init_self z).symm
      rw [hz, pathWeight_snoc, hmmToCRF_pathWeight hn t]
      simp [Cslib.MachineLearning.Sequence.HiddenMarkov.pathProb, hmmToCRF, Fin.snoc_last,
        Fin.snoc_castSucc]

end Embedding

/-! ## Tabulated algorithms on `Fin n` -/

section Tabulated

variable {O R : Type*} {n : ℕ} (x : ℕ → O)

section ForwardTab

variable [Semiring R] [LE R] (c : ChainCRF (Fin n) O R)

/-- One forward step on a table of the previous step's values. -/
def forwardStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => (∑ s', v[s'] * c.trans x t s' s) * c.unary x (t + 1) s

/-- The forward variables, tabulated step by step: `O(n²)` operations per step. -/
def forwardTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => c.unary x 0 s
  | t + 1 => forwardStep x c (forwardTab t) t

theorem forwardTab_get : ∀ (t : ℕ) (s : Fin n), (forwardTab x c t)[s] = forward c x t s
  | 0, s => by simp [forwardTab, forward]
  | t + 1, s => by simp [forwardTab, forwardStep, forward, forwardTab_get t]

/-- **The tabulated forward algorithm**: the partition function in `O(t n²)` operations. -/
def partitionTab (t : ℕ) : R :=
  Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec (forwardTab x c t)

theorem partitionTab_eq (t : ℕ) : partitionTab x c t = partition c x t := by
  rw [partition_eq_sum_forward, partitionTab,
    Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec]
  exact Finset.sum_congr rfl fun s _ => forwardTab_get x c t s

end ForwardTab

section ViterbiTab

variable [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
variable [NeZero n] (c : ChainCRF (Fin n) O R)

/-- One Viterbi step on a table of the previous step's values. -/
def viterbiStep (v : Vector R n) (t : ℕ) : Vector R n :=
  Vector.ofFn fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun s' => v[s'] * c.trans x t s' s) * c.unary x (t + 1) s

/-- The Viterbi variables, tabulated step by step. -/
def viterbiTab : ℕ → Vector R n
  | 0 => Vector.ofFn fun s => c.unary x 0 s
  | t + 1 => viterbiStep x c (viterbiTab t) t

theorem viterbiTab_get : ∀ (t : ℕ) (s : Fin n), (viterbiTab x c t)[s] = viterbi c x t s
  | 0, s => by simp [viterbiTab, viterbi]
  | t + 1, s => by simp [viterbiTab, viterbiStep, viterbi, viterbiTab_get t]

/-- The backpointer: the best predecessor of `s` at step `t`, given the previous table. -/
def back (t : ℕ) (v : Vector R n) (s : Fin n) : Fin n :=
  Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxFin fun s' => v[s'] * c.trans x t s' s

/-- The best path of length `t + 1` ending in `s`, following the backpointers. -/
def bestPath : (t : ℕ) → Fin n → Fin (t + 1) → Fin n
  | 0, s => fun _ => s
  | t + 1, s => Fin.snoc (bestPath t (back x c t (viterbiTab x c t) s)) s

omit [IsOrderedRing R] in
theorem bestPath_last : ∀ (t : ℕ) (s : Fin n), bestPath x c t s (Fin.last t) = s
  | 0, _ => rfl
  | t + 1, s => by simp [bestPath]

/-- The backtracked path attains the Viterbi variable. -/
theorem pathWeight_bestPath : ∀ (t : ℕ) (s : Fin n),
    pathWeight c x t (bestPath x c t s) = viterbi c x t s
  | 0, s => by simp [bestPath, pathWeight, viterbi]
  | t + 1, s => by
      have hf : (fun s' => (viterbiTab x c t)[s'] * c.trans x t s' s) =
          fun s' => viterbi c x t s' * c.trans x t s' s :=
        funext fun s' => by rw [viterbiTab_get]
      rw [bestPath, pathWeight_snoc, bestPath_last, pathWeight_bestPath t, viterbi,
        Cslib.MachineLearning.Sequence.HiddenMarkov.sup'_eq_argmaxFin, back, hf]

/-- **Viterbi's MAP path**: backtracked from the best final state. -/
def crfPath (t : ℕ) : Fin (t + 1) → Fin n :=
  bestPath x c t
    (Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec (viterbiTab x c t))

/-- **The Viterbi path is a most probable path**: no path weighs more. -/
theorem pathWeight_le_crfPath (t : ℕ) (z : Fin (t + 1) → Fin n) :
    pathWeight c x t z ≤ pathWeight c x t (crfPath x c t) := by
  rw [crfPath, Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec, pathWeight_bestPath]
  refine le_trans (pathWeight_le_viterbi x t z) ?_
  have := Cslib.MachineLearning.Sequence.HiddenMarkov.le_argmaxFin
    (fun s => (viterbiTab x c t)[s]) (z (Fin.last t))
  simpa only [viterbiTab_get] using this

end ViterbiTab

end Tabulated

end Cslib.MachineLearning.GraphicalModels.ConditionalRandomField
