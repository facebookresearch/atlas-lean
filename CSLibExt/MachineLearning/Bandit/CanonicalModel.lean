/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Stochastic k-armed bandits: the canonical bandit model

A stochastic `k`-armed bandit is a family `ν = (P_i)` of reward laws on `ℝ`, indexed by the arms
`i : Fin k`, each a probability measure (`StochasticBandit k`); the bandit has finite means when
each reward law has a finite first moment (`StochasticBandit.HasFiniteMeans`). A policy
is a sequence of Markov kernels from histories to arms (`Policy k`), where a history of length `t`
is a tuple `(a_1, x_1, …, a_t, x_t)` of arms and rewards (`History k t`). The canonical bandit
model is the law `canonicalLaw ν π n` of the history of `n` rounds of interaction, obtained by
alternately drawing an arm from the policy given the history so far and a reward from the chosen
arm's law. The pull counts `pullCount i h` and the regret `regret ν π n` are defined on it.

## Main definitions

* `History k t`: the histories of `t` rounds, `Fin t → Fin k × ℝ`.
* `StochasticBandit k`: a reward law, a probability measure on `ℝ`, for each of the `k` arms; the
  predicate `HasFiniteMeans` (every reward law has a finite first moment), the means `mean` and
  the largest mean `maxMean`.
* `Policy k`: a sequence of probability kernels from histories to arms.
* `canonicalLaw ν π n`: the canonical bandit model, a probability measure on `(Fin k × ℝ)^n`.
* `pullCount i h`: the number of rounds of the history `h` in which arm `i` is chosen.
* `regret ν π n`: `n μ*` minus the expected total reward under the canonical bandit model.

## Main statements

* `canonicalLaw` is a probability measure, and its image under the restriction to the first `m`
  rounds is `canonicalLaw ν π m` (`map_take_canonicalLaw`).
* `map_take_action_canonicalLaw`, `map_take_action_reward_canonicalLaw`: the joint law of the
  history before a round and the arm chosen in that round is the composition-product of the law
  of that history with the policy's kernel, and the joint law of these and the reward of the round
  is the composition-product of the former with the chosen arm's reward law.
* `map_eq_canonicalLaw_iff`: random variables `A_1, X_1, …, A_n, X_n` on a probability space have
  the law `canonicalLaw ν π n` if and only if, at every round, the conditional distribution of the
  arm given the past is the policy's kernel and that of the reward given the past and the arm is
  the arm's reward law (Lattimore and Szepesvári, conditions (a) and (b) of Section 4.6 and
  Proposition 4.8). `eq_canonicalLaw_iff` is the same characterization for a measure on the
  histories, with the conditions written as equalities of joint laws.
* `sum_pullCount`: the pull counts of the arms sum to the number of rounds.
* `integrable_reward`, `integral_reward`: for a bandit with finite means, each reward is
  integrable under the canonical bandit model, and its expectation is the expected mean of the
  chosen arm; so the integral in `regret` is the expectation of the total reward, and
  `regret_nonneg` follows.

## Conventions

Arms are indexed by `Fin k`: the arm `i ∈ {1, …, k}` of the source is stored as `i - 1`. Rounds
are counted from `0` too: for a history `h : History k n` and `t : Fin n`, the coordinate `h t`
holds round `t + 1`, the pair `(A_{t+1} - 1, X_{t+1})` in the source's notation, and
`π.kernel t` is the source's kernel `π_{t+1}`, which reads a history of length `t`. A policy is a
sequence over all rounds, so the same policy runs for every horizon. The horizon `n = 0` is
allowed: its canonical law is the point mass at the empty history. The reward kernel
`ν.rewardKernel t` maps a history of length `t` and an arm `a` to the law of `a`; the history is
an unused argument, so that it composes with the policy's kernel. The pull count `T_i(t)` of the
source at an earlier round `t ≤ n` is `pullCount a (Fin.take t _ h)` for the stored arm
`a = i - 1`.

As in the source's Section 4.1, a stochastic bandit is only a family of probability measures: the
model, the canonical law and its characterization make no moment assumption. The source assumes
finite means from Section 4.4 on, where it defines the regret; here that assumption is the
predicate `HasFiniteMeans`, a hypothesis of the results about means and the regret. The
definitions `mean`, `maxMean` and `regret` are total: `mean` is a Bochner integral, which is `0`
for a non-integrable function, `maxMean` is the largest value of `mean`, and `regret` combines
`maxMean` with a Bochner integral under the canonical law, so they are the source's quantities
under `HasFiniteMeans`.

## Construction and proof outline

* `canonicalLaw ν π (n + 1)` is the image of
  `(canonicalLaw ν π n ⊗ₘ π.kernel n) ⊗ₘ ν.rewardKernel n` under appending the new arm and reward
  to the history: the Ionescu-Tulcea construction for a finite horizon, unrolled as a recursion.
  It is a probability measure because each kernel is Markov.
* Restricting the appended history to its first `m ≤ n` rounds forgets the new round, and the
  first marginal of a composition-product with a Markov kernel is the first measure; induction on
  `n` gives the marginal property and the joint laws above.
* For the characterization, Mathlib's `condDistrib_ae_eq_iff_measure_eq_compProd` turns
  conditions (a) and (b) into equalities of joint laws with composition-products. The canonical
  law satisfies them; conversely, by induction on `m`, they determine the law of the first `m`
  rounds, since the history of `m + 1` rounds is the history of `m` rounds with the arm and the
  reward of round `m + 1` appended.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 4.1 (stochastic bandits), Section 4.4 (the means and the regret), Section 4.5 (the pull
  counts), Section 4.6 (policies as probability kernels, conditions (a) and (b), Proposition 4.8
  and the canonical bandit model) and Section 4.7 (the bandit as a probability kernel, and the
  canonical bandit model as the product of the kernels `π_1, P_1, …, π_n, P_n` by the
  Ionescu-Tulcea theorem).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Cslib.MachineLearning.Bandit

/-- A history of `t` rounds of a `k`-armed bandit: the arms chosen and the rewards received,
`(a_1, x_1, …, a_t, x_t)`, as a map `Fin t → Fin k × ℝ`. Rounds and arms are counted from `0`:
the arm `a ∈ {1, …, k}` is stored as `a - 1`, and the coordinate `s` holds round `s + 1`, the pair
`(a_{s+1} - 1, x_{s+1})`. It carries the `t`-fold product of the σ-algebra on arm–reward pairs,
the product of the discrete σ-algebra on the arms and the Borel σ-algebra on `ℝ`. -/
abbrev History (k t : ℕ) : Type := Fin t → Fin k × ℝ

/-- A stochastic `k`-armed bandit `ν = (P_1, …, P_k)`: for each arm, a probability measure on `ℝ`,
its reward law. No moment assumption is made; the means and the regret are about bandits with
finite means (`StochasticBandit.HasFiniteMeans`). The arms are indexed by `Fin k`, so the arm `i`
of the source is `i - 1` here. -/
structure StochasticBandit (k : ℕ) where
  /-- The reward law of each arm. -/
  law : Fin k → Measure ℝ
  /-- Each reward law is a probability measure. -/
  isProbabilityMeasure_law (i : Fin k) : IsProbabilityMeasure (law i)

attribute [instance] StochasticBandit.isProbabilityMeasure_law

/-- A policy for `k` arms: a sequence `(π_t)` of probability kernels from the histories of the
earlier rounds to the arms, measurable in the history. The sequence runs over all rounds, so the
same policy serves every horizon. Rounds and arms are counted from `0`, the arm `i ∈ {1, …, k}`
being stored as `i - 1`: the kernel `π.kernel t` maps a history of `t` rounds to the law of the
arm chosen in the next round, and it is the source's `π_{t+1}`. -/
structure Policy (k : ℕ) where
  /-- The kernel of round `t + 1`, from the histories of `t` rounds to the arms. -/
  kernel (t : ℕ) : Kernel (History k t) (Fin k)
  /-- Each kernel maps every history to a probability measure on the arms. -/
  isMarkovKernel_kernel (t : ℕ) : IsMarkovKernel (kernel t)

attribute [instance] Policy.isMarkovKernel_kernel

namespace StochasticBandit

variable {k : ℕ} (ν : StochasticBandit k)

/-- A stochastic bandit `ν = (P_1, …, P_k)` has finite means when every reward law has a finite
first moment, `∫ |x| dP_i(x) < ∞`, so that the mean `μ_i = ∫ x dP_i(x)` of each arm is defined. -/
def HasFiniteMeans : Prop := ∀ i, Integrable (fun x : ℝ ↦ x) (ν.law i)

/-- The mean `μ_i = ∫ x dP_i(x)` of the reward law of arm `i`, as a Bochner integral. It is the
mean of `P_i` when `P_i` has a finite first moment (as under `HasFiniteMeans`), and `0` otherwise,
the value of the Bochner integral of a non-integrable function. -/
noncomputable def mean (i : Fin k) : ℝ := ∫ x, x ∂ν.law i

/-- The largest mean `μ* = max_i μ_i` of a stochastic bandit with `k ≥ 1` arms, the largest value
of `mean`, in which an arm whose reward law has no finite first moment has mean `0` by convention.
When the bandit has finite means (`HasFiniteMeans`), it is the largest mean of the reward laws. -/
noncomputable def maxMean [NeZero k] : ℝ := univ.sup' univ_nonempty ν.mean

theorem mean_le_maxMean [NeZero k] (i : Fin k) : ν.mean i ≤ ν.maxMean :=
  le_sup' ν.mean (mem_univ i)

theorem exists_mean_eq_maxMean [NeZero k] : ∃ i, ν.mean i = ν.maxMean := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty ν.mean
  exact ⟨i, hi.symm⟩

/-- The reward laws of a stochastic bandit as a probability kernel from the arms to `ℝ`: it maps
arm `i` to its reward law `P_i`. -/
noncomputable def armKernel : Kernel (Fin k) ℝ := Kernel.ofFunOfCountable ν.law

@[simp]
theorem armKernel_apply (i : Fin k) : ν.armKernel i = ν.law i := rfl

instance : IsMarkovKernel ν.armKernel := ⟨fun i ↦ by rw [armKernel_apply]; infer_instance⟩

/-- The reward kernel of round `t + 1`: the probability kernel that maps a history of `t` rounds
and an arm `a` to the reward law `P_a` of `a`, whatever the history. -/
noncomputable def rewardKernel (t : ℕ) : Kernel (History k t × Fin k) ℝ :=
  Kernel.prodMkLeft (History k t) ν.armKernel

@[simp]
theorem rewardKernel_apply (t : ℕ) (p : History k t × Fin k) :
    ν.rewardKernel t p = ν.law p.2 := rfl

instance (t : ℕ) : IsMarkovKernel (ν.rewardKernel t) := by
  unfold rewardKernel; infer_instance

end StochasticBandit

section Measurability

variable {k : ℕ}

theorem History.measurable_take {n : ℕ} (m : ℕ) (hm : m ≤ n) :
    Measurable (Fin.take m hm : History k n → History k m) :=
  measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _

theorem History.measurable_snoc (t : ℕ) :
    Measurable (fun p : (History k t × Fin k) × ℝ ↦
      (Fin.snoc p.1.1 (p.1.2, p.2) : History k (t + 1))) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  induction i using Fin.lastCases with
  | last => simpa using measurable_fst.snd.prodMk measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst.fst

/- The history before round `t` (counted from zero) and the arm chosen in it. -/
theorem History.measurable_take_action {n : ℕ} (t : Fin n) :
    Measurable (fun h : History k n ↦ (Fin.take t t.isLt.le h, (h t).1)) :=
  (History.measurable_take _ _).prodMk (measurable_pi_apply _).fst

/- The history before round `t` (counted from zero), the arm chosen in it and its reward. -/
theorem History.measurable_take_action_reward {n : ℕ} (t : Fin n) :
    Measurable (fun h : History k n ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2)) :=
  (History.measurable_take_action t).prodMk (measurable_pi_apply _).snd

private theorem measurable_init (t : ℕ) :
    Measurable (fun h : History k (t + 1) ↦ (Fin.init h : History k t)) :=
  measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _

end Measurability

variable {k : ℕ} (ν : StochasticBandit k) (π : Policy k)

/-- **Canonical bandit model.** Fix `k` arms and a horizon `n`. A stochastic `k`-armed bandit
`ν = (P_1, …, P_k)` (`StochasticBandit k`) is a family of probability measures on `ℝ`, one for each
arm. A policy `π` (`Policy k`) is a sequence of probability kernels
`π_t` from histories `(a_1, x_1, …, a_{t-1}, x_{t-1})` to arms, measurable in the history. The
canonical bandit model `canonicalLaw ν π n` is the probability law `ℙ_{ν,π}` on
`({1, …, k} × ℝ)^n` of the history `(A_1, X_1, …, A_n, X_n)` obtained by alternately applying
`π_t` to the history so far, which gives the law of the arm `A_t`, and the reward law `P_{A_t}`
of the chosen arm, which gives the law of the reward `X_t`. For `n = 0` it is the point mass at
the empty history. In Lean, arms and rounds are counted from `0`: the arm `i` is stored as
`i - 1`, the coordinate `t : Fin n` of a history holds round `t + 1`, the pair
`(A_{t+1} - 1, X_{t+1})`, and `π.kernel t` is `π_{t+1}`. -/
noncomputable def canonicalLaw : (n : ℕ) → Measure (History k n)
  | 0 => Measure.dirac default
  | n + 1 => (((canonicalLaw n) ⊗ₘ π.kernel n) ⊗ₘ ν.rewardKernel n).map
      fun p ↦ Fin.snoc p.1.1 (p.1.2, p.2)

@[simp]
theorem canonicalLaw_zero : canonicalLaw ν π 0 = Measure.dirac default := rfl

theorem canonicalLaw_succ (n : ℕ) :
    canonicalLaw ν π (n + 1) =
      ((canonicalLaw ν π n ⊗ₘ π.kernel n) ⊗ₘ ν.rewardKernel n).map
        fun p ↦ Fin.snoc p.1.1 (p.1.2, p.2) := rfl

instance isProbabilityMeasure_canonicalLaw (n : ℕ) :
    IsProbabilityMeasure (canonicalLaw ν π n) := by
  induction n with
  | zero => rw [canonicalLaw_zero]; infer_instance
  | succ n ih => rw [canonicalLaw_succ]; infer_instance

section Marginals

/- Restricting a history to its first `m` rounds forgets a round appended after them. -/
private theorem take_snoc {n m : ℕ} (hm : m ≤ n) (h : History k n) (x : Fin k × ℝ) :
    Fin.take m (hm.trans n.le_succ) (Fin.snoc h x : History k (n + 1)) = Fin.take m hm h := by
  rw [← Fin.take_init m hm, Fin.init_snoc]

private theorem take_self {n : ℕ} : (Fin.take n le_rfl : History k n → History k n) = id :=
  funext Fin.take_eq_self

private theorem map_fst_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).map Prod.fst = μ :=
  Measure.fst_compProd μ κ

/- The image of the canonical law of `n` rounds under the restriction to the first `m ≤ n`
rounds is the canonical law of `m` rounds. -/
theorem map_take_canonicalLaw {n m : ℕ} (hm : m ≤ n) :
    (canonicalLaw ν π n).map (Fin.take m hm) = canonicalLaw ν π m := by
  induction n with
  | zero =>
    obtain rfl := Nat.le_zero.1 hm
    rw [take_self, Measure.map_id]
  | succ n ih =>
    rcases Nat.of_le_succ hm with hm' | rfl
    · have key : (Fin.take m hm ∘ fun p : (History k n × Fin k) × ℝ ↦
          (Fin.snoc p.1.1 (p.1.2, p.2) : History k (n + 1))) =
          Fin.take m hm' ∘ (Prod.fst ∘ Prod.fst) := by
        funext p
        exact take_snoc hm' _ _
      rw [canonicalLaw_succ,
        Measure.map_map (History.measurable_take _ _) (History.measurable_snoc n), key,
        ← Measure.map_map (History.measurable_take _ _) (measurable_fst.comp measurable_fst),
        ← Measure.map_map measurable_fst measurable_fst, map_fst_compProd, map_fst_compProd, ih]
    · rw [take_self, Measure.map_id]

/- Under the canonical law of `n` rounds, the joint law of the history of the rounds before `t`,
the arm chosen at round `t` and the reward of round `t` (counted from zero) is the
composition-product of the joint law of the first two, `canonicalLaw ν π t ⊗ₘ π.kernel t`, with
the reward kernel, which gives the reward the law of the chosen arm. -/
theorem map_take_action_reward_canonicalLaw {n : ℕ} (t : Fin n) :
    (canonicalLaw ν π n).map (fun h ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2)) =
      (canonicalLaw ν π t ⊗ₘ π.kernel t) ⊗ₘ ν.rewardKernel t := by
  have hg : Measurable (fun h : History k (t + 1) ↦
      ((Fin.init h, (h (Fin.last t)).1), (h (Fin.last t)).2)) :=
    ((measurable_init t).prodMk (measurable_pi_apply _).fst).prodMk (measurable_pi_apply _).snd
  have key : (fun h : History k n ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2)) =
      (fun h : History k (t + 1) ↦ ((Fin.init h, (h (Fin.last t)).1), (h (Fin.last t)).2)) ∘
        Fin.take (t + 1) t.isLt := by
    funext h
    refine Prod.ext (Prod.ext (funext fun i ↦ ?_) ?_) ?_
    · simp [Fin.take_apply, Fin.init]
    · rfl
    · rfl
  have key' : (fun h : History k (t + 1) ↦
      ((Fin.init h, (h (Fin.last t)).1), (h (Fin.last t)).2)) ∘
      (fun p : (History k t × Fin k) × ℝ ↦ (Fin.snoc p.1.1 (p.1.2, p.2) : History k (t + 1))) =
      id := by
    funext p
    simp
  rw [key, ← Measure.map_map hg (History.measurable_take _ _), map_take_canonicalLaw,
    canonicalLaw_succ, Measure.map_map hg (History.measurable_snoc _), key', Measure.map_id]

/- Under the canonical law of `n` rounds, the joint law of the history of the rounds before `t`
and of the arm chosen at round `t` (counted from zero) is the composition-product of the
canonical law of `t` rounds with the policy's kernel `π.kernel t`: the first marginal of the
joint law above. -/
theorem map_take_action_canonicalLaw {n : ℕ} (t : Fin n) :
    (canonicalLaw ν π n).map (fun h ↦ (Fin.take t t.isLt.le h, (h t).1)) =
      canonicalLaw ν π t ⊗ₘ π.kernel t := by
  have key : (fun h : History k n ↦ (Fin.take t t.isLt.le h, (h t).1)) =
      Prod.fst ∘ fun h : History k n ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2) := rfl
  rw [key, ← Measure.map_map measurable_fst (History.measurable_take_action_reward t),
    map_take_action_reward_canonicalLaw, map_fst_compProd]

end Marginals

section Characterization

/- Two probability measures on the histories of zero rounds are equal: there is only one such
history. -/
private theorem eq_of_isProbabilityMeasure_zero (μ μ' : Measure (History k 0))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] : μ = μ' := by
  ext s -
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · rw [show s = Set.univ from Set.eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx]
    simp

/- A probability measure `μ` on the histories of `n` rounds is the canonical law if and only if,
at every round `t` (counted from zero), the joint law of the history of the earlier rounds and
the arm chosen at round `t` is the composition-product of the law of that history with the
policy's kernel `π.kernel t`, and the joint law of these and the reward of round `t` is the
composition-product of their joint law with the reward kernel `ν.rewardKernel t`. -/
theorem eq_canonicalLaw_iff {n : ℕ} (μ : Measure (History k n)) [IsProbabilityMeasure μ] :
    μ = canonicalLaw ν π n ↔ ∀ t : Fin n,
      μ.map (fun h ↦ (Fin.take t t.isLt.le h, (h t).1)) =
          μ.map (Fin.take t t.isLt.le) ⊗ₘ π.kernel t ∧
        μ.map (fun h ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2)) =
          μ.map (fun h ↦ (Fin.take t t.isLt.le h, (h t).1)) ⊗ₘ ν.rewardKernel t := by
  constructor
  · rintro rfl t
    rw [map_take_action_reward_canonicalLaw, map_take_action_canonicalLaw,
      map_take_canonicalLaw]
    exact ⟨rfl, rfl⟩
  · intro hμ
    suffices ∀ m (hm : m ≤ n), μ.map (Fin.take m hm) = canonicalLaw ν π m by
      simpa [take_self, Measure.map_id] using this n le_rfl
    intro m hm
    induction m with
    | zero => exact eq_of_isProbabilityMeasure_zero _ _
    | succ m ih =>
      have key : (Fin.take (m + 1) hm : History k n → History k (m + 1)) =
          (fun p : (History k m × Fin k) × ℝ ↦ (Fin.snoc p.1.1 (p.1.2, p.2) : History k (m + 1))) ∘
            (fun h ↦ ((Fin.take m (Nat.le_of_succ_le hm) h, (h ⟨m, hm⟩).1), (h ⟨m, hm⟩).2)) := by
        funext h
        exact Fin.take_succ_eq_snoc m hm h
      obtain ⟨ha, hb⟩ := hμ ⟨m, hm⟩
      rw [key, ← Measure.map_map (History.measurable_snoc m)
        (History.measurable_take_action_reward ⟨m, hm⟩), hb, ha, ih (Nat.le_of_succ_le hm),
        canonicalLaw_succ]

/-- **Characterization of the canonical bandit model** (Lattimore and Szepesvári, Section 4.6,
conditions (a) and (b) and Proposition 4.8). Fix `k ≥ 1` arms, a horizon `n`, a stochastic
bandit `ν = (P_1, …, P_k)` and a policy `π = (π_t)`. Let `H = (A_1, X_1, …, A_n, X_n)` be a
measurable map from a probability space `(Ω, P)` to the histories of `n` rounds. Then the law of
`H` under `P` is the canonical law `canonicalLaw ν π n` if and only if, for every round `t`,
(a) the conditional distribution of the arm `A_t` given `A_1, X_1, …, A_{t-1}, X_{t-1}` is
`π_t(· | A_1, X_1, …, A_{t-1}, X_{t-1})` almost surely, and (b) the conditional distribution of
the reward `X_t` given `A_1, X_1, …, A_{t-1}, X_{t-1}, A_t` is `P_{A_t}` almost surely. In
particular, any two probability spaces carrying such random variables give them the same law.
In Lean, arms and rounds are counted from `0`: the arm `i` is stored as `i - 1`, the coordinate
`t : Fin n` of `H` is `(A_{t+1} - 1, X_{t+1})`, the history before it is `Fin.take t _ H`, and
conditional distributions are Mathlib's `condDistrib`. -/
theorem map_eq_canonicalLaw_iff [NeZero k] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} {H : Ω → History k n} (hH : Measurable H) :
    P.map H = canonicalLaw ν π n ↔ ∀ t : Fin n,
      condDistrib (fun ω ↦ (H ω t).1) (fun ω ↦ Fin.take t t.isLt.le (H ω)) P
          =ᵐ[P.map fun ω ↦ Fin.take t t.isLt.le (H ω)] π.kernel t ∧
        condDistrib (fun ω ↦ (H ω t).2) (fun ω ↦ (Fin.take t t.isLt.le (H ω), (H ω t).1)) P
          =ᵐ[P.map fun ω ↦ (Fin.take t t.isLt.le (H ω), (H ω t).1)] ν.rewardKernel t := by
  rw [eq_canonicalLaw_iff]
  refine forall_congr' fun t ↦ ?_
  have hX : Measurable (Fin.take t t.isLt.le : History k n → History k t) :=
    History.measurable_take _ _
  have hA : Measurable (fun h : History k n ↦ (h t).1) := (measurable_pi_apply t).fst
  have hR : Measurable (fun h : History k n ↦ (h t).2) := (measurable_pi_apply t).snd
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (X := fun ω ↦ Fin.take t t.isLt.le (H ω))
      (Y := fun ω ↦ (H ω t).1) (hX.comp hH).aemeasurable (hA.comp hH).aemeasurable,
    condDistrib_ae_eq_iff_measure_eq_compProd
      (X := fun ω ↦ (Fin.take t t.isLt.le (H ω), (H ω t).1)) (Y := fun ω ↦ (H ω t).2)
      ((History.measurable_take_action t).comp hH).aemeasurable (hR.comp hH).aemeasurable,
    Measure.map_map hX hH, Measure.map_map (History.measurable_take_action t) hH,
    Measure.map_map (History.measurable_take_action_reward t) hH]
  rfl

end Characterization

section PullCount

/-- The pull count `T_i(n) = #{t ≤ n : A_t = i}` of arm `i` in a history `(A_1, X_1, …, A_n, X_n)`
of `n` rounds: the number of rounds in which arm `i` is chosen. On the canonical bandit model it
is a random variable, as the arms `A_t` are the coordinates of the history. -/
def pullCount {n : ℕ} (i : Fin k) (h : History k n) : ℕ :=
  #{t | (h t).1 = i}

theorem pullCount_eq_sum {n : ℕ} (i : Fin k) (h : History k n) :
    pullCount i h = ∑ t, if (h t).1 = i then 1 else 0 :=
  card_filter _ _

theorem pullCount_le {n : ℕ} (i : Fin k) (h : History k n) : pullCount i h ≤ n :=
  (card_filter_le _ _).trans (by simp)

/- The pull counts of the arms sum to the number of rounds: `∑ i, T_i(n) = n`. -/
theorem sum_pullCount {n : ℕ} (h : History k n) : ∑ i, pullCount i h = n := by
  simpa [pullCount] using (card_eq_sum_card_fiberwise (f := fun t ↦ (h t).1) (s := univ)
    (t := univ) fun _ _ ↦ mem_univ _).symm

theorem pullCount_snoc {t : ℕ} (i : Fin k) (h : History k t) (a : Fin k) (x : ℝ) :
    pullCount i (Fin.snoc h (a, x) : History k (t + 1)) =
      pullCount i h + if a = i then 1 else 0 := by
  rw [pullCount_eq_sum, pullCount_eq_sum, Fin.sum_univ_castSucc]
  simp

theorem measurable_pullCount {n : ℕ} (i : Fin k) :
    Measurable (pullCount i : History k n → ℕ) := by
  rw [show (pullCount i : History k n → ℕ) = fun h ↦ ∑ t, if (h t).1 = i then 1 else 0 from
    funext (pullCount_eq_sum i)]
  exact Finset.measurable_sum _ fun t _ ↦
    Measurable.ite ((measurable_pi_apply t).fst (measurableSet_singleton i)) measurable_const
      measurable_const

end PullCount

section Regret

/- For a bandit with finite means, the reward of round `t + 1` is integrable under the joint law
of a history of `t` rounds, the next arm and the next reward: the reward laws have finite first
moments and there are finitely many arms. -/
private theorem integrable_snd_compProd (hν : ν.HasFiniteMeans) {t : ℕ}
    (μ : Measure (History k t × Fin k)) [IsFiniteMeasure μ] :
    Integrable (fun p : (History k t × Fin k) × ℝ ↦ p.2) (μ ⊗ₘ ν.rewardKernel t) := by
  rw [Measure.integrable_compProd_iff measurable_snd.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun q ↦ hν q.2, ?_⟩
  refine (integrable_const (∑ i, ∫ y, ‖y‖ ∂ν.law i)).mono'
    ((measurable_of_countable fun i ↦ ∫ y, ‖y‖ ∂ν.law i).comp
      measurable_snd).aestronglyMeasurable (ae_of_all _ fun q ↦ ?_)
  change ‖∫ y, ‖y‖ ∂ν.law q.2‖ ≤ ∑ i, ∫ y, ‖y‖ ∂ν.law i
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  exact single_le_sum (f := fun i ↦ ∫ y, ‖y‖ ∂ν.law i)
    (fun i _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) (mem_univ q.2)

/- For a bandit with finite means, the reward `X_t` of each round is integrable under the
canonical law. -/
theorem integrable_reward (hν : ν.HasFiniteMeans) {n : ℕ} (t : Fin n) :
    Integrable (fun h ↦ (h t).2) (canonicalLaw ν π n) := by
  have hint := integrable_snd_compProd ν hν (canonicalLaw ν π t ⊗ₘ π.kernel t)
  rw [← map_take_action_reward_canonicalLaw] at hint
  exact (integrable_map_measure measurable_snd.aestronglyMeasurable
    (History.measurable_take_action_reward t).aemeasurable).1 hint

/- Under any finite measure on histories, the mean of the arm chosen in a round is integrable:
it takes finitely many values. -/
theorem integrable_mean_action {n : ℕ} (μ : Measure (History k n)) [IsFiniteMeasure μ]
    (t : Fin n) : Integrable (fun h ↦ ν.mean (h t).1) μ :=
  (integrable_const (∑ i, |ν.mean i|)).mono'
    ((measurable_of_countable ν.mean).comp (measurable_pi_apply t).fst).aestronglyMeasurable
    (ae_of_all _ fun h ↦ single_le_sum (f := fun i ↦ |ν.mean i|) (fun _ _ ↦ abs_nonneg _)
      (mem_univ (h t).1))

/- For a bandit with finite means, the expected reward of each round under the canonical law is
the expected mean of the arm chosen in that round: `𝔼[X_t] = 𝔼[μ_{A_t}]`. -/
theorem integral_reward (hν : ν.HasFiniteMeans) {n : ℕ} (t : Fin n) :
    ∫ h, (h t).2 ∂canonicalLaw ν π n = ∫ h, ν.mean (h t).1 ∂canonicalLaw ν π n := by
  calc ∫ h, (h t).2 ∂canonicalLaw ν π n
      = ∫ p, p.2 ∂(canonicalLaw ν π n).map
          (fun h ↦ ((Fin.take t t.isLt.le h, (h t).1), (h t).2)) :=
        (integral_map (History.measurable_take_action_reward t).aemeasurable
          measurable_snd.aestronglyMeasurable).symm
    _ = ∫ p, p.2 ∂(canonicalLaw ν π t ⊗ₘ π.kernel t) ⊗ₘ ν.rewardKernel t := by
        rw [map_take_action_reward_canonicalLaw]
    _ = ∫ q, ν.mean q.2 ∂(canonicalLaw ν π t ⊗ₘ π.kernel t) :=
        Measure.integral_compProd (integrable_snd_compProd ν hν _)
    _ = ∫ q, ν.mean q.2 ∂(canonicalLaw ν π n).map
          (fun h ↦ (Fin.take t t.isLt.le h, (h t).1)) := by
        rw [map_take_action_canonicalLaw]
    _ = ∫ h, ν.mean (h t).1 ∂canonicalLaw ν π n :=
        integral_map (History.measurable_take_action t).aemeasurable
          ((measurable_of_countable ν.mean).comp measurable_snd).aestronglyMeasurable

/-- The regret `R_n = n μ* - 𝔼_{ν,π}[∑_{t ≤ n} X_t]` of a policy `π` on a stochastic bandit `ν`
with `k ≥ 1` arms over `n` rounds, where `μ_i = ∫ x dP_i(x)` is the mean of arm `i`,
`μ* = max_i μ_i` is the largest mean, and the expectation is the integral under the canonical
bandit model `ℙ_{ν,π} = canonicalLaw ν π n`. When the bandit has finite means
(`HasFiniteMeans`), each reward `X_t` is integrable under `ℙ_{ν,π}` (`integrable_reward`) and
this is the source's regret. Otherwise the definition still gives a number: a Bochner integral of
a non-integrable function is `0`, both in the means and in the expectation. -/
noncomputable def regret [NeZero k] (n : ℕ) : ℝ :=
  n * ν.maxMean - ∫ h, ∑ t, (h t).2 ∂canonicalLaw ν π n

/-- The regret of every policy `π` on every stochastic bandit `ν` with `k ≥ 1` arms and finite
means is nonnegative: `R_n ≥ 0` for every horizon `n` (Lattimore and Szepesvári, Lemma 4.4 (a)). -/
theorem regret_nonneg [NeZero k] (hν : ν.HasFiniteMeans) (n : ℕ) : 0 ≤ regret ν π n := by
  rw [regret, integral_finsetSum _ fun t _ ↦ integrable_reward ν π hν t, sub_nonneg]
  calc ∑ t, ∫ h, (h t).2 ∂canonicalLaw ν π n
      = ∑ t : Fin n, ∫ h, ν.mean (h t).1 ∂canonicalLaw ν π n :=
        sum_congr rfl fun t _ ↦ integral_reward ν π hν t
    _ ≤ ∑ _t : Fin n, ν.maxMean := sum_le_sum fun t _ ↦ by
        simpa using integral_mono (integrable_mean_action ν (canonicalLaw ν π n) t)
          (integrable_const ν.maxMean) fun h ↦ ν.mean_le_maxMean (h t).1
    _ = n * ν.maxMean := by simp

end Regret

end Cslib.MachineLearning.Bandit
