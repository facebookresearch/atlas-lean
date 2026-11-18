/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.InteractiveEpistemology.CommonKnowledge
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Order.OrderIsoNat

@[expose] public section

/-! # The agreement theorem and dialogues of posteriors

Aumann's agreement theorem (Aumann 1976): agents with a common prior whose posteriors for an
event are common knowledge have equal posteriors, even though their information may differ.
Agents "cannot agree to disagree".

The state space `Ω` is finite, the common prior is a finite measure `μ` on `Ω` (with
measurable singletons), and agent `i` has information partition `r i : Setoid Ω`. The
posterior of `A` at `ω` is `μ(A ∩ P(ω)) / μ(P(ω))`, where `P(ω) = cell (r i) ω`
(`posterior`; it agrees with Mathlib's conditional probability `μ[A | P(ω)]` by
`posterior_eq_cond`).

## Main results

* `agreement`: for any family of agents, if it is common knowledge at `ω` that the posteriors
  of `A` are `a i`, and the cell of the meet containing `ω` is not null, then all `a i` are
  equal (Aumann 1976, Theorem and Proposition, p. 1236–1237, there on any probability space
  for two agents; here on a finite state space).
* `agreeing_to_disagree`: Aumann's two-agent statement, on a finite state space.
* `geanakoplos_polemarchakis`: if all agents repeatedly announce their posteriors publicly and
  refine their partitions by the announcements, the partitions stop changing after finitely
  many rounds, and from then on all posteriors agree at every state whose meet cell is not
  null. This is a simultaneous-announcement form of the convergence result of Geanakoplos and
  Polemarchakis (1982), whose protocol has the two agents announce in turn.

## References

* R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239.
* J. D. Geanakoplos and H. M. Polemarchakis, "We can't disagree forever", J. Econom. Theory
  28(1) (1982), 192–200 (abstract consulted; the protocol here is a variant, see
  `geanakoplos_polemarchakis`).
-/

namespace MathlibExt.GameTheory.InteractiveEpistemology

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Posterior probability.** The posterior probability of the event `A` at state `ω` for an
agent with information partition `r`: `μ(A ∩ P(ω)) / μ(P(ω))` where `P(ω)` is the agent's cell
containing `ω` (Aumann 1976, p. 1237: "`qᵢ(ω) = p(A ∩ Pᵢ(ω)) / p(Pᵢ(ω))`"). If the cell is
null, Lean's convention `x / 0 = 0` makes the posterior `0`. -/
noncomputable def posterior (r : Setoid Ω) (A : Set Ω) (ω : Ω) : ℝ :=
  μ.real (A ∩ cell r ω) / μ.real (cell r ω)

/-- **One round of public announcement of posteriors.** Every agent announces its current
posterior of `A`; each agent's new partition is its old one refined by the level sets of the
announced profile of posteriors (Geanakoplos and Polemarchakis 1982, in the
simultaneous-announcement form). -/
noncomputable def dialogueStep {ι : Type*} (A : Set Ω) (r : ι → Setoid Ω) : ι → Setoid Ω :=
  fun i => r i ⊓ Setoid.ker fun ω j => posterior μ (r j) A ω

/-- **Dialogue of posteriors.** The information partitions after `n` rounds of
`dialogueStep`, starting from the partitions `r₀`. -/
noncomputable def dialogue {ι : Type*} (A : Set Ω) (r₀ : ι → Setoid Ω) (n : ℕ) :
    ι → Setoid Ω :=
  (dialogueStep μ A)^[n] r₀

theorem dialogue_succ {ι : Type*} (A : Set Ω) (r₀ : ι → Setoid Ω) (n : ℕ) :
    dialogue μ A r₀ (n + 1) = dialogueStep μ A (dialogue μ A r₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- **Partitions only get finer during a dialogue.** -/
theorem dialogue_antitone {ι : Type*} (A : Set Ω) (r₀ : ι → Setoid Ω) :
    Antitone (dialogue μ A r₀) :=
  antitone_nat_of_succ_le fun n i => by
    rw [dialogue_succ]
    exact inf_le_left

section Finite

variable [Finite Ω] [MeasurableSingletonClass Ω]

/-- **Posteriors are conditional probabilities.** On a finite state space, `posterior μ r A ω`
is the real value of Mathlib's conditional probability `μ[A | cell r ω]`. -/
theorem posterior_eq_cond (r : Setoid Ω) (A : Set Ω) (ω : Ω) :
    posterior μ r A ω = (ProbabilityTheory.cond μ (cell r ω) A).toReal := by
  rw [ProbabilityTheory.cond_apply (Set.toFinite _).measurableSet μ, ENNReal.toReal_mul,
    ENNReal.toReal_inv, posterior, Set.inter_comm, div_eq_inv_mul]
  rfl

omit [Finite Ω] in
open Classical in
-- The real measure of a set on a finite space is the sum of the masses of its points.
private theorem measureReal_eq_sum_ite [Fintype Ω] [IsFiniteMeasure μ] (S : Set Ω) :
    μ.real S = ∑ x, if x ∈ S then μ.real {x} else 0 := by
  rw [← Finset.sum_filter, sum_measureReal_singleton]
  congr 1
  ext x
  simp

open Classical in
/-- **The tower step of the agreement theorem.** Let `r` be finer than `s`. If the posterior of
`A` for partition `r` equals `a` throughout the `s`-cell of `ω`, then
`μ(A ∩ S) = a · μ(S)` for that cell `S`. This is the computation "`p(A ∩ Pⱼ) = q₁ p(Pⱼ)` for all
`j`; hence, summing over `j`, `p(A ∩ P) = q₁ p(P)`" of Aumann 1976, p. 1237. No cell needs to
be nonnull: on a null `r`-cell both sides vanish. -/
theorem measureReal_inter_cell_eq_mul [IsFiniteMeasure μ] {r s : Setoid Ω} (hrs : r ≤ s)
    (A : Set Ω) (ω : Ω)
    {a : ℝ} (h : ∀ ω' ∈ cell s ω, posterior μ r A ω' = a) :
    μ.real (A ∩ cell s ω) = a * μ.real (cell s ω) := by
  have := Fintype.ofFinite Ω
  set w : Ω → ℝ := fun x => μ.real {x} with hw
  let f : Ω → ℝ := fun x => if s x ω then (if x ∈ A then w x else 0) - a * w x else 0
  have hsum : ∑ x, f x = 0 := by
    refine sum_eq_zero_of_forall_sum_cell_eq_zero r fun y => ?_
    rw [cellFinset, Finset.sum_filter]
    by_cases hy : s y ω
    · have hpost := h y hy
      have hC : ∑ x, (if r x y then f x else 0) =
          μ.real (A ∩ cell r y) - a * μ.real (cell r y) := by
        rw [measureReal_eq_sum_ite μ (A ∩ cell r y), measureReal_eq_sum_ite μ (cell r y),
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hxy : r x y
        · have hxs : s x ω := s.trans (Setoid.le_def.mp hrs hxy) hy
          by_cases hxA : x ∈ A <;> simp [f, hxy, hxs, hxA, w]
        · simp [hxy]
      rw [hC]
      by_cases h0 : μ.real (cell r y) = 0
      · have : μ.real (A ∩ cell r y) = 0 :=
          le_antisymm (h0 ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
        rw [this, h0]; ring
      · rw [← hpost, posterior, div_mul_cancel₀ _ h0, sub_self]
    · refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hxy : r x y
      · have hxs : ¬ s x ω := fun hxs => hy (s.trans (s.symm (Setoid.le_def.mp hrs hxy)) hxs)
        simp [f, hxy, hxs]
      · simp [hxy]
  have hsplit : ∑ x, f x = μ.real (A ∩ cell s ω) - a * μ.real (cell s ω) := by
    rw [measureReal_eq_sum_ite μ (A ∩ cell s ω), measureReal_eq_sum_ite μ (cell s ω),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hxs : s x ω
    · by_cases hxA : x ∈ A <;> simp [f, hxs, hxA, w]
    · simp [f, hxs]
  linarith

/-- **Agreement theorem** (Aumann 1976, Proposition, p. 1237, for any family of agents). Agents
`i : ι` share the prior `μ` and have information partitions `r i`. If it is common knowledge at
`ω` that each agent's posterior of `A` equals `a i`, and the cell of the meet `⨆ i, r i`
containing `ω` is not null, then `a i = a j` for all `i, j`.

Compared with the source, the two statements are incomparable. Aumann works on an arbitrary
probability space, with two agents whose join (coarsest common refinement) consists of nonnull
events; here the state space is finite. Within finite state spaces the statement is stronger:
any family of agents is allowed, and only the meet cell of `ω` must be nonnull. That extra
generality is stated through the convention that the posterior on a null cell is `0`
(`posterior`, Lean's `x / 0 = 0`): the common-knowledge hypothesis is read with that value. -/
theorem agreement [IsFiniteMeasure μ] {ι : Type*} (r : ι → Setoid Ω) (A : Set Ω) (ω : Ω) (a : ι → ℝ)
    (hck : IsCommonKnowledgeAt r {ω' | ∀ i, posterior μ (r i) A ω' = a i} ω)
    (hM : μ.real (cell (⨆ i, r i) ω) ≠ 0) (i j : ι) : a i = a j := by
  have hi := measureReal_inter_cell_eq_mul μ (le_iSup r i) A ω (a := a i)
    fun ω' h => hck h i
  have hj := measureReal_inter_cell_eq_mul μ (le_iSup r j) A ω (a := a j)
    fun ω' h => hck h j
  exact mul_right_cancel₀ hM (hi.symm.trans hj)

/-- **Agreeing to disagree** (Aumann 1976, Theorem, p. 1236, and Proposition, p. 1237). Two
agents with common prior `μ` and information partitions `r₁`, `r₂`: if at `ω` it is common
knowledge that agent 1's posterior of `A` is `q₁` and agent 2's is `q₂` (the event is
contained in the cell of the meet `r₁ ⊔ r₂` that contains `ω`), and that cell is not null,
then `q₁ = q₂`.

This is Aumann's two-agent theorem on a finite state space; Aumann works on an arbitrary
probability space whose join cells are nonnull, so the statements are incomparable. On finite
spaces Aumann's hypothesis implies the one used here (only the meet cell of `ω` must be nonnull),
which is stated through the convention that the posterior on a null cell is `0`. -/
theorem agreeing_to_disagree [IsFiniteMeasure μ] (r₁ r₂ : Setoid Ω) (A : Set Ω) (ω : Ω) (q₁ q₂ : ℝ)
    (hck : cell (r₁ ⊔ r₂) ω ⊆ {ω' | posterior μ r₁ A ω' = q₁ ∧ posterior μ r₂ A ω' = q₂})
    (hM : μ.real (cell (r₁ ⊔ r₂) ω) ≠ 0) : q₁ = q₂ := by
  have h₁ := measureReal_inter_cell_eq_mul μ (le_sup_left : r₁ ≤ r₁ ⊔ r₂) A ω (a := q₁)
    fun ω' h => (hck h).1
  have h₂ := measureReal_inter_cell_eq_mul μ (le_sup_right : r₂ ≤ r₁ ⊔ r₂) A ω (a := q₂)
    fun ω' h => (hck h).2
  exact mul_right_cancel₀ hM (h₁.symm.trans h₂)

/-- **At a fixed point of the dialogue, posteriors agree.** If one more round of announcements
leaves the partitions `r` unchanged, then every agent's posterior is constant on the cells of
the meet, hence common knowledge, and by the agreement theorem all posteriors coincide at
every state whose meet cell is not null. -/
theorem posterior_eq_of_dialogueStep_eq [IsFiniteMeasure μ] {ι : Type*} (A : Set Ω)
    (r : ι → Setoid Ω)
    (hr : dialogueStep μ A r = r) (ω : Ω) (hM : μ.real (cell (⨆ i, r i) ω) ≠ 0) (i j : ι) :
    posterior μ (r i) A ω = posterior μ (r j) A ω := by
  have hker : ∀ k, r k ≤ Setoid.ker fun ω j => posterior μ (r j) A ω := fun k =>
    (congrFun hr k).symm.le.trans inf_le_right
  have hck := isCommonKnowledgeAt_level_set hker ω
  refine agreement μ r A ω (fun j => posterior μ (r j) A ω) ?_ hM i j
  intro ω' hω' k
  exact congrFun (hck hω') k

/-- **We can't disagree forever** (Geanakoplos and Polemarchakis 1982, main result, in a
simultaneous-announcement form). On a finite state space with a common prior, let finitely many
agents repeatedly announce their posteriors of `A` publicly and refine their information
partitions by the announcements. Then after finitely many rounds `T` the partitions stop
changing, and at round `T` all agents' posteriors of `A` are equal at every state whose meet
cell is not null.

Compared with the source: Geanakoplos and Polemarchakis let two agents announce in turn and
assume finite information partitions; here any finite family announces simultaneously and the
state space is finite. No bound on `T` is claimed. -/
theorem geanakoplos_polemarchakis [IsFiniteMeasure μ] {ι : Type*} [Finite ι] (A : Set Ω)
    (r₀ : ι → Setoid Ω) :
    ∃ T, (∀ n, T ≤ n → dialogue μ A r₀ n = dialogue μ A r₀ T) ∧
      ∀ ω, μ.real (cell (⨆ i, dialogue μ A r₀ T i) ω) ≠ 0 →
        ∀ i j, posterior μ (dialogue μ A r₀ T i) A ω =
          posterior μ (dialogue μ A r₀ T j) A ω := by
  have : Finite (Setoid Ω) :=
    Finite.of_injective (fun r : Setoid Ω => (r : Ω → Ω → Prop))
      fun r s h => Setoid.ext fun a b => iff_of_eq (congrFun (congrFun h a) b)
  obtain ⟨T, hT⟩ := WellFoundedLT.antitone_chain_condition (dialogue_antitone μ A r₀)
  refine ⟨T, fun n hn => (hT n hn).symm, fun ω hM i j => ?_⟩
  have hfix : dialogueStep μ A (dialogue μ A r₀ T) = dialogue μ A r₀ T := by
    rw [← dialogue_succ]
    exact (hT (T + 1) (Nat.le_succ T)).symm
  exact posterior_eq_of_dialogueStep_eq μ A _ hfix ω hM i j

end Finite

end MathlibExt.GameTheory.InteractiveEpistemology
