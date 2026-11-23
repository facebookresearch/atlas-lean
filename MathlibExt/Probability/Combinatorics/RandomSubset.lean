/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli

import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Random subsets of a finite ground set

The basic probability space of probabilistic combinatorics: a random subset `R` of a finite
ground set `α` that contains each element `a` independently with probability `p a`. A subset is
encoded by its indicator `ω : α → Bool`, and the law is the product of Bernoulli laws. The
binomial random graph `G(n, p)` is the case where `α` is the set of pairs of vertices and `p` is
constant.

## Main definitions

* `randomSubsetLaw p`: the law of the random subset, `Measure.pi` of `Ber(true, false, p a)`.
* `containsEvent S`: the event `S ⊆ R` for a finite set `S ⊆ α`.
* `avoidEvent S`: the event `S ∩ R = ∅`.

## Main result

* `randomSubsetLaw_real_containsEvent`: `P(S ⊆ R) = ∏_{a ∈ S} p a`.
* `randomSubsetLaw_real_avoidEvent`: `P(S ∩ R = ∅) = ∏_{a ∈ S} (1 - p a)`.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Setup 7.10 (https://yufeizhao.com/pm/sp19/pmnotes.pdf).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval

namespace MathlibExt.Probability.Combinatorics.RandomSubset

variable {α : Type*}

/-- **Law of a random subset with independent elements.** For `p : α → [0, 1]`, the law on
`α → Bool` (indicators of subsets of `α`) under which the coordinates are independent and the
coordinate `a` is `true` with probability `p a`; that is, the random subset `R` contains each
element `a` independently with probability `p a` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Setup 7.10). -/
noncomputable def randomSubsetLaw [Fintype α] (p : α → I) : Measure (α → Bool) :=
  Measure.pi fun a => bernoulliMeasure true false (p a)

instance [Fintype α] (p : α → I) : IsProbabilityMeasure (randomSubsetLaw p) := by
  unfold randomSubsetLaw; infer_instance

/-- **The event that a random subset contains a given set.** For a finite set `S ⊆ α`, the set
of indicators `ω : α → Bool` with `ω a = true` for every `a ∈ S`, that is, the event `S ⊆ R`
(Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Setup 7.10, the
bad event `Aᵢ`). -/
def containsEvent (S : Finset α) : Set (α → Bool) :=
  {ω | ∀ a ∈ S, ω a = true}

lemma containsEvent_eq_pi (S : Finset α) [DecidablePred (· ∈ S)] :
    containsEvent S = Set.univ.pi (fun a => if a ∈ S then ({true} : Set Bool) else Set.univ) := by
  ext ω
  simp only [containsEvent, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h a
    by_cases ha : a ∈ S
    · simp [ha, h a ha]
    · simp [ha]
  · intro h a ha
    simpa [ha] using h a

lemma measurableSet_containsEvent [Countable α] (S : Finset α) :
    MeasurableSet (containsEvent S) := by
  classical
  rw [containsEvent_eq_pi]
  exact MeasurableSet.univ_pi (fun a => by split_ifs <;> simp)

lemma containsEvent_inter [DecidableEq α] (S T : Finset α) :
    containsEvent S ∩ containsEvent T = containsEvent (S ∪ T) := by
  ext ω
  simp only [containsEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ a (ha | ha)
    exacts [h1 a ha, h2 a ha]
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩

/-- **Probability that a random subset contains a given set.** If `R` contains each element `a`
independently with probability `p a`, then `P(S ⊆ R) = ∏_{a ∈ S} p a` (Y. Zhao, *The
Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Setup 7.10). -/
theorem randomSubsetLaw_real_containsEvent [Fintype α] (p : α → I) (S : Finset α) :
    (randomSubsetLaw p).real (containsEvent S) = ∏ a ∈ S, (p a : ℝ) := by
  classical
  rw [containsEvent_eq_pi, measureReal_def, randomSubsetLaw, Measure.pi_pi,
    ENNReal.toReal_prod, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
  have h1 : ∏ a ∈ Finset.univ.filter (fun a => a ∉ S),
      ((bernoulliMeasure true false (p a))
        (if a ∈ S then ({true} : Set Bool) else Set.univ)).toReal = 1 := by
    refine Finset.prod_eq_one (fun a ha => ?_)
    simp only [Finset.mem_filter] at ha
    simp [ha.2]
  have h2 : ∏ a ∈ Finset.univ.filter (fun a => a ∈ S),
      ((bernoulliMeasure true false (p a))
        (if a ∈ S then ({true} : Set Bool) else Set.univ)).toReal = ∏ a ∈ S, (p a : ℝ) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.prod_congr rfl (fun a ha => ?_)
    simp only [ha, ite_true]
    exact bernoulliMeasure_real_apply_of_mem_of_notMem (p a) (measurableSet_singleton true)
      rfl (by simp)
  rw [h1, h2, mul_one]

/-- **The event that a random subset avoids a given set.** For a finite set `S ⊆ α`, the set of
indicators `ω : α → Bool` with `ω a = false` for every `a ∈ S`, that is, the event
`S ∩ R = ∅` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
proof of Theorem 1.4, where a set of `k` vertices spans no edge of the random colour class). -/
def avoidEvent (S : Finset α) : Set (α → Bool) :=
  {ω | ∀ a ∈ S, ω a = false}

lemma avoidEvent_eq_pi (S : Finset α) [DecidablePred (· ∈ S)] :
    avoidEvent S = Set.univ.pi (fun a => if a ∈ S then ({false} : Set Bool) else Set.univ) := by
  ext ω
  simp only [avoidEvent, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h a
    by_cases ha : a ∈ S
    · simp [ha, h a ha]
    · simp [ha]
  · intro h a ha
    simpa [ha] using h a

/-- **Probability that a random subset avoids a given set.** If `R` contains each element `a`
independently with probability `p a`, then `P(S ∩ R = ∅) = ∏_{a ∈ S} (1 - p a)` (Y. Zhao, *The
Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, proof of Theorem 1.4 for
`p = 1/2`). -/
theorem randomSubsetLaw_real_avoidEvent [Fintype α] (p : α → I) (S : Finset α) :
    (randomSubsetLaw p).real (avoidEvent S) = ∏ a ∈ S, (1 - (p a : ℝ)) := by
  classical
  rw [avoidEvent_eq_pi, measureReal_def, randomSubsetLaw, Measure.pi_pi,
    ENNReal.toReal_prod, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
  have h1 : ∏ a ∈ Finset.univ.filter (fun a => a ∉ S),
      ((bernoulliMeasure true false (p a))
        (if a ∈ S then ({false} : Set Bool) else Set.univ)).toReal = 1 := by
    refine Finset.prod_eq_one (fun a ha => ?_)
    simp only [Finset.mem_filter] at ha
    simp [ha.2]
  have h2 : ∏ a ∈ Finset.univ.filter (fun a => a ∈ S),
      ((bernoulliMeasure true false (p a))
        (if a ∈ S then ({false} : Set Bool) else Set.univ)).toReal =
        ∏ a ∈ S, (1 - (p a : ℝ)) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.prod_congr rfl (fun a ha => ?_)
    simp only [ha, ite_true]
    exact bernoulliMeasure_real_apply_of_notMem_of_mem (p a) (measurableSet_singleton false)
      (by simp) rfl
  rw [h1, h2, mul_one]

end MathlibExt.Probability.Combinatorics.RandomSubset
