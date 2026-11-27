/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Occam
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# PAC learning k-CNF by elimination (Valiant 1984, Theorem A)

Valiant's first learnable class (L. G. Valiant, *A theory of the learnable*, Comm. ACM 27 (1984),
1134-1142, Section 5, Theorem A) is the class of `k`-CNF expressions over `t` Boolean variables,
for any fixed `k`, learned from positive examples alone. The **elimination algorithm** starts from
the conjunction of all clauses of at most `k` literals and deletes every clause that some positive
example falsifies. Two invariants carry the proof:

* every clause of the target survives, so the hypothesis **never says yes when it should not**
  (`eliminate_imp`, the one-sided error of Valiant's definition);
* the hypothesis is satisfied by every positive example seen (`eval_eliminate_of_mem`).

Here instances are total truth assignments `Fin t → Bool` (Valiant's paper also allows partial
vectors). Valiant bounds the sample size through his Bernoulli-trial function `L(h, S)` of
Section 4; this file instead derives the PAC guarantee from the Occam bound for consistent
learners (`CSLibExt.MachineLearning.PACLearning.Occam`). The elimination learner is a CSLib
`Learner` on labelled samples that is consistent with the `k`-CNF class (`isConsistent_learner`),
so `pi_eliminate_error_gt_le` bounds its failure probability by `2^N (1 - ε)^m`, with `N` the
number of clauses of at most `k` literals, and `isPACLearnable_kcnfClass` states CSLib's
`IsPACLearnable` for the class over its realizable distributions.

## Cost model

None: the statements concern the hypothesis produced, not its running time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning.KCNF

open MeasureTheory
open scoped ENNReal

variable {t : ℕ}

/-- **Literal over `t` Boolean variables.** A literal `(i, b)` is the variable `pᵢ` when
`b = true` and its negation `¬pᵢ` when `b = false` (Valiant, *A theory of the learnable*, Comm.
ACM 27 (1984), Section 5). -/
abbrev Literal (t : ℕ) := Fin t × Bool

/-- **Clause.** A clause is a finite set of literals, read as their disjunction. -/
abbrev Clause (t : ℕ) := Finset (Literal t)

/-- **CNF expression.** A CNF expression is a finite set of clauses, read as their conjunction
(Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), Section 5). -/
abbrev CNF (t : ℕ) := Finset (Clause t)

/-- **Truth of a literal.** A literal `(i, b)` is true at the assignment `x` when `x i = b`. -/
def Literal.Holds (l : Literal t) (x : Fin t → Bool) : Prop := x l.1 = l.2

instance (l : Literal t) (x : Fin t → Bool) : Decidable (l.Holds x) :=
  inferInstanceAs (Decidable (x l.1 = l.2))

/-- **Truth of a clause.** A clause is true at the assignment `x` when one of its literals is. -/
def Clause.Holds (c : Clause t) (x : Fin t → Bool) : Prop := ∃ l ∈ c, l.Holds x

instance (c : Clause t) (x : Fin t → Bool) : Decidable (c.Holds x) :=
  inferInstanceAs (Decidable (∃ l ∈ c, l.Holds x))

/-- **Truth of a CNF expression.** A CNF expression is true at the assignment `x` when all its
clauses are. -/
def CNF.Holds (f : CNF t) (x : Fin t → Bool) : Prop := ∀ c ∈ f, c.Holds x

instance (f : CNF t) (x : Fin t → Bool) : Decidable (f.Holds x) :=
  inferInstanceAs (Decidable (∀ c ∈ f, c.Holds x))

/-- **Boolean function of a CNF expression.** The function `x ↦ [f is true at x]` computed by a
CNF expression `f`. -/
def CNF.toFun (f : CNF t) (x : Fin t → Bool) : Bool := decide (f.Holds x)

/-- **k-CNF expression.** A CNF expression is a `k`-CNF expression when each of its clauses has
at most `k` literals (Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), Section 5). -/
def IsKCNF (k : ℕ) (f : CNF t) : Prop := ∀ c ∈ f, c.card ≤ k

instance (k : ℕ) (f : CNF t) : Decidable (IsKCNF k f) :=
  inferInstanceAs (Decidable (∀ c ∈ f, c.card ≤ k))

/-- **Clauses of at most `k` literals.** The set of all clauses of at most `k` literals over `t`
variables, the initial hypothesis of the elimination algorithm (Valiant, *A theory of the
learnable*, Comm. ACM 27 (1984), Section 5, proof of Theorem A). There are `2t` literals, so no
clause has more than `2t` of them. The set is built as the union, over `j ≤ min k (2t)`, of the
sets of `j` literals, so neither clauses of width above `k` nor widths above `2t` are enumerated;
`mem_allClauses` characterizes its members. -/
def allClauses (t k : ℕ) : CNF t :=
  (Finset.range (min k (2 * t) + 1)).biUnion fun j => Finset.powersetCard j Finset.univ

/-- **Membership in the initial clauses.** A clause over `t` variables is one of the initial
clauses exactly when it has at most `k` literals. -/
@[simp] theorem mem_allClauses {k : ℕ} {c : Clause t} : c ∈ allClauses t k ↔ c.card ≤ k := by
  have hlit : Fintype.card (Literal t) = 2 * t := by
    simp [Literal, Fintype.card_prod, mul_comm]
  have hc : c.card ≤ 2 * t := hlit ▸ Finset.card_le_univ c
  simp only [allClauses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (le_min_iff.1 (Nat.lt_succ_iff.1 hj)).1
  · intro hk
    exact ⟨c.card, Nat.lt_succ_iff.2 (le_min_iff.2 ⟨hk, hc⟩), rfl⟩

/-- **Counting the initial clauses.** There are at most `∑_{j ≤ k} (2t)^j` clauses of at most `k`
literals over `t` variables, since there are `2t` literals and at most `(2t)^j` sets of `j` of them
(Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), Section 5, proof of Theorem A, where
the clauses of one to `k` literals are counted as fewer than `(2t)^{k+1}`). -/
theorem card_allClauses_le (t k : ℕ) :
    (allClauses t k).card ≤ ∑ j ∈ Finset.range (k + 1), (2 * t) ^ j := by
  have hlit : Fintype.card (Literal t) = 2 * t := by
    simp [Literal, Fintype.card_prod, mul_comm]
  calc (allClauses t k).card
      ≤ ∑ j ∈ Finset.range (min k (2 * t) + 1),
          (Finset.powersetCard j (Finset.univ : Finset (Literal t))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (min k (2 * t) + 1), (2 * t) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Finset.card_powersetCard, Finset.card_univ, hlit]
        exact (Nat.choose_le_pow _ _).trans (by simp)
    _ ≤ ∑ j ∈ Finset.range (k + 1), (2 * t) ^ j :=
        Finset.sum_le_sum_of_subset
          (Finset.range_subset_range.2 (Nat.succ_le_succ (min_le_left _ _)))

/-- **Valiant's elimination algorithm for k-CNF.** Given a list of positive examples (truth
assignments at which the target is true), keep exactly the clauses of at most `k` literals that
every example satisfies (Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), Section 5,
proof of Theorem A: "for each `cᵢ` in `g` delete `cᵢ` if `v ⇏ cᵢ`"). -/
def eliminate (k : ℕ) (examples : List (Fin t → Bool)) : CNF t :=
  (allClauses t k).filter fun c => ∀ x ∈ examples, c.Holds x

/-- **The elimination output is a k-CNF expression.** Every clause kept by the elimination
algorithm has at most `k` literals. -/
theorem isKCNF_eliminate (k : ℕ) (examples : List (Fin t → Bool)) :
    IsKCNF k (eliminate k examples) := by
  intro c hc
  simp only [eliminate, Finset.mem_filter] at hc
  exact mem_allClauses.1 hc.1

/-- **The elimination output keeps only initial clauses.** The output of elimination is a
sub-collection of the clauses of at most `k` literals. -/
theorem eliminate_subset_allClauses (k : ℕ) (examples : List (Fin t → Bool)) :
    eliminate k examples ⊆ allClauses t k :=
  Finset.filter_subset _ _

/-- **The elimination output is consistent with the positive examples.** Every example used by
the elimination algorithm satisfies the hypothesis it outputs (Valiant, *A theory of the
learnable*, Comm. ACM 27 (1984), Section 5, proof of Theorem A). -/
theorem eval_eliminate_of_mem (k : ℕ) (examples : List (Fin t → Bool)) {x : Fin t → Bool}
    (hx : x ∈ examples) : (eliminate k examples).Holds x := by
  intro c hc
  simp only [eliminate, Finset.mem_filter] at hc
  exact hc.2 x hx

/-- **The target's clauses are never deleted.** If `f` is a `k`-CNF expression satisfied by every
example, every clause of `f` survives elimination (Valiant, *A theory of the learnable*, Comm. ACM
27 (1984), Section 5, proof of Theorem A: "in the course of the algorithm no clause in `B` can ever
be deleted"). -/
theorem subset_eliminate {k : ℕ} {f : CNF t} (hf : IsKCNF k f) (examples : List (Fin t → Bool))
    (hpos : ∀ x ∈ examples, f.Holds x) : f ⊆ eliminate k examples := by
  intro c hc
  simp only [eliminate, Finset.mem_filter]
  exact ⟨mem_allClauses.2 (hf c hc), fun x hx => hpos x hx c hc⟩

/-- **One-sided error: the elimination hypothesis implies the target.** If `f` is a `k`-CNF
expression satisfied by every example, then at every assignment where the elimination output is
true, `f` is true: the hypothesis "never says yes when it should not" (Valiant, *A theory of the
learnable*, Comm. ACM 27 (1984), Section 3, condition (i), and Section 5, proof of Theorem A). -/
theorem eliminate_imp {k : ℕ} {f : CNF t} (hf : IsKCNF k f) (examples : List (Fin t → Bool))
    (hpos : ∀ x ∈ examples, f.Holds x) {x : Fin t → Bool} (hx : (eliminate k examples).Holds x) :
    f.Holds x :=
  fun c hc => hx c (subset_eliminate hf examples hpos hc)

/-- **Positive examples of a labelled sample.** The instances of a labelled sample that carry the
label `true`, in sample order. -/
def positives {m : ℕ} (S : LabeledSample (Fin t → Bool) Bool m) : List (Fin t → Bool) :=
  ((List.ofFn S).filter fun p => p.2).map Prod.fst

/-- **Membership in the positive examples.** An instance is a positive example of a labelled
sample when the sample contains it with the label `true`. -/
theorem mem_positives {m : ℕ} {S : LabeledSample (Fin t → Bool) Bool m} {x : Fin t → Bool} :
    x ∈ positives S ↔ ∃ i, S i = (x, true) := by
  simp only [positives, List.mem_map, List.mem_filter, List.mem_ofFn]
  constructor
  · rintro ⟨⟨y, b⟩, ⟨⟨i, hi⟩, hb⟩, rfl⟩
    simp only at hb
    exact ⟨i, by rw [hi, hb]⟩
  · rintro ⟨i, hi⟩
    exact ⟨(x, true), ⟨⟨i, hi⟩, rfl⟩, rfl⟩

/-- **The elimination learner.** A CSLib `Learner` on labelled samples: run Valiant's elimination
algorithm on the instances labelled `true` (the positive examples) and output the Boolean function
of the resulting `k`-CNF. It reads the sample only, never the target (Valiant, *A theory of the
learnable*, Comm. ACM 27 (1984), Section 5, proof of Theorem A). -/
def learner (k : ℕ) {m : ℕ} : Learner (Fin t → Bool) Bool m :=
  fun S => (eliminate k (positives S)).toFun

/-- **The class of k-CNF functions.** The hypothesis class of `k`-CNF functions over `t`
variables, as a finite set of Boolean functions: the functions of the sub-collections of the
clauses of at most `k` literals. -/
def kcnfClass (t k : ℕ) : Finset ((Fin t → Bool) → Bool) :=
  (allClauses t k).powerset.image CNF.toFun

/-- **The elimination learner outputs a k-CNF function.** Its output belongs to the class of
`k`-CNF functions. -/
theorem learner_mem_kcnfClass (k : ℕ) {m : ℕ} (S : LabeledSample (Fin t → Bool) Bool m) :
    learner k S ∈ kcnfClass t k :=
  Finset.mem_image.2 ⟨_, Finset.mem_powerset.2 (eliminate_subset_allClauses _ _), rfl⟩

/-- **Size of the k-CNF class.** The class of `k`-CNF functions has at most `2^N` members, `N`
the number of clauses of at most `k` literals. -/
theorem card_kcnfClass_le (t k : ℕ) : (kcnfClass t k).card ≤ 2 ^ (allClauses t k).card :=
  Finset.card_image_le.trans (Finset.card_powerset _).le

/-- **The elimination learner is consistent with the k-CNF class.** On every labelled sample
realizable by a `k`-CNF function, the elimination output is a `k`-CNF function that agrees with
every label (CSLib's `IsConsistent`): it is true at the positive examples, which satisfy it, and
false at the negative examples, because it implies the target (Valiant, *A theory of the
learnable*, Comm. ACM 27 (1984), Section 5, proof of Theorem A). -/
theorem isConsistent_learner (k : ℕ) {m : ℕ} :
    IsConsistent (learner (t := t) k (m := m)) (kcnfClass t k : ConceptClass _ Bool) := by
  rintro S ⟨c, hc, hS⟩
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
  have hfk : IsKCNF k f := by
    intro cl hcl
    exact mem_allClauses.1 (Finset.mem_powerset.1 hf hcl)
  have hpos : ∀ x ∈ positives S, f.Holds x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_positives.1 hx
    have := hS i
    rw [hi] at this
    simpa [CNF.toFun] using this.symm
  refine ⟨learner_mem_kcnfClass k S, fun i => ?_⟩
  have hlab := hS i
  change decide ((eliminate k (positives S)).Holds (S i).1) = (S i).2
  cases hb : (S i).2 with
  | true =>
    have hmem : (S i).1 ∈ positives S := mem_positives.2 ⟨i, by rw [← hb]⟩
    simp [eval_eliminate_of_mem k _ hmem]
  | false =>
    rw [hb] at hlab
    have hnot : ¬ f.Holds (S i).1 := by simpa [CNF.toFun] using hlab.symm
    have : ¬ (eliminate k (positives S)).Holds (S i).1 :=
      fun h => hnot (eliminate_imp hfk _ hpos h)
    simp [this]

/-- Every subset of the finite product `(Fin t → Bool) × Bool` is measurable. -/
theorem measurableSet_disagreement (h : (Fin t → Bool) → Bool) :
    MeasurableSet {p : (Fin t → Bool) × Bool | h p.1 ≠ p.2} :=
  (Set.toFinite _).measurableSet

/-- **k-CNF is PAC learnable by elimination.** Let `D` be any probability distribution on labelled
truth assignments of `t` variables under which some `k`-CNF function has error `0` (the
realizable case). For `m` independent examples from `D`, the probability that the elimination
learner outputs a hypothesis of error greater than `ε` is at most `2^N (1 - ε)^m`, where `N` is
the number of clauses of at most `k` literals, so `N ≤ ∑_{j ≤ k} (2t)^j` by
`card_allClauses_le`. Valiant (*A theory of the learnable*, Comm. ACM 27 (1984), Section 5,
Theorem A) proves learnability of `k`-CNF with `L(h, (2t)^{k+1})` positive examples through his
Bernoulli-trial bound; this statement replaces that argument by the Occam bound for consistent
learners (Blumer, Ehrenfeucht, Haussler and Warmuth, *Occam's razor*, Inform. Process. Lett. 24
(1987), 377-380). -/
theorem pi_eliminate_error_gt_le (D : Measure ((Fin t → Bool) × Bool)) [IsProbabilityMeasure D]
    {k : ℕ} (hD : D ∈ realizableFamily (kcnfClass t k : ConceptClass _ Bool)) (m : ℕ)
    (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D) {S | ε < error D (learner k S)} ≤
      2 ^ (allClauses t k).card * (1 - ε) ^ m := by
  obtain ⟨h, hh, h0⟩ := hD
  refine (pi_consistent_learner_error_gt_le D (kcnfClass t k)
    (fun h _ => measurableSet_disagreement h) ⟨h, hh, h0⟩ (learner k)
    (isConsistent_learner k) ε).trans ?_
  have : ((kcnfClass t k).card : ℝ≥0∞) ≤ 2 ^ (allClauses t k).card := by
    exact_mod_cast card_kcnfClass_le t k
  exact mul_le_mul_left this _

/-- **k-CNF is PAC learnable (Valiant 1984, Theorem A).** For fixed `t` and `k`, the class of
`k`-CNF functions over `t` variables is PAC learnable (CSLib's `IsPACLearnable`) over its
realizable family, by the elimination learner with `⌈log (|kcnfClass| / δ) / ε⌉` examples
(Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), Section 5, Theorem A, without the
running-time bound). -/
theorem isPACLearnable_kcnfClass (t k : ℕ) :
    IsPACLearnable (kcnfClass t k : ConceptClass (Fin t → Bool) Bool)
      (realizableFamily (kcnfClass t k : ConceptClass (Fin t → Bool) Bool)) :=
  isPACLearnable_of_isConsistent (kcnfClass t k) (fun h _ => measurableSet_disagreement h)
    (fun _ => learner k) (fun _ => isConsistent_learner k)

end Cslib.MachineLearning.PACLearning.KCNF
