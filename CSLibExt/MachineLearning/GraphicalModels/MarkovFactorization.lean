/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket

/-!
# Markov laws factorize: the ordered Markov property is equivalent to factorization

Fix parent sets `pa k ⊆ {0, …, k - 1}` of a directed acyclic graph whose nodes `0, …, n - 1`
are listed in a topological order. A law `P` on `Fin n → α` (finite `α`) has the *ordered Markov
property* (O) if every node `k` is conditionally independent of its predecessors that are not
its parents, given its parents. It *factorizes* (F) if it is the joint law of a Bayesian network
on these parent sets, `P(x) = ∏ k p_k(x_k | x_{pa k})`. The two are equivalent for every law,
with no positivity assumption (Lauritzen, *Markov properties for directed graphs*, 2009, where
(F) is equivalent to the directed Markov properties (O), (L) and (G)); this is what makes a
Bayesian network a faithful encoding of the conditional independencies "every variable depends
on its predecessors only through its parents".

## Main definitions

* `parentSet pa k`: the parents of node `k`, as nodes of `Fin n`.
* `OrderedMarkov P pa`: the ordered Markov property of the law `P` for the parent sets `pa`.

## Main results

* `orderedMarkov_joint`: (F) ⇒ (O), from the local Markov property `BayesNet.condIndep_localMarkov`
  and decomposition.
* `exists_bayesNet_of_orderedMarkov`: (O) ⇒ (F): a law with the ordered Markov property is the
  joint of a Bayesian network on the same parent sets, whose table at `k` is the conditional
  law of `X_k` given its parents.
* `orderedMarkov_iff_exists_bayesNet`: the equivalence.

## References

* S. L. Lauritzen, *Markov properties for directed graphs*, Graphical Models lecture notes,
  University of Oxford (2009).
* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.1,
  eq. (2).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

variable {α : Type*} {n : ℕ}

/-- **Parents as nodes.** The parents of node `k`, embedded in `Fin n`. -/
def parentSet (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) : Finset (Fin n) :=
  (pa k).map (Fin.castLEEmb k.2.le)

/-- **Non-parent predecessors.** The nodes before `k` in the order that are not parents of
`k`. -/
def nonParentPred (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) : Finset (Fin n) :=
  univ.filter fun j => j < k ∧ j ∉ parentSet pa k

/-- **Ordered Markov property of a law** (Lauritzen 2009, property (O)): every node is
conditionally independent of its non-parent predecessors given its parents. Like `CondIndep`, in
terms of which it is stated, it is defined for an arbitrary weight function `P`; it is the
property of a law when `P` is nonnegative with total mass `1`, the hypotheses of the results
below that read it so. For the zero weight it holds for every choice of parents. -/
def OrderedMarkov [Fintype α] (P : (Fin n → α) → ℝ) (pa : (k : Fin n) → Finset (Fin k)) : Prop :=
  ∀ k, CondIndep P ↑({k} : Finset (Fin n)) ↑(nonParentPred pa k) ↑(parentSet pa k)

/-- **Membership in the parent set.** A node `i` is in `parentSet pa k` exactly when it comes
before `k` and is listed among the parents of `k`. -/
theorem mem_parentSet {pa : (k : Fin n) → Finset (Fin k)} {k i : Fin n} :
    i ∈ parentSet pa k ↔ ∃ h : i.val < k.val, (⟨i.val, h⟩ : Fin k) ∈ pa k := by
  simp only [parentSet, mem_map, Fin.castLEEmb_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, by simpa [Fin.castLE] using hj⟩
  · rintro ⟨h, hmem⟩
    exact ⟨_, hmem, Fin.ext rfl⟩

/-- **Parents come first.** Every parent of `k` comes before `k` in the order. -/
theorem lt_of_mem_parentSet {pa : (k : Fin n) → Finset (Fin k)} {k i : Fin n}
    (h : i ∈ parentSet pa k) : i < k := by
  obtain ⟨h, -⟩ := mem_parentSet.1 h
  exact h

/-- **Factorizing laws have the ordered Markov property** ((F) ⇒ (O)). -/
theorem orderedMarkov_joint [Fintype α] [Nonempty α] (b : BayesNet α n) :
    OrderedMarkov b.joint b.pa := by
  classical
  intro k
  have hl := b.condIndep_localMarkov k
  set B := univ.filter fun j => ¬b.IsDescendant k j ∧ ¬b.Edge j k
  have eK : ({k} : Set (Fin n)) = ↑({k} : Finset (Fin n)) := by simp
  have eB : {j | ¬b.IsDescendant k j ∧ ¬b.Edge j k} = (↑B : Set (Fin n)) := by ext j; simp [B]
  have ePa : {j | b.Edge j k} = (↑(parentSet b.pa k) : Set (Fin n)) := by
    ext j
    simp only [Set.mem_ofPred_eq, mem_coe, mem_parentSet]
    rfl
  rw [eK, eB, ePa] at hl
  have hsub : nonParentPred b.pa k ⊆ B := by
    intro j hj
    simp only [nonParentPred, mem_filter, mem_univ, true_and] at hj
    simp only [B, mem_filter, mem_univ, true_and]
    refine ⟨fun hd => absurd hd.le (not_le.2 hj.1), fun he => hj.2 ?_⟩
    exact mem_parentSet.2 he
  have hdisj : Disjoint B {k} := by
    rw [disjoint_singleton_right]
    intro hk
    simp only [B, mem_filter, mem_univ, true_and] at hk
    exact hk.1 .refl
  exact condIndep_symm (condIndep_mono_left (condIndep_symm hl) hsub hdisj)

section Factorization

variable [Nonempty α]

/-- **Extension of parent values.** An assignment with prescribed values `z` on the parents of
`k` (and arbitrary elsewhere). -/
noncomputable def extendPa (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) (z : pa k → α) :
    Fin n → α :=
  fun i => if h : ∃ hi : i.val < k.val, (⟨i.val, hi⟩ : Fin k) ∈ pa k then
    z ⟨⟨i.val, h.1⟩, h.2⟩ else Classical.arbitrary α

/-- **The extension has the prescribed parent values.** -/
theorem extendPa_apply_castLE (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) (z : pa k → α)
    (j : pa k) : extendPa pa k z (Fin.castLE k.2.le j) = z j := by
  have h : ∃ hi : (Fin.castLE k.2.le j.1).val < k.val,
      (⟨(Fin.castLE k.2.le j.1).val, hi⟩ : Fin k) ∈ pa k := ⟨j.1.2, by simp [Fin.castLE]⟩
  simp only [extendPa, h, dite_true]
  rfl

/-- **The conditional law of a node given its parents.** For a law `P`, the table at node `k`
and parent values `z`: `a ↦ P(X_k = a, X_{pa k} = z) / P(X_{pa k} = z)` (any law where the
denominator vanishes). -/
noncomputable def condTable [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) (z : pa k → α) : StdSimplex ℝ α :=
  if h : marginal P ↑(parentSet pa k) (extendPa pa k z) = 0 then
    StdSimplex.single (Classical.arbitrary α)
  else
    { weights := Finsupp.equivFunOnFinite.symm fun a =>
        marginal P ↑(insert k (parentSet pa k)) (Function.update (extendPa pa k z) k a) /
          marginal P ↑(parentSet pa k) (extendPa pa k z)
      nonneg := fun a => by
        simpa using div_nonneg (marginal_nonneg hP _ _) (marginal_nonneg hP _ _)
      total := by
        rw [Finsupp.sum_fintype _ _ fun _ => rfl]
        simp only [Finsupp.coe_equivFunOnFinite_symm, ← sum_div]
        have hk : k ∉ parentSet pa k := fun hk => lt_irrefl _ (lt_of_mem_parentSet hk)
        rw [← marginal_eq_sum_insert P hk, div_self h] }

/-- **The network of conditional tables of a law.** The Bayesian network on the parent sets
`pa` whose table at each node is the conditional law of that node given its parents. -/
noncomputable def condNet [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (pa : (k : Fin n) → Finset (Fin k)) : BayesNet α n where
  pa := pa
  cpt := condTable P hP pa

/-- **The table of `k` at the parents' values of `x` is the conditional law.** Where
`P(X_{pa k} = x_{pa k}) ≠ 0`, `condTable` evaluated at `x_k` is
`P(X_k = x_k, X_{pa k} = x_{pa k}) / P(X_{pa k} = x_{pa k})`. -/
theorem condTable_weights [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (pa : (k : Fin n) → Finset (Fin k)) (k : Fin n) (x : Fin n → α)
    (h : marginal P ↑(parentSet pa k) x ≠ 0) :
    (condTable P hP pa k fun j => x (Fin.castLE k.2.le j)).weights (x k) =
      marginal P ↑(insert k (parentSet pa k)) x / marginal P ↑(parentSet pa k) x := by
  classical
  have hkPa : k ∉ parentSet pa k := fun hk => lt_irrefl _ (lt_of_mem_parentSet hk)
  have hext : ∀ i ∈ parentSet pa k,
      extendPa pa k (fun j => x (Fin.castLE k.2.le j)) i = x i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_map.1 hi
    exact extendPa_apply_castLE pa k _ ⟨j, hj⟩
  have hden : marginal P ↑(parentSet pa k) (extendPa pa k fun j => x (Fin.castLE k.2.le j)) =
      marginal P ↑(parentSet pa k) x := marginal_congr_of_eqOn P _ hext
  have hnum : marginal P ↑(insert k (parentSet pa k))
      (Function.update (extendPa pa k fun j => x (Fin.castLE k.2.le j)) k (x k)) =
      marginal P ↑(insert k (parentSet pa k)) x := by
    refine marginal_congr_of_eqOn P _ fun i hi => ?_
    rcases mem_insert.1 hi with rfl | hi
    · simp
    · rw [Function.update_of_ne (fun h => hkPa (by rw [h] at hi; exact hi)), hext i hi]
  unfold condTable
  rw [dite_eq_right_of_eq_false (eq_false (by rw [hden]; exact h))]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [hnum, hden]

omit [Nonempty α] in
/-- The marginal on all variables is the law itself. -/
private theorem marginal_univ_apply [Fintype α] (P : (Fin n → α) → ℝ) (x : Fin n → α) :
    marginal P Set.univ x = P x := by
  unfold marginal
  simp only [sum_filter]
  rw [Fintype.sum_eq_single x]
  · simp
  · intro y hne
    exact ite_eq_right_of_eq_false _ _
      (eq_false fun h => hne (funext fun v => h v (Set.mem_univ v)))

/-- The nodes before position `m`. -/
private def prefixSet (n m : ℕ) : Finset (Fin n) := univ.filter fun j => j.val < m

/-- **Markov laws factorize** ((O) ⇒ (F); Lauritzen 2009): a law with the ordered Markov
property for the parent sets `pa` is the joint law of a Bayesian network on these parent sets,
namely the network of its conditional laws given the parents. No positivity is assumed. -/
theorem exists_bayesNet_of_orderedMarkov [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (h1 : ∑ x, P x = 1) (pa : (k : Fin n) → Finset (Fin k)) (hO : OrderedMarkov P pa) :
    ∃ b : BayesNet α n, b.pa = pa ∧ b.joint = P := by
  classical
  refine ⟨condNet P hP pa, rfl, ?_⟩
  set b := condNet P hP pa
  have key : ∀ m ≤ n, ∀ x, marginal P ↑(prefixSet n m) x =
      ∏ k ∈ univ.filter (fun k : Fin n => k.val < m),
        (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
    intro m
    induction m with
    | zero =>
      intro _ x
      have : prefixSet n 0 = ∅ := by ext j; simp [prefixSet]
      rw [this, coe_empty]
      simp [marginal, h1]
    | succ m ih =>
      intro hm x
      set k : Fin n := ⟨m, hm⟩
      have hS : prefixSet n (m + 1) = insert k (prefixSet n m) := by
        ext j
        simp only [prefixSet, mem_filter, mem_univ, true_and, mem_insert, k, Fin.ext_iff]
        omega
      have hF : univ.filter (fun j : Fin n => j.val < m + 1) =
          insert k (univ.filter fun j : Fin n => j.val < m) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_insert, k, Fin.ext_iff]
        omega
      have hkF : k ∉ univ.filter fun j : Fin n => j.val < m := by simp [k]
      rw [hF, prod_insert hkF, ← ih (Nat.le_of_succ_le hm) x, mul_comm]
      -- the ordered Markov property at `k`
      set Pa := parentSet pa k with hPa
      have hPaS : Pa ⊆ prefixSet n m := fun j hj => by
        simpa [prefixSet, k, Fin.lt_def] using lt_of_mem_parentSet hj
      have hkPa : k ∉ Pa := fun hk => lt_irrefl _ (lt_of_mem_parentSet hk)
      have hci := (condIndep_coe_iff.1 (hO k)) x
      have e1 : {k} ∪ nonParentPred pa k ∪ Pa = prefixSet n (m + 1) := by
        rw [hS]
        ext j
        simp only [mem_union, mem_singleton, nonParentPred, mem_filter, mem_univ, true_and,
          mem_insert, prefixSet]
        constructor
        · rintro ((h | ⟨h, -⟩) | h)
          · exact Or.inl h
          · exact Or.inr (by simpa [k, Fin.lt_def] using h)
          · exact Or.inr (by simpa [prefixSet] using hPaS h)
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · by_cases hp : j ∈ Pa
            · exact Or.inr hp
            · exact Or.inl (Or.inr ⟨by simpa [k, Fin.lt_def] using h, hp⟩)
      have e2 : nonParentPred pa k ∪ Pa = prefixSet n m := by
        ext j
        simp only [mem_union, nonParentPred, mem_filter, mem_univ, true_and, prefixSet]
        constructor
        · rintro (⟨h, -⟩ | h)
          · simpa [k, Fin.lt_def] using h
          · simpa [prefixSet] using hPaS h
        · intro h
          by_cases hp : j ∈ Pa
          · exact Or.inr hp
          · exact Or.inl ⟨by simpa [k, Fin.lt_def] using h, hp⟩
      have e3 : ({k} : Finset (Fin n)) ∪ Pa = insert k Pa := by simp
      rw [e1, e2, e3] at hci
      by_cases h0 : marginal P ↑Pa x = 0
      · have hm0 : marginal P ↑(prefixSet n m) x = 0 :=
          le_antisymm (h0 ▸ marginal_le_of_subset hP hPaS x) (marginal_nonneg hP _ _)
        have hm1 : marginal P ↑(prefixSet n (m + 1)) x = 0 :=
          le_antisymm (hm0 ▸ marginal_le_of_subset hP (hS ▸ subset_insert k _) x)
            (marginal_nonneg hP _ _)
        rw [hm0, hm1, zero_mul]
      · have hcpt : (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) =
            marginal P ↑(insert k Pa) x / marginal P ↑Pa x :=
          condTable_weights P hP pa k x h0
        rw [hcpt, mul_div_assoc', eq_div_iff h0, hci]
        ring
  funext x
  have hall := key n le_rfl x
  have hpre : prefixSet n n = univ := by ext j; simp [prefixSet]
  have hfil : univ.filter (fun k : Fin n => k.val < n) = univ := by ext j; simp
  rw [hpre, hfil] at hall
  rw [BayesNet.joint_eq_prod, ← hall, coe_univ]
  exact marginal_univ_apply P x

/-- **The ordered Markov property is equivalent to factorization** (Lauritzen 2009): a law on
`Fin n → α` has the ordered Markov property for the parent sets `pa` if and only if it is the
joint law of a Bayesian network on `pa`. -/
theorem orderedMarkov_iff_exists_bayesNet [Fintype α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (h1 : ∑ x, P x = 1) (pa : (k : Fin n) → Finset (Fin k)) :
    OrderedMarkov P pa ↔ ∃ b : BayesNet α n, b.pa = pa ∧ b.joint = P := by
  constructor
  · exact exists_bayesNet_of_orderedMarkov P hP h1 pa
  · rintro ⟨b, rfl, rfl⟩
    exact orderedMarkov_joint b

end Factorization

end Cslib.MachineLearning.GraphicalModels
