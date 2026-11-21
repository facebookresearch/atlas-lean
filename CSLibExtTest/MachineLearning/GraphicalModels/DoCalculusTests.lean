/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DoCalculus

/-!
# Tests for the do-calculus rules

Examples for `CSLibExt/MachineLearning/GraphicalModels/DoCalculus.lean`, on two-node networks
`0 → 1` over `Bool`:

* the edge lemma of `BayesNet.cutOut`;
* rule 2 with `Z = ∅`, where the d-separation hypothesis holds vacuously;
* rule 2 with `X = W = ∅`, `Y = {1}` and `Z = {0}`, where the d-separation of `Y` and `Z` in
  `G_{\underline Z}` is discharged by checking every path.
-/

@[expose] public section

namespace Cslib.MachineLearning.DoCalculusTests

open Cslib.MachineLearning GraphicalModels BayesNet Finset MetaMathlibExt.FiniteWeight

/-- The two-node network `0 → 1` with constant-`true` tables, for the examples below. -/
noncomputable def chain2 : BayesNet Bool 2 where
  pa k := Finset.univ.filter fun i : Fin k => i.val + 1 = k.val
  cpt _ _ := Convexity.StdSimplex.single true

/-- Rule 2 on the two-node network `0 → 1`, with `Z = ∅` so `hd` holds vacuously. -/
example : marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((({1} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) /
      marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => true) =
    marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      ((({1} ∪ ∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) /
      marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) := by
  have dXY : Disjoint (∅ : Finset (Fin 2)) ({1} : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dXZ : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dXW : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dYZ : Disjoint ({1} : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a _ haE => (notMem_empty a haE).elim
  have dYW : Disjoint ({1} : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a _ haE => (notMem_empty a haE).elim
  have dZW : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have hd : ((chain2.mutilateSet ∅ (fun _ => true)).cutOut ∅ (fun _ => true)).DSeparated
      (({1} : Finset (Fin 2)) : Set (Fin 2)) ((∅ : Finset (Fin 2)) : Set (Fin 2))
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) :=
    fun x _ y hy p _ => (notMem_empty y (mem_coe.1 hy)).elim
  have hpos : ∀ (P : (Fin 2 → Bool) → ℝ) (S : Finset (Fin 2)), (∀ v, 0 ≤ P v) →
      P (fun _ => true) = 1 → marginal P (S : Set (Fin 2)) (fun _ => true) ≠ 0 := by
    intro P S hnn h1
    simp only [marginal_coe]
    have ha : (fun _ => true) ∈
        univ.filter (fun v : Fin 2 → Bool => ∀ i ∈ S, v i = (fun _ => true) i) :=
      mem_filter.2 ⟨mem_univ _, fun _ _ => rfl⟩
    have hle : (1 : ℝ) ≤
        ∑ v ∈ univ.filter (fun v : Fin 2 → Bool => ∀ i ∈ S, v i = (fun _ => true) i), P v := by
      rw [← h1]
      exact Finset.single_le_sum (fun v _ => hnn v) ha
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hle)
  have hcpt : ∀ (j : Fin 2) (u : chain2.pa j → Bool),
      chain2.cpt j u = Convexity.StdSimplex.single true :=
    fun j u => rfl
  have hj1 : (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint (fun _ => true) = 1 := by
    rw [joint_mutilateSet]
    refine prod_eq_one fun j _ => ?_
    by_cases hj : j ∈ (∅ ∪ ∅ : Finset (Fin 2))
    · rcases mem_union.1 hj with h | h <;> exact (notMem_empty j h).elim
    · simp only [if_neg hj]
      rw [hcpt]
      simp [Convexity.StdSimplex.single]
  have hj0 : (chain2.mutilateSet ∅ (fun _ => true)).joint (fun _ => true) = 1 := by
    rw [joint_mutilateSet]
    refine prod_eq_one fun j _ => ?_
    by_cases hj : j ∈ (∅ : Finset (Fin 2))
    · exact (notMem_empty j hj).elim
    · simp only [if_neg hj]
      rw [hcpt]
      simp [Convexity.StdSimplex.single]
  have hnn1 : ∀ v, 0 ≤ (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint v :=
    fun v => (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).toChain.joint_nonneg 2 v
  have hnn0 : ∀ v, 0 ≤ (chain2.mutilateSet ∅ (fun _ => true)).joint v :=
    fun v => (chain2.mutilateSet ∅ (fun _ => true)).toChain.joint_nonneg 2 v
  have hw : marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => true) ≠ 0 :=
    hpos _ _ hnn1 hj1
  have hzw : marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) ≠ 0 :=
    hpos _ _ hnn0 hj0
  exact doCalculus_rule2 chain2 (fun _ => true) dXY dXZ dXW dYZ dYW dZW hd hw hzw

/-- `cutOut` removes the arrows out of the cut set, so no arrow leaves it. -/
example {α : Type*} {n : ℕ} (b : BayesNet α n) (z : Fin n → α) {i j : Fin n} :
    ¬ (b.cutOut {i} z).Edge i j := by
  simp [edge_cutOut_iff]

/-- Without intervened nodes, the joint is that of `b` (a copy of the private lemma
`joint_mutilateSet_empty` of `CausalAdjustment.lean`). -/
theorem joint_mutilateSet_empty_dc {α : Type*} {n : ℕ} [Nonempty α]
    (b : BayesNet α n) (w : Fin n → α) :
    (b.mutilateSet ∅ w).joint = b.joint := by
  classical
  funext x
  rw [joint_mutilateSet, joint_eq_prod]
  simp only [Finset.notMem_empty, ite_false]
  rfl

/-- The two-node network `0 → 1` over `Bool`, both tables point masses at `false`. -/
noncomputable def exampleNet_dc : BayesNet Bool 2 where
  pa j := Finset.univ.filter fun i : Fin j => i.val = 0 ∧ j.val = 1
  cpt _ _ := Convexity.StdSimplex.single false

example {α : Type*} (b : BayesNet α 2) (x : Fin 2 → α) :
    ((b.cutOut {0} x).Edge 0 1 ↔ b.Edge 0 1 ∧ (0 : Fin 2) ∉ ({0} : Finset (Fin 2))) :=
  edge_cutOut_iff b {0} x

example : marginal (exampleNet_dc.mutilateSet (∅ ∪ {0}) (fun _ => false)).joint
      ((({1} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => false) /
      marginal (exampleNet_dc.mutilateSet (∅ ∪ {0}) (fun _ => false)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => false) =
    marginal (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint
      ((({1} ∪ {0} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => false) /
      marginal (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint
      ((({0} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => false) := by
  have hXY' : Disjoint (∅ : Finset (Fin 2)) {1} := by decide
  have hXZ' : Disjoint (∅ : Finset (Fin 2)) {0} := by decide
  have hXW' : Disjoint (∅ : Finset (Fin 2)) ∅ := by decide
  have hYZ' : Disjoint ({1} : Finset (Fin 2)) {0} := by decide
  have hYW' : Disjoint ({1} : Finset (Fin 2)) ∅ := by decide
  have hZW' : Disjoint ({0} : Finset (Fin 2)) ∅ := by decide
  have h01 : ∀ a c : Fin 2, a.val < c.val → a = 0 ∧ c = 1 := by decide
  have hhd : ((exampleNet_dc.mutilateSet ∅ (fun _ => false)).cutOut {0} (fun _ => false)).DSeparated
      ((({1} : Finset (Fin 2))) : Set (Fin 2)) ((({0} : Finset (Fin 2))) : Set (Fin 2))
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) := by
    intro y hy z hz p hp
    rw [Finset.mem_coe, Finset.mem_singleton] at hy hz
    subst hy
    subst hz
    obtain ⟨-, hch, hh, hl⟩ := hp
    cases p with
    | nil => exact absurd hh (by decide)
    | cons y0 rest =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases rest with
      | nil => exact absurd hl (by decide)
      | cons y1 rest' =>
        have hAdj := (List.isChain_cons_cons.1 hch).1
        simp only [Adj] at hAdj
        rcases hAdj with hE | hE
        · obtain ⟨hM, -⟩ := ((exampleNet_dc.mutilateSet ∅ (fun _ => false)).edge_cutOut_iff {0}
            (fun _ => false)).1 hE
          obtain ⟨hB, -⟩ := (exampleNet_dc.edge_mutilateSet_iff ∅ (fun _ => false)).1 hM
          obtain ⟨hlt, -⟩ := hB
          exact absurd (h01 _ _ hlt).1 (by decide)
        · obtain ⟨hM, hne⟩ := ((exampleNet_dc.mutilateSet ∅ (fun _ => false)).edge_cutOut_iff {0}
            (fun _ => false)).1 hE
          obtain ⟨hB, -⟩ := (exampleNet_dc.edge_mutilateSet_iff ∅ (fun _ => false)).1 hM
          obtain ⟨hlt, -⟩ := hB
          have hy10 : y1 = 0 := (h01 _ _ hlt).1
          rw [Finset.mem_singleton] at hne
          exact absurd hy10 hne
  have hhw : marginal (exampleNet_dc.mutilateSet (∅ ∪ {0}) (fun _ => false)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => false) ≠ 0 := by
    have h1 : marginal (exampleNet_dc.mutilateSet (∅ ∪ {0}) (fun _ => false)).joint
        ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => false) = 1 := by
      classical
      rw [marginal_coe]
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true_of_mem]
      exact (exampleNet_dc.mutilateSet (∅ ∪ {0}) (fun _ => false)).sum_joint
    rw [h1]
    exact one_ne_zero
  have hhzw : marginal (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint
      ((({0} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => false) ≠ 0 := by
    have hJ1 : (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint (fun _ => false) = 1 := by
      rw [joint_mutilateSet_empty_dc, exampleNet_dc.joint_eq_prod]
      have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [huniv, Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
        Finset.prod_singleton]
      simp [exampleNet_dc, Convexity.StdSimplex.single]
    have hle : (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint (fun _ => false) ≤
        marginal (exampleNet_dc.mutilateSet ∅ (fun _ => false)).joint
          ((({0} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => false) := by
      rw [marginal_coe]
      refine Finset.single_le_sum
        (fun v _ => ((exampleNet_dc.mutilateSet ∅ (fun _ => false)).toChain.joint_nonneg 2 v)) ?_
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i _ => rfl⟩
    rw [hJ1] at hle
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hle)
  exact doCalculus_rule2 exampleNet_dc (fun _ => false) hXY' hXZ' hXW' hYZ' hYW' hZW' hhd hhw hhzw

end Cslib.MachineLearning.DoCalculusTests
