/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DirectedMarkovProperties
public import CSLibExt.MachineLearning.GraphicalModels.Junctions
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for the equivalence of the directed Markov properties

On the chain `X₀ → X₁ → X₂`: the parents `{X₁}` d-separate `X₂` from `X₀`; a law with the global
Markov property for the chain factorizes over it; and the joint of the chain has all four
properties.

For every finite value type, with factorization stated as the product of the tables
(`orderedMarkov_iff_exists_bayesNet_prod`, `directedMarkov_tfae_prod`):

* the empty value type on zero nodes: its only law, mass `1` on the empty assignment, is ordered,
  local and global Markov and is the product of the tables of the network on zero nodes;
* the empty value type on three nodes carries no network and no law, so the chain, the fork and
  the collider have no instance there;
* the chain `X₀ → X₁ → X₂` and the fork `X₁ ← X₀ → X₂` in product form: the end nodes are
  conditionally independent given the middle node, for every table, and the ordered Markov
  property at node `2` gives the same independence for every finite value type;
* the collider `X₀ → X₂ ← X₁` in product form: the roots are independent for every table, and in
  `Junctions.berksonNet` they are dependent given `X₂`;
* the edge `X₀ → X₁` with `X₀ = false` almost surely: the law factorizes, and the table of `X₁`
  at the null row `X₀ = true` is arbitrary;
* countermodels: without total mass `1` (zero nodes over the empty value type, and one `Bool`
  node) or without nonnegativity, an ordered Markov weight need not be a product of tables.
-/

@[expose] public section

namespace Cslib.MachineLearning.DirectedMarkovPropertiesTests

open Cslib.MachineLearning GraphicalModels Convexity Finset MetaMathlibExt.FiniteWeight

/-- The fair coin on `Bool`. -/
noncomputable def fair : StdSimplex ℝ Bool :=
  StdSimplex.duple (s := 1 / 2) (t := 1 / 2) true false (by norm_num) (by norm_num) (by norm_num)

/-- The parents of the chain `X₀ → X₁ → X₂`. -/
def chainPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Every table is the fair coin. -/
noncomputable def chain : BayesNet Bool 3 where
  pa := chainPa
  cpt _ _ := fair

/-- The parents of `X₂` d-separate it from its other non-descendants. -/
example : chain.DSeparated {2} {j | ¬chain.IsDescendant 2 j ∧ ¬chain.Edge j 2}
    {j | chain.Edge j 2} :=
  chain.dSeparated_localMarkov 2

/-- A law with the global Markov property for the chain factorizes over it. -/
example (P : (Fin 3 → Bool) → ℝ) (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1)
    (hG : GlobalMarkovFor P chain) : ∃ b : BayesNet Bool 3, b.pa = chain.pa ∧ b.joint = P :=
  ((directedMarkov_tfae P hP h1 chain).out 2 1).1 hG

/-- The joint of the chain has the local Markov property. -/
example : LocalMarkovFor chain.joint chain :=
  ((directedMarkov_tfae chain.joint (fun x => chain.toChain.joint_nonneg 3 x) chain.sum_joint
    chain).out 1 3).1 (⟨chain, rfl, rfl⟩ : ∃ b' : BayesNet Bool 3, b'.pa = chain.pa ∧
      b'.joint = chain.joint)

/-! ### Every finite value type: factorization as the product of the tables -/

/-! #### The empty value type on zero nodes -/

/-- The law on zero nodes over the empty value type, mass `1` on the empty assignment, is
ordered, local and global Markov for the network on zero nodes. -/
theorem emptyZero_markov :
    OrderedMarkov (fun _ : Fin 0 → Empty => (1 : ℝ)) (default : BayesNet Empty 0).pa ∧
      LocalMarkovFor (fun _ : Fin 0 → Empty => (1 : ℝ)) (default : BayesNet Empty 0) ∧
      GlobalMarkovFor (fun _ : Fin 0 → Empty => (1 : ℝ)) (default : BayesNet Empty 0) := by
  have hO : OrderedMarkov (fun _ : Fin 0 → Empty => (1 : ℝ))
      (default : BayesNet Empty 0).pa := fun k => k.elim0
  have hP : ∀ x : Fin 0 → Empty, 0 ≤ (fun _ : Fin 0 → Empty => (1 : ℝ)) x := by simp
  have h1 : ∑ x : Fin 0 → Empty, (fun _ : Fin 0 → Empty => (1 : ℝ)) x = 1 := by simp
  have htfae := directedMarkov_tfae_prod (fun _ : Fin 0 → Empty => (1 : ℝ)) hP h1
    (default : BayesNet Empty 0)
  refine ⟨hO, (htfae.out 4 3).mp hO, (htfae.out 4 2).mp hO⟩

/-- That law is the product of the tables of the network on zero nodes, the empty product. -/
theorem emptyZero_eq_prod_cpt (x : Fin 0 → Empty) :
    (1 : ℝ) = ∏ k : Fin 0,
      ((default : BayesNet Empty 0).cpt k
        ((default : BayesNet Empty 0).paVal k x)).weights (x k) := by
  simp

/-- The equivalence of the ordered Markov property and factorization at the empty corner. -/
theorem emptyZero_orderedMarkov_iff (pa : (k : Fin 0) → Finset (Fin k)) :
    OrderedMarkov (fun _ : Fin 0 → Empty => (1 : ℝ)) pa ↔
      ∃ b : BayesNet Empty 0, b.pa = pa ∧
        ∀ x : Fin 0 → Empty,
          (1 : ℝ) = ∏ k : Fin 0, (b.cpt k (b.paVal k x)).weights (x k) := by
  have hP : ∀ x : Fin 0 → Empty, 0 ≤ (fun _ : Fin 0 → Empty => (1 : ℝ)) x := by simp
  have h1 : ∑ x : Fin 0 → Empty, (fun _ : Fin 0 → Empty => (1 : ℝ)) x = 1 := by simp
  exact orderedMarkov_iff_exists_bayesNet_prod _ hP h1 pa

/-! #### The empty value type on three nodes -/

/-- There is no network on three nodes over the empty value type, so the chain, the fork and the
collider have no instance there. -/
theorem isEmpty_bayesNet_empty_three : IsEmpty (BayesNet Empty 3) := by
  exact BayesNet.instIsEmptySucc (n := 2)

/-- There is no law on three nodes over the empty value type. -/
theorem sum_ne_one_empty_three (P : (Fin 3 → Empty) → ℝ) : ∑ x, P x ≠ 1 := by
  have : IsEmpty (Fin 3 → Empty) := ⟨fun f => Empty.elim (f 0)⟩
  simp

/-! #### The chain `X₀ → X₁ → X₂` -/

/-- In product form, the end nodes of the chain are conditionally independent given the middle
node, `X₀ ⫫ X₂ | X₁`, for every table and every finite nonempty value type. -/
theorem condIndep_chain_prod_cpt {α : Type*} [Fintype α] [Nonempty α]
    (cpt : (k : Fin 3) → (Junctions.chainPa k → α) → StdSimplex ℝ α) :
    CondIndep (fun x => ∏ k : Fin 3,
        ((BayesNet.mk Junctions.chainPa cpt).cpt k
          ((BayesNet.mk Junctions.chainPa cpt).paVal k x)).weights (x k))
      {0} {2} {1} := by
  have h : (fun x => ∏ k : Fin 3,
      ((BayesNet.mk Junctions.chainPa cpt).cpt k
        ((BayesNet.mk Junctions.chainPa cpt).paVal k x)).weights (x k))
      = (BayesNet.mk Junctions.chainPa cpt).joint := by
    funext x
    exact (BayesNet.joint_eq_prod _ x).symm
  rw [h]
  exact Junctions.condIndep_chain cpt

/-- The same independence from the ordered Markov property at node `2`
(`orderedMarkov_prod_cpt`), `X₂ ⫫ X₀ | X₁`, for every table and every finite value type. -/
theorem condIndep_chain_prod_cpt_of_orderedMarkov {α : Type*} [Fintype α]
    (cpt : (k : Fin 3) → (Junctions.chainPa k → α) → StdSimplex ℝ α) :
    CondIndep (fun x => ∏ k : Fin 3,
        ((BayesNet.mk Junctions.chainPa cpt).cpt k
          ((BayesNet.mk Junctions.chainPa cpt).paVal k x)).weights (x k))
      {2} {0} {1} := by
  have hO := orderedMarkov_prod_cpt (BayesNet.mk Junctions.chainPa cpt)
  have h2 := hO 2
  have hpar : parentSet Junctions.chainPa 2 = {1} := by decide
  have hnp : nonParentPred Junctions.chainPa 2 = {0} := by decide
  rw [hpar, hnp] at h2
  simpa only [Finset.coe_singleton] using h2

/-! #### The fork `X₁ ← X₀ → X₂` -/

/-- In product form, the children of the fork are conditionally independent given the common
parent, `X₁ ⫫ X₂ | X₀`, for every table and every finite nonempty value type. -/
theorem condIndep_fork_prod_cpt {α : Type*} [Fintype α] [Nonempty α]
    (cpt : (k : Fin 3) → (Junctions.forkPa k → α) → StdSimplex ℝ α) :
    CondIndep (fun x => ∏ k : Fin 3,
        ((BayesNet.mk Junctions.forkPa cpt).cpt k
          ((BayesNet.mk Junctions.forkPa cpt).paVal k x)).weights (x k))
      {1} {2} {0} := by
  have h : (fun x => ∏ k : Fin 3,
      ((BayesNet.mk Junctions.forkPa cpt).cpt k
        ((BayesNet.mk Junctions.forkPa cpt).paVal k x)).weights (x k))
      = (BayesNet.mk Junctions.forkPa cpt).joint := by
    funext x
    exact (BayesNet.joint_eq_prod _ x).symm
  rw [h]
  exact Junctions.condIndep_fork cpt

/-- The same independence from the ordered Markov property at node `2`
(`orderedMarkov_prod_cpt`), `X₂ ⫫ X₁ | X₀`, for every table and every finite value type. -/
theorem condIndep_fork_prod_cpt_of_orderedMarkov {α : Type*} [Fintype α]
    (cpt : (k : Fin 3) → (Junctions.forkPa k → α) → StdSimplex ℝ α) :
    CondIndep (fun x => ∏ k : Fin 3,
        ((BayesNet.mk Junctions.forkPa cpt).cpt k
          ((BayesNet.mk Junctions.forkPa cpt).paVal k x)).weights (x k))
      {2} {1} {0} := by
  have hO := orderedMarkov_prod_cpt (BayesNet.mk Junctions.forkPa cpt)
  have h2 := hO 2
  have hpar : parentSet Junctions.forkPa 2 = {0} := by decide
  have hnp : nonParentPred Junctions.forkPa 2 = {1} := by decide
  rw [hpar, hnp] at h2
  simpa only [Finset.coe_singleton] using h2

/-! #### The collider `X₀ → X₂ ← X₁` -/

/-- In product form, the roots of the collider are independent, `X₁ ⫫ X₀`, from the ordered
Markov property at node `1` (`orderedMarkov_prod_cpt`), for every table and every finite value
type. -/
theorem condIndep_collider_prod_cpt_of_orderedMarkov {α : Type*} [Fintype α]
    (cpt : (k : Fin 3) → (Junctions.colliderPa k → α) → StdSimplex ℝ α) :
    CondIndep (fun x => ∏ k : Fin 3,
        ((BayesNet.mk Junctions.colliderPa cpt).cpt k
          ((BayesNet.mk Junctions.colliderPa cpt).paVal k x)).weights
          (x k))
      {1} {0} ∅ := by
  have hO := orderedMarkov_prod_cpt (BayesNet.mk Junctions.colliderPa cpt)
  have h1 := hO 1
  have hpar : parentSet Junctions.colliderPa 1 = ∅ := by decide
  have hnp : nonParentPred Junctions.colliderPa 1 = {0} := by decide
  rw [hpar, hnp] at h1
  simpa only [Finset.coe_singleton, Finset.coe_empty] using h1

/-- In the product form of the Berkson network (`X₀`, `X₁` independent fair coins and
`X₂ = X₀ ∨ X₁`), the roots are independent, `X₀ ⫫ X₁`. -/
theorem berksonNet_prod_cpt_condIndep_parents :
    CondIndep (fun x => ∏ k : Fin 3,
        (Junctions.berksonNet.cpt k (Junctions.berksonNet.paVal k x)).weights (x k))
      {0} {1} ∅ := by
  have h : (fun x => ∏ k : Fin 3,
      (Junctions.berksonNet.cpt k (Junctions.berksonNet.paVal k x)).weights (x k))
      = Junctions.berksonNet.joint := by
    funext x
    exact (BayesNet.joint_eq_prod _ x).symm
  rw [h]
  exact Junctions.berksonNet_condIndep_parents

/-- In the product form of the Berkson network the roots are dependent given the collider,
`¬ X₀ ⫫ X₁ | X₂` (Berkson's paradox). -/
theorem berksonNet_prod_cpt_not_condIndep_given_collider :
    ¬ CondIndep (fun x => ∏ k : Fin 3,
        (Junctions.berksonNet.cpt k (Junctions.berksonNet.paVal k x)).weights (x k))
      {0} {1} {2} := by
  have h : (fun x => ∏ k : Fin 3,
      (Junctions.berksonNet.cpt k (Junctions.berksonNet.paVal k x)).weights (x k))
      = Junctions.berksonNet.joint := by
    funext x
    exact (BayesNet.joint_eq_prod _ x).symm
  rw [h]
  exact Junctions.berksonNet_not_condIndep_given_collider

/-! #### A parent value of probability zero -/

/-- The edge `X₀ → X₁`. -/
def edgePa : (k : Fin 2) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨_ + 2, h⟩ => absurd h (by omega)

private theorem fm_aux_tb_orderedMarkov_one_empty (P : (Fin 1 → Bool) → ℝ) :
    OrderedMarkov P (fun _ => ∅) := by
  intro k
  fin_cases k
  have hp : parentSet (fun k : Fin 1 => (∅ : Finset (Fin k))) 0 = ∅ := by decide
  have hn : nonParentPred (fun k : Fin 1 => (∅ : Finset (Fin k))) 0 = ∅ := by decide
  simp [CondIndep, hp, hn]

/-- The law on the edge with `X₀ = false` almost surely and `X₁` a fair coin factorizes over it
(`exists_bayesNet_prod_of_orderedMarkov`), although the parent value `X₀ = true` has probability
zero. -/
theorem exists_bayesNet_prod_edge_null_row :
    ∃ b : BayesNet Bool 2, b.pa = edgePa ∧
      ∀ x : Fin 2 → Bool, (if x 0 = false then (1 / 2 : ℝ) else 0) =
        ∏ k : Fin 2, (b.cpt k (b.paVal k x)).weights (x k) := by
  have hP : ∀ x : Fin 2 → Bool, 0 ≤ (if x 0 = false then (1 / 2 : ℝ) else 0) := by
    intro x
    split_ifs <;> norm_num
  have h1 : ∑ x : Fin 2 → Bool, (if x 0 = false then (1 / 2 : ℝ) else 0) = 1 := by
    show ∑ x : Fin (1 + 1) → Bool, (if x 0 = false then (1 / 2 : ℝ) else 0) = 1
    rw [sum_snoc]
    simp only [Fin.snoc_apply_zero]
    have hstep : (∑ y : Fin 1 → Bool, ∑ a : Bool, (if y 0 = false then (1 / 2 : ℝ) else 0))
        = ∑ b : Bool, ∑ a : Bool, (if b = false then (1 / 2 : ℝ) else 0) := by
      have hbase := (Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm
        (fun y : Fin 1 → Bool => ∑ a : Bool, (if y 0 = false then (1 / 2 : ℝ) else 0))).symm
      have hpt : ∀ b : Bool, (fun y : Fin 1 → Bool =>
          ∑ a : Bool, (if y 0 = false then (1 / 2 : ℝ) else 0))
          (((Equiv.funUnique (Fin 1) Bool).symm) b)
          = ∑ a : Bool, (if b = false then (1 / 2 : ℝ) else 0) := by
        intro b
        rw [show (((Equiv.funUnique (Fin 1) Bool).symm) b) = uniqueElim b from rfl]
        show (∑ a : Bool, (if (uniqueElim (ι := Fin 1) (α := fun _ => Bool) b 0) = false then
          (1 / 2 : ℝ) else 0)) = _
        rw [uniqueElim_const]
      exact hbase.trans (Finset.sum_congr rfl fun b _ => hpt b)
    rw [hstep]
    norm_num [Fintype.sum_bool]
  have hO : OrderedMarkov (fun x : Fin 2 → Bool => (if x 0 = false then (1 / 2 : ℝ) else 0))
      edgePa := by
    intro k
    fin_cases k
    · have hp0 : parentSet edgePa 0 = ∅ := by decide
      have hn0 : nonParentPred edgePa 0 = ∅ := by decide
      simp [CondIndep, hp0, hn0]
    · have hp1 : parentSet edgePa 1 = {0} := by decide
      have hn1 : nonParentPred edgePa 1 = ∅ := by decide
      simp [CondIndep, hp1, hn1]
  obtain ⟨b, hbpa, hfac⟩ := exists_bayesNet_prod_of_orderedMarkov _ hP h1 _ hO
  exact ⟨b, hbpa, hfac⟩

/-! #### Countermodels: total mass `1` and nonnegativity are needed -/

/-- Total mass `1` is needed at the empty corner itself: on zero nodes over the empty value type
the zero weight is ordered Markov, but every product of tables there is `1`. -/
theorem orderedMarkov_zero_not_prod_cpt_emptyZero (pa : (k : Fin 0) → Finset (Fin k)) :
    OrderedMarkov (0 : (Fin 0 → Empty) → ℝ) pa ∧
      ¬ ∃ b : BayesNet Empty 0, b.pa = pa ∧
        ∀ x : Fin 0 → Empty,
          (0 : ℝ) = ∏ k : Fin 0, (b.cpt k (b.paVal k x)).weights (x k) := by
  constructor
  · exact fun k => k.elim0
  · rintro ⟨b, -, h⟩
    have h1 := h (fun k => k.elim0)
    simp at h1

/-- Total mass `1` is needed on a nonempty value type: on one `Bool` node without parents the
weight `1` (total mass `2`) is ordered Markov but is not a product of tables. -/
theorem orderedMarkov_mass_two_not_prod_cpt :
    OrderedMarkov (fun _ : Fin 1 → Bool => (1 : ℝ)) (fun _ => ∅) ∧
      ¬ ∃ b : BayesNet Bool 1, b.pa = (fun _ => ∅) ∧
        ∀ x : Fin 1 → Bool,
          (1 : ℝ) = ∏ k : Fin 1, (b.cpt k (b.paVal k x)).weights (x k) := by
  constructor
  · exact fm_aux_tb_orderedMarkov_one_empty _
  · rintro ⟨b, -, h⟩
    have h2 : (∑ _x : Fin 1 → Bool, (1 : ℝ)) = 1 := by
      calc ∑ _x : Fin 1 → Bool, (1 : ℝ)
          = ∑ x : Fin 1 → Bool,
              ∏ k : Fin 1, (b.cpt k (b.paVal k x)).weights (x k) :=
            Finset.sum_congr rfl fun x _ => h x
        _ = 1 := BayesNet.sum_prod_cpt b
    have hcard : Fintype.card (Fin 1 → Bool) = 2 := by decide
    rw [Finset.sum_const, Finset.card_univ, hcard] at h2
    norm_num at h2

/-- Nonnegativity is needed: on one `Bool` node without parents the signed weight `(2, -1)` of
total mass `1` is ordered Markov but is not a product of tables. -/
theorem orderedMarkov_signed_not_prod_cpt :
    (∑ x : Fin 1 → Bool, (if x 0 then (2 : ℝ) else -1) = 1) ∧
      OrderedMarkov (fun x : Fin 1 → Bool => if x 0 then (2 : ℝ) else -1) (fun _ => ∅) ∧
      ¬ ∃ b : BayesNet Bool 1, b.pa = (fun _ => ∅) ∧
        ∀ x : Fin 1 → Bool, (if x 0 then (2 : ℝ) else -1) =
          ∏ k : Fin 1, (b.cpt k (b.paVal k x)).weights (x k) := by
  refine ⟨?_, fm_aux_tb_orderedMarkov_one_empty _, ?_⟩
  · have hstep : (∑ x : Fin 1 → Bool, (if x 0 then (2 : ℝ) else -1))
        = ∑ b : Bool, (if b then (2 : ℝ) else -1) := by
      have hbase := (Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm
        (fun x : Fin 1 → Bool => (if x 0 then (2 : ℝ) else -1))).symm
      have hpt : ∀ b : Bool, (fun x : Fin 1 → Bool => (if x 0 then (2 : ℝ) else -1))
          (((Equiv.funUnique (Fin 1) Bool).symm) b)
          = (if b then (2 : ℝ) else -1) := by
        intro b
        rw [show (((Equiv.funUnique (Fin 1) Bool).symm) b) = uniqueElim b from rfl]
        show (if (uniqueElim (ι := Fin 1) (α := fun _ => Bool) b 0) then (2 : ℝ)
          else -1) = _
        rw [uniqueElim_const]
      exact hbase.trans (Finset.sum_congr rfl fun b _ => hpt b)
    rw [hstep]
    norm_num [Fintype.sum_bool]
  · rintro ⟨b, -, h⟩
    have h0 := h (fun _ => false)
    have hneg : (∏ k : Fin 1,
        (b.cpt k (b.paVal k (fun _ => false))).weights ((fun _ => false) k)) < 0 := by
      rw [← h0]
      norm_num
    have hnn : 0 ≤ ∏ k : Fin 1,
        (b.cpt k (b.paVal k (fun _ => false))).weights ((fun _ => false) k) :=
      Finset.prod_nonneg fun k _ => StdSimplex.weights_nonneg _
    exact (not_le_of_gt hneg) hnn

/-- On the edge, `X₀ = false` almost surely and `X₁` is a fair coin whatever `X₀` is. -/
noncomputable def nullRowFair : BayesNet Bool 2 where
  pa := edgePa
  cpt k _ := if (k : ℕ) = 0 then StdSimplex.single false else Junctions.fairCoin

/-- The same network, except that `X₁ = true` when `X₀ = true`, a parent value of probability
zero. -/
noncomputable def nullRowTrue : BayesNet Bool 2 where
  pa := edgePa
  cpt k u := if (k : ℕ) = 0 then StdSimplex.single false else
    if ∃ i, u i = true then StdSimplex.single true else Junctions.fairCoin

/-- The network of the converse is not unique: the two networks above differ only at the null
row `X₀ = true`, and their tables have the same product. -/
theorem nullRow_ne_and_prod_cpt_eq :
    nullRowFair ≠ nullRowTrue ∧ ∀ x : Fin 2 → Bool,
      ∏ k : Fin 2, (nullRowFair.cpt k (nullRowFair.paVal k x)).weights (x k) =
        ∏ k : Fin 2, (nullRowTrue.cpt k (nullRowTrue.paVal k x)).weights (x k) := by
  constructor
  · intro hcon
    have h1 := congrArg (fun b : BayesNet Bool 2 => b.cpt 1 (fun _ => true)) hcon
    have h10 : ((1 : Fin 2) : ℕ) ≠ 0 := by decide
    have hex : (∃ i : ↥(edgePa (1 : Fin 2)), (fun _ => true) i = true) :=
      ⟨⟨⟨0, by decide⟩, by decide⟩, rfl⟩
    have hL : (nullRowFair.cpt 1 (fun _ => true)) = Junctions.fairCoin := by
      show (if ((1 : Fin 2) : ℕ) = 0 then StdSimplex.single false else Junctions.fairCoin) = _
      rw [ite_eq_right h10]
    have hR : (nullRowTrue.cpt 1 (fun _ => true)) = StdSimplex.single true := by
      show (if ((1 : Fin 2) : ℕ) = 0 then StdSimplex.single false else
        if (∃ i : ↥(edgePa (1 : Fin 2)), (fun _ => true) i = true) then StdSimplex.single true
        else Junctions.fairCoin) = _
      rw [ite_eq_right h10, ite_eq_left hex]
    have hEq : Junctions.fairCoin = StdSimplex.single true := by
      rw [← hL, ← hR]
      exact h1
    have hw := congrArg (fun w : StdSimplex ℝ Bool => w.weights true) hEq
    have hsw : (StdSimplex.single (R := ℝ) true).weights true = (1 : ℝ) := by simp
    rw [Junctions.fairCoin_weights] at hw
    have hcontra : (1 : ℝ) = 1 / 2 := hsw.symm.trans hw.symm
    norm_num at hcontra
  · intro x
    simp only [Fin.prod_univ_two]
    by_cases h : x 0 = false
    · have h00 : ((0 : Fin 2) : ℕ) = 0 := by decide
      have h10 : ((1 : Fin 2) : ℕ) ≠ 0 := by decide
      have hF0 : (nullRowFair.cpt 0 (nullRowFair.paVal 0 x))
          = StdSimplex.single false := by
        show (if ((0 : Fin 2) : ℕ) = 0 then StdSimplex.single false else Junctions.fairCoin) = _
        rw [ite_eq_left h00]
      have hT0 : (nullRowTrue.cpt 0 (nullRowTrue.paVal 0 x))
          = StdSimplex.single false := by
        show (if ((0 : Fin 2) : ℕ) = 0 then StdSimplex.single false else
          if (∃ i : ↥(edgePa (0 : Fin 2)),
            (fun j => x (Fin.castLE (0 : Fin 2).2.le j)) i = true)
          then StdSimplex.single true else Junctions.fairCoin) = _
        rw [ite_eq_left h00]
      have hF1 : (nullRowFair.cpt 1 (nullRowFair.paVal 1 x))
          = Junctions.fairCoin := by
        show (if ((1 : Fin 2) : ℕ) = 0 then StdSimplex.single false else Junctions.fairCoin) = _
        rw [ite_eq_right h10]
      have hno : ¬ ∃ i : ↥(edgePa (1 : Fin 2)),
          (fun j => x (Fin.castLE (1 : Fin 2).2.le j)) i = true := by
        rintro ⟨i, hi⟩
        have h1v : ((1 : Fin 2) : ℕ) = 1 := by decide
        have hj := i.val.2
        have h0v : i.val.val = 0 := by omega
        have hcast : Fin.castLE (1 : Fin 2).2.le ↑i = 0 := by
          apply Fin.ext
          exact h0v
        simp only at hi
        rw [hcast, h] at hi
        exact absurd hi (by decide)
      have hT1 : (nullRowTrue.cpt 1 (nullRowTrue.paVal 1 x))
          = Junctions.fairCoin := by
        show (if ((1 : Fin 2) : ℕ) = 0 then StdSimplex.single false else
          if (∃ i : ↥(edgePa (1 : Fin 2)),
            (fun j => x (Fin.castLE (1 : Fin 2).2.le j)) i = true)
          then StdSimplex.single true else Junctions.fairCoin) = _
        rw [ite_eq_right h10, ite_eq_right hno]
      rw [hF0, hT0, hF1, hT1]
    · have hx0 : x 0 = true := by
        cases h0 : x 0
        · exact absurd h0 h
        · rfl
      have h00 : ((0 : Fin 2) : ℕ) = 0 := by decide
      have hF0 : (nullRowFair.cpt 0 (nullRowFair.paVal 0 x))
          = StdSimplex.single false := by
        show (if ((0 : Fin 2) : ℕ) = 0 then StdSimplex.single false else Junctions.fairCoin) = _
        rw [ite_eq_left h00]
      have hT0 : (nullRowTrue.cpt 0 (nullRowTrue.paVal 0 x))
          = StdSimplex.single false := by
        show (if ((0 : Fin 2) : ℕ) = 0 then StdSimplex.single false else
          if (∃ i : ↥(edgePa (0 : Fin 2)),
            (fun j => x (Fin.castLE (0 : Fin 2).2.le j)) i = true)
          then StdSimplex.single true else Junctions.fairCoin) = _
        rw [ite_eq_left h00]
      have hzF : (nullRowFair.cpt 0 (nullRowFair.paVal 0 x)).weights (x 0)
          = 0 := by
        rw [hF0, hx0]
        simp
      have hzT : (nullRowTrue.cpt 0 (nullRowTrue.paVal 0 x)).weights (x 0)
          = 0 := by
        rw [hT0, hx0]
        simp
      rw [hzF, hzT, zero_mul, zero_mul]

end Cslib.MachineLearning.DirectedMarkovPropertiesTests
