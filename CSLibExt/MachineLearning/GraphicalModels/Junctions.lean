/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Canonical junctions: chain, fork and collider

The three ways two edges can meet at a middle node of a causal Bayesian network
(Pearl, Glymour and Jewell 2016, §2.2–2.4). In a chain `0 → 1 → 2` and in a fork `1 ← 0 → 2`,
conditioning on the middle node makes the end nodes independent, for every choice of tables;
this is the global Markov property (`BayesNet.condIndep_of_dSeparated`) applied to the
d-separation of the end nodes by the middle node. In a collider `0 → 2 ← 1` with independent
parents, conditioning on the collider can create dependence (Berkson's paradox, explaining
away): an explicit finite law shows this. Faithfulness is not assumed: the collider statement
is about one explicit law, not about every law on the graph.

## Main definitions

* `Junctions.chainPa`, `Junctions.forkPa`, `Junctions.colliderPa`: the three graphs on three nodes.
* `Junctions.berksonNet`: independent fair coins `X₀`, `X₁` and `X₂ = X₀ ∨ X₁`.

## Main results

* `Junctions.condIndep_chain`, `Junctions.condIndep_fork`: `X₀ ⫫ X₂ | X₁` on the chain and
  `X₁ ⫫ X₂ | X₀` on the fork, for all tables.
* `Junctions.berksonNet_marginal_collider`: `P(X₂ = true) = 3/4`.
* `Junctions.berksonNet_condIndep_parents`: `X₀ ⫫ X₁` in the collider law.
* `Junctions.berksonNet_not_condIndep_given_collider`: `¬ X₀ ⫫ X₁ | X₂`.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §2.2–2.4.
* J. Berkson, *Limitations of the application of fourfold table analysis to hospital data*,
  Biometrics Bulletin 2(3) (1946), 47–53.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

namespace Junctions

open Finset Convexity MetaMathlibExt.FiniteWeight

/-- The chain `0 → 1 → 2`: node `1` has parent `0`, node `2` has parent `1`. -/
def chainPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- The fork `1 ← 0 → 2`: nodes `1` and `2` both have the single parent `0`. -/
def forkPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {0}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- The collider `0 → 2 ← 1`: node `2` has parents `0` and `1`; nodes `0`, `1` have none. -/
def colliderPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => ∅
  | ⟨2, _⟩ => {0, 1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

theorem chain_edge {α : Type*} [Nonempty α]
    (cpt : (k : Fin 3) → (chainPa k → α) → StdSimplex ℝ α) {i j : Fin 3} :
    (BayesNet.mk chainPa cpt).Edge i j ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ chainPa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

theorem chain_dsep {α : Type*} [Nonempty α]
    (cpt : (k : Fin 3) → (chainPa k → α) → StdSimplex ℝ α) :
    (BayesNet.mk chainPa cpt).DSeparated {0} {2} {1} := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx
  subst hy
  unfold BayesNet.IsPath at hp
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  cases p with
  | nil => exact absurd hh (by decide)
  | cons a t =>
    cases t with
    | nil =>
      have e1 : [a].head? = some a := rfl
      have ha : (0 : Fin 3) = a := by
        have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
        simpa using h2
      subst ha
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        have e1 : [a, b].head? = some a := rfl
        have ha : (0 : Fin 3) = a := by
          have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
          simpa using h2
        subst ha
        have hadj : (BayesNet.mk chainPa cpt).Adj 0 b :=
          (List.isChain_cons_cons.1 hch).1
        have hb : b = 1 := by
          simp only [BayesNet.Adj, chain_edge] at hadj
          rcases hadj with (⟨-, rfl⟩ | ⟨h01, -⟩) | (⟨-, h01'⟩ | ⟨rfl, -⟩)
          · rfl
          · exact absurd h01 (by decide)
          · exact absurd h01' (by decide)
          · rfl
        subst hb
        exact absurd hlast (by decide)
      | cons c t3 =>
        cases t3 with
        | nil =>
          have e1 : [a, b, c].head? = some a := rfl
          have ha : (0 : Fin 3) = a := by
            have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          have hadj1 : (BayesNet.mk chainPa cpt).Adj 0 b :=
            (List.isChain_cons_cons.1 hch).1
          have hb : b = 1 := by
            simp only [BayesNet.Adj, chain_edge] at hadj1
            rcases hadj1 with (⟨-, rfl⟩ | ⟨h01, -⟩) | (⟨-, h01'⟩ | ⟨rfl, -⟩)
            · rfl
            · exact absurd h01 (by decide)
            · exact absurd h01' (by decide)
            · rfl
          subst hb
          have hc0 : c ≠ 0 := by
            intro hcon
            subst hcon
            simp at hnd
          have hadj2 : (BayesNet.mk chainPa cpt).Adj 1 c :=
            (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
          have hc : c = 2 := by
            simp only [BayesNet.Adj, chain_edge] at hadj2
            rcases hadj2 with (⟨h10, -⟩ | ⟨-, rfl⟩) | (⟨hc0', -⟩ | ⟨-, h12⟩)
            · exact absurd h10 (by decide)
            · rfl
            · exact absurd hc0' hc0
            · exact absurd h12 (by decide)
          subst hc
          refine ⟨0, by decide, Or.inr ⟨by simp only [chain_edge]; decide, by simp⟩⟩
        | cons d l =>
          have e1 : (a :: b :: c :: d :: l).head? = some a := rfl
          have ha : (0 : Fin 3) = a := by
            have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          fin_cases b <;> fin_cases c <;> fin_cases d <;> simp at hnd

theorem fork_edge {α : Type*} [Nonempty α]
    (cpt : (k : Fin 3) → (forkPa k → α) → StdSimplex ℝ α) {i j : Fin 3} :
    (BayesNet.mk forkPa cpt).Edge i j ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ forkPa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

theorem fork_dsep {α : Type*} [Nonempty α]
    (cpt : (k : Fin 3) → (forkPa k → α) → StdSimplex ℝ α) :
    (BayesNet.mk forkPa cpt).DSeparated {1} {2} {0} := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx
  subst hy
  unfold BayesNet.IsPath at hp
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  cases p with
  | nil => exact absurd hh (by decide)
  | cons a t =>
    cases t with
    | nil =>
      have e1 : [a].head? = some a := rfl
      have ha : (1 : Fin 3) = a := by
        have h2 : some (1 : Fin 3) = some a := hh.symm.trans e1
        simpa using h2
      subst ha
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        have e1 : [a, b].head? = some a := rfl
        have ha : (1 : Fin 3) = a := by
          have h2 : some (1 : Fin 3) = some a := hh.symm.trans e1
          simpa using h2
        subst ha
        have hadj : (BayesNet.mk forkPa cpt).Adj 1 b :=
          (List.isChain_cons_cons.1 hch).1
        have hb : b = 0 := by
          simp only [BayesNet.Adj, fork_edge] at hadj
          rcases hadj with (⟨h10, -⟩ | ⟨h10', -⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact absurd h10 (by decide)
          · exact absurd h10' (by decide)
          · rfl
          · rfl
        subst hb
        exact absurd hlast (by decide)
      | cons c t3 =>
        cases t3 with
        | nil =>
          have e1 : [a, b, c].head? = some a := rfl
          have ha : (1 : Fin 3) = a := by
            have h2 : some (1 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          have hadj1 : (BayesNet.mk forkPa cpt).Adj 1 b :=
            (List.isChain_cons_cons.1 hch).1
          have hb : b = 0 := by
            simp only [BayesNet.Adj, fork_edge] at hadj1
            rcases hadj1 with (⟨h10, -⟩ | ⟨h10', -⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩)
            · exact absurd h10 (by decide)
            · exact absurd h10' (by decide)
            · rfl
            · rfl
          subst hb
          have hc1 : c ≠ 1 := by
            intro hcon
            subst hcon
            simp at hnd
          have hadj2 : (BayesNet.mk forkPa cpt).Adj 0 c :=
            (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
          have hc : c = 2 := by
            simp only [BayesNet.Adj, fork_edge] at hadj2
            rcases hadj2 with (⟨-, hc1'⟩ | ⟨-, rfl⟩) | (⟨-, h01⟩ | ⟨-, h02⟩)
            · exact absurd hc1' hc1
            · rfl
            · exact absurd h01 (by decide)
            · exact absurd h02 (by decide)
          subst hc
          refine ⟨0, by decide, Or.inr ⟨by simp only [fork_edge]; decide, by simp⟩⟩
        | cons d l =>
          have e1 : (a :: b :: c :: d :: l).head? = some a := rfl
          have ha : (1 : Fin 3) = a := by
            have h2 : some (1 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          fin_cases b <;> fin_cases c <;> fin_cases d <;> simp at hnd

/-- **Chain junction**: for every choice of tables on the chain `0 → 1 → 2`, the end nodes are
conditionally independent given the middle node, `X₀ ⫫ X₂ | X₁`. -/
theorem condIndep_chain {α : Type*} [Fintype α] [Nonempty α]
    (cpt : (k : Fin 3) → (chainPa k → α) → StdSimplex ℝ α) :
    CondIndep (BayesNet.mk chainPa cpt).joint {0} {2} {1} := by
  exact (BayesNet.mk chainPa cpt).condIndep_of_dSeparated (chain_dsep cpt)

/-- **Fork junction**: for every choice of tables on the fork `1 ← 0 → 2`, the two children are
conditionally independent given the common parent, `X₁ ⫫ X₂ | X₀`. -/
theorem condIndep_fork {α : Type*} [Fintype α] [Nonempty α]
    (cpt : (k : Fin 3) → (forkPa k → α) → StdSimplex ℝ α) :
    CondIndep (BayesNet.mk forkPa cpt).joint {1} {2} {0} := by
  exact (BayesNet.mk forkPa cpt).condIndep_of_dSeparated (fork_dsep cpt)

/-- The fair coin on `Bool`. -/
noncomputable def fairCoin : StdSimplex ℝ Bool :=
  StdSimplex.duple (s := (1 / 2 : ℝ)) (t := 1 / 2) true false (by norm_num) (by norm_num)
    (by norm_num)

theorem fairCoin_weights (a : Bool) : fairCoin.weights a = 1 / 2 := by
  cases a <;> norm_num [fairCoin, StdSimplex.duple]

theorem single_weights_same (b : Bool) : (StdSimplex.single b).weights b = 1 := by
  simp [StdSimplex.single]

theorem single_weights_ne {a d : Bool} (h : a ≠ d) :
    (StdSimplex.single d).weights a = 0 := by
  simp [StdSimplex.single, h, Ne.symm h]

/-- The explicit collider law (Berkson's paradox, explaining away): `X₀` and `X₁` are
independent fair coins and `X₂ = X₀ ∨ X₁` (deterministic: node `2` is `true` exactly when
one of its parents `0`, `1` is). -/
noncomputable def berksonNet : BayesNet Bool 3 where
  pa := colliderPa
  cpt k u := if (k : ℕ) = 2 then StdSimplex.single (decide (∃ i, u i = true)) else fairCoin

theorem berkson_cpt_0 (u : berksonNet.pa 0 → Bool) (a : Bool) :
    (berksonNet.cpt 0 u).weights a = 1 / 2 := by
  have h : berksonNet.cpt 0 u = fairCoin := rfl
  rw [h]
  exact fairCoin_weights a

theorem berkson_cpt_1 (u : berksonNet.pa 1 → Bool) (a : Bool) :
    (berksonNet.cpt 1 u).weights a = 1 / 2 := by
  have h : berksonNet.cpt 1 u = fairCoin := rfl
  rw [h]
  exact fairCoin_weights a

theorem berkson_cpt_2 (u : berksonNet.pa 2 → Bool) (a : Bool) :
    (berksonNet.cpt 2 u).weights a =
      if decide (∃ i, u i = true) = a then 1 else 0 := by
  have h : berksonNet.cpt 2 u = StdSimplex.single (decide (∃ i, u i = true)) := rfl
  rw [h]
  by_cases hda : decide (∃ i, u i = true) = a
  · rw [ite_eq_left hda, ← hda, StdSimplex.weights_single, Finsupp.single_eq_same]
  · rw [ite_eq_right hda, StdSimplex.weights_single]
    exact Finsupp.single_eq_of_ne (Ne.symm hda)

theorem berkson_exists_iff (x : Fin 3 → Bool) (h : ((2 : Fin 3) : ℕ) ≤ 3) :
    (∃ i : berksonNet.pa 2, x (Fin.castLE h i) = true) ↔
      (x 0 = true ∨ x 1 = true) := by
  have hfin : ∀ j : Fin ((2 : Fin 3) : ℕ),
      j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    decide
  constructor
  · rintro ⟨i, hi⟩
    rcases hfin i with h2 | h2
    · left
      have e : Fin.castLE h i = 0 := by rw [h2]; rfl
      rw [e] at hi
      exact hi
    · right
      have e : Fin.castLE h i = 1 := by rw [h2]; rfl
      rw [e] at hi
      exact hi
  · rintro (h0 | h1)
    · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
      show x (Fin.castLE h (⟨0, by decide⟩ : Fin ((2 : Fin 3) : ℕ))) = true
      have e : Fin.castLE h (⟨0, by decide⟩ : Fin ((2 : Fin 3) : ℕ)) = 0 := rfl
      rw [e]
      exact h0
    · refine ⟨⟨⟨1, by decide⟩, by decide⟩, ?_⟩
      show x (Fin.castLE h (⟨1, by decide⟩ : Fin ((2 : Fin 3) : ℕ))) = true
      have e : Fin.castLE h (⟨1, by decide⟩ : Fin ((2 : Fin 3) : ℕ)) = 1 := rfl
      rw [e]
      exact h1

theorem berksonNet_joint (x : Fin 3 → Bool) :
    berksonNet.joint x =
      if decide (x 0 = true ∨ x 1 = true) = x 2 then 1 / 4 else 0 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three, berkson_cpt_0, berkson_cpt_1,
    berkson_cpt_2]
  have hiff : (∃ i : berksonNet.pa 2, (fun j => x (Fin.castLE (2 : Fin 3).2.le j)) i = true) ↔
      (x 0 = true ∨ x 1 = true) :=
    berkson_exists_iff x _
  have dcongr : decide (∃ i : berksonNet.pa 2,
      (fun j => x (Fin.castLE (2 : Fin 3).2.le j)) i = true) =
      decide (x 0 = true ∨ x 1 = true) := by
    by_cases hP : (∃ i : berksonNet.pa 2, (fun j => x (Fin.castLE (2 : Fin 3).2.le j)) i = true)
    · have hQ : (x 0 = true ∨ x 1 = true) := hiff.mp hP
      rw [decide_eq_true hP, decide_eq_true hQ]
    · have hQ : ¬ (x 0 = true ∨ x 1 = true) := fun hQ => hP (hiff.mpr hQ)
      rw [decide_eq_false hP, decide_eq_false hQ]
  rw [dcongr]
  by_cases h2 : decide (x 0 = true ∨ x 1 = true) = x 2
  · rw [ite_eq_left h2, ite_eq_left h2]
    norm_num
  · rw [ite_eq_right h2, ite_eq_right h2]
    norm_num

theorem berkson_joint_TTT : berksonNet.joint ![true, true, true] = 1 / 4 := by
  rw [berksonNet_joint,
    ite_eq_left (show decide (![true, true, true] 0 = true ∨
      ![true, true, true] 1 = true) = ![true, true, true] 2 from by decide)]

theorem berkson_joint_TFT : berksonNet.joint ![true, false, true] = 1 / 4 := by
  rw [berksonNet_joint,
    ite_eq_left (show decide (![true, false, true] 0 = true ∨
      ![true, false, true] 1 = true) = ![true, false, true] 2 from by decide)]

theorem berkson_joint_FTT : berksonNet.joint ![false, true, true] = 1 / 4 := by
  rw [berksonNet_joint,
    ite_eq_left (show decide (![false, true, true] 0 = true ∨
      ![false, true, true] 1 = true) = ![false, true, true] 2 from by decide)]

theorem berkson_joint_FFT : berksonNet.joint ![false, false, true] = 0 := by
  rw [berksonNet_joint,
    ite_eq_right (show ¬ decide (![false, false, true] 0 = true ∨
      ![false, false, true] 1 = true) = ![false, false, true] 2 from by decide)]

theorem berkson_marginal_2 :
    marginal berksonNet.joint {2} ![true, true, true] = 3 / 4 := by
  rw [marginal, Finset.sum_filter]
  have huniv : (Finset.univ : Finset (Fin 3 → Bool)) =
      {![true, true, true], ![true, true, false], ![true, false, true], ![true, false, false],
       ![false, true, true], ![false, true, false], ![false, false, true], ![false, false,
           false]} := by
    decide
  rw [huniv,
    Finset.sum_insert (show ![true, true, true] ∉
      ({![true, true, false], ![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, true, false] ∉
      ({![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, true] ∉
      ({![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, false] ∉
      ({![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, true] ∉
      ({![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, false] ∉
      ({![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, false, true] ∉
      ({![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_singleton]
  have hTTT : (∀ v ∈ ({2} : Set (Fin 3)), (![true, true, true] : Fin 3 → Bool) v = ![true, true,
      true] v) := by
    decide
  have hTTF : ¬ (∀ v ∈ ({2} : Set (Fin 3)), (![true, true, false] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  have hTFT : (∀ v ∈ ({2} : Set (Fin 3)), (![true, false, true] : Fin 3 → Bool) v = ![true, true,
      true] v) := by
    decide
  have hTFF : ¬ (∀ v ∈ ({2} : Set (Fin 3)), (![true, false, false] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  have hFTT : (∀ v ∈ ({2} : Set (Fin 3)), (![false, true, true] : Fin 3 → Bool) v = ![true, true,
      true] v) := by
    decide
  have hFTF : ¬ (∀ v ∈ ({2} : Set (Fin 3)), (![false, true, false] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  have hFFT : (∀ v ∈ ({2} : Set (Fin 3)), (![false, false, true] : Fin 3 → Bool) v = ![true, true,
      true] v) := by
    decide
  have hFFF : ¬ (∀ v ∈ ({2} : Set (Fin 3)), (![false, false, false] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  rw [ite_eq_left hTTT, ite_eq_right hTTF, ite_eq_left hTFT, ite_eq_right hTFF, ite_eq_left hFTT,
      ite_eq_right hFTF, ite_eq_left hFFT, ite_eq_right hFFF]
  rw [berkson_joint_TTT, berkson_joint_TFT, berkson_joint_FTT, berkson_joint_FFT]
  norm_num

theorem berkson_marginal_02 :
    marginal berksonNet.joint ({0} ∪ {2}) ![true, true, true] = 1 / 2 := by
  rw [marginal, Finset.sum_filter]
  have huniv : (Finset.univ : Finset (Fin 3 → Bool)) =
      {![true, true, true], ![true, true, false], ![true, false, true], ![true, false, false],
       ![false, true, true], ![false, true, false], ![false, false, true], ![false, false,
           false]} := by
    decide
  rw [huniv,
    Finset.sum_insert (show ![true, true, true] ∉
      ({![true, true, false], ![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, true, false] ∉
      ({![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, true] ∉
      ({![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, false] ∉
      ({![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, true] ∉
      ({![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, false] ∉
      ({![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, false, true] ∉
      ({![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_singleton]
  have hTTT : (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![true, true, true] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  have hTTF : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![true, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFT : (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![true, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFF : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![true, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTT : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![false, true,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTF : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![false, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFT : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![false, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFF : ¬ (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), (![false, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  rw [ite_eq_left hTTT, ite_eq_right hTTF, ite_eq_left hTFT, ite_eq_right hTFF, ite_eq_right hFTT,
      ite_eq_right hFTF, ite_eq_right hFFT, ite_eq_right hFFF]
  rw [berkson_joint_TTT, berkson_joint_TFT]
  norm_num

theorem berkson_marginal_12 :
    marginal berksonNet.joint ({1} ∪ {2}) ![true, true, true] = 1 / 2 := by
  rw [marginal, Finset.sum_filter]
  have huniv : (Finset.univ : Finset (Fin 3 → Bool)) =
      {![true, true, true], ![true, true, false], ![true, false, true], ![true, false, false],
       ![false, true, true], ![false, true, false], ![false, false, true], ![false, false,
           false]} := by
    decide
  rw [huniv,
    Finset.sum_insert (show ![true, true, true] ∉
      ({![true, true, false], ![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, true, false] ∉
      ({![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, true] ∉
      ({![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, false] ∉
      ({![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, true] ∉
      ({![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, false] ∉
      ({![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, false, true] ∉
      ({![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_singleton]
  have hTTT : (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![true, true, true] : Fin 3 → Bool) v = ![true,
      true, true] v) := by
    decide
  have hTTF : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![true, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFT : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![true, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFF : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![true, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTT : (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![false, true,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTF : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![false, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFT : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![false, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFF : ¬ (∀ v ∈ (({1} ∪ {2} : Set (Fin 3))), (![false, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  rw [ite_eq_left hTTT, ite_eq_right hTTF, ite_eq_right hTFT, ite_eq_right hTFF, ite_eq_left hFTT,
      ite_eq_right hFTF, ite_eq_right hFFT, ite_eq_right hFFF]
  rw [berkson_joint_TTT, berkson_joint_FTT]
  norm_num

theorem berkson_marginal_012 :
    marginal berksonNet.joint ({0} ∪ {1} ∪ {2}) ![true, true, true] = 1 / 4 := by
  rw [marginal, Finset.sum_filter]
  have huniv : (Finset.univ : Finset (Fin 3 → Bool)) =
      {![true, true, true], ![true, true, false], ![true, false, true], ![true, false, false],
       ![false, true, true], ![false, true, false], ![false, false, true], ![false, false,
           false]} := by
    decide
  rw [huniv,
    Finset.sum_insert (show ![true, true, true] ∉
      ({![true, true, false], ![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, true, false] ∉
      ({![true, false, true], ![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, true] ∉
      ({![true, false, false],
        ![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![true, false, false] ∉
      ({![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, true] ∉
      ({![false, true, false], ![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, true, false] ∉
      ({![false, false, true],
        ![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_insert (show ![false, false, true] ∉
      ({![false, false, false]} : Finset (Fin 3 → Bool)) from by decide),
    Finset.sum_singleton]
  have hTTT : (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![true, true,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTTF : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![true, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFT : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![true, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hTFF : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![true, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTT : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![false, true,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFTF : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![false, true,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFT : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![false, false,
      true] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  have hFFF : ¬ (∀ v ∈ (({0} ∪ {1} ∪ {2} : Set (Fin 3))), (![false, false,
      false] : Fin 3 → Bool) v = ![true, true, true] v) := by
    decide
  rw [ite_eq_left hTTT, ite_eq_right hTTF, ite_eq_right hTFT, ite_eq_right hTFF,
      ite_eq_right hFTT, ite_eq_right hFTF, ite_eq_right hFFT, ite_eq_right hFFF]
  rw [berkson_joint_TTT]
  norm_num

theorem berkson_edge {i j : Fin 3} :
    berksonNet.Edge i j ↔ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ colliderPa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

theorem berkson_dsep_empty : berksonNet.DSeparated {0} {1} ∅ := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx
  subst hy
  unfold BayesNet.IsPath at hp
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  cases p with
  | nil => exact absurd hh (by decide)
  | cons a t =>
    cases t with
    | nil =>
      have e1 : [a].head? = some a := rfl
      have ha : (0 : Fin 3) = a := by
        have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
        simpa using h2
      subst ha
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        have e1 : [a, b].head? = some a := rfl
        have ha : (0 : Fin 3) = a := by
          have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
          simpa using h2
        subst ha
        have hadj : berksonNet.Adj 0 b :=
          (List.isChain_cons_cons.1 hch).1
        have hb : b = 2 := by
          simp only [BayesNet.Adj, berkson_edge] at hadj
          rcases hadj with (⟨-, rfl⟩ | ⟨h01, -⟩) | (⟨-, h02⟩ | ⟨-, h02'⟩)
          · rfl
          · exact absurd h01 (by decide)
          · exact absurd h02 (by decide)
          · exact absurd h02' (by decide)
        subst hb
        exact absurd hlast (by decide)
      | cons c t3 =>
        cases t3 with
        | nil =>
          have e1 : [a, b, c].head? = some a := rfl
          have ha : (0 : Fin 3) = a := by
            have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          have hadj1 : berksonNet.Adj 0 b :=
            (List.isChain_cons_cons.1 hch).1
          have hb : b = 2 := by
            simp only [BayesNet.Adj, berkson_edge] at hadj1
            rcases hadj1 with (⟨-, rfl⟩ | ⟨h01, -⟩) | (⟨-, h02⟩ | ⟨-, h02'⟩)
            · rfl
            · exact absurd h01 (by decide)
            · exact absurd h02 (by decide)
            · exact absurd h02' (by decide)
          subst hb
          have hc0 : c ≠ 0 := by
            intro hcon
            subst hcon
            simp at hnd
          have hadj2 : berksonNet.Adj 2 c :=
            (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
          have hc : c = 1 := by
            simp only [BayesNet.Adj, berkson_edge] at hadj2
            rcases hadj2 with (⟨h20, -⟩ | ⟨h21, -⟩) | (⟨hc0', -⟩ | ⟨rfl, -⟩)
            · exact absurd h20 (by decide)
            · exact absurd h21 (by decide)
            · exact absurd hc0' hc0
            · rfl
          subst hc
          refine ⟨0, by decide, Or.inl ⟨by simp only [berkson_edge]; decide,
              by simp only [berkson_edge]; decide, by simp⟩⟩
        | cons d l =>
          have e1 : (a :: b :: c :: d :: l).head? = some a := rfl
          have ha : (0 : Fin 3) = a := by
            have h2 : some (0 : Fin 3) = some a := hh.symm.trans e1
            simpa using h2
          subst ha
          fin_cases b <;> fin_cases c <;> fin_cases d <;> simp at hnd

/-- The conditioning event `X₂ = true` has positive probability: `P(X₂ = true) = 3/4`. -/
theorem berksonNet_marginal_collider :
    marginal berksonNet.joint {2} ![true, true, true] = 3 / 4 := by
  exact berkson_marginal_2

/-- In the collider law the parents are independent, `X₀ ⫫ X₁` (conditioning on nothing). -/
theorem berksonNet_condIndep_parents : CondIndep berksonNet.joint {0} {1} ∅ := by
  exact berksonNet.condIndep_of_dSeparated berkson_dsep_empty

/-- **Collider junction (Berkson's paradox)**: conditioning on the collider makes the
independent parents dependent, `¬ X₀ ⫫ X₁ | X₂`: at `x = (true, true, true)`,
`P(X₀, X₁, X₂) P(X₂) = 1/4 · 3/4 ≠ 1/2 · 1/2 = P(X₀, X₂) P(X₁, X₂)`. -/
theorem berksonNet_not_condIndep_given_collider :
    ¬ CondIndep berksonNet.joint {0} {1} {2} := by
  intro h
  have hTTT := h ![true, true, true]
  rw [berkson_marginal_012, berkson_marginal_2, berkson_marginal_02,
    berkson_marginal_12] at hTTT
  norm_num at hTTT

end Junctions

end Cslib.MachineLearning.GraphicalModels
