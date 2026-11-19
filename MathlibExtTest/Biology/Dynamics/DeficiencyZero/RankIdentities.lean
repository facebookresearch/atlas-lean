/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.DeficiencyZero.RankIdentities

/-! Tests for the deficiency rank identities: the isomerization `A ⇌ B` (deficiency zero; the
identities compute `dim 𝒮 = 1`), the network `0 ← A → 2A` (deficiency one: an explicit
nonzero vector in `ker Y ∩ Δ` makes the deficiency nonzero), a self-reaction `A → A` (no
linkage edge), the empty network, and the exact `range src ∪ range prod` / `fromRel` form
with the stoichiometric-matrix rank. -/

open Module

namespace MathlibExtTest.Biology.Dynamics.DeficiencyZero.RankIdentities

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork
open MathlibExt.Biology.Dynamics.DeficiencyZero

/-! ### `A ⇌ B`: deficiency zero -/

/-- The isomerization `A ⇌ B` on species `Fin 2`: reaction `0` is `A → B`, reaction `1` is
`B → A`. -/
def isomer : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

/-- Complex compositions of `isomer`: complex `0` is `A`, complex `1` is `B`. -/
def isomerY : Fin 2 → Fin 2 → ℕ := ![![1, 0], ![0, 1]]

lemma isomer_adj : ∀ c c' : Fin 2, (⊤ : SimpleGraph (Fin 2)).Adj c c' ↔
    c ≠ c' ∧ ∃ r, (![0, 1] r = c ∧ ![1, 0] r = c') ∨ (![0, 1] r = c' ∧ ![1, 0] r = c) := by
  decide

lemma isomer_src : ∀ r, isomer.src r = isomerY (![0, 1] r) := by decide
lemma isomer_prod : ∀ r, isomer.prod r = isomerY (![1, 0] r) := by decide

lemma isomerY_linearIndependent : LinearIndependent ℝ fun c i => (isomerY c i : ℝ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Fin.sum_univ_two, isomerY] at h0 h1
  fin_cases c <;> simp [h0, h1]

lemma natCard_top_fin_two : Nat.card (⊤ : SimpleGraph (Fin 2)).ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨SimpleGraph.connected_top.preconnected.subsingleton_connectedComponent,
    ⟨SimpleGraph.connectedComponentMk _ 0⟩⟩

/-- Deficiency zero for `A ⇌ B`, from linear independence of `A`, `B`. -/
example : (Fintype.card (Fin 2) : ℤ) - Nat.card (⊤ : SimpleGraph (Fin 2)).ConnectedComponent -
    finrank ℝ isomer.stoichiometricSubspace = 0 :=
  isomer.card_sub_card_sub_finrank_eq_zero_of_linearIndependent isomerY ![0, 1] ![1, 0]
    isomer_src isomer_prod ⊤ isomer_adj isomerY_linearIndependent

/-- The identities compute the stoichiometric dimension of `A ⇌ B`: `s = n - ℓ = 2 - 1`. -/
example : finrank ℝ isomer.stoichiometricSubspace = 1 := by
  have h := isomer.card_sub_card_sub_finrank_eq_zero_of_linearIndependent isomerY ![0, 1]
    ![1, 0] isomer_src isomer_prod ⊤ isomer_adj isomerY_linearIndependent
  rw [natCard_top_fin_two, Fintype.card_fin] at h
  omega

/-- The complex-space reaction span of `A ⇌ B` has dimension `n - ℓ = 1`. -/
example : finrank ℝ (Submodule.span ℝ (Set.range fun r =>
    (Pi.single (![1, 0] r) 1 - Pi.single (![0, 1] r) 1 : Fin 2 → ℝ))) = 1 := by
  rw [finrank_span_incidence_eq (![0, 1] : Fin 2 → Fin 2) ![1, 0] ⊤ isomer_adj,
    natCard_top_fin_two, Fintype.card_fin]

/-- Rank of the stoichiometric matrix of `A ⇌ B`. -/
example : (Matrix.of fun i r => (isomer.prod r i : ℝ) - isomer.src r i).rank = 1 := by
  rw [rank_stoichiometricMatrix_eq_finrank]
  have h := isomer.card_sub_card_sub_finrank_eq_zero_of_linearIndependent isomerY ![0, 1]
    ![1, 0] isomer_src isomer_prod ⊤ isomer_adj isomerY_linearIndependent
  rw [natCard_top_fin_two, Fintype.card_fin] at h
  omega

/-- Exact form for `A ⇌ B`: complexes `range src ∪ range prod`, linkage graph `fromRel`,
deficiency in rank form, and nonnegativity. -/
example : 0 ≤ (Nat.card ↥(Set.range isomer.src ∪ Set.range isomer.prod) : ℤ) -
    Nat.card (SimpleGraph.fromRel fun c c' : ↥(Set.range isomer.src ∪ Set.range isomer.prod) =>
      ∃ r, isomer.src r = c ∧ isomer.prod r = c').ConnectedComponent -
    (Matrix.of fun i r => (isomer.prod r i : ℝ) - isomer.src r i).rank :=
  (isomer.complexes_linkage_rank_nonneg _ rfl _ rfl).2

/-! ### `0 ← A → 2A`: deficiency one -/

/-- One species, reactions `A → 2A` (reaction `0`) and `A → 0` (reaction `1`). -/
def branch : ReactionNetwork (Fin 1) (Fin 2) where
  src := ![![1], ![1]]
  prod := ![![2], ![0]]

/-- Complexes of `branch`: `0 = ∅`, `1 = A`, `2 = 2A`. -/
def branchY : Fin 3 → Fin 1 → ℕ := ![![0], ![1], ![2]]

lemma branch_src : ∀ r, branch.src r = branchY (![1, 1] r) := by decide
lemma branch_prod : ∀ r, branch.prod r = branchY (![2, 0] r) := by decide

/-- The linkage graph of `branch`: `A` is adjacent to `∅` and to `2A`. -/
def branchG : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun c c' => c = 1 ∧ c' ≠ 1

instance : DecidableRel branchG.Adj := fun _ _ => by
  unfold branchG; infer_instance

lemma branch_adj : ∀ c c' : Fin 3, branchG.Adj c c' ↔
    c ≠ c' ∧ ∃ r, (![1, 1] r = c ∧ ![2, 0] r = c') ∨ (![1, 1] r = c' ∧ ![2, 0] r = c) := by
  decide

/-- `e_∅ - 2 e_A + e_{2A}` lies in `ker Y ∩ Δ` and is nonzero, so `branch` does not have
deficiency zero. -/
example : (Fintype.card (Fin 3) : ℤ) - Nat.card branchG.ConnectedComponent -
    finrank ℝ branch.stoichiometricSubspace ≠ 0 := by
  rw [Ne, branch.card_sub_card_sub_finrank_eq_zero_iff branchY ![1, 1] ![2, 0] branch_src
    branch_prod branchG branch_adj]
  intro h
  let v : Fin 3 → ℝ := ![1, -2, 1]
  have hv : v ∈ LinearMap.ker (Matrix.of fun i c => (branchY c i : ℝ)).mulVecLin ⊓
      Submodule.span ℝ (Set.range fun r =>
        (Pi.single (![2, 0] r) 1 - Pi.single (![1, 1] r) 1 : Fin 3 → ℝ)) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker]
      funext i
      fin_cases i
      simp [v, branchY, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · have h0 : (Pi.single (2 : Fin 3) 1 - Pi.single 1 1 : Fin 3 → ℝ) ∈ Submodule.span ℝ
          (Set.range fun r => (Pi.single (![2, 0] r) 1 - Pi.single (![1, 1] r) 1 :
            Fin 3 → ℝ)) := Submodule.subset_span ⟨0, rfl⟩
      have h1 : (Pi.single (0 : Fin 3) 1 - Pi.single 1 1 : Fin 3 → ℝ) ∈ Submodule.span ℝ
          (Set.range fun r => (Pi.single (![2, 0] r) 1 - Pi.single (![1, 1] r) 1 :
            Fin 3 → ℝ)) := Submodule.subset_span ⟨1, rfl⟩
      have hsum := Submodule.add_mem _ h0 h1
      have hvw : v = Pi.single 2 1 - Pi.single 1 1 + (Pi.single 0 1 - Pi.single 1 1) := by
        funext i
        fin_cases i <;> simp [v]
        norm_num
      rw [hvw]
      exact hsum
  rw [h, Submodule.mem_bot] at hv
  have := congrFun hv 0
  simp [v] at this

/-- Nonnegativity for `branch`. -/
example : 0 ≤ (Fintype.card (Fin 3) : ℤ) - Nat.card branchG.ConnectedComponent -
    finrank ℝ branch.stoichiometricSubspace :=
  branch.card_sub_card_sub_finrank_nonneg branchY ![1, 1] ![2, 0] branch_src branch_prod
    branchG branch_adj

/-! ### Boundary cases -/

/-- A self-reaction `A → A`: no linkage edge (`G = ⊥`), and the stoichiometric subspace is
zero, so the deficiency is `1 - 1 - 0 = 0`. -/
def selfLoop : ReactionNetwork (Fin 1) (Fin 1) where
  src := ![![1]]
  prod := ![![1]]

lemma selfLoop_adj : ∀ c c' : Fin 1, (⊥ : SimpleGraph (Fin 1)).Adj c c' ↔
    c ≠ c' ∧ ∃ r, (![0] r = c ∧ ![0] r = c') ∨ (![0] r = c' ∧ ![0] r = c) := by
  decide

example : (Fintype.card (Fin 1) : ℤ) - Nat.card (⊥ : SimpleGraph (Fin 1)).ConnectedComponent -
    finrank ℝ selfLoop.stoichiometricSubspace = 0 := by
  refine selfLoop.card_sub_card_sub_finrank_eq_zero_of_linearIndependent ![![1]] ![0] ![0]
    (by decide) (by decide) ⊥ selfLoop_adj ?_
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have := congrFun hg 0
  fin_cases c
  simpa using this

/-- The empty network (no reactions): no complexes, and the exact-form deficiency is
nonnegative (it is `0 - 0 - 0`). -/
def emptyNet : ReactionNetwork (Fin 2) Empty where
  src := Empty.elim
  prod := Empty.elim

example : 0 ≤ (Nat.card ↥(Set.range emptyNet.src ∪ Set.range emptyNet.prod) : ℤ) -
    Nat.card (SimpleGraph.fromRel fun c c' :
      ↥(Set.range emptyNet.src ∪ Set.range emptyNet.prod) =>
        ∃ r, emptyNet.src r = c ∧ emptyNet.prod r = c').ConnectedComponent -
    finrank ℝ emptyNet.stoichiometricSubspace :=
  emptyNet.complexes_linkage_finrank_nonneg _ rfl _ rfl

end MathlibExtTest.Biology.Dynamics.DeficiencyZero.RankIdentities
