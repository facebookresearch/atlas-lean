/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Tests for the back-door and front-door adjustments

* Back-door: the network `U → X`, `U → W`, `X → Y`, `W → Y` (nodes `0, 1, 2, 3`) on `Bool`,
  every table giving both values positive probability. The set `Z = {W}` meets the back-door
  criterion for the effect of `X` on `Y`: `W` is not a descendant of `X`, and the only back-door
  path `X ← U → W → Y` is blocked at `W`. `W` comes after `X` in the topological order, so this
  is not covered by the adjustment for predecessors of the treatment.
* Front-door: the network `U → X → M → Y`, `U → Y` (nodes `0, 1, 2, 3`), with the confounder
  `U` of `X` and `Y`: the set `{M}` meets the three front-door conditions.
* The truncated factorization for an intervention on a set of nodes.
-/

@[expose] public section

namespace Cslib.MachineLearning.CausalAdjustmentTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The distribution on `Bool` with `P(true) = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, StdSimplex.duple]

/-- The parents: `U → X`, `U → W`, `X → Y`, `W → Y`. -/
def bdPa : (k : Fin 4) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {0}
  | ⟨3, _⟩ => {1, 2}
  | ⟨_ + 4, h⟩ => absurd h (by omega)

/-- Each node is `true` with probability `3/4` if all its parents are `true` and `1/4`
otherwise. -/
noncomputable def bdNet : BayesNet Bool 4 where
  pa := bdPa
  cpt _ u := if ∀ i, u i = true then coin (3 / 4) (by norm_num) (by norm_num)
    else coin (1 / 4) (by norm_num) (by norm_num)

theorem bd_edge {i j : Fin 4} : bdNet.Edge i j ↔
    ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 3) ∨
      ((i : ℕ) = 2 ∧ (j : ℕ) = 3) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ bdPa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

theorem bd_cpt_pos (k : Fin 4) (u : bdNet.pa k → Bool) (a : Bool) :
    0 < (bdNet.cpt k u).weights a := by
  simp only [bdNet]
  split_ifs <;> cases a <;> simp [coin_true, coin_false] <;> norm_num

theorem bd_joint_pos (x : Fin 4 → Bool) : 0 < bdNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  exact prod_pos fun k _ => bd_cpt_pos k _ _

/-- The descendants of `X` are `X` and `Y`. -/
theorem bd_desc {j : Fin 4} (h : bdNet.IsDescendant 1 j) : (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by
  unfold BayesNet.IsDescendant at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hE ih => rw [bd_edge] at hE; omega

/-- `{W}` blocks every back-door path from `X` to `Y`. -/
theorem bd_block : ∀ l, bdNet.IsPath 1 3 l → (∃ h : 1 < l.length, bdNet.Edge l[1] 1) →
    bdNet.PathBlocked ((({2} : Finset (Fin 4))) : Set (Fin 4)) l := by
  intro l hl ⟨h1, hE⟩
  obtain ⟨hnd, hch, hh, hlast⟩ := hl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp at h1
  · simp at h1
  · simp at hh hlast
    subst hh hlast
    simp [bd_edge] at hE
  · simp at hh hlast
    subst hh hlast
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, bd_edge] at hE
    have hb : b = 0 := Fin.ext (by omega)
    subst hb
    rcases (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1 with h | h <;>
      simp [bd_edge] at h
  · simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, bd_edge] at hE
    have hb : b = 0 := Fin.ext (by omega)
    subst hb
    have hc1 : c ≠ 1 := fun h => by subst h; simp at hnd
    have hd0 : d ≠ 0 := fun h => by subst h; simp at hnd
    have hc : c = 2 := by
      rcases (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1 with h | h <;>
        rw [bd_edge] at h
      · have : (c : ℕ) ≠ 1 := fun h' => hc1 (Fin.ext h')
        exact Fin.ext (by omega)
      · omega
    subst hc
    refine ⟨1, by simp, Or.inr ⟨fun h => ?_, by simp⟩⟩
    have h2 := h.2
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, bd_edge] at h2
    exact hd0 (Fin.ext (by omega))

/-- **Non-vacuity** of the back-door adjustment with an adjustment set `{W}` that follows the
treatment in the topological order: `P(Y = true | do(X = true))` is
`∑_w P(W = w) P(Y = true | X = true, W = w)`. -/
example :
    ∑ x with x 3 = true, (bdNet.intervene 1 true).joint x =
      ∑ z : ({2} : Finset (Fin 4)) → Bool,
        (∑ x with (fun i : ({2} : Finset (Fin 4)) => x i) = z, bdNet.joint x) *
        ((∑ x with x 1 = true ∧ x 3 = true ∧ (fun i : ({2} : Finset (Fin 4)) => x i) = z,
            bdNet.joint x) /
          ∑ x with x 1 = true ∧ (fun i : ({2} : Finset (Fin 4)) => x i) = z, bdNet.joint x) := by
  refine bdNet.backdoor_adjustment 1 3 {2} true true (by decide) (by decide) ?_ bd_block ?_
  · intro z hz h
    rw [mem_singleton] at hz
    subst hz
    have := bd_desc h
    simp at this
  · intro z _
    refine ne_of_gt (sum_pos (fun x _ => bd_joint_pos x)
      ⟨fun i => if h : i ∈ ({2} : Finset (Fin 4)) then z ⟨i, h⟩ else true, ?_⟩)
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨by simp, funext fun i => ?_⟩
    simp [i.2]

/-- The truncated factorization for a set: after `do(X = true, W = true)`, an assignment with
`W = false` has probability `0`. -/
example : (bdNet.mutilateSet {1, 2} fun _ => true).joint ![true, true, false, true] = 0 := by
  rw [BayesNet.joint_mutilateSet]
  exact prod_eq_zero (mem_univ 2) (by simp)

/-! ### Front-door -/

/-- The parents: `U → X`, `X → M`, `U → Y`, `M → Y`. -/
def fdPa : (k : Fin 4) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}
  | ⟨3, _⟩ => {0, 2}
  | ⟨_ + 4, h⟩ => absurd h (by omega)

/-- Each node is `true` with probability `3/4` if all its parents are `true` and `1/4`
otherwise. -/
noncomputable def fdNet : BayesNet Bool 4 where
  pa := fdPa
  cpt _ u := if ∀ i, u i = true then coin (3 / 4) (by norm_num) (by norm_num)
    else coin (1 / 4) (by norm_num) (by norm_num)

theorem fd_edge {i j : Fin 4} : fdNet.Edge i j ↔
    ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = 3) ∨
      ((i : ℕ) = 2 ∧ (j : ℕ) = 3) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ fdPa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

theorem fd_joint_pos (x : Fin 4 → Bool) : 0 < fdNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  refine prod_pos fun k _ => ?_
  simp only [fdNet]
  split_ifs <;> cases x k <;> simp [coin_true, coin_false] <;> norm_num

/-- **Non-vacuity** of the front-door adjustment: `M` mediates the whole effect of `X` on `Y`,
which are confounded by `U`. -/
example :
    ∑ x with x 3 = true, (fdNet.intervene 1 true).joint x =
      ∑ m : ({2} : Finset (Fin 4)) → Bool,
        ((∑ x with x 1 = true ∧ (fun i : ({2} : Finset (Fin 4)) => x i) = m, fdNet.joint x) /
            ∑ x with x 1 = true, fdNet.joint x) *
          ∑ a' : Bool,
            ((∑ x with x 1 = a' ∧ x 3 = true ∧ (fun i : ({2} : Finset (Fin 4)) => x i) = m,
                fdNet.joint x) /
                ∑ x with x 1 = a' ∧ (fun i : ({2} : Finset (Fin 4)) => x i) = m, fdNet.joint x) *
              ∑ x with x 1 = a', fdNet.joint x := by
  refine fdNet.frontdoor_adjustment 1 3 {2} true true (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_
  · -- every directed path from `X` to `Y` passes through `M`
    intro l hl hh hlast
    refine ⟨2, mem_singleton_self 2, ?_⟩
    rcases l with _ | ⟨a, _ | ⟨q, l⟩⟩
    · simp at hh
    · simp at hh hlast
      exact absurd (hh.symm.trans hlast) (by decide)
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      have h := (List.isChain_cons_cons.1 hl).1
      rw [fd_edge] at h
      have hq : q = 2 := Fin.ext (by omega)
      simp [hq]
  · -- no open back-door path from `X` to `M`
    intro m hm l hl ⟨h1, hE⟩
    rw [mem_singleton] at hm
    subst hm
    obtain ⟨hnd, hch, hh, hlast⟩ := hl
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
    · simp at h1
    · simp at h1
    · simp at hh hlast
      subst hh hlast
      simp [fd_edge] at hE
    · simp at hh hlast
      subst hh hlast
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, fd_edge] at hE
      have hb : b = 0 := Fin.ext (by omega)
      subst hb
      rcases (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1 with h | h <;>
        simp [fd_edge] at h
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, fd_edge] at hE
      have hb : b = 0 := Fin.ext (by omega)
      subst hb
      have hc1 : c ≠ 1 := fun h => by subst h; simp at hnd
      have hc : c = 3 := by
        rcases (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1 with h | h <;>
          rw [fd_edge] at h
        · have : (c : ℕ) ≠ 1 := fun h' => hc1 (Fin.ext h')
          exact Fin.ext (by omega)
        · omega
      subst hc
      have hd := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1
        (List.isChain_cons_cons.1 hch).2).2).1
      refine ⟨1, by simp, Or.inl ⟨by simp [fd_edge], ?_, by simp⟩⟩
      simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rcases hd with h | h
      · simp [fd_edge] at h
      · exact h
  · -- every back-door path from `M` to `Y` is blocked by `{X}`
    intro m hm l hl ⟨h1, hE⟩
    rw [mem_singleton] at hm
    subst hm
    obtain ⟨-, -, hh, hlast⟩ := hl
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at h1
    · simp at h1
    · simp at hh hlast
      subst hh hlast
      simp [fd_edge] at hE
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, fd_edge] at hE
      have hb : b = 1 := Fin.ext (by omega)
      subst hb
      refine ⟨0, by simp, Or.inr ⟨fun h => ?_, by simp⟩⟩
      have h1' := h.1
      simp [fd_edge] at h1'
  · -- positivity
    intro a' m
    refine ne_of_gt (sum_pos (fun x _ => fd_joint_pos x)
      ⟨fun i => if h : i ∈ ({2} : Finset (Fin 4)) then m ⟨i, h⟩ else a', ?_⟩)
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨by simp, funext fun i => ?_⟩
    simp [i.2]

end Cslib.MachineLearning.CausalAdjustmentTests
