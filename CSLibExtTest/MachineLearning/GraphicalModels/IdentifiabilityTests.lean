/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import CSLibExtTest.MachineLearning.GraphicalModels.CausalAdjustmentTests
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tests for identifiability

* A functional that is not identified: the identity on `Bool` with a constant observation.
* Non-vacuity of `BayesNet.backdoorClass`: the two-node network `X → Y` on `Bool` with
  fair-coin tables (built with `StdSimplex.duple`) belongs to the back-door class with the empty
  adjustment set (no path enters `X`, which has no parents).
* Non-vacuity of `BayesNet.frontdoorClass`: the front-door network `fdNet` of
  `CausalAdjustmentTests` belongs to its front-door class, and `identifiedOn_frontdoorClass`
  applied to it.
-/

@[expose] public section

namespace Cslib.MachineLearning.IdentifiabilityTests

open Cslib.MachineLearning GraphicalModels BayesNet

noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Convexity.StdSimplex ℝ Bool :=
  Convexity.StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, Convexity.StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, Convexity.StdSimplex.duple]

def testPa : (k : Fin 2) → Finset (Fin k) :=
  Fin.cases (motive := fun k => Finset (Fin k)) ∅ (fun _ => {⟨0, Nat.succ_pos _⟩})

noncomputable def testNet : BayesNet Bool 2 where
  pa := testPa
  cpt := fun _ _ => coin (1 / 2) (by norm_num) (by norm_num)

theorem test_cpt_pos (k : Fin 2) (w : testNet.pa k → Bool) (v : Bool) :
    0 < (testNet.cpt k w).weights v := by
  simp only [testNet]
  cases v
  case false =>
    rw [coin_false]
    norm_num
  case true =>
    rw [coin_true]
    norm_num

theorem testNet_joint_pos (x : Fin 2 → Bool) : 0 < testNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  exact Finset.prod_pos fun k _ => test_cpt_pos k _ _

example : (⟨0, by decide⟩ : Fin 1) ∈ testPa 1 := by
  show (⟨0, by decide⟩ : Fin 1) ∈ ({⟨0, Nat.succ_pos _⟩} : Finset (Fin ↑(1 : Fin 2)))
  exact Finset.mem_singleton_self _

example : ¬ IdentifiedOn (Set.univ : Set Bool) (fun _ => ()) id := by
  intro h
  exact Bool.noConfusion (h true (Set.mem_univ true) false (Set.mem_univ false) rfl)

example : testNet ∈ backdoorClass testNet.pa 0 1 ∅ true := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · exact fun z hz => (Finset.notMem_empty z hz).elim
  · intro p _ hex
    obtain ⟨_, hedge⟩ := hex
    obtain ⟨hlt, _⟩ := hedge
    exact absurd hlt (Nat.not_lt_zero _)
  · intro z _
    refine ne_of_gt (Finset.sum_pos (fun x _ => testNet_joint_pos x) ⟨fun _ => true, ?_⟩)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, ?_⟩
    exact funext fun i => absurd i.2 (Finset.notMem_empty _)

end Cslib.MachineLearning.IdentifiabilityTests

namespace Cslib.MachineLearning.IdentifiabilityFrontdoorTests

open Cslib.MachineLearning GraphicalModels BayesNet CausalAdjustmentTests Finset

/-- **Non-vacuity of `frontdoorClass`**: the front-door network `U → X → M → Y`, `U → Y`
(`fdNet`, nodes `0, 1, 2, 3`) satisfies the front-door criterion for the effect of `X = 1` on
`Y = 3` with mediator set `{M} = {2}`, and its positivity hypothesis. -/
theorem fdNet_mem_frontdoorClass : fdNet ∈ frontdoorClass fdNet.pa 1 3 {2} := by
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
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

/-- **Front-door identification, exercised**: every network in the front-door class of `fdNet`'s
graph whose joint law equals `fdNet`'s has the same interventional probabilities
`P(Y = v | do(X = a))`. -/
theorem fdNet_identified (a v : Bool) (b : BayesNet Bool 4)
    (hb : b ∈ frontdoorClass fdNet.pa 1 3 {2}) (hjoint : b.joint = fdNet.joint) :
    ∑ x with x 3 = v, (b.intervene 1 a).joint x =
      ∑ x with x 3 = v, (fdNet.intervene 1 a).joint x := by
  exact BayesNet.identifiedOn_frontdoorClass fdNet.pa 1 3 {2} a v
    (by decide) (by decide) (by decide) b hb fdNet fdNet_mem_frontdoorClass hjoint

end Cslib.MachineLearning.IdentifiabilityFrontdoorTests
