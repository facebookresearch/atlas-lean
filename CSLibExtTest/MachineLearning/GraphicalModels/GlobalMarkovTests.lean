/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
public import Mathlib.Tactic.FinCases

/-!
# Tests for the global Markov property

* The chain `0 → 1 → 2`: `{1}` d-separates `0` from `2` (every path from `0` to `2` passes
  through `1` as a non-collider), so `X₀ ⫫ X₂ | X₁` under every law factorizing along the chain.
* Two unconnected roots are d-separated by `∅`, so they are independent.
* Boundary case: `CondIndep` with `Y = ∅` holds for every law.
-/

@[expose] public section

namespace Cslib.MachineLearning.GlobalMarkovTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The chain `0 → 1 → 2` on `Bool`: node `0` has law `p0` and node `k > 0` has law `p x_{k-1}`
given its parent. -/
noncomputable def chain (p0 : StdSimplex ℝ Bool) (p : Bool → StdSimplex ℝ Bool) :
    BayesNet Bool 3 where
  pa k := if h : (k : ℕ) = 0 then ∅ else {⟨k - 1, by omega⟩}
  cpt k u := if h : (k : ℕ) = 0 then p0 else p (u ⟨⟨k - 1, by omega⟩, by simp [h]⟩)

theorem chain_pa {p0 p} (k : Fin 3) :
    (chain p0 p).pa k = if h : (k : ℕ) = 0 then ∅ else {⟨k - 1, by omega⟩} :=
  rfl

theorem chain_edge {p0 p} {i j : Fin 3} : (chain p0 p).Edge i j ↔ (i : ℕ) + 1 = j := by
  rw [BayesNet.Edge, chain_pa]
  fin_cases i <;> fin_cases j <;> decide

/-- In the chain, `{1}` d-separates `0` from `2`. -/
theorem chain_dSeparated {p0 p} :
    (chain p0 p).DSeparated ((({0} : Finset (Fin 3))) : Set (Fin 3))
      (({2} : Finset (Fin 3)) : Set (Fin 3)) (({1} : Finset (Fin 3)) : Set (Fin 3)) := by
  intro x hx y hy l hl
  simp only [coe_singleton, Set.mem_singleton_iff] at hx hy
  subst hx hy
  obtain ⟨hnd, hch, hh, hlast⟩ := hl
  rcases l with _ | ⟨a, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at hh
  · simp at hh hlast
    exact absurd (hh.symm.trans hlast) (by decide)
  · simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp at hlast
    subst hlast
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    rcases hch with h | h <;> simp [chain_edge] at h
  · simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hq : q = 1 := by
      have h := (List.isChain_cons_cons.1 hch).1
      rcases h with h | h <;> rw [chain_edge] at h
      · exact Fin.ext (by simpa using h.symm)
      · simp at h
    subst hq
    have hr : r ≠ 0 := fun h => by subst h; simp at hnd
    refine ⟨0, by simp, Or.inr ⟨fun h => ?_, by simp⟩⟩
    have h2 := h.2
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h2
    rw [chain_edge] at h2
    exact hr (Fin.ext (by simp at h2; omega))

/-- **Non-vacuity** of the global Markov property: under every law factorizing along the chain
`0 → 1 → 2`, `X₀ ⫫ X₂ | X₁`. -/
example {p0 p} : CondIndep (chain p0 p).joint {0} {2} {1} :=
  (chain p0 p).condIndep_of_dSeparated chain_dSeparated

/-- Two roots with no arrows. -/
noncomputable def twoRoots (p q : StdSimplex ℝ Bool) : BayesNet Bool 2 where
  pa _ := ∅
  cpt k _ := if (k : ℕ) = 0 then p else q

/-- Unconnected roots are d-separated by `∅`, hence independent. -/
example (p q : StdSimplex ℝ Bool) : CondIndep (twoRoots p q).joint {0} {1} ∅ := by
  refine (twoRoots p q).condIndep_of_dSeparated fun x hx y hy l hl => ?_
  simp only [coe_singleton, Set.mem_singleton_iff] at hx hy
  subst hx hy
  obtain ⟨-, hch, hh, hlast⟩ := hl
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp at hh
  · simp at hh hlast
    exact absurd (hh.symm.trans hlast) (by decide)
  · rcases (List.isChain_cons_cons.1 hch).1 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [twoRoots] at h

/-- Boundary case: `X ⫫ ∅ | Z` holds for every law. -/
example (P : (Fin 2 → Bool) → ℝ) (X Z : Finset (Fin 2)) : CondIndep P X ∅ Z := by
  intro x
  simp [mul_comm]

end Cslib.MachineLearning.GlobalMarkovTests
