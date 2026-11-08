/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.LPRelaxations.FractionalColouring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Basic

@[expose] public section

open SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.LPRelaxations.FractionalColouring

open MetaMathlibExt

-- Combinatorics 437: Fractional colouring & fractional chromatic number

-- Sanity check: the fractional colouring of K2 with each singleton
-- assigned 1 has weight = 2.

abbrev K2 := completeGraph (Fin 2)

/-- Weight function for `fcc`: `1` on each singleton, `0` elsewhere. -/

def fccW : Finset (Fin 2) → ℝ :=
  fun s => if s = {0} ∨ s = {1} then 1 else 0

/-- The fractional colouring of `K2` weighing each singleton `1`. -/

def fcc : FracColouring K2 where
  w := fccW
  nonneg := by
    intro s
    simp only [fccW]
    split <;> norm_num
  indep := by
    intro s hs a ha b hb hab
    have hdisj : s = {0} ∨ s = {1} := by
      by_contra hc
      unfold fccW at hs
      rw [if_neg hc] at hs
      exact hs rfl
    rcases hdisj with rfl | rfl <;>
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] at hab <;>
      exact absurd rfl hab
  cover := by
    intro v
    have hw1 : ∀ u : Fin 2, fccW {u} = 1 := by
      intro u
      fin_cases u <;> simp [fccW]
    calc (1 : ℝ) = fccW {v} := (hw1 v).symm
      _ ≤ ∑ s ∈ Finset.univ.filter (fun s => v ∈ s), fccW s :=
        Finset.single_le_sum
          (fun s _ => by simp only [fccW]; split <;> norm_num) (by simp)

/-- `fcc` has total weight 2. -/

theorem fcc_weight : fcc.weight = 2 := by
  have e0 : fccW (∅ : Finset (Fin 2)) = 0 := by
    change (if ∅ = ({0} : Finset (Fin 2)) ∨ ∅ = {1} then (1 : ℝ) else 0) = 0
    exact if_neg (by decide)
  have e1 : fccW ({0} : Finset (Fin 2)) = 1 := by
    change (if ({0} : Finset (Fin 2)) = {0} ∨ {0} = {1} then (1 : ℝ) else 0) = 1
    exact if_pos (Or.inl rfl)
  have e2 : fccW ({1} : Finset (Fin 2)) = 1 := by
    change (if ({1} : Finset (Fin 2)) = {0} ∨ {1} = {1} then (1 : ℝ) else 0) = 1
    exact if_pos (Or.inr rfl)
  have e3 : fccW ({0, 1} : Finset (Fin 2)) = 0 := by
    change (if ({0, 1} : Finset (Fin 2)) = {0} ∨ {0, 1} = {1} then (1 : ℝ) else 0) = 0
    exact if_neg (by decide)
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by
    decide
  change (∑ s ∈ Finset.univ, fccW s) = 2
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [e0, e1, e2, e3]
  norm_num

-- The fractional chromatic number of `K2` is at most `2`, witnessed by `fcc`.

example : K2.fracChromaticNumber ≤ 2 := by
  have hbdd : BddBelow {q : ℝ | ∃ c : FracColouring K2, c.weight = q} := by
    refine ⟨0, ?_⟩
    rintro q ⟨c, rfl⟩
    show (0 : ℝ) ≤ c.weight
    simp only [FracColouring.weight]
    exact Finset.sum_nonneg (fun s _ => c.nonneg s)
  have hle : K2.fracChromaticNumber ≤ fcc.weight := csInf_le hbdd ⟨fcc, rfl⟩
  rw [fcc_weight] at hle
  exact hle

-- Combinatorics 438: Regular fractional colouring

--  Sanity check: the fractional colouring of $K_2$ with 1 on both singleton independent sets is regular.
/-- `fcc` is regular: every vertex is covered with total weight `1`. -/

theorem fcc_regular : fcc.IsRegular := by
  intro w
  have hmem : ({w} : Finset (Fin 2)) ∈ Finset.univ.filter (fun s => w ∈ s) := by simp
  have hw1 : fccW {w} = 1 := by fin_cases w <;> simp [fccW]
  rw [← hw1]
  refine Finset.sum_eq_single (M := ℝ) (f := fccW) {w} (fun b hb hbne => ?_)
    (fun h => absurd hmem h)
  have hmem' : w ∈ b := (Finset.mem_filter.mp hb).2
  by_cases h : b = {0} ∨ b = {1}
  · rcases h with rfl | rfl
    · exact absurd (by rw [Finset.mem_singleton.mp hmem']) hbne
    · exact absurd (by rw [Finset.mem_singleton.mp hmem']) hbne
  · change (if b = ({0} : Finset (Fin 2)) ∨ b = {1} then (1 : ℝ) else 0) = 0
    exact if_neg h

end MathlibExtTest.Combinatorics.SimpleGraph.AlgebraicGraphTheory.LPRelaxations.FractionalColouring

end
