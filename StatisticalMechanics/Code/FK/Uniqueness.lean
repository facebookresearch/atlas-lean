/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.FK.EdgeMarginal
import Code.FK.IvProperties
import Code.FK.DlrSandwich
import Code.FK.LimitsInfinite
import Code.Foundations.MonotoneLimit

open Set Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK









variable {E : Type*} [Fintype E] [DecidableEq E]












theorem fk_unique_of_edgeMarg_eq {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A = eventMassProb ν A :=
  eventMass_eq_of_edgeMarg_eq hP hmarg hA












section Densities

variable {a b : ℝ → ℝ}








theorem countable_discontinuities (hb : Monotone b) :
    {p : ℝ | ¬ ContinuousAt b p}.Countable :=
  hb.countable_not_continuousAt










theorem eq_on_continuousAt
    (heq_at_cont : ∀ p : ℝ, ContinuousAt b p → a p = b p)
    {p : ℝ} (hp : ContinuousAt b p) : a p = b p :=
  heq_at_cont p hp









theorem countable_edgeMarg_ne (hb : Monotone b)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt b p → a p = b p) :
    {p : ℝ | a p ≠ b p}.Countable := by
  refine (countable_discontinuities hb).mono ?_
  intro p hp
  
  simp only [mem_setOf_eq] at hp ⊢
  exact fun hcont => hp (heq_at_cont p hcont)

end Densities





























theorem phi0_eq_phi1_off_countable
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb : Monotone (fun p => edgeMargProb (ν p) e))
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A →
        eventMassProb (μ p) A = eventMassProb (ν p) A := by
  
  refine ⟨{p : ℝ | ¬ ContinuousAt (fun p => edgeMargProb (ν p) e) p},
    countable_discontinuities hb, ?_⟩
  intro p hp A hA
  
  simp only [mem_setOf_eq, not_not] at hp
  exact fk_unique_of_edgeMarg_eq (hcoup p) (heq_at_cont p hp) hA









theorem countable_phi_ne
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb : Monotone (fun p => edgeMargProb (ν p) e))
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
  refine (countable_discontinuities hb).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  obtain ⟨A, hA, hne⟩ := hp
  
  intro hcont
  exact hne (fk_unique_of_edgeMarg_eq (hcoup p) (heq_at_cont p hcont) hA)

end FK

end StatMech
