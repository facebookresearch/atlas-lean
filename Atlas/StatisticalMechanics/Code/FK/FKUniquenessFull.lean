/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.FK.InfiniteVolume
import Code.FK.PressureDiff
import Code.FK.DlrSandwich
import Code.FK.Uniqueness
import Code.Inequalities.IncreasingEvent

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace











section Abstract

variable {Ω : Type*} [MeasurableSpace Ω]













theorem dlr_sandwich_unique {free wired phi : Measure Ω} {A : Set Ω}
    (hsand : free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : free.real A = wired.real A) :
    phi.real A = free.real A ∧ phi.real A = wired.real A := by
  obtain ⟨h1, h2⟩ := hsand
  
  rw [hfw] at h1
  have heqw : phi.real A = wired.real A := le_antisymm h2 h1
  exact ⟨by rw [heqw, hfw], heqw⟩








theorem sandwich_eq_of_free_eq_wired {free wired phi : Measure Ω} {P : Set Ω → Prop}
    (hsand : ∀ A, P A → free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : ∀ A, P A → free.real A = wired.real A) :
    ∀ A, P A → phi.real A = free.real A ∧ phi.real A = wired.real A :=
  fun A hA => dlr_sandwich_unique (hsand A hA) (hfw A hA)










theorem countable_density_ne {a b : ℝ → ℝ} (hb : Monotone b)
    (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p) :
    {p : ℝ | a p ≠ b p}.Countable := by
  refine (hb.countable_not_continuousAt).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  exact fun hcont => hp (heq_at_cont p hcont)




























theorem fk_uniqueness_off_countable_abstract
    (free wired : ℝ → Measure Ω) (P : Set Ω → Prop) (a b : ℝ → ℝ)
    (hb : Monotone b)
    (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p)
    (hcrit : ∀ p, a p = b p → ∀ A, P A → (free p).real A = (wired p).real A) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ phi : Measure Ω,
        (∀ A, P A → (free p).real A ≤ phi.real A ∧ phi.real A ≤ (wired p).real A) →
          ∀ A, P A → phi.real A = (free p).real A ∧ phi.real A = (wired p).real A := by
  
  refine ⟨{p : ℝ | a p ≠ b p}, countable_density_ne hb heq_at_cont, ?_⟩
  intro p hp phi hsand A hA
  
  simp only [mem_setOf_eq, not_not] at hp
  have hfw : ∀ A, P A → (free p).real A = (wired p).real A := hcrit p hp
  
  exact sandwich_eq_of_free_eq_wired hsand hfw A hA

end Abstract










section InfiniteVolume

open StatMech.Lattice



def fkEdgeOpenEvent {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}




theorem isIncreasing_fkEdgeOpenEvent {E : Type*} (e : E) :
    IsIncreasing (fkEdgeOpenEvent e) := by
  intro x y hxy hx
  simp only [fkEdgeOpenEvent, mem_setOf_eq] at hx ⊢
  have hle := hxy e
  rw [hx] at hle
  exact le_antisymm (by simp) hle




noncomputable def wiredEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (wiredInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0




noncomputable def freeEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (freeInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0











theorem wiredEdgeDensity_monotone_of_pressure (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hb_eq : ∀ p, wiredEdgeDensity d q e p = pressureRightDeriv g p) :
    Monotone (wiredEdgeDensity d q e) := by
  have hfun : wiredEdgeDensity d q e = pressureRightDeriv g := funext hb_eq
  rw [hfun]
  exact pressureRightDeriv_monotone hg

































theorem fk_uniqueness_off_countable (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
    (hb : Monotone (wiredEdgeDensity d q e))
    (heq_at_cont : ∀ p, ContinuousAt (wiredEdgeDensity d q e) p →
      freeEdgeDensity d q e p = wiredEdgeDensity d q e p)
    (hcrit : ∀ p, freeEdgeDensity d q e p = wiredEdgeDensity d q e p →
      ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
        ∀ {hp : 0 < p} {hp1 : p < 1} {hq : 0 < q},
          (freeInfiniteVolume d hp hp1 hq : Measure _).real A
            = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) :
    ∀ {hq : 0 < q}, ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        (∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
          (freeInfiniteVolume d hp hp1 hq : Measure _).real A ≤ phi.real A
            ∧ phi.real A ≤ (wiredInfiniteVolume d hp hp1 hq : Measure _).real A) →
        ∀ A : Set (ConfigSpace (Sym2 (Site d))), IsIncreasing A →
          phi.real A = (freeInfiniteVolume d hp hp1 hq : Measure _).real A
            ∧ phi.real A = (wiredInfiniteVolume d hp hp1 hq : Measure _).real A := by
  intro hq
  
  refine ⟨{p : ℝ | freeEdgeDensity d q e p ≠ wiredEdgeDensity d q e p},
    countable_density_ne hb heq_at_cont, ?_⟩
  intro p hp hp0 hp1 phi hsand A hA
  
  simp only [mem_setOf_eq, not_not] at hp
  
  have hfw : (freeInfiniteVolume d hp0 hp1 hq : Measure _).real A
      = (wiredInfiniteVolume d hp0 hp1 hq : Measure _).real A :=
    hcrit p hp A hA (hp := hp0) (hp1 := hp1) (hq := hq)
  
  exact dlr_sandwich_unique (hsand A hA) hfw

end InfiniteVolume

end FK

end StatMech
