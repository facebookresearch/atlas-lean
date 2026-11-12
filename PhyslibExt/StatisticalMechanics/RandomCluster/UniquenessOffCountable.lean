/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PressureDiff

/-!
# Uniqueness of the infinite-volume random-cluster measure off a countable set

If the wired edge density is monotone in `p` and agrees with the free edge density at its
continuity points, then for all but countably many `p` every measure sandwiched between the free
and wired infinite-volume measures agrees with both on increasing events.

## i. Overview

An abstract sandwich argument: when `φ^0(A) ≤ φ(A) ≤ φ^1(A)` and `φ^0(A) = φ^1(A)`, all three
agree. The wired edge density `p ↦ φ^1_{p,q}(e open)` is the right derivative of a convex pressure
and hence monotone; a monotone function has countably many discontinuities, so the free and wired
densities agree off a countable set. Equality of edge densities propagates to increasing events
by the hypothesis `hcrit`.

## ii. Key results

- `countable_density_ne` : agreement at continuity points of a monotone function fails on a
  countable set (via Mathlib's `Monotone.countable_not_continuousAt`).
- `fk_uniqueness_off_countable_abstract` : the abstract countable-exception statement.
- `wiredEdgeDensity`, `freeEdgeDensity` : the infinite-volume edge densities.
- `fk_uniqueness_off_countable` : the random-cluster instance, given `hb`, `heq_at_cont`, and
  `hcrit`.

## iii. Table of contents

- A. Abstract sandwich arguments
- B. Edge densities of the infinite-volume measures

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.63.
-/

@[expose] public section

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

/-! ## A. Abstract sandwich arguments -/

lemma dlr_sandwich_unique {free wired phi : Measure Ω} {A : Set Ω}
    (hsand : free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : free.real A = wired.real A) :
    phi.real A = free.real A ∧ phi.real A = wired.real A := by
  obtain ⟨h1, h2⟩ := hsand
  rw [hfw] at h1
  have heqw : phi.real A = wired.real A := le_antisymm h2 h1
  exact ⟨by rw [heqw, hfw], heqw⟩

lemma sandwich_eq_of_free_eq_wired {free wired phi : Measure Ω} {P : Set Ω → Prop}
    (hsand : ∀ A, P A → free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : ∀ A, P A → free.real A = wired.real A) :
    ∀ A, P A → phi.real A = free.real A ∧ phi.real A = wired.real A :=
  fun A hA => dlr_sandwich_unique (hsand A hA) (hfw A hA)

lemma countable_density_ne {a b : ℝ → ℝ} (hb : Monotone b)
    (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p) :
    {p : ℝ | a p ≠ b p}.Countable := by
  refine (hb.countable_not_continuousAt).mono ?_
  intro p hp
  simp only [mem_ofPred_eq] at hp ⊢
  exact fun hcont => hp (heq_at_cont p hcont)

lemma fk_uniqueness_off_countable_abstract
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
  simp only [mem_ofPred_eq, not_not] at hp
  have hfw : ∀ A, P A → (free p).real A = (wired p).real A := hcrit p hp
  exact sandwich_eq_of_free_eq_wired hsand hfw A hA

end Abstract

section InfiniteVolume

open StatMech.Lattice

/-! ## B. Edge densities of the infinite-volume measures -/

/-- The event that the edge `e` is open. -/
def fkEdgeOpenEvent {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

lemma isIncreasing_fkEdgeOpenEvent {E : Type*} (e : E) :
    IsIncreasing (fkEdgeOpenEvent e) := by
  intro x y hxy hx
  simp only [fkEdgeOpenEvent, mem_ofPred_eq] at hx ⊢
  have hle := hxy e
  rw [hx] at hle
  exact le_antisymm (by simp) hle

/-- The edge density `φ^1_{p,q}(e open)` of the wired infinite-volume random-cluster measure on
`ℤ^d`, set to `0` outside `p ∈ (0, 1)`, `q > 0`.
-/
noncomputable def wiredEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (wiredInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0

/-- The edge density `φ^0_{p,q}(e open)` of the free infinite-volume random-cluster measure on
`ℤ^d`, set to `0` outside `p ∈ (0, 1)`, `q > 0`.
-/
noncomputable def freeEdgeDensity (d : ℕ) (q : ℝ) (e : Sym2 (Site d)) (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 ∧ 0 < q then
    (freeInfiniteVolume d h.1 h.2.1 h.2.2 : Measure (ConfigSpace (Sym2 (Site d)))).real
      (fkEdgeOpenEvent e)
  else 0

lemma wiredEdgeDensity_monotone_of_pressure (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hb_eq : ∀ p, wiredEdgeDensity d q e p = pressureRightDeriv g p) :
    Monotone (wiredEdgeDensity d q e) := by
  have hfun : wiredEdgeDensity d q e = pressureRightDeriv g := funext hb_eq
  rw [hfun]
  exact pressureRightDeriv_monotone hg

lemma fk_uniqueness_off_countable (d : ℕ) (q : ℝ) (e : Sym2 (Site d))
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
  simp only [mem_ofPred_eq, not_not] at hp
  have hfw : (freeInfiniteVolume d hp0 hp1 hq : Measure _).real A
      = (wiredInfiniteVolume d hp0 hp1 hq : Measure _).real A :=
    hcrit p hp A hA (hp := hp0) (hp1 := hp1) (hq := hq)
  exact dlr_sandwich_unique (hsand A hA) hfw

end InfiniteVolume

end FK

end StatMech
