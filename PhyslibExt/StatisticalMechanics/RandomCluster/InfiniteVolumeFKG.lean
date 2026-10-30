/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit
/-!
# FKG inequality and ordering for infinite-volume FK measures at `q = 2`

The chosen free and wired infinite-volume measures at `q = 2` satisfy the FKG inequality and
`φ⁰ ≤ φ¹` on increasing cylinder events.

## i. Overview

A cylinder event of the box `Λ_N` is a preimage `boxRestrict d N ⁻¹' S`. For `m ≥ N` it is
also a cylinder event of `Λ_m`, so the finite-volume FKG inequality applies to the box measures
`φ⁰_m` and `φ¹_m`. At `q = 2` the probabilities of increasing cylinder events converge along
the whole sequence `m → ∞` to their values under `freeInfiniteVolume` and
`wiredInfiniteVolume` (`fk_free_infinite_measure`, `fk_wired_infinite_measure`), so the FKG
inequality and the domination `φ⁰_m ≼ φ¹_m` pass to the limit. The restriction to `q = 2`
comes from those convergence lemmas; the finite-volume inputs hold for all `q ≥ 1`.

## ii. Key results

- `ivp_iv_fkg` : FKG for the free infinite-volume measure on increasing cylinder events.
- `wiredFkProb_positively_associated_events` : FKG for the wired measure on a finite graph.
- `ivp_iv_fkg_wired` : FKG for the wired infinite-volume measure on increasing cylinder events.
- `ivp_iv_monotone` : `φ⁰(A) ≤ φ¹(A)` for increasing cylinder events `A`.

## iii. Table of contents

- A. The FKG inequality for the free measures
- B. The FKG inequality for the wired measures
- C. Ordering of the infinite-volume measures

## iv. References

- C. M. Fortuin, P. W. Kasteleyn, J. Ginibre, *Correlation inequalities on some partially
  ordered sets*, Comm. Math. Phys. 22 (1971).
- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators
open StatMech.Lattice StatMech.IsingFK

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {d : ℕ}

/-!
## A. The FKG inequality for the free measures
-/

/-- FKG inequality for the free box measure `φ⁰_m` (`q = 2`) on two increasing cylinder events of a
smaller box `Λ_N`, `N ≤ m`. -/
lemma freeFiniteMeasure_fkg (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  set T₁ := boxRestrictLE d hNm ⁻¹' S₁ with hT₁
  set T₂ := boxRestrictLE d hNm ⁻¹' S₂ with hT₂
  have hT₁inc : IsIncreasing T₁ := fun a b hab ha => hS₁ (boxRestrictLE_monotone d hNm hab) ha
  have hT₂inc : IsIncreasing T₂ := fun a b hab ha => hS₂ (boxRestrictLE_monotone d hNm hab) ha
  have heq₁ : boxRestrict d N ⁻¹' S₁ = boxRestrict d m ⁻¹' T₁ := by
    ext ω; simp only [hT₁, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have heq₂ : boxRestrict d N ⁻¹' S₂ = boxRestrict d m ⁻¹' T₂ := by
    ext ω; simp only [hT₂, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas₁ : MeasurableSet (boxRestrict d m ⁻¹' T₁) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeas₂ : MeasurableSet (boxRestrict d m ⁻¹' T₂) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeascap : MeasurableSet (boxRestrict d m ⁻¹' (T₁ ∩ T₂)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq₁, heq₂, ← Set.preimage_inter,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T₁ hmeas₁,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T₂ hmeas₂,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) (T₁ ∩ T₂) hmeascap]
  have hfkg := fkProb_positively_associated_events (boxGraph d m) hp hp1
    (by norm_num : (1 : ℝ) ≤ 2) hT₁inc hT₂inc
  calc (∑ ω, T₁.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d m) p 2 ω)
        * (∑ ω, T₂.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d m) p 2 ω)
      = (∑ ω, fkProb (boxGraph d m) p 2 ω * T₁.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, fkProb (boxGraph d m) p 2 ω * T₂.indicator (fun _ => (1 : ℝ)) ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm _ _),
          Finset.sum_congr rfl (fun ω _ => mul_comm (T₂.indicator _ ω) _)]
    _ ≤ ∑ ω, fkProb (boxGraph d m) p 2 ω * (T₁ ∩ T₂).indicator (fun _ => (1 : ℝ)) ω := hfkg
    _ = ∑ ω, (T₁ ∩ T₂).indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d m) p 2 ω :=
        Finset.sum_congr rfl (fun ω _ => mul_comm _ _)

/-- FKG inequality for the free infinite-volume measure at `q = 2` on increasing cylinder events of
a box. -/
lemma ivp_iv_fkg (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  have hcap : IsIncreasing (S₁ ∩ S₂) := hS₁.inter hS₂
  have heqcap : boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂
      = boxRestrict d N ⁻¹' (S₁ ∩ S₂) := (Set.preimage_inter).symm
  rw [heqcap]
  have hlim₁ := fk_free_infinite_measure N hp hp1 hS₁
  have hlim₂ := fk_free_infinite_measure N hp hp1 hS₂
  have hlimcap := fk_free_infinite_measure N hp hp1 hcap
  have hprod := hlim₁.mul hlim₂
  have heventually :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
          * (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
          ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (boxRestrict d N ⁻¹' (S₁ ∩ S₂)) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    have h := freeFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂
    rwa [← Set.preimage_inter] at h
  exact le_of_tendsto_of_tendsto hprod hlimcap heventually

/-!
## B. The FKG inequality for the wired measures
-/

section Wired
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-- The wired random-cluster measure satisfies the FKG lattice condition when `q ≥ 1`. -/
lemma wiredFkProb_FKGLatticeCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FKGLatticeCondition (fun ω => wiredFkProb G bdry p q ω) := by
  intro a b
  simp only [← bcProb_clique_eq_wiredFkProb]
  have hcross := bcProb_cross G (StatMech.Lattice.boundaryCliqueGraph bdry)
    (StatMech.Lattice.boundaryCliqueGraph bdry) le_rfl hp hp1 hq a b
  calc bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q a
        * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q b
      ≤ bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊓ b)
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊔ b) := hcross
    _ = bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊔ b)
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q (a ⊓ b) := mul_comm _ _

/-- FKG inequality for the wired random-cluster measure on a finite graph: increasing events are
positively correlated when `q ≥ 1`. -/
lemma wiredFkProb_positively_associated_events {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, wiredFkProb G bdry p q ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, wiredFkProb G bdry p q ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, wiredFkProb G bdry p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact fkg_inequality_events
    (fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω)
    (wiredFkProb_sum_eq_one G bdry hp hp1 hq0)
    (wiredFkProb_FKGLatticeCondition G bdry hp hp1 hq) hA hB

end Wired

/-- FKG inequality for the wired box measure `φ¹_m` (`q = 2`) on two increasing cylinder events of a
smaller box `Λ_N`, `N ≤ m`. -/
lemma wiredFiniteMeasure_fkg (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  set T₁ := boxRestrictLE d hNm ⁻¹' S₁ with hT₁
  set T₂ := boxRestrictLE d hNm ⁻¹' S₂ with hT₂
  have hT₁inc : IsIncreasing T₁ := fun a b hab ha => hS₁ (boxRestrictLE_monotone d hNm hab) ha
  have hT₂inc : IsIncreasing T₂ := fun a b hab ha => hS₂ (boxRestrictLE_monotone d hNm hab) ha
  have heq₁ : boxRestrict d N ⁻¹' S₁ = boxRestrict d m ⁻¹' T₁ := by
    ext ω; simp only [hT₁, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have heq₂ : boxRestrict d N ⁻¹' S₂ = boxRestrict d m ⁻¹' T₂ := by
    ext ω; simp only [hT₂, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas₁ : MeasurableSet (boxRestrict d m ⁻¹' T₁) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeas₂ : MeasurableSet (boxRestrict d m ⁻¹' T₂) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  have hmeascap : MeasurableSet (boxRestrict d m ⁻¹' (T₁ ∩ T₂)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq₁, heq₂, ← Set.preimage_inter,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T₁ hmeas₁,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T₂ hmeas₂,
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (T₁ ∩ T₂) hmeascap]
  have hfkg := wiredFkProb_positively_associated_events (boxGraph d m) (boxBoundary d m)
    hp hp1 (by norm_num : (1 : ℝ) ≤ 2) hT₁inc hT₂inc
  calc (∑ ω, T₁.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω)
        * (∑ ω, T₂.indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω)
      = (∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
            * T₁.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
            * T₂.indicator (fun _ => (1 : ℝ)) ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm _ _),
          Finset.sum_congr rfl (fun ω _ => mul_comm (T₂.indicator _ ω) _)]
    _ ≤ ∑ ω, wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω
          * (T₁ ∩ T₂).indicator (fun _ => (1 : ℝ)) ω := hfkg
    _ = ∑ ω, (T₁ ∩ T₂).indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω :=
        Finset.sum_congr rfl (fun ω _ => mul_comm _ _)

/-- FKG inequality for the wired infinite-volume measure at `q = 2` on increasing cylinder events of
a box. -/
lemma ivp_iv_fkg_wired (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
      * (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  have hcap : IsIncreasing (S₁ ∩ S₂) := hS₁.inter hS₂
  have heqcap : boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂
      = boxRestrict d N ⁻¹' (S₁ ∩ S₂) := (Set.preimage_inter).symm
  rw [heqcap]
  have hlim₁ := fk_wired_infinite_measure N hp hp1 hS₁
  have hlim₂ := fk_wired_infinite_measure N hp hp1 hS₂
  have hlimcap := fk_wired_infinite_measure N hp hp1 hcap
  have hprod := hlim₁.mul hlim₂
  have heventually :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₁)
          * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S₂)
          ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (boxRestrict d N ⁻¹' (S₁ ∩ S₂)) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    have h := wiredFiniteMeasure_fkg N m hNm hp hp1 hS₁ hS₂
    rwa [← Set.preimage_inter] at h
  exact le_of_tendsto_of_tendsto hprod hlimcap heventually

/-!
## C. Ordering of the infinite-volume measures
-/

/-- At `q = 2` the free infinite-volume measure gives every increasing cylinder event at most the
probability the wired one gives it. -/
lemma ivp_iv_monotone (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have hAinc : IsIncreasing (boxRestrict d N ⁻¹' S) :=
    isIncreasing_boxRestrict_preimage N hS
  have hAmeas : MeasurableSet (boxRestrict d N ⁻¹' S) :=
    measurableSet_boxRestrict_preimage N S
  have hfree := fk_free_infinite_measure N hp hp1 hS
  have hwired := fk_wired_infinite_measure N hp hp1 hS
  have heventually :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
          ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
    filter_upwards with m
    have hdom := freeFiniteMeasure_dominated d m hp hp1 (by norm_num : (1 : ℝ) ≤ 2)
      (boxRestrict d N ⁻¹' S) hAmeas hAinc
    exact hdom
  exact le_of_tendsto_of_tendsto hfree hwired heventually

end FK

end StatMech
