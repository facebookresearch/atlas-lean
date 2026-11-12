/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.FieldGhostDict
import Code.Walls.gc7core
import Code.Walls.gc7ghosteven
import Code.Walls.gc6_core
import Code.Walls.gc6_ghostgraph
import Code.Walls.gc5_core
import Code.Walls.gc2_core
import Code.Ising.CorrelationRatio
import Code.Ising.GKS2
import Code.Ising.GKS

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
















theorem gc8_fourMarks_pairwise_distinct (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V))
      ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hox
  · simpa using hoy
  · simp
  · simpa using hxy
  · simp
  · simp













theorem gc8_fourMarks_eq_explicit (o x y : V) :
    insert (none : Option V) (({o, x, y} : Finset V).map someEmb)
      = ({none, some o, some x, some y} : Finset (Option V)) := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_singleton, someEmb_apply]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · tauto
    · rcases ha with rfl | rfl | rfl <;> tauto
  · rintro (rfl | rfl | rfl | rfl)
    · tauto
    · right; exact ⟨o, by simp, rfl⟩
    · right; exact ⟨x, by simp, rfl⟩
    · right; exact ⟨y, by simp, rfl⟩











theorem gc8_fourMarks_card_explicit (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (({none, some o, some x, some y} : Finset (Option V))).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp [hox, hoy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]




theorem gc8_fourMarks_card (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4 :=
  gc7_combined_source_card o x y hox hoy hxy







theorem gc8_fourMarks_even (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card :=
  gc7_combined_source_even o x y hox hoy hxy




















theorem gc8_fourMarks (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ((some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V))
        ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)))
      ∧ (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4
      ∧ Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card :=
  ⟨gc8_fourMarks_pairwise_distinct o x y hox hoy hxy,
   gc8_fourMarks_card o x y hox hoy hxy,
   gc8_fourMarks_even o x y hox hoy hxy⟩










variable {ι : Type*} [DecidableEq ι] [Fintype ι]












theorem gc8_fourMarks_dichotomy (ends : ι → Sym2 (Option V)) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V)))
    (hog_disc : ¬ connK ends K (some o) none) :
    ((connK ends K (some o) (some x) ∧ connK ends K (some y) none)
        ∨ (connK ends K (some o) (some y) ∧ connK ends K (some x) none))
      ∧ ¬ ((connK ends K (some o) (some x) ∧ connK ends K (some y) none)
        ∧ (connK ends K (some o) (some y) ∧ connK ends K (some x) none)) := by
  obtain ⟨hsox, hsoy, hsog, hsxy, hsxg, hsyg⟩ :=
    gc8_fourMarks_pairwise_distinct o x y hox hoy hxy
  exact gc7_core_pathCrossing_dichotomy ends K hnd (some o) (some x) (some y) none
    hsox hsoy hsog hsxy hsxg hsyg hbdry hog_disc







theorem gc8_fourMarks_trichotomy (ends : ι → Sym2 (Option V)) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V))) :
    (connK ends K (some o) none)
      ∨ (connK ends K (some o) (some x) ∧ connK ends K (some y) none)
      ∨ (connK ends K (some o) (some y) ∧ connK ends K (some x) none) := by
  obtain ⟨hsox, hsoy, hsog, hsxy, hsxg, hsyg⟩ :=
    gc8_fourMarks_pairwise_distinct o x y hox hoy hxy
  exact gc7_core_pathCrossing_trichotomy ends K hnd (some o) (some x) (some y) none
    hsox hsoy hsog hsxy hsxg hsyg hbdry















theorem gc8_fourMarks_cluster_even (ends : ι → Sym2 (Option V)) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y u : V)
    (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V))) :
    Even (#(({some o, some x, some y, none} : Finset (Option V)) ∩ (compOf ends K (some u)))) :=
  gc7_core_marks_in_cluster_even ends K hnd (some o) (some x) (some y) none (some u) hbdry









theorem gc8_fourMarks_nonvacuous :
    ((some (0 : Fin 3) ≠ some 1) ∧ (some (0 : Fin 3) ≠ some 2)
        ∧ (some (0 : Fin 3) ≠ (none : Option (Fin 3)))
        ∧ (some (1 : Fin 3) ≠ some 2) ∧ (some (1 : Fin 3) ≠ (none : Option (Fin 3)))
        ∧ (some (2 : Fin 3) ≠ (none : Option (Fin 3))))
      ∧ (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card = 4
      ∧ Even (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card :=
  gc8_fourMarks (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)


















theorem gc8_fourMarks_griffiths_step (eS cS eΛ : ℝ)
    (hSnn : 0 ≤ eS) (hcSnn : 0 ≤ cS) (hgriff : eS ≤ eΛ) :
    eΛ * (eS * cS) ≥ eS ^ 2 * cS :=
  acr_claim1_griffiths_step eS cS eΛ hSnn hcSnn hgriff














theorem gc8_fourMarks_ursell_nonpos_of_eqSwi (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (hid : gc6_EqSwiIdentity G β h o) (x y : V) :
    GhcEqGap.eg_ursell3 G β h o x y ≤ 0 :=
  gc6_core_ursell_nonpos G β h hβ hh o hid x y

end StatMech.Walls
