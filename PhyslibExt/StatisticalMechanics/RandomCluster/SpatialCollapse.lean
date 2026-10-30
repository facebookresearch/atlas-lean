/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.IVPressureConvex
/-!
# Boundary fractions of boxes and graphs on a fixed box

The boundary fraction of box edges, and why collapse cannot be obtained on a fixed box.

## i. Overview

If the edges of `Λ_n` outside a bulk set number at most a constant times the boundary of `Λ_n`,
their fraction tends to zero because the surface-to-volume ratio of boxes does
(`spc_boundaryFraction_le_surfaceVolume`).

The second part records why collapse of average densities cannot be obtained from graphs on a
fixed box.
Per-edge free energies of a sequence of graphs on the fixed vertex set `Λ_N` take only finitely
many values, so a limit along such a sequence is one of those values; matching the growing-box
free energy therefore requires growing boxes.

## ii. Key results

- `spc_boundaryFraction_le_surfaceVolume` : the boundary fraction is bounded by the
  surface-to-volume ratio.
- `spc_fixedBox_collapse_obstruction` : a limit of per-edge free energies of graphs on a fixed
  box is attained by one of those graphs.

## iii. Table of contents

- A. Collapse on growing boxes
- B. Graphs on a fixed box

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.4.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}

/-!
## A. Collapse on growing boxes
-/

set_option linter.unusedVariables false in
/-- If the non-bulk edges of `Λ_n` number at most `C` times the boundary of `Λ_n`, their fraction
is at most `C` times the boundary-to-edge ratio. -/
lemma spc_boundaryFraction_le_surfaceVolume (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (In : Finset (Sym2 (boxVerts d n)))
    (hIE : In ⊆ (boxGraph d n).edgeFinset)
    (hbd : ((boxGraph d n).edgeFinset.card - In.card : ℝ)
      ≤ C * (Finset.univ.filter (boxBoundary d n)).card)
    (hEpos : 0 < (boxGraph d n).edgeFinset.card) :
    (((boxGraph d n).edgeFinset.card - In.card : ℝ)) / (boxGraph d n).edgeFinset.card
      ≤ C * (((Finset.univ.filter (boxBoundary d n)).card : ℝ)
              / (boxGraph d n).edgeFinset.card) := by
  have hEpos' : (0:ℝ) < (boxGraph d n).edgeFinset.card := by exact_mod_cast hEpos
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hEpos').mpr hbd

/-!
## B. Graphs on a fixed box
-/

/-- The per-edge free energy does not depend on the decidability instance of the adjacency
relation. -/
lemma spc_tiltFreeEnergy_instIrrel (N : ℕ) (H : SimpleGraph (boxVerts d N))
    (i1 i2 : DecidableRel H.Adj) (t : ℝ) :
    @ivp2_tiltFreeEnergy _ _ _ H i1 2 t = @ivp2_tiltFreeEnergy _ _ _ H i2 2 t := by
  congr 1

/-- The per-edge free energies of a sequence of graphs on the fixed box `Λ_N` take finitely many
values. -/
lemma spc_range_finite (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [inst : ∀ n, DecidableRel (Gn n).Adj] (t : ℝ) :
    (Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t)).Finite := by
  have heq : (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t)
      = (fun H : SimpleGraph (boxVerts d N) =>
          @ivp2_tiltFreeEnergy _ _ _ H (Classical.decRel _) 2 t) ∘ Gn := by
    funext n
    exact spc_tiltFreeEnergy_instIrrel N (Gn n) (inst n) (Classical.decRel _) t
  rw [heq, Set.range_comp]
  exact (Set.toFinite (Set.range Gn)).image _

/-- A limit of per-edge free energies of graphs on the fixed box `Λ_N` is attained by one of the
graphs. -/
lemma spc_feketeLimit_mem_finiteRange (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [∀ n, DecidableRel (Gn n).Adj] (g : ℝ → ℝ)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) :
    g t ∈ Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) :=
  (spc_range_finite N Gn t).isClosed.mem_of_tendsto (hfree t)
    (Eventually.of_forall (fun n => ⟨n, rfl⟩))

/-- If graphs on the fixed box `Λ_N` and the growing boxes `Λ_n` have the same limiting per-edge
free energy `g t`, then `g t` is the free energy of a single graph on `Λ_N`. -/
lemma spc_fixedBox_collapse_obstruction (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [∀ n, DecidableRel (Gn n).Adj] (g : ℝ → ℝ)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) :
    (∃ H : SimpleGraph (boxVerts d N), ∃ _ : DecidableRel H.Adj,
        g t = ivp2_tiltFreeEnergy H 2 t)
      ∧ Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)) := by
  refine ⟨?_, hboxfree t⟩
  obtain ⟨n, hn⟩ := spc_feketeLimit_mem_finiteRange N Gn g hfree t
  exact ⟨Gn n, inferInstance, hn.symm⟩

end FK

end StatMech
