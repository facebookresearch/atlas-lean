/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Lattice.ContourSubsetCount

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}























def PerContourDualCircuit (d n ℓ : ℕ) : Prop :=
  ∃ anchorPool : Finset (Site d), anchorPool.card ≤ ℓ ∧
    ∃ decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)),
      ∀ F ∈ realisedContours d n ℓ,
        ∃ v : Site d, v ∈ anchorPool ∧
          ∃ W : (hypercubicLattice d).Walk v v, W.length = ℓ ∧ decode ⟨v, W⟩ = F














theorem realisedContourWalkEncoding_of_perContour {n ℓ : ℕ}
    (h : PerContourDualCircuit d n ℓ) : RealisedContourWalkEncoding d n ℓ := by
  classical
  obtain ⟨anchorPool, hcard, decode, hcirc⟩ := h
  
  
  refine ⟨anchorPool, hcard,
    fun F => if hF : F ∈ realisedContours d n ℓ
      then ⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩
      else ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩,
    decode, ?_⟩
  
  intro F hF
  beta_reduce
  have hred : (if hF : F ∈ realisedContours d n ℓ
      then (⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩ :
        Σ v : Site d, (hypercubicLattice d).Walk v v)
      else ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩)
      = ⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩ := dif_pos hF
  refine ⟨?_, ?_, ?_⟩
  · rw [hred]
    exact (hcirc F hF).choose_spec.1
  · rw [hred]
    exact (hcirc F hF).choose_spec.2.choose_spec.1
  · rw [hred]
    exact (hcirc F hF).choose_spec.2.choose_spec.2












def axisVertex (d j : ℕ) : Site d := fun i => if i.val = 0 then (j : ℤ) else 0

@[simp] theorem axisVertex_zero_coord (d j : ℕ) (h : 0 < d) :
    axisVertex d j ⟨0, h⟩ = (j : ℤ) := by
  simp only [axisVertex, if_true]



noncomputable def axisAnchorPool (d ℓ : ℕ) : Finset (Site d) :=
  (Finset.range ℓ).image (fun j => axisVertex d j)



theorem axisAnchorPool_card_le (d ℓ : ℕ) : (axisAnchorPool d ℓ).card ≤ ℓ := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_range]


theorem axisVertex_zero_eq_origin :
    axisVertex d 0 = StatMech.Ising.origin d := by
  funext i
  simp only [axisVertex, StatMech.Ising.origin, Nat.cast_zero]
  split <;> rfl












def AxisContourDualCircuit (d n ℓ : ℕ) : Prop :=
  ∃ decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)),
    ∀ F ∈ realisedContours d n ℓ,
      ∃ j : ℕ, j < ℓ ∧
        ∃ W : (hypercubicLattice d).Walk (axisVertex d j) (axisVertex d j),
          W.length = ℓ ∧ decode ⟨axisVertex d j, W⟩ = F




theorem perContourDualCircuit_of_axis {n ℓ : ℕ} (h : AxisContourDualCircuit d n ℓ) :
    PerContourDualCircuit d n ℓ := by
  classical
  obtain ⟨decode, hcirc⟩ := h
  refine ⟨axisAnchorPool d ℓ, axisAnchorPool_card_le d ℓ, decode, ?_⟩
  intro F hF
  obtain ⟨j, hj, W, hlen, hdec⟩ := hcirc F hF
  refine ⟨axisVertex d j, ?_, W, hlen, hdec⟩
  
  simp only [axisAnchorPool, Finset.mem_image, Finset.mem_range]
  exact ⟨j, hj, rfl⟩






theorem realisedContourWalkEncoding_of_axisCircuit {n ℓ : ℕ}
    (h : AxisContourDualCircuit d n ℓ) : RealisedContourWalkEncoding d n ℓ :=
  realisedContourWalkEncoding_of_perContour (perContourDualCircuit_of_axis h)











theorem perContourDualCircuit_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : PerContourDualCircuit d n ℓ := by
  refine ⟨∅, by simp, fun _ => ∅, ?_⟩
  intro F hF
  rw [hempty] at hF
  simp at hF



theorem axisContourDualCircuit_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : AxisContourDualCircuit d n ℓ := by
  refine ⟨fun _ => ∅, ?_⟩
  intro F hF
  rw [hempty] at hF
  simp at hF




theorem contourSubsetCountBound_of_empty_axis {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : ContourSubsetCountBound d n ℓ :=
  contourSubsetCountBound_of_walkEncoding
    (realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_empty hempty))

end Lattice

end StatMech
