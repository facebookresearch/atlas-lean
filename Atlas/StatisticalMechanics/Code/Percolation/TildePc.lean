/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Code.Lattice.Clusters
import Code.Percolation.Theta
import Code.Foundations.ProductMeasure

open MeasureTheory
open scoped NNReal
open Finset

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def coordShift (x : Site d) (i : Fin d) (δ : ℤ) : Site d :=
  Function.update x i (x i + δ)


def stepSign (b : Bool) : ℤ := if b then 1 else -1






noncomputable def boundaryEdges (d : ℕ) (S : Finset (Site d)) :
    Finset (Site d × Site d) := by
  classical
  exact
    ((S ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset Bool)).filter
        (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ S)).image
      (fun t => (t.1, coordShift t.1 t.2.1 (stepSign t.2.2)))








noncomputable def connWithinProb (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (x : Site d) : ℝ := by
  classical
  exact
    if h0 : origin d ∈ S then
      if hx : x ∈ S then
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | ConnectedWithin d ω (S : Set (Site d)) ⟨origin d, h0⟩ ⟨x, hx⟩}
      else 0
    else 0


theorem connWithinProb_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (x : Site d) : 0 ≤ connWithinProb d p hp S x := by
  classical
  unfold connWithinProb
  split
  · split
    · exact ENNReal.toReal_nonneg
    · exact le_refl 0
  · exact le_refl 0




noncomputable def phi (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) : ℝ :=
  (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1


theorem phi_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) :
    0 ≤ phi d p hp S := by
  unfold phi
  refine mul_nonneg p.coe_nonneg (Finset.sum_nonneg ?_)
  intro e _
  exact connWithinProb_nonneg d p hp S e.1



def tildePcSet (d : ℕ) : Set ℝ≥0 :=
  {p : ℝ≥0 | ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1}

@[simp]
theorem mem_tildePcSet {d : ℕ} {p : ℝ≥0} :
    p ∈ tildePcSet d ↔
      ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1 :=
  Iff.rfl





noncomputable def tildePc (d : ℕ) : ℝ≥0 :=
  sSup (tildePcSet d)

end Percolation

end StatMech
