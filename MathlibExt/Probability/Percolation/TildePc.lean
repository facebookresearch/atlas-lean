/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.Theta
public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# The Duminil-Copin–Tassion quantity `φ_p(S)` and the threshold `p̃_c`

For a finite set `S ⊆ ℤ^d` containing the origin, Duminil-Copin and Tassion define
`φ_p(S) = p · ∑_{(x, y) ∈ ∂S} ℙ_p(0 ↔ x inside S)`, where `∂S` is the set of lattice edges
`(x, y)` with `x ∈ S` and `y ∉ S`, and the threshold
`p̃_c = sup {p : ∃ S ∋ 0 finite, φ_p(S) < 1}`. Their theorem `p̃_c = p_c` is
`StatMech.Percolation.sharp_phase_transition`.

## Main definitions

* `StatMech.Percolation.coordShift`, `StatMech.Percolation.stepSign`: unit steps in `ℤ^d`.
* `StatMech.Percolation.boundaryEdges`: the oriented edge boundary `∂S` of a finite set.
* `StatMech.Percolation.connWithinProb`: `ℙ_p(0 ↔ x inside S)`.
* `StatMech.Percolation.phi`: the quantity `φ_p(S)`.
* `StatMech.Percolation.tildePcSet`, `StatMech.Percolation.tildePc`: the threshold `p̃_c(d)`.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal
open Finset

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

/-- The site `x + δ e_i` obtained by moving `x` by `δ` in coordinate `i`. -/
def coordShift (x : Site d) (i : Fin d) (δ : ℤ) : Site d :=
  Function.update x i (x i + δ)

/-- The unit step `+1` (for `true`) or `-1` (for `false`). -/
def stepSign (b : Bool) : ℤ := if b then 1 else -1

/-- The oriented edge boundary `∂S = {(x, x ± e_i) : x ∈ S, x ± e_i ∉ S}` of a finite set
`S ⊆ ℤ^d`, as ordered pairs (inner endpoint first). -/
noncomputable def boundaryEdges (d : ℕ) (S : Finset (Site d)) :
    Finset (Site d × Site d) := by
  classical
  exact
    ((S ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset Bool)).filter
        (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ S)).image
      (fun t => (t.1, coordShift t.1 t.2.1 (stepSign t.2.2)))

/-- The edge boundary of `S` has at most `2d |S|` elements. -/
theorem card_boundaryEdges_le (S : Finset (Site d)) :
    (boundaryEdges d S).card ≤ S.card * (2 * d) := by
  classical
  unfold boundaryEdges
  refine le_trans (Finset.card_image_le) ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_bool]
  exact le_of_eq (by ring)

/-- The probability `ℙ_p(0 ↔ x inside S)` that the origin and `x` are joined by an open path
using only vertices of `S`; it is `0` if `0 ∉ S` or `x ∉ S`. -/
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

/-- The Duminil-Copin–Tassion quantity `φ_p(S) = p ∑_{(x, y) ∈ ∂S} ℙ_p(0 ↔ x inside S)`. -/
noncomputable def phi (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) : ℝ :=
  (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1

theorem phi_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) :
    0 ≤ phi d p hp S := by
  unfold phi
  refine mul_nonneg p.coe_nonneg (Finset.sum_nonneg ?_)
  intro e _
  exact connWithinProb_nonneg d p hp S e.1

/-- The set of densities `p ∈ [0, 1]` for which some finite `S ∋ 0` has `φ_p(S) < 1`. -/
def tildePcSet (d : ℕ) : Set ℝ≥0 :=
  {p : ℝ≥0 | ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1}

@[simp]
theorem mem_tildePcSet {d : ℕ} {p : ℝ≥0} :
    p ∈ tildePcSet d ↔
      ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1 :=
  Iff.rfl

/-- The Duminil-Copin–Tassion threshold `p̃_c(d) = sup {p : ∃ S ∋ 0 finite, φ_p(S) < 1}`. -/
noncomputable def tildePc (d : ℕ) : ℝ≥0 :=
  sSup (tildePcSet d)

end Percolation

end StatMech
