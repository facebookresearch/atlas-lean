/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.CylinderDeriv
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.Theta
public import MathlibExt.Probability.Percolation.TildePc
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# The box-crossing probability as a polynomial in `p`

The event that the origin is connected inside `Λ_n` to the vertex boundary of `Λ_n` depends only on
the finitely many edges of `Λ_n` and is increasing. Its probability is therefore a polynomial in
`p`, differentiable with nonnegative derivative on `[0, 1]` (Russo's formula).

## Main definitions

* `StatMech.Percolation.boxEdgeFinset`: the pairs of sites of the box `Λ_n` (`boxFinset` is defined
  in `Theta`).
* `StatMech.Percolation.boxCrossingEvent`: `0` is joined inside `Λ_n` to the vertex boundary of
  `Λ_n`.
* `StatMech.Percolation.boxCrossProb`: its probability.

## Main results

* `StatMech.Percolation.boxCrossingEvent_dependsOn`,
  `StatMech.Percolation.boxCrossingEvent_isIncreasing`.
* `StatMech.Percolation.boxCrossProb_eq_prob`: `boxCrossProb` equals the polynomial `StatMech.prob`.
* `StatMech.Percolation.hasDerivAt_boxCrossProb`, `StatMech.Percolation.deriv_boxCrossProb_nonneg`.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745.
-/

@[expose] public section

open MeasureTheory Function Set
open scoped NNReal
open StatMech

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

/-- All unordered pairs of sites of `Λ_n` (containing the lattice edges of `Λ_n`). -/
noncomputable def boxEdgeFinset (d n : ℕ) : Finset (Sym2 (Site d)) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).image (fun p => s(p.1, p.2))

theorem mem_boxEdgeFinset {d n : ℕ} {e : Sym2 (Site d)} :
    e ∈ boxEdgeFinset d n ↔ ∃ x y, x ∈ box d n ∧ y ∈ box d n ∧ e = s(x, y) := by
  simp only [boxEdgeFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩
    exact ⟨x, y, by simpa using hx, by simpa using hy, he.symm⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨(x, y), ⟨by simpa using hx, by simpa using hy⟩, rfl⟩

theorem coord_of_agree (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e)
    (x y : Site d) (hx : x ∈ box d n) (hy : y ∈ box d n) : ω s(x, y) = ω' s(x, y) := by
  apply h
  simp only [boxEdgeFinset, Finset.coe_image, Finset.coe_product, Set.mem_image, Set.mem_prod]
  exact ⟨(x, y), ⟨by simp [hx], by simp [hy]⟩, rfl⟩

/-- The event that the origin is joined by an open path inside `Λ_n` to the vertex boundary of
`Λ_n`. -/
def boxCrossingEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ (x : Site d) (hx : x ∈ box d n), x ∈ vertexBoundary d n ∧
       ∃ (h0 : origin d ∈ box d n),
         ConnectedWithin d ω (box d n) ⟨origin d, h0⟩ ⟨x, hx⟩}

@[simp]
theorem mem_boxCrossingEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ boxCrossingEvent d n ↔ ∃ (x : Site d) (hx : x ∈ box d n), x ∈ vertexBoundary d n ∧
      ∃ (h0 : origin d ∈ box d n),
        ConnectedWithin d ω (box d n) ⟨origin d, h0⟩ ⟨x, hx⟩ :=
  Iff.rfl

theorem openSubgraphInduce_box_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y)) :
    openSubgraphInduce d ω (box d n) = openSubgraphInduce d ω' (box d n) := by
  apply SimpleGraph.ext
  ext a b
  simp only [openSubgraphInduce_adj, openSubgraph_adj]
  rw [h a b a.2 b.2]

theorem boxCrossingEvent_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
    ω ∈ boxCrossingEvent d n ↔ ω' ∈ boxCrossingEvent d n := by
  have hcoord : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y) :=
    coord_of_agree n h
  have hG := openSubgraphInduce_box_congr n hcoord
  unfold boxCrossingEvent ConnectedWithin
  simp only [Set.mem_ofPred_eq, hG]

theorem boxCrossingEvent_dependsOn (n : ℕ) :
    DependsOn ((boxCrossingEvent d n).indicator (fun _ => (1 : ℝ)))
      ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff := boxCrossingEvent_congr n (fun e he => h e he)
  by_cases hω : ω ∈ boxCrossingEvent d n
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]

theorem boxCrossingEvent_isIncreasing (n : ℕ) : IsIncreasing (boxCrossingEvent d n) := by
  intro a b hab ha
  obtain ⟨x, hx, hxb, h0, hconn⟩ := ha
  refine ⟨x, hx, hxb, h0, hconn.mono ?_⟩
  intro u v huv
  simp only [openSubgraphInduce_adj, openSubgraph_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  have := hab s(u, v)
  rw [huv.2] at this
  exact le_antisymm (Bool.le_true _) this

/-- The probability of `boxCrossingEvent d n`. -/
noncomputable def boxCrossProb (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (boxCrossingEvent d n)

theorem boxCrossProb_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    0 ≤ boxCrossProb d p hp n :=
  measureReal_nonneg

theorem boxCrossProb_eq_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    boxCrossProb d p hp n
      = prob (p : ℝ) ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) := by
  unfold boxCrossProb
  exact realProb_cylinder_eq_prob (E := Sym2 (Site d)) p hp (boxCrossingEvent d n)
    (boxEdgeFinset d n) (boxCrossingEvent_dependsOn n)

theorem hasDerivAt_boxCrossProb (n : ℕ) (q : ℝ) :
    HasDerivAt (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)))
      (∑ e : ↥(boxEdgeFinset d n),
        pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e) q :=
  hasDerivAt_realProb_cylinder_pivotal (boxCrossingEvent d n)
    (boxCrossingEvent_isIncreasing n) (boxEdgeFinset d n) q

theorem deriv_boxCrossProb (n : ℕ) (q : ℝ) :
    deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q
      = ∑ e : ↥(boxEdgeFinset d n),
          pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e :=
  deriv_realProb_cylinder_pivotal (boxCrossingEvent d n)
    (boxCrossingEvent_isIncreasing n) (boxEdgeFinset d n) q

theorem differentiable_boxCrossProb (n : ℕ) :
    Differentiable ℝ
      (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) :=
  differentiable_realProb_cylinder (boxCrossingEvent d n) (boxEdgeFinset d n)

theorem deriv_boxCrossProb_nonneg (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q := by
  rw [deriv_boxCrossProb]
  refine Finset.sum_nonneg (fun e _ => ?_)
  unfold pivotalProb configWeight edgeWeight
  refine Finset.sum_nonneg (fun ω _ => ?_)
  refine mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) ?_
  refine Finset.prod_nonneg (fun j _ => ?_)
  by_cases h : ω j
  · simpa [h] using hq0
  · simpa [h] using sub_nonneg.mpr hq1

end Percolation

end StatMech
