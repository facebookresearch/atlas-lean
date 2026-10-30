/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Limits

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Limits`

* `fkProb_le_wiredFkProb_increasing` on `⊤ : SimpleGraph (Fin 2)` with both vertices on the
  boundary, at `p = 1/2`, `q = 2`, applied to the increasing event "the edge `s(0, 1)` is open";
* `monotone_extendEdge` and `isIncreasing_preimage_extendEdge` on a concrete event;
* `freeFiniteMeasure_dominated` at `d = 2`, `n = 1`, `p = 1/2`, `q = 2`, applied to the
  increasing measurable event "the edge between the origin and `e₀` is open" of `ℤ²`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Limits

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- The event "the coordinate `e` is open". -/
def edgeOpen {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

/-- "The coordinate `e` is open" is an increasing event. -/
theorem isIncreasing_edgeOpen {E : Type*} (e : E) : IsIncreasing (edgeOpen e) := by
  intro x y hxy hx
  have h := hxy e
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- "The coordinate `e` is open" is measurable for the product σ-algebra. -/
theorem measurableSet_edgeOpen {E : Type*} (e : E) : MeasurableSet (edgeOpen e) :=
  (measurable_pi_apply (X := fun _ : E => Bool) e) (measurableSet_singleton true)

-- Free ≤ wired on the finite graph `⊤ : SimpleGraph (Fin 2)` (both vertices wired), for the
-- event that the edge is open.
example :
    (∑ ω, (edgeOpen (s(0, 1) : Sym2 (Fin 2))).indicator (fun _ => (1 : ℝ)) ω
        * fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω)
      ≤ ∑ ω, (edgeOpen (s(0, 1) : Sym2 (Fin 2))).indicator (fun _ => (1 : ℝ)) ω
        * wiredFkProb (⊤ : SimpleGraph (Fin 2)) (fun _ => True) (1 / 2) 2 ω :=
  fkProb_le_wiredFkProb_increasing _ _ (by norm_num) (by norm_num) (by norm_num)
    (isIncreasing_edgeOpen _)

-- `extendEdge` is monotone, so preimages of increasing events are increasing.
example (d n : ℕ) (e : Sym2 (Site d)) :
    IsIncreasing (extendEdge d n ⁻¹' edgeOpen e) :=
  isIncreasing_preimage_extendEdge d n (isIncreasing_edgeOpen e)

/-- The unit vector `e₀` of `ℤ²`. -/
def e0 : Site 2 := fun i => if i = 0 then 1 else 0

-- The free box measure on `Λ_1 ⊆ ℤ²` gives the edge `{0, e₀}` at most the probability the wired
-- box measure gives it (`p = 1/2`, `q = 2`).
example :
    (freeFiniteMeasure 2 1 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
        : Measure (ConfigSpace (Sym2 (Site 2)))).real (edgeOpen s(0, e0))
      ≤ (wiredFiniteMeasure 2 1 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
        : Measure (ConfigSpace (Sym2 (Site 2)))).real (edgeOpen s(0, e0)) :=
  freeFiniteMeasure_dominated 2 1 (by norm_num) (by norm_num) (by norm_num) _
    (measurableSet_edgeOpen _) (isIncreasing_edgeOpen _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Limits
