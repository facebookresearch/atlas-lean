/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.LimitsInfinite

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.LimitsInfinite`

`exists_infiniteVolume_extremal` for general `q ≥ 1`, here `q = 3` on `ℤ²` at `p = 1/2`: there is
a common subsequence of box sizes along which free and wired box measures converge weakly to
limits `φ0`, `φ1`, and `φ0(A) ≤ φ1(A)` for the clopen increasing event "the edge `s(0, e₀)` is
open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.LimitsInfinite

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

/-- "The coordinate `e` is open" is clopen in the product topology. -/
theorem isClopen_edgeOpen {E : Type*} (e : E) : IsClopen (edgeOpen e) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply e)

/-- The unit vector `e₀` of `ℤ²`. -/
def e0 : Site 2 := fun i => if i = 0 then 1 else 0

-- Ordered free/wired subsequential limits exist for `q = 3`, and the free limit gives the edge
-- `s(0, e₀)` at most the probability the wired limit gives it.
example : ∃ (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))),
    (φ0 : Measure (ConfigSpace (Sym2 (Site 2)))).real (edgeOpen s(0, e0))
      ≤ (φ1 : Measure (ConfigSpace (Sym2 (Site 2)))).real (edgeOpen s(0, e0)) := by
  obtain ⟨_, φ0, φ1, _, _, _, hle⟩ :=
    exists_infiniteVolume_extremal 2 (p := 1 / 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num)
  exact ⟨φ0, φ1, hle _ (isClopen_edgeOpen _) (isIncreasing_edgeOpen _)⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.LimitsInfinite
