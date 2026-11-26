/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ArrayClosure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ArrayClosure`

* Refutations: `RecursiveRectangleArrayCertificate`, `MacroArrayCertificate` and
  `PointwiseMacroArrayCertificate` are empty for every planar dual pair and probability measure,
  and `TwoLevelBoundaryScoreArray` is empty for every FKG probability measure (the library's
  `.false` lemmas, stated as `IsEmpty`).
* `adjacent_height_array_contradiction_of_primal_dual_bounded_limits` on explicit tables: with
  all primal crossings `1` and all dual crossings `0`, every hypothesis except the dual limits
  holds, so the lemma refutes the dual limits.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ArrayClosure

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Recursive rectangle-array certificates do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] : IsEmpty (D.RecursiveRectangleArrayCertificate mu) :=
  ⟨PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false D mu⟩

-- Macro-array certificates, bundled or pointwise, do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] :
    IsEmpty (D.MacroArrayCertificate mu) ∧ IsEmpty (D.PointwiseMacroArrayCertificate mu) :=
  ⟨⟨PeriodicPlanarDualPair.MacroArrayCertificate.false D mu⟩,
    ⟨PeriodicPlanarDualPair.PointwiseMacroArrayCertificate.false D mu⟩⟩

-- Two-level boundary-score arrays do not exist under FKG.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (hFKG : IsFKG mu) (B : ℝ) :
    IsEmpty (D.TwoLevelBoundaryScoreArray mu B) :=
  ⟨PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray.false D mu hFKG⟩

-- All-one primal tables with zero dual tables: the dual limits must fail.
example : ¬ ∀ k : ℕ → ℕ, (∀ n, k n ≤ 0 + 1) →
    Tendsto (fun _ : ℕ => max (0 : ℝ) 0) atTop (nhds 1) := fun h =>
  adjacent_height_array_contradiction_of_primal_dual_bounded_limits (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) tendsto_const_nhds tendsto_const_nhds
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by simp) h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ArrayClosure
