/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ContinuousTuran
import Mathlib.MeasureTheory.Measure.Real

/-!
# Monotonicity of higher-dimensional continuous Turán numbers

Enlarging the ambient cube preserves each open set that avoids the pattern as a competitor.
-/

namespace MetaMathlibExt

open Set MeasureTheory in
/-- **Higher-dimensional continuous Turán numbers are monotone in the side length.** For every
set $P \subseteq \mathbb{R}^d$ and all real numbers $m \le n$,
$\mathrm{opx}(m, P, d) \le \mathrm{opx}(n, P, d)$.

The source defines $\mathrm{opx}(n, P, d)$ only for positive side lengths $n$; under the definition
used here, the inequality also holds when either side length is nonpositive.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.2
(`integers-2024-A1-lem-5-2`). -/
public theorem opxD_mono_left {d : ℕ} (P : Set (Fin d → ℝ)) {m n : ℝ} (hmn : m ≤ n) :
    opxD d m P ≤ opxD d n P := by
  have hboxes : Icc (0 : Fin d → ℝ) (fun _ => m) ⊆ Icc 0 (fun _ => n) :=
    Icc_subset_Icc_right (fun _ => hmn)
  apply Real.sSup_le _ (opxD_nonneg d n P)
  rintro _ ⟨S, ⟨hS, hSm, hfree⟩, rfl⟩
  refine le_csSup ?_ ⟨S, ⟨hS, hSm.trans hboxes, hfree⟩, rfl⟩
  refine ⟨volume.real (Icc (0 : Fin d → ℝ) (fun _ => n)), ?_⟩
  rintro _ ⟨T, ⟨_, hTn, _⟩, rfl⟩
  exact measureReal_mono hTn isCompact_Icc.measure_ne_top

end MetaMathlibExt
