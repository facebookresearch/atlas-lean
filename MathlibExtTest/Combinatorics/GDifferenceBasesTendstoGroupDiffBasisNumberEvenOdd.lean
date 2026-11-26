/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberEvenOdd
import Mathlib.Topology.Constructions.SumProd

/-!
# Tests for even and odd difference basis limits

For the prime three and multiplicity one, the two normalized parity sequences converge jointly
to a pair of positive real numbers.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2.
-/

namespace MathlibExtTest.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberEvenOdd

open Filter Topology MetaMathlibExt

example : ∃ L : ℝ × ℝ, 0 < L.1 ∧ 0 < L.2 ∧ Tendsto (fun k : ℕ =>
    ((groupDiffBasisNumber 1 (Fin (2 * k) → ZMod 3) : ℝ) / Real.sqrt ((3 : ℝ) ^ (2 * k)),
      (groupDiffBasisNumber 1 (Fin (2 * k + 1) → ZMod 3) : ℝ) /
        Real.sqrt ((3 : ℝ) ^ (2 * k + 1)))) atTop (𝓝 L) := by
  obtain ⟨⟨Le, he, hLe⟩, ⟨Lo, ho, hLo⟩⟩ :=
    tendsto_groupDiffBasisNumber_even_odd 3 1 (by decide) (by decide)
  exact ⟨(Le, Lo), he, ho, hLe.prodMk_nhds hLo⟩

end MathlibExtTest.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberEvenOdd
