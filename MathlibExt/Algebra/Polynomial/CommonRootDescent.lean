/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The theorem and gcd argument are adapted from
`P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean`, lines 11-53,
in Fermat's Last Theorem in Lean 4 at
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0:
https://www.apache.org/licenses/LICENSE-2.0
The source was assembled by AI agents; no individual author is named.
-/

module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Descent of a unique common root

If `A` splits with simple roots in a field extension, its unique common root
with any base-field polynomial `B` belongs to the base field. The gcd has
exactly one simple root, hence degree one, so it already splits over the base.
-/

public section

namespace Polynomial

/-- A unique common root descends when the first polynomial is nonzero and
splits with simple roots in the extension. The second polynomial may be zero;
neither polynomial needs to be monic. -/
theorem mem_range_of_unique_common_root {F L : Type*}
    [Field F] [Field L] [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0)
    (hAs : (A.map (algebraMap F L)).Splits)
    (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L)
    (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0)
    (huniq : ∀ y : L, Polynomial.aeval y A = 0 →
      Polynomial.aeval y B = 0 → y = x) :
    x ∈ (algebraMap F L).range := by
  classical
  let g := EuclideanDomain.gcd A B
  have hg0 : g ≠ 0 := fun h ↦ hA (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgA : g ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hAm0 : A.map (algebraMap F L) ≠ 0 := map_ne_zero hA
  have hgm0 : g.map (algebraMap F L) ≠ 0 := map_ne_zero hg0
  have hxg : (g.map (algebraMap F L)).IsRoot x := by
    rw [IsRoot.def, eval_map]
    exact eval₂_gcd_eq_zero hxA hxB
  have hnd := Multiset.nodup_of_le
    (roots.le_of_dvd hAm0 (map_dvd _ hgA)) hAnd
  have hr : (g.map (algebraMap F L)).roots = {x} := by
    apply le_antisymm
    · apply (Multiset.le_iff_subset hnd).mpr
      intro y hy
      rw [Multiset.mem_singleton]
      have hy' := (mem_roots_map hg0).mp hy
      exact huniq y (root_left_of_root_gcd hy')
        (root_right_of_root_gcd hy')
    · exact Multiset.singleton_le.mpr ((mem_roots hgm0).mpr hxg)
  have hgs := hAs.of_dvd hAm0 (map_dvd _ hgA)
  have hdeg : g.natDegree = 1 := by
    rw [← natDegree_map (algebraMap F L), hgs.natDegree_eq_card_roots, hr]
    rfl
  exact (Splits.of_natDegree_eq_one hdeg).mem_range_of_isRoot hg0 hxg

end Polynomial
