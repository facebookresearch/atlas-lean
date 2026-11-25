/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SingerProductDifferenceBasis

/-! # Tests for the Singer product construction -/

open MetaMathlibExt

private def residues (i : Fin 2) : ℤ := if i = 0 then 2 else 3

private theorem residues_mem (i : Fin 2) : residues i ∈ Finset.Icc (1 : ℤ) 3 :=
  (by decide : ∀ i, residues i ∈ Finset.Icc (1 : ℤ) 3) i

private theorem residues_singer : ∀ r ∈ Finset.Icc (1 : ℤ) 2,
    ∃! ij : Fin 2 × Fin 2, ij.1 ≠ ij.2 ∧ residues ij.1 - residues ij.2 ≡ r [ZMOD 3] := by
  intro r hr
  have hr' := Finset.mem_Icc.mp hr
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨(1, 0), by decide, by decide⟩
  · exact ⟨(0, 1), by decide, by decide⟩

private def basis : Finset ℤ := {-1, 0, 1}

private theorem two_le_liftCount : ∀ s ∈ Finset.Icc (1 : ℤ) 3,
    2 ≤ subRepCount ((Finset.univ ×ˢ basis).image fun p : Fin 2 × ℤ =>
      residues p.1 + 3 * p.2) s :=
  singer_product_diffBasis 2 1 1 residues residues_mem residues_singer basis (by decide)

-- The difference 1 comes from 3 - 2 and hence needs the quotient-zero case.
example : 2 ≤ subRepCount ((Finset.univ ×ˢ basis).image fun p : Fin 2 × ℤ =>
    residues p.1 + 3 * p.2) 1 :=
  two_le_liftCount 1 (by decide)

-- The difference 2 uses the negative representative difference 2 - 3.
example : 2 ≤ subRepCount ((Finset.univ ×ˢ basis).image fun p : Fin 2 × ℤ =>
    residues p.1 + 3 * p.2) 2 :=
  two_le_liftCount 2 (by decide)

-- The upper endpoint has residue zero.
example : 2 ≤ subRepCount ((Finset.univ ×ˢ basis).image fun p : Fin 2 × ℤ =>
    residues p.1 + 3 * p.2) 3 :=
  two_le_liftCount 3 (by decide)

-- The empty basis is allowed for an empty horizon, for arbitrary multiplicity.
example (g : ℕ) : ∀ s ∈ Finset.Icc (1 : ℤ) 0,
    g ≤ subRepCount ((Finset.univ ×ˢ (∅ : Finset ℤ)).image fun p : Fin 2 × ℤ =>
      residues p.1 + 3 * p.2) s :=
  singer_product_diffBasis g 1 0 residues residues_mem residues_singer ∅ (by simp)
