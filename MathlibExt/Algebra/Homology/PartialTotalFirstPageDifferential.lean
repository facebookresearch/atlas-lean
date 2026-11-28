/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalFirstPage
public import MathlibExt.Algebra.Homology.PartialTotalHasSpectralSequence

/-!
# First-page differentials in signed-row homology

For a first-quadrant bicomplex `B` in an abelian category, the first page of the partial-total
spectral sequence has differential of bidegree `(-1, 0)`. Conjugating this differential by the
signed-row homology coordinates gives a map from `H_(m+1+q)(B.totalRow (m+1))` to
`H_(m+q)(B.totalRow m)`.

The inverse conjugacy formula expresses the page differential through this row-homology map.
Every outgoing differential from column zero vanishes because its target would have negative
column index.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- Successor columns are related by the first-page shape.

The increasing homological core has first-page differential shape `(-1, 0)`. Thus `(m + 1, q)`
and `(m, q)` are related for every pair of natural indices `m` and `q`. -/
theorem coreE₁IncreasingHomologicalNat_rel_succ (m q : ℕ) :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).Rel
      (m + 1, q) (m, q) := by
  simp only [ComplexShape.spectralSequenceNat_rel_iff]
  constructor <;> omega

/-- First-page differential transported between adjacent row homologies.

For a first-quadrant bicomplex, conjugate the first-page differential from `(m + 1, q)` to
`(m, q)` by the first-page row isomorphisms. This gives `H_(m+1+q)(B.totalRow (m+1)) ⟶
H_(m+q)(B.totalRow m)`. -/
noncomputable def partialTotalE₁RowDifferential (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  (B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q).inv ≫
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
      (m + 1, q) (m, q) ≫
    (B.partialTotalSpectralSequenceFirstPageRowIso m q).hom

/-- First-page differential recovered from its row coordinates.

The differential from `(m + 1, q)` to `(m, q)` is the source row-coordinate isomorphism
followed by `B.partialTotalE₁RowDifferential m q` and the inverse target row-coordinate
isomorphism. -/
theorem partialTotalSpectralSequenceFirstPage_d_eq (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
        (m + 1, q) (m, q) =
      (B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q).hom ≫
        B.partialTotalE₁RowDifferential m q ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso m q).inv := by
  simp only [partialTotalE₁RowDifferential, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every first-page differential out of column zero vanishes.

For any natural `q` and any target bidegree `pq'`, the first-page differential from `(0, q)`
to `pq'` is zero. The differential shape would require a predecessor column of zero. -/
theorem partialTotalSpectralSequenceFirstPage_d_zero
    (q : ℕ) (pq' : ℕ × ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
      (0, q) pq' = 0 := by
  apply HomologicalComplex.shape
  intro h
  simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
  omega

end HomologicalComplex₂

end
