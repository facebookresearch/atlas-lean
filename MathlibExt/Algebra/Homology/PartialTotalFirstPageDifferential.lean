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
# The transported first-page differential

This file transports the actual page-one differential through the canonical
signed-row homology isomorphisms.  It records the inverse conjugacy formula
and the zero-boundary behavior at filtration degree zero.

Identification with the horizontal bicomplex differential, E₂, Tor, and
convergence are deliberately deferred.
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

/-- The page-one shape connects `(m+1,q)` to `(m,q)`. -/
theorem coreE₁IncreasingHomologicalNat_rel_succ (m q : ℕ) :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).Rel
      (m + 1, q) (m, q) := by
  simp only [ComplexShape.spectralSequenceNat_rel_iff]
  constructor <;> omega

/-- The actual page-one differential, transported to homology of the signed
rows.  Its source has total degree `m+1+q` and its target degree `m+q`. -/
noncomputable def partialTotalE₁RowDifferential (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  (B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q).inv ≫
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
      (m + 1, q) (m, q) ≫
    (B.partialTotalSpectralSequenceFirstPageRowIso m q).hom

/-- Conjugating the transported row differential back by the row isomorphisms
recovers the actual page-one differential. -/
theorem partialTotalSpectralSequenceFirstPage_d_eq (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
        (m + 1, q) (m, q) =
      (B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q).hom ≫
        B.partialTotalE₁RowDifferential m q ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso m q).inv := by
  simp only [partialTotalE₁RowDifferential, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- There is no outgoing page-one differential from filtration degree zero. -/
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
