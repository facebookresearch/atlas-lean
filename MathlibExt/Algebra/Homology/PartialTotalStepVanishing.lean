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

public import MathlibExt.Algebra.Homology.PartialTotalStepHomology

/-!
# Below-row vanishing for partial-total filtration steps

The mapping cone of a partial-total filtration step is quasi-isomorphic to
the extended signed row.  This file records that comparison in every degree
and proves vanishing below the row's support.

These are prerequisites for a later `HasSpectralSequence` instance.  No
spectral page or convergence statement is made here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- In every cochain degree, mapping-cone homology of the `p`th filtration
step is homology of the extended signed `p`th row. -/
noncomputable def partialTotalStepConeExtendedRowHomologyIso (p : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone
        (B.partialTotalStepCochainShortComplex p).f).homology n ≅
      ((B.totalRow p).extend ComplexShape.embeddingDownNat).homology n := by
  let S := B.partialTotalStepCochainShortComplex p
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact p
  let desc := CochainComplex.mappingCone.descShortComplex S
  let _ : QuasiIso desc :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  exact asIso (HomologicalComplex.homologyMap desc n) ≪≫
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso p) n

/-- Mapping-cone homology of the `p`th filtration step vanishes in the
cochain degree corresponding to a chain degree strictly below `p`. -/
theorem isZero_partialTotalStepConeHomology_of_lt
    (p k : ℕ) (h : k < p) :
    IsZero ((CochainComplex.mappingCone
      (B.partialTotalStepCochainShortComplex p).f).homology (-(k : ℤ))) := by
  have hRow : IsZero ((B.totalRow p).homology k) :=
    ((B.totalRow p).sc k).isZero_homology_of_isZero_X₂
      (B.totalRow_isZero_X p k h)
  have hExtended : IsZero
      (((B.totalRow p).extend ComplexShape.embeddingDownNat).homology
        (-(k : ℤ))) :=
    IsZero.of_iso hRow
      ((B.totalRow p).extendHomologyIso
        ComplexShape.embeddingDownNat rfl)
  exact IsZero.of_iso hExtended
    (B.partialTotalStepConeExtendedRowHomologyIso p (-(k : ℤ)))

end HomologicalComplex₂

end
