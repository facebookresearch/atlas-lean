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

public import MathlibExt.MeasureTheory.Group.ModularCharacterAbelian
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRightRegularRepresentation

/-!
# Left and right regular representations of an abelian group

For a locally compact abelian Borel topological group and regular Haar measure, the modular
character is one. Normalized right translation therefore equals left translation by the inverse:
`R_g=λ_(g⁻¹)`.

The equality is on the same Hilbert-valued Haar L² space, with complete complex Hilbert
coefficients. No Hausdorff or nonzero coefficient-space hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter

namespace StronglyContinuousUnitaryRepresentation

noncomputable section

universe uG uH

variable (G : Type uG) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Abelian right regular unitary equals inverse left translation.** Let `G` be a locally
compact abelian Borel topological group, `μ` regular Haar measure and `H` a complete
complex Hilbert space. For `g∈G`, `haarRightRegular G μ H g=haarLeftRegular G μ H g⁻¹`,
since `Δ(g)=1` and `xg=gx`. -/
theorem haarRightRegular_eq_haarLeftRegular_inv (g : G) :
    haarRightRegular G μ H g = haarLeftRegular G μ H g⁻¹ := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [haarRightRegular_ae_eq G μ H g ξ,
    haarLeftRegular_ae_eq G μ H g⁻¹ ξ] with x hRight hLeft
  rw [hRight, hLeft]
  simp only [Measure.modularCharacter_eq_one_of_comm, NNReal.coe_one,
    Real.one_rpow, one_smul, inv_inv, mul_comm]

end

end StronglyContinuousUnitaryRepresentation
