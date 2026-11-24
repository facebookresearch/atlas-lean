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
# The original left and right Haar representations in an abelian group

A locally compact commutative group has trivial modular character. The
actual normalized right action on Haar `L²(G,H)` is therefore exactly the
left action by the inverse element. This comparison supplies the original
regular-representation identification used in the abelian dual action and
Takai statements, on the same actual Haar carrier and all Hilbert universes.
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

/-- The actual abelian right regular unitary is the actual inverse left regular unitary. -/
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
