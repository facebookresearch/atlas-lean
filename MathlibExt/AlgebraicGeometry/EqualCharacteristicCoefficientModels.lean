/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LocalField.Basic

/-!
# Actual equal-characteristic local coefficients

The coefficient field is literally k((t)), for the actual finite field k.
Its integer ring is the actual unit ball of the native t-adic valuation.
The native power-series coefficient ring is identified with that exact
integer ring. The residue-degree datum uses the cardinality of k itself.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1;
Zhu, arXiv:1407.8519v3, Section 0.1.1. The native Laurent-series
valuation/completeness results are reused from pinned Mathlib.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels

open scoped WithZero

variable (k : Type) [Field k]

/-- The original coefficient field, not a separately chosen local-field carrier. -/
abbrev CoefficientField := LaurentSeries k

/-- The actual valuation integer ring of that native t-adic field. -/
abbrev Integers := ↥((Valued.v : Valuation (CoefficientField k) ℤᵐ⁰).integer)

/-- The original integral coefficients are the genuine power-series ring. -/
abbrev IntegralCoefficients := PowerSeries k

/-- The actual original power-series embedding in the Laurent-series field. -/
def integralEmbedding : IntegralCoefficients k →+* CoefficientField k :=
  algebraMap (PowerSeries k) (LaurentSeries k)

/-- The source valuative relation is the native t-adic valuation of k((t)). -/
@[instance_reducible]
def valuativeRelation : ValuativeRel (CoefficientField k) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (CoefficientField k) ℤᵐ⁰)

/-- The native integer ring is exactly the image of the original power series. -/
def integerEquiv : IntegralCoefficients k ≃+* Integers k :=
  RingEquiv.ofBijective
    (show IntegralCoefficients k →+* Integers k from
      { toFun := fun f ↦ ⟨integralEmbedding k f,
          (LaurentSeries.val_le_one_iff_eq_coe k _).mpr ⟨f, rfl⟩⟩
        map_zero' := by apply Subtype.ext; exact map_zero _
        map_one' := by apply Subtype.ext; exact map_one _
        map_add' := by intro a b; apply Subtype.ext; exact map_add _ _ _
        map_mul' := by intro a b; apply Subtype.ext; exact map_mul _ _ _ }) (by
    constructor
    · intro a b h
      exact HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨f, hf⟩ := (LaurentSeries.val_le_one_iff_eq_coe k x.val).mp x.property
      exact ⟨f, Subtype.ext hf⟩)

/-- The integer dictionary fixes every original integral field coefficient. -/
theorem integerEquiv_normalized (f : IntegralCoefficients k) :
    (integerEquiv k f : CoefficientField k) = integralEmbedding k f := rfl

/-- The actual original equal-characteristic uniformizer t. -/
def uniformizer : Integers k := integerEquiv k PowerSeries.X

/-- Residue degree is normalized to the original finite residue field. -/
structure ResidueData (p : ℕ) [Fact p.Prime] (k : Type)
    [Field k] [CharP k p] [Fintype k] where
  degree : ℕ
  positive : 0 < degree
  cardinality : Nat.card k = p ^ degree

end MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
