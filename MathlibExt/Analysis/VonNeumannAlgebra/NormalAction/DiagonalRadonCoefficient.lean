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

public import MathlibExt.MeasureTheory.Measure.RadonProduct.Haar
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.Pullback
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CoefficientNormality

/-!
# Actual coordinate coefficients on the original Hilbert-valued Radon square

Pullback of the original normal action along the first projection gives
the literal first-coordinate regular coefficient. For an abelian group,
pullback along `(s,t) ↦ s*t⁻¹` gives the literal difference-coordinate
coefficient. Both are the existing actual regular pointwise operators on
the full `Lp H 2 (radonProd μ μ)` and retain their original a.e. values.

The original normal coefficient API supplies actual normal homomorphisms
into the full bounded-operator algebra on this same Borel Radon carrier.
No normal range, Fourier transform, shear or spatial identification is
selected from an open statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The actual Borel measurable space of the original topological product. -/
local instance instRadonCoefficientProductMeasurableSpace : MeasurableSpace (G × G) :=
  borel (G × G)
local instance instRadonCoefficientProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

/-- The literal continuous group homomorphism given by the original coordinate difference. -/
def differenceCoordinateHom : (G × G) →ₜ* G :=
  ContinuousMonoidHom.fst G G * (ContinuousMonoidHom.snd G G)⁻¹

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The difference homomorphism has its original multiplicative coordinate values. -/
@[simp]
theorem differenceCoordinateHom_apply (z : G × G) :
    differenceCoordinateHom z = z.1 * z.2⁻¹ :=
  rfl

/-- The original first-coordinate coefficient is the actual regular operator of the pulled-back action. -/
def firstRadonCoefficient (α : NormalAction G M) (x : M) :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ) :=
  regularCoefficient (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G)) x

omit [μ.Regular] in
/-- Every full Radon product-L2 vector has the original first-coordinate coefficient formula a.e. -/
theorem firstRadonCoefficient_ae_eq (α : NormalAction G M) (x : M)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    firstRadonCoefficient μ α x ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => (α z.1⁻¹ x : H →L[ℂ] H) (ξ z) :=
  regularCoefficient_ae_eq (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G)) x ξ

/-- The original first-coordinate coefficient carries the existing proved normality. -/
def firstRadonCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :=
  regularCoefficientNormalHom (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G))

/-- The normal first-coordinate map has the exact original bounded-operator value. -/
@[simp]
theorem firstRadonCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (firstRadonCoefficientNormalHom μ α x :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        firstRadonCoefficient μ α x :=
  rfl

/-- The original recovered coefficient is the actual regular operator of the difference pullback. -/
def recoveredRadonCoefficient (α : NormalAction G M) (x : M) :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ) :=
  regularCoefficient (Measure.radonProd μ μ) (comp α differenceCoordinateHom) x

omit [μ.Regular] in
/-- Every full Radon product-L2 vector has the exact original inverse-difference coefficient a.e. -/
theorem recoveredRadonCoefficient_ae_eq (α : NormalAction G M) (x : M)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    recoveredRadonCoefficient μ α x ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => (α (z.1 * z.2⁻¹)⁻¹ x : H →L[ℂ] H) (ξ z) := by
  have h := regularCoefficient_ae_eq (Measure.radonProd μ μ)
    (comp α differenceCoordinateHom) x ξ
  filter_upwards [h] with z hz
  change regularCoefficient (Measure.radonProd μ μ) (comp α differenceCoordinateHom) x ξ z = _
  rw [hz]
  change (α (differenceCoordinateHom z⁻¹) x : H →L[ℂ] H) (ξ z) = _
  rw [map_inv, differenceCoordinateHom_apply]

/-- The recovered-coordinate coefficient carries the existing proved normality on the original carrier. -/
def recoveredRadonCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :=
  regularCoefficientNormalHom (Measure.radonProd μ μ) (comp α differenceCoordinateHom)

/-- The normal recovered-coordinate map is the same original bounded pointwise operator. -/
@[simp]
theorem recoveredRadonCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (recoveredRadonCoefficientNormalHom μ α x :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        recoveredRadonCoefficient μ α x :=
  rfl

end

end VonNeumannAlgebra.NormalAction
