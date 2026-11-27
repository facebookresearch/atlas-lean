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
# First and difference coordinates in a Radon square

For a normal action of a Hausdorff locally compact abelian group, use `Lp H 2 (radonProd μ μ)`
on the Borel topological square. Pullback along `(s,t) ↦ s` gives the first coefficient the L²
class represented almost everywhere for `radonProd μ μ` by `(s,t) ↦ α_(s⁻¹)(x)ξ(s,t)`.

Pullback along the continuous homomorphism `(s,t) ↦ st⁻¹` gives the difference coefficient the
L² class represented almost everywhere for `radonProd μ μ` by `(s,t) ↦ α_((st⁻¹)⁻¹)(x)ξ(s,t)`.
Both define normal star homomorphisms into the full operator algebra of this Radon L² space. No
Fourier transform or shear identification is assumed.

Here `=ᵐ[radonProd μ μ]` denotes equality of measurable representatives almost everywhere for
the indicated Radon-product measure. The normal homomorphisms and operator identities are
equalities of bounded operators.
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

/-- **Borel measurable structure for a Radon coefficient square.** For a topological space
`G`, use `borel (G×G)` from the product topology as the measurable structure on its
square. -/
local instance instRadonCoefficientProductMeasurableSpace : MeasurableSpace (G × G) :=
  borel (G × G)
local instance instRadonCoefficientProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

/-- **Continuous difference-coordinate group homomorphism.** For an abelian topological group
`G`, `differenceCoordinateHom : G×G →ₜ* G` sends `(s,t)` to `st⁻¹`. No measure, local
compactness or Hausdorff condition is required for this homomorphism. -/
def differenceCoordinateHom : (G × G) →ₜ* G :=
  ContinuousMonoidHom.fst G G * (ContinuousMonoidHom.snd G G)⁻¹

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Value of the multiplicative difference coordinate.** For an abelian topological group
`G` and `(s,t)∈G×G`, `differenceCoordinateHom (s,t)=st⁻¹`. -/
@[simp]
theorem differenceCoordinateHom_apply (z : G × G) :
    differenceCoordinateHom z = z.1 * z.2⁻¹ :=
  rfl

/-- **First-coordinate regular coefficient on the Radon square.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. `firstRadonCoefficient μ α x : L_R →L[ℂ] L_R` is the regular
coefficient of the action pulled back by `(s,t) ↦ s`. -/
def firstRadonCoefficient (α : NormalAction G M) (x : M) :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ) :=
  regularCoefficient (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G)) x

omit [μ.Regular] in
/-- **Almost-everywhere first-coordinate coefficient formula.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and regular Haar measure `μ`, `H` a
complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with norm-continuous
inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel topological square.
for `x∈M`, `ξ∈L_R`, `firstRadonCoefficient μ α x ξ =ᵐ[radonProd μ μ] ((s,t) ↦
α_(s⁻¹)(x)ξ(s,t))` almost everywhere for `radonProd μ μ`.

Here `=ᵐ[radonProd μ μ]` denotes equality of measurable representatives almost everywhere
for the indicated Radon-product measure. The normal homomorphisms and operator identities
are equalities of bounded operators. -/
theorem firstRadonCoefficient_ae_eq (α : NormalAction G M) (x : M)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    firstRadonCoefficient μ α x ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => (α z.1⁻¹ x : H →L[ℂ] H) (ξ z) :=
  regularCoefficient_ae_eq (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G)) x ξ

/-- **Normal first-coordinate coefficient map on the Radon square.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. `firstRadonCoefficientNormalHom μ α : NormalStarAlgHom M B(L_R)` has
the first-coordinate regular coefficient as its operator value. -/
def firstRadonCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :=
  regularCoefficientNormalHom (Measure.radonProd μ μ) (comp α (ContinuousMonoidHom.fst G G))

/-- **Operator value of the normal first-coordinate coefficient.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. for `x∈M`, the normal map's bounded-operator value is
`firstRadonCoefficient μ α x`. -/
@[simp]
theorem firstRadonCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (firstRadonCoefficientNormalHom μ α x :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        firstRadonCoefficient μ α x :=
  rfl

/-- **Difference-coordinate regular coefficient on the Radon square.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. `recoveredRadonCoefficient μ α x` is the regular coefficient for the
action pulled back along `(s,t) ↦ st⁻¹`. -/
def recoveredRadonCoefficient (α : NormalAction G M) (x : M) :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ) :=
  regularCoefficient (Measure.radonProd μ μ) (comp α differenceCoordinateHom) x

omit [μ.Regular] in
/-- **Almost-everywhere inverse-difference coefficient formula.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. for `x∈M`, `ξ∈L_R`, `recoveredRadonCoefficient μ α x ξ =ᵐ[radonProd μ
μ] ((s,t) ↦ α_((st⁻¹)⁻¹)(x)ξ(s,t))` almost everywhere.

Here `=ᵐ[radonProd μ μ]` denotes equality of measurable representatives almost everywhere
for the indicated Radon-product measure. The normal homomorphisms and operator identities
are equalities of bounded operators. -/
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

/-- **Normal difference-coordinate coefficient map.** Let `G` be a Hausdorff locally compact
abelian topological group with Borel structure and regular Haar measure `μ`, `H` a
complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with norm-continuous
inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel topological square.
`recoveredRadonCoefficientNormalHom μ α : NormalStarAlgHom M B(L_R)` has the
difference-pullback regular operator as its value. -/
def recoveredRadonCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :=
  regularCoefficientNormalHom (Measure.radonProd μ μ) (comp α differenceCoordinateHom)

/-- **Operator value of the normal recovered-coordinate coefficient.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and regular Haar measure
`μ`, `H` a complete complex Hilbert space, and `α` a normal action on `M⊆B(H)` with
norm-continuous inverse predual orbits. Put `L_R=Lp H 2 (radonProd μ μ)` on the Borel
topological square. for `x∈M`, the operator underlying `recoveredRadonCoefficientNormalHom
μ α x` is `recoveredRadonCoefficient μ α x`. -/
@[simp]
theorem recoveredRadonCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (recoveredRadonCoefficientNormalHom μ α x :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        recoveredRadonCoefficient μ α x :=
  rfl

end

end VonNeumannAlgebra.NormalAction
