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
public import MathlibExt.Analysis.VonNeumannAlgebra.HaarWeylAlgebra

/-!
# Diagonal Weyl algebra on a Hilbert-valued Radon square

Let `G` be a Hausdorff locally compact topological group with Borel structure and regular Haar
measure `μ`. For a complete complex Hilbert space `H`, use `L=Lp H 2 (radonProd μ μ)` on the
Borel topological product `G×G`.

The diagonal translation is `D_gξ(s,t)=ξ(g⁻¹s,g⁻¹t)`, and the second-coordinate character
multiplier is `V_χξ(s,t)=χ(t) • ξ(s,t)`. These strongly continuous unitary families generate the
diagonal Weyl von Neumann algebra on `L`. It is WOT closed and is the least von Neumann algebra
containing both families.

No countability or s-finiteness hypothesis is imposed. The measure is the Radon product on the
topological product's Borel structure; the Hilbert space may be zero.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped Topology CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Borel measurable structure on a topological square.** For a topological space `G`, the
measurable structure on `G×G` is `borel (G×G)`, formed from its product topology. This
definition does not require a Haar measure or a countability assumption. -/
local instance instDiagonalWeylProductMeasurableSpace : MeasurableSpace (G × G) := borel (G × G)
local instance instDiagonalWeylProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

/-- **Strongly continuous diagonal Haar translation representation.** Let `G` be a Hausdorff
locally compact topological group with its Borel structure, `μ` a regular Haar measure and
`H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel
topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
`diagonalHaarLeftRegular μ : G → U(L)` is the Haar representation of `G×G` restricted to
`g ↦ (g,g)`. -/
def diagonalHaarLeftRegular :
    StronglyContinuousUnitaryRepresentation G (Lp H 2 (Measure.radonProd μ μ)) where
  toMonoidHom :=
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular (G × G) (Measure.radonProd μ μ) H).toMonoidHom.comp
      (ContinuousMonoidHom.diag G).toMonoidHom
  continuous_orbit ξ :=
    ((StronglyContinuousUnitaryRepresentation.haarLeftRegular
      (G × G) (Measure.radonProd μ μ) H).continuous_orbit ξ).comp
        (ContinuousMonoidHom.diag G).continuous

/-- **Diagonal translation as a product-group Haar operator.** Let `G` be a Hausdorff locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel topological
product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for `g∈G`,
`diagonalHaarLeftRegular μ g` is the Haar left translation of the product group at
`(g,g)`. -/
@[simp]
theorem diagonalHaarLeftRegular_apply (g : G) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
      (StronglyContinuousUnitaryRepresentation.haarLeftRegular
        (G × G) (Measure.radonProd μ μ) H (g, g) :
          Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  rfl

/-- **Almost-everywhere diagonal translation on the Radon square.** Let `G` be a Hausdorff
locally compact topological group with its Borel structure, `μ` a regular Haar measure and
`H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel
topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for
`ξ∈L`, `(diagonalHaarLeftRegular μ g)ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` almost everywhere for `radonProd
μ μ`. -/
theorem diagonalHaarLeftRegular_ae_eq (g : G) (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ξ (g⁻¹ * z.1, g⁻¹ * z.2) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq
    (G × G) (Measure.radonProd μ μ) H (g, g) ξ

/-- **Character pullback along the second projection.** For a group `G` with a topology,
`secondCoordinateCharacterMap : PontryaginDual G →ₜ* PontryaginDual (G×G)` sends the
continuous character `χ` to `(s,t) ↦ χ(t)`. -/
def secondCoordinateCharacterMap : PontryaginDual G →ₜ* PontryaginDual (G × G) :=
  PontryaginDual.map (ContinuousMonoidHom.snd G G)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Value of a pulled-back second-coordinate character.** For a group `G` with topology, a
continuous character `χ` and `(s,t)∈G×G`, `secondCoordinateCharacterMap χ (s,t)=χ(t)`. -/
@[simp]
theorem secondCoordinateCharacterMap_apply (χ : PontryaginDual G) (z : G × G) :
    secondCoordinateCharacterMap χ z = χ z.2 :=
  rfl

/-- **Strongly continuous character multiplication on the Radon square.** Let `G` be a
Hausdorff locally compact topological group with its Borel structure, `μ` a regular Haar
measure and `H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the
Borel topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
`diagonalHaarCharacterRepresentation μ : PontryaginDual G → U(L)` is the representation `χ
↦ V_χ`, with the compact-open character topology. -/
def diagonalHaarCharacterRepresentation :
    StronglyContinuousUnitaryRepresentation (PontryaginDual G) (Lp H 2 (Measure.radonProd μ μ)) where
  toMonoidHom :=
    (HaarL2.characterMultiplierRepresentation (H := H) (Measure.radonProd μ μ)).toMonoidHom.comp
      (secondCoordinateCharacterMap (G := G)).toMonoidHom
  continuous_orbit ξ :=
    ((HaarL2.characterMultiplierRepresentation (H := H)
      (Measure.radonProd μ μ)).continuous_orbit ξ).comp
        (secondCoordinateCharacterMap (G := G)).continuous

omit [μ.Regular] in
/-- **Operator of a second-coordinate character representation.** Let `G` be a Hausdorff
locally compact topological group with its Borel structure, `μ` a regular Haar measure and
`H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel
topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
`diagonalHaarCharacterRepresentation μ χ` is the multiplier associated to the character
`(s,t) ↦ χ(t)`. -/
@[simp]
theorem diagonalHaarCharacterRepresentation_apply (χ : PontryaginDual G) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        HaarL2.characterMultiplier (H := H) (Measure.radonProd μ μ)
          (secondCoordinateCharacterMap χ) :=
  rfl

omit [μ.Regular] in
/-- **Almost-everywhere second-coordinate character action.** Let `G` be a Hausdorff locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel topological
product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for `ξ∈L`,
`(diagonalHaarCharacterRepresentation μ χ)ξ(s,t)=χ(t) • ξ(s,t)` almost everywhere for the
Radon product measure. -/
theorem diagonalHaarCharacterRepresentation_ae_eq (χ : PontryaginDual G)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ((χ z.2 : Circle) : ℂ) • ξ z :=
  HaarL2.characterMultiplier_ae_eq (Measure.radonProd μ μ) (secondCoordinateCharacterMap χ) ξ

omit [μ.Regular] in
/-- **Inverse character action on the Radon square.** Let `G` be a Hausdorff locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complete
complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel topological product
`G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for `ξ∈L`, the
representation at `χ⁻¹` has almost-everywhere value `χ⁻¹(t) • ξ(s,t)`. -/
theorem diagonalHaarInverseCharacterRepresentation_ae_eq (χ : PontryaginDual G)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ⁻¹ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ((χ⁻¹ z.2 : Circle) : ℂ) • ξ z :=
  diagonalHaarCharacterRepresentation_ae_eq μ χ⁻¹ ξ

/-- **Generator set of diagonal translations and second-coordinate multipliers.** Let `G` be a
Hausdorff locally compact topological group with its Borel structure, `μ` a regular Haar
measure and `H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the
Borel topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
`diagonalHaarWeylGenerators μ=range(D)∪range(V)` in `B(L)`. -/
def diagonalHaarWeylGenerators :
    Set (Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  Set.range (fun g : G => (diagonalHaarLeftRegular (H := H) μ g :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ))) ∪
    Set.range (fun χ : PontryaginDual G => (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)))

/-- **Von Neumann algebra generated by diagonal Haar Weyl operators.** Let `G` be a Hausdorff
locally compact topological group with its Borel structure, `μ` a regular Haar measure and
`H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel
topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
`diagonalHaarWeylAlgebra μ` is the von Neumann algebra generated by `D_g` and `V_χ` on
`L`. -/
def diagonalHaarWeylAlgebra : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ)) :=
  generatedBy (diagonalHaarWeylGenerators (H := H) μ)

/-- **Diagonal translation belongs to its Weyl algebra.** Let `G` be a Hausdorff locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel topological
product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for every `g∈G`,
`D_g∈diagonalHaarWeylAlgebra μ`. -/
theorem diagonalHaarLeftRegular_mem_diagonalHaarWeylAlgebra (g : G) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈
        diagonalHaarWeylAlgebra (H := H) μ :=
  subset_generatedBy _ (Or.inl (Set.mem_range_self g))

/-- **Second-coordinate character belongs to the diagonal Weyl algebra.** Let `G` be a
Hausdorff locally compact topological group with its Borel structure, `μ` a regular Haar
measure and `H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the
Borel topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`.
for every `χ∈PontryaginDual G`, `V_χ∈diagonalHaarWeylAlgebra μ`. -/
theorem diagonalHaarCharacterRepresentation_mem_diagonalHaarWeylAlgebra (χ : PontryaginDual G) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈
        diagonalHaarWeylAlgebra (H := H) μ :=
  subset_generatedBy _ (Or.inr (Set.mem_range_self χ))

/-- **Diagonal Weyl containment tested by its two unitary families.** Let `G` be a Hausdorff
locally compact topological group with its Borel structure, `μ` a regular Haar measure and
`H` a complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel
topological product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. for a
concrete von Neumann algebra `N⊆B(L)`, `diagonalHaarWeylAlgebra μ≤N` exactly when `D_g∈N`
for all `g` and `V_χ∈N` for all `χ`. -/
theorem diagonalHaarWeylAlgebra_le_iff
    (N : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :
    diagonalHaarWeylAlgebra (H := H) μ ≤ N ↔
      (∀ g : G, (diagonalHaarLeftRegular (H := H) μ g :
        Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈ N) ∧
      ∀ χ : PontryaginDual G, (diagonalHaarCharacterRepresentation (H := H) μ χ :
        Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈ N := by
  rw [diagonalHaarWeylAlgebra, generatedBy_le_iff]
  simp only [diagonalHaarWeylGenerators, Set.union_subset_iff, Set.range_subset_iff]
  exact Iff.rfl

/-- **WOT closedness of the diagonal Haar Weyl algebra.** Let `G` be a Hausdorff locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complete complex Hilbert space. Put `L=Lp H 2 (radonProd μ μ)` on the Borel topological
product `G×G`, `D_g ξ(s,t)=ξ(g⁻¹s,g⁻¹t)` and `V_χ ξ(s,t)=χ(t) • ξ(s,t)`. the operator
carrier of `diagonalHaarWeylAlgebra μ` is closed in the weak operator topology on `B(L)`. -/
theorem diagonalHaarWeylAlgebra_isClosedWOT :
    IsClosed {T : Lp H 2 (Measure.radonProd μ μ) →WOT[ℂ] Lp H 2 (Measure.radonProd μ μ) |
      T.toCLM ∈ diagonalHaarWeylAlgebra (H := H) μ} :=
  generatedBy_isClosedWOT (diagonalHaarWeylGenerators (H := H) μ)

end

end VonNeumannAlgebra
