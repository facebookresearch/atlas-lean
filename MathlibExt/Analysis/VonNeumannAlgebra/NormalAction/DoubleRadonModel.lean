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

public import MathlibExt.Analysis.VonNeumannAlgebra.IsometryConjugation
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.DoubleCrossedProductTensor
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.HFirst

/-!
# Actual explicit-dual-Haar double operators on the Borel Radon model

The original double tensor construction and both actual Haar inputs are
retained. Its verified H-first coordinate unitary conjugates the original
normal coefficient maps and group unitaries onto the full H-valued Borel
Radon product L2 space. Those original operator images generate an actual
weakly closed concrete algebra on that same carrier.

No normalized dual measure, Fourier unitary, source normal range or type I
factor is supplied or chosen. Fourier transport and duality proofs remain
whole-open; the operators here are the original pre-Fourier source images.
H may be zero, with original independent group/H universes preserved.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory UniformSpace
open scoped TensorProduct CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
variable (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]

/-- The original Borel measurable structure of the actual group/dual topological product. -/
local instance instDoubleRadonProductMeasurableSpace :
    MeasurableSpace (G × PontryaginDual G) := borel (G × PontryaginDual G)
local instance instDoubleRadonProductBorelSpace : BorelSpace (G × PontryaginDual G) := ⟨rfl⟩

/-- The actual double-tensor algebra maps normally through its original H-first coordinate unitary. -/
def doubleRadonSpatialNormalHom (α : NormalAction G M) :
    NormalStarAlgHom (doubleCrossedProductTensor μ ν α)
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν))) :=
  isometryConjugationNormalHom (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν)
    (doubleCrossedProductTensor μ ν α)

/-- The spatial normal map keeps the exact original conjugated bounded operator. -/
theorem doubleRadonSpatialNormalHom_coe (α : NormalAction G M)
    (x : doubleCrossedProductTensor μ ν α) :
    (doubleRadonSpatialNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (x : Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
          Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν))) := rfl

/-- The original first crossed product embeds normally into the actual product-L2 operator algebra. -/
def doubleRadonFirstCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom (crossedProductTensor μ α)
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν))) :=
  (doubleRadonSpatialNormalHom μ ν α).comp
    (crossedProductTensorCoefficientNormalHom ν (tensorCharacterNormalAction μ α))

/-- Every original first-algebra element retains its literal H-first conjugated coefficient operator. -/
theorem doubleRadonFirstCoefficientNormalHom_coe (α : NormalAction G M)
    (x : crossedProductTensor μ α) :
    (doubleRadonFirstCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α) x) := by
  let z : doubleCrossedProductTensor μ ν α :=
    crossedProductTensorCoefficientNormalHom ν (tensorCharacterNormalAction μ α) x
  have hx : (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) =
        regularCoefficientTensor ν (tensorCharacterNormalAction μ α) x :=
    crossedProductTensorCoefficientNormalHom_coe ν (tensorCharacterNormalAction μ α) x
  calc
    _ = (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) := rfl
    _ = (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
          Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) :=
      doubleRadonSpatialNormalHom_coe μ ν α z
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro ξ
      simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
      exact congrArg
        (fun η : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) =>
          HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν η)
        (congrArg
          (fun T : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
            Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) =>
              T ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ)) hx)

/-- The original first coefficient uses the actual inverse and forward H-first maps on every vector. -/
theorem doubleRadonFirstCoefficientNormalHom_apply (α : NormalAction G M)
    (x : crossedProductTensor μ α) (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    (doubleRadonFirstCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α) x
          ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ)) := by
  calc
    _ = ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α) x)) ξ :=
      congrArg
        (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ)
        (doubleRadonFirstCoefficientNormalHom_coe μ ν α x)
    _ = _ := rfl

/-- The two original canonical tensor coefficient maps form the actual double coefficient. -/
def doubleTensorCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (doubleCrossedProductTensor μ ν α) :=
  (crossedProductTensorCoefficientNormalHom ν (tensorCharacterNormalAction μ α)).comp
    (crossedProductTensorCoefficientNormalHom μ α)

/-- The original coefficient algebra maps normally to the full actual Borel product-L2 operators. -/
def doubleRadonCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν))) :=
  (doubleRadonSpatialNormalHom μ ν α).comp (doubleTensorCoefficientNormalHom μ ν α)

omit [T2Space G] in
/-- The nested double coefficient is the unchanged original second tensor coefficient operator. -/
theorem doubleTensorCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (doubleTensorCoefficientNormalHom μ ν α x :
      Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
        Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν))) =
      regularCoefficientTensor ν (tensorCharacterNormalAction μ α)
        (crossedProductTensorCoefficient μ α x) := rfl

omit [T2Space G] in
private theorem doubleTensorCoefficientNormalHom_apply_operator (α : NormalAction G M) (x : M)
    (η : Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν))) :
    (doubleTensorCoefficientNormalHom μ ν α x :
      Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
        Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν))) η =
      regularCoefficientTensor ν (tensorCharacterNormalAction μ α)
        (crossedProductTensorCoefficient μ α x) η :=
  congrArg
    (fun T : Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) => T η)
    (doubleTensorCoefficientNormalHom_coe μ ν α x)

private theorem doubleRadonCoefficientNormalHom_factorization (α : NormalAction G M) (x : M) :
    (doubleRadonCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (doubleRadonSpatialNormalHom μ ν α (doubleTensorCoefficientNormalHom μ ν α x) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) := rfl

/-- The actual normal product coefficient is literal H-first conjugation of the original tensor coefficient. -/
theorem doubleRadonCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (doubleRadonCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α)
          (crossedProductTensorCoefficient μ α x)) := by
  calc
    _ = (doubleRadonSpatialNormalHom μ ν α (doubleTensorCoefficientNormalHom μ ν α x) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) :=
      doubleRadonCoefficientNormalHom_factorization μ ν α x
    _ = (HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
        (doubleTensorCoefficientNormalHom μ ν α x :
          Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
            Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν))) :=
      doubleRadonSpatialNormalHom_coe μ ν α (doubleTensorCoefficientNormalHom μ ν α x)
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro ξ
      simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
      exact congrArg
        (fun η : Completion (Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) ⊗[ℂ] (Lp ℂ 2 ν)) =>
          HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν η)
        (doubleTensorCoefficientNormalHom_apply_operator μ ν α x
          ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ))

/-- The actual normal coefficient uses the original inverse and forward coordinate-model maps on vectors. -/
theorem doubleRadonCoefficientNormalHom_apply (α : NormalAction G M) (x : M)
    (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    (doubleRadonCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α)
          (crossedProductTensorCoefficient μ α x)
          ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ)) := by
  rw [doubleRadonCoefficientNormalHom_coe]
  exact LinearIsometryEquiv.conjStarAlgEquiv_apply_apply _ _ _

/-- The original first Haar unitary retains its actual normal double-coefficient operator image. -/
def doubleRadonFirstGroupUnitary (α : NormalAction G M) (g : G) :
    unitary (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν))) :=
  Unitary.map
    { toMonoidHom := (doubleRadonFirstCoefficientNormalHom μ ν α).toStarAlgHom.toMonoidHom
      map_star' := map_star (doubleRadonFirstCoefficientNormalHom μ ν α).toStarAlgHom }
    (crossedProductTensorGroupUnitary μ α g)

/-- The mapped first Haar unitary is the exact normal image of the original first source unitary. -/
@[simp]
theorem doubleRadonFirstGroupUnitary_coe (α : NormalAction G M) (g : G) :
    ((doubleRadonFirstGroupUnitary μ ν α g :
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (doubleRadonFirstCoefficientNormalHom μ ν α
        (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) :
          Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) := rfl

/-- The first mapped unitary acts through the original H-first coordinates and second coefficient. -/
theorem doubleRadonFirstGroupUnitary_apply (α : NormalAction G M) (g : G)
    (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    ((doubleRadonFirstGroupUnitary μ ν α g :
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
        (regularCoefficientTensor ν (tensorCharacterNormalAction μ α)
          (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α)
          ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ)) := by
  let E := HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
  let u : crossedProductTensor μ α := (crossedProductTensorGroupUnitary μ α g).val
  let z : doubleCrossedProductTensor μ ν α :=
    crossedProductTensorCoefficientNormalHom ν (tensorCharacterNormalAction μ α) u
  let A : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) :=
    regularCoefficientTensor ν (tensorCharacterNormalAction μ α) u
  have hz : (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) = A :=
    crossedProductTensorCoefficientNormalHom_coe ν (tensorCharacterNormalAction μ α) u
  have hm : (doubleRadonFirstCoefficientNormalHom μ ν α u :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) := rfl
  have hmap :
      ((doubleRadonFirstGroupUnitary μ ν α g :
        (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
          Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ :=
    (congrArg
      (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ)
      (doubleRadonFirstGroupUnitary_coe μ ν α g)).trans
        (congrArg
          (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ) hm)
  have hbase :
      (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      E ((z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
        Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) (E.symm ξ)) :=
    by
      calc
        _ = ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
            (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
              Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν))) ξ :=
          congrArg
            (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ)
            (doubleRadonSpatialNormalHom_coe μ ν α z)
        _ = _ := rfl
  exact hmap.trans (hbase.trans
    (congrArg
      (fun v : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) => E v)
      (congrArg
        (fun T : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
          Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) => T (E.symm ξ)) hz)))

/-- The original dual-group Haar unitary retains its actual spatial coordinate-model image. -/
def doubleRadonSecondGroupUnitary (α : NormalAction G M) (χ : PontryaginDual G) :
    unitary (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν))) :=
  Unitary.map
    { toMonoidHom := (doubleRadonSpatialNormalHom μ ν α).toStarAlgHom.toMonoidHom
      map_star' := map_star (doubleRadonSpatialNormalHom μ ν α).toStarAlgHom }
    (crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ)

/-- The mapped dual-Haar unitary is the exact spatial image of the original second source unitary. -/
@[simp]
theorem doubleRadonSecondGroupUnitary_coe (α : NormalAction G M) (χ : PontryaginDual G) :
    ((doubleRadonSecondGroupUnitary μ ν α χ :
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) =
      (doubleRadonSpatialNormalHom μ ν α
        ((crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ).val :
          doubleCrossedProductTensor μ ν α) :
            Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) := rfl

/-- The second mapped unitary retains the original Haar translation in the completed dual factor. -/
theorem doubleRadonSecondGroupUnitary_apply (α : NormalAction G M) (χ : PontryaginDual G)
    (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    ((doubleRadonSecondGroupUnitary μ ν α χ :
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
        ((StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor
          (PontryaginDual G) ν (Completion (H ⊗[ℂ] Lp ℂ 2 μ)) χ :
            Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
              Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν))
            ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).symm ξ)) := by
  let E := HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν
  let z : doubleCrossedProductTensor μ ν α :=
    (crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ).val
  let A : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) :=
    (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor
      (PontryaginDual G) ν (Completion (H ⊗[ℂ] Lp ℂ 2 μ)) χ :
        Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
          Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν))
  have hz : (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
      Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) = A :=
    crossedProductTensorGroupUnitary_coe ν (tensorCharacterNormalAction μ α) χ
  have hmap :
      ((doubleRadonSecondGroupUnitary μ ν α χ :
        (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
          Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ :=
    congrArg
      (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ)
      (doubleRadonSecondGroupUnitary_coe μ ν α χ)
  have hbase :
      (doubleRadonSpatialNormalHom μ ν α z :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ξ =
      E ((z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
        Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) (E.symm ξ)) :=
    by
      calc
        _ = ((HaarL2.radonProductHFirstTensorUnitary (H := H) μ ν).conjStarAlgEquiv
            (z : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
              Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν))) ξ :=
          congrArg
            (fun T : Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν) => T ξ)
            (doubleRadonSpatialNormalHom_coe μ ν α z)
        _ = _ := rfl
  exact hmap.trans (hbase.trans
    (congrArg
      (fun v : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) => E v)
      (congrArg
        (fun T : Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ]
          Completion (Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν) => T (E.symm ξ)) hz)))

/-- The full first-coefficient and second-group images are the actual transported two generator families. -/
def doubleRadonGenerators (α : NormalAction G M) :
    Set (Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) :=
  Set.range (fun x : crossedProductTensor μ α =>
    (doubleRadonFirstCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν))) ∪
    Set.range (fun χ : PontryaginDual G => (doubleRadonSecondGroupUnitary μ ν α χ :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)))

/-- The actual original operator images generate the Borel product-L2 double model. -/
def doubleRadonAlgebra (α : NormalAction G M) : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)) :=
  generatedBy (doubleRadonGenerators μ ν α)

/-- Every original first-product coefficient image belongs to this same actual generated model. -/
theorem doubleRadonFirstCoefficient_mem (α : NormalAction G M) (x : crossedProductTensor μ α) :
    (doubleRadonFirstCoefficientNormalHom μ ν α x :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ∈
        doubleRadonAlgebra μ ν α :=
  subset_generatedBy _ (Or.inl (Set.mem_range_self x))

/-- The mapped original first Haar unitary belongs directly to the actual generated Radon algebra. -/
theorem doubleRadonFirstGroup_mem (α : NormalAction G M) (g : G) :
    ((doubleRadonFirstGroupUnitary μ ν α g :
      (⊤ : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ ν)))) :
        Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ∈
      doubleRadonAlgebra μ ν α := by
  rw [doubleRadonFirstGroupUnitary_coe]
  exact doubleRadonFirstCoefficient_mem μ ν α
    (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α)

/-- Every actual second Haar unitary image belongs to the same generated product model. -/
theorem doubleRadonSecondGroup_mem (α : NormalAction G M) (χ : PontryaginDual G) :
    (doubleRadonSecondGroupUnitary μ ν α χ :
      Lp H 2 (Measure.radonProd μ ν) →L[ℂ] Lp H 2 (Measure.radonProd μ ν)) ∈ doubleRadonAlgebra μ ν α :=
  subset_generatedBy _ (Or.inr (Set.mem_range_self χ))

/-- The original generated coordinate-model carrier is closed in the actual weak operator topology. -/
theorem doubleRadonAlgebra_isClosedWOT (α : NormalAction G M) :
    IsClosed {T : Lp H 2 (Measure.radonProd μ ν) →WOT[ℂ] Lp H 2 (Measure.radonProd μ ν) |
      T.toCLM ∈ doubleRadonAlgebra μ ν α} :=
  generatedBy_isClosedWOT (doubleRadonGenerators μ ν α)

end

end VonNeumannAlgebra.NormalAction
