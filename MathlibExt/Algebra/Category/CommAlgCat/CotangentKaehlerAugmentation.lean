/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentAugmentation
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The actual cotangent augmentation to ordinary Kähler differentials

The terminal object over `A` linearizes to `A ⊗[A] Ω[A/k]`. Its native
scalar-extension unitor identifies this actual point with `Ω[A/k]`. Compose
the actual polynomial cotangent augmentation with that unitor, then use the
native Moore inclusion to obtain the genuine chain map to ordinary differentials.

Every component sends `a ⊗ dp` to `a · d(ε(p))`. No degree-zero identification
or desired quasi-isomorphism is supplied by a caller.

Reference: Stacks Project 92.4.5; Loday 3.5.3–3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The terminal linearization is identified by the actual native unitor. -/
def cotangentTerminalIso :
    cotangent.{u, v} k A (Over.mk (𝟙 A)) ≅ ModuleCat.of A (KaehlerDifferential k A) :=
  by
    let Ω : ModuleCat.{max u v} A := ModuleCat.of A (KaehlerDifferential k A)
    let e := (ModuleCat.extendScalarsId A).app Ω
    dsimp only [cotangent, cotangentAlgebra, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.obj']
    exact e

@[simp]
theorem cotangentTerminalIso_unit (a : A) :
    (cotangentTerminalIso.{u, v} k A).hom.hom
      (cotangentTensor.{u, v} k A (Over.mk (𝟙 A)) 1 a) = KaehlerDifferential.D k A a :=
  ModuleCat.extendScalarsId_hom_app_one_tmul _ _

/-- The unitor preserves the original coefficient on the differential tensor. -/
theorem cotangentTerminalIso_tensor (a b : A) :
    (cotangentTerminalIso.{u, v} k A).hom.hom
      (cotangentTensor.{u, v} k A (Over.mk (𝟙 A)) a b) = a • KaehlerDifferential.D k A b := by
  have h : cotangentTensor.{u, v} k A (Over.mk (𝟙 A)) a b =
      a • cotangentTensor.{u, v} k A (Over.mk (𝟙 A)) 1 b := by
    change a ⊗ₜ[A] KaehlerDifferential.D k A b =
      a • ((1 : A) ⊗ₜ[A] KaehlerDifferential.D k A b)
    have hm : a • (1 : A) = a := by rw [smul_eq_mul, mul_one]
    exact (congrArg (fun x : A => x ⊗ₜ[A] KaehlerDifferential.D k A b) hm).symm.trans
      (TensorProduct.smul_tmul' a (1 : A) (KaehlerDifferential.D k A b)).symm
  rw [h, map_smul, cotangentTerminalIso_unit]

/-- The actual simplicial cotangent augmentation to ordinary differentials. -/
def cotangentKaehlerAugmentation :
    (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)) ⟶
      (SimplicialObject.const (ModuleCat.{max u v} A)).obj
        (ModuleCat.of A (KaehlerDifferential k A)) :=
  (polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom ≫
    (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentTerminalIso.{u, v} k A).hom

/-- Its point and every simplicial component are the actual source constructions. -/
def cotangentKaehlerAugmented : SimplicialObject.Augmented (ModuleCat.{max u v} A) where
  left := (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))
  right := ModuleCat.of A (KaehlerDifferential k A)
  hom := cotangentKaehlerAugmentation.{u, v} k A

/-- The literal normalized cotangent chain map to ordinary differentials. -/
def cotangentKaehlerNormalizedAugmentation :
    cotangentComplex k A ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} A)).obj
        (ModuleCat.of A (KaehlerDifferential k A)) :=
  inclusionOfMooreComplexMap
      ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))) ≫
    AlternatingFaceMapComplex.ε.app (cotangentKaehlerAugmented k A)

/-- Every actual simplicial differential tensor follows the original evaluation map. -/
theorem cotangentKaehlerAugmentation_tensor (n : ℕ) (a : A)
    (p : (polynomialResolution.{u, v} k A).left.obj (op ⦋n⦌)) :
    ((cotangentKaehlerAugmentation.{u, v} k A).app (op ⦋n⦌)).hom
        (cotangentTensor.{u, v} k A (Over.mk
          (((polynomialResolution.{u, v} k A).hom.app (op ⦋n⦌)) ≫ 𝟙 A)) a p) =
      a • KaehlerDifferential.D k A
        (((polynomialResolution.{u, v} k A).hom.app (op ⦋n⦌)).hom p) := by
  change (cotangentTerminalIso.{u, v} k A).hom.hom
      ((polynomialCotangentAugmentationAt.{u, v} k A (Over.mk (𝟙 A)) n).hom _) = _
  have hP := polynomialCotangentAugmentationAt_tensor.{u, v} k A (Over.mk (𝟙 A)) n a p
  have hT := cotangentTerminalIso_tensor.{u, v} k A a
    (((polynomialResolution.{u, v} k A).hom.app (op ⦋n⦌)).hom p)
  exact (congrArg (cotangentTerminalIso.{u, v} k A).hom.hom hP).trans hT

end CommAlgCat

end
