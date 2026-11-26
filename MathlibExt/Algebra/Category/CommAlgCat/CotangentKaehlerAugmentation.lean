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
# Cotangent augmentation to Kähler differentials

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. Linearization of the
terminal algebra over `A` is `A ⊗_A Ω_{A/k}`, identified with `Ω_{A/k}` by the
scalar-extension unitor. The polynomial cotangent simplicial model augments to the constant
simplicial module of ordinary differentials.

In degree `n`, the augmentation sends `a ⊗ d p` to `a·d(ε_n(p))`, where `ε_n` is the
polynomial-resolution augmentation to `A`. Moore normalization gives a chain map to `Ω_{A/k}`
concentrated in degree zero.

## References

* Stacks Project, 92.4.5.
* J.-L. Loday, *Cyclic Homology*, 3.5.3–3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The isomorphism
`cotangentTerminalIso k A : cotangent k A (Over.mk (𝟙 A)) ≅ ModuleCat.of A
(KaehlerDifferential k A)` is the scalar-extension unitor `A ⊗_A Ω_{A/k} ≅ Ω_{A/k}`. -/
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

/-- For a commutative ring `k`, a `k`-algebra `A`, and `a,b∈A`, the terminal cotangent unitor
sends `cotangentTensor k A (Over.mk (𝟙 A)) a b` to `a • KaehlerDifferential.D k A b`. Thus `a
⊗ d b` maps to `a·d b`. -/
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

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The morphism
`cotangentKaehlerAugmentation k A` runs from the polynomial cotangent simplicial module at
`Over.mk (𝟙 A)` to the constant simplicial `A`-module `Ω_{A/k}`. It composes the polynomial
cotangent augmentation with the terminal cotangent unitor. -/
def cotangentKaehlerAugmentation :
    (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)) ⟶
      (SimplicialObject.const (ModuleCat.{max u v} A)).obj
        (ModuleCat.of A (KaehlerDifferential k A)) :=
  (polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom ≫
    (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentTerminalIso.{u, v} k A).hom

/-- Let `k` be a commutative ring and `A` a `k`-algebra. The augmented simplicial `A`-module
`cotangentKaehlerAugmented k A` has left object the polynomial cotangent simplicial model at
`A→A`, augmentation point `Ω_{A/k}`, and augmentation morphism `cotangentKaehlerAugmentation k
A`. -/
def cotangentKaehlerAugmented : SimplicialObject.Augmented (ModuleCat.{max u v} A) where
  left := (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))
  right := ModuleCat.of A (KaehlerDifferential k A)
  hom := cotangentKaehlerAugmentation.{u, v} k A

/-- For a commutative ring `k : Type u` and `A : CommAlgCat.{max u v} k`,
`cotangentKaehlerNormalizedAugmentation k A` is a chain map from `cotangentComplex k A` to
`Ω_{A/k}` concentrated in degree zero. It is the Moore-complex inclusion followed by the
alternating-face augmentation of `cotangentKaehlerAugmented k A`. -/
def cotangentKaehlerNormalizedAugmentation :
    cotangentComplex k A ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} A)).obj
        (ModuleCat.of A (KaehlerDifferential k A)) :=
  inclusionOfMooreComplexMap
      ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))) ≫
    AlternatingFaceMapComplex.ε.app (cotangentKaehlerAugmented k A)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `n : ℕ`, `a∈A`, and `p∈P_n` in its
polynomial resolution. Writing `ε_n:P_n→A` for the resolution augmentation, the degree-`n`
cotangent augmentation sends `a ⊗ d p` to `a • KaehlerDifferential.D k A (ε_n(p))` in
`Ω_{A/k}`. -/
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
