/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalHigherCotangentComparison
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentHomology
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZeroCoefficients
public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient.Normalization

/-!
# Higher André–Quillen homology with arbitrary coefficients

Let `k` be a commutative ring, `A` a commutative `k`-algebra, and `M` an `A`-module in
an independent universe. For each weight `q`, form the degreewise higher forms on the
canonical polynomial resolution of `A`, normalize, and tensor with `M` as first factor.
The homology in chain degree `n` defines the weight-`q` higher André–Quillen module.

The coefficient tensor complex is naturally isomorphic to normalization of the
degreewise coefficient tensor diagram. Weight one agrees with ordinary André–Quillen
homology. In weight zero, degree-zero homology is naturally a universe lift of `M` and
linearly equivalent to its original carrier; every positive homology module is zero.
The exterior powers use alternating multilinearity, including in characteristic two.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The coefficient-complex functor `M ↦ M ⊗[A] C_q`, where `C_q` is the normalized
canonical weight-`q` higher-form complex and `M` is the first tensor factor.
-/
abbrev higherCotangentCoefficientComplexFunctor (q : ℕ) :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ :=
  ChainComplex.TensorCoefficient.functor A (CanonicalHigherCotangentComparison.complex k A q)

/--
The functor taking homology in chain degree `n` of the canonical weight-`q` coefficient
complex, with coefficient maps induced on the first tensor factor.
-/
def higherAndreQuillenHomologyFunctor (q n : ℕ) :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  higherCotangentCoefficientComplexFunctor k A q ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n

/--
The weight-`q`, degree-`n` homology of the canonical higher-form coefficient complex
with coefficients in the `A`-module `M`.
-/
abbrev higherAndreQuillenHomology (M : ModuleCat.{t} A) (q n : ℕ) :=
  (higherAndreQuillenHomologyFunctor k A q n).obj M

/--
The map on weight-`q`, degree-`n` higher André–Quillen homology induced by an
`A`-linear coefficient map `f : M ⟶ N`.
-/
abbrev higherAndreQuillenHomologyMap {M N : ModuleCat.{t} A}
    (f : M ⟶ N) (q n : ℕ) :
    higherAndreQuillenHomology k A M q n ⟶ higherAndreQuillenHomology k A N q n :=
  (higherAndreQuillenHomologyFunctor k A q n).map f

/--
The functor taking `M` to the normalization of the degreewise coefficient diagram
`M ⊗[A] (A ⊗[P] exteriorPower_P^q Ω(P/k))` on the canonical polynomial resolution
in positive weight `q`, using `M ⊗[A] (A ⊗[P] P)` in weight zero.
-/
abbrev higherCotangentCoefficientDiagramFunctor (q : ℕ) :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ :=
  ChainComplex.TensorCoefficient.normalizedDiagramFunctor.{max u v, max u v, t} A
    (CotangentPushout.higherSimplicial.{u, v, 0} k A q (CanonicalPolynomialResolutionComparison.canonical k A))

/--
The natural isomorphism between tensoring the canonical normalized weight-`q`
higher-form complex with `M` as first factor and normalizing the degreewise coefficient
tensor diagram.
-/
def higherCotangentCoefficientNormalizationNatIso (q : ℕ) :
    higherCotangentCoefficientComplexFunctor.{u, v, t} k A q ≅
      higherCotangentCoefficientDiagramFunctor k A q :=
  ChainComplex.TensorCoefficient.normalizationNatIso.{max u v, max u v, t} A
    (CotangentPushout.higherSimplicial.{u, v, 0} k A q (CanonicalPolynomialResolutionComparison.canonical k A))

/--
The natural isomorphism from the weight-one higher-form coefficient complex to the
ordinary cotangent coefficient complex.
-/
def higherCotangentCoefficientOneNatIso :
    higherCotangentCoefficientComplexFunctor.{u, v, t} k A 1 ≅
      cotangentCoefficientComplexFunctor k A :=
  ChainComplex.TensorCoefficient.mapIso A (CanonicalHigherCotangentComparison.oneIso k A)

/--
The natural isomorphism from weight-one higher André–Quillen homology to ordinary
André–Quillen homology in chain degree `n`.
-/
def higherAndreQuillenHomologyOneNatIso (n : ℕ) :
    higherAndreQuillenHomologyFunctor.{u, v, t} k A 1 n ≅
      andreQuillenHomologyFunctor k A n :=
  isoWhiskerRight (higherCotangentCoefficientOneNatIso k A)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n)

/--
The natural isomorphism identifying normalization of the weight-zero coefficient-form
diagram with the normalized regular coefficient tensor diagram on the canonical
polynomial resolution.
-/
def higherCotangentCoefficientZeroDiagramNatIso :
    higherCotangentCoefficientDiagramFunctor.{u, v, t} k A 0 ≅
      cotangentWeightZeroTensorComplexFunctor k A
        (CanonicalPolynomialResolutionComparison.canonical k A) :=
  NatIso.ofComponents
    (fun M => (normalizedMooreComplex (ModuleCat.{max u v t} A)).mapIso
      (isoWhiskerRight
        (CotangentPushout.higherSimplicialZeroIso.{u, v, 0} k A
          (CanonicalPolynomialResolutionComparison.canonical k A))
        ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M)))
    (by
      intro M N f
      let X : SimplicialObject (ModuleCat.{max u v} A) :=
        CotangentPushout.higherSimplicial.{u, v, 0} k A 0
          (CanonicalPolynomialResolutionComparison.canonical k A)
      let Z : SimplicialObject (ModuleCat.{max u v} A) := cotangentWeightZeroOnResolution k A
        (CanonicalPolynomialResolutionComparison.canonical k A)
      let e : X ≅ Z := CotangentPushout.higherSimplicialZeroIso.{u, v, 0} k A
        (CanonicalPolynomialResolutionComparison.canonical k A)
      let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v t} A :=
        (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
      let G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v t} A :=
        (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj N
      let α : F ⟶ G := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map f
      let Nm := normalizedMooreComplex (ModuleCat.{max u v t} A)
      have h : Functor.whiskerLeft X α ≫ Functor.whiskerRight e.hom G =
          Functor.whiskerRight e.hom F ≫ Functor.whiskerLeft Z α := by
        apply NatTrans.ext
        funext i
        exact (α.naturality (e.hom.app i)).symm
      have hN : Nm.map (Functor.whiskerLeft X α) ≫ Nm.map (Functor.whiskerRight e.hom G) =
          Nm.map (Functor.whiskerRight e.hom F) ≫ Nm.map (Functor.whiskerLeft Z α) :=
        (Nm.map_comp _ _).symm.trans ((congrArg Nm.map h).trans (Nm.map_comp _ _))
      exact hN)

/--
The natural isomorphism from weight-zero, degree-zero higher André–Quillen homology
to the canonical universe lift of the coefficient module.
-/
def higherAndreQuillenHomologyZeroNatIso :
    higherAndreQuillenHomologyFunctor.{u, v, t} k A 0 0 ≅
      cotangentWeightZeroCoefficientLift k A :=
  isoWhiskerRight
      (higherCotangentCoefficientNormalizationNatIso k A 0 ≪≫
        higherCotangentCoefficientZeroDiagramNatIso k A)
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) 0) ≪≫
    cotangentWeightZeroTensorHomologyZeroNatIso k A
      (CanonicalPolynomialResolutionComparison.canonical k A)

/--
The `A`-linear equivalence from weight-zero, degree-zero higher André–Quillen homology
with coefficients in `M` to the original carrier of `M`.
-/
def higherAndreQuillenHomologyZeroLinearEquiv (M : ModuleCat.{t} A) :
    higherAndreQuillenHomology k A M 0 0 ≃ₗ[A] M :=
  ((higherAndreQuillenHomologyZeroNatIso k A).app M).toLinearEquiv.trans ULift.moduleEquiv

/--
Weight-zero higher André–Quillen homology with coefficients in any `M` is zero in
all positive chain degrees `n + 1`.
-/
theorem higherAndreQuillenHomology_zero_isZero_succ (M : ModuleCat.{t} A) (n : ℕ) :
    IsZero (higherAndreQuillenHomology k A M 0 (n + 1)) := by
  let e : higherAndreQuillenHomologyFunctor.{u, v, t} k A 0 (n + 1) ≅
      cotangentWeightZeroTensorHomologyFunctor.{u, v, t} k A
        (CanonicalPolynomialResolutionComparison.canonical k A) (n + 1) :=
    isoWhiskerRight
      (higherCotangentCoefficientNormalizationNatIso k A 0 ≪≫
        higherCotangentCoefficientZeroDiagramNatIso k A)
      (HomologicalComplex.homologyFunctor
        (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) (n + 1))
  exact (cotangentWeightZeroTensorHomology_isZero_succ k A
    (CanonicalPolynomialResolutionComparison.canonical k A) M n).of_iso (e.app M)

end CommAlgCat

end
