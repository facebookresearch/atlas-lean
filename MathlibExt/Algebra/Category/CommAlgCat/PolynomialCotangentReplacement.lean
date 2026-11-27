/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentAugmentation
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentationQuasiIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.DiagonalQuasiIso

/-!
# Bisimplicial polynomial cotangent replacements

For an augmented simplicial commutative `k`-algebra `Q → const A`, applying the
polynomial cotangent simplicial functor in each degree produces a bisimplicial
`A`-module. With polynomial comonad `T`, its bidegree `(q,p)` is
`A ⊗[T^(p+1) Q_q] Ω(T^(p+1) Q_q/k)`.

The vertical augmentation maps to the cotangent diagram of `Q`, constant in the inner
direction; the horizontal augmentation maps to the canonical cotangent diagram of `A`,
constant in the outer direction. Taking diagonals gives the two cotangent comparison
maps. Degreewise polynomial presentations of `Q` make the vertical comparison a
quasi-isomorphism of alternating-face complexes.

For the cotriple comparison construction, see the Stacks Project, §§92.4.1–92.4.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The bisimplicial `A`-module obtained by applying the polynomial cotangent simplicial
functor to each degree of the augmented algebra `Q → const A`.
-/
def polynomialCotangentReplacement
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject (SimplicialObject (ModuleCat.{max u v} A)) :=
  Over.lift Q.left Q.hom ⋙ polynomialCotangentSimplicialFunctor.{u, v} k A

/--
The map from the double polynomial replacement to the cotangent diagram of `Q`,
viewed as constant in the inner simplicial direction, given by degreewise polynomial
cotangent augmentations.
-/
def polynomialCotangentReplacementVertical
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentReplacement.{u, v} k A Q ⟶
      cotangentSimplicial.{u, v} k A Q ⋙ SimplicialObject.const (ModuleCat.{max u v} A) where
  app q := (polynomialCotangentAugmented.{u, v} k A ((Over.lift Q.left Q.hom).obj q)).hom
  naturality {q q'} f :=
    polynomialCotangentAugmentation_naturality.{u, v} k A ((Over.lift Q.left Q.hom).map f)

/--
The map from the double polynomial replacement to the canonical cotangent diagram
of `A`, viewed as constant in the outer direction, induced by the augmentation
`Q → const A`.
-/
def polynomialCotangentReplacementHorizontal
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentReplacement.{u, v} k A Q ⟶
      (SimplicialObject.const (SimplicialObject (ModuleCat.{max u v} A))).obj
        ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))) where
  app q := (polynomialCotangentSimplicialFunctor.{u, v} k A).map
    (show (Over.lift Q.left Q.hom).obj q ⟶ Over.mk (𝟙 A) from
      Over.homMk (Q.hom.app q) (Category.comp_id _))
  naturality {q q'} f := by
    let F := polynomialCotangentSimplicialFunctor.{u, v} k A
    let p : (Over.lift Q.left Q.hom).obj q ⟶ Over.mk (𝟙 A) :=
      Over.homMk (Q.hom.app q) (Category.comp_id _)
    let p' : (Over.lift Q.left Q.hom).obj q' ⟶ Over.mk (𝟙 A) :=
      Over.homMk (Q.hom.app q') (Category.comp_id _)
    have h : (Over.lift Q.left Q.hom).map f ≫ p' = p := by
      apply Over.OverMorphism.ext
      have hQ := Q.hom.naturality f
      change Q.left.map f ≫ Q.hom.app q' = Q.hom.app q ≫ 𝟙 A at hQ
      exact hQ.trans (Category.comp_id _)
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (Category.comp_id _).symm)

/--
The natural isomorphism from the diagonal of a simplicial diagram made constant in
the inner direction to the original diagram `X`.
-/
def cotangentDiagonalConstantInnerIso (X : SimplicialObject (ModuleCat.{max u v} A)) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
      (X ⋙ SimplicialObject.const (ModuleCat.{max u v} A)) ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q q' f
    change (𝟙 _ ≫ X.map f) ≫ 𝟙 _ = 𝟙 _ ≫ X.map f
    simp only [Category.id_comp, Category.comp_id])

/--
The map from the diagonal polynomial replacement to the cotangent simplicial diagram
of `Q`, obtained from the vertical augmentation and the inner-constant diagonal
identification.
-/
def polynomialCotangentReplacementToOriginal
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
      (polynomialCotangentReplacement.{u, v} k A Q) ⟶ cotangentSimplicial.{u, v} k A Q :=
  (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
      (polynomialCotangentReplacementVertical.{u, v} k A Q) ≫
    (cotangentDiagonalConstantInnerIso k A (cotangentSimplicial.{u, v} k A Q)).hom

/--
The map from the diagonal polynomial replacement to the canonical cotangent simplicial
diagram of `A`, obtained from the horizontal augmentation and the outer-constant
diagonal identification.
-/
def polynomialCotangentReplacementToStandard
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).obj
      (polynomialCotangentReplacement.{u, v} k A Q) ⟶
        (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)) :=
  (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
      (polynomialCotangentReplacementHorizontal.{u, v} k A Q) ≫
    (SimplicialObject.diagonalConstIso (ModuleCat.{max u v} A)
      ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)))).hom

/--
If every degree of `Q` admits a polynomial presentation, the diagonal vertical
cotangent comparison induces a quasi-isomorphism of alternating-face complexes.
-/
theorem polynomialCotangentReplacementToOriginal_quasiIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌))) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).map
      (polynomialCotangentReplacementToOriginal k A Q)) := by
  let C := ModuleCat.{max u v} A
  let t := SimplicialObject.transposeFunctor C
  let φ := polynomialCotangentReplacementVertical.{u, v} k A Q
  have hRows : ∀ q : ℕ,
      QuasiIso ((alternatingFaceMapComplex C).map
        (Functor.whiskerRight (t.map φ)
          ((evaluation SimplexCategoryᵒᵖ C).obj (op ⦋q⦌)))) := by
    intro q
    obtain ⟨σ, ⟨e⟩⟩ := hpoly q
    exact SimplicialObject.Augmented.quasiIso_alternating_augmentation
      (polynomialCotangentRightExtra k A ((Over.lift Q.left Q.hom).obj (op ⦋q⦌)) σ e)
  letI : QuasiIso ((alternatingFaceMapComplex C).map
      ((SimplicialObject.diagonalFunctor C).map (t.map φ))) :=
    SimplicialObject.quasiIso_diagonalMap_of_outerRowMaps (t.map φ) hRows
  have hNat := SimplicialObject.diagonalTransposeIso_naturality C φ
  have hComp : QuasiIso ((alternatingFaceMapComplex C).map
      (SimplicialObject.diagonalTransposeIso C (polynomialCotangentReplacement.{u, v} k A Q)).hom ≫
        (alternatingFaceMapComplex C).map ((SimplicialObject.diagonalFunctor C).map φ)) := by
    rw [← Functor.map_comp, ← hNat, Functor.map_comp]
    infer_instance
  letI := hComp
  letI : QuasiIso ((alternatingFaceMapComplex C).map
      ((SimplicialObject.diagonalFunctor C).map φ)) :=
    quasiIso_of_comp_left
      ((alternatingFaceMapComplex C).map
        (SimplicialObject.diagonalTransposeIso C (polynomialCotangentReplacement.{u, v} k A Q)).hom)
      ((alternatingFaceMapComplex C).map ((SimplicialObject.diagonalFunctor C).map φ))
  unfold polynomialCotangentReplacementToOriginal
  rw [Functor.map_comp]
  infer_instance

end CommAlgCat

end
