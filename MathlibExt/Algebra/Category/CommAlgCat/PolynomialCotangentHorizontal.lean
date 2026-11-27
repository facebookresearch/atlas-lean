/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolutionOverPower
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentReplacement
public import MathlibExt.AlgebraicTopology.SimplicialObject.SliceTrivialFibration
public import Mathlib.CategoryTheory.Whiskering

/-!
# Horizontal comparison for polynomial cotangent replacements

The polynomial comonad on the category of commutative `k`-algebras over `A` factors
through the free-forgetful adjunction on sets over the underlying set of `A`. This
factorization identifies each outer row of the double polynomial cotangent diagram
with a functor applied to the underlying simplicial augmentation.

If that underlying augmentation is a trivial fibration, the outer-row comparisons are
quasi-isomorphisms. The diagonal comparison from the polynomial replacement to the
standard cotangent model is consequently a quasi-isomorphism. The ground-ring and
algebra-carrier universes are independent.

For cotriple resolutions and the cotangent comparison, see the Stacks Project,
§§92.4.1–92.4.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The functor from `k`-algebras over `A` to sets over the underlying set of `A`, induced
by forgetting the algebra structure.
-/
abbrev polynomialSliceForget : Over A ⥤ Over (A : Type (max u v)) :=
  Over.post (forget (CommAlgCat.{max u v} k))

/--
The free polynomial algebra on a set mapping to `A`, augmented to `A` by the
polynomial counit, as a functor from sets over `A` to `k`-algebras over `A`.
-/
def polynomialSliceFree : Over (A : Type (max u v)) ⥤ Over A :=
  Over.post (free.{u, v} k) ⋙ Over.map ((freeForgetAdjunction.{u, v} k).counit.app A)

/--
The adjunction between the free polynomial functor on sets over `A` and the
forgetful functor on `k`-algebras over `A`.
-/
def polynomialSliceAdjunction : polynomialSliceFree k A ⊣ polynomialSliceForget k A :=
  Over.postAdjunctionRight (freeForgetAdjunction.{u, v} k)

/--
The natural isomorphism identifying the polynomial comonad on the algebra slice
with forgetting to the set slice and then applying its free polynomial functor.
-/
def polynomialOverComonadFactorIso :
    (polynomialOverComonad k A).toFunctor ≅
      polynomialSliceForget k A ⋙ polynomialSliceFree k A :=
  NatIso.ofComponents
    (fun P => Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫
        ((polynomialComonad.{u, v} k).map P.hom ≫
          (polynomialComonad.{u, v} k).ε.app A) =
        (polynomialComonad.{u, v} k).ε.app P.left ≫ P.hom
      rw [Category.id_comp]
      exact (polynomialComonad.{u, v} k).ε.naturality P.hom))
    (by
      intro P Q f
      apply Over.OverMorphism.ext
      change (polynomialComonad.{u, v} k).map f.left ≫ 𝟙 _ =
        𝟙 _ ≫ (polynomialComonad.{u, v} k).map f.left
      rw [Category.comp_id, Category.id_comp])

/--
The natural isomorphism between applying the cotangent functor to polynomial-resolution
degree `p` and evaluating the polynomial cotangent simplicial diagram in degree `p`.
-/
def polynomialCotangentDegreeIso (p : ℕ) :
    polynomialResolutionDegreeOverFunctor k A p ⋙ cotangentFunctor.{u, v} k A ≅
      polynomialCotangentSimplicialFunctor.{u, v} k A ⋙
        (evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj (op ⦋p⦌) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q f
    change (cotangentFunctor.{u, v} k A).map _ ≫ 𝟙 _ =
      𝟙 _ ≫ (cotangentFunctor.{u, v} k A).map _
    rw [Category.comp_id, Category.id_comp]
    congr 1
    all_goals apply Over.OverMorphism.ext
    all_goals rfl)

/--
The functor on sets over `A` obtained by applying the free polynomial slice functor,
then `p` powers of the polynomial slice comonad, and then the cotangent functor.
-/
def polynomialCotangentOuterRowFunctor (p : ℕ) :
    Over (A : Type (max u v)) ⥤ ModuleCat.{max u v} A :=
  polynomialSliceFree k A ⋙
    Comonad.comonadPow (polynomialOverComonad k A) p ⋙ cotangentFunctor.{u, v} k A

/--
The natural isomorphism between the outer-row functor after forgetting an algebra
slice object and the degree-`p` evaluation of its polynomial cotangent simplicial diagram.
-/
def polynomialCotangentOuterRowIso (p : ℕ) :
    polynomialSliceForget k A ⋙ polynomialCotangentOuterRowFunctor.{u, v} k A p ≅
      polynomialCotangentSimplicialFunctor.{u, v} k A ⋙
        (evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj (op ⦋p⦌) :=
  (Functor.isoWhiskerRight (polynomialOverComonadFactorIso.{u, v} k A)
      (Comonad.comonadPow (polynomialOverComonad k A) p ⋙ cotangentFunctor.{u, v} k A)).symm ≪≫
    Functor.isoWhiskerRight (polynomialOverPowerNatIso.{u, v} k A p) (cotangentFunctor.{u, v} k A) ≪≫
    polynomialCotangentDegreeIso.{u, v} k A p

/--
The condition that the underlying simplicial-set augmentation of `Q → const A`,
viewed as the point map of a diagram in the set slice over `A`, is a trivial fibration.
-/
def polynomialCotangentResolutionCondition
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) : Prop :=
  trivialFibrations SSet.{max u v}
    (SimplicialObject.slicePoint
      (Over.lift Q.left Q.hom ⋙ polynomialSliceForget k A))

/--
If `Q` satisfies the underlying simplicial resolution condition, the horizontal
replacement map induces a quasi-isomorphism of alternating-face complexes on every
outer row `p`.
-/
theorem polynomialCotangentReplacementHorizontal_outerRow_quasiIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hQ : polynomialCotangentResolutionCondition k A Q) (p : ℕ) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).map
      (Functor.whiskerRight (polynomialCotangentReplacementHorizontal k A Q)
        ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj (op ⦋p⦌)))) := by
  let C := ModuleCat.{max u v} A
  let R := polynomialCotangentOuterRowFunctor.{u, v} k A p
  let X := Over.lift Q.left Q.hom
  let U := polynomialSliceForget k A
  let K := alternatingFaceMapComplex C
  let φ := Functor.whiskerRight (SimplicialObject.slicePointOver (X ⋙ U)) R
  let ψ := Functor.whiskerRight (polynomialCotangentReplacementHorizontal k A Q)
    ((evaluation SimplexCategoryᵒᵖ C).obj (op ⦋p⦌))
  let eX : (X ⋙ U) ⋙ R ≅
      polynomialCotangentReplacement k A Q ⋙
        (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋p⦌) :=
    Functor.isoWhiskerLeft X (polynomialCotangentOuterRowIso.{u, v} k A p)
  let eY :
      (((SimplicialObject.const (Over (A : Type (max u v)))).obj
        (Over.mk (𝟙 (A : Type (max u v))))) ⋙ R) ≅
      ((SimplicialObject.const C).obj
        (((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A))).obj
          (op ⦋p⦌))) :=
    NatIso.ofComponents
      (fun _ => (polynomialCotangentOuterRowIso.{u, v} k A p).app (Over.mk (𝟙 A)))
      (by
        intro q q' f
        change R.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
        rw [R.map_id, Category.id_comp, Category.comp_id])
  have hSquare : eX.hom ≫ ψ = φ ≫ eY.hom := by
    apply NatTrans.ext
    funext q
    let a : (Over.lift Q.left Q.hom).obj q ⟶ Over.mk (𝟙 A) :=
      Over.homMk (Q.hom.app q) (by
        change Q.hom.app q ≫ (𝟙 A) = Q.hom.app q
        exact Category.comp_id _)
    exact ((polynomialCotangentOuterRowIso.{u, v} k A p).hom.naturality a).symm
  letI : QuasiIso (K.map φ) :=
    SimplicialObject.quasiIso_alternatingSlicePoint (X ⋙ U) R hQ
  have hComp : QuasiIso (K.map eX.hom ≫ K.map ψ) := by
    rw [← K.map_comp, hSquare, K.map_comp]
    infer_instance
  letI := hComp
  exact quasiIso_of_comp_left (K.map eX.hom) (K.map ψ)

/--
If the underlying augmentation of `Q` is a trivial fibration, the diagonal horizontal
map from its polynomial cotangent replacement to the standard cotangent simplicial
model induces a quasi-isomorphism of alternating-face complexes.
-/
theorem polynomialCotangentReplacementToStandard_quasiIso
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hQ : polynomialCotangentResolutionCondition k A Q) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).map
      (polynomialCotangentReplacementToStandard k A Q)) := by
  let C := ModuleCat.{max u v} A
  let φ := polynomialCotangentReplacementHorizontal k A Q
  letI : QuasiIso ((alternatingFaceMapComplex C).map
      ((SimplicialObject.diagonalFunctor C).map φ)) :=
    SimplicialObject.quasiIso_diagonalMap_of_outerRowMaps φ
      (polynomialCotangentReplacementHorizontal_outerRow_quasiIso k A Q hQ)
  unfold polynomialCotangentReplacementToStandard
  rw [Functor.map_comp]
  infer_instance

end CommAlgCat

end
