/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso
public import
  MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.HomotopyEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialObject.Diagonal

/-!
# Outer-row quasi-isomorphisms on bisimplicial diagonals

In an abelian category with countable coproducts, suppose a map of bisimplicial
objects induces a quasi-isomorphism on the outer alternating-face complex at every
fixed inner degree. Its diagonal alternating-face map is a quasi-isomorphism.

Transposition identifies those outer rows with inner rows of the transposed object.
The signed first-quadrant total comparison and Alexander–Whitney naturality give the
transposed diagonal result, which is transported by the diagonal-transposition
isomorphism. Object and morphism universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

/--
For a bisimplicial map in an abelian category with countable coproducts,
quasi-isomorphisms of the outer alternating-face maps at every fixed inner degree
imply a quasi-isomorphism of the diagonal alternating-face map.
-/
theorem quasiIso_diagonalMap_of_outerRowMaps
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {B B' : SimplicialObject (SimplicialObject C)} (φ : B ⟶ B')
    (hRows : ∀ q : ℕ,
      QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map
        (Functor.whiskerRight φ
          ((evaluation SimplexCategoryᵒᵖ C).obj (op ⦋q⦌))))) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map
      ((diagonalFunctor C).map φ)) := by
  let K := AlgebraicTopology.alternatingFaceMapComplex C
  let φt := (transposeFunctor C).map φ
  let Bt := (transposeFunctor C).obj B
  let Bt' := (transposeFunctor C).obj B'
  let ψ := (AlgebraicTopology.bisimplicialAlternatingBicomplexFunctor C).map φt
  -- The inner complex at q is the original outer row evaluated at inner degree q.
  have hRowsT : ∀ q : ℕ, QuasiIso (ψ.f q) := by
    intro q
    exact hRows q
  let _ : QuasiIso
      ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor C).map φt) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant ψ hRowsT
  let _ : QuasiIso
      (AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap Bt) :=
    (AlgebraicTopology.BisimplicialNormalization.homotopyEquiv Bt).quasiIso_hom
  let _ : QuasiIso
      (AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap Bt') :=
    (AlgebraicTopology.BisimplicialNormalization.homotopyEquiv Bt').quasiIso_hom
  have hDiagonalT : QuasiIso (K.map ((diagonalFunctor C).map φt)) := by
    have hComposite : QuasiIso
        (K.map ((diagonalFunctor C).map φt) ≫
          AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap Bt') := by
      rw [AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap_naturality φt]
      infer_instance
    let _ : QuasiIso
        (K.map ((diagonalFunctor C).map φt) ≫
          AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap Bt') := hComposite
    exact quasiIso_of_comp_right
      (K.map ((diagonalFunctor C).map φt))
      (AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap Bt')
  let _ : QuasiIso (K.map ((diagonalFunctor C).map φt)) := hDiagonalT
  let _ : QuasiIso (K.map (diagonalTransposeIso C B).hom) := inferInstance
  let _ : QuasiIso (K.map (diagonalTransposeIso C B').hom) := inferInstance
  have hSquare :
      K.map ((diagonalFunctor C).map φt) ≫ K.map (diagonalTransposeIso C B').hom =
        K.map (diagonalTransposeIso C B).hom ≫ K.map ((diagonalFunctor C).map φ) := by
    calc
      _ = K.map ((diagonalFunctor C).map φt ≫ (diagonalTransposeIso C B').hom) :=
        (K.map_comp _ _).symm
      _ = K.map ((diagonalTransposeIso C B).hom ≫ (diagonalFunctor C).map φ) :=
        congrArg (fun f => K.map f) (diagonalTransposeIso_naturality C φ)
      _ = _ := K.map_comp _ _
  have hComposite : QuasiIso
      (K.map (diagonalTransposeIso C B).hom ≫ K.map ((diagonalFunctor C).map φ)) := by
    rw [← hSquare]
    infer_instance
  let _ : QuasiIso
      (K.map (diagonalTransposeIso C B).hom ≫ K.map ((diagonalFunctor C).map φ)) := hComposite
  exact quasiIso_of_comp_left
    (K.map (diagonalTransposeIso C B).hom) (K.map ((diagonalFunctor C).map φ))

end CategoryTheory.SimplicialObject

end
