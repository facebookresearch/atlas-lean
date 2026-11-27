/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.HomotopyEquivalence
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso

/-!
# Rowwise quasi-isomorphisms on bisimplicial diagonals

In an abelian category with countable coproducts, a map of bisimplicial objects that
is a quasi-isomorphism on the alternating-face complex of each inner row induces
a quasi-isomorphism on the alternating-face complex of the diagonal.

The Alexander–Whitney and shuffle homotopy equivalence compares diagonal chains
with the signed first-quadrant total complex, and its naturality transports the
rowwise total comparison to the diagonal. Category object and morphism universes
remain independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [Abelian C]
  [Limits.HasCountableCoproducts C]

/--
For a map `φ : X ⟶ Y` of bisimplicial objects in an abelian category with countable
coproducts, if each component at fixed outer degree `p` induces a quasi-isomorphism
of inner alternating-face complexes, then the diagonal alternating-face map is a
quasi-isomorphism.
-/
theorem quasiIso_alternatingDiagonal_of_rows
    {X Y : SimplicialObject (SimplicialObject C)} (φ : X ⟶ Y)
    (hφ : ∀ p : ℕ, QuasiIso ((alternatingFaceMapComplex C).map (φ.app (Opposite.op ⦋p⦌)))) :
    QuasiIso ((alternatingFaceMapComplex C).map ((SimplicialObject.diagonalFunctor C).map φ)) := by
  let b := (bisimplicialAlternatingBicomplexFunctor C).map φ
  have hb : ∀ p : ℕ, QuasiIso (b.f p) := fun p => hφ p
  let t := (bisimplicialAlternatingTotalComplexFunctor C).map φ
  let _ : QuasiIso t := HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant b hb
  let eX := BisimplicialNormalization.homotopyEquiv X
  let eY := BisimplicialNormalization.homotopyEquiv Y
  let d := (alternatingFaceMapComplex C).map ((SimplicialObject.diagonalFunctor C).map φ)
  let _ : QuasiIso eX.hom := eX.quasiIso_hom
  let _ : QuasiIso eY.hom := eY.quasiIso_hom
  have hnat : d ≫ eY.hom = eX.hom ≫ t :=
    BisimplicialAlexanderWhitney.alternatingMap_naturality φ
  have hd : QuasiIso (d ≫ eY.hom) := by
    rw [hnat]
    infer_instance
  let _ : QuasiIso (d ≫ eY.hom) := hd
  exact quasiIso_of_comp_right d eY.hom

end CategoryTheory.SimplicialObject
