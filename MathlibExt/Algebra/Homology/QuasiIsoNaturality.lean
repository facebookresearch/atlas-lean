/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of the homology isomorphism induced by a quasi-isomorphism

Given a commuting square of homological complexes in which the horizontal
arrows are quasi-isomorphisms in degree `i`, the isomorphisms
`isoOfQuasiIsoAt` commute with the maps induced on homology by the vertical
arrows. This is the one-degree naturality square for `isoOfQuasiIsoAt`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {c : ComplexShape ι}
variable {K L K' L' : HomologicalComplex C c}

/-- Naturality square for `isoOfQuasiIsoAt`.

For a commuting square `u ≫ f' = f ≫ v` in which `f` and `f'` are
quasi-isomorphisms in degree `i`, the homology maps of the vertical arrows
commute with the induced homology isomorphisms of the horizontal arrows:

`homologyMap u ≫ (isoOfQuasiIsoAt f').hom = (isoOfQuasiIsoAt f).hom ≫ homologyMap v`.

The proof applies `homologyMap` to the commuting square and uses the
functoriality `homologyMap_comp` together with
`(isoOfQuasiIsoAt _ _).hom = homologyMap _ _`. -/
theorem isoOfQuasiIsoAt_naturality
    (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    [QuasiIsoAt f i] [QuasiIsoAt f' i]
    (h : u ≫ f' = f ≫ v) :
    homologyMap u i ≫ (isoOfQuasiIsoAt f' i).hom =
      (isoOfQuasiIsoAt f i).hom ≫ homologyMap v i := by
  simpa only [isoOfQuasiIsoAt_hom] using homologyMap_square h i

/-- Inverse form of the `isoOfQuasiIsoAt` naturality square.

Under the same hypotheses as `isoOfQuasiIsoAt_naturality`, the inverse
isomorphisms satisfy the transposed square:

`(isoOfQuasiIsoAt f).inv ≫ homologyMap u = homologyMap v ≫ (isoOfQuasiIsoAt f').inv`.
-/
theorem isoOfQuasiIsoAt_inv_naturality
    (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    [QuasiIsoAt f i] [QuasiIsoAt f' i]
    (h : u ≫ f' = f ≫ v) :
    (isoOfQuasiIsoAt f i).inv ≫ homologyMap u i =
      homologyMap v i ≫ (isoOfQuasiIsoAt f' i).inv := by
  have hhom := isoOfQuasiIsoAt_naturality f f' u v i h
  calc (isoOfQuasiIsoAt f i).inv ≫ homologyMap u i
      = (isoOfQuasiIsoAt f i).inv ≫ homologyMap u i ≫ 𝟙 _ := by simp
    _ = (isoOfQuasiIsoAt f i).inv ≫ homologyMap u i ≫
          ((isoOfQuasiIsoAt f' i).hom ≫ (isoOfQuasiIsoAt f' i).inv) := by simp
    _ = (isoOfQuasiIsoAt f i).inv ≫ (isoOfQuasiIsoAt f i).hom ≫
          homologyMap v i ≫ (isoOfQuasiIsoAt f' i).inv := by
        simp only [← Category.assoc, hhom]
    _ = homologyMap v i ≫ (isoOfQuasiIsoAt f' i).inv := by simp

end HomologicalComplex
