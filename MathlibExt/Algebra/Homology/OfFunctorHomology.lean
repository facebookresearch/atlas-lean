/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.OfFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex

variable {J C : Type*} [Category J] [Category C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι}

/-- Canonical iso from homology of `ofFunctor K` in `J ⥤ C` to pointwise
homology `K ⋙ homologyFunctor`. -/
noncomputable def ofFunctorHomologyIso (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (homologyFunctor (J ⥤ C) c i).obj (ofFunctor K) ≅
      K ⋙ homologyFunctor C c i :=
  NatIso.ofComponents
    (fun j =>
      let S := (ofFunctor K).sc i
      (S.mapHomologyIso ((evaluation J C).obj j)).symm)
    (fun {j j'} f => by
      let S := (ofFunctor K).sc i
      let F := (evaluation J C).obj j
      let G := (evaluation J C).obj j'
      let τ : F ⟶ G := (evaluation J C).map f
      exact NatTrans.app_homology_comp_mapHomologyIso_inv τ S)

/-- Component formula: the `j`-th component of the hom is the inverse of
`mapHomologyFunctorIso` at `ofFunctor K` for evaluation at `j`. -/
@[simp]
theorem ofFunctorHomologyIso_hom_app (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (ofFunctorHomologyIso K i).hom.app j =
      ((mapHomologyFunctorIso i ((evaluation J C).obj j)).app (ofFunctor K)).inv :=
  rfl

end HomologicalComplex
