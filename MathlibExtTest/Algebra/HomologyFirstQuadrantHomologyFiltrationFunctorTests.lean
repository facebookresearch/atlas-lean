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

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationFunctor

/-! # Tests for the finite total-homology filtration diagram functor -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyFiltrationFunctorTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFiniteTotalHomologyFiltrationDiagramFunctor
#check horizontalFiniteTotalHomologyFiltrationDiagramFunctor_obj_obj
#check horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app
#check horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι

example (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      ℕ ⥤ C :=
  horizontalFiniteTotalHomologyFiltrationDiagramFunctor n

example (n i : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).obj K).obj i =
      (horizontalFiniteTotalHomologyFiltration K n).obj i := by
  simp

example (n i : ℕ) (f : K ⟶ L) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app i =
      horizontalFiniteHomologyImageMapOfBicomplex f n i :=
  horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app n f i

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor 0).obj K).obj 0 =
      (horizontalFiniteTotalHomologyFiltration K 0).obj 0 := by
  simp

example (n i : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map (𝟙 K)).app i =
      𝟙 ((horizontalFiniteTotalHomologyFiltration K n).obj i) := by
  simp

example (n i : ℕ) (f : K ⟶ L) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app i ≫
        (horizontalFiniteTotalHomologyFiltration L n).ι.app i =
      (horizontalFiniteTotalHomologyFiltration K n).ι.app i ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) n :=
  horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι n f i

#print axioms horizontalFiniteTotalHomologyFiltrationDiagramFunctor
#print axioms horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι

end HomologicalComplex₂.FirstQuadrantHomologyFiltrationFunctorTests

end
