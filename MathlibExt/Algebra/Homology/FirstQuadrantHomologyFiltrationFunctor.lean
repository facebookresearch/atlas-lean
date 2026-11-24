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

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationNaturality
public import MathlibExt.CategoryTheory.NatTrans.PointwiseImage

/-!
# The finite total-homology filtration diagram functor

The finite-stage inclusions into total homology form a natural transformation
of natural-index diagrams.  Taking its pointwise images packages the induced
homology filtration as a functor of the first-quadrant bicomplex.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The finite total-homology filtration diagram, functorial in the
first-quadrant bicomplex. -/
noncomputable def horizontalFiniteTotalHomologyFiltrationDiagramFunctor
    (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      ℕ ⥤ C :=
  (horizontalTotalFiltrationHomologyDiagramToTotal (C := C) n).pointwiseImage

@[simp]
theorem horizontalFiniteTotalHomologyFiltrationDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).obj K).obj i =
      (horizontalFiniteTotalHomologyFiltration K n).obj i :=
  rfl

@[simp]
theorem horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app i =
      horizontalFiniteHomologyImageMapOfBicomplex f n i :=
  rfl

/-- The functorial map between finite homology-filtration stages commutes
with their canonical inclusions into total homology. -/
@[reassoc (attr := simp)]
theorem horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app i ≫
        (horizontalFiniteTotalHomologyFiltration L n).ι.app i =
      (horizontalFiniteTotalHomologyFiltration K n).ι.app i ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) n := by
  rw [horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app,
    horizontalFiniteTotalHomologyFiltration_ι_app,
    horizontalFiniteTotalHomologyFiltration_ι_app]
  exact horizontalFiniteHomologyImageMapOfBicomplex_ι f n i

end HomologicalComplex₂

end
