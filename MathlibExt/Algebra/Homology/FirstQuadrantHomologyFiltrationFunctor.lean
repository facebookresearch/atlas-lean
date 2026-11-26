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
# Functorial image diagrams for total homology

Let C be an abelian category and n ∈ ℕ. For a bicomplex K of shape (down ℕ,down ℕ), the images
of the horizontal-stage maps H_n(G_i(K)) → H_n(Tot(K)) form a diagram ℕ → C. A bicomplex
morphism induces a map between these diagrams by the corresponding commutative squares on
homology.

This gives a functor from first-quadrant bicomplexes to ℕ-indexed C-diagrams. Each stage map
commutes with the inclusion of its image into total homology.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category and n ∈ ℕ. Assign to a bicomplex K of shape (down ℕ,down ℕ) the
diagram i ↦ im(H_n(G_i(K)) → H_n(Tot(K))), for i ∈ ℕ, where G_i retains horizontal columns at
most i. This assignment is a functor to ℕ ⥤ C. A bicomplex map f induces the pointwise image
map of the square with horizontal arrows the stage-homology inclusions and vertical arrows
H_n(G_i(f)) and H_n(Tot(f)). The transition maps arise from the stage inclusions G_i → G_j for
i ≤ j. -/
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

/-- Let C be an abelian category, f : K → L a map of bicomplexes of shape (down ℕ,down ℕ), and n,i
∈ ℕ. Let F_i(K) and F_i(L) be the images of the stage-homology maps into total homology, and
let a_i : F_i(K) → F_i(L) be the component of the image-diagram functor applied to f. If ι_i^K
and ι_i^L are the image inclusions, then a_i ≫ ι_i^L = ι_i^K ≫ H_n(Tot(f)). This is the
compatibility needed for a map of filtered homology objects. -/
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
