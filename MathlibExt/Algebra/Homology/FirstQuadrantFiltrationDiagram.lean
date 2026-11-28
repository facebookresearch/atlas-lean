/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Filtration.Basic
public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationMaps

/-!
# The increasing horizontal filtration of a total chain complex

Let C be preadditive with a zero object and finite coproducts, and let K
be a nonnegative homological bicomplex. The complexes
F_k T_n = ⨁_(p+q=n, p≤k) K_(p,q) form an increasing filtration
of T = Tot(K) by subcomplexes.

For k≤l, the stage map F_k T → F_l T includes the same coordinates
and commutes with the inclusions into T. Each stage-to-total chain
map is monic. In every degree n, the inclusion F_k T_n → T_n is an
isomorphism once n≤k, with inverse the coordinate projection.
This is degreewise finite exhaustiveness of the filtration.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the inclusions
F_k T_n → Tot(K)_n define the chain map i_k : F_k T → Tot(K).
The stage differential is the restriction of the signed total
differential, so each degree square commutes. -/
noncomputable def horizontalFilteredTotalComplexToTotal (k : ℕ) :
    horizontalFilteredTotalComplex K k ⟶
      K.total (ComplexShape.down ℕ) where
  f := horizontalFilteredTotalToTotal K k
  comm' := by
    intro n m hnm
    obtain rfl : n = m + 1 := hnm.symm
    exact (horizontalFilteredTotalD_toTotal K k m).symm

noncomputable instance horizontalFilteredTotalComplexToTotal_mono (k : ℕ) :
    Mono (horizontalFilteredTotalComplexToTotal K k) :=
  HomologicalComplex.mono_of_mono_f _ fun n => by
    change Mono (horizontalFilteredTotalToTotal K k n)
    infer_instance

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalComplexMap_toTotal
    {k l : ℕ} (h : k ≤ l) :
    horizontalFilteredTotalComplexMap K h ≫
        horizontalFilteredTotalComplexToTotal K l =
      horizontalFilteredTotalComplexToTotal K k := by
  ext n
  exact horizontalFilteredTotalMap_toTotal K h n

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the complexes
F_k T with coordinates p≤k form a filtration of Tot(K) indexed
by ℕ. Its stage maps are coordinate inclusions, and its stage
inclusions into Tot(K) are monomorphisms of chain complexes. -/
noncomputable def horizontalTotalFiltration :
    CategoryTheory.Filtration (K.total (ComplexShape.down ℕ)) ℕ where
  toMonoOver :=
    { obj := fun k => MonoOver.mk
        (horizontalFilteredTotalComplexToTotal K k)
      map := fun {k l} f => MonoOver.homMk
        (horizontalFilteredTotalComplexMap K (leOfHom f))
        (horizontalFilteredTotalComplexMap_toTotal K (leOfHom f))
      map_id := by
        intro k
        apply Subsingleton.elim
      map_comp := by
        intro k l m f g
        apply Subsingleton.elim }

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltration_diagram_obj (k : ℕ) :
    (horizontalTotalFiltration K).diagram.obj k =
      horizontalFilteredTotalComplex K k :=
  rfl

omit [HasZeroObject C] in
/-- The underlying chain complex of a horizontal filtration subobject is its horizontal stage. -/
@[simp]
theorem horizontalTotalFiltration_toMonoOver_obj_left (i : ℕ) :
    ((horizontalTotalFiltration K).toMonoOver.obj i).obj.left =
      horizontalFilteredTotalComplex K i := by
  change (horizontalTotalFiltration K).diagram.obj i = _
  exact horizontalTotalFiltration_diagram_obj K i

omit [HasZeroObject C] in
theorem horizontalTotalFiltration_diagram_map
    {k l : ℕ} (h : k ≤ l) :
    (horizontalTotalFiltration K).diagram.map (homOfLE h) =
      horizontalFilteredTotalComplexMap K h :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltration_ι_app (k : ℕ) :
    (horizontalTotalFiltration K).ι.app k =
      horizontalFilteredTotalComplexToTotal K k :=
  rfl

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, if n≤k, the stage inclusion gives
F_k T_n ≅ Tot(K)_n.
The forward map is the filtered-to-total inclusion and the inverse
retains every total antidiagonal coordinate, since p≤n≤k. -/
noncomputable def horizontalTotalFiltrationEvalIsoOfLE
    (k n : ℕ) (h : n ≤ k) :
    ((horizontalTotalFiltration K).obj k).X n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  horizontalFilteredTotalIsoOfLE K k n h

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationEvalIsoOfLE_hom
    (k n : ℕ) (h : n ≤ k) :
    (horizontalTotalFiltrationEvalIsoOfLE K k n h).hom =
      ((horizontalTotalFiltration K).ι.app k).f n :=
  rfl

end HomologicalComplex₂

end
