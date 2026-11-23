/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Filtration.Basic
public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationMaps

/-!
# The canonical filtration of a first-quadrant total complex

The horizontal stages of a first-quadrant bicomplex form a filtration of its
total complex in the sense of `CategoryTheory.Filtration`: each stage is a
subcomplex, transition maps commute with the inclusions, and the inclusions
are monomorphisms.  In every total degree `n`, the filtration is already the
whole total object from stage `n` onward.

The associated spectral object is constructed in
`FirstQuadrantSpectralObject` and completed over `EInt` in
`FirstQuadrantCompleteFiltration`.
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

/-- Inclusion of a horizontal filtration stage into the total complex. -/
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

/-- The horizontal filtration of a first-quadrant total complex, bundled
using Mathlib's canonical filtration API. -/
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

/-- In total degree `n`, stage `k` of the canonical filtration is the whole
total degree whenever `n ≤ k`. -/
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
