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

public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Quasi-isomorphisms of filtered colimit legs

Let K be a filtered diagram of homological complexes of arbitrary shape in an abelian
category. Assume colimits of that indexing shape exist and the colimit functor preserves
homology. If every transition of K is a quasi-isomorphism, every leg of any colimit cocone is
a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe wJ vJ u v t

variable {J : Type wJ} [Category.{vJ} J] [IsFiltered J]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type t} {c : ComplexShape I}
variable [HasColimitsOfShape J C]
variable [(colim (J := J) (C := C)).PreservesHomology]

/-- Every filtered colimit leg is a quasi-isomorphism.

For an actual colimit cocone of K, homology-preserving colimits and quasi-isomorphic diagram
transitions imply that its leg from every stage is a quasi-isomorphism. -/
theorem quasiIso_ι_of_isColimit_of_quasiIso_maps
    (K : J ⥤ HomologicalComplex C c) (s : Cocone K) (hs : IsColimit s)
    (hK : ∀ {i j : J} (f : i ⟶ j), QuasiIso (K.map f)) (j : J) :
    QuasiIso (s.ι.app j) := by
  let _ : HasExactColimitsOfShape J C :=
    CategoryTheory.HasExactColimitsOfShape.of_colim_preservesHomology (J := J) (C := C)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H : HomologicalComplex C c ⥤ C := homologyFunctor C c n
  have h : (K ⋙ H).IsEventuallyConstantFrom j := by
    intro k f
    let _ : QuasiIso (K.map f) := hK f
    change IsIso (homologyMap (K.map f) n)
    infer_instance
  exact h.isIso_ι_of_isColimit (isColimitOfPreserves H hs)

end HomologicalComplex
