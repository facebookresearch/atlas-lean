/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HomologyFunctorAccessible
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology of exact colimits

Let C be an abelian category with exact colimits of shape J. For any complex shape c,
homology in degree i commutes with colimits of J-indexed complexes. The comparison
Hᵢ(colim K) ≅ colim Hᵢ(K) identifies the homology of each diagram injection with the
corresponding injection into the colimit of homology.

If the colimit functor preserves homology of short complexes, then the J-shaped colimits
are exact. This implication relates the two equivalent hypotheses in an abelian category.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
universe w w' v u t

namespace HomologicalComplex
variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} {c : ComplexShape ι} [HasColimitsOfShape J C]

-- Keep this implication explicit, since the converse is a native typeclass instance.
/-- In an abelian category C with J-shaped colimits, preservation of short-complex homology
by colim implies exactness of those colimits. -/
theorem hasExactColimitsOfShape_of_colim_preservesHomology
    [(colim (J := J) (C := C)).PreservesHomology] :
    HasExactColimitsOfShape J C where
  preservesFiniteLimits := by
    let _ : (colim (J := J) (C := C)).Additive :=
      preservesFiniteColimits_le_additiveFunctor (J ⥤ C) C _ (by infer_instance)
    exact Functor.preservesFiniteLimits_of_preservesHomology (colim (J := J) (C := C))

variable [HasExactColimitsOfShape J C]

/-- In an abelian category C with exact J-shaped colimits, degree-i homology preserves
colimits of J-indexed complexes of any shape c. -/
instance homologyFunctor_preservesColimitsOfShape (i : ι) :
    PreservesColimitsOfShape J (homologyFunctor C c i) :=
  inferInstanceAs (PreservesColimitsOfShape J
    (shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C))

/-- For a J-indexed diagram K of shape-c complexes in an abelian category C with exact
J-shaped colimits, the canonical comparison identifies Hᵢ(colim K) with colim Hᵢ(K). -/
abbrev homologyColimitIso (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (colimit K).homology i ≅ colimit (K ⋙ homologyFunctor C c i) :=
  preservesColimitIso (homologyFunctor C c i) K

/-- Homology of a diagram injection followed by the comparison is its homology-diagram injection. -/
abbrev map_ι_comp_homologyColimitIso_hom
    (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (homologyFunctor C c i).map (colimit.ι K j) ≫ (homologyColimitIso K i).hom =
      colimit.ι (K ⋙ homologyFunctor C c i) j :=
  ι_preservesColimitIso_hom (G := homologyFunctor C c i) (F := K) j

/-- A homology-diagram injection followed by the inverse comparison is homology of the injection. -/
abbrev ι_comp_homologyColimitIso_inv
    (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    colimit.ι (K ⋙ homologyFunctor C c i) j ≫ (homologyColimitIso K i).inv =
      (homologyFunctor C c i).map (colimit.ι K j) :=
  ι_preservesColimitIso_inv (G := homologyFunctor C c i) (F := K) j

/-- The inverse comparison colim Hᵢ(K) → Hᵢ(colim K) is induced by applying homology
to the colimit injections of K. -/
abbrev homologyColimitIso_inv_eq_colimit_post
    (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (homologyColimitIso K i).inv = colimit.post K (homologyFunctor C c i) := rfl

end HomologicalComplex
