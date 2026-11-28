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
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

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
    let _ : HasBinaryBiproducts (J ⥤ C) :=
      HasBinaryBiproducts.of_hasBinaryProducts
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

/-- Let C be abelian with exact J-shaped colimits, and K a J-indexed diagram of
complexes of any shape. In degree i, homology of the injection from K(j), followed
by the homology-colimit comparison, is the injection from H_i(K(j)) into its colimit. -/
@[reassoc (attr := simp)]
theorem map_ι_comp_homologyColimitIso_hom
    (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (homologyFunctor C c i).map (colimit.ι K j) ≫ (homologyColimitIso K i).hom =
      colimit.ι (K ⋙ homologyFunctor C c i) j :=
  ι_preservesColimitIso_hom (G := homologyFunctor C c i) (F := K) j

/-- Let C be abelian with exact J-shaped colimits, and K a J-indexed diagram of
complexes of any shape. In degree i, the injection of H_i(K(j)) into the colimit,
followed by the inverse homology-colimit comparison, is homology of the injection K(j). -/
@[reassoc (attr := simp)]
theorem ι_comp_homologyColimitIso_inv
    (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    colimit.ι (K ⋙ homologyFunctor C c i) j ≫ (homologyColimitIso K i).inv =
      (homologyFunctor C c i).map (colimit.ι K j) :=
  ι_preservesColimitIso_inv (G := homologyFunctor C c i) (F := K) j

/-- Let C be abelian with exact J-shaped colimits, and K a J-indexed diagram of
complexes of any shape. The inverse comparison colim H_i(K) → H_i(colim K)
is the colimit map induced by applying degree-i homology to every diagram injection. -/
theorem homologyColimitIso_inv_eq_colimit_post
    (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (homologyColimitIso K i).inv = colimit.post K (homologyFunctor C c i) := rfl

end HomologicalComplex
