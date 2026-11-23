/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.GroupCompletionSpace
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHomology

/-!
# Realization of the additive S⁻¹S zero component

The nerve of the categorical zero component is the selected connected-
component subcomplex of the full additive `S⁻¹S` nerve.  Applying native
CGWH realization gives an isomorphism whose composite with the realized
component inclusion is the existing categorical zero-component inclusion.
The same formula is exposed after forgetting to ordinary topological spaces.

These are isomorphisms of realizations.  No ambient-subspace equality,
telescope comparison, Bousfield--Kan statement, or plus recognition is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe w v u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Native CGWH realization identifies the categorical zero component with
the selected simplicial connected component. -/
noncomputable def zeroComponentClassifyingSpaceComponentIso :
    zeroComponentClassifyingSpace.{w} C ≅
      SSet.toCGWH.{w, max u v}.obj
        (zeroComponentNerveComponent C : SSet) :=
  SSet.toCGWH.{w, max u v}.mapIso (zeroComponentNerveIso C)

/-- The realized zero-component comparison followed by the realized
component inclusion is the categorical zero-component inclusion. -/
@[reassoc]
theorem zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion :
    (zeroComponentClassifyingSpaceComponentIso.{w} C).hom ≫
        SSet.toCGWH.{w, max u v}.map
          (zeroComponentNerveComponent C).ι =
      zeroComponentClassifyingSpaceInclusion.{w} C := by
  change SSet.toCGWH.{w, max u v}.map (zeroComponentNerveIso C).hom ≫
      SSet.toCGWH.{w, max u v}.map
        (zeroComponentNerveComponent C).ι =
    SSet.toCGWH.{w, max u v}.map
      (nerveMap (zeroComponentProperty (C := C)).ι)
  rw [← Functor.map_comp, zeroComponentNerveIso_hom_comp_ι]

/-- The zero-component realization comparison after forgetting from CGWH to
ordinary topological spaces. -/
noncomputable def zeroComponentClassifyingSpaceComponentTopIso :
    CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C) ≅
      CGWH.cgwhToTop.obj
        (SSet.toCGWH.{w, max u v}.obj
          (zeroComponentNerveComponent C : SSet)) :=
  CGWH.cgwhToTop.{w, max u v}.mapIso
    (zeroComponentClassifyingSpaceComponentIso.{w} C)

/-- The underlying-Top comparison retains the realized component-inclusion
formula. -/
@[reassoc]
theorem zeroComponentClassifyingSpaceComponentTopIso_hom_comp_inclusion :
    (zeroComponentClassifyingSpaceComponentTopIso.{w} C).hom ≫
        CGWH.cgwhToTop.{w, max u v}.map
          (SSet.toCGWH.{w, max u v}.map
            (zeroComponentNerveComponent C).ι) =
      CGWH.cgwhToTop.{w, max u v}.map
        (zeroComponentClassifyingSpaceInclusion.{w} C) := by
  change CGWH.cgwhToTop.{w, max u v}.map
        (zeroComponentClassifyingSpaceComponentIso.{w} C).hom ≫
      CGWH.cgwhToTop.{w, max u v}.map
        (SSet.toCGWH.{w, max u v}.map
          (zeroComponentNerveComponent C).ι) = _
  rw [← Functor.map_comp,
    zeroComponentClassifyingSpaceComponentIso_hom_comp_inclusion]
  rfl

/-- The same comparison with the selected component realized directly in
ordinary topological spaces. -/
noncomputable def zeroComponentClassifyingSpaceComponentRealizationTopIso :
    CGWH.cgwhToTop.obj (zeroComponentClassifyingSpace.{w} C) ≅
      SSet.toTop.obj (zeroComponentNerveComponent C : SSet) :=
  zeroComponentClassifyingSpaceComponentTopIso.{w} C ≪≫
    SSet.realizationToTopIso.{w, max u v}.app
      (zeroComponentNerveComponent C : SSet)

end SInverseS
end CategoryTheory

end
