/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.CategoryHomology.ClassifyingSpaceSingular

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w v u

namespace MathlibExtTest.CategoryTheory.CategoryHomology
namespace ClassifyingSpaceSingularTests

#check CategoryTheory.nerve_isConnected_of_category_isConnected
#check CategoryTheory.classifyingSpaceCGWHSingularIntegralHomologyIso
#check CategoryTheory.classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality

section Generic

variable {C D E : Type u}
  [Category.{v} C] [Category.{v} D] [Category.{v} E]

example (n : ℕ) :
    AlgebraicTopology.singularIntegralHomology n
        (CGWH.cgwhToTop.obj
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))) ≅
      (nerve C).homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{max u v}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n

example (F : C ⥤ D) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
          (CGWH.cgwhToTop.map
            (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)) ≫
        (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} D n).hom =
      (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n).hom ≫
        SSet.homologyMap (nerveMap F)
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{max u v}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality.{w} F n

example (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
          (CGWH.cgwhToTop.map
            (classifyingSpaceCGWH.{w, v, u}.map (𝟭 C).toCatHom)) ≫
        (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n).hom =
      (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n).hom ≫
        SSet.homologyMap (nerveMap (𝟭 C))
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{max u v}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality.{w}
    (𝟭 C) n

example (F : C ⥤ D) (G : D ⥤ E) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
          (CGWH.cgwhToTop.map
            (classifyingSpaceCGWH.{w, v, u}.map (F ⋙ G).toCatHom)) ≫
        (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} E n).hom =
      (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n).hom ≫
        SSet.homologyMap (nerveMap (F ⋙ G))
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{max u v}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality.{w}
    (F ⋙ G) n

example [IsConnected C] : (nerve C).IsConnected :=
  nerve_isConnected_of_category_isConnected

end Generic

section EmptyCategory

abbrev EmptyCat := Discrete PEmpty

example (n : ℕ) :
    AlgebraicTopology.singularIntegralHomology n
        (CGWH.cgwhToTop.obj
          (classifyingSpaceCGWH.{0, 0, 0}.obj (Cat.of EmptyCat))) ≅
      (nerve EmptyCat).homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{0}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso.{0} EmptyCat n

end EmptyCategory

section ConnectedBoundary

example : (nerve (Discrete PUnit)).IsConnected := by
  let _ : IsConnected (Discrete PUnit) := by
    apply zigzag_isConnected
    rintro ⟨x⟩ ⟨y⟩
    obtain rfl : x = y := Subsingleton.elim _ _
    exact Zigzag.refl _
  exact nerve_isConnected_of_category_isConnected

end ConnectedBoundary

section MixedRaisedUniverses

variable {C D : Type 1} [Category.{0} C] [Category.{0} D]

example (n : ℕ) :
    AlgebraicTopology.singularIntegralHomology n
        (CGWH.cgwhToTop.obj
          (classifyingSpaceCGWH.{2, 0, 1}.obj (Cat.of C))) ≅
      (nerve C).homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{1}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso.{2} C n

example (F : C ⥤ D) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor.{1} n).map
          (CGWH.cgwhToTop.map
            (classifyingSpaceCGWH.{2, 0, 1}.map F.toCatHom)) ≫
        (classifyingSpaceCGWHSingularIntegralHomologyIso.{2} D n).hom =
      (classifyingSpaceCGWHSingularIntegralHomologyIso.{2} C n).hom ≫
        SSet.homologyMap (nerveMap F)
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{1}) n :=
  classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality.{2} F n

end MixedRaisedUniverses

#print axioms CategoryTheory.nerve_isConnected_of_category_isConnected
#print axioms CategoryTheory.classifyingSpaceCGWHSingularIntegralHomologyIso
#print axioms CategoryTheory.classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality

end ClassifyingSpaceSingularTests
end MathlibExtTest.CategoryTheory.CategoryHomology

end
