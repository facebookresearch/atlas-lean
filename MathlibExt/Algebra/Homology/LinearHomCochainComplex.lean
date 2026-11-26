/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.CategoryTheory.Linear.Yoneda.Limits
/-!
# Linear Hom-cochains of a chain complex

Let R be a ring and C a preadditive R-linear category. For a chain complex K indexed by ℕ and
an object G, the linear Hom-cochain complex has degree-n module Hom_C(K_n, G) and differential
φ ↦ d_(n+1,n) ≫ φ. It is contravariant in K and covariant in G; the modules have the morphism
universe of C.

For fixed G, the contravariant complex functor preserves limits of shape J when Cᵒᵖ has those
limits. For fixed K and n, its cohomology defines the coefficient functor G ↦ H^n(Hom_C(K,
G)). Applying Hom-cochains to a chain homotopy gives a cochain homotopy and equal maps on
cohomology where the indicated objects exist.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe w v u vJ uJ
namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

noncomputable def linearHomCochainComplexFunctor (G : C) :
    (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    ((linearYoneda R C).obj G).mapHomologicalComplex (ComplexShape.up ℕ)

noncomputable instance linearHomCochainComplexFunctor_additive (G : C) :
    (linearHomCochainComplexFunctor R C G).Additive := by
  change (HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    ((linearYoneda R C).obj G).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).Additive
  infer_instance

/-- Let R be a ring and C a preadditive R-linear category. Let G : C and let J be a category such
that Cᵒᵖ has limits of shape J. The functor (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat
R) ℕ sending K to the cochains Hom_C(K_n, G) preserves limits of shape J. Its cochain modules
lie in the morphism universe of C. -/
noncomputable instance
    linearHomCochainComplexFunctor_preservesLimitsOfShape
    {J : Type uJ} [Category.{vJ} J] [HasLimitsOfShape J Cᵒᵖ]
    (G : C) :
    PreservesLimitsOfShape J
      (linearHomCochainComplexFunctor R C G) := by
  have hOp : PreservesLimitsOfShape J
      (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)) :=
    inferInstance
  have hMap : PreservesLimitsOfShape J
      (((linearYoneda R C).obj G).mapHomologicalComplex
        (ComplexShape.up ℕ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval
      (((linearYoneda R C).obj G).mapHomologicalComplex
        (ComplexShape.up ℕ))
      (fun n => by
        have hEval : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n) :=
          inferInstance
        have hYoneda : PreservesLimitsOfShape J
            ((linearYoneda R C).obj G) :=
          inferInstance
        have hComp : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ
                (ComplexShape.up ℕ) n ⋙
              (linearYoneda R C).obj G) :=
          @CategoryTheory.Limits.comp_preservesLimitsOfShape
            _ _ _ _ _ _ _ _
            (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n)
            ((linearYoneda R C).obj G) hEval hYoneda
        change PreservesLimitsOfShape J
          (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n ⋙
            (linearYoneda R C).obj G)
        exact hComp)
  exact @CategoryTheory.Limits.comp_preservesLimitsOfShape
    _ _ _ _ _ _ _ _
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (((linearYoneda R C).obj G).mapHomologicalComplex
      (ComplexShape.up ℕ)) hOp hMap
noncomputable def linearHomCochainComplexBifunctor :
    C ⥤ ((ChainComplex C ℕ)ᵒᵖ ⥤
      CochainComplex (ModuleCat.{v} R) ℕ) where
  obj G := linearHomCochainComplexFunctor R C G
  map f := Functor.whiskerLeft
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (NatTrans.mapHomologicalComplex
      ((linearYoneda R C).map f) (ComplexShape.up ℕ))

@[simp]
lemma linearHomCochainComplexFunctor_obj_X (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C G).obj (Opposite.op K)).X n =
      ModuleCat.of R (K.X n ⟶ G) := rfl

/-- Let R be a ring and C a preadditive R-linear category. For a chain complex K indexed by ℕ and
n : ℕ, define the functor C ⥤ ModuleCat R by G ↦ H^n(Hom_C(K, G)). The cochain modules in
degree i are Hom_C(K_i, G), with differential given by precomposition with d_K(i+1,i);
coefficient morphisms act by postcomposition. -/
noncomputable def linearHomCochainComplexHomologyFunctor
    (K : ChainComplex C ℕ) (n : ℕ) : C ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexBifunctor R C ⋙
    (evaluation _ _).obj (Opposite.op K) ⋙
    homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : ChainComplex C ℕ} {f g : K ⟶ L}

/-- Let R be a ring and C a preadditive R-linear category. Let f, g : K ⟶ L be chain maps between
complexes indexed by ℕ, and let h be a chain homotopy from f to g. For G : C, precomposition
with f and g gives maps Hom_C(L, G) ⟶ Hom_C(K, G) of cochain complexes. Applying the linear
Yoneda functor to the opposite homotopy gives a cochain homotopy between these maps. -/
noncomputable def mapLinearHomCochainComplex (h : Homotopy f g) (G : C) :
    Homotopy
      ((linearHomCochainComplexFunctor R C G).map f.op)
      ((linearHomCochainComplexFunctor R C G).map g.op) :=
  ((linearYoneda R C).obj G).mapHomotopy h.op

/-- Let R be a ring and C a preadditive R-linear category. Let f, g : K ⟶ L be chain-homotopic
maps of complexes indexed by ℕ. Fix G : C and n : ℕ, and assume the cochain complexes Hom_C(L,
G) and Hom_C(K, G) have homology in degree n. Then the maps on H^n induced by precomposition
with f and with g are equal, from H^n(Hom_C(L, G)) to H^n(Hom_C(K, G)). -/
lemma linearHomCochainComplex_homologyMap_eq
    (h : Homotopy f g) (G : C) (n : ℕ)
    [((linearHomCochainComplexFunctor R C G).obj (Opposite.op L)).HasHomology n]
    [((linearHomCochainComplexFunctor R C G).obj (Opposite.op K)).HasHomology n] :
    homologyMap ((linearHomCochainComplexFunctor R C G).map f.op) n =
      homologyMap ((linearHomCochainComplexFunctor R C G).map g.op) n :=
  (h.mapLinearHomCochainComplex R G).homologyMap_eq n

end Homotopy
