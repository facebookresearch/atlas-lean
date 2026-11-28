/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailFunctor
public import Mathlib.Algebra.Homology.Additive

/-!
# Positive tails commute with zero-preserving functors

Let C and D have zero morphisms and let F : C → D preserve zero morphisms. Mapping a nonnegative
chain complex and then taking its positive tail is naturally isomorphic to first taking its tail
and then mapping it. In degree n both complexes have term F(K_{n+1}) and differential
F(d_K,n+2,n+1); the comparison has identity components.
-/

@[expose] public section

open CategoryTheory Limits

namespace ChainComplex

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Let C and D be categories with zero morphisms and F : C → D a functor preserving zero morphisms.
There is a canonical natural isomorphism T_D ∘ F_* ≅ F_* ∘ T_C on nonnegative chain complexes,
where F_* applies F termwise. Its component at K in degree n is the identity of F(K_{n+1}). -/
def positiveTailMapFunctorIso :
    F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ positiveTailFunctor D ≅
      positiveTailFunctor C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) :=
  NatIso.ofComponents (fun K =>
    HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl (F.obj (K.X (n + 1)))) (by
      intro i j hij
      have hi : j + 1 = i := hij
      subst i
      change 𝟙 _ ≫
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (positiveTail K)).d (j + 1) j =
        (positiveTail ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)).d (j + 1) j ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, positiveTail_d_succ]
      change F.map ((positiveTail K).d (j + 1) j) = F.map (K.d (j + 2) (j + 1))
      rw [positiveTail_d_succ]
      rfl)) (by
        intro K L f
        apply HomologicalComplex.Hom.ext
        funext n
        change F.map (f.f (n + 1)) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.f (n + 1))
        rw [Category.comp_id, Category.id_comp])

end ChainComplex
