/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.FromComplex
public import MathlibExt.Algebra.Homology.Embedding.UpNatToInt
public import MathlibExt.Algebra.Homology.Embedding.ExtendExact

/-!
# Cohomological δ-functors of nonnegative cochain families

Let `A` be preadditive, `B` abelian, and `F : A → CochainComplex B ℕ`
additive and preserving short exact sequences. Extension by zero outside
nonnegative degrees gives a cohomological δ-functor with degree functor
`Hⁿ(F(-))` and the connecting maps of the original cochain sequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CohomologicalDeltaFunctor

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
  (B : Type u₂) [Category.{v₂} B] [Abelian B]

/-- For a preadditive category `A`, an abelian category `B`, and an
additive functor `F : A → CochainComplex B ℕ` preserving short
exact sequences, the nonnegative cohomology functors of `F` form
a cohomological δ-functor `A → B`. -/
def ofNonnegativeCochains (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact) :
    CohomologicalDeltaFunctor A B :=
  ofHomology A B (F ⋙ ComplexShape.embeddingUpNat.extendFunctor B)
    (fun S ↦ by
      simpa only [ShortComplex.map_comp] using
        ShortComplex.ShortExact.map_extendFunctor ComplexShape.embeddingUpNat
          (S.obj.map F) (hF S))
    (fun n ↦ (n : ℤ))
    (fun n ↦ by change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ); simp)
    (-1 : ℤ) (by change (-1 : ℤ) + 1 = (0 : ℤ); norm_num)
    (fun X ↦ HomologicalComplex.isZero_homology_extendUpNat_neg
      (F.obj X) (-1) (by norm_num))

/-- For additive short-exact-sequence-preserving
`F : A → CochainComplex B ℕ`, with `A` preadditive and `B` abelian,
the degree-`n` functor of the resulting δ-functor is naturally
isomorphic to `F ⋙ homologyFunctor B (up ℕ) n`. -/
def ofNonnegativeCochainsHomologyIso (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact) (n : ℕ) :
    (ofNonnegativeCochains A B F hF).T n ≅
      F ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n := by
  change (F ⋙ ComplexShape.embeddingUpNat.extendFunctor B) ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ) ≅ _
  exact Functor.associator F (ComplexShape.embeddingUpNat.extendFunctor B)
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft F
      (HomologicalComplex.homologyFunctorExtendUpNatIso (C := B) n)

/-- For additive short-exact-sequence-preserving
`F : A → CochainComplex B ℕ`, with `A` preadditive and `B` abelian,
the degree-`n` comparison at `X ∈ A` is the homology isomorphism
from the extension-by-zero complex of `F(X)` to its original degree-`n` homology. -/
theorem ofNonnegativeCochainsHomologyIso_hom_app
    (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (n : ℕ) (X : A) :
    (ofNonnegativeCochainsHomologyIso A B F hF n).hom.app X =
      ((F.obj X).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom := by
  change (Functor.associator F (ComplexShape.embeddingUpNat.extendFunctor B)
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ))).hom.app X ≫
    (Functor.isoWhiskerLeft F
      (HomologicalComplex.homologyFunctorExtendUpNatIso (C := B) n)).hom.app X = _
  have hComponent :
      (HomologicalComplex.homologyFunctorExtendUpNatIso (C := B) n).hom.app (F.obj X) =
        ((F.obj X).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom := by
    change (HomologicalComplex.extendHomologyFunctorIso (C := B)
        ComplexShape.embeddingUpNat n (n : ℤ) rfl).hom.app (F.obj X) = _
    exact HomologicalComplex.extendHomologyFunctorIso_hom_app
      ComplexShape.embeddingUpNat n (n : ℤ) rfl (F.obj X)
  simpa only [Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp] using hComponent

/-- For additive short-exact-sequence-preserving
`F : A → CochainComplex B ℕ`, with `A` preadditive and `B` abelian,
the degree-`n` comparison carries the constructed connecting map
to the boundary `Hⁿ(F(S.X₃)) → Hⁿ⁺¹(F(S.X₁))` of every
short exact sequence `S` in `A`. -/
theorem ofNonnegativeCochains_connecting_app
    (F : A ⥤ CochainComplex B ℕ) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (n : ℕ) (S : ShortComplex.ShortExactSequences A) :
    (ofNonnegativeCochainsHomologyIso A B F hF n).hom.app S.obj.X₃ ≫
        (hF S).δ n (n + 1) (by rfl) =
      ((ofNonnegativeCochains A B F hF).connecting n).app S ≫
        (ofNonnegativeCochainsHomologyIso A B F hF (n + 1)).hom.app S.obj.X₁ := by
  rw [ofNonnegativeCochainsHomologyIso_hom_app,
    ofNonnegativeCochainsHomologyIso_hom_app]
  change ((F.obj S.obj.X₃).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom ≫
      (hF S).δ n (n + 1) (by rfl) =
    (ShortComplex.ShortExact.map_extendFunctor ComplexShape.embeddingUpNat
      (S.obj.map F) (hF S)).δ (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (by change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ); simp) ≫
      ((F.obj S.obj.X₁).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
  exact ShortComplex.ShortExact.map_extendFunctor_δ ComplexShape.embeddingUpNat
    (S.obj.map F) (hF S) n (n + 1) (n : ℤ) ((n + 1 : ℕ) : ℤ) rfl rfl
    (by rfl) (by change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ); simp)

end CategoryTheory.CohomologicalDeltaFunctor

end
