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
# δ-functors from nonnegative cochain families

The extension by zero supplies the missing predecessor of degree zero. The existing homology
constructor supplies the connecting maps and exact sequence. Degree homology is identified through
the extension isomorphism, with its naturality and boundary transport. Universality is separate.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CohomologicalDeltaFunctor

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
  (B : Type u₂) [Category.{v₂} B] [Abelian B]

/-- The homology δ-functor of a nonnegative additive cochain family. -/
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

/-- Its degree functor is naturally identified with the original Nat homology. -/
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

/-- A degree component is the homology comparison of the extension. -/
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

/-- The connecting map agrees with the Nat boundary under those comparisons. -/
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
