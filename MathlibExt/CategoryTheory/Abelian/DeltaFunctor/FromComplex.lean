/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Basic
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor

/-!
# δ-functors from homology of functorial complexes

A functor carrying short exact sequences to short exact sequences of complexes gives natural
connecting maps and a long exact homology sequence. Vanishing in the adjacent degree supplies
the degree-zero endpoint. The construction applies to arbitrary index types and complex shapes.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂ u₃

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
variable (B : Type u₂) [Category.{v₂} B] [Abelian B]
variable {ι : Type u₃} {c : ComplexShape ι}

namespace HomologicalDeltaFunctor

/-- Homology of a functorial family of complexes gives a homological δ-functor
when the complexes preserve short exact sequences and homology vanishes in the
degree adjacent to degree zero. The source needs only a preadditive structure. -/
noncomputable def ofHomology (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i (n + 1)) (i n))
    (j : ι) (h₀ : c.Rel (i 0) j)
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) :
    HomologicalDeltaFunctor A B where
  T n := F ⋙ HomologicalComplex.homologyFunctor B c (i n)
  additive _ := inferInstance
  connecting n := HomologicalComplex.HomologySequence.δNatTransOfFamily
    ((ShortComplex.isShortExact A).ι ⋙ F.mapShortComplex) hF _ _ (hi n)
  exactLeft n S := ⟨(hF S).δ_comp _ _ (hi n), (hF S).homology_exact₁ _ _ (hi n)⟩
  exactMiddle n S := ⟨_, (hF S).homology_exact₂ (i n)⟩
  exactRight n S := ⟨(hF S).comp_δ _ _ (hi n), (hF S).homology_exact₃ _ _ (hi n)⟩
  epiZero S := by
    have hδ : (hF S).δ (i 0) j h₀ = 0 := (hzero S.obj.X₁).eq_of_tgt _ _
    exact (ShortComplex.exact_iff_epi _ hδ).mp ((hF S).homology_exact₃ _ _ h₀)

/-- The degree functor is the specified homology functor after the complex-valued functor. -/
@[simp]
theorem ofHomology_T (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i (n + 1)) (i n))
    (j : ι) (h₀ : c.Rel (i 0) j)
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) (n : ℕ) :
    (ofHomology A B F hF i hi j h₀ hzero).T n =
      F ⋙ HomologicalComplex.homologyFunctor B c (i n) := rfl

/-- Connecting components are the connecting maps of the image short exact sequence. -/
@[simp]
theorem ofHomology_connecting_app (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i (n + 1)) (i n))
    (j : ι) (h₀ : c.Rel (i 0) j)
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j))
    (n : ℕ) (S : ShortComplex.ShortExactSequences A) :
    ((ofHomology A B F hF i hi j h₀ hzero).connecting n).app S =
      (hF S).δ (i (n + 1)) (i n) (hi n) := rfl

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- Homology of a functorial family of complexes gives a cohomological δ-functor
for an index map along which the connecting morphisms increase degree. The
vanishing hypothesis supplies the degree-zero mono endpoint. -/
noncomputable def ofHomology (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i n) (i (n + 1)))
    (j : ι) (h₀ : c.Rel j (i 0))
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) :
    CohomologicalDeltaFunctor A B where
  T n := F ⋙ HomologicalComplex.homologyFunctor B c (i n)
  additive _ := inferInstance
  connecting n := HomologicalComplex.HomologySequence.δNatTransOfFamily
    ((ShortComplex.isShortExact A).ι ⋙ F.mapShortComplex) hF _ _ (hi n)
  exactLeft n S := ⟨(hF S).δ_comp _ _ (hi n), (hF S).homology_exact₁ _ _ (hi n)⟩
  exactMiddle n S := ⟨_, (hF S).homology_exact₂ (i n)⟩
  exactRight n S := ⟨(hF S).comp_δ _ _ (hi n), (hF S).homology_exact₃ _ _ (hi n)⟩
  monoZero S := by
    have hδ : (hF S).δ j (i 0) h₀ = 0 := (hzero S.obj.X₃).eq_of_src _ _
    exact (ShortComplex.exact_iff_mono _ hδ).mp ((hF S).homology_exact₁ _ _ h₀)

/-- The degree functor is the specified homology functor after the complex-valued functor. -/
@[simp]
theorem ofHomology_T (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i n) (i (n + 1)))
    (j : ι) (h₀ : c.Rel j (i 0))
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) (n : ℕ) :
    (ofHomology A B F hF i hi j h₀ hzero).T n =
      F ⋙ HomologicalComplex.homologyFunctor B c (i n) := rfl

/-- Connecting components are the connecting maps of the image short exact sequence. -/
@[simp]
theorem ofHomology_connecting_app (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i n) (i (n + 1)))
    (j : ι) (h₀ : c.Rel j (i 0))
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j))
    (n : ℕ) (S : ShortComplex.ShortExactSequences A) :
    ((ofHomology A B F hF i hi j h₀ hzero).connecting n).app S =
      (hF S).δ (i n) (i (n + 1)) (hi n) := rfl

end CohomologicalDeltaFunctor

end CategoryTheory
