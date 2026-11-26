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
# δ-functors from families of complexes

Let `A` be preadditive, `B` abelian, and `F : A → HomologicalComplex B c`
additive and preserving short exact sequences. Homology along a natural-number
path in the complex shape gives a homological or cohomological δ-functor
according to the direction of the path. Vanishing at the adjacent index
to degree zero supplies the endpoint condition of the long exact sequence.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂ u₃

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
variable (B : Type u₂) [Category.{v₂} B] [Abelian B]
variable {ι : Type u₃} {c : ComplexShape ι}

namespace HomologicalDeltaFunctor

/-- Let `A` be preadditive, `B` abelian, and `F : A → HomologicalComplex B c`
additive and preserving short exact sequences. If `i(n+1) → i(n)`
are shape arrows, `i(0) → j` is a shape arrow, and `H_j(F(X))=0`
for every `X`, the functors `X ↦ H_i(n)(F(X))` form a homological
δ-functor `A → B`. -/
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

/-- For the additive short-exact-sequence-preserving family
`F : A → HomologicalComplex B c`, with `A` preadditive, `B` abelian,
a decreasing shape path `i(n+1) → i(n)` and vanishing at the adjacent
index `j`, the degree-`n` functor of the resulting homological
δ-functor is `F ⋙ homologyFunctor B c (i n)`. -/
@[simp]
theorem ofHomology_T (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i (n + 1)) (i n))
    (j : ι) (h₀ : c.Rel (i 0) j)
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) (n : ℕ) :
    (ofHomology A B F hF i hi j h₀ hzero).T n =
      F ⋙ HomologicalComplex.homologyFunctor B c (i n) := rfl

/-- For a homological δ-functor constructed from additive
`F : A → HomologicalComplex B c`, with `A` preadditive, `B` abelian,
the specified decreasing path and adjacent vanishing, its connecting
component on a short exact sequence `S` is the native boundary
`H_i(n+1)(F(S.X₃)) → H_i(n)(F(S.X₁))` of the mapped sequence. -/
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

/-- Let `A` be preadditive, `B` abelian, and `F : A → HomologicalComplex B c`
additive and preserving short exact sequences. If `i(n) → i(n+1)`
are shape arrows, `j → i(0)` is a shape arrow, and `H_j(F(X))=0`
for every `X`, the functors `X ↦ H_i(n)(F(X))` form a cohomological
δ-functor `A → B`. -/
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

/-- For an additive short-exact-sequence-preserving family
`F : A → HomologicalComplex B c`, with `A` preadditive, `B` abelian,
an increasing shape path `i(n) → i(n+1)` and vanishing at its
adjacent index `j`, the degree-`n` cohomological functor is
`F ⋙ homologyFunctor B c (i n)`. -/
@[simp]
theorem ofHomology_T (F : A ⥤ HomologicalComplex B c) [F.Additive]
    (hF : ∀ S : ShortComplex.ShortExactSequences A, (S.obj.map F).ShortExact)
    (i : ℕ → ι) (hi : ∀ n, c.Rel (i n) (i (n + 1)))
    (j : ι) (h₀ : c.Rel j (i 0))
    (hzero : ∀ X : A, IsZero ((F.obj X).homology j)) (n : ℕ) :
    (ofHomology A B F hF i hi j h₀ hzero).T n =
      F ⋙ HomologicalComplex.homologyFunctor B c (i n) := rfl

/-- For a cohomological δ-functor constructed from additive
`F : A → HomologicalComplex B c`, with `A` preadditive, `B` abelian,
the specified increasing path and adjacent vanishing, its connecting
component on a short exact sequence `S` is the boundary
`H_i(n)(F(S.X₃)) → H_i(n+1)(F(S.X₁))` of the mapped sequence. -/
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
