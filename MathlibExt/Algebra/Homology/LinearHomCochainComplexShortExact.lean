/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

/-!
# Degreewise split short exact sequences of linear Hom cochains

Let R be a ring and C an abelian R-linear category, with independent scalar, object and morphism
universes. A short complex of nonnegative chain complexes K₁→K₂→K₃ becomes the reversed Hom
cochain short complex Hom_C(K₃,M)→Hom_C(K₂,M)→Hom_C(K₁,M), by precomposition, for any M∈C.

If the chain-complex sequence is short exact and its first map K₁,n→K₂,n is split monic in every
degree n, the Hom cochain sequence is short exact. Each degree inherits the splitting of the
reversed Hom sequence; the termwise retractions need not assemble into a chain retraction.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace HomologicalComplex

universe w v u

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For a short complex S=(K₁ --a→ K₂ --b→ K₃) of shape down ℕ
and M∈C, this is the cochain short complex Hom_C(K₃,M) --b*→ Hom_C(K₂,M) --a*→ Hom_C(K₁,M). Its
degree-n terms are Hom_C(Kᵢ,n,M), with the R-module structures from C's linearity. -/
noncomputable abbrev linearHomCochainShortComplex
    (S : ShortComplex (ChainComplex C ℕ)) (M : C) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  S.op.map (linearHomCochainComplexFunctor R C M)

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. Let S=(0→K₁ --a→ K₂ --b→ K₃→0) be short exact in nonnegative
chain complexes, and assume a_n is split monic for every n∈ℕ. For arbitrary M∈C,
0→Hom_C(K₃,M)→Hom_C(K₂,M)→Hom_C(K₁,M)→0 is short exact as a sequence of R-module-valued cochain
complexes. The proof uses the degreewise split short exact rows, with no target injectivity
hypothesis. -/
theorem linearHomCochainShortComplex_shortExact_of_degreewise_splitMono
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (hsplit : ∀ n, SplitMono ((S.map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).f)) (M : C) :
    (linearHomCochainShortComplex R S M).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let S_n : ShortComplex C :=
    S.map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  have hS_n : S_n.ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hsplit_n : SplitMono S_n.f := hsplit n
  let splitting : S_n.Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction S_n hS_n.exact
      hsplit_n.retraction hsplit_n.id hS_n.epi_g
  let F : Functor Cᵒᵖ (ModuleCat.{v} R) := (linearYoneda R C).obj M
  have hMapped : ((S_n.op).map F).ShortExact :=
    (splitting.op.map F).shortExact
  have hEq :
      ((linearHomCochainShortComplex R S M).map
        (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℕ) n)) =
        ((S_n.op).map F) := by
    dsimp [linearHomCochainShortComplex, linearHomCochainComplexFunctor, S_n, F]
    rfl
  rw [hEq]
  exact hMapped

end HomologicalComplex

end
