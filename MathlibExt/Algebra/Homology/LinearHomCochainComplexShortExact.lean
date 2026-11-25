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

@[expose] public section

noncomputable section

open CategoryTheory

namespace HomologicalComplex

universe w v u

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Apply the contravariant linear-Hom cochain functor to a short complex of
chain complexes. -/
noncomputable abbrev linearHomCochainShortComplex
    (S : ShortComplex (ChainComplex C ℕ)) (M : C) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  S.op.map (linearHomCochainComplexFunctor R C M)

/-- Applying `Hom_R(-, M)` to a short exact sequence of chain complexes remains
short exact when the first map is split mono in every degree. -/
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
