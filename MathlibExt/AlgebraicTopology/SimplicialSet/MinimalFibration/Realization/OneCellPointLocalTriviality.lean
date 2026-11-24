/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.TrivialBundleWithFiberOver
public import MathlibExt.CategoryTheory.TrivialBundleWithFiber
public import MathlibExt.Topology.Category.TopCat.Subspace
public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellComplementTrivialBundleOver
public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellOpenComplement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Point-local triviality for one-cell induction

Purpose: predicate for finite-base local induction plus old-range/complement
restriction and canonical-fiber adapters around a one-cell pushout.
Given old-range data over `range r` and new-cell data over `(range l)ᶜ`,
produce open neighborhoods with fixed-fiber data, without assembling
boundary points or global charts.

Route: predicate as open neighborhood with `Nonempty` over-presentation;
old-range restriction by `baseChange` with `subspaceInclOfSubset_comp`;
complement restriction by `trivialBundleWithFiberOver_oneCellComplement`
then base change; complement constructor with `isOpen_oneCellOpenComplement`;
conditional old-range constructor as thin wrapper; canonical fiber by
`toCanonical` then `pullback`.

Nonclaims: no boundary-point assembler, no binary gluing, no global or
finite-base chart, no collar or descent data, no varying-fiber or monodromy
claim, no fibration, weak-equivalence, realization, or model-instance result,
and no KQ3 content.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

namespace modelCategoryQuillen

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
variable {E E₃ : TopCat.{u}} {p : E ⟶ X₄} {p₃ : E₃ ⟶ X₃} {e : E₃ ⟶ E}

/-- Point-local fixed-fiber neighborhood predicate. -/
def OneCellPointLocalTriviality (p : E ⟶ X₄) (F : TopCat.{u}) (pt : X₄) : Prop :=
  ∃ U : Set X₄, IsOpen U ∧ pt ∈ U ∧
    Nonempty (CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U))

/-- Old-range restriction to `U` by base change. -/
noncomputable def oneCellPointLocal_oldRange_of_subset
    (F : TopCat.{u})
    (h_old : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl (Set.range r.hom)))
    (U : Set X₄) (h_sub : U ⊆ Set.range r.hom)
    [Limits.HasPullback h_old.p'
      (AlgebraicTopology.subspaceInclOfSubset h_sub)] :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U) :=
  (AlgebraicTopology.subspaceInclOfSubset_comp h_sub) ▸
    h_old.baseChange
      (IsPullback.of_hasPullback h_old.p'
        (AlgebraicTopology.subspaceInclOfSubset h_sub))

/-- Complement restriction to `U` by transport then base change. -/
noncomputable def oneCellPointLocal_complement_of_subset
    (F : TopCat.{u})
    (sqBase : IsPushout t l r b)
    (hr : IsClosedEmbedding r.hom)
    (sqQ : IsPullback e p₃ p b)
    (h_new : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (AlgebraicTopology.subspaceIncl ((Set.range l.hom)ᶜ)))
    (U : Set X₄) (h_sub : U ⊆ (Set.range r.hom)ᶜ)
    [Limits.HasPullback
      (trivialBundleWithFiberOver_oneCellComplement sqBase hr sqQ F h_new).p'
      (AlgebraicTopology.subspaceInclOfSubset h_sub)] :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U) :=
  (AlgebraicTopology.subspaceInclOfSubset_comp h_sub) ▸
    (trivialBundleWithFiberOver_oneCellComplement sqBase hr sqQ F h_new).baseChange
      (IsPullback.of_hasPullback
        (trivialBundleWithFiberOver_oneCellComplement sqBase hr sqQ F h_new).p'
        (AlgebraicTopology.subspaceInclOfSubset h_sub))

/-- Complement points satisfy the predicate. -/
theorem oneCellPointLocal_of_complement
    (F : TopCat.{u})
    (sqBase : IsPushout t l r b)
    (hr : IsClosedEmbedding r.hom)
    (sqQ : IsPullback e p₃ p b)
    (h_new : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (AlgebraicTopology.subspaceIncl ((Set.range l.hom)ᶜ)))
    (pt : X₄) (hpt : pt ∈ (Set.range r.hom)ᶜ)
    [Limits.HasPullback
      (trivialBundleWithFiberOver_oneCellComplement sqBase hr sqQ F h_new).p'
      (AlgebraicTopology.subspaceInclOfSubset (fun _x hx => hx))] :
    OneCellPointLocalTriviality p F pt :=
  ⟨(Set.range r.hom)ᶜ, isOpen_oneCellOpenComplement hr, hpt,
    ⟨oneCellPointLocal_complement_of_subset F sqBase hr sqQ h_new
      ((Set.range r.hom)ᶜ) (fun _x hx => hx)⟩⟩

/-- Conditional old-range points satisfy the predicate. -/
theorem oneCellPointLocal_of_oldRange_subset
    (F : TopCat.{u})
    (h_old : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl (Set.range r.hom)))
    (U : Set X₄) (h_open : IsOpen U) (pt : X₄) (hpt : pt ∈ U)
    (h_sub : U ⊆ Set.range r.hom)
    [Limits.HasPullback h_old.p'
      (AlgebraicTopology.subspaceInclOfSubset h_sub)] :
    OneCellPointLocalTriviality p F pt :=
  ⟨U, h_open, hpt, ⟨oneCellPointLocal_oldRange_of_subset F h_old U h_sub⟩⟩

/-- Canonical fiber then local restriction. -/
noncomputable def oneCellPointLocal_toCanonical_fiber
    (F : TopCat.{u})
    (U : Set X₄)
    (h_over : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U))
    [Limits.HasPullback p (AlgebraicTopology.subspaceIncl U)]
    {P B' : TopCat.{u}}
    {s : P ⟶ Limits.pullback p (AlgebraicTopology.subspaceIncl U)}
    {q : P ⟶ B'} {f : B' ⟶ TopCat.of U}
    (sq : IsPullback s q
      (Limits.pullback.snd p (AlgebraicTopology.subspaceIncl U)) f) :
    CategoryTheory.TrivialBundleWithFiber F q :=
  (h_over.toCanonical).pullback sq

end modelCategoryQuillen

end TopCat
