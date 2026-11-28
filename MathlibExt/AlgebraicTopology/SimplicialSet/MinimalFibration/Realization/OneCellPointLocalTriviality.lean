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

/-!
# Local trivializations near points of a topological pushout

For `p : E ⟶ X₄` and a fixed fiber `F` in `TopCat.{u}`, point-local triviality means that a
point lies in an open subset `U` over which a pullback presentation of `p` is a product with
`F`. Trivializations restrict to subsets by pullback. A trivialization over the image of `r :
X₂ ⟶ X₄` therefore gives this property on any open neighborhood contained in that image.

For a pushout `IsPushout t l r b`, with `r` a closed embedding and `IsPullback e p₃ p b`, a
trivialization of `p₃` over `(Set.range l.hom)ᶜ` transports to the open complement `(Set.range
r.hom)ᶜ`. Every point of that complement is then point-locally trivial, with the restriction
pullbacks specified in the statements. A trivial pullback presentation over `U` also gives a
product presentation for any further pullback of the canonical projection over `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

namespace modelCategoryQuillen

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
variable {E E₃ : TopCat.{u}} {p : E ⟶ X₄} {p₃ : E₃ ⟶ X₃} {e : E₃ ⟶ E}

/-- For `p : E ⟶ X₄`, `F : TopCat.{u}`, and `pt : X₄`, point-local triviality is the existence of
a subset `U ⊆ X₄` such that `IsOpen U`, `pt ∈ U`, and `TrivialBundleWithFiberOver F p
(AlgebraicTopology.subspaceIncl U)` is nonempty. Such a presentation is a pullback of `p` over
`U` whose total space, with its projection, is a product of `U` and `F`. -/
def OneCellPointLocalTriviality (p : E ⟶ X₄) (F : TopCat.{u}) (pt : X₄) : Prop :=
  ∃ U : Set X₄, IsOpen U ∧ pt ∈ U ∧
    Nonempty (CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U))

/-- In `TopCat.{u}`, let `p : E ⟶ X₄`, `r : X₂ ⟶ X₄`, and `F : TopCat.{u}`. Suppose `h_old` is a
trivial pullback presentation of `p` with fiber `F` over `Set.range r.hom`. For `U : Set X₄`
and `h_sub : U ⊆ Set.range r.hom`, assume the pullback of `h_old.p'` along
`subspaceInclOfSubset h_sub` exists. Restricting along this inclusion gives a trivial pullback
presentation of `p` with fiber `F` over `U`. -/
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

/-- Let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a pushout in
`TopCat.{u}`, with `r` a closed embedding, and let `IsPullback e p₃ p b` relate `p₃ : E₃ ⟶ X₃`
to `p : E ⟶ X₄`. Suppose `h_new` trivializes `p₃` with fiber `F` over `(Set.range l.hom)ᶜ`.
For `h_sub : U ⊆ (Set.range r.hom)ᶜ`, assume the pullback of the transported presentation's
projection along `subspaceInclOfSubset h_sub` exists. Transport followed by restriction gives
a trivial pullback presentation of `p` with fiber `F` over `U`. -/
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

/-- In `TopCat.{u}`, let `IsPushout t l r b` have legs `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶
X₄`, and `b : X₃ ⟶ X₄`, with `r` a closed embedding. Suppose `IsPullback e p₃ p b` and a
presentation `h_new` trivializes `p₃` with fiber `F` over `(Set.range l.hom)ᶜ`. Let `pt ∈
(Set.range r.hom)ᶜ`, and assume the pullback of the transported projection along the inclusion
of this complement into itself exists. Then `OneCellPointLocalTriviality p F pt` holds,
witnessed by the open complement `(Set.range r.hom)ᶜ`. -/
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

/-- Let `p : E ⟶ X₄` and `r : X₂ ⟶ X₄` be morphisms in `TopCat.{u}`, and let `h_old` trivialize
the pullback of `p` over `Set.range r.hom` with fiber `F`. Suppose `U : Set X₄` is open, `pt ∈
U`, and `h_sub : U ⊆ Set.range r.hom`. If the pullback of `h_old.p'` along
`subspaceInclOfSubset h_sub` exists, then `OneCellPointLocalTriviality p F pt` holds,
witnessed by the restriction to `U`. -/
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

/-- In `TopCat.{u}`, let `p : E ⟶ X₄`, `U : Set X₄`, and let `h_over` trivialize a pullback
presentation of `p` over `U` with fixed fiber `F`. Assume the canonical pullback `Q = pullback
p (subspaceIncl U)` exists, with projection `Q ⟶ TopCat.of U`. For objects `P, B'`, maps `s :
P ⟶ Q`, `q : P ⟶ B'`, and `f : B' ⟶ TopCat.of U`, suppose their square with that projection is
a pullback. The induced datum `TrivialBundleWithFiber F q` exhibits `P`, with projections to
`B'` and `F`, as their product. -/
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
