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
public import MathlibExt.Topology.Category.TopCat.TrivialBundlePushoutComplement
public import MathlibExt.Topology.Category.TopCat.PushoutComplement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Fixed-fiber local triviality and restriction to open subsets

A map is locally trivial at a point when an open neighborhood has a pullback product
presentation with the chosen fiber. Such presentations restrict along subset inclusions.
Pushout complements transport local trivializations under a closed-range hypothesis.
All categorical pullbacks used here exist in TopCat.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- An open neighborhood of the point admits a pullback product presentation of `p`. -/
def IsLocallyTrivialAt (p : E ⟶ B) (F : TopCat.{u}) (pt : B) : Prop :=
  ∃ U : Set B, IsOpen U ∧ pt ∈ U ∧
    Nonempty (CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p (subspaceIncl U))

/-- Restrict a fixed-fiber pullback presentation over a subset to any smaller subset. -/
noncomputable def trivialBundleWithFiberOverSubset (F : TopCat.{u})
    {U V : Set B}
    (h : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p (subspaceIncl V))
    (hUV : U ⊆ V) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p (subspaceIncl U) :=
  (subspaceInclOfSubset_comp hUV) ▸
    h.baseChange (IsPullback.of_hasPullback h.p' (subspaceInclOfSubset hUV))

/-- A presentation over a larger subset gives local triviality at every point of an open
smaller subset. No existence assumption for the restriction pullback is necessary. -/
theorem isLocallyTrivialAt_of_open_subset (F : TopCat.{u})
    {U V : Set B}
    (h : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p (subspaceIncl V))
    (hU : IsOpen U) (pt : B) (hpt : pt ∈ U) (hUV : U ⊆ V) :
    IsLocallyTrivialAt p F pt :=
  ⟨U, hU, hpt, ⟨trivialBundleWithFiberOverSubset F h hUV⟩⟩

section Pushout

variable {X₁ X₂ X₃ X₄ E E₃ : TopCat.{u}}
variable {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
variable {p : E ⟶ X₄} {p₃ : E₃ ⟶ X₃} {e : E₃ ⟶ E}

/-- Transport a presentation across a pushout complement, then restrict to a smaller subset.
Only the range of `r` must be closed; neither injectivity nor a closed embedding is needed. -/
noncomputable def trivialBundleWithFiberOverSubsetOfPushoutComplement
    (F : TopCat.{u}) (sqBase : IsPushout t l r b) (hr : IsClosed (Set.range r.hom))
    (sqQ : IsPullback e p₃ p b)
    (h : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (subspaceIncl ((Set.range l.hom)ᶜ)))
    {U : Set X₄} (hU : U ⊆ (Set.range r.hom)ᶜ) :
    CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p (subspaceIncl U) :=
  trivialBundleWithFiberOverSubset F
    (trivialBundleWithFiberOverPushoutComplement sqBase hr sqQ F h) hU

/-- Every point of the complement of a closed pushout-leg range admits the transported
local trivialization. All required pullbacks are supplied by TopCat. -/
theorem isLocallyTrivialAt_of_isPushout_compl_range
    (F : TopCat.{u}) (sqBase : IsPushout t l r b) (hr : IsClosed (Set.range r.hom))
    (sqQ : IsPullback e p₃ p b)
    (h : CategoryTheory.MorphismProperty.TrivialBundleWithFiberOver F p₃
      (subspaceIncl ((Set.range l.hom)ᶜ)))
    (pt : X₄) (hpt : pt ∈ (Set.range r.hom)ᶜ) : IsLocallyTrivialAt p F pt :=
  ⟨(Set.range r.hom)ᶜ, hr.isOpen_compl, hpt,
    ⟨trivialBundleWithFiberOverPushoutComplement sqBase hr sqQ F h⟩⟩

end Pushout

end TopCat
