/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Exact additive functors from an all-projective abelian category

Let C,D be abelian categories and suppose every object of C is projective.
Every short exact sequence in C splits. An additive functor F:C → D
preserves its splitting and therefore maps it to a short exact sequence.
Consequently every such additive functor preserves finite limits.
-/

@[expose] public section
noncomputable section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [∀ X : C, Projective X] (F : C ⥤ D) [F.Additive]

/-- Let C,D be abelian, suppose every object of C is projective, and let
F:C → D be additive. For each short exact sequence S in C, its
termwise image under F is short exact. -/
lemma additive_map_shortExact_of_allProjective (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map F).ShortExact :=
  ((hS.splittingOfProjective).map F).shortExact

/-- For abelian categories C,D with every object of C projective, every
additive functor F:C → D preserves finite limits. -/
lemma additive_preservesFiniteLimits_of_allProjective : PreservesFiniteLimits F := by
  have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((F.exact_tfae).out 1 4).1 (additive_map_shortExact_of_allProjective F)
  exact h.1

end CategoryTheory
