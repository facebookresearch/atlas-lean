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
# Actual exactness of additive functors on all-projective coefficients

Every original short exact sequence splits by projectivity of its actual
third coefficient. Its actual mapped splitting proves exactness of any
additive functor and native finite-limit preservation follows.
-/

@[expose] public section
noncomputable section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [∀ X : C, Projective X] (F : C ⥤ D) [F.Additive]

/-- Every original short exact sequence retains a mapped native splitting. -/
lemma additive_map_shortExact_of_allProjective (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map F).ShortExact :=
  ((hS.splittingOfProjective).map F).shortExact

/-- Actual mapped splittings make every additive functor exact on this coefficient domain. -/
lemma additive_preservesFiniteLimits_of_allProjective : PreservesFiniteLimits F := by
  have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((F.exact_tfae).out 1 4).1 (additive_map_shortExact_of_allProjective F)
  exact h.1

end CategoryTheory
