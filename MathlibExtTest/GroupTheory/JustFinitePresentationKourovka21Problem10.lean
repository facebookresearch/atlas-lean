/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.ZMod.Basic
import MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10

namespace MathlibExtTest.JustFinitePresentationKourovka21Problem10

open MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10Wanted

-- The trivial group is included, with no nontriviality assumption.
example : ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃* PUnit.{1}) ∧
    ∀ r ∈ R, Infinite (PresentedGroup (R.erase r : Set (FreeGroup (Fin n)))) :=
  finiteGroupHasJustFinitePresentation_holds PUnit

-- The Klein four group is a noncyclic instance of both conclusions.
example : ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
    ∀ r ∈ R, Infinite (PresentedGroup (R.erase r : Set (FreeGroup (Fin n)))) :=
  finiteGroupHasJustFinitePresentation_holds (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

end MathlibExtTest.JustFinitePresentationKourovka21Problem10
