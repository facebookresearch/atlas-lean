/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CountabilityMono

/-! Public consumers for inclusions, actual pullback projections, full
simplices and an empty subcomplex, in the original value universe. -/

public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CountabilityMono

/-- The actual inclusion of every subcomplex transfers countability. -/
theorem subcomplex {Y : SSet.{u}} [Countable Y.N] (V : Y.Subcomplex) :
    Countable V.toSSet.N :=
  SSet.countable_N_of_mono V.ι

/-- Only the original monomorphism and countability of the pullback target
are needed; the other span map and ambient objects are arbitrary. -/
theorem pullbackSource {X Y V : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (j : V ⟶ Y) [Countable V.N] : Countable (pullback i j).N :=
  SSet.countable_N_of_mono (pullback.snd i j)

/-- The same source has countably many simplices in all degrees together. -/
theorem allDegrees {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] [Countable Y.N] :
    Countable (Σ n : ℕ, X _⦋n⦌) := by
  have : Countable X.N := SSet.countable_N_of_mono i
  exact SSet.countable_sigma_obj_of_countable_N X

/-- The inclusion and counting result also apply to the empty subcomplex. -/
theorem emptySubcomplex (Y : SSet.{u}) [Countable Y.N] :
    Countable (⊥ : Y.Subcomplex).toSSet.N :=
  SSet.countable_N_of_mono (⊥ : Y.Subcomplex).ι

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CountabilityMono
