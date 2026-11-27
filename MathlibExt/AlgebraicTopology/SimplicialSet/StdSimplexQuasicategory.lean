/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Standard simplices are quasicategories

This file contains the single global instance that every standard
simplex `Δ[n]` is a quasicategory, through the isomorphism
`Δ[n] ≅ nerve (ULift (Fin (n + 1)))` (`SSet.stdSimplex.isoNerve`)
and the fact that nerves of categories are quasicategories.

It is deliberately a standalone, low-level module: it imports only
Mathlib. In particular the proof below is the isomorphism-transport
argument specialized to `stdSimplex.isoNerve`, rather than an
application of any higher-level transport lemma, so that consumers
such as the (higher-level, path-object) slice file
[Slice.lean](Slice.lean) can import this instance without an
import cycle. The `Δ[n]` instance here subsumes the `Δ[0]` case;
this file is the single home for it, so that no second, overlapping
global instance for `Δ[0]` exists.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- Every standard simplex is a quasicategory: it is isomorphic to
the nerve of the linearly ordered category `ULift (Fin (n + 1))`,
and being a quasicategory (equivalently, the map to the terminal
object being an inner fibration) transports along that isomorphism.
This is the unique global instance for standard simplices; in
particular it covers `Δ[0]`. -/
instance (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) := by
  have hB : InnerFibration
      (terminal.from (nerve (ULift.{u} (Fin (n + 1))))) :=
    (quasicategory_iff_innerFibration _).1 inferInstance
  rw [quasicategory_iff_innerFibration]
  have e : Arrow.mk (terminal.from (Δ[n] : SSet.{u})) ≅
      Arrow.mk (terminal.from (nerve (ULift.{u} (Fin (n + 1))))) :=
    Arrow.isoMk (stdSimplex.isoNerve n) (Iso.refl _) (by
      simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
      exact terminal.hom_ext _ _)
  exact ⟨(innerFibrations.arrow_mk_iso_iff e).2 hB.mem⟩

end SSet
