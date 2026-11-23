/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.Relations

/-! # Non-vacuity and universe probes for the relational carrier -/

open Cslib.Languages.LambdaCalculus.SystemF

example : (Model.app (Model.atom 0) (Model.atom 1)).val =
    Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.app
      (.fvar 0) (.fvar 1) := rfl

example (x : Model) : (Rel.betaClass x).holds x x :=
  ⟨BetaEq.refl x, BetaEq.refl x⟩

example (f g : Model) : ¬ Rel.empty.holds f g := fun h => h

-- A nonempty input relation and empty output reject every function pair.
example (f g : Model) : ¬ (Rel.arrow Rel.total Rel.empty).holds f g := by
  intro h
  exact h (Model.atom 0) (Model.atom 1) trivial

-- The universal helper accepts an index above Model/Rel's universe.
example (f g : Model) :
    (Rel.universal (fun _ : Type => Rel.total)).holds f g := fun _ => trivial
