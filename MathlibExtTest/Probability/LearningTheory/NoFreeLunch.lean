/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.NoFreeLunch

@[expose] public section

/-- Boundary check: with domain `Fin 2`, one sample point
`0`, and the constant-`true` hypothesis, the total number of
errors over all four targets is `(2 - 1) * 2 ^ (2 - 1) = 2`. -/
example : (∑ f : Fin 2 → Bool,
      errCount (fun _ : Fin 1 => (0 : Fin 2)) f (fun _ => true)) = 2 := by
  have h := nfl_average (X := Fin 2) (m := 1)
    (fun _ => (fun _ => true)) (fun _ : Fin 1 => (0 : Fin 2))
    (fun a b _ => Subsingleton.elim a b)
  simpa using h
