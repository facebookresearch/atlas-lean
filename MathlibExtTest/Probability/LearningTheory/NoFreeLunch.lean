/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.NoFreeLunch

/-! # Tests for the no-free-lunch averaging and tail bounds

All checks use the domain `Fin 2`, the single sample point `0` and the learner that always
outputs the constant-`true` hypothesis. The definitions are evaluated directly by `decide`,
independently of the theorems: only an error at the unseen point `1` counts, the total over the
four targets is `2`, and exactly two targets make the learner err. `nfl_average` and `nfl_tail`
are then instantiated on the same case.
-/

@[expose] public section

/-! ### Definitions -/

/-- `sampleOf` labels the sample point `0` with the target. -/
example (f : Fin 2 → Bool) :
    sampleOf (fun _ : Fin 1 => (0 : Fin 2)) f = fun _ => ((0 : Fin 2), f 0) := rfl

/-- The target that is `true` only at `0` disagrees with the constant-`true` hypothesis at the
unseen point `1`: one error. -/
example : errCount (fun _ : Fin 1 => (0 : Fin 2)) (fun t => t = 0) (fun _ => true) = 1 := by
  decide

/-- The target that is `true` only at `1` disagrees with it at the sample point `0`, which is
not counted: no error. -/
example : errCount (fun _ : Fin 1 => (0 : Fin 2)) (fun t => t = 1) (fun _ => true) = 0 := by
  decide

/-- Direct evaluation of the total number of errors over all four targets: `2`. -/
example : (∑ f : Fin 2 → Bool,
      errCount (fun _ : Fin 1 => (0 : Fin 2)) f (fun _ => true)) = 2 := by
  decide

/-- Direct evaluation: exactly two of the four targets (those with `f 1 = false`) make the
learner err, on one of the two points. -/
example : (Finset.univ.filter (fun f : Fin 2 → Bool =>
      errCount (fun _ : Fin 1 => (0 : Fin 2)) f (fun _ => true) = 1)).card = 2 := by
  decide

/-! ### Theorems on the same case -/

/-- `nfl_average`: the total number of errors over all four targets is
`(2 - 1) * 2 ^ (2 - 1) = 2`, matching the direct evaluation above. -/
example : (∑ f : Fin 2 → Bool,
      errCount (fun _ : Fin 1 => (0 : Fin 2)) f (fun _ => true)) = 2 := by
  have h := nfl_average (X := Fin 2) (m := 1)
    (fun _ => (fun _ => true)) (fun _ : Fin 1 => (0 : Fin 2))
    (fun a b _ => Subsingleton.elim a b)
  simpa using h

/-- `nfl_tail` with `card (Fin 2) = 2 * 1`: at least `4/7` of the four targets make the learner
err on more than `1/8` of the domain. The direct count above is `2`. -/
example : ((Finset.univ.filter (fun f : Fin 2 → Bool =>
      (1 / 8 : ℝ) < (errCount (fun _ : Fin 1 => (0 : Fin 2)) f (fun _ => true) : ℝ)
        / (Fintype.card (Fin 2) : ℝ))).card : ℝ) ≥ (1 / 7) * 2 ^ (Fintype.card (Fin 2)) :=
  nfl_tail (fun _ => fun _ => true) (fun _ : Fin 1 => (0 : Fin 2))
    (fun a b _ => Subsingleton.elim a b) (by simp) (by norm_num)
