/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.P5Equivalences
public import Mathlib.Tactic

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.P5Equivalences`

* The retained implications `rp5_p5_p5a` and `rp5_p5a_p5b` for the constant model
  `μ ξ n S = ν R n S = 1/2`, which satisfies their hypotheses (`hglue`, `hcmp`); `rp5_P5a`,
  `rp5_P5b` and `P5` hold for it. The `P5b → P5` step and the combined equivalence were removed
  with `rp5_p5_equiv`: they needed the uniform-in-`α` hypothesis `hchain`.
* `rp5_p5b_p5_upper` for the same constant model.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.P5Equivalences

/-- The constant set function `1/2`. -/
noncomputable def half : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ := fun _ _ => 1 / 2

theorem half_P5a : rp5_P5a half := ⟨1 / 2, by norm_num, fun _ => le_rfl⟩

theorem half_P5b : rp5_P5b (fun _ => half) := fun _ _ => ⟨1 / 2, by norm_num, fun _ => le_rfl⟩

theorem half_P5 : P5 half := fun _ _ => ⟨1 / 2, by norm_num, fun _ => le_rfl⟩

theorem half_p5_to_p5a : P5 half → rp5_P5a half :=
  rp5_p5_p5a (fun _ => by simp only [half]; norm_num)

theorem half_p5a_to_p5b : rp5_P5a half → rp5_P5b (fun _ => half) :=
  rp5_p5a_p5b (fun _ _ => le_rfl)

example : rp5_P5a half := half_p5_to_p5a half_P5
example : rp5_P5b (fun _ => half) := half_p5a_to_p5b half_P5a

example : ∀ n : ℕ, half n (boxCrossingEvent 2 n) ≤ 1 - 1 / 2 :=
  rp5_p5b_p5_upper (compl := half) (by norm_num) (fun _ => by simp only [half]; norm_num)
    (fun _ => le_rfl)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.P5Equivalences
