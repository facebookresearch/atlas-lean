/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.P5Equivalences
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.P5Equivalences`

* All four components of `rp5_p5_equiv` for the constant model `μ ξ n S = ν R n S = 1/2`, which
  satisfies every hypothesis (`hcmp`, `hglue`, `hchain`, `htwo`); `rp5_P5a`, `rp5_P5b` and `P5`
  hold for it.
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

theorem half_htwo : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (_ : Unit) (n : ℕ),
    c ≤ half n (boxCrossingEvent α n) ∧ half n (boxCrossingEvent α n) ≤ 1 - c :=
  fun _ _ => ⟨1 / 2, by norm_num, fun _ _ => by simp only [half]; norm_num⟩

theorem half_equiv :
    (P5 half ↔ rp5_P5a half) ∧ (rp5_P5a half → rp5_P5b (fun _ => half)) ∧
      (rp5_P5b (fun _ => half) → P5 half) ∧ (P5 half ↔ P5c (fun (_ : Unit) => half)) :=
  rp5_p5_equiv (Ξ := Unit) (μ := fun _ => half) (ν := fun _ => half) ()
    (fun _ _ => le_rfl) (fun _ => by simp only [half]; norm_num) (fun _ _ => le_rfl) half_htwo

example : P5 half ↔ rp5_P5a half := half_equiv.1
example : rp5_P5b (fun _ => half) := half_equiv.2.1 half_P5a
example : P5 half := half_equiv.2.2.1 half_P5b
example : P5c (fun (_ : Unit) => half) := half_equiv.2.2.2.mp half_P5

example : ∀ n : ℕ, half n (boxCrossingEvent 2 n) ≤ 1 - 1 / 2 :=
  rp5_p5b_p5_upper (compl := half) (by norm_num) (fun _ => by simp only [half]; norm_num)
    (fun _ => le_rfl)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.P5Equivalences
