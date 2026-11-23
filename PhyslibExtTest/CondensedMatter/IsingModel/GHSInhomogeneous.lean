/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.GHSInhomogeneous

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.GHSInhomogeneous`

On the triangle `⊤ : SimpleGraph (Fin 3)` with inhomogeneous couplings `K` and fields `h_x`:
* `ghsi_ursell_nonpos` with couplings `K = 1/2` on every pair and fields `h = (0, 1, 2)`, for the
  triple `(o, x, y) = (0, 1, 2)` and for the repeated triple `(0, 1, 1)`;
* `ghsi_magnetization_fieldLine_concaveOn` along the field line `h + t·d` with `d = (0, 1, 1)`;
  the concavity is used as the midpoint inequality `(m(0) + m(1)) / 2 ≤ m(1/2)`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.GHSInhomogeneous

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Sharpness

/-- The triangle, the complete graph on three vertices. -/
abbrev triangle : SimpleGraph (Fin 3) := ⊤

/-- An inhomogeneous nonnegative field: `h_x = x`. -/
def field : Fin 3 → ℝ := fun x => (x : ℝ)

lemma field_nonneg (x : Fin 3) : 0 ≤ field x := Nat.cast_nonneg _

/-- The direction `(0, 1, 1)`: increase the field away from the site `0`. -/
def dir : Fin 3 → ℝ := fun x => if x = 0 then 0 else 1

lemma dir_nonneg (x : Fin 3) : 0 ≤ dir x := by unfold dir; split_ifs <;> norm_num

-- GHS for the triple `(0, 1, 2)` with couplings `1/2` and fields `(0, 1, 2)`.
example :
    expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 0 * (spin s 1 * spin s 2)) -
          expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 0) *
            expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 1 * spin s 2) -
          expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 0 * spin s 1) *
            expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 2) -
          expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 0 * spin s 2) *
            expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 1) +
          2 * expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 0) *
            expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 1) *
            expJ triangle.edgeFinset (fun _ => 1 / 2) field (fun s => spin s 2) ≤ 0 :=
  ghsi_ursell_nonpos triangle (fun _ => 1 / 2) field (fun _ => by norm_num) field_nonneg 0 1 2
    (by decide)

-- GHS also covers a repeated site, `(o, x, y) = (0, 1, 1)`.
example :
    expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 0 * (spin s 1 * spin s 1)) -
          expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 0) *
            expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 1 * spin s 1) -
          expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 0 * spin s 1) *
            expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 1) -
          expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 0 * spin s 1) *
            expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 1) +
          2 * expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 0) *
            expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 1) *
            expJ triangle.edgeFinset (fun _ => 1) field (fun s => spin s 1) ≤ 0 :=
  ghsi_ursell_nonpos triangle (fun _ => 1) field (fun _ => zero_le_one) field_nonneg 0 1 1
    (by decide)

-- GHS concavity along `h + t·d`, used at the midpoint of `[0, 1]`.
example :
    (expJ triangle.edgeFinset (fun _ => 1) (ghsiFieldLine field dir 0) (fun s => spin s 0)
        + expJ triangle.edgeFinset (fun _ => 1) (ghsiFieldLine field dir 1) (fun s => spin s 0)) / 2
      ≤ expJ triangle.edgeFinset (fun _ => 1) (ghsiFieldLine field dir (1 / 2))
          (fun s => spin s 0) := by
  have hc := ghsi_magnetization_fieldLine_concaveOn triangle (fun _ => 1) field dir
    (fun _ => zero_le_one) field_nonneg dir_nonneg 0 (by simp [dir])
  have := hc.2 (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl) (show (1 : ℝ) ∈ Set.Ici 0 from zero_le_one)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at this
  rw [show (1 / 2 : ℝ) * 0 + 1 / 2 * 1 = 1 / 2 by norm_num] at this
  linarith

end PhyslibExtTest.CondensedMatter.IsingModel.GHSInhomogeneous
