/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source word images from fully checked finite representative prefix recurrences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact original C322 source word denoted by a literal finite matrix cache prefix. -/
noncomputable def y322Orthogonal3TCCacheSource (i : Fin 7253) : Y322Presentation :=
  y322LocalProgramValue y322TransportProgram (y322Orthogonal3TCCacheReference i)

/-- The source word of the base matrix cache entry is actually one. -/
theorem y322Orthogonal3TCCacheSource_zero_of_checked
    (checked : ∀ i : Fin 7253, y322Orthogonal3TCCacheCheckAt i.val) :
    y322Orthogonal3TCCacheSource 0 = 1 := by
  have hc := checked 0
  simp only [y322Orthogonal3TCCacheCheckAt,
    dite_eq_left (show (0 : ℕ) < 7253 by decide), Fin.val_zero, ite_true] at hc
  have hi : y322TransportProgram (y322Orthogonal3TCCacheReference 0) = .one := by
    apply y322Instruction_eq_of_raw_eq
    exact hc.2.1
  rw [y322Orthogonal3TCCacheSource, y322LocalProgramValue_eq, hi]
  rfl

/-- Each nonbase entry denotes its actual earlier source word times a generator. -/
theorem y322Orthogonal3TCCacheSource_step_of_checked
    (checked : ∀ i : Fin 7253, y322Orthogonal3TCCacheCheckAt i.val)
    (i : Fin 7253) (hi : i.val ≠ 0) :
    y322Orthogonal3TCCacheSource i =
      y322Orthogonal3TCCacheSource (y322Orthogonal3TCCacheParent i) *
        PresentedGroup.of (y322Orthogonal3TCCacheGenerator i) := by
  have hc := checked i
  simp only [y322Orthogonal3TCCacheCheckAt, dite_eq_left i.isLt, ite_eq_right hi] at hc
  let p := y322Orthogonal3TCCacheParent i
  let ref : Fin (y322Orthogonal3TCCacheReference i).val :=
    ⟨38540 + (y322Orthogonal3TCCacheNode p).val, by
      dsimp [y322Orthogonal3TCCacheReference, p]
      have hn := hc.2.1
      dsimp [p] at hn
      omega⟩
  have hj : y322TransportProgram (y322Orthogonal3TCCacheReference i) =
      .appendGenerator ref (y322Orthogonal3TCCacheGenerator i) := by
    apply y322Instruction_eq_of_raw_eq
    exact hc.2.2.1
  rw [y322Orthogonal3TCCacheSource, y322LocalProgramValue_eq, hj]
  rfl

/-- Every finite prefix matrix and inverse is the image of its actual original C322 word. -/
theorem y322Orthogonal3TCCacheSource_matrices_of_checked
    (checked : ∀ i : Fin 7253, y322Orthogonal3TCCacheCheckAt i.val) (i : Fin 7253) :
    (y322Orthogonal3Hom (y322Orthogonal3TCCacheSource i)).val =
        y322Orthogonal3TCCacheMatrix i ∧
      ((y322Orthogonal3Hom (y322Orthogonal3TCCacheSource i))⁻¹).val =
        y322Orthogonal3TCCacheInverse i := by
  induction i using (measure (fun i : Fin 7253 => i.val)).wf.induction with
  | h i ih =>
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i
      have hc := checked 0
      simp only [y322Orthogonal3TCCacheCheckAt,
        dite_eq_left (show (0 : ℕ) < 7253 by decide), Fin.val_zero, ite_true] at hc
      rw [y322Orthogonal3TCCacheSource_zero_of_checked checked, map_one]
      exact ⟨hc.2.2.1.symm, hc.2.2.2.symm⟩
    · have hc := checked i
      simp only [y322Orthogonal3TCCacheCheckAt, dite_eq_left i.isLt, ite_eq_right hi] at hc
      have hp := ih (y322Orthogonal3TCCacheParent i) hc.1
      rw [y322Orthogonal3TCCacheSource_step_of_checked checked i hi, map_mul,
        y322Orthogonal3Hom_generator]
      constructor
      · rw [Units.val_mul, hp.1, y322Orthogonal3Generator_matrix]
        exact hc.2.2.2.1.symm
      · rw [mul_inv_rev, Units.val_mul, hp.2]
        change y322Orthogonal3Reflection (y322Orthogonal3TCCacheGenerator i) *
          y322Orthogonal3TCCacheInverse (y322Orthogonal3TCCacheParent i) =
            y322Orthogonal3TCCacheInverse i
        exact hc.2.2.2.2.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
