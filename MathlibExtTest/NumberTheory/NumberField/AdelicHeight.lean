/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicHeight

@[expose] public section

open NumberField NumberField.AdelicHeight IsDedekindDomain

/-- The height of the identity is `1`. -/
example : adelicHeight ℚ 1 = 1 := adelicHeight_one ℚ

/-- The criterion applied to the identity map and the identity permutations of places. -/
example (F : Type*) [Field F] [NumberField F] (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    adelicHeight F (Matrix.GeneralLinearGroup.map (RingHom.id _) g) = adelicHeight F g :=
  adelicHeight_map_of_norm_eq (RingHom.id _) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) g

/-- The finite local height of a scalar matrix `c • 1` is `1`, whatever `c ≠ 0` is: the
determinant `c²` cancels the bottom row `(0, c)`. -/
example (c : ℚ) (hc : c ≠ 0) :
    finLocalHeight (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => c)
      (by simpa [Matrix.det_diagonal] using pow_ne_zero 2 hc)) = 1 := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  simp [finLocalHeight, rowMaxNorm, Matrix.det_fin_two, Matrix.diagonal]
  field_simp
