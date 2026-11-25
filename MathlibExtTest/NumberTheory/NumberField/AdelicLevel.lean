/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicLevel

@[expose] public section

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace AdelicLevelTest

/-- The component at an infinite place reads off the entries at that place. -/
example (w : InfinitePlace ℚ) (g : GL (Fin 2) (InfiniteAdeleRing ℚ)) (i j : Fin 2) :
    (archComponent ℚ w g : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w :=
  archComponent_apply ℚ w g i j

/-- At the image of the rational matrix `!![2, 1; 0, 1]`, the component at an infinite place is
that matrix again: the trivial map, the transpose or the inverse would change it. -/
example (w : InfinitePlace ℚ) :
    (archComponent ℚ w (Matrix.GeneralLinearGroup.map (algebraMap ℚ (InfiniteAdeleRing ℚ))
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 1; 0, 1] (by simp [Matrix.det_fin_two]))) :
      Matrix (Fin 2) (Fin 2) w.Completion) = !![2, 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archComponent, archEval_apply] <;> rfl

/-- Away from the zero ideal, the local bound is `exp (-n)` for the multiplicity `n`: at the unit
ideal every multiplicity is `0`. -/
example (v : HeightOneSpectrum (𝓞 ℚ)) : idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) v = 1 := by
  rw [idealBound_of_ne_bot top_ne_bot, ← Ideal.one_eq_top, Associates.mk_one,
    Associates.factors_one, Associates.count_zero (Associates.irreducible_mk.mpr v.irreducible)]
  simp

/-- At the prime of a height-one prime `v` itself, the local bound at `v` is `exp (-1)`. -/
example (v : HeightOneSpectrum (𝓞 ℚ)) : idealBound (𝓞 ℚ) v.asIdeal v = WithZero.exp (-1) := by
  rw [idealBound_of_ne_bot v.ne_bot,
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible)]
  rfl

/-- The balls are closed under subtraction and grow with the ideal: `(4) ≤ (2)`. -/
example {x y : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {4}))
    (hy : y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {4})) :
    x - y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {2}) :=
  idealBall_mono (by simp) (Ideal.span_singleton_le_span_singleton.mpr ⟨2, by norm_num⟩)
    (sub_mem_idealBall hx hy)

/-- Negation stays in the ball. -/
example {N : Ideal (𝓞 ℚ)} {x : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ idealBall (𝓞 ℚ) ℚ N) :
    -x ∈ idealBall (𝓞 ℚ) ℚ N :=
  neg_mem_idealBall hx

end AdelicLevelTest
