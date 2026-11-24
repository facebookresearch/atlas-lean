/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_CubicInduction_PrincipalSeries2.lean`
and
`Theorems/Thm_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_
and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell.CubicInduction

section PrincipalSeries2

variable (v : HeightOneSpectrum (𝓞 ℚ))

public abbrev LocalGL2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

public def rightTranslate2 (g : LocalGL2 v) : Module.End ℂ (LocalGL2 v → ℂ) where
  toFun f := fun h => f (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem rightTranslate2_apply (g : LocalGL2 v) (f : LocalGL2 v → ℂ) (h : LocalGL2 v) :
    rightTranslate2 v g f h = f (h * g) :=
  rfl

public theorem rightTranslate2_mul (g g' : LocalGL2 v) :
    rightTranslate2 v (g * g') = rightTranslate2 v g * rightTranslate2 v g' := by
  ext f h
  simp [rightTranslate2_apply, mul_assoc]

public def diagonal2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : LocalGL2 v where
  val := diagonal fun i => (a i : v.adicCompletion ℚ)
  inv := diagonal fun i => ((a i)⁻¹ : (v.adicCompletion ℚ)ˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp only [Units.mul_inv, diagonal_one]
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp only [Units.inv_mul, diagonal_one]

@[simp] public theorem diagonal2_coe (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      diagonal fun i => (a i : v.adicCompletion ℚ) :=
  rfl

public theorem diagonal2_mul (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    diagonal2 v (a * b) = diagonal2 v a * diagonal2 v b := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [diagonal2]
  · simp [diagonal2, Matrix.diagonal_apply_ne _ hij]

public def upperUnipotent2 (x : v.adicCompletion ℚ) : LocalGL2 v where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] public theorem upperUnipotent2_coe (x : v.adicCompletion ℚ) :
    (upperUnipotent2 v x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, x; 0, 1] :=
  rfl

public def halfModulus2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ((Real.sqrt (‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖) : ℝ) : ℂ)

public theorem halfModulus2_mul (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    halfModulus2 v (a * b) = halfModulus2 v a * halfModulus2 v b := by
  simp only [halfModulus2, Pi.mul_apply, Units.val_mul, norm_mul]
  rw [show ‖(a 0 : v.adicCompletion ℚ)‖ * ‖(b 0 : v.adicCompletion ℚ)‖ /
        (‖(a 1 : v.adicCompletion ℚ)‖ * ‖(b 1 : v.adicCompletion ℚ)‖)
      = ‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖ *
        (‖(b 0 : v.adicCompletion ℚ)‖ / ‖(b 1 : v.adicCompletion ℚ)‖) by ring,
    Real.sqrt_mul (by positivity)]
  push_cast
  ring

@[simp] public theorem halfModulus2_one : halfModulus2 v 1 = 1 := by
  simp [halfModulus2]

public theorem halfModulus2_ne_zero (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : halfModulus2 v a ≠ 0 := by
  unfold halfModulus2
  exact_mod_cast (Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr (a 0).ne_zero)
    (norm_pos_iff.mpr (a 1).ne_zero))).ne'

public theorem halfModulus2_eq_pos_real (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ∃ r : ℝ, 0 < r ∧ halfModulus2 v a = (r : ℂ) :=
  ⟨_, Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr (a 0).ne_zero)
    (norm_pos_iff.mpr (a 1).ne_zero)), rfl⟩


public def torusChar2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ∏ i : Fin 2, ((χ i (a i) : ℂˣ) : ℂ)

public theorem torusChar2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    torusChar2 v χ (a * b) = torusChar2 v χ a * torusChar2 v χ b := by
  simp only [torusChar2, Pi.mul_apply, map_mul, Units.val_mul, Finset.prod_mul_distrib]

@[simp] public theorem torusChar2_one (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    torusChar2 v χ 1 = 1 := by
  simp [torusChar2]

public def principalSeries2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    Submodule ℂ (LocalGL2 v → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    (∀ (x : v.adicCompletion ℚ) (g : LocalGL2 v), f (upperUnipotent2 v x * g) = f g) ∧
    ∀ (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v),
      f (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁lc, h₁n, h₁t⟩ := h₁
    obtain ⟨h₂lc, h₂n, h₂t⟩ := h₂
    refine ⟨h₁lc.comp₂ h₂lc (· + ·), fun x g => ?_, fun a g => ?_⟩
    · show f₁ _ + f₂ _ = f₁ g + f₂ g
      rw [h₁n, h₂n]
    · show f₁ _ + f₂ _ = _ * (f₁ g + f₂ g)
      rw [h₁t, h₂t]
      ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hlc, hn, ht⟩ := hf
    refine ⟨hlc.comp (c * ·), fun x g => ?_, fun a g => ?_⟩
    · show c * f _ = c * f g
      rw [hn]
    · show c * f _ = _ * (c * f g)
      rw [ht]
      ring

variable {v}

public theorem mem_principalSeries2_iff {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL2 v → ℂ} :
    f ∈ principalSeries2 v χ ↔
      IsLocallyConstant f ∧
        (∀ (x : v.adicCompletion ℚ) (g : LocalGL2 v), f (upperUnipotent2 v x * g) = f g) ∧
        ∀ (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v),
          f (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * f g :=
  Iff.rfl

public theorem rightTranslate2_mem_principalSeries2 {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : LocalGL2 v) :
    rightTranslate2 v g f ∈ principalSeries2 v χ := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  refine mem_principalSeries2_iff.mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun x h => ?_, fun a h => ?_⟩
  · show f (upperUnipotent2 v x * h * g) = f (h * g)
    rw [mul_assoc, hn]
  · show f (diagonal2 v a * h * g) = _ * f (h * g)
    rw [mul_assoc, ht]

public def principalSeries2Rep (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    LocalGL2 v →* Module.End ℂ ↥(principalSeries2 v χ) where
  toFun g := (rightTranslate2 v g).restrict fun f hf => rightTranslate2_mem_principalSeries2 hf g
  map_one' := by
    ext f h
    simp [rightTranslate2_apply]
  map_mul' g g' := by
    ext f h
    simp [rightTranslate2_apply, mul_assoc]


section UnipotentLine

variable (v)

public theorem upperUnipotent2_mul (x y : v.adicCompletion ℚ) :
    upperUnipotent2 v x * upperUnipotent2 v y = upperUnipotent2 v (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

public theorem upperUnipotent2_zero : upperUnipotent2 v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

public def unipotentHom2 : Multiplicative (v.adicCompletion ℚ) →* LocalGL2 v where
  toFun x := upperUnipotent2 v (Multiplicative.toAdd x)
  map_one' := upperUnipotent2_zero v
  map_mul' x y := (upperUnipotent2_mul v (Multiplicative.toAdd x) (Multiplicative.toAdd y)).symm

@[simp] public theorem unipotentHom2_ofAdd (x : v.adicCompletion ℚ) :
    unipotentHom2 v (Multiplicative.ofAdd x) = upperUnipotent2 v x :=
  rfl

public def unipotentRep2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    Representation ℂ (Multiplicative (v.adicCompletion ℚ)) ↥(principalSeries2 v χ) :=
  (principalSeries2Rep (v := v) χ).comp (unipotentHom2 v)

public theorem unipotentRep2_ofAdd_apply_coe (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x : v.adicCompletion ℚ)
    (f : ↥(principalSeries2 v χ)) (g : LocalGL2 v) :
    (unipotentRep2 v χ (Multiplicative.ofAdd x) f : LocalGL2 v → ℂ) g
      = (f : LocalGL2 v → ℂ) (g * upperUnipotent2 v x) :=
  rfl

end UnipotentLine

end PrincipalSeries2

end LanglandsTunnell.CubicInduction

end
