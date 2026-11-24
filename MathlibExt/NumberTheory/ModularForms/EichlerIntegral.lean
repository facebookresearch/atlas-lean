/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_HeckeEis_BinaryFormRep.lean`,
`Definitions/Def_HeckeEis_EichlerIntegral.lean`,
`Theorems/Thm_HeckeEis_IsEichlerIntegral_add.lean`
and
`P2M/Sol/S_HeckeEis_IsEichlerIntegral_add.lean`
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

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

open scoped UpperHalfPlane

namespace EichlerIntegral

/-- Binary forms of degree `n` in two variables over `ℂ`: the homogeneous
degree-`n` part of `MvPolynomial (Fin 2) ℂ`. -/
abbrev BinaryForm (n : ℕ) : Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n

/-- The degree-`n` binary form `(τ X₀ + X₁)ⁿ`, viewed in `BinaryForm n`. -/
noncomputable def linePow (n : ℕ) (τ : ℂ) : BinaryForm n :=
  ⟨(MvPolynomial.C τ * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n,
    (MvPolynomial.mem_homogeneousSubmodule n _).mpr (by
      simpa using (((MvPolynomial.isHomogeneous_X ℂ 0).C_mul τ).add
        (MvPolynomial.isHomogeneous_X ℂ 1)).pow n)⟩

@[simp]
theorem coe_linePow (n : ℕ) (τ : ℂ) :
    ((linePow n τ : BinaryForm n) : MvPolynomial (Fin 2) ℂ)
      = (MvPolynomial.C τ * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n :=
  rfl

/-- `F` is an Eichler integral of `f` of degree `n` when every coefficient of
`F`, read as a function on the upper half plane via `UpperHalfPlane.ofComplex`,
has derivative `f τ` times the corresponding coefficient of `linePow n τ`. -/
def IsEichlerIntegral (n : ℕ) (f : ℍ → ℂ) (F : ℍ → BinaryForm n) : Prop :=
  ∀ (d : Fin 2 →₀ ℕ) (τ : ℍ),
    HasDerivAt
      (fun z : ℂ => ((F (UpperHalfPlane.ofComplex z) : BinaryForm n) :
        MvPolynomial (Fin 2) ℂ).coeff d)
      (f τ * ((linePow n (τ : ℂ) : BinaryForm n) :
        MvPolynomial (Fin 2) ℂ).coeff d) (τ : ℂ)

namespace IsEichlerIntegral

/-- The zero function is an Eichler integral of the zero function. -/
theorem zero (n : ℕ) : IsEichlerIntegral n 0 0 := by
  intro d τ
  have hfun : (fun z : ℂ => (((0 : ℍ → BinaryForm n) (UpperHalfPlane.ofComplex z) :
      BinaryForm n) : MvPolynomial (Fin 2) ℂ).coeff d) = fun _ => (0 : ℂ) := by
    funext z
    simp
  rw [hfun]
  simp only [Pi.zero_apply, zero_mul]
  exact hasDerivAt_const _ _

/-- Eichler integrals of a fixed degree are closed under pointwise addition:
if `F` is an Eichler integral of `f` and `G` is an Eichler integral of `g`,
then `F + G` is an Eichler integral of `f + g`. -/
theorem add {n : ℕ} {f g : ℍ → ℂ} {F G : ℍ → BinaryForm n}
    (hF : IsEichlerIntegral n f F) (hG : IsEichlerIntegral n g G) :
    IsEichlerIntegral n (f + g) (F + G) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [← add_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp [Submodule.coe_add]

end IsEichlerIntegral

end EichlerIntegral
