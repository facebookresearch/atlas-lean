/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffineObstructionComplexes

/-!
# Obstruction-complex degree and nonzero-slot probes

The zero differential must leave a genuine nonzero obstruction direction.
An identity differential, the acyclic stabilization used in POT models,
must kill that direction. These check variance and the quotient slot.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes

noncomputable section

def zeroModel : FreeTwoTerm ℚ := ⟨1, 1, 0⟩
def identityModel : FreeTwoTerm ℚ := ⟨1, 1, LinearMap.id⟩

example : IsZero ((complex ℚ zeroModel).X (-2)) :=
  supportedDegrees zeroModel (-2) (by decide) (by decide)

example : IsZero ((complex ℚ zeroModel).X 1) :=
  supportedDegrees zeroModel 1 (by decide) (by decide)

example :
    (LinearMap.range (dualDifferential zeroModel ℚ)).mkQ (LinearMap.proj (0 : Fin 1)) ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨f, hf⟩ := hmem
  have h1 := congrArg (fun g : (Fin 1 → ℚ) →ₗ[ℚ] ℚ => g (fun _ => 1)) hf
  change f (0 : Fin zeroModel.zeroRank → ℚ) = 1 at h1
  rw [map_zero] at h1
  exact zero_ne_one h1

example :
    (LinearMap.range (dualDifferential identityModel ℚ)).mkQ (LinearMap.proj (0 : Fin 1)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨LinearMap.proj (0 : Fin 1), ?_⟩
  change (LinearMap.proj (0 : Fin 1) : (Fin 1 → ℚ) →ₗ[ℚ] ℚ) ∘ₗ LinearMap.id = _
  ext x
  rfl
