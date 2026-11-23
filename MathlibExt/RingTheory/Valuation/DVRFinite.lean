/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean` and
`P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean`
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

public import MathlibExt.RingTheory.KrullAkizuki
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Valuation subrings of finite extensions are DVRs

A valuation subring of a finite extension of the fraction field of a
Noetherian domain of Krull dimension at most one, containing the base
ring and different from the whole field, is a discrete valuation ring.
This is the Krull–Akizuki theorem applied to the subring as a
subalgebra, plus the fact that a valuation ring which is Noetherian
and not a field is a DVR.
-/

@[expose] public section

namespace ValuationDVRFiniteAux

private theorem main {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  let B : Subalgebra A L :=
    { carrier := O
      mul_mem' := fun ha hb => O.mul_mem _ _ ha hb
      one_mem' := O.one_mem
      add_mem' := fun ha hb => O.add_mem _ _ ha hb
      zero_mem' := O.zero_mem
      algebraMap_mem' := hA }
  have hB := Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  haveI : IsNoetherianRing B := hB.1
  let e : B ≃+* O :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsNoetherianRing O := isNoetherianRing_of_ringEquiv B e
  have hnf : ¬ IsField O := by
    intro hF
    apply hO
    rw [eq_top_iff]
    intro x _
    by_contra hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx O.zero_mem
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
    have hne : (⟨x⁻¹, hxinv⟩ : O) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg Subtype.val h
      simpa using this
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    have hy' : x⁻¹ * (y : L) = 1 := by
      have := congrArg Subtype.val hy
      simpa using this
    have hyx : (y : L) = x := by
      have h1 : x * (x⁻¹ * (y : L)) = x := by rw [hy', mul_one]
      rwa [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact hx (hyx ▸ y.2)
  haveI : IsLocalRing O := inferInstance
  haveI : ValuationRing O := inferInstance
  exact (IsDiscreteValuationRing.TFAE O hnf).out 2 1 |>.mp ‹ValuationRing O›

end ValuationDVRFiniteAux

/-- A valuation subring of a finite extension of the fraction field of a
Noetherian domain of Krull dimension at most one, containing the base ring
and different from the whole field, is a discrete valuation ring. -/
theorem ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O :=
  ValuationDVRFiniteAux.main (K := K) O hA hO
