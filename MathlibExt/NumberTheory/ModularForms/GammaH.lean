/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_gamma1_coe_eq_of_gammaH.lean`,
`Definitions/Def_CohCarrier_Level.lean` and
`P2M/Sol/S_CuspForm_exists_gamma1_coe_eq_of_gammaH.lean`
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

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

/-- The product of the diagonal entries of an element of `Gamma0 M`, cast to
`ZMod M`, is `1`: this is the determinant relation together with the vanishing
of the lower-left entry. -/
public theorem gamma0_d_mul_a (M : ℕ) (γ : Gamma0 M) :
    ((γ.1 1 1 : ℤ) : ZMod M) * ((γ.1 0 0 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ.1
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ.1 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at h
  rw [mul_comm]
  exact h

/-- The homomorphism from `Gamma0 M` to the units of `ZMod M` given by the
lower-right entry, whose inverse is given by the upper-left entry. -/
public def gamma0Units (M : ℕ) : Gamma0 M →* (ZMod M)ˣ where
  toFun γ :=
    { val := Gamma0Map M γ
      inv := ((γ.1 0 0 : ℤ) : ZMod M)
      val_inv := gamma0_d_mul_a M γ
      inv_val := by rw [mul_comm]; exact gamma0_d_mul_a M γ }
  map_one' := by ext; simp
  map_mul' γ δ := by ext; exact map_mul (Gamma0Map M) γ δ

@[simp]
public theorem val_gamma0Units (M : ℕ) (γ : Gamma0 M) :
    (gamma0Units M γ : ZMod M) = Gamma0Map M γ :=
  rfl

/-- The intermediate congruence subgroup between `Gamma1 M` and `Gamma0 M`
cut out by a subgroup `H` of the units of `ZMod M`: matrices in `Gamma0 M`
whose lower-right entry, viewed as a unit, lies in `H`. -/
public def GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  (H.comap (gamma0Units M)).map (Gamma0 M).subtype

public theorem mem_GammaH_iff (M : ℕ) {H : Subgroup (ZMod M)ˣ} {A : SL(2, ℤ)} :
    A ∈ GammaH M H ↔ ∃ hA : A ∈ Gamma0 M, gamma0Units M ⟨A, hA⟩ ∈ H := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  · rintro ⟨hA, h⟩
    exact ⟨⟨A, hA⟩, h, rfl⟩

public theorem GammaH_le_Gamma0 (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    GammaH M H ≤ Gamma0 M := by
  intro A hA
  obtain ⟨hA0, _⟩ := (mem_GammaH_iff M).mp hA
  exact hA0

public theorem gamma1_le_gammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    Gamma1 M ≤ GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  rw [mem_GammaH_iff]
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA.2.2
  refine ⟨h0, ?_⟩
  have h1 : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA.2.1, Units.val_one]
  rw [h1]
  exact one_mem H

public theorem gamma_le_gammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    Gamma M ≤ GammaH M H := by
  intro A hA
  rw [mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have h1 : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [h1]
  exact one_mem H

/-- `GammaH M H` has finite index in `SL(2, ℤ)` for nonzero `M`, since it
contains the principal congruence subgroup `Gamma M`. -/
public instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma_le_gammaH M H)

end CongruenceSubgroup

namespace CuspForm

/-- A cusp form for the intermediate subgroup `GammaH M H` is already a cusp
form for `Gamma1 M`, with the same underlying function: `Gamma1 M` is contained
in `GammaH M H`, so invariance and vanishing at the cusps restrict. -/
public theorem exists_gamma1_coe_eq_of_gammaH (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g : UpperHalfPlane → ℂ) = ⇑f := by
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.GammaH M H : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (CongruenceSubgroup.gamma1_le_gammaH M H)
  refine ⟨{ toFun := ⇑f
            slash_action_eq' := fun γ hγ =>
              SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
            holo' := CuspFormClass.holo f
            zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

end CuspForm
