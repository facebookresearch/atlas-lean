/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_
residue_eq_of_injective.lean`
and
`P2M/Sol/S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_
residue_eq_of_injective.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open Polynomial IsLocalRing
open scoped TensorProduct

universe u v w

namespace IsLocalRing

variable {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪]
  {A : Type v} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
  [Module.Free 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]

omit [Module.Free 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)] in
private theorem exists_pow_mem_map_maximalIdeal (m : A) (hm : m ∈ maximalIdeal A) :
    ∃ n : ℕ, m ^ n ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 A) := by
  have hrad : m ∈ ((maximalIdeal 𝒪).map (algebraMap 𝒪 A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    have hcomap : maximalIdeal 𝒪 ≤ P.comap (algebraMap 𝒪 A) :=
      Ideal.map_le_iff_le_comap.mp hIP
    have hne : P.comap (algebraMap 𝒪 A) ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    have heq : P.comap (algebraMap 𝒪 A) = maximalIdeal 𝒪 :=
      ((IsLocalRing.maximalIdeal.isMaximal 𝒪).eq_of_le hne hcomap).symm
    have hmax' : (P.comap (algebraMap 𝒪 A)).IsMaximal :=
      heq ▸ IsLocalRing.maximalIdeal.isMaximal 𝒪
    have := hP
    have hPmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap 𝒪 A)
        (algebraMap_isIntegral_iff.mpr inferInstance) P hmax'
    rw [IsLocalRing.eq_maximalIdeal hPmax]
    exact hm
  exact hrad

omit [IsLocalRing A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
  [IsLocalHom (algebraMap 𝒪 A)] in
private theorem baseChange_lmul_eq_zero_of_mem {a : A}
    (ha : a ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    (Algebra.lmul 𝒪 A a).baseChange (ResidueField 𝒪) = 0 := by
  refine Submodule.span_induction
    (p := fun a _ => (Algebra.lmul 𝒪 A a).baseChange (ResidueField 𝒪) = 0)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨r, hr, rfl⟩
    have h1 : Algebra.lmul 𝒪 A (algebraMap 𝒪 A r) = r • (1 : Module.End 𝒪 A) := by
      ext b
      simp [Algebra.smul_def]
    rw [h1, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      ← algebraMap_smul (ResidueField 𝒪) r, ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_smul]
  · change (Algebra.lmul 𝒪 A 0).baseChange (ResidueField 𝒪) = 0
    rw [map_zero, LinearMap.baseChange_zero]
  · intro a b _ _ ha hb
    rw [map_add, LinearMap.baseChange_add, ha, hb, add_zero]
  · intro a b _ hb
    rw [smul_eq_mul, map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, hb,
      LinearMap.comp_zero]

private theorem exists_monic_aeval_eq_zero_map_residue_eq_pow
    {F : Type w} [CommRing F] [Algebra 𝒪 F]
    (φ : A →ₐ[𝒪] F) (x : A) (c : ResidueField 𝒪)
    (hx : residue A x = ResidueField.map (algebraMap 𝒪 A) c) :
    ∃ R : Polynomial 𝒪, R.Monic ∧ aeval (φ x) R = 0 ∧
        R.map (residue 𝒪) = (X - C c) ^ R.natDegree := by
  classical
  set f : Module.End 𝒪 A := Algebra.lmul 𝒪 A x with hf
  have hCH : aeval x f.charpoly = 0 := by
    have h1 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
    have h2 := congrArg (fun g : Module.End 𝒪 A => g 1) h1
    simp only [LinearMap.zero_apply, hf, aeval_algHom_apply] at h2
    simpa [hf] using h2
  refine ⟨f.charpoly, f.charpoly_monic, by rw [aeval_algHom_apply, hCH, map_zero], ?_⟩
  obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
  change residue A x = ResidueField.map (algebraMap 𝒪 A) (residue 𝒪 c₀) at hx
  rw [ResidueField.map_residue] at hx
  set m : A := x - algebraMap 𝒪 A c₀ with hm
  have hmmem : m ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hm, map_sub, hx, sub_self]
  obtain ⟨n, hn⟩ := exists_pow_mem_map_maximalIdeal (𝒪 := 𝒪) m hmmem
  have hnil : IsNilpotent ((Algebra.lmul 𝒪 A m).baseChange (ResidueField 𝒪)) := by
    refine ⟨n, ?_⟩
    rw [← LinearMap.baseChange_pow, ← map_pow]
    exact baseChange_lmul_eq_zero_of_mem hn
  have hkey : (Algebra.lmul 𝒪 A m).baseChange (ResidueField 𝒪) =
      f.baseChange (ResidueField 𝒪) - (residue 𝒪 c₀) • 1 := by
    have h1 : Algebra.lmul 𝒪 A (algebraMap 𝒪 A c₀) = c₀ • (1 : Module.End 𝒪 A) := by
      ext b
      simp [Algebra.smul_def]
    rw [hm, map_sub, LinearMap.baseChange_sub, hf, h1, LinearMap.baseChange_smul,
      LinearMap.baseChange_one, ← algebraMap_smul (ResidueField 𝒪) c₀,
      ResidueField.algebraMap_eq]
  have hchar : (f.baseChange (ResidueField 𝒪) - (residue 𝒪 c₀) • 1).charpoly =
      X ^ Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] A) := by
    rw [← hkey]
    exact hnil.charpoly_eq_X_pow_finrank
  rw [LinearMap.charpoly_sub_smul] at hchar
  have hbc : (f.baseChange (ResidueField 𝒪)).charpoly =
      (X - C (residue 𝒪 c₀)) ^
        Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] A) := by
    have h := congrArg (fun p : Polynomial (ResidueField 𝒪) => p.comp (X - C (residue 𝒪 c₀)))
      hchar
    simp only [Polynomial.comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel,
      Polynomial.comp_X, X_pow_comp] at h
    exact h
  rw [LinearMap.charpoly_baseChange, ResidueField.algebraMap_eq] at hbc
  rw [hbc]
  congr 1
  have hdeg := congrArg natDegree hbc
  rwa [(f.charpoly_monic).natDegree_map, natDegree_pow, natDegree_X_sub_C, mul_one,
    eq_comm] at hdeg

omit [Module.Finite 𝒪 A] [Module.Free 𝒪 A] in
private theorem residue_eq_of_monic_aeval_eq_zero_map_residue_eq_pow
    {F : Type w} [CommRing F] [Algebra 𝒪 F]
    (j : A →ₐ[𝒪] F) (hj : Function.Injective j) (x : A) (c : ResidueField 𝒪)
    (R : Polynomial 𝒪) (hR : R.Monic) (hRx : aeval (j x) R = 0)
    (hRc : R.map (residue 𝒪) = (X - C c) ^ R.natDegree) :
    residue A x = ResidueField.map (algebraMap 𝒪 A) c := by
  have hRA : aeval x R = 0 := by
    apply hj
    rw [← aeval_algHom_apply, hRx, map_zero]
  have hn : R.natDegree ≠ 0 := by
    intro h0
    have hR1 : R = 1 := Polynomial.eq_one_of_monic_natDegree_zero hR h0
    rw [hR1, map_one] at hRA
    exact one_ne_zero hRA
  set ψ : 𝒪 →+* ResidueField A := (residue A).comp (algebraMap 𝒪 A) with hψ
  have hfac : ψ = (ResidueField.map (algebraMap 𝒪 A)).comp (residue 𝒪) := by
    ext r
    change residue A (algebraMap 𝒪 A r) = ResidueField.map (algebraMap 𝒪 A) (residue 𝒪 r)
    rw [ResidueField.map_residue]
  have h1 : residue A (aeval x R) = R.eval₂ ψ (residue A x) := by
    rw [aeval_def, Polynomial.hom_eval₂]
  rw [hRA, map_zero, hfac, ← Polynomial.eval₂_map, hRc, eval₂_pow, eval₂_sub, eval₂_X,
    eval₂_C] at h1
  have h2 := (pow_eq_zero_iff hn).mp h1.symm
  exact (sub_eq_zero.mp h2)

/-- The residue of an element of a finite free local algebra is recognized by a
monic annihilating polynomial whose reduction is a pure power of `X - C c`. -/
public theorem exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
    {F : Type w} [CommRing F] [Algebra 𝒪 F]
    (j : A →ₐ[𝒪] F) (hj : Function.Injective j) (x : A) (c : ResidueField 𝒪) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (j x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) ↔
      IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c :=
  ⟨fun ⟨R, hR, hRx, hRc⟩ =>
    residue_eq_of_monic_aeval_eq_zero_map_residue_eq_pow j hj x c R hR hRx hRc,
   fun hx => exists_monic_aeval_eq_zero_map_residue_eq_pow j x c hx⟩

end IsLocalRing
