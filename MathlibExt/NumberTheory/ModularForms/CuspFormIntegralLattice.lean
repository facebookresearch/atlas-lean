/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_intLattice_fg.lean`,
`P2M/Sol/S_CuspForm_intLattice_fg.lean`, and
`Definitions/Def_CuspForm_IntegralStructure.lean`
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

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0
import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace CuspForm

/-- The integral lattice of cusp forms on `Γ₀(N)` of weight `k`: the
`ℤ`-span of the cusp forms whose `q`-expansion coefficients are all
integers. -/
public def intLattice (N : ℕ) (k : ℤ) :
    Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  Submodule.span ℤ
    {f | ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 (f : ℍ → ℂ)).coeff n = (m : ℂ)}

end CuspForm

namespace CuspFormIntegralLattice

variable {N : ℕ} {k : ℤ}

private theorem coeff_add (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    (qExpansion 1 ((f + g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℍ → ℂ)).coeff n
      = (qExpansion 1 (f : ℍ → ℂ)).coeff n + (qExpansion 1 (g : ℍ → ℂ)).coeff n := by
  simp only [FunLike.coe_add]
  rw [ModularForm.qExpansion_add one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]

private theorem coeff_zero (n : ℕ) :
    (qExpansion 1 ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℍ → ℂ)).coeff n
      = 0 := by
  simp only [FunLike.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

private theorem coeff_zsmul (c : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    (qExpansion 1 ((c • f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℍ → ℂ)).coeff n
      = c * (qExpansion 1 (f : ℍ → ℂ)).coeff n := by
  have h1 : ((c • f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℍ → ℂ)
      = (c : ℂ) • (f : ℍ → ℂ) := by
    ext z
    simp
  rw [h1, ModularForm.qExpansion_smul one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) (c : ℂ) f]
  simp

private def intSubmodule (N : ℕ) (k : ℤ) :
    Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) where
  carrier := {f | ∀ n : ℕ, ∃ m : ℤ,
    (qExpansion 1 (f : ℍ → ℂ)).coeff n = (m : ℂ)}
  add_mem' {f g} hf hg n := by
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a + b, by rw [coeff_add, ha, hb]; push_cast; ring⟩
  zero_mem' n := ⟨0, by rw [coeff_zero]; simp⟩
  smul_mem' c {f} hf n := by
    obtain ⟨a, ha⟩ := hf n
    exact ⟨c * a, by rw [coeff_zsmul, ha]; push_cast; ring⟩

private theorem intLattice_eq (N : ℕ) (k : ℤ) :
    CuspForm.intLattice N k = intSubmodule N k :=
  Submodule.span_eq (intSubmodule N k)

end CuspFormIntegralLattice

/-- A cusp form lies in the integral lattice exactly when every
`q`-expansion coefficient is an integer. -/
public theorem CuspForm.mem_intLattice_iff {N : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    f ∈ CuspForm.intLattice N k ↔
      ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 (f : ℍ → ℂ)).coeff n = (m : ℂ) := by
  rw [CuspFormIntegralLattice.intLattice_eq]
  rfl

namespace CuspFormIntegralLattice

variable {N : ℕ} {k : ℤ}

private noncomputable def sturmB (N : ℕ) (k : ℤ) : ℕ :=
  (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12

private noncomputable def trunc (N : ℕ) (k : ℤ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℤ] (Fin (sturmB N k + 1) → ℂ) where
  toFun f i := (qExpansion 1 (f : ℍ → ℂ)).coeff i
  map_add' f g := by
    funext i
    exact coeff_add f g i
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, eq_intCast, Int.cast_id]
    rw [coeff_zsmul, zsmul_eq_mul]

private theorem trunc_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (trunc N k) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  have hmf : (ModularFormClass.modularForm f :
      ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N _ fun n hn ↦ ?_
    have hcoeff := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [trunc] using hcoeff
  have hcoe : (f : ℍ → ℂ) = 0 := by
    have harg := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) k ↦
      (F : ℍ → ℂ)) hmf
    simpa using harg
  exact DFunLike.coe_injective (hcoe.trans (FunLike.coe_zero).symm)

end CuspFormIntegralLattice

/-- The integral lattice of cusp forms on `Γ₀(N)` of weight `k` is
finitely generated as a `ℤ`-module: by the Sturm bound, a cusp form in
the lattice is determined by its first `sturmB N k + 1` coefficients,
and those coefficients are integers. -/
public theorem CuspForm.intLattice_fg (N : ℕ) [NeZero N] (k : ℤ) :
    (CuspForm.intLattice N k).FG := by
  classical
  set B := CuspFormIntegralLattice.sturmB N k
  set M : Submodule ℤ (Fin (B + 1) → ℂ) :=
    Submodule.span ℤ (Set.range fun i : Fin (B + 1) ↦
      (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ)) with hM
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hle : (CuspForm.intLattice N k).map (CuspFormIntegralLattice.trunc N k) ≤ M := by
    rw [CuspForm.intLattice, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    choose m hm using hf
    have hv : CuspFormIntegralLattice.trunc N k f
        = ∑ i : Fin (B + 1), (m i) • (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j, Pi.smul_apply, Pi.single_eq_same,
        zsmul_eq_mul, mul_one]
      · exact hm j
      · intro i _ hij
        rw [Pi.smul_apply, Pi.single_eq_of_ne' hij, smul_zero]
      · simp
    rw [hv]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.fg_of_fg_map_injective (CuspFormIntegralLattice.trunc N k)
    (CuspFormIntegralLattice.trunc_injective N k) (hMfg.of_le hle)

namespace CuspForm

/-- The cusp forms on `Γ₀(N)` of weight `k` have an integral structure
when the complex span of the integral lattice is the whole space of
cusp forms. -/
public def HasIntegralStructure (N : ℕ) (k : ℤ) : Prop :=
  Submodule.span ℂ
    ((CuspForm.intLattice N k : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
      Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤

/-- An integral structure is exactly the statement that the complex span
of the integral lattice is everything. -/
public theorem hasIntegralStructure_iff (N : ℕ) (k : ℤ) :
    CuspForm.HasIntegralStructure N k ↔
      Submodule.span ℂ
        ((CuspForm.intLattice N k :
          Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
          Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤ :=
  Iff.rfl

end CuspForm
