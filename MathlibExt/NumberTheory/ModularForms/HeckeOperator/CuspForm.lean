/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean`,
`P2M/Sol/S_CuspFormClass_isZeroAt_heckeT.lean`,
`Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean`,
`P2M/Sol/S_CuspFormClass_isZeroAt_heckeU.lean`,
`Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean`,
`P2M/Sol/S_CuspForm_exists_coe_eq_heckeT.lean`,
`Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean`
and
`P2M/Sol/S_CuspForm_exists_coe_eq_heckeU.lean`
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

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.QExpansion
public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.SlashInvariance

/-!
# Hecke operators on cusp forms

For an arithmetic group `Γ`, the Hecke operators `heckeU k p` and `heckeT k p`
send a cusp form for `Γ` to a function vanishing at every cusp of `Γ`: each
summand is the slash of the form by a rational matrix, which permutes the
cusps. Combined with the invariance results, `T p` for a prime `p ∤ N` and
`U p` for `p ∣ N` map `S_k(Γ₀(N))` to itself.

## Main results

* `CuspFormClass.isZeroAt_heckeU`, `CuspFormClass.isZeroAt_heckeT`
* `CuspForm.exists_coe_eq_heckeT`, `CuspForm.exists_coe_eq_heckeU`
-/

@[expose] public section

noncomputable section

open UpperHalfPlane OnePoint
open scoped MatrixGroups ModularForm

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

private theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

private theorem isZeroAt_slash_ratCast [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_ratCast_smul hc g))

/-- The rational upper-triangular matrix `!![a, b; 0, d]`. -/
private def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

private theorem exists_heckeUpperMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ,
      heckeUpperMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeUpperMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, ratUpperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem exists_heckeDiagMatrix_eq_map (p : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeDiagMatrix p = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeDiagMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, ratUpperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem isZeroAt_sum {ι : Type*} {c : OnePoint ℝ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsZeroAt (f i) k) : c.IsZeroAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end ModularForm

namespace CuspFormClass

open ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- For an arithmetic group `Γ`, the `U`-type Hecke sum of a cusp form for `Γ`
vanishes at every cusp of `Γ`. -/
public theorem isZeroAt_heckeU [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isZeroAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeUpperMatrix_eq_map p j
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

/-- For an arithmetic group `Γ`, the `T`-type Hecke operator applied to a cusp
form for `Γ` vanishes at every cusp of `Γ`. -/
public theorem isZeroAt_heckeT [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isZeroAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

end CuspFormClass

namespace CuspForm

/-- For a prime `p ∤ N`, the Hecke operator `T p` maps `S_k(Γ₀(N))` to itself. -/
public theorem exists_coe_eq_heckeT {N : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f := by
  have : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  exact ⟨{ toFun := ModularForm.heckeT k p ⇑f
           slash_action_eq' := fun γ hγ => ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 k hp
             hpN (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
           holo' := ModularForm.mdifferentiable_heckeT k p (CuspFormClass.holo f)
           zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }, rfl⟩

/-- For `p ∣ N`, the Hecke operator `U p` maps `S_k(Γ₀(N))` to itself. -/
public theorem exists_coe_eq_heckeU {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨{ toFun := ModularForm.heckeU k p ⇑f
     slash_action_eq' := fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 k hpN
       (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
     holo' := ModularForm.mdifferentiable_heckeU k p (CuspFormClass.holo f)
     zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }, rfl⟩

end CuspForm
