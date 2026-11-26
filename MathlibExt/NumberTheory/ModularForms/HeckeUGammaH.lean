/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_CohCarrier_Level.lean`,
`Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`,
`Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean`,
`Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean`,
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean`,
`Theorems/Thm_CuspForm_stableU.lean`,
`Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean` and
`Theorems/Thm_CuspForm_heckeULinH_comm.lean`
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
public import MathlibExt.NumberTheory.ModularForms.GammaH
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
public import MathlibExt.NumberTheory.ModularForms.CoeffHecke
public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan
public import MathlibExt.NumberTheory.ModularForms.HeckeOperator

/-!
# The Hecke operators `U_q` on cusp forms for `GammaH M H`

For `M ≠ 0`, a subgroup `H` of `(ZMod M)ˣ` and a prime `q` dividing `M`, the Hecke sum
`ModularForm.heckeU k q` (from `TwoCuspReductionSpan`) preserves invariance under the weight-`k`
slash action of `CongruenceSubgroup.GammaH M H` (`ModularForm.heckeU_slash_eq_self_of_mem_GammaH`).
The proof splits `GammaH M H` into cosets of its intersection `CongruenceSubgroup.GammaHUpper M H q`
with the matrices whose upper-right entry is divisible by `q`, using `HeckeEis.heckeUpperSL` and
`HeckeEis.heckeConjSL` from `CoeffHecke`. So cusp forms for `GammaH M H` satisfy
`CuspForm.StableU` at such `q` (`CuspForm.stableU`), and there `CuspForm.heckeULinH k q` is
`heckeU k q` rather than its zero default. On `q`-expansion coefficients it sends `a n` to
`a (n * q)` (`CuspForm.qCoeff_heckeULinH`), so the operators at two such primes commute
(`CuspForm.heckeULinH_comm`).
-/

@[expose] public section

open scoped MatrixGroups ModularForm

namespace CongruenceSubgroup

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

theorem mem_heckeUpperSL_iff_intCast_eq_zero {ℓ : ℕ} {A : SL(2, ℤ)} :
    A ∈ HeckeEis.heckeUpperSL ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

abbrev GammaHUpper : Subgroup ↥(GammaH M H) := (HeckeEis.heckeUpperSL ℓ).subgroupOf (GammaH M H)

theorem dvd_of_mem_GammaHUpper (γ : ↥(GammaHUpper M H ℓ)) : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
  HeckeEis.mem_heckeUpperSL.mp (Subgroup.mem_subgroupOf.mp γ.2)

def conjL [NeZero ℓ] : ↥(GammaHUpper M H ℓ) →* ↥(GammaH M H) where
  toFun γ := ⟨HeckeEis.heckeConjSL M ℓ
      ⟨⟨(γ : SL(2, ℤ)), GammaH_le_Gamma0 M H (γ : ↥(GammaH M H)).2⟩, γ.2⟩, by
    obtain ⟨hγ0, hγH⟩ := (mem_GammaH_iff M).mp (γ : ↥(GammaH M H)).2
    rw [mem_GammaH_iff M]
    refine ⟨HeckeEis.heckeConjSL_mem_Gamma0 M ℓ _, ?_⟩
    convert hγH using 1
    ext
    simp only [val_gamma0Units, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    change HeckeEis.heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1
    exact HeckeEis.heckeConjMat_one ℓ
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    change HeckeEis.heckeConjMat ℓ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      HeckeEis.heckeConjMat ℓ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        HeckeEis.heckeConjMat ℓ ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    exact HeckeEis.heckeConjMat_mul (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
      (dvd_of_mem_GammaHUpper M H ℓ γ) (dvd_of_mem_GammaHUpper M H ℓ δ)

public instance gammaHUpper_finiteIndex [NeZero M] [NeZero ℓ] :
    (GammaHUpper M H ℓ).FiniteIndex := by
  have : ((Gamma (M * ℓ)).subgroupOf (GammaH M H)).FiniteIndex := inferInstance
  refine Subgroup.finiteIndex_of_le (H := (Gamma (M * ℓ)).subgroupOf (GammaH M H)) ?_
  intro γ hγ
  have hγ2 := Subgroup.mem_subgroupOf.mp hγ
  refine Subgroup.mem_subgroupOf.mpr (HeckeEis.mem_heckeUpperSL.mpr ?_)
  have h01 : (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod (M * ℓ)) = 0 := (Gamma_mem.mp hγ2).2.1
  exact dvd_trans (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) by exact_mod_cast dvd_mul_left ℓ M)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (M * ℓ)).mp h01)

end CongruenceSubgroup

namespace ModularFormHeckeGammaH

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace HeckeGammaH

section

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

private noncomputable def beta
    (c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q) :
    GL (Fin 2) ℝ :=
  ModularForm.heckeUpperMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))⁻¹) :
      GL (Fin 2) ℝ)

omit [NeZero M] in
private theorem mapGL_conjL_mul_heckeUpperMatrix (t : ↥(CongruenceSubgroup.GammaHUpper M H q)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
      ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeUpperMatrix q 0 =
      ModularForm.heckeUpperMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) :
          GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hdvd : (q : ℤ) ∣ (((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin
    2) ℤ) 0 1 :=
    dvd_of_mem_GammaHUpper M H q t
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeUpperMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
    ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (HeckeEis.heckeConjMat q
        (((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))
    : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have hcast : (((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0
    1 / q : ℤ) : ℝ) * q =
      (((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) :
        ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hdvd
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

private theorem sum_slash_beta_slash_eq (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ =
      f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.GammaH M H).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) :
    letI := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
      q c) ∣[k] γ =
      ∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
        q c := by
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  set g' : ↥(CongruenceSubgroup.GammaH M H) := ⟨g, hg⟩ with hg'
  have hterm : ∀ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q,
      (f ∣[k] beta M H q c) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        f ∣[k] beta M H q (g'⁻¹ • c) := by
    intro c
    set d := g'⁻¹ • c with hd
    have hmk : (QuotientGroup.mk (g'⁻¹ * c.out) : ↥(CongruenceSubgroup.GammaH M H) ⧸
      CongruenceSubgroup.GammaHUpper M H q) = d := by
      rw [hd]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [MulAction.Quotient.smul_mk]
      rfl
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.GammaHUpper M H q) (g'⁻¹ *
      c.out)
    rw [hmk] at ht
    have hrel : (((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)))⁻¹ * g =
        (((t : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) : SL(2,
          ℤ)) * (((d.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)))⁻¹ := by
      have h1 : ((d.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) =
          (g⁻¹ * ((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) * (((t :
            ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))
              := by
        have := congrArg (fun x : ↥(CongruenceSubgroup.GammaH M H) => (x : SL(2, ℤ))) ht
        simpa using this
      rw [h1]; group
    rw [← SlashAction.slash_mul]
    have hb : beta M H q c * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
          ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          beta M H q d := by
      simp only [beta]
      rw [mul_assoc, ← map_mul, hrel, map_mul, ← mul_assoc, ← mapGL_conjL_mul_heckeUpperMatrix,
        mul_assoc]
    rw [hb, SlashAction.slash_mul, hf _ (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.conjL M H q
      t).2)]
  classical
  have hsum : ∀ (s : Finset (↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H
    q)) (F : (↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q) → ℍ → ℂ)
      (A : GL (Fin 2) ℝ), (∑ c ∈ s, F c) ∣[k] A = ∑ c ∈ s, (F c) ∣[k] A := by
    intro s F A
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum]
  simp_rw [hterm]
  exact Fintype.sum_bijective (g'⁻¹ • ·) (MulAction.bijective g'⁻¹) _ _ (fun c => rfl)

end

end HeckeGammaH

namespace HeckeGammaH

section Affine

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

private def transl (n : ℤ) : ↥(CongruenceSubgroup.GammaH M H) :=
  ⟨ModularGroup.T ^ n, by
    rw [mem_GammaH_iff M]
    have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
      rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
    refine ⟨h0, ?_⟩
    have : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
      ext; rw [val_gamma0Units]
      change (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
      rw [ModularGroup.coe_T_zpow]; simp
    rw [this]; exact one_mem H⟩

omit [NeZero M] in
@[scoped simp] private theorem coe_transl (n : ℤ) :
    ((transl M H n : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) = ModularGroup.T ^ n := rfl

private theorem exists_add_neg_eq_mul (j : Fin q) :
    ∃ e : ℕ, (j : ℕ) + ((-j : Fin q) : ℕ) = e * q := by
  have h : ((j : ℕ) + ((-j : Fin q) : ℕ)) % q = 0 := by
    have := Fin.val_add j (-j)
    rw [add_neg_cancel, Fin.val_zero] at this
    exact this.symm
  exact ⟨((j : ℕ) + ((-j : Fin q) : ℕ)) / q, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩

private theorem heckeUpperMatrix_zero_mul_mapGL_T_zpow_neg (j : Fin q) (e : ℕ)
    (he : (j : ℕ) + ((-j : Fin q) : ℕ) = e * q) :
    ModularForm.heckeUpperMatrix q 0 *
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ ((j : ℕ) : ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
        ModularForm.heckeUpperMatrix q ((-j : Fin q) : ℕ) := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeUpperMatrix hq,
    ModularForm.val_heckeUpperMatrix hq]
  have e1 : ∀ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ n)⁻¹) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (-n : ℝ); 0, 1] := by
    intro n
    rw [← zpow_neg, show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (-n))) : GL (Fin 2)
      ℝ) =
      ((ModularGroup.T ^ (-n) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl,
      ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e1, e1]
  have he' : ((j : ℕ) : ℝ) + (((-j : Fin q) : ℕ) : ℝ) = (e : ℝ) * (q : ℝ) := by exact_mod_cast he
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linarith [he']

omit [NeZero M] in
private theorem bijective_transl (hqM : q ∣ M) :
    Function.Bijective (fun j : Fin q => (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)) :
      ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q)) := by
  have hq : q ≠ 0 := NeZero.ne q
  constructor
  · intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl, ←
      zpow_neg, ← zpow_add,
      mem_heckeUpperSL_iff_intCast_eq_zero, ModularGroup.coe_T_zpow] at hij
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero] at hij
    apply Fin.ext
    have h1 : ((j : ℕ) : ZMod q) = ((i : ℕ) : ZMod q) := by
      have : ((-(i : ℕ) + (j : ℕ) : ℤ) : ZMod q) = 0 := by exact_mod_cast hij
      push_cast at this
      linear_combination this
    have := (ZMod.natCast_eq_natCast_iff' (j : ℕ) (i : ℕ) q).mp h1
    rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at this
    exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H γ =>
    obtain ⟨h0, -⟩ := (mem_GammaH_iff M).mp γ.2
    have hc : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (Int.natCast_dvd_natCast.mpr hqM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (Gamma0_mem.mp h0))
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at hdet
    have had : ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 :=
      by
      have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this
    set jz : ZMod q := ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q)
      with hjz
    refine ⟨⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
    symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
      mem_heckeUpperSL_iff_intCast_eq_zero]
    have hentry : ((γ : SL(2, ℤ))⁻¹ * ModularGroup.T ^ (((jz.val : ℕ) : ℤ)) : SL(2, ℤ)) 0 1 =
        ((γ : SL(2, ℤ)) 1 1 : ℤ) * ((jz.val : ℕ) : ℤ) - ((γ : SL(2, ℤ)) 0 1 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        ModularGroup.coe_T_zpow,
        Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hentry]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
    linear_combination ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * had

private theorem sum_slash_beta_eq_heckeU (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ =
      f) :
    letI := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
      q c) = ModularForm.heckeU k q f := by
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [← Fintype.sum_bijective _ (bijective_transl M H q hqM) (fun j => f ∣[k] beta M H q
      (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)))) _ (fun _ => rfl)]
  have hterm : ∀ j : Fin q, f ∣[k] beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      f ∣[k] ModularForm.heckeUpperMatrix q ((-j : Fin q) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.GammaHUpper M H q) (transl M H
      ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul q j
    have hb : beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q k⁻¹ :
          ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeUpperMatrix q ((-j : Fin q) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) :
          SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) :
            SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeUpperMatrix, mul_assoc, coe_transl,
        heckeUpperMatrix_zero_mul_mapGL_T_zpow_neg q j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q k⁻¹ :
      ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (CongruenceSubgroup.conjL M H q k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, hf _ hmem1,
      hf _ hmem2]
  simp_rw [hterm]
  rw [ModularForm.heckeU_def,
    ← Fin.sum_univ_eq_sum_range (fun i => f ∣[k] ModularForm.heckeUpperMatrix q i) q]
  exact Fintype.sum_equiv (Equiv.neg (Fin q)) _ _ (fun j => rfl)

end Affine

end HeckeGammaH

end ModularFormHeckeGammaH

namespace ModularForm

/-- Let `M ≠ 0` and let `q` be a prime dividing `M`. If `f : ℍ → ℂ` is invariant under the
weight-`k` slash action of `GammaH M H`, then so is `heckeU k q f`. -/
public theorem heckeU_slash_eq_self_of_mem_GammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k q f) ∣[k] γ = heckeU k q f := by
  have : NeZero q := ⟨hq.ne_zero⟩
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [← ModularFormHeckeGammaH.HeckeGammaH.sum_slash_beta_eq_heckeU M H q hqM k hf]
  exact ModularFormHeckeGammaH.HeckeGammaH.sum_slash_beta_slash_eq M H q k hf γ hγ

end ModularForm

namespace CuspForm

/-- For `M ≠ 0` and a prime `q` dividing `M`, cusp forms of weight `k` for `GammaH M H` satisfy
`StableU M H k q`: for each such cusp form `f`, `heckeU k q f` is invariant under `GammaH M H`,
holomorphic, and vanishes at every cusp. So at such `q`, `heckeULinH k q` is `heckeU k q` rather
than its zero default (`coe_heckeULinH_apply`). -/
public theorem stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) : StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩

end CuspForm

namespace CuspForm

private theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.GammaH M H : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.GammaH M H :=
    CongruenceSubgroup.gamma1_le_gammaH M H
      (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

private theorem eq_of_forall_qCoeff_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (F G : CuspForm (CongruenceSubgroup.GammaH M H) k)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff F n = ModularFormClass.qCoeff G n) :
    F = G := by
  have hΓ := one_mem_strictPeriods_GammaH M H
  have : Fact (IsCusp OnePoint.infty
      ((CongruenceSubgroup.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h1 : UpperHalfPlane.qExpansion 1 (⇑(F - G)) = 0 := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ F G]
    ext n
    have hh := h n
    simp only [ModularFormClass.qCoeff] at hh
    simp [hh]
  have h2 : (⇑(F - G) : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (F - G) hΓ)
      (ModularFormClass.holo (F - G)) (ModularFormClass.bdd_at_infty (F - G))).mp h1
  have h3 : F - G = 0 := DFunLike.ext' (by rw [h2]; rfl)
  exact sub_eq_zero.mp h3

/-- For `M ≠ 0` and a prime `q` dividing `M`, the `n`-th `q`-expansion coefficient
(`ModularFormClass.qCoeff`, in powers of `exp (2 * π * I * τ)`) of `heckeULinH k q f` is the
`(n * q)`-th coefficient of the cusp form `f` of weight `k` for `GammaH M H`. -/
public theorem qCoeff_heckeULinH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeULinH k q f) n = ModularFormClass.qCoeff f (n * q) := by
  have hcoe : ModularFormClass.qCoeff (⇑(heckeULinH k q f)) n =
      ModularFormClass.qCoeff (ModularForm.heckeU k q ⇑f) n := by
    rw [coe_heckeULinH_apply k (stableU M H k hq hqM) f]
  rw [hcoe, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_GammaH M H) hq.ne_zero n,
    ModularForm.coeffHeckeU_apply]

/-- For `M ≠ 0` and primes `q` and `q'` dividing `M`, the operators `heckeULinH k q` and
`heckeULinH k q'` commute on cusp forms of weight `k` for `GammaH M H`. At such primes these
operators are `heckeU k q` and `heckeU k q'` (`stableU`), so this is the commutation of `U_q` and
`U_{q'}`. -/
public theorem heckeULinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    heckeULinH k q (heckeULinH k q' f) = heckeULinH k q' (heckeULinH k q f) := by
  apply eq_of_forall_qCoeff_eq M H
  intro n
  rw [qCoeff_heckeULinH M H k hq hqM, qCoeff_heckeULinH M H k hq' hq'M,
    qCoeff_heckeULinH M H k hq' hq'M, qCoeff_heckeULinH M H k hq hqM, mul_right_comm]

end CuspForm
