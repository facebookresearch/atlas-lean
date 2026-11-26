/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean` and
`P2M/Sol/S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan
import MathlibExt.NumberTheory.ModularForms.FrickeGamma0
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The trace from `Γ₀(p)` to level one

For a prime `p` and a modular form `X` of weight `k` and level `Γ₀(p)`, the sum
of `X` and its slashes by the coset representatives `S T ^ j` (`0 ≤ j < p`) of
`Γ₀(p)` in `SL(2, ℤ)` is a modular form of level one: the trace of `X` to level one, written
with these coset representatives.
Slashing `X` by the Fricke matrix `!![0, -1; p, 0]` and applying the Hecke
operator `U_p` recovers `p ^ (k - 2)` times the non-identity part of that sum,
so `p ^ (k - 2) X + U_p (X ∣ W_p)` is a modular form of level one
(`ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke`).

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

@[expose] public section

open Matrix UpperHalfPlane OnePoint
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularForm

namespace LevelOneTrace

variable {p : ℕ} {k : ℤ} (X : ModularForm (CongruenceSubgroup.Gamma0 p) k)

private lemma hp0 [Fact p.Prime] : p ≠ 0 := (Fact.out : p.Prime).ne_zero

/-- The slash `X ∣[k] (S * T ^ j)` of a modular form `X` of weight `k` on `Γ₀(p)`. For prime
`p`, the matrices `S * T ^ j` with `0 ≤ j < p`, together with `1`, are coset representatives of
`Γ₀(p)` in `SL(2, ℤ)`. -/
private def cosetSlash (j : ℕ) : UpperHalfPlane → ℂ :=
  ⇑X ∣[k] (ModularGroup.S * ModularGroup.T ^ j)

/-- The function `X + ∑_{0 ≤ j < p} X ∣[k] (S * T ^ j)` for a modular form `X` of weight `k`
on `Γ₀(p)`. For prime `p` it is the underlying function of the trace of `X` to level one. -/
private def traceFun : UpperHalfPlane → ℂ :=
  (∑ j ∈ Finset.range p, cosetSlash X j) + ⇑X

private theorem slash_eq_self_of_mem {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 p) :
    ⇑X ∣[k] A = ⇑X :=
  SlashInvariantFormClass.slash_action_eq (F := ModularForm (CongruenceSubgroup.Gamma0 p) k)
    X (Matrix.SpecialLinearGroup.mapGL ℝ A) (Subgroup.mem_map_of_mem _ hA)

private theorem coe_T_pow (j : ℕ) : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = !![1, (j : ℤ); 0, 1] := by
  rw [← zpow_natCast, ModularGroup.coe_T_zpow]

private theorem coe_T_pow' (j : ℕ) :
    ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ^ j = !![1, (j : ℤ); 0, 1] := by
  rw [← Matrix.SpecialLinearGroup.coe_pow, coe_T_pow]

private theorem T_mem : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [ModularGroup.coe_T]

private theorem S_mul_S_mem : ModularGroup.S * ModularGroup.S ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
    Fin.sum_univ_two]

private noncomputable def eta0 (q : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; -(q : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] private theorem eta0_coe (q : ℕ) :
    ((eta0 q : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -(q : ℤ), 1] := rfl

private theorem eta0_mem : eta0 p ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp

private theorem S_T_pow_add_p (j : ℕ) :
    ModularGroup.S * ModularGroup.T ^ (j + p)
      = eta0 p * (ModularGroup.S * ModularGroup.T ^ j) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      ModularGroup.coe_S, coe_T_pow', -ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

private theorem u_add_p (j : ℕ) : cosetSlash X (j + p) = cosetSlash X j := by
  unfold cosetSlash
  rw [S_T_pow_add_p, SlashAction.slash_mul, slash_eq_self_of_mem X eta0_mem]

private theorem sum_zmod_val [Fact p.Prime] {α : Type*} [AddCommMonoid α] (g : ℕ → α) :
    ∑ a : ZMod p, g a.val = ∑ j ∈ Finset.range p, g j := by
  have : NeZero p := ⟨hp0⟩
  exact Finset.sum_nbij' (fun (a : ZMod p) => a.val) (fun (n : ℕ) => (n : ZMod p))
    (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
    (fun n _ => Finset.mem_univ _)
    (fun a _ => ZMod.natCast_rightInverse a)
    (fun n hn => ZMod.val_cast_of_lt (Finset.mem_range.mp hn))
    (fun a _ => rfl)

private noncomputable def v (a : ZMod p) : UpperHalfPlane → ℂ := cosetSlash X a.val

private theorem u_slash_T (j : ℕ) :
    (cosetSlash X j) ∣[k] ModularGroup.T = cosetSlash X (j + 1) := by
  unfold cosetSlash
  rw [← SlashAction.slash_mul, mul_assoc, ← pow_succ]

private theorem trace_slash_T : (traceFun X) ∣[k] ModularGroup.T = traceFun X := by
  unfold traceFun
  rw [SlashAction.add_slash, SlashAction.sum_slash, slash_eq_self_of_mem X T_mem]
  congr 1
  calc ∑ j ∈ Finset.range p, (cosetSlash X j) ∣[k] ModularGroup.T
      = ∑ j ∈ Finset.range p, cosetSlash X (j + 1) :=
        Finset.sum_congr rfl fun j _ => u_slash_T X j
    _ = ∑ j ∈ Finset.range p, cosetSlash X j := by
        have e1 := Finset.sum_range_succ' (cosetSlash X) p
        have e2 := Finset.sum_range_succ (cosetSlash X) p
        have e3 : cosetSlash X p = cosetSlash X 0 := by simpa using u_add_p X 0
        rw [e3] at e2
        exact add_right_cancel (e1.symm.trans e2)

private noncomputable def etaS (j j' : ℕ) : SL(2, ℤ) :=
  ⟨!![-(j' : ℤ), -1; (j : ℤ) * (j' : ℤ) + 1, (j : ℤ)], by
    rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] private theorem etaS_coe (j j' : ℕ) :
    ((etaS j j' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![-(j' : ℤ), -1; (j : ℤ) * (j' : ℤ) + 1, (j : ℤ)] := rfl

private theorem u_mul_S (j j' : ℕ) (hmod : (((j : ℤ) * (j' : ℤ) + 1 : ℤ) : ZMod p) = 0) :
    (cosetSlash X j) ∣[k] ModularGroup.S = cosetSlash X j' := by
  have hmem : etaS j j' ∈ CongruenceSubgroup.Gamma0 p := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((j : ℤ) * (j' : ℤ) + 1 : ℤ) : ZMod p) = 0
    exact hmod
  have hmat : (ModularGroup.S * ModularGroup.T ^ j) * ModularGroup.S
      = etaS j j' * (ModularGroup.S * ModularGroup.T ^ j') := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i l => ?_
    fin_cases i <;> fin_cases l <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        ModularGroup.coe_S, coe_T_pow', -ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  unfold cosetSlash
  rw [← SlashAction.slash_mul, hmat, SlashAction.slash_mul, slash_eq_self_of_mem X hmem]

private theorem v_slash_S [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    (v X a) ∣[k] ModularGroup.S = v X (-a⁻¹) := by
  have : NeZero p := ⟨hp0⟩
  refine u_mul_S X a.val (-a⁻¹).val ?_
  push_cast
  rw [ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse (-a⁻¹), mul_neg,
    mul_inv_cancel₀ ha]
  ring

private theorem v_zero_slash_S : (v X 0) ∣[k] ModularGroup.S = ⇑X := by
  change (cosetSlash X (0 : ZMod p).val) ∣[k] ModularGroup.S = ⇑X
  rw [ZMod.val_zero]
  unfold cosetSlash
  rw [pow_zero, mul_one, ← SlashAction.slash_mul, slash_eq_self_of_mem X S_mul_S_mem]

private theorem X_slash_S : ⇑X ∣[k] ModularGroup.S = v X 0 := by
  change _ = cosetSlash X (0 : ZMod p).val
  rw [ZMod.val_zero]
  unfold cosetSlash
  rw [pow_zero, mul_one]

private theorem trace_slash_S [Fact p.Prime] :
    (traceFun X) ∣[k] ModularGroup.S = traceFun X := by
  unfold traceFun
  rw [SlashAction.add_slash, SlashAction.sum_slash, X_slash_S,
    ← sum_zmod_val (fun j => (cosetSlash X j) ∣[k] ModularGroup.S), ← sum_zmod_val (cosetSlash X)]
  change (∑ a : ZMod p, (v X a) ∣[k] ModularGroup.S) + v X 0
      = (∑ a : ZMod p, v X a) + ⇑X
  have e0 : ∑ a : ZMod p, (v X a) ∣[k] ModularGroup.S
      = (v X 0) ∣[k] ModularGroup.S
        + ∑ a ∈ Finset.univ.erase 0, (v X a) ∣[k] ModularGroup.S :=
    (Finset.add_sum_erase _ (fun a => (v X a) ∣[k] ModularGroup.S)
      (Finset.mem_univ 0)).symm
  have e1 : ∑ a : ZMod p, v X a = v X 0 + ∑ a ∈ Finset.univ.erase 0, v X a :=
    (Finset.add_sum_erase _ (v X) (Finset.mem_univ 0)).symm
  have hcong : ∑ a ∈ Finset.univ.erase 0, (v X a) ∣[k] ModularGroup.S
      = ∑ a ∈ Finset.univ.erase 0, v X a := by
    rw [Finset.sum_congr rfl fun a ha => v_slash_S X (Finset.ne_of_mem_erase ha)]
    refine Finset.sum_nbij' (fun (a : ZMod p) => -a⁻¹) (fun (a : ZMod p) => -a⁻¹)
      ?_ ?_ ?_ ?_ (fun a _ => rfl)
    · intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      simpa using inv_ne_zero (Finset.ne_of_mem_erase ha)
    · intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      simpa using inv_ne_zero (Finset.ne_of_mem_erase ha)
    · intro a _; simp
    · intro a _; simp
  rw [e0, e1, v_zero_slash_S, hcong]
  abel

private theorem trace_slash_SL [Fact p.Prime] (A : SL(2, ℤ)) :
    (traceFun X) ∣[k] A = traceFun X :=
  SlashInvariantForm.slash_action_generators_SL2Z (trace_slash_S X) (trace_slash_T X) A

private theorem trace_slash_GL [Fact p.Prime] (A : SL(2, ℤ)) :
    (traceFun X) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ A) = traceFun X :=
  trace_slash_SL X A

private theorem trace_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (traceFun X) := by
  unfold traceFun
  have hsum : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ j ∈ Finset.range p, cosetSlash X j) := by
    refine Finset.sum_induction _ (fun g : UpperHalfPlane → ℂ => MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
      (fun a b ha hb => ha.add hb) ?_ ?_
    · exact mdifferentiable_const
    · intro j _
      exact (ModularFormClass.holo X).slash _ _
  exact hsum.add (ModularFormClass.holo X)

private theorem trace_bdd [Fact p.Prime] : IsBoundedAtImInfty (traceFun X) := by
  have hsum : IsBoundedAtImInfty (∑ j ∈ Finset.range p, cosetSlash X j) := by
    refine Finset.sum_induction _ (fun g : UpperHalfPlane → ℂ => IsBoundedAtImInfty g)
      (fun a b ha hb => Filter.BoundedAtFilter.add ha hb) zero_form_isBoundedAtImInfty ?_
    intro j _
    have hcusp : IsCusp ((Matrix.SpecialLinearGroup.mapGL ℝ
        (ModularGroup.S * ModularGroup.T ^ j)) • (∞ : OnePoint ℝ))
        (CongruenceSubgroup.Gamma0 p) :=
      (isCusp_SL2Z_iff'.mpr ⟨_, rfl⟩).of_isFiniteRelIndex
    exact ModularFormClass.bdd_at_cusps X hcusp _ rfl
  have hX : IsBoundedAtImInfty ⇑X := by
    have hcusp : IsCusp (∞ : OnePoint ℝ) (CongruenceSubgroup.Gamma0 p) :=
      (isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩).of_isFiniteRelIndex
    have h := ModularFormClass.bdd_at_cusps X hcusp 1 (by simp)
    rwa [SlashAction.slash_one] at h
  unfold traceFun
  exact Filter.BoundedAtFilter.add hsum hX


private theorem heckeU_slash_W [Fact p.Prime] (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, -1; (p : ℝ), 0]) :
    heckeU k p (⇑X ∣[k] W) = (p : ℂ) ^ (k - 2) • ∑ j ∈ Finset.range p, cosetSlash X j := by
  rw [heckeU_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : p ≠ 0 := hp0
  have hpu : ((p : ℝ)) ≠ 0 := by exact_mod_cast hp
  rw [← SlashAction.slash_mul]
  have hZ : ((ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![0, -1; 1, (j : ℤ)] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_pow, ModularGroup.coe_S]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hR : ((Matrix.SpecialLinearGroup.mapGL ℝ
      (ModularGroup.S * ModularGroup.T ^ j) : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, (j : ℝ)] := by
    rw [show ((SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ j) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
          (algebraMap ℤ ℝ) from rfl, hZ]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.map_apply]
  have hWM : W * heckeUpperMatrix p j
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu)
        * Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ j) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hW, val_heckeUpperMatrix hp]
    rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hpu) :
        Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = Matrix.scalar (Fin 2) (p : ℝ) from rfl]
    rw [hR, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  rw [hWM, SlashAction.slash_mul, slash_scalar_natCast k hpu]
  exact SL_smul_slash k (ModularGroup.S * ModularGroup.T ^ j) ⇑X ((p : ℂ) ^ (k - 2))


end LevelOneTrace

open LevelOneTrace

variable {p : ℕ} [Fact p.Prime] {k : ℤ} (X : ModularForm (CongruenceSubgroup.Gamma0 p) k)

/-- For a prime `p` and a modular form `X` of weight `k` on `Γ₀(p)`, the trace of `X` to level
one: the level-one modular form `X + ∑_{0 ≤ j < p} X ∣[k] (S * T ^ j)` of weight `k`. -/
private def levelOneTrace : ModularForm 𝒮ℒ k where
  toFun := LevelOneTrace.traceFun X
  slash_action_eq' := by
    rintro γ ⟨A, rfl⟩
    exact LevelOneTrace.trace_slash_SL X A
  holo' := LevelOneTrace.trace_holo X
  bdd_at_cusps' := by
    intro c hc
    obtain ⟨A, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    rw [OnePoint.isBoundedAt_iff rfl, LevelOneTrace.trace_slash_GL X A]
    exact LevelOneTrace.trace_bdd X

private theorem coe_levelOneTrace :
    ⇑(levelOneTrace X)
      = (∑ j ∈ Finset.range p, ⇑X ∣[k] (ModularGroup.S * ModularGroup.T ^ j)) + ⇑X :=
  rfl

/-- Let `p` be prime, `X` a modular form of weight `k` on `Γ₀(p)`, and `W ∈ GL(2, ℝ)` the
Fricke matrix `!![0, -1; p, 0]`. Then `p ^ (k - 2) • X + U_p (X ∣[k] W)` is a modular form of
weight `k` and level one, where `U_p` is `heckeU k p`, the sum of the weight-`k` slashes by
`!![1, j; 0, p]` for `0 ≤ j < p`. -/
theorem exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke (p : ℕ) [Fact p.Prime]
    (k : ℤ) (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ∃ Y : ModularForm 𝒮ℒ k, ⇑Y = (p : ℂ) ^ (k - 2) • ⇑X + heckeU k p (⇑X ∣[k] W) := by
  refine ⟨(p : ℂ) ^ (k - 2) • levelOneTrace X, ?_⟩
  rw [heckeU_slash_W X W hW, FunLike.coe_smul, coe_levelOneTrace, smul_add, add_comm]
  rfl

end ModularForm
