/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_span_tmul_intTwoCuspReduce_eq_top.lean`,
`P2M/Sol/S_CuspForm_span_tmul_intTwoCuspReduce_eq_top.lean`,
`Definitions/Def_ModularCurve_XHDifferentialsModL.lean`,
`Definitions/Def_CuspForm_TwoCuspLattice.lean`,
`Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`,
`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_CohCarrier_Level.lean`, and
`Definitions/Def_CohCarrier_Inst.lean`
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
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import MathlibExt.NumberTheory.ModularForms.GammaH
public import MathlibExt.NumberTheory.ModularForms.AtkinLehnerSlash
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm TensorProduct

namespace CongruenceSubgroup

/-- The character `Gamma0 M →* (ZMod M)ˣ` is surjective: every unit is the
lower-right entry of a matrix in `Gamma0 M`. -/
public theorem gamma0Units_surjective (M : ℕ) [NeZero M] :
    Function.Surjective (gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ)
      - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k;
    (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]

private theorem gammaH_normal_in_gamma0 (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    ((GammaH M H).subgroupOf (Gamma0 M)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨_, hnH⟩ := (mem_GammaH_iff M).mp hn
  rw [mem_GammaH_iff]
  refine ⟨(g * n * g⁻¹).2, ?_⟩
  have e1 : (⟨((g * n * g⁻¹ : ↥(Gamma0 M)) : SL(2, ℤ)), (g * n * g⁻¹).2⟩ :
      ↥(Gamma0 M)) = g * n * g⁻¹ := Subtype.coe_eta _ _
  have e2 : (⟨(n : SL(2, ℤ)), n.2⟩ : ↥(Gamma0 M)) = n := Subtype.coe_eta _ _
  rw [e2] at hnH
  rw [e1, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact hnH

private theorem conj_mem_gammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (σ : Gamma0 M) (γ : ↥(GammaH M H)) :
    (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ ∈ GammaH M H := by
  obtain ⟨hγ0, _⟩ := (mem_GammaH_iff M).mp γ.2
  have hmem : (⟨(γ : SL(2, ℤ)), hγ0⟩ : Gamma0 M) ∈
      (GammaH M H).subgroupOf (Gamma0 M) := by
    rw [Subgroup.mem_subgroupOf]; exact γ.2
  have h := (gammaH_normal_in_gamma0 M H).conj_mem _ hmem σ
  rw [Subgroup.mem_subgroupOf] at h
  exact h

end CongruenceSubgroup

namespace ModularForm

public def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] public theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![a, b; 0, d] :=
  rfl

/-- The upper-triangular matrix `!![1, j; 0, p]` in `GL (Fin 2) ℝ`, with the
convention that it is the identity when `p = 0`. -/
public def heckeUpperMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

@[simp] public theorem val_heckeUpperMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeUpperMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeUpperMatrix, hp]

@[simp] public theorem heckeUpperMatrix_zero (j : ℕ) : heckeUpperMatrix 0 j = 1 := by
  simp [heckeUpperMatrix]

public theorem det_heckeUpperMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeUpperMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeUpperMatrix hp,
    Matrix.det_fin_two_of]
  ring

public theorem det_heckeUpperMatrix_pos (p j : ℕ) :
    0 < ((heckeUpperMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeUpperMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

public theorem σ_heckeUpperMatrix (p j : ℕ) :
    UpperHalfPlane.σ (heckeUpperMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeUpperMatrix_pos p j)]

/-- The `U`-type Hecke sum on functions on the upper half-plane: the sum of
the slashes by the matrices `!![1, j; 0, p]` for `0 ≤ j < p`. -/
public def heckeU (k : ℤ) (p : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeUpperMatrix p j

public theorem heckeU_def (k : ℤ) (p : ℕ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeUpperMatrix p j :=
  rfl

@[simp] public theorem heckeU_zero_left (k : ℤ) (f : ℍ → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

@[simp] public theorem heckeU_zero (k : ℤ) (p : ℕ) :
    heckeU k p (0 : ℍ → ℂ) = 0 := by
  simp [heckeU]

public theorem heckeU_add (k : ℤ) (p : ℕ) (f g : ℍ → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

public theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : ℍ → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeUpperMatrix,
    ContinuousAlgEquiv.refl_apply, Finset.smul_sum]

end ModularForm

namespace CuspForm

/-- Generators of the Hecke ring at level `M`, away from the set `S` of
primes: prime-to-level operators `T ℓ`, operators `U q` at primes dividing
the level, and diamond operators. -/
public inductive Gen (M : ℕ) (S : Set ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M)
  | U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
  | dia (d : (ZMod M)ˣ)

section GammaHOperators

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

/-- A chosen lift to `Gamma0 M` of a unit of `ZMod M`. -/
public def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CongruenceSubgroup.gamma0Units_surjective M d)

public theorem gamma0Units_gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) :
    CongruenceSubgroup.gamma0Units M (gammaLift M d) = d :=
  Classical.choose_spec (CongruenceSubgroup.gamma0Units_surjective M d)

/-- The unit of `ZMod M` attached to a prime not dividing `M`. -/
public def unitOfPrimeNotDvd {M ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    (ZMod M)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)

public theorem gammaLift_apply_11 {M ℓ : ℕ} [NeZero M] (hℓ : ℓ.Prime)
    (hℓM : ¬ ℓ ∣ M) :
    ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) :
      ZMod M) = ℓ := by
  have h := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M))
    (gamma0Units_gammaLift M (unitOfPrimeNotDvd hℓ hℓM))
  simp [unitOfPrimeNotDvd, CongruenceSubgroup.val_gamma0Units] at h
  exact h

private theorem mul_inv_mem_gammaH_of_gamma0Units_eq {H : Subgroup (ZMod M)ˣ}
    (ρ σ : Gamma0 M)
    (h : CongruenceSubgroup.gamma0Units M ρ = CongruenceSubgroup.gamma0Units M σ) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CongruenceSubgroup.GammaH M H := by
  rw [CongruenceSubgroup.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ : Gamma0 M)
      = ρ * σ⁻¹ := rfl
  rw [e1, map_mul, map_inv, h, mul_inv_cancel]
  exact one_mem H

private theorem slash_mapGL_eq_of_gamma0Units_eq (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (ρ σ : Gamma0 M)
    (h : CongruenceSubgroup.gamma0Units M ρ = CongruenceSubgroup.gamma0Units M σ)
    (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ
        ((ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_gammaH_of_gamma0Units_eq ρ σ h))]

/-- Stability of weight-`k` cusp forms for `GammaH M H` under slashing by
elements of `Gamma0 M`, at every cusp. When this holds, slashing by a lift
of a unit defines the diamond operator. -/
public def StableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) : Prop :=
  ∀ (σ : Gamma0 M) (f : CuspForm (CongruenceSubgroup.GammaH M H) k)
    (c : OnePoint ℝ),
    IsCusp c (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c
        (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) :
          GL (Fin 2) ℝ))) k

/-- Stability of weight-`k` cusp forms for `GammaH M H` under the `U q`
Hecke sum. -/
public def StableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (q : ℕ) : Prop :=
  ∀ f : CuspForm (CongruenceSubgroup.GammaH M H) k,
    (∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      (ModularForm.heckeU k q ⇑f) ∣[k] γ = ModularForm.heckeU k q ⇑f) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (ModularForm.heckeU k q ⇑f) ∧
    ∀ c : OnePoint ℝ,
      IsCusp c (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
        OnePoint.IsZeroAt c (ModularForm.heckeU k q ⇑f) k

/-- Stability of weight-`k` cusp forms for `GammaH M H` under the `T ℓ`
Hecke operator, for every choice of lift of `ℓ` to `Gamma0 M`. -/
public def StableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (ℓ : ℕ) : Prop :=
  ∀ (ρ : Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
    ∀ f : CuspForm (CongruenceSubgroup.GammaH M H) k,
      (∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ))) ∣[k] γ =
        ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ))) ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ))) ∧
      ∀ c : OnePoint ℝ,
        IsCusp c (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
          OnePoint.IsZeroAt c
            (ModularForm.heckeU k ℓ ⇑f +
              (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) :
                GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ))) k

/-- The diamond operator attached to a unit `d`, defined from a stability
witness: slash by a lift of `d` to `Gamma0 M`. -/
public def diamondLinHOf (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k where
  toFun f :=
    { toFun := ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
        rw [← SlashAction.slash_mul, ← map_mul,
          show (gammaLift M d : SL(2, ℤ)) * g =
            ((gammaLift M d : SL(2, ℤ)) * g * (gammaLift M d : SL(2, ℤ))⁻¹) *
              (gammaLift M d : SL(2, ℤ)) by rw [inv_mul_cancel_right],
          map_mul, SlashAction.slash_mul,
          SlashInvariantFormClass.slash_action_eq f _
            (Subgroup.mem_map_of_mem _
              (CongruenceSubgroup.conj_mem_gammaH M H (gammaLift M d) ⟨g, hg⟩))]
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' := fun hc => hD (gammaLift M d) f _ hc }
  map_add' f g := DFunLike.coe_injective <| by
    show (⇑(f + g)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))) +
      (⇑g ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show (⇑(c • f)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.IsGLPos.coe_smul]
    exact ModularForm.SL_smul_slash k (gammaLift M d : SL(2, ℤ)) ⇑f c

open Classical in
/-- The diamond operator attached to a unit `d`: slash by a lift of `d`
when cusp forms are stable under `Gamma0 M` slashes, and zero otherwise. -/
public def diamondLinH (k : ℤ) (d : (ZMod M)ˣ) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k :=
  if hD : StableD M H k then diamondLinHOf k hD d else 0

public theorem diamondLinH_eq (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    (diamondLinH k d : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) =
      diamondLinHOf k hD d := by
  rw [diamondLinH, dif_pos hD]

public theorem coe_diamondLinH_apply (k : ℤ) (hD : StableD M H k)
    (d : (ZMod M)ˣ) (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ⇑(diamondLinH k d f) =
      ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) :
        GL (Fin 2) ℝ)) := by
  rw [diamondLinH_eq k hD]; rfl

/-- The `U q` operator on cusp forms for `GammaH M H`, defined from a
stability witness. -/
public def heckeULinHOf (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k where
  toFun f :=
    { toFun := ModularForm.heckeU k q ⇑f
      slash_action_eq' := fun γ hγ => (hU f).1 γ hγ
      holo' := (hU f).2.1
      zero_at_cusps' := fun hc => (hU f).2.2 _ hc }
  map_add' f g := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(f + g) = ModularForm.heckeU k q ⇑f +
      ModularForm.heckeU k q ⇑g by
      rw [CuspForm.coe_add, ModularForm.heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(c • f) = c • ModularForm.heckeU k q ⇑f by
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul]

open Classical in
/-- The `U q` operator on cusp forms for `GammaH M H`: the `U q` Hecke sum
when cusp forms are stable under it, and zero otherwise. -/
public def heckeULinH (k : ℤ) (q : ℕ) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k :=
  if hU : StableU M H k q then heckeULinHOf k hU else 0

public theorem heckeULinH_eq (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    (heckeULinH k q : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) =
      heckeULinHOf k hU := by
  rw [heckeULinH, dif_pos hU]

public theorem coe_heckeULinH_apply (k : ℤ) {q : ℕ} (hU : StableU M H k q)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ⇑(heckeULinH k q f) = ModularForm.heckeU k q ⇑f := by
  rw [heckeULinH_eq k hU]; rfl

/-- The `T ℓ` operator on cusp forms for `GammaH M H`, defined from a
stability witness. -/
public def heckeTLinHOf (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hT : StableT M H k ℓ) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := fun f =>
      { toFun := ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
              ModularForm.heckeDiagMatrix ℓ))
        slash_action_eq' := fun γ hγ => (hT _ (gammaLift_apply_11 hℓ hℓM) f).1 γ hγ
        holo' := (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.1
        zero_at_cusps' := fun hc => (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.2 _ hc }
    map_add' := fun f g => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(f + g) + (⇑(f + g)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ)) +
        (ModularForm.heckeU k ℓ ⇑g + ⇑g ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.coe_add, ModularForm.heckeU_add, SlashAction.add_slash]
      abel
    map_smul' := fun c f => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(c • f) + (⇑(c • f)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        c • (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul, SlashAction.slash_mul,
        SlashAction.slash_mul, smul_add]
      congr 1
      rw [show (c • ⇑f) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ))) from
        ModularForm.SL_smul_slash k _ ⇑f c]
      simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix,
        ContinuousAlgEquiv.refl_apply] }

open Classical in
/-- The `T ℓ` operator on cusp forms for `GammaH M H`: the `T ℓ` Hecke
operator when cusp forms are stable under it, and zero otherwise. -/
public def heckeTLinH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k :=
  if hT : StableT M H k ℓ then heckeTLinHOf k hℓ hℓM hT else 0

public theorem heckeTLinH_eq (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hT : StableT M H k ℓ) :
    (heckeTLinH k hℓ hℓM : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) =
      heckeTLinHOf k hℓ hℓM hT := by
  rw [heckeTLinH, dif_pos hT]

public theorem coe_heckeTLinH_apply (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ⇑(heckeTLinH k hℓ hℓM f) = ModularForm.heckeU k ℓ ⇑f +
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  rw [heckeTLinH_eq k hℓ hℓM hT]; rfl

end GammaHOperators

section HeckeRing

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

/-- The Hecke operator attached to a generator of the Hecke ring. -/
public def heckeGenH (S : Set ℕ) (k : ℤ) :
    Gen M S → (CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k)
  | .T _ hℓ _ hℓM => heckeTLinH k hℓ hℓM
  | .U q _ _ => heckeULinH k q
  | .dia d => diamondLinH k d

@[simp] public theorem heckeGenH_T (S : Set ℕ) (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    heckeGenH (H := H) S k (.T ℓ hℓ hℓS hℓM) = heckeTLinH k hℓ hℓM :=
  rfl

@[simp] public theorem heckeGenH_U (S : Set ℕ) (k : ℤ) (q : ℕ) (hq : q.Prime)
    (hqM : q ∣ M) :
    heckeGenH (H := H) S k (.U q hq hqM) = heckeULinH k q :=
  rfl

@[simp] public theorem heckeGenH_dia (S : Set ℕ) (k : ℤ) (d : (ZMod M)ˣ) :
    heckeGenH (H := H) S k (.dia d) = diamondLinH k d :=
  rfl

/-- The Hecke ring at level `GammaH M H` and weight `k`: the subring of
endomorphisms of cusp forms generated by the `T`, `U`, and diamond
operators. -/
public def heckeRingH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    Subring (CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k) :=
  Subring.closure (Set.range (heckeGenH (H := H) (∅ : Set ℕ) k))

public theorem heckeGenH_mem_heckeRingH (S : Set ℕ) (k : ℤ) (g : Gen M S) :
    heckeGenH (H := H) S k g ∈ heckeRingH M H k := by
  refine Subring.subset_closure ?_
  cases g with
  | T ℓ hℓ hℓS hℓM => exact ⟨.T ℓ hℓ (Set.notMem_empty ℓ) hℓM, rfl⟩
  | U q hq hqM => exact ⟨.U q hq hqM, rfl⟩
  | dia d => exact ⟨.dia d, rfl⟩

end HeckeRing

section Lattice

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ)
  (W : ModularForm.AtkinLehnerDatum M p) (A : Subring ℂ)

/-- The cusp forms `f` such that, for every `t` in the Hecke ring, the
`q`-expansion coefficients of `t f` and of its Atkin-Lehner slash by `W` lie
in `A`: integrality at the cusp `∞` and at its image under the Atkin-Lehner
matrix of `W`. The datum `W` records a factorization `M = p * R` with `p` and
`R` coprime, so it exists only when `p` exactly divides `M`; it is an argument
rather than a quantified variable, so the condition cannot hold vacuously
for want of a datum. -/
public def twoCuspIntegralSet : Set (CuspForm (CongruenceSubgroup.GammaH M H) k) :=
  {f | ∀ t ∈ heckeRingH M H k, ∀ n : ℕ,
    ModularFormClass.qCoeff (⇑(t f)) n ∈ A ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W k ⇑(t f)) n ∈ A}

public theorem mem_twoCuspIntegralSet_iff
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    f ∈ twoCuspIntegralSet M H k p W A ↔
      ∀ t ∈ heckeRingH M H k, ∀ n : ℕ,
        ModularFormClass.qCoeff (⇑(t f)) n ∈ A ∧
          ModularFormClass.qCoeff (ModularForm.alSlash W k ⇑(t f)) n ∈ A :=
  Iff.rfl

-- Two Atkin-Lehner data at `p` share the bottom row `(M, p)` of their matrices, so the
-- matrices differ by a translation `!![1, m; 0, 1]` in `Gamma1 M`, under which cusp forms
-- for `GammaH M H` are invariant.
variable {M H k p} in
private theorem alSlash_congr_datum (W' : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ModularForm.alSlash W' k ⇑f = ModularForm.alSlash W k ⇑f := by
  have hR : W'.R = W.R :=
    (Nat.eq_of_mul_eq_mul_left W.q_pos (W.hM.symm.trans W'.hM)).symm
  have hb := W.bezout
  have hb' := W'.bezout
  rw [hR] at hb'
  let γ : SL(2, ℤ) :=
    ⟨!![1, W.a * W'.b - W'.a * W.b; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hγ : γ ∈ CongruenceSubgroup.GammaH M H :=
    CongruenceSubgroup.gamma1_le_gammaH M H
      ((CongruenceSubgroup.Gamma1_mem M γ).mpr ⟨by simp [γ], by simp [γ], by simp [γ]⟩)
  have hmat : W'.mat = (γ : Matrix (Fin 2) (Fin 2) ℤ) * W.mat := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ, ModularForm.AtkinLehnerDatum.mat, Matrix.mul_apply, Fin.sum_univ_two, hR]
    · linear_combination (↑p * W.a) * hb' - (↑p * W'.a) * hb
    · linear_combination W.b * hb' - W'.b * hb
  have hGL : W'.alGL = Matrix.SpecialLinearGroup.mapGL ℝ γ * W.alGL := by
    apply Units.ext
    rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe,
      ModularForm.AtkinLehnerDatum.alGL_coe, Matrix.SpecialLinearGroup.mapGL_coe_matrix, hmat,
      Matrix.map_mul]
    rfl
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, hGL, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)]

-- The set does not depend on the Bezout coefficients that `W` records.
public theorem twoCuspIntegralSet_congr_datum (W' : ModularForm.AtkinLehnerDatum M p) :
    twoCuspIntegralSet M H k p W A = twoCuspIntegralSet M H k p W' A :=
  Set.ext fun f => forall₂_congr fun t _ => forall_congr' fun n => by
    rw [alSlash_congr_datum W W' (t f)]

public theorem zero_mem_twoCuspIntegralSet :
    (0 : CuspForm (CongruenceSubgroup.GammaH M H) k) ∈ twoCuspIntegralSet M H k p W A := by
  intro t _ n
  have h0 : ModularFormClass.qCoeff (0 : ℍ → ℂ) n = 0 := by
    simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero]
  have hW : ModularForm.alSlash W k (0 : ℍ → ℂ) = 0 := by
    rw [ModularForm.alSlash_def]; exact SlashAction.zero_slash k _
  refine ⟨?_, ?_⟩
  · rw [map_zero, CuspForm.coe_zero, h0]; exact A.zero_mem
  · rw [map_zero, CuspForm.coe_zero, hW, h0]; exact A.zero_mem

variable {M H k p W A} in
public theorem heckeRingH_apply_mem_twoCuspIntegralSet
    {t : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k}
    (ht : t ∈ heckeRingH M H k)
    {f : CuspForm (CongruenceSubgroup.GammaH M H) k}
    (hf : f ∈ twoCuspIntegralSet M H k p W A) :
    t f ∈ twoCuspIntegralSet M H k p W A := by
  intro t' ht' n
  have hmul : t' * t ∈ heckeRingH M H k := (heckeRingH M H k).mul_mem ht' ht
  exact hf (t' * t) hmul n

/-- The two-cusp integral lattice: the `A`-span of the two-cusp integral
cusp forms inside all cusp forms. -/
public def twoCuspLattice :
    Submodule A (CuspForm (CongruenceSubgroup.GammaH M H) k) :=
  Submodule.span A (twoCuspIntegralSet M H k p W A)

public theorem twoCuspIntegralSet_subset_twoCuspLattice :
    twoCuspIntegralSet M H k p W A ⊆
      (twoCuspLattice M H k p W A : Set (CuspForm (CongruenceSubgroup.GammaH M H) k)) :=
  Submodule.subset_span

public theorem twoCuspLattice_congr_datum (W' : ModularForm.AtkinLehnerDatum M p) :
    twoCuspLattice M H k p W A = twoCuspLattice M H k p W' A :=
  congrArg (Submodule.span A) (twoCuspIntegralSet_congr_datum M H k p W A W')

variable {M H k p W A} in
public theorem heckeRingH_apply_mem_twoCuspLattice
    {t : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.GammaH M H) k}
    (ht : t ∈ heckeRingH M H k)
    {f : CuspForm (CongruenceSubgroup.GammaH M H) k}
    (hf : f ∈ twoCuspLattice M H k p W A) :
    t f ∈ twoCuspLattice M H k p W A := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (heckeRingH_apply_mem_twoCuspIntegralSet ht hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [show t (a • x) = a • t x from by
        rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smul]]
      exact Submodule.smul_mem _ a hx

variable {M H k p W A} in
/-- A Hecke operator, viewed as an endomorphism of the two-cusp lattice. -/
public def twoCuspEnd (t : heckeRingH M H k) :
    twoCuspLattice M H k p W A →ₗ[A] twoCuspLattice M H k p W A where
  toFun x := ⟨(t : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) x,
    heckeRingH_apply_mem_twoCuspLattice t.2 x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply, Subring.smul_def,
      LinearMap.map_smul])

@[simp] public theorem coe_twoCuspEnd_apply (t : heckeRingH M H k)
    (x : twoCuspLattice M H k p W A) :
    ((twoCuspEnd t x : twoCuspLattice M H k p W A) :
      CuspForm (CongruenceSubgroup.GammaH M H) k) =
      (t : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) x :=
  rfl

end Lattice

section Reduction

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ)
  (W : ModularForm.AtkinLehnerDatum M p) (A : Subring ℂ) (I : Ideal A)

/-- The reduction of the two-cusp lattice modulo an ideal `I` of `A`: the
quotient of the lattice by `I` times the lattice. -/
public def TwoCuspForms : Type :=
  twoCuspLattice M H k p W A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A))

public instance instAddCommGroupTwoCuspForms : AddCommGroup (TwoCuspForms M H k p W A I) :=
  inferInstanceAs (AddCommGroup
    (twoCuspLattice M H k p W A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A))))

public instance instModuleTwoCuspForms : Module A (TwoCuspForms M H k p W A I) :=
  inferInstanceAs (Module A
    (twoCuspLattice M H k p W A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A))))

public instance instModuleQuotientTwoCuspForms :
    Module (A ⧸ I) (TwoCuspForms M H k p W A I) :=
  inferInstanceAs (Module (A ⧸ I)
    (twoCuspLattice M H k p W A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A))))

public instance instIsScalarTowerSelfTwoCuspForms :
    IsScalarTower A A (TwoCuspForms M H k p W A I) :=
  inferInstanceAs (IsScalarTower A A
    (twoCuspLattice M H k p W A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A))))

public instance instIsScalarTowerTwoCuspForms :
    IsScalarTower A (A ⧸ I) (TwoCuspForms M H k p W A I) :=
  ⟨fun a b x => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact mul_smul a c x⟩

variable {M H k p W A} in
/-- Reduction of a lattice element modulo `I`: the quotient map. -/
public def twoCuspReduce :
    twoCuspLattice M H k p W A →ₗ[A] TwoCuspForms M H k p W A I :=
  (I • ⊤ : Submodule A (twoCuspLattice M H k p W A)).mkQ

public theorem twoCuspReduce_surjective :
    Function.Surjective (twoCuspReduce (M := M) (H := H) (k := k) (p := p)
      (W := W) (A := A) I) :=
  Submodule.mkQ_surjective _

variable {M H k p W A} in
public theorem ker_twoCuspReduce :
    LinearMap.ker (twoCuspReduce (M := M) (H := H) (k := k) (p := p) (W := W) (A := A) I) =
      (I • ⊤ : Submodule A (twoCuspLattice M H k p W A)) :=
  Submodule.ker_mkQ _

public theorem twoCuspReduce_eq_zero_iff (x : twoCuspLattice M H k p W A) :
    twoCuspReduce I x = 0 ↔ x ∈ (I • ⊤ : Submodule A (twoCuspLattice M H k p W A)) :=
  Submodule.Quotient.mk_eq_zero _

end Reduction

section IntTwoCusp

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)
  (W : ModularForm.AtkinLehnerDatum M p)

/-- The ideal of the integers generated by `p`, inside the bottom subring
of `ℂ`. -/
public abbrev intIdeal : Ideal (⊥ : Subring ℂ) :=
  Ideal.span {(p : (⊥ : Subring ℂ))}

public theorem natCast_mem_intIdeal : (p : (⊥ : Subring ℂ)) ∈ intIdeal p :=
  Ideal.subset_span rfl

/-- The mod-`p` two-cusp forms of weight two: the two-cusp lattice over the
integers, reduced modulo `p`. -/
public def IntTwoCuspForms : Type :=
  TwoCuspForms M H 2 p W (⊥ : Subring ℂ) (intIdeal p)

public instance instAddCommGroupIntTwoCuspForms :
    AddCommGroup (IntTwoCuspForms M H p W) :=
  inferInstanceAs (AddCommGroup
    (TwoCuspForms M H 2 p W (⊥ : Subring ℂ) (intIdeal p)))

/-- Every element of the reduction of the two-cusp lattice modulo `p` is
annihilated by `p`, so its exponent divides `p`. -/
public theorem IntTwoCuspForms.nsmul_eq_zero (x : IntTwoCuspForms M H p W) :
    p • x = 0 := by
  change p • (x : TwoCuspForms M H 2 p W (⊥ : Subring ℂ) (intIdeal p)) = 0
  obtain ⟨y, rfl⟩ := twoCuspReduce_surjective M H 2 p W (⊥ : Subring ℂ) (intIdeal p) x
  have h : p • twoCuspReduce (intIdeal p) y = twoCuspReduce (intIdeal p) (p • y) :=
    (map_nsmul (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (W := W)
      (A := (⊥ : Subring ℂ)) (intIdeal p)) p y).symm
  refine h.trans ((twoCuspReduce_eq_zero_iff (M := M) (H := H) (k := 2) (p := p) (W := W)
    (A := (⊥ : Subring ℂ)) (intIdeal p) (p • y)).mpr ?_)
  rw [← Nat.cast_smul_eq_nsmul (⊥ : Subring ℂ)]
  exact Submodule.smul_mem_smul (natCast_mem_intIdeal p) Submodule.mem_top

variable [Fact p.Prime]

public instance instModuleZModIntTwoCuspForms :
    Module (ZMod p) (IntTwoCuspForms M H p W) :=
  AddCommGroup.zmodModule (IntTwoCuspForms.nsmul_eq_zero M H p W)

/-- Reduction modulo `p` of a two-cusp lattice element, as an additive
map into the mod-`p` two-cusp forms. -/
public def intTwoCuspReduce :
    twoCuspLattice M H 2 p W (⊥ : Subring ℂ) →+ IntTwoCuspForms M H p W :=
  (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (W := W) (A := (⊥ : Subring ℂ))
    (intIdeal p)).toAddMonoidHom

public theorem intTwoCuspReduce_apply
    (x : twoCuspLattice M H 2 p W (⊥ : Subring ℂ)) :
    intTwoCuspReduce M H p W x =
      (twoCuspReduce (intIdeal p) x :
        TwoCuspForms M H 2 p W (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

public theorem intTwoCuspReduce_surjective :
    Function.Surjective (intTwoCuspReduce M H p W) :=
  twoCuspReduce_surjective M H 2 p W (⊥ : Subring ℂ) (intIdeal p)

end IntTwoCusp

section SpanTop

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (W : ModularForm.AtkinLehnerDatum M p)

private theorem span_intTwoCuspReduce_eq_top :
    Submodule.span (ZMod p) {y : IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          y = intTwoCuspReduce M H p W
            ⟨f, twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := intTwoCuspReduce_surjective M H p W x
  have htop : (Submodule.span (⊥ : Subring ℂ)
      (((↑) : ↥(twoCuspLattice M H 2 p W (⊥ : Subring ℂ)) →
        CuspForm (CongruenceSubgroup.GammaH M H) 2) ⁻¹'
        twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)) :
      Submodule (⊥ : Subring ℂ) ↥(twoCuspLattice M H 2 p W (⊥ : Subring ℂ))) = ⊤ :=
    Submodule.span_span_coe_preimage
  have hy : y ∈ Submodule.span (⊥ : Subring ℂ)
      (((↑) : ↥(twoCuspLattice M H 2 p W (⊥ : Subring ℂ)) →
        CuspForm (CongruenceSubgroup.GammaH M H) 2) ⁻¹'
        twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)) := by
    rw [htop]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
      obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
      have ha : a = (n : (⊥ : Subring ℂ)) := Subtype.ext (by exact hn.symm)
      rw [ha, Int.cast_smul_eq_zsmul, map_zsmul]
      exact zsmul_mem hy n

/-- After scalar extension to any field `K` over `ZMod p`, the reductions
modulo `p` of the two-cusp integral weight-two cusp forms span the whole
scalar extension of the mod-`p` two-cusp forms. -/
public theorem span_tmul_intTwoCuspReduce_eq_top
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] intTwoCuspReduce M H p W
            ⟨f, twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} = ⊤ := by
  have hset : {x : K ⊗[ZMod p] IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] intTwoCuspReduce M H p W
            ⟨f, twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} =
      TensorProduct.mk (ZMod p) K (IntTwoCuspForms M H p W) 1 ''
        {y : IntTwoCuspForms M H p W |
          ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
            (hf : f ∈ twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
            y = intTwoCuspReduce M H p W
              ⟨f, twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
  rw [hset, ← Submodule.baseChange_span, span_intTwoCuspReduce_eq_top,
    Submodule.baseChange_top]

end SpanTop

end CuspForm

end
