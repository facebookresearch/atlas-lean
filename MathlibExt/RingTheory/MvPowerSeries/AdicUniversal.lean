/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_algHom_apply_X_eq.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_algHom_apply_X_eq.lean`
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

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.SModEq.Basic

/-!
# Universal property of multivariate power series over adically complete rings

For a finite index type and an adically complete target algebra, a choice of
elements of the ideal in the target determines an algebra map from the
multivariate power series ring sending each variable to the chosen element.
-/

@[expose] public section

universe u v w

namespace MvPowerSeriesAdicUniversalAux

open MvPowerSeries

variable {σ : Type w} (𝒪 : Type u) {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]

private theorem smodEq_pow_smul_top_iff (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

section Construction

variable [Finite σ] (a : σ → A) (I : Ideal A) (ha : ∀ i, a i ∈ I)

include ha
omit [Finite σ] in
private theorem idealOfVars_pow_le (k : ℕ) :
    MvPolynomial.idealOfVars σ 𝒪 ^ k ≤
      (I ^ k).comap (MvPolynomial.aeval (R := 𝒪) a).toRingHom := by
  refine le_trans (Ideal.pow_right_mono ?_ k) (Ideal.le_comap_pow _ k)
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using ha i

private noncomputable def evalTrunc (k : ℕ) : MvPowerSeries σ 𝒪 →+* A ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (MvPolynomial.aeval (R := 𝒪) a).toRingHom
    (idealOfVars_pow_le 𝒪 a I ha k)).comp (truncTotalAlgHom σ 𝒪 k).toRingHom

private theorem evalTrunc_apply (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    evalTrunc 𝒪 a I ha k p =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  simp [evalTrunc]

private theorem evalTrunc_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow I h).comp (evalTrunc 𝒪 a I ha l) = evalTrunc 𝒪 a I ha k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, evalTrunc_apply, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact idealOfVars_pow_le 𝒪 a I ha k (truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl p)

variable [IsAdicComplete I A]

private noncomputable def lift : MvPowerSeries σ 𝒪 →+* A :=
  IsAdicComplete.liftRingHom I (evalTrunc 𝒪 a I ha) (fun h => evalTrunc_compat 𝒪 a I ha h)

private theorem mk_lift (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    Ideal.Quotient.mk (I ^ k) (lift 𝒪 a I ha p) =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  rw [lift, IsAdicComplete.mk_liftRingHom, evalTrunc_apply]

private theorem lift_coe (P : MvPolynomial σ 𝒪) :
    lift 𝒪 a I ha (P : MvPowerSeries σ 𝒪) = MvPolynomial.aeval (R := 𝒪) a P := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, ← Ideal.Quotient.eq, mk_lift, Ideal.Quotient.eq, ← map_sub]
  refine idealOfVars_pow_le 𝒪 a I ha k ?_
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx, MvPolynomial.coeff_coe]

private theorem lift_X (i : σ) : lift 𝒪 a I ha (X i) = a i := by
  rw [← MvPolynomial.coe_X, lift_coe, MvPolynomial.aeval_X]

private theorem lift_C (c : 𝒪) : lift 𝒪 a I ha (C c) = algebraMap 𝒪 A c := by
  rw [← MvPolynomial.coe_C, lift_coe, MvPolynomial.aeval_C]

private noncomputable def liftAlgHom : MvPowerSeries σ 𝒪 →ₐ[𝒪] A :=
  { lift 𝒪 a I ha with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_ofClass]
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, lift_C] }

private theorem liftAlgHom_X (i : σ) : liftAlgHom 𝒪 a I ha (X i) = a i := lift_X 𝒪 a I ha i

end Construction

end MvPowerSeriesAdicUniversalAux

namespace MvPowerSeries

/-- An algebra map out of a multivariate power series ring into an adically
complete target is determined by the images of the variables in the ideal. -/
public theorem exists_algHom_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w}
    [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A]
    (a : σ → A) (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  ⟨MvPowerSeriesAdicUniversalAux.liftAlgHom 𝒪 a I ha,
    fun i => MvPowerSeriesAdicUniversalAux.liftAlgHom_X 𝒪 a I ha i⟩

end MvPowerSeries
