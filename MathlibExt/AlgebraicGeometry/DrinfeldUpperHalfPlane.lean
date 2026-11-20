/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_DrinfeldUpperHalfPlane.lean`
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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

open scoped MatrixGroups Topology

namespace DrinfeldUpperHalfPlane

section Moebius

variable (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]

noncomputable scoped instance (priority := low) glAction [DecidableEq K] : MulAction (GL (Fin 2)
  K₀) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.GeneralLinearGroup.map (algebraMap K₀ K))

theorem gl_smul_def [DecidableEq K] (g : GL (Fin 2) K₀) (x : OnePoint K) :
    g • x = (Matrix.GeneralLinearGroup.map (algebraMap K₀ K) g) • x := rfl

theorem scalar_smul_eq [DecidableEq K] (u : K₀ˣ) (x : OnePoint K) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀) • x = x := by
  have h10 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h00 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 0 = algebraMap K₀ K (u : K₀)
        := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h11 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 1 = algebraMap K₀ K (u : K₀)
        := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h01 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 1 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hu : algebraMap K₀ K (u : K₀) ≠ 0 := by
    simp
  induction x using OnePoint.rec with
  | infty => rw [gl_smul_def, OnePoint.smul_infty_eq_ite, if_pos h10]
  | coe k =>
    rw [gl_smul_def, OnePoint.smul_some_eq_ite, h10, h11, h00, h01, zero_mul, zero_add, if_neg hu,
      add_zero,
      mul_div_cancel_left₀ _ hu]

noncomputable scoped instance (priority := low) pglAction [DecidableEq K] : MulAction PGL(2, K₀)
  (OnePoint K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL (fun u x => scalar_smul_eq K₀ K u x)

theorem mk_smul_eq [DecidableEq K] (g : GL (Fin 2) K₀) (x : OnePoint K) :
    Matrix.ProjGenLinGroup.mk g • x = g • x :=
  Matrix.ProjGenLinGroup.mk_smul _ g x

def moebius (g : GL (Fin 2) K₀) (z : K) : K :=
  (algebraMap K₀ K (g 0 0) * z + algebraMap K₀ K (g 0 1)) / (algebraMap K₀ K (g 1 0) * z +
    algebraMap K₀ K (g 1 1))

variable {K} in

def toAffine (x : OnePoint K) : K := OnePoint.elim x 0 id

@[simp] theorem toAffine_coe (z : K) : toAffine (z : OnePoint K) = z := rfl
@[simp] theorem toAffine_infty : toAffine (OnePoint.infty : OnePoint K) = 0 := rfl

variable {K} in

noncomputable def pmoebius [DecidableEq K] (g : PGL(2, K₀)) (z : K) : K := toAffine (g • (z :
  OnePoint K))

variable {K} in
theorem pmoebius_mk [DecidableEq K] (g : GL (Fin 2) K₀) (z : K)
    (hz : algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1) ≠ 0) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z = moebius K₀ K g z := by
  rw [pmoebius, mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
  simp only [Matrix.GeneralLinearGroup.map_apply] at *
  rw [if_neg (by simpa using hz)]
  rfl

end Moebius

def upperHalfPlane (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K] : Set K :=
  (Set.range (algebraMap K₀ K))ᶜ

theorem mem_upperHalfPlane_iff (K₀ : Type*) [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] (z :
  K) :
    z ∈ upperHalfPlane K₀ K ↔ ∀ x : K₀, algebraMap K₀ K x ≠ z := by
  simp [upperHalfPlane]

section OmegaAction

variable (K₀ : Type*) [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]

theorem moebius_denom_ne_zero_of_mem {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀) :
    algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1) ≠ 0 := by
  rw [mem_upperHalfPlane_iff] at hz
  intro h
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      apply g.det_ne_zero
      rw [Matrix.det_fin_two]
      simp [hc, hd]
    rw [hc, map_zero, zero_mul, zero_add] at h
    exact hd ((algebraMap K₀ K).injective (by rw [h, map_zero]))
  · have hc' : algebraMap K₀ K (g 1 0) ≠ 0 := by
      intro h'; exact hc ((algebraMap K₀ K).injective (by rw [h', map_zero]))
    apply hz (-(g 1 1) / g 1 0)
    rw [map_div₀, map_neg, div_eq_iff hc', eq_comm, ← sub_eq_zero]
    rw [← h]; ring

variable [DecidableEq K]

theorem coe_pmoebius_of_mem {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : PGL(2, K₀)) :
    ((pmoebius K₀ g z : K) : OnePoint K) = g • (z : OnePoint K) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    rw [pmoebius, mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.map_apply]
    rw [if_neg (moebius_denom_ne_zero_of_mem K₀ hz g)]
    rfl

theorem pmoebius_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : PGL(2, K₀)) :
    pmoebius K₀ g z ∈ upperHalfPlane K₀ K := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    have hden := moebius_denom_ne_zero_of_mem K₀ hz g
    rw [pmoebius_mk K₀ g z hden, mem_upperHalfPlane_iff]
    rw [mem_upperHalfPlane_iff] at hz
    intro t ht
    rw [moebius, eq_div_iff hden] at ht

    have key : algebraMap K₀ K (g 0 0 - t * g 1 0) * z = algebraMap K₀ K (t * g 1 1 - g 0 1) := by
      rw [map_sub, map_sub, map_mul, map_mul]
      linear_combination -ht
    by_cases h0 : g 0 0 - t * g 1 0 = 0
    · have h1 : t * g 1 1 - g 0 1 = 0 := by
        have := key
        rw [h0, map_zero, zero_mul] at this
        exact ((algebraMap K₀ K).injective (by rw [← this, map_zero])).symm
      apply g.det_ne_zero
      rw [Matrix.det_fin_two]
      have ha : g 0 0 = t * g 1 0 := sub_eq_zero.mp h0
      have hb : g 0 1 = t * g 1 1 := (sub_eq_zero.mp h1).symm
      show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 0
      rw [ha, hb]; ring
    · apply hz ((t * g 1 1 - g 0 1) / (g 0 0 - t * g 1 0))
      have h0' : algebraMap K₀ K (g 0 0 - t * g 1 0) ≠ 0 := by
        intro h'; exact h0 ((algebraMap K₀ K).injective (by rw [h', map_zero]))
      rw [map_div₀, div_eq_iff h0', ← key, mul_comm]

@[simp] theorem pmoebius_one (z : K) : pmoebius K₀ (1 : PGL(2, K₀)) z = z := by
  rw [pmoebius, one_smul, toAffine_coe]

theorem pmoebius_mul {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g h : PGL(2, K₀)) :
    pmoebius K₀ (g * h) z = pmoebius K₀ g (pmoebius K₀ h z) := by
  rw [pmoebius, pmoebius, mul_smul, coe_pmoebius_of_mem K₀ hz h]

end OmegaAction

section Theta

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] {G : Type*} [Group G]

def crossRatio (z z₀ x y : K) : K := ((z - x) * (z₀ - y)) / ((z - y) * (z₀ - x))

noncomputable def thetaFactor [DecidableEq K] (ρ : G →* PGL(2, K₀)) (a b z₀ z : K) (γ : G) : K :=
  crossRatio z z₀ (pmoebius K₀ (ρ γ) a) (pmoebius K₀ (ρ γ) b)

noncomputable def theta [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a b z₀ : K) (z
  : K) : K :=
  ∏' γ : G, thetaFactor ρ a b z₀ z γ

def ThetaMultipliable [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a b z₀ z : K) :
  Prop :=
  Multipliable (thetaFactor ρ a b z₀ z)

def IsAutomorphicWithMultiplier [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K) (c :
  G →* Kˣ) : Prop :=
  ∀ γ : G, ∀ z ∈ Ω, f (pmoebius K₀ (ρ γ) z) = (c γ : K) * f z

def IsInvariant [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K) : Prop :=
  IsAutomorphicWithMultiplier ρ Ω f 1

noncomputable def period [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a z₀ : K) (α
  β : G) : K :=
  theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀)

end Theta

end DrinfeldUpperHalfPlane
