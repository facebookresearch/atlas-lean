/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_DoubleComplex.lean`
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

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring

/-!
# Bounded first-quadrant double complexes of modules

A lightweight, `ℕ × ℕ`-graded double complex of `R`-modules whose horizontal and
vertical differentials commute, bounded in both directions, together with its
total complex `Tot n = ∏_{p + q = n} C p q` and total differential
`dTot = dH + (-1)^p dV`.

Mathlib's `HomologicalComplex₂` and `HomologicalComplex₂.total` cover the same mathematics
categorically. This file keeps the elementwise presentation because the Čech double complexes
built on it (`AlgebraicGeometry.OModulePresheaf.biCech`) are stated with explicit
families of sections, and the degree-zero comparison results downstream are statements
about those families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex

/-- A first-quadrant double complex of `R`-modules with commuting differentials,
vanishing outside the square `[0, N) × [0, N)`. -/
structure Bounded (R : Type u) [CommRing R] where
  /-- The term in bidegree `(p, q)`. -/
  C : ℕ → ℕ → Type u
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  [modR : ∀ p q, Module R (C p q)]
  /-- The horizontal differential. -/
  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q
  /-- The vertical differential. -/
  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0
  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q
  /-- A bound on the support. -/
  N : ℕ
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

/-- The bidegrees on the `n`-th antidiagonal. -/
abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The `n`-th term of the total complex. -/
abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

/-- The horizontal contribution to the total differential, into one bidegree. -/
def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

/-- The vertical contribution to the total differential, into one bidegree. -/
def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

/-- The total differential `dH + (-1)^p dV`. -/
def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

theorem dTot_apply_zero_succ {n q' : ℕ} (h : 0 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(0, q' + 1), h⟩ = D.dV 0 q' (c ⟨(0, q'), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, dTotH, dTotV,
    LinearMap.comp_apply, LinearMap.proj_apply, pow_zero, one_smul, zero_add]

theorem dTot_apply_succ_zero {n p' : ℕ} (h : p' + 1 + 0 = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, 0), h⟩ = D.dH p' 0 (c ⟨(p', 0), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, dTotH, dTotV,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_zero, add_zero]

theorem dTot_apply_succ_succ {n p' q' : ℕ} (h : p' + 1 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, q' + 1), h⟩
      = D.dH p' (q' + 1) (c ⟨(p', q' + 1), by omega⟩)
        + ((-1 : ℤ) ^ (p' + 1)) • D.dV (p' + 1) q' (c ⟨(p' + 1, q'), by omega⟩) := by
  rfl

theorem dTot_comp_dTot (D : Bounded R) (n : ℕ) :
    dTot D (n + 1) ∘ₗ dTot D n = 0 := by
  refine LinearMap.ext fun c => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  match pp, q, h with
  | 0, 0, h => omega
  | 0, q' + 1, h =>
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    rw [dTot_apply_zero_succ, dTot_apply_zero_succ,
      ← LinearMap.comp_apply, D.dV_sq, LinearMap.zero_apply]
  | p' + 1, 0, h =>
    obtain ⟨p'', rfl⟩ : ∃ p'', p' = p'' + 1 := ⟨p' - 1, by omega⟩
    rw [dTot_apply_succ_zero, dTot_apply_succ_zero,
      ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply]
  | p' + 1, q' + 1, h =>
    rw [dTot_apply_succ_succ]
    have hH : D.dH p' (q' + 1) (dTot D n c ⟨(p', q' + 1), by omega⟩)
        = ((-1 : ℤ) ^ p') • D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases p' with _ | p''
      · rw [dTot_apply_zero_succ, pow_zero, one_smul]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply, zero_add]
    have hV : D.dV (p' + 1) q' (dTot D n c ⟨(p' + 1, q'), by omega⟩)
        = D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases q' with _ | q''
      · rw [dTot_apply_succ_zero]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          show D.dV (p' + 1) (q'' + 1) (D.dV (p' + 1) q'' (c ⟨(p' + 1, q''), by omega⟩)) = 0 from
            LinearMap.congr_fun (D.dV_sq (p' + 1) q'') _, smul_zero, add_zero]
    rw [hH, hV,
      show D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩))
        = D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) from
        LinearMap.congr_fun (D.dHV_comm p' q') _,
      ← add_smul, show ((-1:ℤ)^p' + (-1)^(p'+1)) = 0 from by ring, zero_smul]

end DTotGeneric

end DoubleComplex
