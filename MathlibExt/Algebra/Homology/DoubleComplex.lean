/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_DoubleComplex.lean`
and
`Theorems/Thm_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH.lean
and
`P2M/Sol/S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH.lean`
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

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

@[expose] public section

universe u

namespace DoubleComplex

structure Bounded (R : Type u) [CommRing R] where

  C : ℕ → ℕ → Type u
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  [modR : ∀ p q, Module R (C p q)]

  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q

  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0

  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q

  N : ℕ
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

theorem dTot_apply_zero_succ {n q' : ℕ} (h : 0 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(0, q' + 1), h⟩ = D.dV 0 q' (c ⟨(0, q'), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, pow_zero, one_smul, zero_add]

theorem dTot_apply_succ_zero {n p' : ℕ} (h : p' + 1 + 0 = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, 0), h⟩ = D.dH p' 0 (c ⟨(p', 0), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
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

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          show D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

section Proof


variable {R : Type u} [CommRing R] (D : Bounded R)

private theorem eq_zero_of_neg_one_pow_smul_eq_zero {M : Type u} [AddCommGroup M] (m : ℕ) (x : M)
    (hx : ((-1 : ℤ) ^ m) • x = 0) : x = 0 := by
  rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] at hx <;> simpa using hx

private theorem neg_one_pow_smul_neg_one_pow_smul {M : Type u} [AddCommGroup M] (m : ℕ) (x : M) :
    ((-1 : ℤ) ^ m) • (((-1 : ℤ) ^ m) • x) = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

open Classical in

private theorem dTot_single_vert {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q')
    (h : k + (q' + 1) = n + 1) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) ⟨(k, q' + 1), h⟩
      = ((-1 : ℤ) ^ k) • D.dV k q' w := by
  cases k with
  | zero =>
    rw [dTot_apply_zero_succ, pow_zero, one_smul]
    congr 1
    exact Pi.single_eq_same _ _
  | succ k' =>
    rw [dTot_apply_succ_succ]
    have h1 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k', q' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg (fun i : Diag n => i.1.1) e
        simp only at this
        omega) _
    have h2 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k' + 1, q'), by omega⟩ = w :=
      Pi.single_eq_same _ _
    rw [h1, h2, map_zero, zero_add]

open Classical in

private theorem dTot_single_eq_zero {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q') (j : Diag (n + 1))
    (hj : j.1.1 ≤ k) (hj' : ¬ (j.1.1 = k ∧ j.1.2 = q' + 1)) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) j = 0 := by
  obtain ⟨⟨p, r⟩, hpr⟩ := j
  simp only at hj hj' hpr
  rcases p with _ | p' <;> rcases r with _ | r'
  · exfalso; omega
  · rw [dTot_apply_zero_succ]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(0, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_zero]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', 0), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_succ]
    have e1 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', r' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    have e2 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p' + 1, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e1, e2, map_zero, map_zero, smul_zero, add_zero]

open Classical in

private theorem stair (n : ℕ)
    (hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0)
    (hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z)
    (c : Tot D (n + 1)) (hc : dTot D (n + 1) c = 0) (k : ℕ) :
    ∃ b : Tot D n, ∀ i : Diag (n + 1), i.1.1 < k → (c - dTot D n b) i = 0 := by
  induction k with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hk : n + 1 < k
    · exact ⟨b, fun i hi => hb i (by have := i.2; omega)⟩
    obtain ⟨q, hq⟩ : ∃ q, k + q = n + 1 := ⟨n + 1 - k, by omega⟩
    have hcyc : dTot D (n + 1) (c - dTot D n b) = 0 := by
      rw [map_sub, hc, zero_sub, neg_eq_zero]
      simpa using LinearMap.congr_fun (dTot_comp_dTot D n) b
    have KV : D.dV k q ((c - dTot D n b) ⟨(k, q), hq⟩) = 0 := by
      cases k with
      | zero =>
        have e := congrFun hcyc ⟨(0, q + 1), by omega⟩
        rw [dTot_apply_zero_succ, Pi.zero_apply] at e
        exact e
      | succ k' =>
        have e := congrFun hcyc ⟨(k' + 1, q + 1), by omega⟩
        rw [dTot_apply_succ_succ, Pi.zero_apply, hb ⟨(k', q + 1), by omega⟩ (Nat.lt_succ_self _),
          map_zero, zero_add] at e
        exact eq_zero_of_neg_one_pow_smul_eq_zero _ _ e
    cases q with
    | zero =>
      refine ⟨b, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact hb i hlt
      · have hi2 : i = ⟨(k, 0), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2]
        exact hcol0 k _ KV
    | succ q' =>
      obtain ⟨y, hy⟩ := hcolS k q' _ KV
      refine ⟨b + Pi.single (⟨(k, q'), by omega⟩ : Diag n) (((-1 : ℤ) ^ k) • y), fun i hi => ?_⟩
      rw [map_add, ← sub_sub, Pi.sub_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · rw [hb i hlt, dTot_single_eq_zero D _ _ i hlt.le (fun h => by omega), sub_zero]
      · have hi2 : i = ⟨(k, q' + 1), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2, dTot_single_vert D, map_zsmul, neg_one_pow_smul_neg_one_pow_smul, hy, sub_self]

/-- If every column cohomology group of a bounded double complex vanishes
(as a subsingleton), then every total cohomology group vanishes. -/
theorem subsingleton_HTot_of_forall_subsingleton_colH
    (h : ∀ p q : ℕ, Subsingleton (colH D p q)) (n : ℕ) :
    Subsingleton (HTot D n) := by
  classical
  have hcol : ∀ (p q : ℕ) (z : LinearMap.ker (D.dV p q)), z ∈ colB D p q := fun p q z =>
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0 := fun p z hz => by
    have e := hcol p 0 ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (⊥ : Submodule R _) at e
    rw [Submodule.mem_bot] at e
    exact congrArg Subtype.val e
  have hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z :=
    fun p q' z hz => by
    have e := hcol p (q' + 1) ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype at e
    rw [Submodule.mem_comap, LinearMap.mem_range] at e
    exact e
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨c, hc⟩ -
  cases n with
  | zero =>
    change (⟨c, hc⟩ : LinearMap.ker (dTot D 0)) ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    show c = 0
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hp : p = 0 := by simp only at hpq; omega
    have hq : q = 0 := by simp only at hpq; omega
    subst hp hq
    have e := congrFun (LinearMap.mem_ker.1 hc) ⟨(0, 1), by omega⟩
    rw [dTot_apply_zero_succ, Pi.zero_apply] at e
    exact hcol0 0 _ e
  | succ n =>
    obtain ⟨b, hb⟩ := stair D n hcol0 hcolS c (LinearMap.mem_ker.1 hc) (n + 2)
    change (⟨c, hc⟩ : LinearMap.ker (dTot D (n + 1))) ∈
      (LinearMap.range (dTot D n)).comap (LinearMap.ker (dTot D (n + 1))).subtype
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨b, ?_⟩
    show dTot D n b = c
    have e : c - dTot D n b = 0 := funext fun i => hb i (by have := i.2; omega)
    exact (sub_eq_zero.1 e).symm


end Proof

end DoubleComplex
