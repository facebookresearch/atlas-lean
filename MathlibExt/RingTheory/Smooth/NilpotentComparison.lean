/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map.lean`
and
`P2M/Sol/S_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map.lean`
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

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Algebra.Algebra.Equiv

@[expose] public section

universe u v w x

namespace SmoothNilpotentComparison

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type v} [CommRing A] [Algebra R A]

private def K (k : ℕ) : Submodule R A := (I ^ k) • ⊤

private theorem K_zero : K I (A := A) 0 = ⊤ := by
  rw [K, pow_zero, Ideal.one_eq_top, Submodule.top_smul]

private theorem K_one : K I (A := A) 1 = (I.map (algebraMap R A)).restrictScalars R := by
  rw [K, pow_one, Ideal.smul_top_eq_map]

private theorem mem_K_one_iff (a : A) : a ∈ K I (A := A) 1 ↔ a ∈ I.map (algebraMap R A) := by
  rw [K_one]; rfl

private theorem K_eq_bot_of_pow_eq_bot {n : ℕ} (hn : I ^ n = ⊥) : K I (A := A) n = ⊥ := by
  rw [K, hn, Submodule.bot_smul]

private theorem sub_mem_K_succ (θ : A →ₐ[R] A) (hθ : ∀ a, θ a - a ∈ I.map (algebraMap R A))
    {k : ℕ} {a : A} (ha : a ∈ K I k) : θ a - a ∈ K I (k + 1) := by
  rw [K] at ha
  induction ha using Submodule.smul_induction_on' with
  | smul r hr m _ =>
    have hθm : θ m - m ∈ K I (A := A) 1 := (mem_K_one_iff I _).mpr (hθ m)
    rw [K, pow_one] at hθm
    rw [map_smul, ← smul_sub, K, pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr hθm
  | add x _ y _ hx hy =>
    have h : θ (x + y) - (x + y) = (θ x - x) + (θ y - y) := by rw [map_add]; ring
    rw [h]
    exact Submodule.add_mem _ hx hy

private theorem bijective_of_forall_sub_mem (hI : IsNilpotent I) (θ : A →ₐ[R] A)
    (hθ : ∀ a, θ a - a ∈ I.map (algebraMap R A)) : Function.Bijective θ := by
  obtain ⟨n, hn⟩ := hI
  have hKn : K I (A := A) n = ⊥ := K_eq_bot_of_pow_eq_bot I hn
  constructor
  · intro a b hab
    have hab' : θ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    suffices h : ∀ k, a - b ∈ K I (A := A) k by
      have hmem := h n
      rw [hKn, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    intro k
    induction k with
    | zero => rw [K_zero]; exact Submodule.mem_top
    | succ k ih =>
      have hstep := sub_mem_K_succ I θ hθ ih
      rw [hab', zero_sub] at hstep
      simpa using Submodule.neg_mem _ hstep
  · intro b
    suffices h : ∀ k, ∃ a, b - θ a ∈ K I (A := A) k by
      obtain ⟨a, ha⟩ := h n
      rw [hKn, Submodule.mem_bot, sub_eq_zero] at ha
      exact ⟨a, ha.symm⟩
    intro k
    induction k with
    | zero => exact ⟨0, by rw [K_zero]; exact Submodule.mem_top⟩
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + (b - θ a), ?_⟩
      have hstep := sub_mem_K_succ I θ hθ ha
      have h : b - θ (a + (b - θ a)) = -(θ (b - θ a) - (b - θ a)) := by
        rw [map_add]; ring
      rw [h]
      exact Submodule.neg_mem _ hstep

end SmoothNilpotentComparison

namespace Algebra.FormallySmooth

/-- Two formally smooth algebras with surjective maps to a common algebra,
whose kernels are the extension of the same nilpotent ideal, are isomorphic
over that common algebra. -/
public theorem exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {A : Type v} {A' : Type w} {A₀ : Type x} [CommRing A] [CommRing A'] [CommRing A₀]
    [Algebra R A] [Algebra R A'] [Algebra R A₀]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
    (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
    (hg : Function.Surjective g) (hg' : Function.Surjective g')
    (hkg : RingHom.ker g = I.map (algebraMap R A))
    (hkg' : RingHom.ker g' = I.map (algebraMap R A')) :
    ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g := by
  have hI₀ := hI
  obtain ⟨n, hn⟩ := hI
  have hnil : IsNilpotent (RingHom.ker (g : A →+* A₀)) := by
    refine ⟨n, ?_⟩
    rw [RingHom.ker_coe_toRingHom, hkg, ← Ideal.map_pow, hn]
    simp
  have hnil' : IsNilpotent (RingHom.ker (g' : A' →+* A₀)) := by
    refine ⟨n, ?_⟩
    rw [RingHom.ker_coe_toRingHom, hkg', ← Ideal.map_pow, hn]
    simp
  let φ : A →ₐ[R] A' := Algebra.FormallySmooth.liftOfSurjective g g' hg' hnil'
  have hφ : g'.comp φ = g := Algebra.FormallySmooth.comp_liftOfSurjective g g' hg' hnil'
  let ψ : A' →ₐ[R] A := Algebra.FormallySmooth.liftOfSurjective g' g hg hnil
  have hψ : g.comp ψ = g' := Algebra.FormallySmooth.comp_liftOfSurjective g' g hg hnil
  have h1 : Function.Bijective (ψ.comp φ) := by
    refine SmoothNilpotentComparison.bijective_of_forall_sub_mem I hI₀ _ (fun a => ?_)
    rw [← hkg, RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.comp_apply]
    change (g.comp ψ) (φ a) = g a
    rw [hψ, ← AlgHom.comp_apply, hφ]
  have h2 : Function.Bijective (φ.comp ψ) := by
    refine SmoothNilpotentComparison.bijective_of_forall_sub_mem I hI₀ _ (fun a => ?_)
    rw [← hkg', RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.comp_apply]
    change (g'.comp φ) (ψ a) = g' a
    rw [hφ, ← AlgHom.comp_apply, hψ]
  have hφbij : Function.Bijective φ :=
    ⟨Function.Injective.of_comp (f := ψ) h1.1, Function.Surjective.of_comp (g := ψ) h2.2⟩
  exact ⟨AlgEquiv.ofBijective φ hφbij, hφ⟩

end Algebra.FormallySmooth
