/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Filtration

/-!
# Total degree on enveloping Chevalley–Eilenberg terms

The filtration counts enveloping degree plus exterior degree in the
exterior-first regular-coefficient terms. Its stages are submodules over the
ground ring. Every tensor lies in a finite stage, and stages below the
exterior degree vanish.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The total-degree filtration on the original enveloping coefficient CE
carrier. The degree condition includes exterior degree and has no truncated
subtraction at stages smaller than that degree. -/
def envelopingFiltration (p n : ℕ) :
    Submodule R ((⋀[R]^n L) ⊗[R] regularCoefficients R L) :=
  Submodule.span R {z | ∃ q : ℕ, ∃ a : Fin n → L,
    ∃ u : regularCoefficients R L,
      q + n ≤ p ∧ u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q ∧
        exteriorPower.ιMulti R n a ⊗ₜ[R] u = z}

theorem envelopingFiltration_mono (n : ℕ) :
    Monotone (fun p => envelopingFiltration R L p n) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨r, a, u, hra, hu, rfl⟩
  exact ⟨r, a, u, hra.trans hpq, hu, rfl⟩

/-- A decomposable chain has its total enveloping/exterior degree. -/
theorem ιMulti_tmul_mem_envelopingFiltration
    (p n q : ℕ) (a : Fin n → L) (u : regularCoefficients R L)
    (hp : q + n ≤ p)
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    exteriorPower.ιMulti R n a ⊗ₜ[R] u ∈ envelopingFiltration R L p n :=
  Submodule.subset_span ⟨q, a, u, hp, hu, rfl⟩

/-- The same bound holds for arbitrary exterior vectors, using the native
span of decomposable wedges instead of a new CE or exterior construction. -/
theorem tmul_mem_envelopingFiltration
    (p n q : ℕ) (w : ⋀[R]^n L) (u : regularCoefficients R L)
    (hp : q + n ≤ p)
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    w ⊗ₜ[R] u ∈ envelopingFiltration R L p n := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, rfl⟩ := hw
      exact ιMulti_tmul_mem_envelopingFiltration R L p n q a u hp hu
  | zero =>
      rw [TensorProduct.zero_tmul]
      exact (envelopingFiltration R L p n).zero_mem
  | add w z hw hz ihw ihz =>
      rw [TensorProduct.add_tmul]
      exact (envelopingFiltration R L p n).add_mem ihw ihz
  | smul r w hw ih =>
      rw [← TensorProduct.smul_tmul']
      exact (envelopingFiltration R L p n).smul_mem r ih

/-- Stages below the exterior degree vanish. -/
theorem envelopingFiltration_eq_bot_of_lt (p n : ℕ) (hp : p < n) :
    envelopingFiltration R L p n = ⊥ := by
  have hempty : {z : (⋀[R]^n L) ⊗[R] regularCoefficients R L |
      ∃ q : ℕ, ∃ a : Fin n → L, ∃ u : regularCoefficients R L,
        q + n ≤ p ∧ u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q ∧
          exteriorPower.ιMulti R n a ⊗ₜ[R] u = z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨q, a, u, hq, hu, hz⟩ := hz
    omega
  rw [envelopingFiltration, hempty, Submodule.span_empty]

theorem envelopingFiltration_zero_succ (n : ℕ) :
    envelopingFiltration R L 0 (n + 1) = ⊥ :=
  envelopingFiltration_eq_bot_of_lt R L 0 (n + 1) (Nat.zero_lt_succ n)

/-- Every enveloping CE chain has a finite total filtration stage,
without requiring a finite basis or a finite-dimensional Lie algebra. -/
theorem envelopingFiltration_exhaustive (n : ℕ)
    (z : (⋀[R]^n L) ⊗[R] regularCoefficients R L) :
    ∃ p : ℕ, z ∈ envelopingFiltration R L p n := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (envelopingFiltration R L 0 n).zero_mem⟩
  | tmul w u =>
      obtain ⟨q, hq⟩ := UniversalEnvelopingAlgebra.degreeFiltration_exhaustive R L u
      exact ⟨q + n, tmul_mem_envelopingFiltration R L (q + n) n q w u le_rfl hq⟩
  | add z w hz hw =>
      obtain ⟨p, hp⟩ := hz
      obtain ⟨q, hq⟩ := hw
      exact ⟨max p q, (envelopingFiltration R L (max p q) n).add_mem
        (envelopingFiltration_mono R L n (le_max_left p q) hp)
        (envelopingFiltration_mono R L n (le_max_right p q) hq)⟩

end ChevalleyEilenberg
