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
# The total-degree filtration on enveloping chains

Let `R` be a commutative ring and `L` an `R`-Lie algebra. In degree `n`, the regular-
coefficient chain term is `⋀ⁿ[R] L ⊗[R] U_R(L)`, with the exterior factor first.

The stage `F_p` is the `R`-span of `(v₀ ∧ ⋯ ∧ v_(n-1)) ⊗ u` for which `u` has enveloping
degree at most `q` and `q+n ≤ p`. These stages are increasing and exhaustive, and `F_p = 0`
when `p < n`. The scalar-ring and Lie-algebra carrier universes are independent.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The total filtration of an enveloping coefficient chain term.

In degree `n`, stage `p` is spanned by decomposable tensors `w ⊗ u` with `u ∈ U_q` and `q+n ≤
p`, where `U_q` is the enveloping degree filtration. The degree condition includes the
exterior degree `n`. -/
def envelopingFiltration (p n : ℕ) :
    Submodule R ((⋀[R]^n L) ⊗[R] regularCoefficients R L) :=
  Submodule.span R {z | ∃ q : ℕ, ∃ a : Fin n → L,
    ∃ u : regularCoefficients R L,
      q + n ≤ p ∧ u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q ∧
        exteriorPower.ιMulti R n a ⊗ₜ[R] u = z}

/-- Monotonicity of the total enveloping chain filtration.

For each exterior degree `n`, the stages satisfy `F_p ⊆ F_q` whenever `p ≤ q`. -/
theorem envelopingFiltration_mono (n : ℕ) :
    Monotone (fun p => envelopingFiltration R L p n) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨r, a, u, hra, hu, rfl⟩
  exact ⟨r, a, u, hra.trans hpq, hu, rfl⟩

/-- The total-degree bound for a decomposable enveloping chain.

For `a : Fin n → L`, an enveloping coefficient `u ∈ U_q`, and `q+n ≤ p`, the tensor `(⋀ᵢ aᵢ) ⊗
u` belongs to `F_p` in degree `n`. -/
theorem ιMulti_tmul_mem_envelopingFiltration
    (p n q : ℕ) (a : Fin n → L) (u : regularCoefficients R L)
    (hp : q + n ≤ p)
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    exteriorPower.ιMulti R n a ⊗ₜ[R] u ∈ envelopingFiltration R L p n :=
  Submodule.subset_span ⟨q, a, u, hp, hu, rfl⟩

/-- The total-degree bound for an arbitrary exterior tensor.

For any `w ∈ ⋀ⁿ[R] L` and `u ∈ U_q`, the tensor `w ⊗ u` belongs to total filtration stage `p`
whenever `q+n ≤ p`. -/
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

/-- Vanishing of filtration stages below exterior degree.

If `p < n`, the total filtration stage `p` in chain degree `n` is the zero submodule. -/
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

/-- The zero total stage in a positive chain degree.

For every `n ∈ ℕ`, total filtration stage zero in degree `n+1` is the zero submodule. -/
theorem envelopingFiltration_zero_succ (n : ℕ) :
    envelopingFiltration R L 0 (n + 1) = ⊥ :=
  envelopingFiltration_eq_bot_of_lt R L 0 (n + 1) (Nat.zero_lt_succ n)

/-- Exhaustiveness of the enveloping chain filtration.

Every element of `⋀ⁿ[R] L ⊗[R] U_R(L)` belongs to some finite total filtration stage. This
holds for every `R`-Lie algebra `L`. -/
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
