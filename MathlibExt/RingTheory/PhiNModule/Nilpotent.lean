/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.Basic
public import MathlibExt.LinearAlgebra.Determinant.Semilinear
public import Mathlib.RingTheory.Valuation.Basic

/-!
# The monodromy operator of a `(φ, N)`-module is nilpotent

Let `D` be a finite-dimensional `(φ, N)`-module over a field `K₀`, for a ring automorphism `σ` of
`K₀` and a scalar `p ∈ K₀`, so that `N (φ x) = p • φ (N x)`. If `K₀` carries an additive
valuation `v` with values in `WithTop ℤ` such that `v (σ x) = v x` for all `x` and `v p ≠ 0`, then
the monodromy operator `N` is nilpotent. In the setting of Fontaine–Ouyang, `K₀ = W(k)[1/p]`, `σ`
is the absolute Frobenius and `v` is the `p`-adic valuation, so that `v p = 1`.

The proof is elementary. Iterating `N φ = p φ N` gives `N ^ k φ = p ^ k φ N ^ k`, so the images
of the powers of `N`, and hence the stable image `⨅ k, range (N ^ k)` of `N`, are stable under `φ`
and `N` (if `p = 0`, then `N = 0`). In finite dimension, `N` maps the stable image `D'`
bijectively onto itself. On the other hand, computing the determinant of the matrix of `N φ` in a
basis in two ways shows that `det N = p ^ d * σ (det N)` in every finite-dimensional
`(φ, N)`-module of dimension `d`. Applied to `D'`, on which `det N ≠ 0`, this gives
`v (det N) = d • v p + v (det N)`, hence `d • v p = 0` and `d = 0`. So `D' = 0`, that is,
`N ^ h = 0` for `h` large enough.

## Main results

* `PhiNModule.N_pow_φ`: `N ^ k (φ x) = p ^ k • φ (N ^ k x)`.
* `PhiNModule.isStable_iInf_range_N_pow`: the stable image `⨅ k, range (N ^ k)` of `N` is a stable
  subspace.
* `PhiNModule.map_N_iInf_range_N_pow`, `PhiNModule.bijective_restrict_N_iInf_range_N_pow`: in
  finite dimension, `N` maps its stable image bijectively onto itself.
* `PhiNModule.det_N_eq_pow_mul`: `det N = p ^ d * σ (det N)` in dimension `d`.
* `PhiNModule.subsingleton_of_bijective_N`: if `v (σ x) = v x` for all `x` and `v p ≠ 0`, a
  finite-dimensional `(φ, N)`-module on which `N` is bijective is zero.
* `PhiNModule.iInf_range_N_pow_eq_bot`: under the same hypotheses, the stable image of `N` is
  zero.
* `PhiNModule.isNilpotent_N`: under the same hypotheses, the monodromy operator `N` is
  nilpotent.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.1, Proposition 8.17.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.2.2 p. 145.
-/

@[expose] public section

open Module

namespace PhiNModule

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {D : Type*} [AddCommGroup D] [Module K₀ D]

section

variable (M : PhiNModule σ p D)

/-- In a `(φ, N)`-module, `N ^ k (φ x) = p ^ k • φ (N ^ k x)` for all `k : ℕ` and `x : D`. -/
theorem N_pow_φ (k : ℕ) (x : D) : (M.N ^ k) (M.φ x) = p ^ k • M.φ ((M.N ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, M.N_φ, smul_smul, ← pow_succ,
      mul_apply_eq_comp]

/-- If `p = 0`, then the monodromy operator `N` of a `(φ, N)`-module is zero. -/
theorem N_eq_zero_of_p_eq_zero (hp : p = 0) : M.N = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := M.φ.surjective x
  subst hp
  rw [M.N_φ, zero_smul, LinearMap.zero_apply]

/-- For every `k : ℕ`, the image of the power `N ^ k` of the monodromy operator is a stable
subspace of a `(φ, N)`-module. -/
theorem isStable_range_N_pow (k : ℕ) : M.IsStable (LinearMap.range (M.N ^ k)) where
  φ_mem := by
    rintro - ⟨y, rfl⟩
    rcases eq_or_ne p 0 with hp | hp
    · rcases k with _ | k
      · exact ⟨M.φ ((M.N ^ 0) y), by simp⟩
      · simp [M.N_eq_zero_of_p_eq_zero hp]
    · refine ⟨(p ^ k)⁻¹ • M.φ y, ?_⟩
      rw [map_smul, M.N_pow_φ, smul_smul, inv_mul_cancel₀ (pow_ne_zero k hp), one_smul]
  N_mem := by
    rintro - ⟨y, rfl⟩
    refine ⟨M.N y, ?_⟩
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← pow_succ, pow_succ']

/-- The stable image `⨅ k, range (N ^ k)` of the monodromy operator `N`, the intersection of the
images of its powers, is a stable subspace of a `(φ, N)`-module. -/
theorem isStable_iInf_range_N_pow : M.IsStable (⨅ k, LinearMap.range (M.N ^ k)) where
  φ_mem hx := (Submodule.mem_iInf _).mpr fun k =>
    (M.isStable_range_N_pow k).φ_mem ((Submodule.mem_iInf _).mp hx k)
  N_mem hx := (Submodule.mem_iInf _).mpr fun k =>
    (M.isStable_range_N_pow k).N_mem ((Submodule.mem_iInf _).mp hx k)

/-- In a finite-dimensional `(φ, N)`-module, the monodromy operator `N` maps its stable image
`⨅ k, range (N ^ k)` onto itself. -/
theorem map_N_iInf_range_N_pow [FiniteDimensional K₀ D] :
    (⨅ k, LinearMap.range (M.N ^ k)).map M.N = ⨅ k, LinearMap.range (M.N ^ k) := by
  obtain ⟨n, hn⟩ := (LinearMap.eventually_iInf_range_pow_eq M.N).exists_forall_of_atTop
  rw [hn n le_rfl, ← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← pow_succ',
    ← hn (n + 1) n.le_succ, hn n le_rfl]

/-- In a finite-dimensional `(φ, N)`-module, the monodromy operator `N` restricts to a bijection
of its stable image `⨅ k, range (N ^ k)`: the monodromy operator of the restricted
`(φ, N)`-module structure on the stable image is bijective. -/
theorem bijective_restrict_N_iInf_range_N_pow [FiniteDimensional K₀ D] :
    Function.Bijective (M.restrict _ M.isStable_iInf_range_N_pow).N := by
  have hsurj : Function.Surjective (M.restrict _ M.isStable_iInf_range_N_pow).N := by
    rintro ⟨y, hy⟩
    rw [← M.map_N_iInf_range_N_pow] at hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

/-- In a finite-dimensional `(φ, N)`-module `D`, the determinant of the monodromy operator `N`
satisfies `det N = p ^ d * σ (det N)`, where `d` is the dimension of `D`. -/
theorem det_N_eq_pow_mul [FiniteDimensional K₀ D] :
    LinearMap.det M.N = p ^ finrank K₀ D * σ (LinearMap.det M.N) := by
  set b := Module.finBasis K₀ D
  have hNb : b.det (M.N ∘ b) = LinearMap.det M.N := by rw [b.det_comp, b.det_self, mul_one]
  -- The determinant of the matrix of `N ∘ φ` in `b`, computed in two ways.
  have h1 : b.det (M.N ∘ M.φ ∘ b) = LinearMap.det M.N * b.det (M.φ ∘ b) := b.det_comp _ _
  have h2 : b.det (M.N ∘ M.φ ∘ b) =
      p ^ finrank K₀ D * (b.det (M.φ ∘ b) * σ (LinearMap.det M.N)) := by
    have h : M.N ∘ M.φ ∘ b = fun i => p • (M.φ : D →ₛₗ[σ] D) ((M.N ∘ b) i) := by
      ext i
      simp [M.N_φ]
    rw [h, AlternatingMap.map_smul_univ, Fin.prod_const, smul_eq_mul, ← hNb]
    exact congrArg (p ^ finrank K₀ D * ·) (b.det_compₛₗ (M.φ : D →ₛₗ[σ] D) (M.N ∘ b))
  refine (b.isUnit_det_compₛₗ M.φ).mul_right_inj.mp ?_
  rw [mul_comm, ← h1, h2, mul_left_comm]

/-- Let `v` be an additive valuation on `K₀` with values in `WithTop ℤ` such that
`v (σ x) = v x` for all `x : K₀` and `v p ≠ 0`. Then a finite-dimensional `(φ, N)`-module whose
monodromy operator `N` is bijective is zero. -/
theorem subsingleton_of_bijective_N [FiniteDimensional K₀ D] (v : AddValuation K₀ (WithTop ℤ))
    (hv : ∀ x, v (σ x) = v x) (hp : v p ≠ 0) (hN : Function.Bijective M.N) : Subsingleton D := by
  rw [← Module.finrank_zero_iff (R := K₀)]
  by_contra hd
  have hB : LinearMap.det M.N ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det M.N).mp ((Module.End.isUnit_iff M.N).mpr hN)).ne_zero
  have hdet := M.det_N_eq_pow_mul
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_pow hd, zero_mul] at hdet
    exact hB hdet
  -- Apply `v` to `det N = p ^ d * σ (det N)`, where `v (det N)` and `v p` are finite.
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hB)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hp0)
  have key := congrArg v hdet
  rw [AddValuation.map_mul, AddValuation.map_pow, hv, ← hc, ← hm] at key
  have key' : finrank K₀ D • m + c = c := by exact_mod_cast key.symm
  rcases smul_eq_zero.mp (add_eq_right.mp key') with h0 | h0
  · exact hd h0
  · exact hp (by rw [← hm, h0, WithTop.coe_zero])

/-- Let `v` be an additive valuation on `K₀` with values in `WithTop ℤ` such that
`v (σ x) = v x` for all `x : K₀` and `v p ≠ 0`. Then in a finite-dimensional `(φ, N)`-module, the
stable image `⨅ k, range (N ^ k)` of the monodromy operator `N` is zero. -/
theorem iInf_range_N_pow_eq_bot [FiniteDimensional K₀ D] (v : AddValuation K₀ (WithTop ℤ))
    (hv : ∀ x, v (σ x) = v x) (hp : v p ≠ 0) : ⨅ k, LinearMap.range (M.N ^ k) = ⊥ := by
  have := (M.restrict _ M.isStable_iInf_range_N_pow).subsingleton_of_bijective_N v hv hp
    M.bijective_restrict_N_iInf_range_N_pow
  exact Submodule.eq_bot_of_subsingleton

end

/-- **The monodromy operator is nilpotent** (Fontaine–Ouyang, Proposition 8.17). Let `v` be an
additive valuation on `K₀` with values in `WithTop ℤ` such that `v (σ x) = v x` for all `x : K₀`
and `v p ≠ 0`. Then the monodromy operator `N` of a finite-dimensional `(φ, N)`-module is
nilpotent. -/
theorem isNilpotent_N [FiniteDimensional K₀ D] (M : PhiNModule σ p D)
    (v : AddValuation K₀ (WithTop ℤ)) (hv : ∀ x, v (σ x) = v x) (hp : v p ≠ 0) :
    IsNilpotent M.N := by
  obtain ⟨n, hn⟩ := (LinearMap.eventually_iInf_range_pow_eq M.N).exists
  refine ⟨n, LinearMap.range_eq_bot.mp ?_⟩
  rw [← hn, M.iInf_range_N_pow_eq_bot v hv hp]

end PhiNModule
