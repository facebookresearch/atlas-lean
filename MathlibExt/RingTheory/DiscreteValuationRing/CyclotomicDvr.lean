/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import MathlibExt.RingTheory.AdicCompletion.ModuleFinite
import MathlibExt.RingTheory.Polynomial.Eisenstein.AdjoinRoot

/-!
# Cyclotomic discrete valuation rings over a prime maximal ideal

Over a complete discrete valuation ring whose maximal ideal is generated
by a rational prime `q`, adjoining a root of the `q`-th cyclotomic
polynomial gives a complete discrete valuation ring in which `ζ - 1`
generates the maximal ideal and `ζ` is universal for elements whose
`q`-th cyclotomic sum vanishes.

The ring is `W₀[X] / (Φ_q(X + 1))` with `ζ` the image of `X + 1`. The
shifted polynomial `Φ_q(X + 1)` is Eisenstein at the maximal ideal, so the
Eisenstein extension API (`AdjoinRoot.isLocalRing_of_isEisensteinAt` and its
companions) gives the local ring, its maximal ideal `(ζ - 1)` and the discrete
valuation ring structure. Completeness follows from
`IsLocalRing.isAdicComplete_of_module_finite`, as the extension is finite.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open IsLocalRing Polynomial

namespace CycloDVR

section Eisenstein

variable (q : ℕ) [hq : Fact q.Prime] (W₀ : Type*) [CommRing W₀] [IsDomain W₀]
  [IsDiscreteValuationRing W₀]

private theorem natCast_ne_zero (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) : (q : W₀) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field W₀
  rw [hW₀, h, Ideal.span_singleton_eq_bot]

private theorem natCast_mem_maximalIdeal (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (q : W₀) ∈ maximalIdeal W₀ :=
  hW₀ ▸ Ideal.mem_span_singleton_self _

private theorem natCast_not_mem_sq (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (q : W₀) ∉ (maximalIdeal W₀) ^ 2 := by
  have hq0 := natCast_ne_zero q W₀ hW₀
  have hqmem := natCast_mem_maximalIdeal q W₀ hW₀
  rw [hW₀, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h1 : (q : W₀) * (1 - q * c) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← hc, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact hq0 h
  · have hu : IsUnit (q : W₀) := IsUnit.of_mul_eq_one c (by rwa [sub_eq_zero, eq_comm] at h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hqmem hu

private theorem cyclotomic_comp_X_add_one_eq_map :
    (cyclotomic q W₀).comp (X + 1) = ((cyclotomic q ℤ).comp (X + 1)).map (Int.castRingHom W₀) := by
  rw [Polynomial.map_comp, map_cyclotomic_int]
  simp

private theorem monic_cyclotomic_comp_X_add_one_int : ((cyclotomic q ℤ).comp (X + 1)).Monic := by
  rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
  exact (cyclotomic.monic q ℤ).comp (monic_X_add_C 1) (by rw [natDegree_X_add_C]; exact one_ne_zero)

private theorem monic_cyclotomic_comp_X_add_one : ((cyclotomic q W₀).comp (X + 1)).Monic := by
  rw [cyclotomic_comp_X_add_one_eq_map]
  exact (monic_cyclotomic_comp_X_add_one_int q).map _

private theorem natDegree_cyclotomic_comp_X_add_one :
    ((cyclotomic q W₀).comp (X + 1)).natDegree = ((cyclotomic q ℤ).comp (X + 1)).natDegree := by
  rw [cyclotomic_comp_X_add_one_eq_map, (monic_cyclotomic_comp_X_add_one_int q).natDegree_map]

private theorem natDegree_cyclotomic_comp_X_add_one_int :
    ((cyclotomic q ℤ).comp (X + 1)).natDegree = q - 1 := by
  rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hq.out,
    show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]

private theorem natDegree_cyclotomic_comp_X_add_one_pos :
    0 < ((cyclotomic q W₀).comp (X + 1)).natDegree := by
  rw [natDegree_cyclotomic_comp_X_add_one, natDegree_cyclotomic_comp_X_add_one_int]
  have := hq.out.two_le
  omega

private theorem isEisensteinAt_cyclotomic_comp_X_add_one
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    ((cyclotomic q W₀).comp (X + 1)).IsEisensteinAt (maximalIdeal W₀) := by
  have hEz := cyclotomic_comp_X_add_one_isEisensteinAt q
  refine (monic_cyclotomic_comp_X_add_one q W₀).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal W₀).ne_top ?_ ?_
  · intro n hn
    rw [natDegree_cyclotomic_comp_X_add_one] at hn
    have hmem : ((cyclotomic q ℤ).comp (X + 1)).coeff n ∈ Ideal.span {(q : ℤ)} := hEz.mem hn
    have hd : (q : ℤ) ∣ ((cyclotomic q ℤ).comp (X + 1)).coeff n := Ideal.mem_span_singleton.mp hmem
    rw [cyclotomic_comp_X_add_one_eq_map, coeff_map, hW₀, Ideal.mem_span_singleton]
    simpa using map_dvd (Int.castRingHom W₀) hd
  · have h0 : ((cyclotomic q W₀).comp (X + 1)).coeff 0 = (q : W₀) := by
      rw [coeff_zero_eq_eval_zero, eval_comp]
      simp [eval_one_cyclotomic_prime]
    rw [h0]
    exact natCast_not_mem_sq q W₀ hW₀

end Eisenstein

section Main

variable (q : ℕ) [hq : Fact q.Prime] (W₀ : Type*) [CommRing W₀] [IsDomain W₀]
  [IsDiscreteValuationRing W₀]

private abbrev O (q : ℕ) [Fact q.Prime] (W₀ : Type*) [CommRing W₀] : Type _ :=
  AdjoinRoot ((cyclotomic q W₀).comp (X + 1))

private noncomputable abbrev zeta (q : ℕ) [Fact q.Prime] (W₀ : Type*) [CommRing W₀] :
    O q W₀ := AdjoinRoot.root ((cyclotomic q W₀).comp (X + 1)) + 1

private theorem aeval_cyclotomic_prime_eq_sum {S : Type*} [CommRing S] [Algebra W₀ S] (z : S) :
    aeval z (cyclotomic q W₀) = ∑ i ∈ Finset.range q, z ^ i := by
  rw [cyclotomic_prime, map_sum]
  simp

private theorem aeval_cyclotomic_comp_X_add_one {S : Type*} [CommRing S] [Algebra W₀ S]
    (z : S) : aeval z ((cyclotomic q W₀).comp (X + 1)) = ∑ i ∈ Finset.range q, (z + 1) ^ i := by
  rw [aeval_comp, map_add, aeval_X, map_one, aeval_cyclotomic_prime_eq_sum]

private theorem sum_zeta_pow : (∑ i ∈ Finset.range q, (zeta q W₀) ^ i) = 0 := by
  rw [← aeval_cyclotomic_comp_X_add_one q W₀ (AdjoinRoot.root _), AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self]

private theorem zeta_sub_one :
    zeta q W₀ - 1 = AdjoinRoot.root ((cyclotomic q W₀).comp (X + 1)) :=
  add_sub_cancel_right _ _

private theorem isLocalRing (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    IsLocalRing (O q W₀) :=
  AdjoinRoot.isLocalRing_of_isEisensteinAt _ (isEisensteinAt_cyclotomic_comp_X_add_one q W₀ hW₀)
    (monic_cyclotomic_comp_X_add_one q W₀) (natDegree_cyclotomic_comp_X_add_one_pos q W₀)

private theorem maximalIdeal_eq (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    [IsLocalRing (O q W₀)] : maximalIdeal (O q W₀) = Ideal.span {zeta q W₀ - 1} := by
  rw [zeta_sub_one]
  exact AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root _
    (isEisensteinAt_cyclotomic_comp_X_add_one q W₀ hW₀) (monic_cyclotomic_comp_X_add_one q W₀)
    (natDegree_cyclotomic_comp_X_add_one_pos q W₀)

section Residue

variable (k : Type*) [Field k] [CharP k q] (res₀ : W₀ →+* k)

private theorem eval₂_zero_cyclotomic_comp_X_add_one :
    ((cyclotomic q W₀).comp (X + 1)).eval₂ res₀ 0 = 0 := by
  rw [eval₂_comp, eval₂_add, eval₂_X, eval₂_one, zero_add, eval₂_at_one,
    eval_one_cyclotomic_prime, map_natCast, CharP.cast_eq_zero]

private noncomputable def res : O q W₀ →+* k :=
  AdjoinRoot.lift res₀ 0 (eval₂_zero_cyclotomic_comp_X_add_one q W₀ k res₀)

private theorem res_of (w : W₀) : res q W₀ k res₀ (algebraMap W₀ (O q W₀) w) = res₀ w := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

private theorem res_surjective (hres₀ : Function.Surjective res₀) :
    Function.Surjective (res q W₀ k res₀) := fun y => by
  obtain ⟨w, rfl⟩ := hres₀ y
  exact ⟨algebraMap W₀ (O q W₀) w, res_of q W₀ k res₀ w⟩

end Residue

private scoped instance : Module.Finite W₀ (O q W₀) :=
  (monic_cyclotomic_comp_X_add_one q W₀).finite_adjoinRoot

private theorem isAdicComplete [IsAdicComplete (maximalIdeal W₀) W₀] [IsLocalRing (O q W₀)] :
    IsAdicComplete (maximalIdeal (O q W₀)) (O q W₀) :=
  IsLocalRing.isAdicComplete_of_module_finite (𝒪 := W₀)

private theorem existsUnique_algHom (S : Type*) [CommRing S] [Algebra W₀ S] (z : S)
    (hz : (∑ i ∈ Finset.range q, z ^ i) = 0) :
    ∃! f : O q W₀ →ₐ[W₀] S, f (zeta q W₀) = z := by
  have hz' : ((cyclotomic q W₀).comp (X + 1)).eval₂ (Algebra.ofId W₀ S) (z - 1) = 0 := by
    have := aeval_cyclotomic_comp_X_add_one q W₀ (z - 1)
    rw [sub_add_cancel, hz, aeval_def] at this
    exact this
  refine ⟨AdjoinRoot.liftAlgHom _ (Algebra.ofId W₀ S) (z - 1) hz', ?_, fun g hg => ?_⟩
  · beta_reduce
    rw [map_add, map_one, AdjoinRoot.liftAlgHom_root, sub_add_cancel]
  · apply AdjoinRoot.algHom_ext
    rw [AdjoinRoot.liftAlgHom_root, ← hg, map_add, map_one, add_sub_cancel_right]

end Main

end CycloDVR

universe u v w

open CycloDVR in
/-- **A complete DVR with maximal ideal $(q)$ has a cyclotomic DVR extension.**
Let `W₀` be a complete discrete valuation ring whose maximal ideal is generated
by a rational prime `q`, let `k` be a field of characteristic `q`, and let
`res₀ : W₀ →+* k` be a surjective ring homomorphism whose kernel is the maximal
ideal of `W₀`. Then there are a complete discrete valuation ring `𝒪` that is a
`W₀`-algebra, an element `ζ` of `𝒪` with `∑ i < q, ζ ^ i = 0` (a root of the
`q`-th cyclotomic polynomial) and a ring homomorphism `res : 𝒪 →+* k` such that:

* the maximal ideal of `𝒪` is generated by `ζ - 1`;
* `res` is surjective, its kernel is the maximal ideal `(ζ - 1)` of `𝒪`, and it
  extends `res₀`: `res (algebraMap W₀ 𝒪 w) = res₀ w` for every `w` in `W₀`;
* for every commutative `W₀`-algebra `S` and every `z` in `S` with
  `∑ i < q, z ^ i = 0`, there is a unique `W₀`-algebra homomorphism from `𝒪` to
  `S` sending `ζ` to `z`.

The hypothesis on the kernel of `res₀` is implied by its surjectivity, since `W₀`
is local. -/
public theorem IsDiscreteValuationRing.exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type u) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type v) [Field k] [CharP k q]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (_hker₀ : RingHom.ker res₀ = IsLocalRing.maximalIdeal W₀) :
    ∃ (𝒪 : Type u) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsDiscreteValuationRing 𝒪)
      (_ : Algebra W₀ 𝒪)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪) (ζ : 𝒪) (res : 𝒪 →+* k),
      (∑ i ∈ Finset.range q, ζ ^ i) = 0 ∧
      IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ζ - 1} ∧
      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal 𝒪 ∧
      (∀ w : W₀, res (algebraMap W₀ 𝒪 w) = res₀ w) ∧
      (∀ (S : Type w) [CommRing S] [Algebra W₀ S] (z : S),
        (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃! f : 𝒪 →ₐ[W₀] S, f ζ = z) := by
  have heis := CycloDVR.isEisensteinAt_cyclotomic_comp_X_add_one q W₀ hW₀
  have hmo := CycloDVR.monic_cyclotomic_comp_X_add_one q W₀
  have hdeg := CycloDVR.natDegree_cyclotomic_comp_X_add_one_pos q W₀
  have := CycloDVR.isLocalRing q W₀ hW₀
  exact ⟨CycloDVR.O q W₀, inferInstance, _,
    AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt _ heis hmo hdeg, inferInstance,
    CycloDVR.isAdicComplete q W₀, CycloDVR.zeta q W₀, CycloDVR.res q W₀ k res₀,
    CycloDVR.sum_zeta_pow q W₀, CycloDVR.maximalIdeal_eq q W₀ hW₀,
    CycloDVR.res_surjective q W₀ k res₀ hres₀,
    IsLocalRing.ker_eq_maximalIdeal _ (CycloDVR.res_surjective q W₀ k res₀ hres₀),
    CycloDVR.res_of q W₀ k res₀, fun S _ _ z hz => CycloDVR.existsUnique_algHom q W₀ S z hz⟩
