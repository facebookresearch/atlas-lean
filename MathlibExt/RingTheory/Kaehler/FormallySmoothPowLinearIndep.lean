/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean`
and
`P2M/Sol/S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean`
and
`Theorems/Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`
and
`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`
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

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Etale.Field
import MathlibExt.RingTheory.Kaehler.NonPthPower

@[expose] public section

open TensorProduct Polynomial IntermediateField
open scoped IntermediateField

namespace Algebra.FormallySmooth

/-- If `K/k` is a formally smooth extension of fields of exponent
characteristic `p`, then raising to the `p`-th power preserves `k`-linear
independence of finite subsets of `K`. -/
public theorem linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchark : CharP k p := by
    cases ‹ExpChar k p› with
    | zero => exact absurd hp Nat.not_prime_one
    | prime _ => assumption
  haveI := hchark
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let k₀ : Subfield k := ⊥
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k₀ k K) := by
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange k₀ k K
    haveI : Subsingleton (Algebra.H1Cotangent k K) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  let B := Module.Free.chooseBasis k (Ω[k⁄k₀])
  let BK := B.baseChange K
  induction s using Finset.strongInduction with
  | H s IH =>
    refine linearIndepOn_finset_iffₛ.mpr ?_
    intro g zg hg
    by_contra hne
    push Not at hne
    obtain ⟨x₀, hx₀, hgx₀⟩ := hne
    set c : K → k := fun x => (g x₀ - zg x₀)⁻¹ * (g x - zg x) with hc
    have hc₀ : c x₀ = 1 := by
      simp [hc, inv_mul_cancel₀ (sub_ne_zero.mpr hgx₀)]
    have hrel : ∑ x ∈ s, c x • x ^ p = 0 := by
      have h0 : ∑ x ∈ s, (g x - zg x) • x ^ p = 0 := by
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        exact hg
      simp only [hc, mul_smul, ← Finset.smul_sum, h0, smul_zero]
    have hD : ∀ x ∈ s, KaehlerDifferential.D k₀ k (c x) = 0 := by
      set T : K ⊗[k] Ω[k⁄k₀] :=
        ∑ x ∈ s, (x ^ p) ⊗ₜ[k] KaehlerDifferential.D k₀ k (c x) with hT
      have hT0 : T = 0 := by
        apply hinj
        rw [map_zero, hT, map_sum]
        simp_rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        have hDrel := congrArg (KaehlerDifferential.D k₀ K) hrel
        rw [map_zero, map_sum] at hDrel
        rw [← hDrel]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz_pow,
          ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, smul_zero, zero_add]
      have hcoord : ∀ j, ∑ x ∈ s, (B.repr (KaehlerDifferential.D k₀ k (c x)) j) • x ^ p = 0 := by
        intro j
        have := congrArg (fun t => BK.repr t j) hT0
        simp only [hT, map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
          Finset.sum_apply, Module.Basis.baseChange_repr_tmul, BK] at this
        exact this
      have hsub : s.erase x₀ ⊂ s := Finset.erase_ssubset hx₀
      have hind' : LinearIndepOn k (· ^ p) ((s.erase x₀ : Finset K) : Set K) :=
        IH _ hsub (hs.mono (by
          intro y hy; exact Finset.mem_of_mem_erase (Finset.mem_coe.mp hy)))
      have hind'' := linearIndepOn_finset_iffₛ.mp hind'
      have hzero : ∀ j, ∀ x ∈ s, B.repr (KaehlerDifferential.D k₀ k (c x)) j = 0 := by
        intro j x hx
        by_cases hxx : x = x₀
        · subst hxx; rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply]
        · have h0 : B.repr (KaehlerDifferential.D k₀ k (c x₀)) j • x₀ ^ p = 0 := by
            rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply, zero_smul]
          have hsum : ∑ x ∈ s.erase x₀,
              B.repr (KaehlerDifferential.D k₀ k (c x)) j • x ^ p = 0 := by
            have h := Finset.add_sum_erase s
              (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j • x ^ p) hx₀
            rw [hcoord j, h0, zero_add] at h
            exact h
          have := hind'' (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j) 0
            (by simpa using hsum) x (Finset.mem_erase.mpr ⟨hxx, hx⟩)
          simpa using this
      intro x hx
      apply B.repr.injective
      rw [map_zero]
      ext j
      rw [hzero j x hx, Finsupp.zero_apply]
    have hroot : ∀ x ∈ s, ∃ b : k, b ^ p = c x := by
      intro x hx
      by_contra h
      push Not at h
      exact KaehlerDifferential.D_ne_zero_of_forall_pow_ne p hp (c x) h (hD x hx)
    choose! b hb using hroot
    have hsum : (∑ x ∈ s, b x • x) ^ p = 0 := by
      rw [sum_pow_char, ← hrel]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow, hb x hx]
    have hsum0 : ∑ x ∈ s, b x • x = 0 := pow_eq_zero_iff hp.ne_zero |>.mp hsum
    have hs' := linearIndepOn_finset_iffₛ.mp hs
    have hb0 : b x₀ = 0 := by
      simpa using hs' b 0 (by simpa using hsum0) x₀ hx₀
    have : c x₀ = 0 := by rw [← hb x₀ hx₀, hb0, zero_pow hp.ne_zero]
    rw [hc₀] at this
    exact one_ne_zero this

end Algebra.FormallySmooth
