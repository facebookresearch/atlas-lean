/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_isRegular_of_systemOfParameters.lean`
and `P2M/Sol/S_IsLocalRing_isRegular_of_systemOfParameters.lean`
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

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Systems of parameters in Cohen–Macaulay local rings

Let `R` be a Noetherian local ring with `depth R = dim R = d`, i.e. a Cohen–Macaulay local
ring. We prove that every system of parameters of `R` is an `R`-regular sequence: if
`x₁, …, x_d` lie in the maximal ideal and `R ⧸ (x₁, …, x_d)` has Krull dimension zero, then
`x₁, …, x_d` is a regular sequence.

Depth is Mathlib's `IsLocalRing.depth`, defined through `Ext`. The proof works with the
supremum of lengths of weakly regular sequences in the maximal ideal and identifies it with
`IsLocalRing.depth` through `IsLocalRing.depth_eq_sSup_length_isRegular`.

The key step is unmixedness: every associated prime `p` of `R` satisfies
`depth R ≤ dim (R ⧸ p)`, so in the Cohen–Macaulay case `dim (R ⧸ p) = dim R`. A parameter
therefore avoids all associated primes and is a nonzerodivisor, and the statement follows by
induction on `d`.

## Main results

* `IsLocalRing.isRegular_of_systemOfParameters`: in a Cohen–Macaulay Noetherian local ring,
  every system of parameters is a regular sequence.
-/

@[expose] public section

open IsLocalRing RingTheory RingTheory.Sequence Module
open scoped Pointwise

namespace IsLocalRing.SystemOfParameters

universe u v

/-- Depth as the supremum of lengths of weakly regular sequences in the maximal ideal. -/
private noncomputable def weakDepth (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : RingTheory.Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }

section Basic

variable (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

private lemma length_le_weakDepth (s : List R)
    (hs : Sequence.IsWeaklyRegular M s) (hs' : ∀ r ∈ s, r ∈ maximalIdeal R) :
    s.length ≤ weakDepth R M :=
  le_sSup ⟨s, hs, hs', rfl⟩

private lemma weakDepth_of_subsingleton [Subsingleton M] :
    weakDepth R M = ⊤ := by
  rw [weakDepth, sSup_eq_top]
  rintro b hb
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hb.ne
  simp only [Set.mem_ofPred_eq, exists_prop, ↓existsAndEq, and_true, Nat.cast_lt]
  refine ⟨List.replicate b.succ 0, ⟨?_, ?_⟩, ?_⟩
  · refine (Sequence.isWeaklyRegular_iff_Fin ..).mpr fun i ↦ ?_
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  · simp
  · simp

private lemma weakDepth_le_krullDim_support [Nontrivial M] [Module.Finite R M] :
    .some (weakDepth R M) ≤ Order.krullDim (Module.support R M) := by
  have : Nonempty (Module.support R M) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty,
      ne_eq, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
  cases h : Order.krullDim (Module.support R M) with
  | bot => simpa using Order.krullDim_nonneg.trans_eq h
  | coe n =>
  cases n with
  | top => simp
  | coe n =>
  clear this
  simp only [WithBot.coe_le_coe, ge_iff_le]
  induction n using Nat.strong_induction_on generalizing M with
  | ind n IH =>
    rw [weakDepth, sSup_le_iff]
    rintro _ ⟨l, hl, hl', rfl⟩
    apply WithTop.coe_le_coe.mpr ?_
    cases l with
    | nil => simp
    | cons x l =>
    simp only [Sequence.isWeaklyRegular_cons_iff] at hl
    have : Nontrivial (QuotSMulTop x M) := by
      apply Submodule.Quotient.nontrivial_iff.2
      rw [← Submodule.ideal_span_singleton_smul, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hl' _ (by simp)
    rw [Module.support_eq_zeroLocus, ← ringKrullDim_quotient] at h
    let f : (R ⧸ annihilator R M) ⧸ Ideal.span {(Ideal.Quotient.mk (annihilator R M)) x} →+*
        R ⧸ annihilator R (QuotSMulTop x M) :=
      Ideal.Quotient.lift _ (Ideal.quotientMap _ (.id R)
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
        (show Ideal.span _ ≤ RingHom.ker _ by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          rw [SetLike.mem_coe, RingHom.mem_ker]
          change Ideal.Quotient.mk (annihilator R (QuotSMulTop x M)) x = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
          intro m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact ⟨m, trivial, rfl⟩)
    have hf : Function.Surjective f := by
      apply Ideal.Quotient.lift_surjective_of_surjective
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective
    have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := R ⧸ annihilator R M) (r := x)
      (by
        rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]
        intro z hz
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
        simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
          Module.mem_annihilator] at hz ⊢
        intro m
        apply hl.1
        simpa [smul_comm x, mul_smul] using hz m)
    rw [h] at this
    replace this := (add_le_add (ringKrullDim_le_of_surjective f hf) le_rfl).trans this
    cases h : ringKrullDim (R ⧸ annihilator R (QuotSMulTop x M)) with
    | bot =>
      have : Nontrivial (R ⧸ annihilator R (QuotSMulTop x M)) := by
        rw [Ideal.Quotient.nontrivial_iff, ← Submodule.annihilator_top, ne_eq,
          Submodule.annihilator_eq_top_iff]
        exact top_ne_bot
      have := ringKrullDim_nonneg_of_nontrivial.trans_eq h
      simp at this
    | coe m =>
    cases m with
    | top =>
      have : (⊤ : ℕ∞) ≤ (n : ℕ) := by
        apply WithBot.coe_le_coe.mp
        simp only [h] at this
        exact this
      cases (ENat.natCast_lt_top n).not_ge this
    | coe m =>
    rw [h] at this
    replace this : m + 1 ≤ n := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    replace IH := IH m (Nat.lt_of_succ_le this) (QuotSMulTop x M)
      (by rwa [Module.support_eq_zeroLocus, ← ringKrullDim_quotient])
    replace IH := WithTop.coe_le_coe.mp
      ((length_le_weakDepth _ _ l hl.2 (by simp_all)).trans IH)
    · simp only [List.length_cons, ge_iff_le]
      linarith

private lemma weakDepth_le_ringKrullDim [Nontrivial M] [Module.Finite R M] :
    .some (weakDepth R M) ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_le (Module.annihilator R M))
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact weakDepth_le_krullDim_support R M

private lemma exists_isSMulRegular_of_weakDepth_pos (h : 0 < weakDepth R M) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  obtain ⟨b, hb, hpos⟩ := lt_sSup_iff.mp h
  obtain ⟨s, hreg, hmem, rfl⟩ := hb
  cases s with
  | nil => simp at hpos
  | cons x rest =>
      rw [Sequence.isWeaklyRegular_cons_iff] at hreg
      exact ⟨x, hmem x (by simp), hreg.1⟩

private lemma exists_isWeaklyRegular_of_le_weakDepth
    (n : ℕ) (hn : (n : ℕ∞) ≤ weakDepth R M) :
    ∃ s : List R, Sequence.IsWeaklyRegular M s ∧ (∀ r ∈ s, r ∈ maximalIdeal R) ∧
      s.length = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨[], Sequence.IsWeaklyRegular.nil R M, by simp, rfl⟩
  · have hlt : ((n - 1 : ℕ) : ℕ∞) < weakDepth R M :=
      lt_of_lt_of_le (Nat.cast_lt.mpr (by omega)) hn
    rw [weakDepth, lt_sSup_iff] at hlt
    obtain ⟨b, ⟨s, hs, hs', rfl⟩, hb⟩ := hlt
    have hlen : n ≤ s.length := by
      have := Nat.cast_lt.mp hb
      omega
    refine ⟨s.take n, ?_, ?_, ?_⟩
    · exact ((Sequence.isWeaklyRegular_append_iff M (s.take n) (s.drop n)).mp
        (by rwa [List.take_append_drop])).1
    · exact fun r hr => hs' r (List.take_subset n s hr)
    · rw [List.length_take]; omega

private lemma weakDepth_lt_top [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] :
    weakDepth R M < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hle := weakDepth_le_ringKrullDim R M
  rw [h, WithBot.coe_top, top_le_iff] at hle
  exact (ringKrullDim_lt_top (R := R)).ne hle

variable {R M} in
private lemma weakDepth_eq_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : weakDepth R M = weakDepth R N := by
  rw [weakDepth, weakDepth]
  congr 1
  ext k
  constructor
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mp hs, hs', rfl⟩
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mpr hs, hs', rfl⟩

private lemma nontrivial_quotSMulTop_of_mem_maximalIdeal [Module.Finite R M] [Nontrivial M]
    {x : R} (hx : x ∈ maximalIdeal R) : Nontrivial (QuotSMulTop x M) := by
  apply Submodule.Quotient.nontrivial_iff.2
  rw [← Submodule.ideal_span_singleton_smul, ne_comm]
  apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
  refine le_trans ?_ (maximalIdeal_le_jacobson _)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact hx

/-- `M ⧸ zM ⧸ x(M ⧸ zM) ≃ M ⧸ (zM + xM)`. -/
private noncomputable def quotSMulTopQuotSMulTopEquivSup (z x : R) :
    QuotSMulTop x (QuotSMulTop z M) ≃ₗ[R]
      M ⧸ (z • (⊤ : Submodule R M) ⊔ x • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).trans
    (Submodule.quotientQuotientEquivQuotientSup (z • ⊤) (x • ⊤))

/-- Quotienting by `z` and then by `x` agrees with the opposite order. -/
private noncomputable def quotSMulTopQuotSMulTopComm (x z : R) :
    QuotSMulTop x (QuotSMulTop z M) ≃ₗ[R] QuotSMulTop z (QuotSMulTop x M) :=
  (quotSMulTopQuotSMulTopEquivSup R M z x).trans <|
    (Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
      (quotSMulTopQuotSMulTopEquivSup R M x z).symm

end Basic

section DepthDrop

variable {R : Type*} [CommRing R] [IsLocalRing R]

private lemma eq_zero_of_maximalIdeal_smul_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    {x y₁ y₂ : R} (hxreg : IsSMulRegular M x)
    (hy : Sequence.IsWeaklyRegular M [y₁, y₂])
    (hy₁ : y₁ ∈ maximalIdeal R) (hy₂ : y₂ ∈ maximalIdeal R)
    (m₀ : QuotSMulTop x M) (hm₀ : ∀ a ∈ maximalIdeal R, a • m₀ = 0) : m₀ = 0 := by
  rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_singleton_iff] at hy
  obtain ⟨hy₁reg, hy₂reg⟩ := hy
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m₀
  rw [Submodule.Quotient.mk_eq_zero]
  have key : ∀ a ∈ maximalIdeal R, ∃ m' : M, x • m' = a • m := by
    intro a ha
    have h := hm₀ a ha
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    exact ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h).imp fun m' hm' => hm'.2
  obtain ⟨a, ha⟩ := key y₁ hy₁
  obtain ⟨b, hb⟩ := key y₂ hy₂
  have hab : y₂ • a = y₁ • b := by
    apply hxreg
    change x • y₂ • a = x • y₁ • b
    rw [smul_comm x y₂ a, ha, smul_comm y₂ y₁ m, ← hb, smul_comm y₁ x b]
  have ha0 : (Submodule.Quotient.mk a : QuotSMulTop y₁ M) = 0 := by
    apply hy₂reg
    change y₂ • (Submodule.Quotient.mk a : QuotSMulTop y₁ M) = y₂ • (0 : QuotSMulTop y₁ M)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hab, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨b, Submodule.mem_top, rfl⟩
  rw [Submodule.Quotient.mk_eq_zero] at ha0
  obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha0
  have hm : m = x • c := by
    apply hy₁reg
    change y₁ • m = y₁ • (x • c)
    rw [← ha, ← hc, smul_comm x y₁ c]
  rw [hm]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨c, Submodule.mem_top, rfl⟩

variable [IsNoetherianRing R]

private lemma not_isAssociatedPrime_maximalIdeal_of_isSMulRegular {M : Type*}
    [AddCommGroup M] [Module R M] {x : R}
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ¬ IsAssociatedPrime (maximalIdeal R) M := by
  intro h
  obtain ⟨hp, y, hyy⟩ := isAssociatedPrime_iff.mp h
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [hyy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem ⊥
  apply hy0
  apply hxreg
  change x • y = x • (0 : M)
  rw [smul_zero]
  have hxy : x ∈ (⊥ : Submodule R M).colon {y} := hyy ▸ hx
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at hxy

private lemma not_isAssociatedPrime_maximalIdeal_quotSMulTop (M : Type*) [AddCommGroup M]
    [Module R M] {x : R} (hxreg : IsSMulRegular M x)
    (hdepth : (2 : ℕ∞) ≤ weakDepth R M) :
    ¬ IsAssociatedPrime (maximalIdeal R) (QuotSMulTop x M) := by
  obtain ⟨pr, hpr, hpr', hprlen⟩ :=
    exists_isWeaklyRegular_of_le_weakDepth R M 2 (by exact_mod_cast hdepth)
  obtain ⟨y₁, y₂, rfl⟩ : ∃ y₁ y₂, pr = [y₁, y₂] := by
    rcases pr with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, t⟩⟩⟩ <;>
      first
        | exact ⟨_, _, rfl⟩
        | (exfalso; simp only [List.length_nil, List.length_cons] at hprlen; omega)
  intro h
  obtain ⟨hp, y, hyy⟩ := isAssociatedPrime_iff.mp h
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [hyy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem ⊥
  apply hy0
  apply eq_zero_of_maximalIdeal_smul_eq_zero hxreg hpr (hpr' y₁ (by simp)) (hpr' y₂ (by simp))
  intro a ha
  have hay : a ∈ (⊥ : Submodule R (QuotSMulTop x M)).colon {y} := hyy ▸ ha
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at hay

private lemma exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
    (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : ¬ IsAssociatedPrime (maximalIdeal R) N₁)
    (h₂ : ¬ IsAssociatedPrime (maximalIdeal R) N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  by_contra hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂ : Set (Ideal R)), (p : Set R) := by
    intro z hz
    rw [Set.biUnion_union]
    by_cases hreg : IsSMulRegular N₁ z
    · refine Set.mem_union_right _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]
      exact fun hreg2 => hcon ⟨z, hz, hreg, hreg2⟩
    · refine Set.mem_union_left _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]
      exact hreg
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hprime : ∀ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂),
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) - -
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hpmem, hple⟩ := (Ideal.subset_union_prime_finite hfin (f := id)
    (I := maximalIdeal R) ⊥ ⊥ hprime).mp (by simpa using hsub)
  have hpprime : p.IsPrime := by
    rcases hpmem with hp | hp
    · exact hp.isPrime
    · exact hp.isPrime
  have hpeq : p = maximalIdeal R := le_antisymm (le_maximalIdeal hpprime.ne_top) hple
  rw [hpeq] at hpmem
  rcases hpmem with hp | hp
  · exact h₁ hp
  · exact h₂ hp

private lemma weakDepth_quotSMulTop_succ_le (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    weakDepth R (QuotSMulTop x M) + 1 ≤ weakDepth R M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [weakDepth_of_subsingleton R (QuotSMulTop x M), weakDepth_of_subsingleton R M,
      top_add]
  · have hQ : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal R M hx
    have hlt : weakDepth R (QuotSMulTop x M) < ⊤ := weakDepth_lt_top R (QuotSMulTop x M)
    cases hd : weakDepth R (QuotSMulTop x M) with
    | top => exact absurd hd hlt.ne
    | coe n =>
      obtain ⟨s, hs, hs', hlen⟩ :=
        exists_isWeaklyRegular_of_le_weakDepth R (QuotSMulTop x M) n (le_of_eq hd.symm)
      have hcons : Sequence.IsWeaklyRegular M (x :: s) :=
        (Sequence.isWeaklyRegular_cons_iff M x s).mpr ⟨hxreg, hs⟩
      have hmem : ∀ r ∈ x :: s, r ∈ maximalIdeal R := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hx
        · exact hs' r hr
      have hle := length_le_weakDepth R M (x :: s) hcons hmem
      rw [List.length_cons, hlen] at hle
      exact_mod_cast hle

private lemma le_weakDepth_quotSMulTop_of_succ_le
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (n : ℕ) (hxreg : IsSMulRegular M x)
    (hd : ((n + 1 : ℕ) : ℕ∞) ≤ weakDepth R M) :
    (n : ℕ∞) ≤ weakDepth R (QuotSMulTop x M) := by
  induction n generalizing M with
  | zero => simp
  | succ n IH =>
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [weakDepth_of_subsingleton R (QuotSMulTop x M)]
      exact le_top
    · have hAssQ : ¬ IsAssociatedPrime (maximalIdeal R) (QuotSMulTop x M) :=
        not_isAssociatedPrime_maximalIdeal_quotSMulTop M hxreg
          (le_trans (by exact_mod_cast Nat.cast_le.mpr (by omega : 2 ≤ n + 1 + 1)) hd)
      obtain ⟨s, hs, hs', hlen⟩ := exists_isWeaklyRegular_of_le_weakDepth R M (n + 1 + 1) hd
      have hsne : s ≠ [] := by
        intro h
        rw [h, List.length_nil] at hlen
        omega
      obtain ⟨s', w, rfl, hs'len⟩ : ∃ s' w, s = s' ++ [w] ∧ s'.length = n + 1 := by
        refine ⟨s.dropLast, s.getLast hsne, (List.dropLast_append_getLast hsne).symm, ?_⟩
        rw [List.length_dropLast, hlen]
        omega
      have hsplit := (Sequence.isWeaklyRegular_append_iff M s' [w]).mp hs
      have hwreg : IsSMulRegular (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) w :=
        (Sequence.isWeaklyRegular_singleton_iff _ w).mp hsplit.2
      have hwm : w ∈ maximalIdeal R := hs' w (by simp)
      have hAssN : ¬ IsAssociatedPrime (maximalIdeal R)
          (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) :=
        not_isAssociatedPrime_maximalIdeal_of_isSMulRegular hwm hwreg
      obtain ⟨z, hz, hzregQ, hzregN⟩ := exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
        (QuotSMulTop x M) (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) hAssQ hAssN
      have hs'z : Sequence.IsWeaklyRegular M (s' ++ [z]) :=
        (Sequence.isWeaklyRegular_append_iff M s' [z]).mpr
          ⟨hsplit.1, (Sequence.isWeaklyRegular_singleton_iff _ z).mpr hzregN⟩
      have hs'mem : ∀ r ∈ s', r ∈ maximalIdeal R :=
        fun r hr => hs' r (List.mem_append_left _ hr)
      have hzs' : Sequence.IsWeaklyRegular M (z :: s') := by
        apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hs'z
          (List.perm_append_singleton z s')
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hs'mem r hr
        · rw [List.mem_singleton] at hr
          subst hr
          exact hz
      have hs'Mz : Sequence.IsWeaklyRegular (QuotSMulTop z M) s' :=
        ((Sequence.isWeaklyRegular_cons_iff M z s').mp hzs').2
      have hdMz : ((n + 1 : ℕ) : ℕ∞) ≤ weakDepth R (QuotSMulTop z M) := by
        have hle := length_le_weakDepth R (QuotSMulTop z M) s' hs'Mz hs'mem
        rwa [hs'len] at hle
      have hxz : Sequence.IsWeaklyRegular M [x, z] :=
        (Sequence.isWeaklyRegular_cons_iff M x [z]).mpr
          ⟨hxreg, (Sequence.isWeaklyRegular_singleton_iff _ z).mpr hzregQ⟩
      have hzx : Sequence.IsWeaklyRegular M [z, x] := by
        apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hxz
          (List.Perm.swap z x [])
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx
        · exact hz
      have hxregMz : IsSMulRegular (QuotSMulTop z M) x :=
        (Sequence.isWeaklyRegular_singleton_iff _ x).mp
          ((Sequence.isWeaklyRegular_cons_iff M z [x]).mp hzx).2
      have hIH : (n : ℕ∞) ≤ weakDepth R (QuotSMulTop x (QuotSMulTop z M)) :=
        IH (QuotSMulTop z M) hxregMz hdMz
      rw [weakDepth_eq_of_linearEquiv (quotSMulTopQuotSMulTopComm R M x z)] at hIH
      obtain ⟨t, ht, ht', htlen⟩ :=
        exists_isWeaklyRegular_of_le_weakDepth R (QuotSMulTop z (QuotSMulTop x M)) n hIH
      have hfinal : Sequence.IsWeaklyRegular (QuotSMulTop x M) (z :: t) :=
        (Sequence.isWeaklyRegular_cons_iff _ z t).mpr ⟨hzregQ, ht⟩
      have hmemzt : ∀ r ∈ z :: t, r ∈ maximalIdeal R := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hz
        · exact ht' r hr
      have hle := length_le_weakDepth R (QuotSMulTop x M) (z :: t) hfinal hmemzt
      rw [List.length_cons, htlen] at hle
      exact_mod_cast hle

private lemma weakDepth_quotSMulTop_succ_eq (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    weakDepth R (QuotSMulTop x M) + 1 = weakDepth R M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [weakDepth_of_subsingleton R (QuotSMulTop x M), weakDepth_of_subsingleton R M,
      top_add]
  · refine le_antisymm (weakDepth_quotSMulTop_succ_le M hx hxreg) ?_
    have hMlt : weakDepth R M < ⊤ := weakDepth_lt_top R M
    cases hdM : weakDepth R M with
    | top => exact absurd hdM hMlt.ne
    | coe d =>
      have hxmem : ∀ r ∈ [x], r ∈ maximalIdeal R := by
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        exact hx
      have hd1 : 1 ≤ d := by
        have hle := length_le_weakDepth R M [x]
          ((Sequence.isWeaklyRegular_singleton_iff M x).mpr hxreg) hxmem
        rw [hdM] at hle
        exact_mod_cast hle
      have hd2 : ((d - 1 + 1 : ℕ) : ℕ∞) ≤ weakDepth R M := by
        rw [hdM]
        exact Nat.cast_le.mpr (by omega : d - 1 + 1 ≤ d)
      have hhard := le_weakDepth_quotSMulTop_of_succ_le M hx (d - 1) hxreg hd2
      calc ((d : ℕ) : ℕ∞) = ((d - 1 : ℕ) : ℕ∞) + 1 := by
            rw [show ((d - 1 : ℕ) : ℕ∞) + 1 = ((d - 1 + 1 : ℕ) : ℕ∞) by push_cast; ring]
            congr 1
            omega
        _ ≤ weakDepth R (QuotSMulTop x M) + 1 := add_le_add hhard le_rfl

end DepthDrop

section Quotient

variable {R : Type*} [CommRing R] [IsLocalRing R]

private lemma weakDepth_quotient_eq (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    weakDepth (R ⧸ I) N = weakDepth R N := by
  have hloc : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap R (R ⧸ I)) ∘
      (Function.surjInv (Ideal.Quotient.mk_surjective (I := I))) = id := by
    funext a
    rw [Function.comp_apply, Ideal.Quotient.algebraMap_eq,
      Function.surjInv_eq Ideal.Quotient.mk_surjective a, id_eq]
  apply le_antisymm
  · refine sSup_le_sSup ?_
    rintro b ⟨t, ht, ht', rfl⟩
    refine ⟨t.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_, ?_, by
      rw [List.length_map]⟩
    · have hmap : (t.map (Function.surjInv Ideal.Quotient.mk_surjective)).map
          (algebraMap R (R ⧸ I)) = t := by
        rw [List.map_map, hcomp, List.map_id]
      rw [← Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) N, hmap]
      exact ht
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      intro hu
      apply ht' a ha
      rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective a]
      exact hu.map (Ideal.Quotient.mk I)
  · refine sSup_le_sSup ?_
    rintro b ⟨s, hs, hs', rfl⟩
    refine ⟨s.map (Ideal.Quotient.mk I), ?_, ?_, by rw [List.length_map]⟩
    · have hmk : s.map (Ideal.Quotient.mk I) = s.map (algebraMap R (R ⧸ I)) := by
        rw [Ideal.Quotient.algebraMap_eq]
      rw [hmk, Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) N]
      exact hs
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      intro hu
      exact hs' a ha (hloc.map_nonunit a hu)

private lemma isLocalRing_quotient_span_singleton {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    rw [Ideal.span_singleton_eq_top] at h
    exact hx h
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private lemma ringKrullDim_quotient_span_singleton_of_eq_succ [IsNoetherianRing R] {x : R}
    (hxreg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) {d : ℕ}
    (hd : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ Ideal.span {x}) = ((d : ℕ) : WithBot ℕ∞) := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hx
  rw [hd] at h
  have : IsLocalRing (R ⧸ Ideal.span {x}) := isLocalRing_quotient_span_singleton hx
  have hbot : ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊤ := ringKrullDim_ne_top
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (R ⧸ Ideal.span {x}) = ((m : ℕ) : WithBot ℕ∞) := by
    cases hk : ringKrullDim (R ⧸ Ideal.span {x}) with
    | bot => exact absurd hk hbot
    | coe e =>
      cases e with
      | top => exact absurd hk htop
      | coe m => exact ⟨m, by norm_cast⟩
  rw [hm] at h ⊢
  rw [← Nat.cast_add_one (R := WithBot ℕ∞) m] at h
  have hmd : m + 1 = d + 1 := by exact_mod_cast h
  have hfin : m = d := by omega
  rw [hfin]

end Quotient

section Unmixed

private lemma ringKrullDim_quotient_succ_le_of_lt {R : Type*} [CommRing R] {p q : Ideal R}
    [p.IsPrime] (hpq : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := IsConcreteLE.exists_of_lt hpq
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le) (r := Ideal.Quotient.mk p x) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero
      fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hxq

/-- The elements of `M` killed by every element of `p`. -/
private def pTorsion {R : Type*} [CommRing R] (p : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] : Submodule R M where
  carrier := {m : M | ∀ a ∈ p, a • m = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := by
    intro m₁ m₂ h₁ h₂
    change ∀ a ∈ p, a • (m₁ + m₂) = 0
    intro a ha
    rw [smul_add, h₁ a ha, h₂ a ha, add_zero]
  smul_mem' := by
    intro c m hm
    change ∀ a ∈ p, a • (c • m) = 0
    intro a ha
    rw [smul_comm, hm a ha, smul_zero]

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private lemma exists_forall_smul_eq_zero_notMem_smul_top {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ k : M, (∀ a ∈ p, a • k = 0) ∧ k ∉ x • (⊤ : Submodule R M) := by
  obtain ⟨hp_prime, z, hz⟩ := isAssociatedPrime_iff.mp hp
  have hz0 : z ≠ 0 := by
    rintro rfl
    refine hp_prime.ne_top ?_
    rw [hz, Submodule.colon_singleton_zero]
  have hzann : ∀ a ∈ p, a • z = 0 := by
    intro a ha
    have haz : a ∈ (⊥ : Submodule R M).colon {z} := hz ▸ ha
    rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at haz
  by_contra hcon
  have hcon' : ∀ k : M, (∀ a ∈ p, a • k = 0) → k ∈ x • (⊤ : Submodule R M) := by
    intro k hk
    by_contra hknot
    exact hcon ⟨k, hk, hknot⟩
  have hKle : pTorsion p M ≤ x • (⊤ : Submodule R M) := fun k hk => hcon' k hk
  have hKxK : pTorsion p M ≤ Ideal.span {x} • pTorsion p M := by
    rw [Submodule.ideal_span_singleton_smul]
    intro k hk
    have hk' : ∀ a ∈ p, a • k = 0 := hk
    obtain ⟨m, -, hm⟩ := (Submodule.mem_smul_pointwise_iff_exists k x ⊤).mp (hKle hk)
    have hmK : ∀ a ∈ p, a • m = 0 := by
      intro a ha
      apply hxreg
      change x • a • m = x • (0 : M)
      rw [smul_zero, smul_comm x a m, hm]
      exact hk' a ha
    have hmK' : m ∈ pTorsion p M := hmK
    exact (Submodule.mem_smul_pointwise_iff_exists k x (pTorsion p M)).mpr ⟨m, hmK', hm⟩
  have hKbot : pTorsion p M = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson (Ideal.span {x}) (pTorsion p M)
      (IsNoetherian.noetherian (pTorsion p M)) hKxK ?_
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hzK : z ∈ pTorsion p M := hzann
  rw [hKbot, Submodule.mem_bot] at hzK
  exact hz0 hzK

private lemma exists_isAssociatedPrime_quotSMulTop_le {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ q : Ideal R, IsAssociatedPrime q (QuotSMulTop x M) ∧ p ≤ q ∧ x ∈ q := by
  obtain ⟨k, hkp, hkx⟩ := exists_forall_smul_eq_zero_notMem_smul_top hp hx hxreg
  have hk0 : (Submodule.Quotient.mk k : QuotSMulTop x M) ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hkx
  obtain ⟨q, hq, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R (Submodule.Quotient.mk k) hk0
  refine ⟨q, hq, ?_, ?_⟩
  · intro a ha
    refine hle ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      hkp a ha, Submodule.Quotient.mk_eq_zero]
    exact Submodule.zero_mem _
  · refine hle ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul k x ⊤ Submodule.mem_top

private lemma natCast_le_ringKrullDim_quotient_of_le_weakDepth (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R),
      IsAssociatedPrime p M → (n : ℕ∞) ≤ weakDepth R M →
      ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction n with
  | zero =>
    intro M _ _ _ p hp _
    have hprime : p.IsPrime := hp.isPrime
    have hnt : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
  | succ n IH =>
    intro M _ _ _ p hp hn
    have hprime : p.IsPrime := hp.isPrime
    have hpos : 0 < weakDepth R M := by
      refine lt_of_lt_of_le ?_ hn
      exact_mod_cast Nat.succ_pos n
    obtain ⟨x, hx, hxreg⟩ := exists_isSMulRegular_of_weakDepth_pos R M hpos
    have hpSet : p ∈ associatedPrimes R M := hp
    have hxp : x ∉ p := by
      intro hxpmem
      have hmem : x ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
        Set.mem_biUnion hpSet hxpmem
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hmem
      exact hmem hxreg
    obtain ⟨q, hq, hpq, hxq⟩ := exists_isAssociatedPrime_quotSMulTop_le hp hx hxreg
    have hdrop : (n : ℕ∞) ≤ weakDepth R (QuotSMulTop x M) :=
      le_weakDepth_quotSMulTop_of_succ_le M hx n hxreg (by exact_mod_cast hn)
    have hIH : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) :=
      IH (QuotSMulTop x M) q hq hdrop
    have hlt : p < q := lt_of_le_of_ne hpq (by rintro rfl; exact hxp hxq)
    have hdim : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
      ringKrullDim_quotient_succ_le_of_lt hlt
    push_cast
    calc ((n : ℕ) : WithBot ℕ∞) + 1
        ≤ ringKrullDim (R ⧸ q) + 1 := add_le_add hIH le_rfl
      _ ≤ ringKrullDim (R ⧸ p) := hdim

/-- Every associated prime `p` of a finite module `M` satisfies `depth M ≤ dim (R ⧸ p)`. -/
private lemma weakDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    .some (weakDepth R M) ≤ ringKrullDim (R ⧸ p) := by
  have hp' : IsAssociatedPrime p M := hp
  have hM : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with hsub | hnt
    · exact absurd hp' not_isAssociatedPrime_of_subsingleton
    · exact hnt
  have hlt : weakDepth R M < ⊤ := weakDepth_lt_top R M
  cases hd : weakDepth R M with
  | top => exact absurd hd hlt.ne
  | coe d =>
    exact natCast_le_ringKrullDim_quotient_of_le_weakDepth d M p hp' (le_of_eq hd.symm)

end Unmixed

section SystemOfParameters

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private lemma notMem_of_ringKrullDim_quotient_cons_le_zero {x : R} {rest : List R}
    (hmem : ∀ y ∈ x :: rest, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList (x :: rest)) ≤ 0)
    {p : Ideal R} (hp : p.IsPrime)
    (hpdim : ringKrullDim (R ⧸ p) = ringKrullDim R)
    (hlen : ((rest.length : ℕ) : WithBot ℕ∞) < ringKrullDim R) :
    x ∉ p := by
  classical
  intro hxp
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  set s : Set (R ⧸ p) := {y | y ∈ rest.map (Ideal.Quotient.mk p)} with hs_def
  have hjac : s ⊆ Ring.jacobson (R ⧸ p) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    rintro y' hy'
    rw [hs_def, Set.mem_ofPred_eq, List.mem_map] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    intro hu
    exact hmem y (List.mem_cons_of_mem x hy) (IsLocalHom.map_nonunit y hu)
  have hcount := ringKrullDim_le_ringKrullDim_quotient_add_encard s hjac
  have hspan : Ideal.span s = Ideal.map (Ideal.Quotient.mk p) (Ideal.ofList rest) := by
    rw [Ideal.map_ofList]
  have hsup : Ideal.ofList (x :: rest) ≤ p ⊔ Ideal.ofList rest := by
    rw [Ideal.ofList_cons]
    exact sup_le_sup_right (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxp)) _
  have hdq : ringKrullDim ((R ⧸ p) ⧸ Ideal.span s) ≤ 0 := by
    rw [hspan, ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.ofList rest))]
    calc ringKrullDim (R ⧸ (p ⊔ Ideal.ofList rest))
        ≤ ringKrullDim (R ⧸ Ideal.ofList (x :: rest)) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsup)
            (Ideal.Quotient.factor_surjective hsup)
      _ ≤ 0 := hsop
  have hcard : s.encard ≤ (rest.length : ℕ∞) := by
    rw [hs_def]
    calc ({y | y ∈ rest.map (Ideal.Quotient.mk p)} : Set (R ⧸ p)).encard
        = (((rest.map (Ideal.Quotient.mk p)).toFinset : Set (R ⧸ p))).encard := by
          rw [List.coe_toFinset]
      _ = ((rest.map (Ideal.Quotient.mk p)).toFinset.card : ℕ∞) :=
          Set.encard_coe_eq_coe_finsetCard _
      _ ≤ ((rest.map (Ideal.Quotient.mk p)).length : ℕ∞) := by
          exact_mod_cast List.toFinset_card_le (rest.map (Ideal.Quotient.mk p))
      _ = (rest.length : ℕ∞) := by rw [List.length_map]
  rw [hpdim] at hcount
  have hfinal : ringKrullDim R ≤ ((rest.length : ℕ) : WithBot ℕ∞) := by
    refine hcount.trans ?_
    calc ringKrullDim ((R ⧸ p) ⧸ Ideal.span s) + (s.encard : WithBot ℕ∞)
        ≤ 0 + (((rest.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          refine add_le_add hdq ?_
          exact_mod_cast hcard
      _ = ((rest.length : ℕ) : WithBot ℕ∞) := by
          rw [zero_add]
          norm_cast
  exact absurd hfinal (not_le.mpr hlen)

private lemma isRegular_of_sop_aux (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (.some (weakDepth R R) : WithBot ℕ∞) = ringKrullDim R →
      ringKrullDim R = (d : WithBot ℕ∞) →
      ∀ xs : List R, xs.length = d →
        (∀ y ∈ xs, y ∈ maximalIdeal R) →
        ringKrullDim (R ⧸ Ideal.ofList xs) = 0 →
        Sequence.IsRegular R xs := by
  induction d with
  | zero =>
    intro R _ _ _ hCM hdim xs hlen hmem hsop
    cases xs with
    | nil => exact Sequence.IsRegular.nil R R
    | cons x rest => exact absurd hlen (by simp)
  | succ n IH =>
    intro R _ _ _ hCM hdim xs hlen hmem hsop
    cases xs with
    | nil => exact absurd hlen (by simp)
    | cons x rest =>
    have hrestlen : rest.length = n := by simpa using hlen
    have hxm : x ∈ maximalIdeal R := hmem x (by simp)
    have hdepth : weakDepth R R = ((n + 1 : ℕ) : ℕ∞) := by
      have h := hCM.trans hdim
      exact_mod_cast h
    have hxreg : IsSMulRegular R x := by
      by_contra hcon
      have hx_in : x ∈ {r : R | IsSMulRegular R r}ᶜ := hcon
      rw [← biUnion_associatedPrimes_eq_compl_regular R R] at hx_in
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx_in
      obtain ⟨p, hpass, hxp⟩ := hx_in
      have hpprime : p.IsPrime := hpass.isPrime
      have hpdim : ringKrullDim (R ⧸ p) = ringKrullDim R := by
        refine le_antisymm (ringKrullDim_quotient_le p) ?_
        rw [← hCM]
        exact weakDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes R hpass
      refine (notMem_of_ringKrullDim_quotient_cons_le_zero hmem (le_of_eq hsop) hpprime hpdim
        ?_) hxp
      rw [hdim, hrestlen]
      exact_mod_cast Nat.lt_succ_self n
    have : IsLocalRing (R ⧸ Ideal.span {x}) := isLocalRing_quotient_span_singleton hxm
    have hdim' : ringKrullDim (R ⧸ Ideal.span {x}) = ((n : ℕ) : WithBot ℕ∞) :=
      ringKrullDim_quotient_span_singleton_of_eq_succ hxreg hxm (by rw [hdim])
    have hsub : (Ideal.span {x} : Submodule R R) = x • (⊤ : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul]
      simp
    have hdepth' : weakDepth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) = ((n : ℕ) : ℕ∞) := by
      have h1 : weakDepth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) =
          weakDepth R (R ⧸ Ideal.span {x}) :=
        weakDepth_quotient_eq (Ideal.span {x}) (R ⧸ Ideal.span {x})
      have h2 : weakDepth R (R ⧸ Ideal.span {x}) = weakDepth R (QuotSMulTop x R) :=
        weakDepth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ hsub)
      have h3 := weakDepth_quotSMulTop_succ_eq R hxm hxreg
      rw [hdepth] at h3
      rw [h1, h2]
      have hcast : ((n + 1 : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast] at h3
      exact WithTop.add_right_cancel (by simp : (1 : ℕ∞) ≠ ⊤) h3
    have hCM' : (.some (weakDepth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) :
        WithBot ℕ∞) = ringKrullDim (R ⧸ Ideal.span {x}) := by
      rw [hdepth', hdim']
      rfl
    have hlen' : (rest.map (Ideal.Quotient.mk (Ideal.span {x}))).length = n := by
      rw [List.length_map]; exact hrestlen
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hmem' : ∀ y ∈ rest.map (Ideal.Quotient.mk (Ideal.span {x})),
        y ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      intro hu
      exact hmem y (List.mem_cons_of_mem x hy) (IsLocalHom.map_nonunit y hu)
    have hsop' : ringKrullDim ((R ⧸ Ideal.span {x}) ⧸
        Ideal.ofList (rest.map (Ideal.Quotient.mk (Ideal.span {x})))) = 0 := by
      have hofl : Ideal.ofList (rest.map (Ideal.Quotient.mk (Ideal.span {x}))) =
          Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.ofList rest) :=
        (Ideal.map_ofList _ _).symm
      rw [hofl, ringKrullDim_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {x}) (Ideal.ofList rest))]
      rw [show Ideal.span {x} ⊔ Ideal.ofList rest = Ideal.ofList (x :: rest) from
        (Ideal.ofList_cons x rest).symm]
      exact hsop
    have hIH := IH (R ⧸ Ideal.span {x}) hCM' hdim'
      (rest.map (Ideal.Quotient.mk (Ideal.span {x}))) hlen' hmem' hsop'
    refine Sequence.IsRegular.cons' hxreg ?_
    have e' : (R ⧸ Ideal.span {x}) ≃ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x R :=
      LinearEquiv.extendScalarsOfSurjective
        (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
        (Submodule.quotEquivOfEq _ _ hsub)
    exact (LinearEquiv.isRegular_congr e' _).mp hIH

variable (R) in
/-- For a Noetherian local ring, `IsLocalRing.depth` of `R` is the supremum of the lengths of
weakly regular sequences in the maximal ideal. -/
private lemma depth_eq_weakDepth :
    IsLocalRing.depth (ModuleCat.of R R) = weakDepth R R := by
  rw [IsLocalRing.depth_eq_sSup_length_isRegular, weakDepth]
  congr 1
  ext k
  constructor
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, hs.toIsWeaklyRegular, hs', rfl⟩
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (M := R) hs').mpr hs, hs', rfl⟩

end SystemOfParameters

end IsLocalRing.SystemOfParameters

/-- In a Cohen–Macaulay Noetherian local ring `R` of dimension `d`, every system of parameters
`x₁, …, x_d` (elements of the maximal ideal with `dim R ⧸ (x₁, …, x_d) = 0`) is an
`R`-regular sequence. -/
theorem IsLocalRing.isRegular_of_systemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs := by
  rw [SystemOfParameters.depth_eq_weakDepth] at hCM
  exact SystemOfParameters.isRegular_of_sop_aux d R hCM hdim xs hlen hmem hsop
