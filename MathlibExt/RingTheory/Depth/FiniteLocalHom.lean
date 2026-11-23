/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_depth_eq_depth_of_finite_of_isLocalHom.lean`
and
`P2M/Sol/S_Module_depth_eq_depth_of_finite_of_isLocalHom.lean`
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

import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

@[expose] public section

universe u v w t

open IsLocalRing RingTheory
open scoped Pointwise

namespace ModuleDepthFiniteLocalHom

section Helpers

variable {T : Type t} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  {M : Type w} [AddCommGroup M] [Module T M] [Module.Finite T M] [Small.{w} T]

private lemma smul_top_maximalIdeal_lt [Nontrivial M] :
    (maximalIdeal T) • (⊤ : Submodule T M) < ⊤ :=
  lt_top_iff_ne_top.mpr
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm

private lemma exists_isRegular_of_le_depth [Nontrivial M] {n : ℕ}
    (hn : (n : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of T M)) :
    ∃ rs : List T, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal T) ∧
      RingTheory.Sequence.IsRegular M rs := by
  have h_ext : ∀ i < n, Subsingleton
      (CategoryTheory.Abelian.Ext ↧(Shrink.{w} (T ⧸ maximalIdeal T))
        (ModuleCat.of T M) i) := by
    intro i hi
    apply ModuleCat.subsingleton_ext_of_lt_depth
    exact lt_of_lt_of_le (by exact_mod_cast hi) hn
  exact ((ModuleCat.exists_isRegular_tfae (maximalIdeal T) n (ModuleCat.of T M)
    smul_top_maximalIdeal_lt).out 2 4).mp h_ext

private lemma le_depth_of_exists_isRegular {rs : List T}
    (hreg : RingTheory.Sequence.IsRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal T) [Nontrivial M] :
    (rs.length : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of T M) := by
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply le_sSup
  exact ⟨rs, hreg, hmem, rfl⟩

private lemma natCast_le_moduleCat_depth {P Q : ModuleCat.{w} T} {n : ℕ}
    (h : ∀ i < n, Subsingleton (CategoryTheory.Abelian.Ext P Q i)) :
    (n : ℕ∞) ≤ P.depth Q := by
  by_contra hlt
  push Not at hlt
  have htop : P.depth Q ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact (lt_irrefl (⊤ : ℕ∞)) (lt_of_lt_of_le hlt le_top)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  have hmn : m < n := by
    rw [← hm] at hlt
    exact Nat.cast_lt.mp hlt
  have hdepth := (ModuleCat.depth_eq_iff P Q m).mp hm.symm
  exact (not_nontrivial_iff_subsingleton.mpr (h m hmn)) hdepth.1

private lemma natCast_le_depth_quotSMulTop {x : T} (hreg : IsSMulRegular M x)
    {n : ℕ} (hn : ((n + 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of T M)) :
    (n : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of T (QuotSMulTop x M)) := by
  apply natCast_le_moduleCat_depth
    (P := (↧(Shrink.{w} (T ⧸ maximalIdeal T)) : ModuleCat.{w} T))
  intro i hi
  have zero1 : CategoryTheory.Limits.IsZero
      (AddCommGrpCat.of
        (CategoryTheory.Abelian.Ext ↧(Shrink.{w} (T ⧸ maximalIdeal T))
          (ModuleCat.of T M) i)) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr
      (ModuleCat.subsingleton_ext_of_lt_depth
        (lt_of_lt_of_le (by exact_mod_cast (by omega : i < n + 1)) hn))
  have zero2 : CategoryTheory.Limits.IsZero
      (AddCommGrpCat.of
        (CategoryTheory.Abelian.Ext ↧(Shrink.{w} (T ⧸ maximalIdeal T))
          (ModuleCat.of T M) (i + 1))) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr
      (ModuleCat.subsingleton_ext_of_lt_depth
        (lt_of_lt_of_le (by exact_mod_cast (by omega : i + 1 < n + 1)) hn))
  have hS : (ModuleCat.smulShortComplex (ModuleCat.of T M) x).ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of T M) hreg
  exact AddCommGrpCat.subsingleton_of_isZero
    (CategoryTheory.ShortComplex.Exact.isZero_of_both_isZero
      ((CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
        (↧(Shrink.{w} (T ⧸ maximalIdeal T)) : ModuleCat.{w} T)
        hS)
        i (i + 1) rfl)
      zero1 zero2)

end Helpers

section Main

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Module.Finite R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M] [Module.Finite S M] [Small.{w} R] [Small.{w} S]

private lemma isAssociatedPrime_maximalIdeal_of_module_finite
    [Module.Finite R M]
    (h : IsAssociatedPrime (maximalIdeal R) M) :
    IsAssociatedPrime (maximalIdeal S) M := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨v, hv⟩ := (isAssociatedPrime_iff.mp h).2
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply (inferInstance : (maximalIdeal R).IsPrime).ne_top
    rw [hv]
    ext r
    simp [Submodule.mem_colon_singleton]
  obtain ⟨P, hP, hPle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S v hv0
  haveI hPprime : P.IsPrime := hP.isPrime
  have hge : maximalIdeal R ≤ P.comap (algebraMap R S) := by
    intro r hr
    rw [Ideal.mem_comap]
    apply hPle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul]
    have hr' : r ∈ (⊥ : Submodule R M).colon {v} := hv ▸ hr
    exact Submodule.mem_colon_singleton.mp hr'
  have heq : P.comap (algebraMap R S) = maximalIdeal R :=
    le_antisymm (le_maximalIdeal
      (Ideal.IsPrime.ne_top (I := P.comap (algebraMap R S))
        (Ideal.comap_isPrime (f := algebraMap R S) (K := P)))) hge
  have hPmax : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S) _ P
    · rw [heq]
      exact inferInstanceAs ((maximalIdeal R).IsMaximal)
    · intro x
      exact Algebra.IsIntegral.isIntegral (R := R) (A := S) x
  rw [← IsLocalRing.eq_maximalIdeal hPmax]
  exact hP

private lemma exists_mem_maximalIdeal_isSMulRegular [Module.Finite R M]
    [Nontrivial M]
    (h : ¬ IsAssociatedPrime (maximalIdeal R) M) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hcon
  push Not at hcon
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro x hx
    by_cases hreg : IsSMulRegular M x
    · exact False.elim (hcon x hx hreg)
    · have hx' : x ∈ ({r : R | IsSMulRegular M r}ᶜ : Set R) := hreg
      rwa [← biUnion_associatedPrimes_eq_compl_regular R M] at hx'
  obtain ⟨p, hp, hle⟩ :=
    ((maximalIdeal R).subset_union_prime_finite (associatedPrimes.finite R M)
      (f := id) (maximalIdeal R) (maximalIdeal R)
      (fun _ hpmem _ _ => hpmem.isPrime)).mp hsub
  have heq : maximalIdeal R = p := le_antisymm hle (le_maximalIdeal hp.isPrime.ne_top)
  exact h (heq ▸ hp)

private lemma smul_top_eq_restrictScalars (x : R) :
    x • (⊤ : Submodule R M) =
      ((algebraMap R S x) • (⊤ : Submodule S M)).restrictScalars R := by
  ext m
  simp only [Submodule.restrictScalars_mem]
  constructor
  · intro hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    rw [← algebraMap_smul S x m']
    exact Submodule.smul_mem_pointwise_smul m' _ ⊤ trivial
  · intro hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    rw [algebraMap_smul S x m']
    exact Submodule.smul_mem_pointwise_smul m' _ ⊤ trivial

/-- The depth of a finite module over a local ring is unchanged under a
finite local homomorphism.

More precisely, if `R → S` is a finite local homomorphism of Noetherian
local rings and `M` is a finite `S`-module, viewed as an `R`-module by
restriction of scalars, then the `R`-depth and the `S`-depth of `M`
agree. Depth is taken with respect to the maximal ideal, in the sense
of `IsLocalRing.depth`. -/
public theorem _root_.IsLocalRing.depth_eq_depth_of_finite_of_isLocalHom :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : Module.Finite R M := Module.Finite.trans S M
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [IsLocalRing.depth_eq_top_of_subsingleton,
      IsLocalRing.depth_eq_top_of_subsingleton]
  · have aux : ∀ (n : ℕ) (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
        [IsScalarTower R S N] [Module.Finite S N],
        (∃ rs : List S, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal S) ∧
          RingTheory.Sequence.IsRegular N rs) →
        ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular N rs := by
      intro n
      induction n with
      | zero =>
        intro N _ _ _ _ _ hseq
        obtain ⟨rs, -, -, hreg⟩ := hseq
        haveI : Nontrivial N := hreg.nontrivial
        exact ⟨[], rfl, by simp, RingTheory.Sequence.IsRegular.nil (R := R) (M := N)⟩
      | succ n IH =>
        intro N _ _ _ _ _ hseq
        obtain ⟨rsS, hrsSlen, hrsSmem, hrsSreg⟩ := hseq
        haveI : Nontrivial N := hrsSreg.nontrivial
        haveI : Module.Finite R N := Module.Finite.trans S N
        have hnS : ((n + 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of S N) := by
          have h := ModuleDepthFiniteLocalHom.le_depth_of_exists_isRegular
            (T := S) (M := N) hrsSreg hrsSmem
          rwa [hrsSlen] at h
        have hnot : ¬ IsAssociatedPrime (maximalIdeal R) N := by
          intro hR
          have hS := ModuleDepthFiniteLocalHom.isAssociatedPrime_maximalIdeal_of_module_finite
            (R := R) (S := S) (M := N) hR
          obtain ⟨y, hymem, hyreg⟩ : ∃ y ∈ maximalIdeal S, IsSMulRegular N y := by
            cases rsS with
            | nil => simp at hrsSlen
            | cons y ys =>
              have hreg : RingTheory.Sequence.IsRegular N (y :: ys) := hrsSreg
              rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
              exact ⟨y, hrsSmem y List.mem_cons_self, hreg.1⟩
          obtain ⟨z, hz⟩ := (isAssociatedPrime_iff.mp hS).2
          have hz0 : z ≠ 0 := by
            rintro rfl
            apply (inferInstance : (maximalIdeal S).IsPrime).ne_top
            rw [hz]
            ext r
            simp [Submodule.mem_colon_singleton]
          have hyz : y • z = 0 := by
            have hym : y ∈ (⊥ : Submodule S N).colon {z} := hz ▸ hymem
            exact Submodule.mem_colon_singleton.mp hym
          exact hz0 (hyreg.right_eq_zero_of_smul hyz)
        obtain ⟨x, hxmem, hxreg⟩ :=
          ModuleDepthFiniteLocalHom.exists_mem_maximalIdeal_isSMulRegular (M := N) hnot
        have hymem : algebraMap R S x ∈ maximalIdeal S := by
          have hx' : x ∈ (maximalIdeal S).comap (algebraMap R S) := by
            rw [IsLocalRing.maximalIdeal_comap (algebraMap R S)]
            exact hxmem
          exact Ideal.mem_comap.mp hx'
        have hyreg : IsSMulRegular N (algebraMap R S x) := by
          rw [isSMulRegular_iff_right_eq_zero_of_smul] at hxreg ⊢
          intro m hm
          apply hxreg
          rwa [algebraMap_smul] at hm
        haveI : Nontrivial (QuotSMulTop (algebraMap R S x) N) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal N hymem
        have hquot : (n : ℕ∞) ≤
            IsLocalRing.depth (ModuleCat.of S (QuotSMulTop (algebraMap R S x) N)) :=
          ModuleDepthFiniteLocalHom.natCast_le_depth_quotSMulTop (T := S) (M := N) hyreg hnS
        obtain ⟨rsq, hrsqlen, hrsqmem, hrsqreg⟩ :=
          ModuleDepthFiniteLocalHom.exists_isRegular_of_le_depth (T := S)
            (M := QuotSMulTop (algebraMap R S x) N) hquot
        obtain ⟨rsR, hrsRlen, hrsRmem, hrsRreg⟩ :=
          IH (QuotSMulTop (algebraMap R S x) N) ⟨rsq, hrsqlen, hrsqmem, hrsqreg⟩
        have e : QuotSMulTop x N ≃ₗ[R] QuotSMulTop (algebraMap R S x) N :=
          (Submodule.quotEquivOfEq _ _
            (ModuleDepthFiniteLocalHom.smul_top_eq_restrictScalars x)).trans
            (Submodule.Quotient.restrictScalarsEquiv R
              ((algebraMap R S x) • (⊤ : Submodule S N)))
        have hrsRx : RingTheory.Sequence.IsRegular (QuotSMulTop x N) rsR :=
          (e.isRegular_congr rsR).mpr hrsRreg
        refine ⟨x :: rsR, by simp [hrsRlen], fun r hr => ?_,
          (RingTheory.Sequence.isRegular_cons_iff N x rsR).mpr ⟨hxreg, hrsRx⟩⟩
        cases List.mem_cons.mp hr with
        | inl h => exact h ▸ hxmem
        | inr h => exact hrsRmem r h
    apply le_antisymm
    · rw [IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of R M),
        IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of S M)]
      apply sSup_le
      rintro _ ⟨rs, hreg, hmem, rfl⟩
      have hmemS : ∀ r ∈ rs.map (algebraMap R S), r ∈ maximalIdeal S := by
        intro r hr
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        have ha' : a ∈ (maximalIdeal S).comap (algebraMap R S) := by
          rw [IsLocalRing.maximalIdeal_comap (algebraMap R S)]
          exact hmem a ha
        exact Ideal.mem_comap.mp ha'
      have hregS : RingTheory.Sequence.IsRegular M (rs.map (algebraMap R S)) :=
        RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
          (L := M) hmemS
          ((RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff S M rs).mpr
            hreg.toIsWeaklyRegular)
      have h := ModuleDepthFiniteLocalHom.le_depth_of_exists_isRegular (T := S) (M := M) hregS hmemS
      rw [List.length_map, IsLocalRing.depth_eq_sSup_length_isRegular] at h
      exact h
    · rw [IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of S M),
        IsLocalRing.depth_eq_sSup_length_isRegular (ModuleCat.of R M)]
      apply sSup_le
      rintro _ ⟨rs, hreg, hmem, rfl⟩
      obtain ⟨rsR, hrsRlen, hrsRmem, hrsRreg⟩ :=
        aux rs.length M ⟨rs, rfl, hmem, hreg⟩
      have h := ModuleDepthFiniteLocalHom.le_depth_of_exists_isRegular
        (T := R) (M := M) hrsRreg hrsRmem
      rw [hrsRlen, IsLocalRing.depth_eq_sSup_length_isRegular] at h
      exact h

end Main

end ModuleDepthFiniteLocalHom
