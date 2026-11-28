/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite.lean`
and
`P2M/Sol/S_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite_univ.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.AdicCompletion.ModuleFinite

/-!
# Finite algebras over complete local rings

A finite algebra over a complete Noetherian local ring has only finitely
many maximal ideals, decomposes as the product of its localizations at
those maximal ideals, and each such localization is finite over the base
and complete at its maximal ideal.
-/

@[expose] public section

namespace FiniteAlgebraDecompositionAux



section Aux

private lemma idem_eq_of_isNilpotent_sub {B : Type*} [CommRing B] {x y : B}
    (hx : IsIdempotentElem x) (hy : IsIdempotentElem y) (hd : IsNilpotent (x - y)) :
    x = y := by
  obtain ⟨m, hm⟩ := hd
  have hx2 : x * x = x := hx
  have hy2 : y * y = y := hy
  have h3 : (x - y) ^ 3 = x - y := by
    linear_combination (1 + x - 3 * y) * hx2 + (3 * x - 1 - y) * hy2
  have hodd : ∀ j : ℕ, (x - y) ^ (2 * j + 1) = x - y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h21 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
      calc (x - y) ^ (2 * (j + 1) + 1) = (x - y) ^ ((2 * j + 1) + 2) := by rw [h21]
        _ = (x - y) ^ (2 * j + 1) * (x - y) ^ 2 := by rw [pow_add]
        _ = (x - y) * (x - y) ^ 2 := by rw [ih]
        _ = (x - y) ^ 3 := by ring
        _ = x - y := h3
  have hz : x - y = 0 := by
    have h1 : x - y = (x - y) ^ (2 * m + 1) := (hodd m).symm
    have h2 : (x - y) ^ (2 * m + 1) = (x - y) ^ m * (x - y) ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h1, h2, hm, zero_mul]
  exact sub_eq_zero.mp hz

private lemma exists_completeOrthogonalIdempotents
    (R : Type*) [CommRing R] [IsArtinianRing R] [Fintype (MaximalSpectrum R)] :
    ∃ e : MaximalSpectrum R → R, CompleteOrthogonalIdempotents e ∧
      (∀ P : MaximalSpectrum R, e P ∉ P.asIdeal) ∧
      (∀ P Q : MaximalSpectrum R, Q ≠ P → e P ∈ Q.asIdeal) := by
  classical
  have hsingle : ∀ P : MaximalSpectrum R,
      ∃ e : R, IsIdempotentElem e ∧ e ∉ P.asIdeal ∧
        ∀ Q : MaximalSpectrum R, Q ≠ P → e ∈ Q.asIdeal := by
    intro P
    have hclopen : IsClopen ({⟨P.asIdeal, P.isMaximal.isPrime⟩} : Set (PrimeSpectrum R)) :=
      isClopen_discrete _
    obtain ⟨e, he, hbo⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
    have hPbo : (⟨P.asIdeal, P.isMaximal.isPrime⟩ : PrimeSpectrum R) ∈
        (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
      rw [← hbo]
      exact Set.mem_singleton _
    refine ⟨e, he, ?_, ?_⟩
    · exact (PrimeSpectrum.mem_basicOpen e _).mp hPbo
    · intro Q hQ
      by_contra hmem
      have hQbo : (⟨Q.asIdeal, Q.isMaximal.isPrime⟩ : PrimeSpectrum R) ∈
          (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.mem_basicOpen e _).mpr hmem
      rw [← hbo] at hQbo
      have hQP : Q.asIdeal = P.asIdeal :=
        congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hQbo)
      exact hQ (MaximalSpectrum.ext hQP)
  choose e hidem hnot hmem using hsingle
  have hprime_to_max : ∀ (I : Ideal R), I.IsPrime → ∃ Q : MaximalSpectrum R, Q.asIdeal = I := by
    intro I hI
    haveI := hI
    exact ⟨⟨I, IsArtinianRing.isMaximal_of_isPrime I⟩, rfl⟩
  have horth : ∀ P Q : MaximalSpectrum R, P ≠ Q → e P * e Q = 0 := by
    intro P Q hPQ
    have hid : IsIdempotentElem (e P * e Q) :=
      (hidem P).mul_of_commute (Commute.all _ _) (hidem Q)
    refine hid.eq_zero_of_isNilpotent ?_
    rw [nilpotent_iff_mem_prime]
    intro I hI
    obtain ⟨QI, rfl⟩ := hprime_to_max I hI
    by_cases h : QI = P
    · have hQne : QI ≠ Q := fun hq => hPQ (h.symm.trans hq)
      exact Ideal.mul_mem_left _ _ (hmem Q QI hQne)
    · exact Ideal.mul_mem_right _ _ (hmem P QI h)
  have horthS : OrthogonalIdempotents e := ⟨hidem, horth⟩
  have hsum : IsIdempotentElem (∑ P, e P) := horthS.isIdempotentElem_sum
  have hone : IsIdempotentElem (1 - ∑ P, e P) := hsum.one_sub
  have hnil : IsNilpotent (1 - ∑ P, e P) := by
    rw [nilpotent_iff_mem_prime]
    intro I hI
    obtain ⟨QI, rfl⟩ := hprime_to_max I hI
    have hsummem : (∑ P, e P) - e QI ∈ QI.asIdeal := by
      have hsplit : ∑ P, e P = e QI + ∑ P ∈ Finset.univ.erase QI, e P := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ QI)]
      rw [hsplit, add_sub_cancel_left]
      refine Ideal.sum_mem _ fun Q hQ => ?_
      exact hmem Q QI fun h => (Finset.mem_erase.mp hQ).1 h.symm
    have h1e : (1 : R) - e QI ∈ QI.asIdeal := by
      have h0 : e QI * (1 - e QI) ∈ QI.asIdeal := by
        rw [mul_sub, mul_one, (hidem QI).eq, sub_self]
        exact Ideal.zero_mem _
      rcases hI.mem_or_mem h0 with h | h
      · exact absurd h (hnot QI)
      · exact h
    have hrw : (1 : R) - ∑ P, e P = ((1 : R) - e QI) - ((∑ P, e P) - e QI) := by ring
    rw [hrw]
    exact Ideal.sub_mem _ h1e hsummem
  have hcomplete : ∑ P, e P = 1 := by
    have h0 := hone.eq_zero_of_isNilpotent hnil
    exact (sub_eq_zero.mp h0).symm
  exact ⟨e, ⟨horthS, hcomplete⟩, hnot, hmem⟩


end Aux

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  (A : Type*) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma mapMax_le (P : Ideal A) [P.IsMaximal] :
    (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) ≤ P := by
  have hint : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.of_finite 𝒪 A
  have hmax : (P.comap (algebraMap 𝒪 A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap 𝒪 A)
    (algebraMap_isIntegral_iff.mpr hint) P
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hmax]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  [Module.Finite 𝒪 A] in
private lemma mem_pow_iff (x : A) (n : ℕ) :
    x ∈ ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) ^ n ↔
      x ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A) := by
  rw [Ideal.smul_top_eq_map, ← Ideal.map_pow, Submodule.restrictScalars_mem]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

private lemma isArtinian_quotient :
    IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) := by
  set 𝔪 := IsLocalRing.maximalIdeal 𝒪 with h𝔪
  set J := 𝔪.map (algebraMap 𝒪 A) with hJ
  letI : Field (𝒪 ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  letI : Algebra (𝒪 ⧸ 𝔪) (A ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI : IsScalarTower 𝒪 (𝒪 ⧸ 𝔪) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite 𝒪 (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 J)
  haveI : Module.Finite (𝒪 ⧸ 𝔪) (A ⧸ J) := Module.Finite.of_restrictScalars_finite 𝒪 _ _
  exact isArtinian_of_tower (𝒪 ⧸ 𝔪) inferInstance

private noncomputable def maxSpecEquiv :
    MaximalSpectrum A ≃
      MaximalSpectrum (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) where
  toFun P :=
    ⟨P.asIdeal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))), by
      haveI := P.isMaximal
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
          Ideal.Quotient.mk_surjective P.isMaximal with h | h
      · exfalso
        have hcm := Ideal.comap_map_of_surjective
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
          Ideal.Quotient.mk_surjective P.asIdeal
        rw [h, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr (mapMax_le A P.asIdeal)] at hcm
        exact P.isMaximal.ne_top hcm.symm
      · exact h⟩
  invFun Q :=
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))), by
      haveI := Q.isMaximal
      exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective⟩
  left_inv P := by
    haveI := P.isMaximal
    refine MaximalSpectrum.ext ?_
    have hcm := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
      Ideal.Quotient.mk_surjective P.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (mapMax_le A P.asIdeal)] at hcm
    exact hcm
  right_inv Q := by
    haveI := Q.isMaximal
    refine MaximalSpectrum.ext ?_
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q.asIdeal

private lemma lift_idempotent (J : Ideal A)
    (hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A))
    (ē : A ⧸ J) (hē : IsIdempotentElem ē) :
    ∃ e : A, IsIdempotentElem e ∧ Ideal.Quotient.mk J e = ē := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) A :=
    IsAdicComplete.of_module_finite (IsLocalRing.maximalIdeal 𝒪)
  have hlift : ∀ n : ℕ, ∃ x : A,
      IsIdempotentElem (Ideal.Quotient.mk (J ^ (n + 1)) x) ∧ Ideal.Quotient.mk J x = ē := by
    intro n
    have hle : J ^ (n + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.factor hle), IsNilpotent x := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hy : y ∈ J := by
        rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
        exact hx
      exact ⟨n + 1, by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hy (n + 1)⟩
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := J) ē
    obtain ⟨etil, hetil, hetil_eq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
      (f := Ideal.Quotient.factor hle) hker ē
      ⟨Ideal.Quotient.mk (J ^ (n + 1)) y₀, by rw [Ideal.Quotient.factor_mk, hy₀]⟩ hē
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := J ^ (n + 1)) etil
    refine ⟨x, by rw [hx]; exact hetil, ?_⟩
    rw [← Ideal.Quotient.factor_mk hle, hx, hetil_eq]
  choose f hfidem hfē using hlift
  have hsub : ∀ {m n : ℕ}, m ≤ n → f n - f m ∈ J ^ (m + 1) := by
    intro m n hmn
    have hle : J ^ (n + 1) ≤ J ^ (m + 1) := Ideal.pow_le_pow_right (by omega)
    have h1 : IsIdempotentElem (Ideal.Quotient.mk (J ^ (m + 1)) (f n)) := by
      have := (hfidem n).map (Ideal.Quotient.factor hle)
      rwa [Ideal.Quotient.factor_mk] at this
    have h2 : IsIdempotentElem (Ideal.Quotient.mk (J ^ (m + 1)) (f m)) := hfidem m
    have hdJ : f n - f m ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hfē n, hfē m, sub_self]
    have hnil : IsNilpotent
        (Ideal.Quotient.mk (J ^ (m + 1)) (f n) - Ideal.Quotient.mk (J ^ (m + 1)) (f m)) := by
      refine ⟨m + 1, ?_⟩
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hdJ (m + 1)
    have heq := idem_eq_of_isNilpotent_sub h1 h2 hnil
    rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at heq
  have hconsist : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((IsLocalRing.maximalIdeal 𝒪) ^ m • ⊤ : Submodule 𝒪 A)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hJm : f n - f m ∈ J ^ m := Ideal.pow_le_pow_right (Nat.le_succ m) (hsub hmn)
    have : f m - f n ∈ J ^ m := by
      simpa using (neg_mem hJm : -(f n - f m) ∈ J ^ m)
    exact (hJpow _ m).mp this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete)
    fun {m n} hmn => hconsist hmn
  have hLn : ∀ n : ℕ, L - f n ∈ J ^ n := by
    intro n
    have hmem := (hJpow _ n).mpr (SModEq.sub_mem.mp (hL n))
    simpa using (neg_mem hmem : -(f n - L) ∈ J ^ n)
  refine ⟨L, ?_, ?_⟩
  · have hmem : ∀ n : ℕ, L * L - L ∈ J ^ n := by
      intro n
      have h1 : L * L - f n * f n ∈ J ^ n := by
        have hdecomp : L * L - f n * f n = (L - f n) * L + f n * (L - f n) := by ring
        rw [hdecomp]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hLn n))
          (Ideal.mul_mem_left _ _ (hLn n))
      have h2 : f n * f n - f n ∈ J ^ n := by
        have := hfidem n
        rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
        exact Ideal.pow_le_pow_right (Nat.le_succ n) this
      have h3 : f n - L ∈ J ^ n := by
        simpa using (neg_mem (hLn n) : -(L - f n) ∈ J ^ n)
      have hdecomp : L * L - L = (L * L - f n * f n) + (f n * f n - f n) + (f n - L) := by ring
      rw [hdecomp]
      exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
    have := IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal 𝒪)
      (M := A)) (L * L - L) fun n => SModEq.zero.mpr ((hJpow _ n).mp (hmem n))
    exact sub_eq_zero.mp this
  · have h1 : L - f 1 ∈ J := by
      have := hLn 1
      rwa [pow_one] at this
    rw [← hfē 1, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h1

private lemma idem_eq_zero_of_mem (J : Ideal A)
    (hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A))
    (x : A) (hx : IsIdempotentElem x) (hxJ : x ∈ J) : x = 0 := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) A :=
    IsAdicComplete.of_module_finite (IsLocalRing.maximalIdeal 𝒪)
  have hxn : ∀ n : ℕ, x ∈ J ^ n := by
    intro n
    have hidem : IsIdempotentElem (Ideal.Quotient.mk (J ^ n) x) := hx.map _
    have hnil : IsNilpotent (Ideal.Quotient.mk (J ^ n) x) := ⟨n, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hxJ n⟩
    have := hidem.eq_zero_of_isNilpotent hnil
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  exact IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal 𝒪)
    (M := A)) x fun n => SModEq.zero.mpr ((hJpow x n).mp (hxn n))

include 𝒪 in
omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

private lemma finite_maxSpec : Finite (MaximalSpectrum A) := by
  haveI : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :=
    isArtinian_quotient A
  haveI : Finite
      (MaximalSpectrum (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))) := by
    haveI : Finite {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) //
        I.IsMaximal} := (IsArtinianRing.setOfPred_isMaximal_finite
      (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))).to_subtype
    exact Finite.of_equiv _ (MaximalSpectrum.equivSubtype _).symm
  exact Finite.of_equiv _ (maxSpecEquiv (𝒪 := 𝒪) A).symm

include 𝒪 in

private lemma lifted_idempotents [Fintype (MaximalSpectrum A)] :
    ∃ e : MaximalSpectrum A → A, CompleteOrthogonalIdempotents e ∧
      (∀ P : MaximalSpectrum A, e P ∉ P.asIdeal) ∧
      (∀ P Q : MaximalSpectrum A, Q ≠ P → e P ∈ Q.asIdeal) := by
  classical
  set J := (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) with hJdef
  have hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A) := mem_pow_iff A
  haveI hart : IsArtinianRing (A ⧸ J) := isArtinian_quotient (𝒪 := 𝒪) A
  letI : Fintype (MaximalSpectrum (A ⧸ J)) :=
    Fintype.ofEquiv _ (maxSpecEquiv (𝒪 := 𝒪) A)
  obtain ⟨ē, hēco, hēnot, hēmem⟩ := exists_completeOrthogonalIdempotents (A ⧸ J)
  set Φ := maxSpecEquiv (𝒪 := 𝒪) A with hΦdef
  have hlift : ∀ P : MaximalSpectrum A, ∃ x : A, IsIdempotentElem x ∧
      Ideal.Quotient.mk J x = ē (Φ P) := fun P =>
    lift_idempotent A J hJpow (ē (Φ P)) (hēco.idem _)
  choose e heidem hemk using hlift
  have horth : ∀ P Q : MaximalSpectrum A, P ≠ Q → e P * e Q = 0 := by
    intro P Q hPQ
    refine idem_eq_zero_of_mem A J hJpow _
      ((heidem P).mul_of_commute (Commute.all _ _) (heidem Q)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hemk, hemk]
    exact hēco.ortho fun h => hPQ (Φ.injective h)
  have horthS : OrthogonalIdempotents e := ⟨heidem, horth⟩
  have hcomplete : ∑ P, e P = 1 := by
    have hsum : IsIdempotentElem (∑ P, e P) := horthS.isIdempotentElem_sum
    have hone : IsIdempotentElem (1 - ∑ P, e P) := hsum.one_sub
    have hmem1 : (1 : A) - ∑ P, e P ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_sum]
      have hre : ∑ P : MaximalSpectrum A, Ideal.Quotient.mk J (e P) = ∑ P, ē (Φ P) :=
        Finset.sum_congr rfl fun P _ => hemk P
      rw [hre, Equiv.sum_comp Φ ē, hēco.complete, sub_self]
    have := idem_eq_zero_of_mem A J hJpow _ hone hmem1
    exact (sub_eq_zero.mp this).symm
  refine ⟨e, ⟨horthS, hcomplete⟩, ?_, ?_⟩
  · intro P hP
    refine hēnot (Φ P) ?_
    rw [← hemk P]
    exact Ideal.mem_map_of_mem _ hP
  · intro P Q hQP
    have hΦne : Φ Q ≠ Φ P := fun h => hQP (Φ.injective h)
    have hmem' : ē (Φ P) ∈ (Φ Q).asIdeal := hēmem (Φ P) (Φ Q) hΦne
    have hmk : Ideal.Quotient.mk J (e P) ∈ Q.asIdeal.map (Ideal.Quotient.mk J) := by
      rw [hemk P]
      exact hmem'
    have hcm : e P ∈ (Q.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) :=
      Ideal.mem_comap.mpr hmk
    haveI := Q.isMaximal
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (mapMax_le A Q.asIdeal)] at hcm

private lemma isLocalization_of_idempotent (P : MaximalSpectrum A) (e : A) (he : IsIdempotentElem e)
    (hnot : e ∉ P.asIdeal) (hmem : ∀ Q : MaximalSpectrum A, Q ≠ P → e ∈ Q.asIdeal) :
    IsLocalization P.asIdeal.primeCompl (A ⧸ Ideal.span {1 - e}) := by
  haveI := P.isMaximal
  have h1eP : 1 - e ∈ P.asIdeal := by
    have h0 : e * (1 - e) ∈ P.asIdeal := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact Ideal.zero_mem _
    rcases P.isMaximal.isPrime.mem_or_mem h0 with h | h
    · exact absurd h hnot
    · exact h
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra hunit
    obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) s})
      (fun htop => hunit (by
        rw [Ideal.span_singleton_eq_top] at htop
        exact htop))
    have hsM' : Ideal.Quotient.mk (Ideal.span {1 - e}) s ∈ M :=
      hsM (Ideal.subset_span rfl)
    haveI := hM
    have hQmax : (M.comap (Ideal.Quotient.mk (Ideal.span {1 - e}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    set Q : MaximalSpectrum A := ⟨M.comap (Ideal.Quotient.mk (Ideal.span {1 - e})), hQmax⟩
    have h1eQ : 1 - e ∈ Q.asIdeal := by
      change 1 - e ∈ M.comap (Ideal.Quotient.mk (Ideal.span {1 - e}))
      rw [Ideal.mem_comap]
      have hz : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [hz]
      exact M.zero_mem
    have hQP : Q = P := by
      by_contra hQP
      have heQ : e ∈ Q.asIdeal := hmem Q hQP
      have : (1 : A) ∈ Q.asIdeal := by
        have := Ideal.add_mem Q.asIdeal h1eQ heQ
        simpa using this
      exact Q.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hsP : s ∈ P.asIdeal := by
      rw [← hQP]
      exact Ideal.mem_comap.mpr hsM'
    exact hs hsP
  · intro z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨a, 1⟩, by simpa using ha.symm⟩
  · intro x y hxy
    have hsub : x - y ∈ Ideal.span {1 - e} := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hxy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hsub
    refine ⟨⟨e, hnot⟩, ?_⟩
    have h0 : e * (1 - e) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    have hxy0 : e * (x - y) = 0 := by
      rw [ht, ← mul_assoc, h0, zero_mul]
    have : e * x - e * y = 0 := by
      rw [← mul_sub]
      exact hxy0
    exact sub_eq_zero.mp this

end Main

end FiniteAlgebraDecompositionAux

namespace Algebra

/-- A finite algebra `A` over a complete Noetherian local ring `𝒪` has
finitely many maximal ideals. The diagonal map from `A` to the product of
its localizations at those maximal ideals is bijective, each localization
is finite over `𝒪`, and each localization is complete at its maximal
ideal. -/
theorem finite_maximalSpectrum_and_bijective_localization_of_module_finite
    {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type*) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) := by
  classical
  have hfin : Finite (MaximalSpectrum A) := FiniteAlgebraDecompositionAux.finite_maxSpec (𝒪 := 𝒪) A
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  obtain ⟨e, heco, henot, hemem⟩ := FiniteAlgebraDecompositionAux.lifted_idempotents (𝒪 := 𝒪) A
  have hloc : ∀ P : MaximalSpectrum A,
      IsLocalization P.asIdeal.primeCompl (A ⧸ Ideal.span {1 - e P}) := fun P =>
    FiniteAlgebraDecompositionAux.isLocalization_of_idempotent A P (e P) (heco.idem P)
      (henot P) fun Q hQ => hemem P Q hQ
  have ψ : ∀ P : MaximalSpectrum A,
      (A ⧸ Ideal.span {1 - e P}) ≃ₐ[A] Localization.AtPrime P.asIdeal := fun P =>
    haveI := hloc P
    IsLocalization.algEquiv P.asIdeal.primeCompl _ _
  have hsurjloc : ∀ P : MaximalSpectrum A,
      Function.Surjective (algebraMap A (Localization.AtPrime P.asIdeal)) := by
    intro P z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((ψ P).symm z)
    refine ⟨a, ?_⟩
    have hψ := congrArg (ψ P) ha
    rwa [← Ideal.Quotient.algebraMap_eq, AlgEquiv.commutes,
      AlgEquiv.apply_symm_apply] at hψ
  have hfinloc : ∀ P : MaximalSpectrum A,
      Module.Finite 𝒪 (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective (IsScalarTower.toAlgHom 𝒪 A _).toLinearMap (hsurjloc P)
  refine ⟨hfin, ?_, hfinloc, ?_⟩
  · have hΨ := heco.bijective_pi
    have hcomp : ⇑(RingHom.pi fun P : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime P.asIdeal)) =
        ⇑(RingEquiv.piCongrRight fun P => (ψ P).toRingEquiv) ∘
          ⇑(RingHom.pi fun P : MaximalSpectrum A =>
            Ideal.Quotient.mk (Ideal.span {1 - e P})) := by
      funext a
      funext P
      show algebraMap A (Localization.AtPrime P.asIdeal) a =
        ψ P (Ideal.Quotient.mk (Ideal.span {1 - e P}) a)
      rw [← Ideal.Quotient.algebraMap_eq, AlgEquiv.commutes]
    rw [hcomp]
    exact (RingEquiv.piCongrRight fun P => (ψ P).toRingEquiv).bijective.comp hΨ
  · intro P
    haveI := hfinloc P
    haveI : IsLocalHom (algebraMap 𝒪 (Localization.AtPrime P.asIdeal)) := by
      constructor
      intro a ha
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal 𝒪 := hna
      have h1 : algebraMap 𝒪 A a ∈ P.asIdeal :=
        FiniteAlgebraDecompositionAux.mapMax_le (𝒪 := 𝒪) A P.asIdeal (Ideal.mem_map_of_mem _ hm)
      have h2 : algebraMap A (Localization.AtPrime P.asIdeal) (algebraMap 𝒪 A a) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P.asIdeal _).mpr h1
      rw [← IsScalarTower.algebraMap_apply] at h2
      exact h2 ha
    exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)
      (T := Localization.AtPrime P.asIdeal)

end Algebra
