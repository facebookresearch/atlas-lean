/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_
comap.lean`,
`P2M/Sol/S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_
comap.lean`,
`Theorems/Thm_AdicCompletion_exists_ringEquiv_map_of_ringEquiv.lean`,
`P2M/Sol/S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv.lean`,
`Theorems/Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_
comp_algebraMap_of_ringEquiv.lean` and
`P2M/Sol/S_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_
comp_algebraMap_of_ringEquiv.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Functoriality of adic completions

A ring homomorphism compatible with the adic topologies lifts to the
completion of a complete target; ring equivalences induce equivalences of
completions, in particular for the maximal-ideal completions of local
rings.
-/

@[expose] public section

universe u v

namespace AdicCompletionFunctorialityAux

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private noncomputable def levelMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (hf n)).comp
    (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)

private theorem levelMap_compat (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (levelMap I J f hf n) = levelMap I J f hf m := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [levelMap, RingHom.coe_comp, Function.comp_apply]
  have hn : (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)
        (AdicCompletion.mk I R a) = Ideal.Quotient.mk (I ^ n) (a.val n) :=
    AdicCompletion.evalₐ_mk I n a
  have hm : (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)
        (AdicCompletion.mk I R a) = Ideal.Quotient.mk (I ^ m) (a.val m) :=
    AdicCompletion.evalₐ_mk I m a
  rw [hn, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  change Ideal.Quotient.factor _ (Ideal.Quotient.mk (J ^ n) (f (a.val n))) =
    Ideal.Quotient.mk (J ^ m) (f (a.val m))
  rw [Ideal.Quotient.factor_mk]
  have hthis := congrArg (Ideal.quotientMap (J ^ m) f (hf m))
    (AdicCompletion.Ideal.mk_eq_mk I hle a)
  rwa [Ideal.quotientMap_mk, Ideal.quotientMap_mk] at hthis

private noncomputable def transportHom (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (levelMap I J f hf)
    (fun hle => levelMap_compat I J f hf hle)

private theorem evalₐ_transportHom (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (transportHom I J f hf x) =
      Ideal.quotientMap (J ^ n) f (hf n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J (levelMap I J f hf)
    (fun hle => levelMap_compat I J f hf hle) n x

private theorem exists_monotone_modulus {B : Type*} [CommRing B] (𝔪 : Ideal B)
    {S : Type*} [CommRing S] (J : Ideal S) (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ N : ℕ → ℕ, Monotone N ∧ ∀ k, 𝔪 ^ N k ≤ (J ^ k).comap ev := by
  choose n hn using hcont
  refine ⟨fun k => (Finset.range (k + 1)).sup n,
    fun a b hab => Finset.sup_mono (Finset.range_mono (by omega)), fun k => ?_⟩
  exact (Ideal.pow_le_pow_right (Finset.le_sup (f := n)
    (Finset.self_mem_range_succ k))).trans (hn k)

end AdicCompletionFunctorialityAux

open AdicCompletionFunctorialityAux in
/-- A ring homomorphism compatible with the adic topologies lifts to a map
from the adic completion into an adically complete target. -/
theorem AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
    {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S)
    [IsAdicComplete J S] (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ ψ : AdicCompletion 𝔪 B →+* S, ψ.comp (algebraMap B (AdicCompletion 𝔪 B)) = ev := by
  obtain ⟨N, hNmono, hN⟩ := exists_monotone_modulus 𝔪 J ev hcont
  let f : (k : ℕ) → AdicCompletion 𝔪 B →+* S ⧸ J ^ k := fun k =>
    (Ideal.quotientMap (J ^ k) ev (hN k)).comp (AdicCompletion.evalₐ 𝔪 (N k)).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    apply RingHom.ext
    intro x
    induction x using AdicCompletion.induction_on with
    | _ a =>
      simp only [f, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      apply hN m
      have h := AdicCompletion.Ideal.mk_eq_mk (I := 𝔪) (hNmono hle) a
      rw [Ideal.Quotient.eq] at h
      simpa [smul_eq_mul, Ideal.mul_top] using h
  refine ⟨IsAdicComplete.liftRingHom J f hf, ?_⟩
  apply RingHom.ext
  intro b
  rw [RingHom.comp_apply]
  apply eq_of_sub_eq_zero
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := J) (R := S))
  intro k
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq,
    IsAdicComplete.mk_liftRingHom]
  simp only [f, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

open AdicCompletionFunctorialityAux in
/-- A ring equivalence induces an equivalence of adic completions. -/
theorem AdicCompletion.exists_ringEquiv_map_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S) :
    ∃ ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion I R) r) =
        algebraMap S (AdicCompletion (I.map e) S) (e r) := by
  classical
  have hJn : ∀ n : ℕ, (I.map e) ^ n = (I ^ n).map (e : R →+* S) := fun n =>
    (Ideal.map_pow (e : R →+* S) I n).symm
  have hf : ∀ n : ℕ, I ^ n ≤ ((I.map e) ^ n).comap (e : R →+* S) := by
    intro n x hx
    rw [Ideal.mem_comap, hJn]
    exact Ideal.mem_map_of_mem _ hx
  have hg : ∀ n : ℕ, (I.map e) ^ n ≤ (I ^ n).comap (e.symm : S →+* R) := by
    intro n y hy
    rw [hJn, Ideal.map_comap_of_equiv] at hy
    exact hy
  let φ := transportHom I (I.map e) (e : R →+* S) hf
  let ψ := transportHom (I.map e) I (e.symm : S →+* R) hg
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I.map e) n y)
    rw [← hs, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  have hψφ : ∀ x, ψ (φ x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  let ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S :=
    { toFun := φ, invFun := ψ, left_inv := hψφ, right_inv := hφψ,
      map_mul' := fun x y => φ.map_mul x y, map_add' := fun x y => φ.map_add x y }
  refine ⟨ê, fun r => ?_⟩
  change φ (algebraMap R (AdicCompletion I R) r) =
    algebraMap S (AdicCompletion (I.map e) S) (e r)
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_transportHom, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  rfl

/-- A ring equivalence between local rings induces an equivalence of their
maximal-ideal adic completions. -/
theorem IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    ∃ ê : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by
  have hmap : (IsLocalRing.maximalIdeal R).map e = IsLocalRing.maximalIdeal S := by
    have hmax : ((IsLocalRing.maximalIdeal R).map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    exact IsLocalRing.eq_maximalIdeal hmax
  exact hmap ▸ AdicCompletion.exists_ringEquiv_map_of_ringEquiv
    (IsLocalRing.maximalIdeal R) e
