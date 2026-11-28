/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv.lean`
and
`P2M/Sol/S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u

namespace AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨a, rfl⟩ := mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk]
  exact Ideal.mk_eq_mk I hle a

private theorem exists_ringEquiv (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ I ^ n),
      e m (Ideal.Quotient.factorPow I hle x) =
        Ideal.Quotient.factorPow J hle (e n x)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ (n : ℕ) (x : AdicCompletion I R),
        evalₐ J n (E x) = e n (evalₐ I n x) := by
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : S ⧸ J ^ n),
      (e m).symm (Ideal.Quotient.factorPow J hle y) =
        Ideal.Quotient.factorPow I hle ((e n).symm y) := by
    intro m n hle y
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom) (by
      intro m n hle
      ext x
      show Ideal.Quotient.factorPow J hle (e n (evalₐ I n x)) =
        e m (evalₐ I m x)
      rw [← he, factorPow_evalₐ])
  let G : AdicCompletion J S →+* AdicCompletion I R :=
    liftRingHom I (fun n => (e n).symm.toRingHom.comp (evalₐ J n).toRingHom) (by
      intro m n hle
      ext y
      show Ideal.Quotient.factorPow I hle ((e n).symm (evalₐ J n y)) =
        (e m).symm (evalₐ J m y)
      rw [← he', factorPow_evalₐ])
  have hF : ∀ n x, evalₐ J n (F x) = e n (evalₐ I n x) :=
    fun n x => evalₐ_liftRingHom J _ _ n x
  have hG : ∀ n y, evalₐ I n (G y) = (e n).symm (evalₐ J n y) :=
    fun n y => evalₐ_liftRingHom I _ _ n y
  refine ⟨RingEquiv.ofRingHom F G (RingHom.ext fun y => ?_)
    (RingHom.ext fun x => ?_), hF⟩
  · apply ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · apply ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

private theorem apply_of_eq_of (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (E : AdicCompletion I R ≃+* AdicCompletion J S)
    (hE : ∀ (n : ℕ) (x : AdicCompletion I R),
      evalₐ J n (E x) = e n (evalₐ I n x))
    (θ : R → S) (hθ : ∀ (n : ℕ) (r : R),
      e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (θ r))
    (r : R) :
    E (of I R r) = of J S (θ r) := by
  apply ext_evalₐ
  intro n
  rw [hE, evalₐ_of, hθ, evalₐ_of]

end AdicCompletion

/-- The adic completion of a commutative ring at a maximal ideal is
ring-isomorphic to the completion of its localization at that ideal at the
maximal ideal of the localization, compatibly with the maps from the ring. -/
public theorem Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv
    {C : Type u} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪))
          (Localization.AtPrime 𝔪) ≃+* AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _
          (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c := by
  classical
  have hmap : ∀ n : ℕ, (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪)) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n := by
    intro n
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  have hunit : ∀ (n : ℕ) (s : C), s ∉ 𝔪 →
      IsUnit (Ideal.Quotient.mk (𝔪 ^ n) s) := by
    intro n s hs
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hs
    have hnil : IsNilpotent (Ideal.Quotient.mk (𝔪 ^ n) i) :=
      ⟨n, by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hi n⟩
    have h1 : Ideal.Quotient.mk (𝔪 ^ n) y * Ideal.Quotient.mk (𝔪 ^ n) s =
        1 - Ideal.Quotient.mk (𝔪 ^ n) i := by
      rw [← map_mul, eq_sub_of_add_eq hyi, map_sub, map_one]
    exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)
  have hU : ∀ n : ℕ,
      Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl ≤
        IsUnit.submonoid (C ⧸ 𝔪 ^ n) := by
    intro n x hx
    rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact hunit n s hs
  let d : ∀ n : ℕ, C ⧸ 𝔪 ^ n ≃+*
      Localization.AtPrime 𝔪 ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n :=
    fun n =>
      (IsLocalization.atUnits (C ⧸ 𝔪 ^ n)
          (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
          (S := Localization.AtPrime 𝔪 ⧸
            (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).toRingEquiv.trans
        (Ideal.quotEquivOfEq (hmap n))
  have hd_mk : ∀ (n : ℕ) (c : C), d n (Ideal.Quotient.mk (𝔪 ^ n) c) =
      Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime 𝔪) c) := by
    intro n c
    have h := (IsLocalization.atUnits (C ⧸ 𝔪 ^ n)
        (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
        (S := Localization.AtPrime 𝔪 ⧸
          (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).commutes
      (Ideal.Quotient.mk (𝔪 ^ n) c)
    rw [Algebra.algebraMap_self, RingHom.id_apply,
      Ideal.Quotient.algebraMap_quotient_map_quotient] at h
    show Ideal.quotEquivOfEq (hmap n)
      (IsLocalization.atUnits (C ⧸ 𝔪 ^ n)
        (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
        (S := Localization.AtPrime 𝔪 ⧸
          (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)
        (Ideal.Quotient.mk (𝔪 ^ n) c)) = _
    rw [h, Ideal.quotEquivOfEq_mk]
  have hd : ∀ {m n : ℕ} (hle : m ≤ n) (x : C ⧸ 𝔪 ^ n),
      d m (Ideal.Quotient.factorPow 𝔪 hle x) =
        Ideal.Quotient.factorPow _ hle (d n x) := by
    intro m n hle x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, hd_mk, hd_mk, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv 𝔪
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) d hd
  refine ⟨E.symm, fun c => ?_⟩
  apply E.injective
  rw [RingEquiv.apply_symm_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]
  exact (AdicCompletion.apply_of_eq_of 𝔪
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) d E hE
    (algebraMap C (Localization.AtPrime 𝔪)) hd_mk c).symm
