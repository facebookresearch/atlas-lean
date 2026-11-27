/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_exists_algEquiv_localization_atPrime_
mvPowerSeries_quotient_apply_mk.lean`
and
`P2M/Sol/S_MvPolynomial_exists_algEquiv_localization_atPrime_
mvPowerSeries_quotient_apply_mk.lean`
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

public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Artinian local polynomial quotients as power-series quotients

Let `K` be a field, `g : Fin r → MvPolynomial (Fin m) K` a finite family of
relations, and `𝔫` a maximal ideal of `K[X]/(g)` containing the class of
every variable, such that the localization at `𝔫` is finite-dimensional
over `K`. Then that localization is canonically isomorphic, as a
`K`-algebra, to the quotient of the formal power-series ring
`K⟦X⟧` by the same relations, and the isomorphism sends each localized
polynomial to its power-series class.
-/

@[expose] public section

open scoped TensorProduct

namespace MvPolynomialLocalizationAux

open MvPowerSeries

section LemmaD

variable {K : Type*} [CommRing K] {n : ℕ}

private theorem mem_span_X_pow_of_coeff_eq_zero_aux (N : ℕ) :
    ∀ (k : ℕ) (f : MvPowerSeries (Fin n) K),
      (∀ mo : Fin n →₀ ℕ, (∀ i : Fin n, (i : ℕ) < k → mo i ≤ N) → coeff mo f = 0) →
      f ∈ Ideal.span (Set.range fun i : Fin n => (X i : MvPowerSeries (Fin n) K) ^ (N + 1)) := by
  intro k
  induction k with
  | zero =>
    intro f hf
    have : f = 0 := MvPowerSeries.ext fun mo => by
      rw [hf mo (fun i hi => absurd hi (Nat.not_lt_zero _)), map_zero]
    rw [this]
    exact Ideal.zero_mem _
  | succ k ih =>
    intro f hf
    by_cases hk : k < n
    ·
      set i₀ : Fin n := ⟨k, hk⟩ with hi₀
      let r : MvPowerSeries (Fin n) K := fun mo => if mo i₀ ≤ N then coeff mo f else 0
      have hr : ∀ mo, coeff mo r = if mo i₀ ≤ N then coeff mo f else 0 := fun _ => rfl
      have hdiv : (X i₀ : MvPowerSeries (Fin n) K) ^ (N + 1) ∣ (f - r) := by
        rw [X_pow_dvd_iff]
        intro mo hmo
        rw [map_sub, hr, if_pos (Nat.lt_succ_iff.mp hmo), sub_self]
      have hrmem : r ∈ Ideal.span (Set.range fun i : Fin n =>
          (X i : MvPowerSeries (Fin n) K) ^ (N + 1)) := by
        refine ih r fun mo hmo => ?_
        rw [hr]
        split_ifs with h
        · refine hf mo fun i hi => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
          · exact hmo i hlt
          · have : i = i₀ := Fin.ext heq
            rw [this]; exact h
        · rfl
      have : f = (f - r) + r := by ring
      rw [this]
      refine Ideal.add_mem _ ?_ hrmem
      obtain ⟨q, hq⟩ := hdiv
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i₀, rfl⟩)
    ·
      refine ih f fun mo hmo => hf mo fun i hi => hmo i ?_
      have := i.isLt
      omega

private theorem mem_span_X_pow_of_coeff_eq_zero (N : ℕ) (f : MvPowerSeries (Fin n) K)
    (hf : ∀ mo : Fin n →₀ ℕ, (∀ i, mo i ≤ N) → coeff mo f = 0) :
    f ∈ Ideal.span (Set.range fun i : Fin n => (X i : MvPowerSeries (Fin n) K) ^ (N + 1)) :=
  mem_span_X_pow_of_coeff_eq_zero_aux N n f fun mo hmo => hf mo fun i => hmo i i.isLt

private theorem coeff_mul_eq_zero_of_coeff_eq_zero (N : ℕ) (h g : MvPowerSeries (Fin n) K)
    (hh : ∀ mo : Fin n →₀ ℕ, (∀ i, mo i ≤ N) → coeff mo h = 0)
    (mo : Fin n →₀ ℕ) (hmo : ∀ i, mo i ≤ N) : coeff mo (h * g) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hh p.1 fun i => ?_, zero_mul]
  have : p.1 i ≤ mo i := by rw [← hp]; exact Nat.le_add_right _ _
  exact this.trans (hmo i)

end LemmaD

section Main

variable (K : Type*) [Field K] {m r : ℕ}

private theorem eval_eq_zero_of_coeff_eq_zero {S : Type*} [CommRing S]
    (φ : MvPolynomial (Fin m) K →+* S) (N : ℕ)
    (hφ : ∀ i, φ (MvPolynomial.X i) ^ (N + 1) = 0)
    (p : MvPolynomial (Fin m) K)
    (hp : ∀ mo : Fin m →₀ ℕ, (∀ i, mo i ≤ N) → p.coeff mo = 0) :
    φ p = 0 := by
  classical
  rw [MvPolynomial.as_sum p, map_sum]
  refine Finset.sum_eq_zero fun mo hmo => ?_
  have hex : ∃ i, N + 1 ≤ mo i := by
    by_contra h
    push Not at h
    exact (MvPolynomial.mem_support_iff.mp hmo) (hp mo fun i => Nat.lt_succ_iff.mp (h i))
  obtain ⟨i, hi⟩ := hex
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  have hi' : i ∈ mo.support := by
    rw [Finsupp.mem_support_iff]; omega
  rw [← Finset.mul_prod_erase _ _ hi', map_pow]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
  rw [hd, pow_add, hφ i]
  simp

end Main

end MvPolynomialLocalizationAux

namespace MvPolynomial

open MvPolynomialLocalizationAux

/-- An Artinian local polynomial quotient at the origin is canonically the
quotient of the corresponding formal power-series ring by the same finite
equations: the localization of `K[X]/(g)` at a maximal ideal containing
every variable class, when finite over `K`, is `K`-algebra isomorphic to
`K⟦X⟧/(g)`, by an isomorphism sending each localized polynomial to its
power-series class. -/
public theorem exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk
    (K : Type*) [Field K] {m r : ℕ} (g : Fin r → MvPolynomial (Fin m) K)
    (𝔫 : Ideal (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))) [𝔫.IsMaximal]
    (h𝔫 : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j) ∈ 𝔫)
    [Module.Finite K (Localization.AtPrime 𝔫)] :
    ∃ e : Localization.AtPrime 𝔫 ≃ₐ[K]
      (MvPowerSeries (Fin m) K ⧸
        Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))),
      ∀ p : MvPolynomial (Fin m) K,
        e (algebraMap (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
            (Localization.AtPrime 𝔫)
            (Ideal.Quotient.mk (Ideal.span (Set.range g)) p)) =
          Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
            (p : MvPowerSeries (Fin m) K) := by
  classical
  let ι : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K :=
    { MvPolynomial.coeToMvPowerSeries.ringHom with
      commutes' := fun c => by
        show ((MvPolynomial.C c : MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) = _
        rw [MvPolynomial.coe_C]; rfl }
  have hι : ∀ p, ι p = (p : MvPowerSeries (Fin m) K) := fun _ => rfl
  have hJmap : (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) =
      (Ideal.span (Set.range g)).map ι := by
    rw [Ideal.map_span]
    congr 1
    ext f
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  let ψ₁ : MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K ⧸
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) :=
    (Ideal.Quotient.mkₐ K
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))).comp ι
  have hψ₁ : ∀ a ∈ (Ideal.span (Set.range g)), ψ₁ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) (ι a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hJmap]
    exact Ideal.mem_map_of_mem _ ha
  let ψ₀ : (MvPolynomial (Fin m) K ⧸ (Ideal.span (Set.range g))) →ₐ[K]
      MvPowerSeries (Fin m) K ⧸
        (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) :=
    Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) ψ₁ hψ₁
  have hψ₀ : ∀ p : MvPolynomial (Fin m) K,
      ψ₀ (Ideal.Quotient.mk (Ideal.span (Set.range g)) p) = Ideal.Quotient.mk
        (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
        (p : MvPowerSeries (Fin m) K) := fun _ => rfl
  have hunit_poly : ∀ p : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∉ 𝔫 →
      IsUnit (p : MvPowerSeries (Fin m) K) := by
    intro p hp
    rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    intro h0
    apply hp
    have hmem : p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) K)) := by
      rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
      intro mo hmo
      by_contra hall
      push Not at hall
      have hz : mo = 0 := Finsupp.ext fun i => hall i (Set.mem_univ i)
      subst hz
      rw [MvPolynomial.mem_support_iff] at hmo
      apply hmo
      have : MvPowerSeries.constantCoeff (p : MvPowerSeries (Fin m) K) =
          p.coeff 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
      rw [← this, h0]
    have hle : Ideal.span (Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) K)) ≤
        𝔫.comap (Ideal.Quotient.mk (Ideal.span (Set.range g))) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h𝔫 j
    exact hle hmem
  have hunits : ∀ y : 𝔫.primeCompl, IsUnit (ψ₀ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hψ₀]
    exact (hunit_poly p hy).map _
  let Ψ : (Localization.AtPrime 𝔫) →ₐ[K] MvPowerSeries (Fin m) K ⧸
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) :=
    IsLocalization.liftAlgHom (M := 𝔫.primeCompl) hunits
  have hΨ : ∀ a, Ψ (algebraMap _ (Localization.AtPrime 𝔫) a) = ψ₀ a :=
    fun a => IsLocalization.lift_eq (M := 𝔫.primeCompl) _ a
  haveI : IsArtinianRing (Localization.AtPrime 𝔫) :=
    IsArtinianRing.of_finite K (Localization.AtPrime 𝔫)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := (Localization.AtPrime 𝔫))
  have hjac : ∀ z ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫),
      z ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime 𝔫)) := by
    intro z hz
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    rw [IsLocalRing.eq_maximalIdeal hM]
    exact hz
  let φloc : MvPolynomial (Fin m) K →+* (Localization.AtPrime 𝔫) :=
    (algebraMap _ (Localization.AtPrime 𝔫)).comp
      (Ideal.Quotient.mk (Ideal.span (Set.range g)))
  have hφloc : ∀ p, φloc p = algebraMap _ (Localization.AtPrime 𝔫)
      (Ideal.Quotient.mk (Ideal.span (Set.range g)) p) := fun _ => rfl
  have hxloc : ∀ i, φloc (MvPolynomial.X i) ^ (N + 1) = 0 := by
    intro i
    have hmem : φloc (MvPolynomial.X i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) := by
      rw [hφloc, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔫) 𝔫]
      exact h𝔫 i
    have hpow : φloc (MvPolynomial.X i) ^ N = 0 := by
      have := Ideal.pow_mem_pow (hjac _ hmem) N
      rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact this
    rw [pow_succ, hpow, zero_mul]
  have hXJ : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin m) K) ^ (N + 1) ∈
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) := by
    intro i
    have h0 : algebraMap _ (Localization.AtPrime 𝔫)
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X i ^ (N + 1))) = 0 := by
      rw [← hφloc, map_pow]; exact hxloc i
    obtain ⟨⟨t, ht⟩, htx⟩ :=
      (IsLocalization.map_eq_zero_iff 𝔫.primeCompl (Localization.AtPrime 𝔫) _).1 h0
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hqI : q * MvPolynomial.X i ^ (N + 1) ∈ (Ideal.span (Set.range g)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact htx
    have hqJ : (q : MvPowerSeries (Fin m) K) * (MvPowerSeries.X i) ^ (N + 1) ∈
        (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) := by
      have := Ideal.mem_map_of_mem ι hqI
      rw [← hJmap, map_mul, map_pow, hι, hι, MvPolynomial.coe_X] at this
      exact this
    exact (Ideal.unit_mul_mem_iff_mem
      (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
      (hunit_poly q ht)).1 hqJ
  let b : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hb : ∀ (mo : Fin m →₀ ℕ), mo ≤ b ↔ ∀ i, mo i ≤ N := fun mo => by
    simp only [Finsupp.le_def, b, Finsupp.coe_equivFunOnFinite_symm]
  have hUJ : ∀ f : MvPowerSeries (Fin m) K,
      (∀ mo : Fin m →₀ ℕ, (∀ i, mo i ≤ N) → MvPowerSeries.coeff mo f = 0) →
      f ∈ (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) := by
    intro f hf
    have := mem_span_X_pow_of_coeff_eq_zero N f hf
    refine (Ideal.span_le.2 ?_) this
    rintro _ ⟨i, rfl⟩
    exact hXJ i
  have hkerA : ∀ a : MvPolynomial (Fin m) K ⧸ (Ideal.span (Set.range g)), ψ₀ a = 0 →
      ∃ c : 𝔫.primeCompl, (c : MvPolynomial (Fin m) K ⧸ (Ideal.span (Set.range g))) * a = 0 := by
    intro a ha0
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hψ₀, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at ha0
    obtain ⟨h, hh⟩ := ha0
    let t : Fin r → MvPolynomial (Fin m) K := fun k => MvPowerSeries.trunc' K b (h k)
    have hbox : ∀ mo : Fin m →₀ ℕ, (∀ i, mo i ≤ N) →
        (p - ∑ k, t k * g k).coeff mo = 0 := by
      intro mo hmo
      have hcoe : ((p - ∑ k, t k * g k : MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) =
          ∑ k, (h k - (t k : MvPowerSeries (Fin m) K)) * (g k : MvPowerSeries (Fin m) K) := by
        rw [← hι, map_sub, map_sum, hι, ← hh, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, hι, hι, sub_mul]
      rw [← MvPolynomial.coeff_coe, hcoe, map_sum]
      refine Finset.sum_eq_zero fun k _ =>
        coeff_mul_eq_zero_of_coeff_eq_zero N _ _ (fun mo' hmo' => ?_) mo hmo
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc',
        if_pos ((hb mo').2 hmo'), sub_self]
    have hp0 : φloc p = 0 := by
      have h1 : φloc (p - ∑ k, t k * g k) = 0 :=
        eval_eq_zero_of_coeff_eq_zero K (S := (Localization.AtPrime 𝔫)) φloc N hxloc
          (p - ∑ k, t k * g k) hbox
      have hpA : Ideal.Quotient.mk (Ideal.span (Set.range g)) p =
          Ideal.Quotient.mk (Ideal.span (Set.range g)) (p - ∑ k, t k * g k) := by
        rw [Ideal.Quotient.eq, sub_sub_cancel]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
      rw [hφloc, hpA, ← hφloc]
      exact h1
    exact (IsLocalization.map_eq_zero_iff 𝔫.primeCompl (Localization.AtPrime 𝔫) _).1 hp0
  have hinj : Function.Injective Ψ := by
    have hfun : ∀ z, Ψ z = IsLocalization.lift (M := 𝔫.primeCompl) hunits z :=
      fun z => IsLocalization.liftAlgHom_apply (M := 𝔫.primeCompl) hunits z
    have hlift : Function.Injective
        (IsLocalization.lift (M := 𝔫.primeCompl) (S := Localization.AtPrime 𝔫) hunits) := by
      rw [IsLocalization.lift_injective_iff]
      intro x y
      constructor
      · intro h
        have := congrArg Ψ h
        rw [hΨ, hΨ] at this
        exact this
      · intro h
        rw [IsLocalization.eq_iff_exists 𝔫.primeCompl]
        have h0 : ψ₀ (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact h
        obtain ⟨c, hc⟩ := hkerA (x - y) h0
        exact ⟨c, by rw [mul_sub, sub_eq_zero] at hc; exact hc⟩
    intro z₁ z₂ h
    rw [hfun, hfun] at h
    exact hlift h
  have hsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨algebraMap _ (Localization.AtPrime 𝔫)
      (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPowerSeries.trunc' K b f)), ?_⟩
    rw [hΨ, hψ₀, Ideal.Quotient.eq, ← Ideal.neg_mem_iff, neg_sub]
    refine hUJ _ fun mo hmo => ?_
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc',
      if_pos ((hb mo).2 hmo), sub_self]
  have hbij : Function.Bijective Ψ := ⟨hinj, hsurj⟩
  exact ⟨AlgEquiv.ofBijective Ψ hbij, fun p => by
    rw [AlgEquiv.ofBijective_apply, hΨ, hψ₀]⟩

end MvPolynomial
