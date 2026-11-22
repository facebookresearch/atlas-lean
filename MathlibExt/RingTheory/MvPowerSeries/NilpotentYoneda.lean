/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent.lean`
and
`P2M/Sol/S_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent.lean`
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

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open MvPowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The finite set of monomials whose exponents are all at most `N`,
realised as first components of antidiagonal pairs. -/
noncomputable def boundFinset [Finite σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  letI : Fintype σ := Fintype.ofFinite σ
  letI : DecidableEq σ := Classical.decEq σ
  (Finset.antidiagonal (Finsupp.equivFunOnFinite.symm fun _ : σ => N)).image
    Prod.fst

theorem mem_boundFinset [Finite σ] {N : ℕ} {d : σ →₀ ℕ} :
    d ∈ boundFinset N ↔ ∀ s, d s ≤ N := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  unfold boundFinset
  simp only [Finset.mem_image, Finset.mem_antidiagonal, Prod.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨e, he⟩ s
    have h := Finsupp.ext_iff.mp he s
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm,
      Function.const_apply] at h
    omega
  · intro hd
    refine ⟨Finsupp.equivFunOnFinite.symm (fun _ : σ => N) - d, ?_⟩
    ext s
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.coe_equivFunOnFinite_symm, Function.const_apply]
    have hds := hd s
    omega

/-- Evaluation of a multivariate power series at a point of a nilpotent
ideal. If `J ^ N = ⊥` and every `x s` lies in `J`, then every monomial of
degree at least `N` evaluates to `0`, so the evaluation is the finite sum
over the monomials bounded by `N`. The value does not depend on the chosen
exponent `N`; see `nilpotentEval_eq_sum`. -/
noncomputable def nilpotentEval {C : Type*} [CommRing C] [Algebra R C] [Finite σ]
    (J : Ideal C) (hJ : IsNilpotent J) (x : σ → C) (_hx : ∀ s, x s ∈ J)
    (f : MvPowerSeries σ R) : C :=
  letI : Fintype σ := Fintype.ofFinite σ
  ∑ d ∈ boundFinset (Classical.choose hJ),
    algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e

variable {C : Type*} [CommRing C] [Algebra R C]

private theorem prod_pow_eq_zero_of_le_degree [Finite σ] (J : Ideal C) {N : ℕ}
    (hN : J ^ N = ⊥) {x : σ → C} (hx : ∀ s, x s ∈ J) (d : σ →₀ ℕ)
    (hd : N ≤ d.degree) : (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J ^ d.degree ≤ J ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

private theorem le_degree_of_not_mem_bound [Finite σ] (N : ℕ)
    (d : σ →₀ ℕ) (hd : d ∉ boundFinset N) :
    N ≤ d.degree := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  rw [mem_boundFinset] at hd
  push Not at hd
  obtain ⟨s, hs⟩ := hd
  calc N ≤ d s := hs.le
    _ ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _

/-- The finite sum defining `nilpotentEval` may be taken over any finite
set of monomials containing all monomials of degree below `N`, where
`J ^ N = ⊥`. -/
theorem nilpotentEval_eq_sum [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C} (hx : ∀ s, x s ∈ J)
    (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    nilpotentEval J hJ x hx f = ∑ d ∈ D, algebraMap R C (coeff d f) *
      d.prod fun s e => x s ^ e := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  have hzero : ∀ {M : ℕ}, J ^ M = ⊥ → ∀ d : σ →₀ ℕ, M ≤ d.degree →
      algebraMap R C (coeff d f) * d.prod (fun s e => x s ^ e) = 0 := by
    intro M hM d hd
    rw [prod_pow_eq_zero_of_le_degree J hM hx d hd, mul_zero]
  have key1 : (∑ d ∈ boundFinset (Classical.choose hJ),
        algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) =
      ∑ d ∈ boundFinset (Classical.choose hJ) ∪ D,
        algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e :=
    Finset.sum_subset Finset.subset_union_left (fun d _ hd =>
      hzero (Classical.choose_spec hJ) d
        (le_degree_of_not_mem_bound (Classical.choose hJ) d hd))
  have key2 : (∑ d ∈ D, algebraMap R C (coeff d f) *
        d.prod fun s e => x s ^ e) =
      ∑ d ∈ boundFinset (Classical.choose hJ) ∪ D,
        algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e :=
    Finset.sum_subset Finset.subset_union_right (fun d _ hd =>
      hzero hN d (hD d hd))
  unfold nilpotentEval
  rw [key1, key2]

theorem nilpotentEval_eq_zero_of_forall_coeff [Finite σ] (J : Ideal C)
    (hJ : IsNilpotent J) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R}
    (hf : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = 0) :
    nilpotentEval J hJ x hx f = 0 := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  rw [nilpotentEval_eq_sum J hJ hN hx f _
    (le_degree_of_not_mem_bound N)]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d.degree < N
  · rw [hf d hd, map_zero, zero_mul]
  · rw [prod_pow_eq_zero_of_le_degree J hN hx d (not_lt.mp hd), mul_zero]

theorem nilpotentEval_mem [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R}
    (hf : f.constantCoeff = 0) : nilpotentEval J hJ x hx f ∈ J := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  show nilpotentEval J ⟨N, hN⟩ x hx f ∈ J
  rw [nilpotentEval_eq_sum J ⟨N, hN⟩ hN hx f _ (le_degree_of_not_mem_bound N)]
  refine sum_mem fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod]
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [← Finset.mul_prod_erase _ _ hs']
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (hx s)

theorem map_nilpotentEval [Finite σ] {C' : Type*} [CommRing C'] [Algebra R C']
    (J : Ideal C) (J' : Ideal C') (hJ : IsNilpotent J) (hJ' : IsNilpotent J')
    (φ : C →ₐ[R] C') {x : σ → C} (hx : ∀ s, x s ∈ J)
    (hx' : ∀ s, φ (x s) ∈ J') (f : MvPowerSeries σ R) :
    φ (nilpotentEval J hJ x hx f) =
      nilpotentEval J' hJ' (fun s => φ (x s)) hx' f := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  show φ (nilpotentEval J ⟨N, hN⟩ x hx f) =
    nilpotentEval J' ⟨N', hN'⟩ (fun s => φ (x s)) hx' f
  rw [nilpotentEval_eq_sum J ⟨N, hN⟩ hM hx f _ (le_degree_of_not_mem_bound (max N N')),
    nilpotentEval_eq_sum J' ⟨N', hN'⟩ hM' hx' f _ (le_degree_of_not_mem_bound (max N N'))]
  simp only [map_sum, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

@[simp]
theorem nilpotentEval_zero [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) :
    nilpotentEval J hJ x hx (0 : MvPowerSeries σ R) = 0 := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  exact nilpotentEval_eq_zero_of_forall_coeff J ⟨N, hN⟩ hN hx
    (fun d _ => by simp)

theorem nilpotentEval_sub [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f g : MvPowerSeries σ R) :
    nilpotentEval J hJ x hx (f - g) =
      nilpotentEval J hJ x hx f - nilpotentEval J hJ x hx g := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  show nilpotentEval J ⟨N, hN⟩ x hx (f - g) =
    nilpotentEval J ⟨N, hN⟩ x hx f - nilpotentEval J ⟨N, hN⟩ x hx g
  rw [nilpotentEval_eq_sum J ⟨N, hN⟩ hN hx (f - g) _
      (le_degree_of_not_mem_bound N),
    nilpotentEval_eq_sum J ⟨N, hN⟩ hN hx f _ (le_degree_of_not_mem_bound N),
    nilpotentEval_eq_sum J ⟨N, hN⟩ hN hx g _ (le_degree_of_not_mem_bound N),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_sub (coeff d), map_sub, sub_mul]

/-- Evaluation of a polynomial, viewed as a power series, at a point of a
nilpotent ideal agrees with polynomial evaluation when the coefficients
below the nilpotency exponent agree. -/
theorem nilpotentEval_eq_aeval_of_forall_coeff [Finite σ] (J : Ideal C)
    (hJ : IsNilpotent J) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (p : MvPolynomial σ R)
    (hfp : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = p.coeff d) :
    nilpotentEval J hJ x hx f = MvPolynomial.aeval x p := by
  have h : nilpotentEval J hJ x hx (f - (p : MvPowerSeries σ R)) = 0 := by
    apply nilpotentEval_eq_zero_of_forall_coeff J hJ hN hx
    intro d hd
    rw [map_sub, hfp d hd, MvPolynomial.coeff_coe, sub_self]
  rw [nilpotentEval_sub] at h
  have hcoe : nilpotentEval J hJ x hx (p : MvPowerSeries σ R) =
      MvPolynomial.aeval x p := by
    classical
    haveI : Fintype σ := Fintype.ofFinite σ
    haveI : DecidableEq (σ →₀ ℕ) := Classical.decEq _
    have key : nilpotentEval J hJ x hx (p : MvPowerSeries σ R) =
        ∑ d ∈ boundFinset N ∪ p.support, algebraMap R C (p.coeff d) *
          d.prod fun s e => x s ^ e := by
      rw [nilpotentEval_eq_sum J hJ hN hx _
        (boundFinset N ∪ p.support)
        (fun d hd => le_degree_of_not_mem_bound N d
          (fun h => hd (Finset.mem_union_left _ h)))]
      exact Finset.sum_congr rfl fun d _ => by rw [MvPolynomial.coeff_coe]
    rw [key, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    exact (Finset.sum_subset Finset.subset_union_right
      (fun d _ hd => by
        rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul])).symm
  rw [hcoe] at h
  exact sub_eq_zero.mp h

theorem nilpotentEval_coe [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (p : MvPolynomial σ R) :
    nilpotentEval J hJ x hx (p : MvPowerSeries σ R) =
      MvPolynomial.aeval x p := by
  obtain ⟨N, hN⟩ := hJ
  exact nilpotentEval_eq_aeval_of_forall_coeff J ⟨N, hN⟩ hN hx _ p
    (fun d _ => by rw [MvPolynomial.coeff_coe])

universe u

namespace NilpotentYoneda

section TestPairs

variable {R : Type u} [CommRing R] {σ : Type}

private noncomputable abbrev varIdeal (R : Type u) [CommRing R] (σ : Type) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range MvPolynomial.X)

private noncomputable abbrev TestRing (R : Type u) [CommRing R] (σ : Type) (N : ℕ) : Type u :=
  MvPolynomial σ R ⧸ varIdeal R σ ^ N

private noncomputable abbrev testIdeal (R : Type u) [CommRing R] (σ : Type) (N : ℕ) :
    Ideal (TestRing R σ N) :=
  (varIdeal R σ).map (Ideal.Quotient.mk (varIdeal R σ ^ N))

private noncomputable def xbar (R : Type u) [CommRing R] (σ : Type) (N : ℕ) :
    σ → TestRing R σ N :=
  fun s => Ideal.Quotient.mk (varIdeal R σ ^ N) (MvPolynomial.X s)

private theorem testIdeal_pow_eq_bot (N : ℕ) : testIdeal R σ N ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

private theorem isNilpotent_testIdeal (N : ℕ) : IsNilpotent (testIdeal R σ N) :=
  ⟨N, testIdeal_pow_eq_bot N⟩

private theorem X_mem_varIdeal (s : σ) :
    (MvPolynomial.X s : MvPolynomial σ R) ∈ varIdeal R σ :=
  Ideal.subset_span ⟨s, rfl⟩

private theorem xbar_mem (N : ℕ) (s : σ) : xbar R σ N s ∈ testIdeal R σ N :=
  Ideal.mem_map_of_mem _ (X_mem_varIdeal s)

private noncomputable def rep {N : ℕ} (q : TestRing R σ N) : MvPolynomial σ R :=
  (Ideal.Quotient.mk_surjective q).choose

private theorem mk_rep {N : ℕ} (q : TestRing R σ N) :
    Ideal.Quotient.mk (varIdeal R σ ^ N) (rep q) = q :=
  (Ideal.Quotient.mk_surjective q).choose_spec

private noncomputable def coeffQ {N : ℕ} (d : σ →₀ ℕ) (q : TestRing R σ N) : R :=
  (rep q).coeff d

private theorem aeval_xbar (N : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.aeval (xbar R σ N) p =
      Ideal.Quotient.mk (varIdeal R σ ^ N) p := by
  have h : MvPolynomial.aeval (xbar R σ N) =
      Ideal.Quotient.mkₐ R (varIdeal R σ ^ N) := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [xbar]
  rw [h]
  rfl

private noncomputable def transition {N M : ℕ} (h : N ≤ M) :
    TestRing R σ M →ₐ[R] TestRing R σ N :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

private theorem transition_mk {N M : ℕ} (h : N ≤ M) (p : MvPolynomial σ R) :
    transition h (Ideal.Quotient.mk (varIdeal R σ ^ M) p) =
      Ideal.Quotient.mk (varIdeal R σ ^ N) p :=
  rfl

private theorem transition_xbar {N M : ℕ} (h : N ≤ M) (s : σ) :
    transition h (xbar R σ M s) = xbar R σ N s :=
  rfl

private theorem transition_mem {N M : ℕ} (h : N ≤ M) {q : TestRing R σ M}
    (hq : q ∈ testIdeal R σ M) : transition h q ∈ testIdeal R σ N := by
  obtain ⟨p, hp, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
  rw [transition_mk]
  exact Ideal.mem_map_of_mem _ hp

private noncomputable def evalAt {C : Type u} [CommRing C] [Algebra R C]
    (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J) :
    TestRing R σ M →ₐ[R] C :=
  Ideal.Quotient.liftₐ (varIdeal R σ ^ M) (MvPolynomial.aeval x) (by
    have hle : (varIdeal R σ).map (MvPolynomial.aeval x) ≤ J := by
      rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      simpa using hx s
    intro a ha
    have hmem : MvPolynomial.aeval x a ∈
        ((varIdeal R σ) ^ M).map (MvPolynomial.aeval x) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at hmem
    have := (Ideal.pow_right_mono hle M) hmem
    rwa [hM, Submodule.mem_bot] at this)

private theorem evalAt_mk {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C)
    {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J)
    (p : MvPolynomial σ R) :
    evalAt J hM x hx (Ideal.Quotient.mk (varIdeal R σ ^ M) p) =
      MvPolynomial.aeval x p :=
  rfl

private theorem evalAt_xbar {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C)
    {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J) (s : σ) :
    evalAt J hM x hx (xbar R σ M s) = x s := by
  rw [xbar, evalAt_mk]; simp

private theorem evalAt_mem {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C)
    {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J)
    {q : TestRing R σ M} (hq : q ∈ testIdeal R σ M) :
    evalAt J hM x hx q ∈ J := by
  obtain ⟨p, hp, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
  rw [evalAt_mk]
  have hle : (varIdeal R σ).map (MvPolynomial.aeval x) ≤ J := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    simpa using hx s
  exact hle (Ideal.mem_map_of_mem _ hp)

end TestPairs

section Coefficients

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]

private def lowVanish (R : Type u) [CommRing R] (σ : Type) [DecidableEq σ]
    (N : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ d : σ →₀ ℕ, d.degree < N → p.coeff d = 0}
  zero_mem' := fun d _ => by simp
  add_mem' := fun {p q} hp hq d hd => by
    simp only [Set.mem_setOf_eq] at hp hq
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp d hd, hq d hd, add_zero]
  smul_mem' := fun q p hp d hd => by
    simp only [Set.mem_setOf_eq] at hp
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have hab' : ab.1 + ab.2 = d :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hdeg : ab.2.degree ≤ d.degree := by
      rw [← hab', map_add]; exact Nat.le_add_left _ _
    rw [hp ab.2 (lt_of_le_of_lt hdeg hd), mul_zero]

omit [Fintype σ] in
private theorem mem_lowVanish {N : ℕ} {p : MvPolynomial σ R} :
    p ∈ lowVanish R σ N ↔
      ∀ d : σ →₀ ℕ, d.degree < N → p.coeff d = 0 :=
  Iff.rfl

private theorem varIdeal_pow_le_lowVanish (N : ℕ) :
    varIdeal R σ ^ N ≤ lowVanish R σ N := by
  induction N with
  | zero =>
    intro p _ d hd
    exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hq
    rw [Finset.mul_sum]
    refine sum_mem fun s _ => ?_
    intro d hd
    rw [← mul_assoc, MvPolynomial.coeff_mul_X']
    split_ifs with hs
    · have hmem : p * c s ∈ varIdeal R σ ^ N := Ideal.mul_mem_right _ _ hp
      apply ih hmem
      have h1 : (d - Finsupp.single s 1).degree + 1 = d.degree := by
        have hds : 1 ≤ d s :=
          Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
        have hsub : d - Finsupp.single s 1 + Finsupp.single s 1 = d := by
          ext i
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
            Pi.sub_apply, Finsupp.single_apply]
          split_ifs with his
          · subst his; omega
          · omega
        conv_rhs => rw [← hsub]
        rw [map_add, Finsupp.degree_single]
      omega
    · rfl

private theorem coeff_eq_zero_of_mem_pow {N : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ varIdeal R σ ^ N) {d : σ →₀ ℕ} (hd : d.degree < N) :
    p.coeff d = 0 :=
  varIdeal_pow_le_lowVanish N hp d hd

private theorem coeffQ_mk {N : ℕ} {d : σ →₀ ℕ} (hd : d.degree < N)
    (p : MvPolynomial σ R) :
    coeffQ d (Ideal.Quotient.mk (varIdeal R σ ^ N) p) =
      p.coeff d := by
  unfold coeffQ
  have h : rep (Ideal.Quotient.mk (varIdeal R σ ^ N) p) - p ∈
      varIdeal R σ ^ N :=
    Ideal.Quotient.eq.mp (mk_rep _)
  have h2 : (rep (Ideal.Quotient.mk (varIdeal R σ ^ N) p)).coeff d -
      p.coeff d = 0 := by
    simpa using coeff_eq_zero_of_mem_pow h hd
  exact sub_eq_zero.mp h2

private noncomputable def truncPoly (M : ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial σ R :=
  ∑ e ∈ boundFinset M, MvPolynomial.monomial e (coeff e f)

private theorem coeff_truncPoly (M : ℕ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ)
    (hd : d.degree < M) : (truncPoly M f).coeff d = coeff d f := by
  unfold truncPoly
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (boundFinset M) d (fun e => coeff e f)]
  rw [if_pos]
  rw [mem_boundFinset]
  intro s
  calc d s ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _
    _ ≤ M := hd.le

private theorem nilpotentEval_xbar (N : ℕ) (f : MvPowerSeries σ R) :
    nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N) (xbar R σ N)
        (xbar_mem N) f =
      Ideal.Quotient.mk (varIdeal R σ ^ N) (truncPoly N f) := by
  rw [nilpotentEval_eq_aeval_of_forall_coeff (testIdeal R σ N)
    (isNilpotent_testIdeal N) (testIdeal_pow_eq_bot N) (xbar_mem N) f
    (truncPoly N f) (fun d hd => (coeff_truncPoly N f d hd).symm), aeval_xbar]

private theorem coeffQ_nilpotentEval_xbar {N : ℕ} (f : MvPowerSeries σ R)
    {d : σ →₀ ℕ} (hd : d.degree < N) :
    coeffQ d (nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N)
      (xbar R σ N) (xbar_mem N) f) = coeff d f := by
  rw [nilpotentEval_xbar, coeffQ_mk hd, coeff_truncPoly N f d hd]

private theorem eq_of_forall_nilpotentEval_xbar_eq {f f' : MvPowerSeries σ R}
    (h : ∀ N, nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N)
        (xbar R σ N) (xbar_mem N) f =
      nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N) (xbar R σ N)
        (xbar_mem N) f') : f = f' := by
  ext d
  have := congrArg (coeffQ d) (h (d.degree + 1))
  rwa [coeffQ_nilpotentEval_xbar f (Nat.lt_succ_self _),
    coeffQ_nilpotentEval_xbar f' (Nat.lt_succ_self _)] at this

private theorem coeffQ_transition {N M : ℕ} (h : N ≤ M) (q : TestRing R σ M)
    {d : σ →₀ ℕ} (hd : d.degree < N) :
    coeffQ d (transition h q) = coeffQ d q := by
  conv_rhs => rw [← mk_rep q]
  conv_lhs => rw [← mk_rep q, transition_mk]
  rw [coeffQ_mk hd, coeffQ_mk (lt_of_lt_of_le hd h)]

private theorem evalAt_eq_aeval_of_forall_coeffQ {C : Type u} [CommRing C]
    [Algebra R C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C)
    (hx : ∀ s, x s ∈ J) (q : TestRing R σ M) (p : MvPolynomial σ R)
    (hqp : ∀ d : σ →₀ ℕ, d.degree < M → coeffQ d q =
      p.coeff d) :
    evalAt J hM x hx q = MvPolynomial.aeval x p := by
  conv_lhs => rw [← mk_rep q, evalAt_mk]
  have hdiff : ∀ d : σ →₀ ℕ, d.degree < M →
      (rep q - p).coeff d = 0 := by
    intro d hd
    rw [show (rep q - p).coeff d = (rep q).coeff d - p.coeff d by simp, ← hqp d hd, sub_eq_zero]
    have := coeffQ_mk hd (rep q) (R := R)
    rw [mk_rep] at this
    exact this.symm
  have hval : MvPolynomial.aeval x (rep q - p) = 0 := by
    have h := nilpotentEval_eq_aeval_of_forall_coeff J ⟨M, hM⟩ hM hx
      (0 : MvPowerSeries σ R) (rep q - p) (fun d hd => by
        rw [map_zero, hdiff d hd])
    rw [show nilpotentEval J ⟨M, hM⟩ x hx (0 : MvPowerSeries σ R) = 0 from
      nilpotentEval_zero J ⟨M, hM⟩ hx] at h
    exact h.symm
  rwa [map_sub, sub_eq_zero] at hval

end Coefficients

section Series

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]

private noncomputable def series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C) :
    MvPowerSeries σ R :=
  fun d => coeffQ d (t (TestRing R σ (d.degree + 1))
    (testIdeal R σ (d.degree + 1)) (xbar R σ (d.degree + 1)))

private theorem coeff_series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    {M : ℕ} (d : σ →₀ ℕ) (hd : d.degree < M) :
    coeff d (series t) =
      coeffQ d (t (TestRing R σ M) (testIdeal R σ M) (xbar R σ M)) := by
  show coeffQ d (t (TestRing R σ (d.degree + 1)) (testIdeal R σ (d.degree + 1))
    (xbar R σ (d.degree + 1))) = _
  have hle : d.degree + 1 ≤ M := hd
  have hnat := ht_nat (TestRing R σ M) (TestRing R σ (d.degree + 1))
    (testIdeal R σ M) (testIdeal R σ (d.degree + 1)) (isNilpotent_testIdeal M)
    (isNilpotent_testIdeal _) (transition hle)
    (fun s hs => transition_mem hle hs) (xbar R σ M) (xbar_mem M)
  have hx : (⇑(transition (R := R) (σ := σ) hle) ∘ xbar R σ M) =
      xbar R σ (d.degree + 1) := by
    funext s; exact transition_xbar hle s
  rw [hx] at hnat
  rw [hnat, coeffQ_transition hle _ (Nat.lt_succ_self _)]

private theorem apply_eq_nilpotentEval_series
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : σ → C) (hx : ∀ s, x s ∈ J) :
    t C J x = nilpotentEval J hJ x hx (series t) := by
  obtain ⟨M, hM⟩ := hJ
  replace hM : J ^ M = ⊥ := hM
  have hnat := ht_nat (TestRing R σ M) C (testIdeal R σ M) J
    (isNilpotent_testIdeal M) ⟨M, hM⟩ (evalAt J hM x hx)
    (fun s hs => evalAt_mem J hM x hx hs) (xbar R σ M) (xbar_mem M)
  have hx' : (⇑(evalAt (R := R) (σ := σ) J hM x hx) ∘ xbar R σ M) = x := by
    funext s; exact evalAt_xbar J hM x hx s
  rw [hx'] at hnat
  rw [hnat, evalAt_eq_aeval_of_forall_coeffQ J hM x hx _ (truncPoly M (series t)),
    nilpotentEval_eq_aeval_of_forall_coeff J ⟨M, hM⟩ hM hx (series t)
      (truncPoly M (series t))]
  · intro d hd
    exact (coeff_truncPoly M (series t) d hd).symm
  · intro d hd
    rw [coeff_truncPoly M (series t) d hd, coeff_series t ht_nat d hd]

private theorem eq_series_of_forall_xbar
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    (f : MvPowerSeries σ R)
    (hf : ∀ N, t (TestRing R σ N) (testIdeal R σ N) (xbar R σ N) =
      nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N) (xbar R σ N)
        (xbar_mem N) f) : f = series t := by
  refine eq_of_forall_nilpotentEval_xbar_eq fun N => ?_
  rw [← hf N]
  exact apply_eq_nilpotentEval_series t ht_nat _ _ (isNilpotent_testIdeal N) _
    (xbar_mem N)

end Series

end NilpotentYoneda

/-- A rule assigning to every `R`-algebra `C`, nilpotent ideal `J` in `C`
and point `x` in `J` an element of `C`, naturally in ideal-preserving
algebra maps, is evaluation of a unique power series. -/
theorem existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C)
        (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J),
          t C J x = nilpotentEval J hJ x hx f := by
  classical
  haveI := Fintype.ofFinite σ
  refine ⟨NilpotentYoneda.series t,
    fun C _ _ J hJ x hx =>
      NilpotentYoneda.apply_eq_nilpotentEval_series t ht_nat C J hJ x hx, ?_⟩
  intro f' hf'
  exact NilpotentYoneda.eq_series_of_forall_xbar t ht_nat f' fun N =>
    hf' (NilpotentYoneda.TestRing R σ N) (NilpotentYoneda.testIdeal R σ N)
      (NilpotentYoneda.isNilpotent_testIdeal N) (NilpotentYoneda.xbar R σ N)
      (NilpotentYoneda.xbar_mem N)

end MvPowerSeries
