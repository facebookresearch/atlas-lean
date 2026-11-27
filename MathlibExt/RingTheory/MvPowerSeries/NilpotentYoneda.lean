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
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import MathlibExt.RingTheory.AdicCompletion.Nilpotent
public import MathlibExt.RingTheory.MvPowerSeries.SpecialFibreCoordinates
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Evaluation of multivariate power series at points of a nilpotent ideal

Let `σ` be a finite type of variables, `C` a commutative `R`-algebra, `J` a nilpotent ideal of
`C` and `x : σ → C` a point with every coordinate in `J`. Every monomial of large total degree
vanishes at `x`, so `MvPowerSeries.nilpotentEval J hJ x hx f` evaluates a power series `f` over
`R` at `x` as a finite sum. It equals the adic evaluation `MvPowerSeries.adicEval J x f` and is
the underlying function of the `R`-algebra homomorphism `MvPowerSeries.nilpotentEvalAlgHom`.

The main theorem, `MvPowerSeries.existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent`,
says that a rule assigning an element of `C` to every such `C`, `J` and `x`, naturally in
ideal-preserving algebra maps, is evaluation of a unique power series. The proof evaluates the
rule at the points `X s` of the truncated polynomial rings
`MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N`, whose coefficients below total degree `N`
determine the series.
-/

@[expose] public section

open MvPowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {σ : Type*}

/-- **Evaluation of a power series at a point of a nilpotent ideal.** Let `σ` be a finite type of
variables, `J` a nilpotent ideal of the `R`-algebra `C`, and `x : σ → C` a point with every
coordinate `x s` in `J`. Choose `N` with `J ^ N = ⊥`; every monomial of total degree at least `N`
then vanishes at `x`. The value `nilpotentEval J hJ x hx f` is the finite sum of
`algebraMap R C (coeff d f) * ∏ s, x s ^ d s` over the monomials `d` of total degree below `N`.
It does not depend on the choice of `N` (`MvPowerSeries.nilpotentEval_eq_sum`), it equals the
adic evaluation `MvPowerSeries.adicEval J x f` (`MvPowerSeries.nilpotentEval_eq_adicEval`), and
it is the underlying function of the algebra homomorphism `MvPowerSeries.nilpotentEvalAlgHom`. -/
noncomputable def nilpotentEval {C : Type*} [CommRing C] [Algebra R C] [Finite σ]
    (J : Ideal C) (hJ : IsNilpotent J) (x : σ → C) (_hx : ∀ s, x s ∈ J)
    (f : MvPowerSeries σ R) : C :=
  ∑ d ∈ (Finsupp.finite_of_degree_lt (Classical.choose hJ)).toFinset,
    algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e

variable {C : Type*} [CommRing C] [Algebra R C]

private theorem prod_pow_eq_zero_of_le_degree (J : Ideal C) {N : ℕ}
    (hN : J ^ N = ⊥) {x : σ → C} (hx : ∀ s, x s ∈ J) (d : σ →₀ ℕ)
    (hd : N ≤ d.degree) : (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J ^ d.degree ≤ J ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

private theorem le_degree_of_notMem [Finite σ] {N : ℕ} {d : σ →₀ ℕ}
    (hd : d ∉ (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset) : N ≤ d.degree :=
  not_lt.mp fun h => hd ((Finsupp.finite_of_degree_lt N).mem_toFinset.mpr h)

/-- **Nilpotent evaluation as a sum over any large enough set of monomials.** Let `σ` be a finite
type of variables. If `J ^ N = ⊥` and every coordinate of `x` lies in `J`, then
`nilpotentEval J hJ x hx f` is the sum of `algebraMap R C (coeff d f) * ∏ s, x s ^ d s` over any
finite set `D` of monomials that contains every monomial of total degree below `N`. -/
theorem nilpotentEval_eq_sum [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C} (hx : ∀ s, x s ∈ J)
    (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    nilpotentEval J hJ x hx f = ∑ d ∈ D, algebraMap R C (coeff d f) *
      d.prod fun s e => x s ^ e := by
  classical
  have hzero : ∀ {M : ℕ}, J ^ M = ⊥ → ∀ d : σ →₀ ℕ, M ≤ d.degree →
      algebraMap R C (coeff d f) * d.prod (fun s e => x s ^ e) = 0 := by
    intro M hM d hd
    rw [prod_pow_eq_zero_of_le_degree J hM hx d hd, mul_zero]
  have key1 : nilpotentEval J hJ x hx f =
      ∑ d ∈ (Finsupp.finite_of_degree_lt (Classical.choose hJ)).toFinset ∪ D,
        algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e :=
    Finset.sum_subset Finset.subset_union_left fun d _ hd =>
      hzero (Classical.choose_spec hJ) d (le_degree_of_notMem hd)
  have key2 : (∑ d ∈ D, algebraMap R C (coeff d f) *
        d.prod fun s e => x s ^ e) =
      ∑ d ∈ (Finsupp.finite_of_degree_lt (Classical.choose hJ)).toFinset ∪ D,
        algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e :=
    Finset.sum_subset Finset.subset_union_right fun d _ hd => hzero hN d (hD d hd)
  rw [key1, key2]

theorem nilpotentEval_eq_zero_of_forall_coeff [Finite σ] (J : Ideal C)
    (hJ : IsNilpotent J) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R}
    (hf : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = 0) :
    nilpotentEval J hJ x hx f = 0 := by
  rw [nilpotentEval_eq_sum J hJ hN hx f _ fun d hd => le_degree_of_notMem hd]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d.degree < N
  · rw [hf d hd, map_zero, zero_mul]
  · rw [prod_pow_eq_zero_of_le_degree J hN hx d (not_lt.mp hd), mul_zero]

theorem nilpotentEval_mem [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R}
    (hf : f.constantCoeff = 0) : nilpotentEval J hJ x hx f ∈ J := by
  classical
  obtain ⟨N, hN⟩ := id hJ
  replace hN : J ^ N = ⊥ := hN
  rw [nilpotentEval_eq_sum J hJ hN hx f _ fun d hd => le_degree_of_notMem hd]
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
  obtain ⟨N, hN⟩ := id hJ
  obtain ⟨N', hN'⟩ := id hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  rw [nilpotentEval_eq_sum J hJ hM hx f _ fun d hd => le_degree_of_notMem hd,
    nilpotentEval_eq_sum J' hJ' hM' hx' f _ fun d hd => le_degree_of_notMem hd]
  simp only [map_sum, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

/-- **Nilpotent evaluation is adic evaluation.** For a finite type of variables, a nilpotent
ideal `J` of the `R`-algebra `C` and a point `x` with every coordinate in `J`,
`nilpotentEval J hJ x hx f` equals the `J`-adic evaluation `MvPowerSeries.adicEval J x f`: the
ring `C` is `J`-adically complete (`IsAdicComplete.of_isNilpotent`), the point lies in `J`, hence
in the radical of `J`, and the adic sum has only the finitely many nonzero terms that
`nilpotentEval` adds up. -/
theorem nilpotentEval_eq_adicEval [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) :
    nilpotentEval J hJ x hx f = adicEval J x f := by
  obtain ⟨N, hN⟩ := id hJ
  replace hN : J ^ N = ⊥ := hN
  let : UniformSpace R := ⊥
  let : WithIdeal C := ⟨J⟩
  have hc : IsAdicComplete J C := IsAdicComplete.of_isNilpotent hJ
  have : CompleteSpace C :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  have : T2Space C :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hsum := hasSum_eval₂ (φ := algebraMap R C) continuous_of_discreteTopology
    (hasEval_of_mem_radical J fun s => Ideal.le_radical (hx s)) f
  rw [nilpotentEval_eq_sum J hJ hN hx f _ fun d hd => le_degree_of_notMem hd]
  refine (hsum.unique (hasSum_sum_of_ne_finset_zero fun d hd => ?_)).symm
  rw [prod_pow_eq_zero_of_le_degree J hN hx d (le_degree_of_notMem hd), mul_zero]

/-- **Nilpotent evaluation as an algebra homomorphism.** For a finite type of variables `σ`, a
nilpotent ideal `J` of the `R`-algebra `C` and a point `x` with every coordinate in `J`,
evaluation at `x` is an `R`-algebra homomorphism `MvPowerSeries σ R →ₐ[R] C`. It is the
specialization of `MvPowerSeries.adicEvalAlgHom` to the nilpotent ideal `J`, at which `C` is
adically complete (`IsAdicComplete.of_isNilpotent`), and its underlying function is
`nilpotentEval J hJ x hx` (`MvPowerSeries.coe_nilpotentEvalAlgHom`). -/
noncomputable def nilpotentEvalAlgHom [Finite σ] (J : Ideal C)
    (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J) :
    MvPowerSeries σ R →ₐ[R] C :=
  haveI := IsAdicComplete.of_isNilpotent hJ
  adicEvalAlgHom J fun s => Ideal.le_radical (hx s)

theorem coe_nilpotentEvalAlgHom [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    (x : σ → C) (hx : ∀ s, x s ∈ J) :
    ⇑(nilpotentEvalAlgHom (R := R) J hJ x hx) = nilpotentEval J hJ x hx := by
  have := IsAdicComplete.of_isNilpotent hJ
  funext f
  rw [nilpotentEval_eq_adicEval]
  exact congrFun (coe_adicEvalAlgHom J fun s => Ideal.le_radical (hx s)) f

@[simp]
theorem nilpotentEval_zero [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) :
    nilpotentEval J hJ x hx (0 : MvPowerSeries σ R) = 0 := by
  rw [← coe_nilpotentEvalAlgHom J hJ x hx, map_zero]

@[simp]
theorem nilpotentEval_one [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) :
    nilpotentEval J hJ x hx (1 : MvPowerSeries σ R) = 1 := by
  rw [← coe_nilpotentEvalAlgHom J hJ x hx, map_one]

theorem nilpotentEval_add [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f g : MvPowerSeries σ R) :
    nilpotentEval J hJ x hx (f + g) =
      nilpotentEval J hJ x hx f + nilpotentEval J hJ x hx g := by
  rw [← coe_nilpotentEvalAlgHom J hJ x hx, map_add]

theorem nilpotentEval_sub [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f g : MvPowerSeries σ R) :
    nilpotentEval J hJ x hx (f - g) =
      nilpotentEval J hJ x hx f - nilpotentEval J hJ x hx g := by
  rw [← coe_nilpotentEvalAlgHom J hJ x hx, map_sub]

theorem nilpotentEval_mul [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f g : MvPowerSeries σ R) :
    nilpotentEval J hJ x hx (f * g) =
      nilpotentEval J hJ x hx f * nilpotentEval J hJ x hx g := by
  rw [← coe_nilpotentEvalAlgHom J hJ x hx, map_mul]

theorem nilpotentEval_coe [Finite σ] (J : Ideal C) (hJ : IsNilpotent J)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (p : MvPolynomial σ R) :
    nilpotentEval J hJ x hx (p : MvPowerSeries σ R) =
      MvPolynomial.aeval x p :=
  (nilpotentEval_eq_adicEval J hJ hx _).trans (adicEval_coe J x p)

/-- **Nilpotent evaluation only sees the coefficients below the nilpotency exponent.** Let `σ` be
a finite type of variables, `J` an ideal of the `R`-algebra `C` with `J ^ N = ⊥`, and `x` a point
with every coordinate in `J`. If the power series `f` and the polynomial `p` have the same
coefficient at every monomial of total degree below `N`, then evaluating `f` at `x` gives the
polynomial evaluation `MvPolynomial.aeval x p`. -/
theorem nilpotentEval_eq_aeval_of_forall_coeff [Finite σ] (J : Ideal C)
    (hJ : IsNilpotent J) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (p : MvPolynomial σ R)
    (hfp : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = p.coeff d) :
    nilpotentEval J hJ x hx f = MvPolynomial.aeval x p := by
  have h : nilpotentEval J hJ x hx (f - (p : MvPowerSeries σ R)) = 0 := by
    apply nilpotentEval_eq_zero_of_forall_coeff J hJ hN hx
    intro d hd
    rw [map_sub, hfp d hd, MvPolynomial.coeff_coe, sub_self]
  rwa [nilpotentEval_sub, nilpotentEval_coe, sub_eq_zero] at h

universe u

namespace NilpotentYoneda

open MvPolynomial (idealOfVars)

section TestPairs

variable {R : Type u} [CommRing R] {σ : Type}

private noncomputable abbrev TestRing (R : Type u) [CommRing R] (σ : Type) (N : ℕ) : Type u :=
  MvPolynomial σ R ⧸ idealOfVars σ R ^ N

private noncomputable abbrev testIdeal (R : Type u) [CommRing R] (σ : Type) (N : ℕ) :
    Ideal (TestRing R σ N) :=
  (idealOfVars σ R).map (Ideal.Quotient.mk (idealOfVars σ R ^ N))

private noncomputable def xbar (R : Type u) [CommRing R] (σ : Type) (N : ℕ) :
    σ → TestRing R σ N :=
  fun s => Ideal.Quotient.mk (idealOfVars σ R ^ N) (MvPolynomial.X s)

private theorem testIdeal_pow_eq_bot (N : ℕ) : testIdeal R σ N ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

private theorem isNilpotent_testIdeal (N : ℕ) : IsNilpotent (testIdeal R σ N) :=
  ⟨N, testIdeal_pow_eq_bot N⟩

private theorem X_mem_idealOfVars (s : σ) :
    (MvPolynomial.X s : MvPolynomial σ R) ∈ idealOfVars σ R :=
  Ideal.subset_span ⟨s, rfl⟩

private theorem xbar_mem (N : ℕ) (s : σ) : xbar R σ N s ∈ testIdeal R σ N :=
  Ideal.mem_map_of_mem _ (X_mem_idealOfVars s)

private noncomputable def rep {N : ℕ} (q : TestRing R σ N) : MvPolynomial σ R :=
  (Ideal.Quotient.mk_surjective q).choose

private theorem mk_rep {N : ℕ} (q : TestRing R σ N) :
    Ideal.Quotient.mk (idealOfVars σ R ^ N) (rep q) = q :=
  (Ideal.Quotient.mk_surjective q).choose_spec

private noncomputable def coeffQ {N : ℕ} (d : σ →₀ ℕ) (q : TestRing R σ N) : R :=
  (rep q).coeff d

private theorem aeval_xbar (N : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.aeval (xbar R σ N) p =
      Ideal.Quotient.mk (idealOfVars σ R ^ N) p := by
  have h : MvPolynomial.aeval (xbar R σ N) =
      Ideal.Quotient.mkₐ R (idealOfVars σ R ^ N) := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [xbar]
  rw [h]
  rfl

private noncomputable def transition {N M : ℕ} (h : N ≤ M) :
    TestRing R σ M →ₐ[R] TestRing R σ N :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

private theorem transition_mk {N M : ℕ} (h : N ≤ M) (p : MvPolynomial σ R) :
    transition h (Ideal.Quotient.mk (idealOfVars σ R ^ M) p) =
      Ideal.Quotient.mk (idealOfVars σ R ^ N) p :=
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
  Ideal.Quotient.liftₐ (idealOfVars σ R ^ M) (MvPolynomial.aeval x) (by
    have hle : (idealOfVars σ R).map (MvPolynomial.aeval x) ≤ J := by
      rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      simpa using hx s
    intro a ha
    have hmem : MvPolynomial.aeval x a ∈
        ((idealOfVars σ R) ^ M).map (MvPolynomial.aeval x) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at hmem
    have := (Ideal.pow_right_mono hle M) hmem
    rwa [hM, Submodule.mem_bot] at this)

private theorem evalAt_mk {C : Type u} [CommRing C] [Algebra R C] (J : Ideal C)
    {M : ℕ} (hM : J ^ M = ⊥) (x : σ → C) (hx : ∀ s, x s ∈ J)
    (p : MvPolynomial σ R) :
    evalAt J hM x hx (Ideal.Quotient.mk (idealOfVars σ R ^ M) p) =
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
  have hle : (idealOfVars σ R).map (MvPolynomial.aeval x) ≤ J := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    simpa using hx s
  exact hle (Ideal.mem_map_of_mem _ hp)

end TestPairs

section Coefficients

variable {R : Type u} [CommRing R] {σ : Type}

private theorem coeffQ_mk {N : ℕ} {d : σ →₀ ℕ} (hd : d.degree < N)
    (p : MvPolynomial σ R) :
    coeffQ d (Ideal.Quotient.mk (idealOfVars σ R ^ N) p) =
      p.coeff d := by
  unfold coeffQ
  have h : rep (Ideal.Quotient.mk (idealOfVars σ R ^ N) p) - p ∈
      idealOfVars σ R ^ N :=
    Ideal.Quotient.eq.mp (mk_rep _)
  have h2 : (rep (Ideal.Quotient.mk (idealOfVars σ R ^ N) p)).coeff d -
      p.coeff d = 0 := by
    simpa using (MvPolynomial.mem_pow_idealOfVars_iff' N _).mp h d hd
  exact sub_eq_zero.mp h2

private theorem nilpotentEval_xbar [Finite σ] (N : ℕ) (f : MvPowerSeries σ R) :
    nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N) (xbar R σ N)
        (xbar_mem N) f =
      Ideal.Quotient.mk (idealOfVars σ R ^ N) (truncTotal N f) := by
  rw [nilpotentEval_eq_aeval_of_forall_coeff (testIdeal R σ N)
    (isNilpotent_testIdeal N) (testIdeal_pow_eq_bot N) (xbar_mem N) f
    (truncTotal N f) (fun d hd => (coeff_truncTotal f hd).symm), aeval_xbar]

private theorem coeffQ_nilpotentEval_xbar [Finite σ] {N : ℕ} (f : MvPowerSeries σ R)
    {d : σ →₀ ℕ} (hd : d.degree < N) :
    coeffQ d (nilpotentEval (testIdeal R σ N) (isNilpotent_testIdeal N)
      (xbar R σ N) (xbar_mem N) f) = coeff d f := by
  rw [nilpotentEval_xbar, coeffQ_mk hd, coeff_truncTotal f hd]

private theorem eq_of_forall_nilpotentEval_xbar_eq [Finite σ] {f f' : MvPowerSeries σ R}
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

private theorem evalAt_eq_aeval_of_forall_coeffQ [Finite σ] {C : Type u} [CommRing C]
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
    exact h.symm.trans (nilpotentEval_zero J ⟨M, hM⟩ hx)
  rwa [map_sub, sub_eq_zero] at hval

end Coefficients

section Series

variable {R : Type u} [CommRing R] {σ : Type}

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
  change coeffQ d (t (TestRing R σ (d.degree + 1)) (testIdeal R σ (d.degree + 1))
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

private theorem apply_eq_nilpotentEval_series [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x))
    (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : σ → C) (hx : ∀ s, x s ∈ J) :
    t C J x = nilpotentEval J hJ x hx (series t) := by
  obtain ⟨M, hM⟩ := id hJ
  replace hM : J ^ M = ⊥ := hM
  have hnat := ht_nat (TestRing R σ M) C (testIdeal R σ M) J
    (isNilpotent_testIdeal M) hJ (evalAt J hM x hx)
    (fun s hs => evalAt_mem J hM x hx hs) (xbar R σ M) (xbar_mem M)
  have hx' : (⇑(evalAt (R := R) (σ := σ) J hM x hx) ∘ xbar R σ M) = x := by
    funext s; exact evalAt_xbar J hM x hx s
  rw [hx'] at hnat
  rw [hnat, evalAt_eq_aeval_of_forall_coeffQ J hM x hx _ (truncTotal M (series t)),
    nilpotentEval_eq_aeval_of_forall_coeff J hJ hM hx (series t)
      (truncTotal M (series t))]
  · intro d hd
    exact (coeff_truncTotal (series t) hd).symm
  · intro d hd
    rw [coeff_truncTotal (series t) hd, coeff_series t ht_nat d hd]

private theorem eq_series_of_forall_xbar [Finite σ]
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

/-- **Natural rules on nilpotent points are evaluations of a unique power series.** Let `σ` be a
finite type of variables and `R` a commutative ring. Suppose `t` assigns an element `t C J x` of
`C` to every commutative `R`-algebra `C` in the universe of `R`, every ideal `J` of `C` and every
point `x : σ → C`, naturally in ideal-preserving algebra maps: whenever `J` and `J'` are
nilpotent, `φ : C →ₐ[R] C'` maps `J` into `J'`, and every coordinate of `x` lies in `J`, then
`t C' J' (φ ∘ x) = φ (t C J x)`. Then there is exactly one power series `f` in
`MvPowerSeries σ R` with `t C J x = nilpotentEval J hJ x hx f` for every such `C`, every
nilpotent ideal `J` of `C` and every point `x` with every coordinate in `J`. The equality is
asserted only at nilpotent ideals and at points with every coordinate in the ideal. -/
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
  refine ⟨NilpotentYoneda.series t,
    fun C _ _ J hJ x hx =>
      NilpotentYoneda.apply_eq_nilpotentEval_series t ht_nat C J hJ x hx, ?_⟩
  intro f' hf'
  exact NilpotentYoneda.eq_series_of_forall_xbar t ht_nat f' fun N =>
    hf' (NilpotentYoneda.TestRing R σ N) (NilpotentYoneda.testIdeal R σ N)
      (NilpotentYoneda.isNilpotent_testIdeal N) (NilpotentYoneda.xbar R σ N)
      (NilpotentYoneda.xbar_mem N)

end MvPowerSeries
