/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import MathlibExt.NumberTheory.FunctionField.KappaPowMoebius
public import MathlibExt.NumberTheory.FunctionField.MonicConvolution

/-! # Möbius convolution of the B-free indicator -/

open Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt

/-- **$B_\kappa$-free polynomials.** Let $F$ be a field and let $\kappa$ assign a natural number to
each polynomial in $F[T]$. A polynomial $f \in F[T]$ is $B_\kappa$-free when $P^{\kappa(P)}$ does
not divide $f$ for any monic irreducible $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`B_κ`-free polynomials. -/
@[expose] public def IsBFree {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : Prop :=
  ∀ P : F[X], P.Monic → Irreducible P → ¬ P ^ κ P ∣ f

namespace monicDirichletConv_bFreeIndicator_moebius

variable {F : Type*} [Field F]

private theorem finite_divisors {f : F[X]} (hf : f ≠ 0) :
    {r : F[X] | r.Monic ∧ r ∣ f}.Finite := by
  let := fintypeSubtypeMonicDvd f hf
  exact Set.toFinite _

private noncomputable def divisors {f : F[X]} (hf : f.Monic) : Finset F[X] :=
  (finite_divisors hf.ne_zero).toFinset

private theorem mem_divisors {f r : F[X]} {hf : f.Monic} :
    r ∈ divisors hf ↔ r.Monic ∧ r ∣ f := Set.Finite.mem_toFinset _

private theorem mul_quotient {a f : F[X]} (ha : a.Monic) (haf : a ∣ f) :
    a * (f /ₘ a) = f := by
  obtain ⟨b, rfl⟩ := haf
  rw [mul_divByMonic_cancel_left _ ha]

private theorem monic_quotient {a f : F[X]} (ha : a.Monic) (hf : f.Monic) (haf : a ∣ f) :
    (f /ₘ a).Monic := ha.of_mul_monic_left (by rwa [mul_quotient ha haf])

private theorem dvd_quotient_iff {a f : F[X]} (ha : a.Monic) (haf : a ∣ f) (b : F[X]) :
    b ∣ f /ₘ a ↔ a * b ∣ f := by
  conv_rhs => rw [← mul_quotient ha haf]
  rw [mul_dvd_mul_iff_left ha.ne_zero]

private theorem quotient_quotient {a f : F[X]} (ha : a.Monic) (hf : f.Monic) (haf : a ∣ f) :
    f /ₘ (f /ₘ a) = a := calc
  _ = ((f /ₘ a) * a) /ₘ (f /ₘ a) :=
    congrArg (· /ₘ (f /ₘ a)) (by rw [mul_comm, mul_quotient ha haf])
  _ = a := mul_divByMonic_cancel_left _ (monic_quotient ha hf haf)

private theorem kappaPow_monic (κ : F[X] → ℕ) (r : F[X]) : (kappaPow κ r).Monic := by
  classical
  apply monic_multiset_prod_of_monic
  intro p hp
  obtain rfl | hr := eq_or_ne r 0
  · simp at hp
  exact ((Polynomial.mem_normalizedFactors_iff hr).mp hp).2.1.pow _

private theorem kappaPow_mul (κ : F[X] → ℕ) {r s : F[X]} (hr : r ≠ 0) (hs : s ≠ 0) :
    kappaPow κ (r * s) = kappaPow κ r * kappaPow κ s := by
  classical
  simp [kappaPow, normalizedFactors_mul hr hs]

private theorem dvd_kappaPow (κ : F[X] → ℕ)
    (hκ : ∀ p : F[X], p.Monic → Irreducible p → κ p ≠ 0) {r : F[X]} (hr : r.Monic) :
    r ∣ kappaPow κ r := by
  classical
  have h := Multiset.prod_dvd_prod_of_dvd (S := normalizedFactors r) id (fun p => p ^ κ p)
    (fun p hp => by
      obtain ⟨hirr, hm, _⟩ := (Polynomial.mem_normalizedFactors_iff hr.ne_zero).mp hp
      exact dvd_pow_self _ (hκ p hm hirr))
  simpa [kappaPow, prod_normalizedFactors_eq hr.ne_zero, hr.normalize_eq_self] using h

private theorem dvd_of_dvd_kappaPow (κ : F[X] → ℕ) {p r : F[X]} (hp : Irreducible p)
    (h : p ∣ kappaPow κ r) : p ∣ r := by
  classical
  rw [kappaPow] at h
  have mem_of_dvd_prod (s : Multiset F[X]) : p ∣ s.prod → ∃ q ∈ s, p ∣ q := by
    refine Quotient.inductionOn s ?_
    intro l hl
    simpa using hp.prime.dvd_prod_iff.mp (show p ∣ l.prod from hl)
  obtain ⟨_, hmem, hdvd⟩ := mem_of_dvd_prod _ h
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hmem
  exact (hp.prime.dvd_of_dvd_pow hdvd).trans (dvd_of_mem_normalizedFactors hq)

open Classical in
-- Pair each element not divisible by p with its multiple by p; square multiples contribute zero.
private theorem sum_moebius_eq_zero_of_pairing (s : Finset F[X]) {p : F[X]} (hp : Irreducible p)
    (hremove : ∀ r, p * r ∈ s → r ∈ s)
    (hinsert : ∀ r ∈ s, ¬ p ∣ r → p * r ∈ s) :
    ∑ r ∈ s, (moebius r : ℂ) = 0 := by
  let multiples := s.filter (p ∣ ·)
  let others := s.filter (fun r => ¬ p ∣ r)
  have hfilter : ∑ r ∈ multiples.filter (fun r => ¬ p * p ∣ r), (moebius r : ℂ) =
      ∑ r ∈ multiples, (moebius r : ℂ) := by
    apply Finset.sum_filter_of_ne
    intro r _ hμ hdiv
    exact hμ (by simp [moebius_of_not_squarefree (fun h => hp.not_isUnit (h p hdiv))])
  have hpair : ∑ r ∈ others, -(moebius r : ℂ) =
      ∑ r ∈ multiples.filter (fun r => ¬ p * p ∣ r), (moebius r : ℂ) := by
    apply Finset.sum_bij (fun r _ => p * r)
    · intro r hr
      obtain ⟨hrs, hnd⟩ := Finset.mem_filter.mp hr
      simp [multiples, hinsert r hrs hnd, hnd, mul_dvd_mul_iff_left hp.ne_zero, dvd_mul_right]
    · exact fun _ _ _ _ h => mul_left_cancel₀ hp.ne_zero h
    · intro t ht
      obtain ⟨ht', hsquare⟩ := Finset.mem_filter.mp ht
      obtain ⟨hts, r, rfl⟩ := Finset.mem_filter.mp ht'
      exact ⟨r, Finset.mem_filter.mpr ⟨hremove r hts,
        (mul_dvd_mul_iff_left hp.ne_zero).not.mp hsquare⟩, rfl⟩
    · intro r hr
      rw [(hp.isRelPrime_iff_not_dvd.mpr (Finset.mem_filter.mp hr).2).moebius_mul, hp.moebius_eq]
      simp
  rw [← Finset.sum_filter_add_sum_filter_not s (p ∣ ·) (fun r => (moebius r : ℂ))]
  change (∑ r ∈ multiples, (moebius r : ℂ)) + ∑ r ∈ others, (moebius r : ℂ) = 0
  rw [← hfilter, ← hpair, Finset.sum_neg_distrib, neg_add_cancel]

open Classical in
private theorem sum_moebius_divisors {f : F[X]} (hf : f.Monic) :
    ∑ r ∈ divisors hf, (moebius r : ℂ) = if f = 1 then 1 else 0 := by
  by_cases h : f = 1
  · subst f
    have hset : divisors hf = {1} := by
      ext r
      simp only [mem_divisors, Finset.mem_singleton]
      exact ⟨fun hr => hr.1.isUnit_iff.mp (isUnit_of_dvd_one hr.2),
        by rintro rfl; exact ⟨monic_one, dvd_rfl⟩⟩
    simp [hset]
  · obtain ⟨p, hpm, hp, hpf⟩ := exists_monic_irreducible_factor f (hf.isUnit_iff.not.mpr h)
    rw [ite_eq_right h]
    apply sum_moebius_eq_zero_of_pairing _ hp
    · intro r hr
      obtain ⟨hrm, hrd⟩ := mem_divisors.mp hr
      exact mem_divisors.mpr ⟨hpm.of_mul_monic_left hrm, (dvd_mul_left r p).trans hrd⟩
    · intro r hr hnd
      obtain ⟨hrm, hrd⟩ := mem_divisors.mp hr
      exact mem_divisors.mpr ⟨hpm.mul hrm, (hp.isRelPrime_iff_not_dvd.mpr hnd).mul_dvd hpf hrd⟩

open Classical in
private noncomputable def kappaDivisors (κ : F[X] → ℕ) {f : F[X]} (hf : f.Monic) : Finset F[X] :=
  (divisors hf).filter (fun r => kappaPow κ r ∣ f)

private theorem mem_kappaDivisors {κ : F[X] → ℕ}
    (hκ : ∀ p : F[X], p.Monic → Irreducible p → κ p ≠ 0) {f r : F[X]} {hf : f.Monic} :
    r ∈ kappaDivisors κ hf ↔ r.Monic ∧ kappaPow κ r ∣ f := by
  classical
  simp only [kappaDivisors, Finset.mem_filter, mem_divisors]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (dvd_kappaPow κ hκ h.1).trans h.2⟩, h.2⟩⟩

-- Expand the indicator by inclusion-exclusion over the forbidden prime powers.
private theorem indicator_eq_sum (κ : F[X] → ℕ)
    (hκ : ∀ p : F[X], p.Monic → Irreducible p → κ p ≠ 0) {f : F[X]} (hf : f.Monic) :
    ({g : F[X] | IsBFree κ g}.indicator (1 : F[X] → ℂ)) f =
      ∑ r ∈ kappaDivisors κ hf, (moebius r : ℂ) := by
  classical
  by_cases h : IsBFree κ f
  · have he : kappaDivisors κ hf = {1} := by
      ext r
      simp only [mem_kappaDivisors hκ, Finset.mem_singleton]
      refine ⟨fun ⟨hrm, hrd⟩ => ?_, by rintro rfl; simp [kappaPow_one, monic_one]⟩
      by_contra hn
      obtain ⟨p, hpm, hp, hpr⟩ := exists_monic_irreducible_factor r (hrm.isUnit_iff.not.mpr hn)
      obtain ⟨t, rfl⟩ := hpr
      have htm := hpm.of_mul_monic_left hrm
      rw [kappaPow_mul κ hpm.ne_zero htm.ne_zero, kappaPow_of_irreducible κ hpm hp] at hrd
      exact h p hpm hp ((dvd_mul_right _ _).trans hrd)
    simp [he, Set.indicator_of_mem (show f ∈ {g : F[X] | IsBFree κ g} from h)]
  · have hex : ∃ p : F[X], p.Monic ∧ Irreducible p ∧ p ^ κ p ∣ f := by
      simpa only [IsBFree, not_forall, Classical.not_imp, not_not, exists_prop] using h
    obtain ⟨p, hpm, hp, hpf⟩ := hex
    rw [Set.indicator_of_notMem (show f ∉ {g : F[X] | IsBFree κ g} from h)]
    symm
    apply sum_moebius_eq_zero_of_pairing _ hp
    · intro r hr
      obtain ⟨hrm, hrd⟩ := (mem_kappaDivisors hκ).mp hr
      have hm := hpm.of_mul_monic_left hrm
      rw [kappaPow_mul κ hpm.ne_zero hm.ne_zero] at hrd
      exact (mem_kappaDivisors hκ).mpr ⟨hm, (dvd_mul_left _ _).trans hrd⟩
    · intro r hr hnd
      obtain ⟨hrm, hrd⟩ := (mem_kappaDivisors hκ).mp hr
      refine (mem_kappaDivisors hκ).mpr ⟨hpm.mul hrm, ?_⟩
      rw [kappaPow_mul κ hpm.ne_zero hrm.ne_zero, kappaPow_of_irreducible κ hpm hp]
      have hn : ¬ p ∣ kappaPow κ r := fun hd => hnd (dvd_of_dvd_kappaPow κ hp hd)
      have hcop : IsRelPrime (p ^ κ p) (kappaPow κ r) := (hp.isRelPrime_iff_not_dvd.mpr hn).pow_left
      exact hcop.mul_dvd hpf hrd

open Classical in
-- Taking complementary divisors carries multiples of a to divisors of f /ₘ a.
private theorem sum_moebius_quotients {a f : F[X]} (ha : a.Monic) (hf : f.Monic) (haf : a ∣ f) :
    ∑ d ∈ (divisors hf).filter (a ∣ ·), (moebius (f /ₘ d) : ℂ) =
      ∑ e ∈ divisors (monic_quotient ha hf haf), (moebius e : ℂ) := by
  have hflip {d : F[X]} (hd : d.Monic) (hdf : d ∣ f) : f /ₘ (f /ₘ d) = d :=
    quotient_quotient hd hf hdf
  have hiff {d : F[X]} (hd : d.Monic) (hdf : d ∣ f) :
      a ∣ d ↔ f /ₘ d ∣ f /ₘ a := by
    rw [dvd_quotient_iff ha haf, mul_comm, ← dvd_quotient_iff (monic_quotient hd hf hdf),
      hflip hd hdf]
    exact ⟨d, by rw [mul_comm, mul_quotient hd hdf]⟩
  refine Finset.sum_nbij' (f /ₘ ·) (f /ₘ ·) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro d hd
    obtain ⟨hd', had⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdm, hdf⟩ := mem_divisors.mp hd'
    exact mem_divisors.mpr ⟨monic_quotient hdm hf hdf, (hiff hdm hdf).mp had⟩
  · intro e he
    obtain ⟨hem, hea⟩ := mem_divisors.mp he
    have hef := hea.trans ⟨a, by rw [mul_comm, mul_quotient ha haf]⟩
    have hm := monic_quotient hem hf hef
    have hd : f /ₘ e ∣ f := ⟨e, by rw [mul_comm, mul_quotient hem hef]⟩
    exact Finset.mem_filter.mpr ⟨mem_divisors.mpr ⟨hm, hd⟩,
      (hiff hm hd).mpr (by rwa [hflip hem hef])⟩
  · intro d hd
    obtain ⟨hdm, hdf⟩ := mem_divisors.mp (Finset.mem_filter.mp hd).1
    exact hflip hdm hdf
  · intro e he
    obtain ⟨hem, hea⟩ := mem_divisors.mp he
    exact hflip hem (hea.trans ⟨a, by rw [mul_comm, mul_quotient ha haf]⟩)

end monicDirichletConv_bFreeIndicator_moebius

open monicDirichletConv_bFreeIndicator_moebius in
/-- **Convolution of the $B_\kappa$-free indicator with the Möbius function.** Let $F$ be a field
and let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ne 0$ for
every monic irreducible $P \in F[T]$. Let $\mathbf{1}_{B_\kappa} \colon F[T] \to \mathbb{C}$ be
the indicator function of the $B_\kappa$-free polynomials, let $\mu$ be the Möbius function of
$F[T]$, and write $r^\kappa$ for the $\kappa$-power of a polynomial $r$. Then for every monic
$f \in F[T]$, the Dirichlet convolution of $\mathbf{1}_{B_\kappa}$ and $\mu$ over monic divisors
satisfies
$$(\mathbf{1}_{B_\kappa} * \mu)(f) = \sum_{r} \mu(r),$$
the sum running over the monic $r \in F[T]$ with $r^\kappa = f$.

There is at most one such $r$, so the right side is $\mu(r)$ if $f = r^\kappa$ for a monic $r$,
and $0$ if there is no such $r$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 5
(`integers-2026-A80-lem-5`). -/
public theorem monicDirichletConv_bFreeIndicator_moebius {F : Type*} [Field F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) {f : F[X]}
    (hf : f.Monic) :
    monicDirichletConv ({g : F[X] | IsBFree κ g}.indicator 1) (fun g => (moebius g : ℂ)) f =
      ∑ᶠ r ∈ {r : F[X] | r.Monic ∧ kappaPow κ r = f}, (moebius r : ℂ) := by
  classical
  calc
    _ = ∑ d ∈ divisors hf, ∑ r ∈ (kappaDivisors κ hf).filter (fun r => kappaPow κ r ∣ d),
          (moebius r : ℂ) * (moebius (f /ₘ d) : ℂ) := by
      rw [monicDirichletConv, finsum_mem_eq_finite_toFinset_sum _ (finite_divisors hf.ne_zero)]
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdm, hdf⟩ := (mem_divisors (hf := hf)).mp hd
      have he : kappaDivisors κ hdm = (kappaDivisors κ hf).filter (fun r => kappaPow κ r ∣ d) := by
        ext r
        simp only [Finset.mem_filter, mem_kappaDivisors hκ]
        exact ⟨fun ⟨hrm, hrd⟩ => ⟨⟨hrm, hrd.trans hdf⟩, hrd⟩,
          fun ⟨⟨hrm, _⟩, hrd⟩ => ⟨hrm, hrd⟩⟩
      rw [indicator_eq_sum κ hκ hdm, Finset.sum_mul, he]
    _ = ∑ r ∈ kappaDivisors κ hf, (moebius r : ℂ) *
          ∑ d ∈ (divisors hf).filter (kappaPow κ r ∣ ·), (moebius (f /ₘ d) : ℂ) := by
      rw [Finset.sum_comm' (t' := kappaDivisors κ hf)
        (s' := fun r => (divisors hf).filter (kappaPow κ r ∣ ·))]
      · simp only [Finset.mul_sum]
      · intro d r
        simp only [Finset.mem_filter, mem_divisors, mem_kappaDivisors hκ]
        exact ⟨fun ⟨hd, ⟨hrm, _⟩, hrd⟩ => ⟨⟨hd, hrd⟩, hrm, hrd.trans hd.2⟩,
          fun ⟨⟨hd, hrd⟩, hr⟩ => ⟨hd, hr, hrd⟩⟩
    _ = ∑ r ∈ (kappaDivisors κ hf).filter (fun r => kappaPow κ r = f), (moebius r : ℂ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      let a := kappaPow κ r
      have ha : a.Monic := kappaPow_monic κ r
      have haf : a ∣ f := ((mem_kappaDivisors hκ).mp hr).2
      have he : f /ₘ a = 1 ↔ a = f := by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · simpa [h] using mul_quotient ha haf
        · rw [← h]
          simpa using mul_divByMonic_cancel_left (1 : F[X]) ha
      rw [sum_moebius_quotients ha hf haf, sum_moebius_divisors]
      change (moebius r : ℂ) * (if f /ₘ a = 1 then 1 else 0) =
        if a = f then (moebius r : ℂ) else 0
      simp only [he, mul_ite, mul_one, mul_zero]
    _ = _ := by
      have hfinite : {r : F[X] | r.Monic ∧ kappaPow κ r = f}.Finite :=
        (finite_divisors hf.ne_zero).subset fun r hr =>
          ⟨hr.1, hr.2 ▸ dvd_kappaPow κ hκ hr.1⟩
      rw [finsum_mem_eq_finite_toFinset_sum _ hfinite]
      congr 1
      ext r
      simp only [Finset.mem_filter, mem_kappaDivisors hκ, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq]
      exact ⟨fun ⟨⟨hm, _⟩, he⟩ => ⟨hm, he⟩, fun ⟨hm, he⟩ => ⟨⟨hm, he ▸ dvd_rfl⟩, he⟩⟩

end MetaMathlibExt
