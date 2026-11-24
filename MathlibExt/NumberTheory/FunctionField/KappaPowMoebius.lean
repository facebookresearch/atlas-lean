/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Möbius sums over variable powers of monic polynomials

We define the variable power and minimum exponent, and prove a bound for the Möbius sum over
monic polynomials whose variable power has bounded degree.
-/

open Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt

@[expose] public section

/-- **The minimal exponent $\kappa_{\min}$.** Let $F$ be a field and let $\kappa$ be a function
from $F[T]$ to the natural numbers. Then $\kappa_{\min}$ is the minimum of $\kappa(P)$ over all
monic irreducible polynomials $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public noncomputable def kappaMin {F : Type*} [Field F] (κ : F[X] → ℕ) : ℕ :=
  ⨅ P : {P : F[X] // P.Monic ∧ Irreducible P}, κ P

/-- **$\kappa_{\min}$ is a lower bound for $\kappa$.** Let $F$ be a field, let $\kappa$ assign a
natural number to each polynomial in $F[T]$, and let $\kappa_{\min}$ be the minimum of $\kappa(P)$
over the monic irreducible $P \in F[T]$. Then $\kappa_{\min} \le \kappa(P)$ for every monic
irreducible $P \in F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public theorem kappaMin_le {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]} (hm : P.Monic)
    (hP : Irreducible P) : kappaMin κ ≤ κ P :=
  ciInf_le (OrderBot.bddBelow _) (⟨P, hm, hP⟩ : {P : F[X] // P.Monic ∧ Irreducible P})

/-- **The $\kappa$-power of a polynomial.** Let $F$ be a field and let $\kappa$ be a function
from $F[T]$ to the natural numbers. For nonzero $f \in F[T]$ and a monic irreducible $P$, write
$\nu_P(f)$ for the multiplicity of $P$ in $f$. The $\kappa$-power of $f$ is
$f^\kappa = \prod_P P^{\nu_P(f)\, \kappa(P)}$, the product over the monic irreducible $P$ dividing
$f$; it does not depend on the leading coefficient of $f$. For $f = 0$ the product is empty and
$0^\kappa = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public noncomputable def kappaPow {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : F[X] :=
  open scoped Classical in
  ((normalizedFactors f).map fun P => P ^ κ P).prod

/-- **The $\kappa$-power of $1$.** Let $F$ be a field and let $\kappa$ be a function from $F[T]$
to the natural numbers. Then the $\kappa$-power of the constant polynomial $1$ is $1^\kappa = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_one {F : Type*} [Field F] (κ : F[X] → ℕ) :
    kappaPow κ (1 : F[X]) = 1 := by
  classical
  simp [kappaPow]

/-- **The $\kappa$-power of a monic irreducible polynomial.** Let $F$ be a field and let $\kappa$
be a function from $F[T]$ to the natural numbers. For every monic irreducible $P \in F[T]$, the
$\kappa$-power of $P$ is $P^\kappa = P^{\kappa(P)}$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_of_irreducible {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]}
    (hm : P.Monic) (hP : Irreducible P) : kappaPow κ P = P ^ κ P := by
  classical
  simp [kappaPow, normalizedFactors_irreducible hP, hm.normalize_eq_self]

namespace abs_sum_moebius_kappaPow_le

variable {F : Type*} [Field F]

private theorem finite_natDegree_le [Finite F] (d : ℕ) :
    {r : F[X] | r.natDegree ≤ d}.Finite := by
  let : Finite (degreeLT F (d + 1)) :=
    Finite.of_injective _ (degreeLTEquiv F (d + 1)).injective
  refine ((degreeLT F (d + 1) : Set F[X]).toFinite).subset ?_
  intro r hr
  exact mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hr))

private theorem finite_monic_dvd [Finite F] {f : F[X]} (hf : f ≠ 0) :
    {r : F[X] | r.Monic ∧ r ∣ f}.Finite :=
  (finite_natDegree_le f.natDegree).subset fun _ hr ↦ natDegree_le_of_dvd hr.2 hf

private theorem kappaPow_monic (κ : F[X] → ℕ) (r : F[X]) :
    (kappaPow κ r).Monic := by
  classical
  apply monic_multiset_prod_of_monic
  intro p hp
  obtain rfl | hr := eq_or_ne r 0
  · simp at hp
  exact ((Polynomial.mem_normalizedFactors_iff hr).mp hp).2.1.pow _

private theorem kappaPow_mul (κ : F[X] → ℕ) {p r : F[X]} (hp : p ≠ 0) (hr : r ≠ 0) :
    kappaPow κ (p * r) = kappaPow κ p * kappaPow κ r := by
  classical
  simp [kappaPow, normalizedFactors_mul hp hr]

private theorem mul_natDegree_le (κ : F[X] → ℕ) (r : F[X]) :
    kappaMin κ * r.natDegree ≤ (kappaPow κ r).natDegree := by
  classical
  obtain rfl | hr := eq_or_ne r 0
  · simp
  rw [kappaPow, natDegree_multiset_prod _ ?_, Multiset.map_map,
    ← sum_natDegree_normalizedFactors r, ← Multiset.sum_map_mul_left]
  · apply Multiset.sum_map_le_sum_map
    intro p hp
    obtain ⟨hirr, hm, _⟩ := (Polynomial.mem_normalizedFactors_iff hr).mp hp
    simpa [Function.comp_def, natDegree_pow, mul_comm] using
      Nat.mul_le_mul_right p.natDegree (kappaMin_le κ hm hirr)
  · intro hz
    obtain ⟨p, hp, hp0⟩ := Multiset.mem_map.mp hz
    exact pow_ne_zero _ (ne_zero_of_mem_normalizedFactors hp) hp0

-- Terms divisible by p² vanish. Pair each remaining multiple of p with its quotient by p.
open Classical in
private theorem sum_moebius_cancel (s : Finset F[X]) {p : F[X]} (hp : Irreducible p)
    (hclosed : ∀ r, p * r ∈ s → r ∈ s) :
    ∑ r ∈ s, (moebius r : ℝ) =
      ∑ r ∈ s.filter (fun r ↦ ¬ p ∣ r), (if p * r ∈ s then 0 else (moebius r : ℝ)) := by
  classical
  let multiples := s.filter (p ∣ ·)
  let others := s.filter (fun r ↦ ¬ p ∣ r)
  have hfilter :
      ∑ r ∈ multiples.filter (fun r ↦ ¬ p * p ∣ r), (moebius r : ℝ) =
        ∑ r ∈ multiples, (moebius r : ℝ) := by
    apply Finset.sum_filter_of_ne
    intro r _ hμ hdiv
    exact hμ (by simp [moebius_of_not_squarefree (fun h => hp.not_isUnit (h p hdiv))])
  have hpair :
      ∑ r ∈ multiples.filter (fun r ↦ ¬ p * p ∣ r), (moebius r : ℝ) =
        ∑ r ∈ others.filter (fun r ↦ p * r ∈ s), -(moebius r : ℝ) := by
    symm
    apply Finset.sum_bij (fun r _ ↦ p * r)
    · intro r hr
      have ⟨hr', hpr⟩ := Finset.mem_filter.mp hr
      have hnd := (Finset.mem_filter.mp hr').2
      simp [multiples, hpr, hnd, mul_dvd_mul_iff_left hp.ne_zero, dvd_mul_right]
    · intro r _ t _ h
      exact mul_left_cancel₀ hp.ne_zero h
    · intro t ht
      have ⟨ht', hsquare⟩ := Finset.mem_filter.mp ht
      have ⟨hts, hpt⟩ := Finset.mem_filter.mp ht'
      obtain ⟨r, rfl⟩ := hpt
      have hnd : ¬ p ∣ r := (mul_dvd_mul_iff_left hp.ne_zero).not.mp hsquare
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hclosed r hts, hnd⟩, hts⟩,
        rfl⟩
    · intro r hr
      have hnd := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      rw [(hp.isRelPrime_iff_not_dvd.mpr hnd).moebius_mul, hp.moebius_eq]
      simp
  rw [← Finset.sum_filter_add_sum_filter_not s (p ∣ ·) (fun r ↦ (moebius r : ℝ))]
  change (∑ r ∈ multiples, (moebius r : ℝ)) + ∑ r ∈ others, (moebius r : ℝ) = _
  rw [← hfilter, hpair, Finset.sum_neg_distrib, Finset.sum_filter]
  rw [add_comm, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by split <;> simp_all

-- The divisor sum of μ is supported at 1.
open Classical in
private theorem sum_moebius_monic_dvd [Finite F] {f : F[X]} (hf : f.Monic) :
    ∑ᶠ r ∈ {r : F[X] | r.Monic ∧ r ∣ f}, (moebius r : ℝ) = if f = 1 then 1 else 0 := by
  classical
  by_cases h : f = 1
  · subst f
    have hset : {r : F[X] | r.Monic ∧ r ∣ 1} = {1} := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun hr ↦ hr.1.isUnit_iff.mp (isUnit_of_dvd_one hr.2),
        fun h ↦ h.symm ▸ ⟨monic_one, dvd_rfl⟩⟩
    simp [hset]
  · obtain ⟨p, hm, hp, hpdvd⟩ := exists_monic_irreducible_factor f (hf.isUnit_iff.not.mpr h)
    rw [ite_eq_right h, finsum_mem_eq_finite_toFinset_sum _ (finite_monic_dvd hf.ne_zero)]
    let s := (finite_monic_dvd hf.ne_zero).toFinset
    have hmem (r : F[X]) : r ∈ s ↔ r.Monic ∧ r ∣ f := Set.Finite.mem_toFinset _
    change ∑ r ∈ s, (moebius r : ℝ) = 0
    rw [sum_moebius_cancel s hp]
    · apply Finset.sum_eq_zero
      intro r hr
      have ⟨hrm, hrd⟩ := (hmem r).mp (Finset.mem_filter.mp hr).1
      have hnd := (Finset.mem_filter.mp hr).2
      have hd := (hp.isRelPrime_iff_not_dvd.mpr hnd).mul_dvd hpdvd hrd
      simp [hmem, hm.mul hrm, hd]
    · intro r hr
      have ⟨hrm, hrd⟩ := (hmem _).mp hr
      exact (hmem _).mpr ⟨hm.of_mul_monic_left hrm, (dvd_mul_left r p).trans hrd⟩

private theorem sum_moebius_monic_dvd_dvd [Finite F] {g : F[X]} (hg : g.Monic) :
    ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ g},
      ∑ᶠ r ∈ {r : F[X] | r.Monic ∧ r ∣ f}, (moebius r : ℝ) = 1 := by
  classical
  trans ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ g}, (if f = 1 then 1 else (0 : ℝ))
  · exact finsum_mem_congr rfl fun f hf ↦ sum_moebius_monic_dvd hf.1
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_monic_dvd hg.ne_zero)]
  simp [Finset.sum_ite_eq', monic_one]

-- Padding by powers of X embeds the eligible polynomials into monic polynomials of degree d.
private theorem card_le_pow [Fintype F] (d : ℕ) (s : Finset F[X])
    (hs : ∀ r ∈ s, r.Monic ∧ r.natDegree ≤ d ∧ ¬ (X : F[X]) ∣ r) :
    s.card ≤ Fintype.card F ^ d := by
  let pad (r : s) : {r : F[X] // r.Monic ∧ r.natDegree = d} :=
    ⟨(r : F[X]) * X ^ (d - (r : F[X]).natDegree), (hs r r.2).1.mul (monic_X.pow _), by
      rw [natDegree_mul_X_pow _ (hs r r.2).1.ne_zero, Nat.add_sub_of_le (hs r r.2).2.1]⟩
  have trailing (r : s) : (pad r : F[X]).natTrailingDegree = d - (r : F[X]).natDegree := by
    have hzero : (r : F[X]).natTrailingDegree = 0 :=
      natTrailingDegree_eq_zero.mpr (.inr (X_dvd_iff.not.mp (hs r r.2).2.2))
    change ((r : F[X]) * X ^ _).natTrailingDegree = _
    rw [natTrailingDegree_mul_X_pow (hs r r.2).1.ne_zero, hzero, zero_add]
  have hpad : Function.Injective pad := by
    intro r t h
    have heq := congrArg Subtype.val h
    have he := (trailing r).symm.trans ((congrArg natTrailingDegree heq).trans (trailing t))
    change (r : F[X]) * X ^ (d - (r : F[X]).natDegree) =
      (t : F[X]) * X ^ (d - (t : F[X]).natDegree) at heq
    rw [he] at heq
    exact Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ X_ne_zero) heq)
  let coeffs : {r : F[X] // r.Monic ∧ r.natDegree = d} ≃ (Fin d → F) :=
    (monicEquivDegreeLT d).trans (degreeLTEquiv F d).toEquiv
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin]
    using Nat.card_le_card_of_injective _ (coeffs.injective.comp hpad)

end abs_sum_moebius_kappaPow_le

open abs_sum_moebius_kappaPow_le in
set_option linter.unusedVariables false in
/-- **Bound on the Möbius sum over κ-th powers.** Let $F$ be a finite field with $q$ elements and
let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for
every monic irreducible $P$. Let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic
irreducible $P$, and for monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$. Then for every natural number $N \ge 1$,
$$
\Bigl|\sum_{r} \mu(r) \sum_{f \mid r^\kappa} \sum_{\ell \mid f} \mu(\ell)\Bigr| \le
q^{N/\kappa_{\min}},
$$
where $r$ runs over the monic polynomials with $\deg r^\kappa \le N$, $f$ and $\ell$ run over monic
divisors, $\mu$ is the Möbius function, and the exponent $N/\kappa_{\min}$ is a real number.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (6)
(`integers-2026-A80-lem-8`). -/
public theorem abs_sum_moebius_kappaPow_le {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {N : ℕ} (hN : 1 ≤ N) :
    |∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N},
        (moebius r : ℝ) * ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
          ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f}, (moebius ℓ : ℝ)| ≤
      (Fintype.card F : ℝ) ^ ((N : ℝ) / kappaMin κ) := by
  classical
  let : Nonempty {P : F[X] // P.Monic ∧ Irreducible P} := ⟨⟨X, monic_X, irreducible_X⟩⟩
  have hk : 2 ≤ kappaMin κ := le_ciInf fun P ↦ hκ P P.2.1 P.2.2
  have hkpos : 0 < kappaMin κ := by omega
  let d := N / kappaMin κ
  let S := {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N}
  have hdegree {r : F[X]} (hr : r ∈ S) : r.natDegree ≤ d :=
    (Nat.le_div_iff_mul_le hkpos).mpr (by
      rw [mul_comm]
      exact (mul_natDegree_le κ r).trans hr.2)
  have hS : S.Finite := (finite_natDegree_le d).subset fun _ hr ↦ hdegree hr
  let s := hS.toFinset
  have hmem (r : F[X]) : r ∈ s ↔ r ∈ S := Set.Finite.mem_toFinset _
  have hreduce :
      ∀ r ∈ S, (moebius r : ℝ) * (∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
        ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f}, (moebius ℓ : ℝ)) = (moebius r : ℝ) := by
    intro r _
    rw [sum_moebius_monic_dvd_dvd (kappaPow_monic κ r), mul_one]
  rw [finsum_mem_congr (t := S) rfl hreduce, finsum_mem_eq_finite_toFinset_sum _ hS]
  change |∑ r ∈ s, (moebius r : ℝ)| ≤ _
  have hclosed (r : F[X]) (hr : X * r ∈ s) : r ∈ s := by
    have ⟨hm, hd⟩ := (hmem _).mp hr
    have hrm := monic_X.of_mul_monic_left hm
    apply (hmem r).mpr
    refine ⟨hrm, le_trans ?_ hd⟩
    rw [kappaPow_mul κ X_ne_zero hrm.ne_zero]
    exact natDegree_le_of_dvd (dvd_mul_left _ _) ((kappaPow_monic κ X).mul
      (kappaPow_monic κ r)).ne_zero
  rw [sum_moebius_cancel s irreducible_X hclosed]
  have hcard := card_le_pow d (s.filter (fun r ↦ ¬ (X : F[X]) ∣ r)) fun r hr ↦ by
    obtain ⟨hr, hnd⟩ := Finset.mem_filter.mp hr
    exact ⟨((hmem r).mp hr).1, hdegree ((hmem r).mp hr), hnd⟩
  calc
    _ ≤ ∑ r ∈ s.filter (fun r ↦ ¬ (X : F[X]) ∣ r), (1 : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
      split
      · simp
      · by_cases h : Squarefree r
        · simp [h.moebius_eq, abs_pow]
        · simp [moebius_of_not_squarefree h]
    _ ≤ (Fintype.card F : ℝ) ^ d := by simpa using (show
      (((s.filter (fun r ↦ ¬ (X : F[X]) ∣ r)).card : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) ^ d
        by exact_mod_cast hcard)
    _ ≤ (Fintype.card F : ℝ) ^ ((N : ℝ) / kappaMin κ) := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast
        (Fintype.one_lt_card (α := F)).le) ((le_div_iff₀ (by exact_mod_cast hkpos)).mpr ?_)
      exact_mod_cast Nat.div_mul_le_self N (kappaMin κ)

end

end MetaMathlibExt
