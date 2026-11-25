/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Norm factorization and norm-fiber counts in `ℤ√d`

For `d < 0` with `ℤ√d` a unique factorization domain (for example `ℤ[i]` and `ℤ[√-2]`):
primes have prime-power norm, an element whose norm is a product of coprime factors
splits accordingly (`Zsqrtd.exists_factor_of_coprime`), and the number of elements of a
given norm is multiplicative up to the number of units (`Zsqrtd.card_mul_of_coprime`).
These are the ring-independent steps of the two-square and `x^2 + 2y^2` representation
counts in `MathlibExt.NumberTheory.JacobiTwoSquareCount` and
`MathlibExt.NumberTheory.X2Y2Count`.
-/

namespace Zsqrtd

@[expose] public section

variable {d : ℤ}

/-- **Elements of $\mathbb{Z}[\sqrt{d}]$ of prime norm are prime.** Let $d$ be an integer such that
the ring $\mathbb{Z}[\sqrt{d}]$ of formal expressions $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$
and $\sqrt{d}^2 = d$ is a unique factorization domain, with norm
$N(a + b\sqrt{d}) = a^2 - db^2$. If $\pi \in \mathbb{Z}[\sqrt{d}]$ and $|N(\pi)|$ is a prime
number, then $\pi$ is prime in $\mathbb{Z}[\sqrt{d}]$. -/
public theorem prime_of_natAbs_norm_prime [UniqueFactorizationMonoid (ℤ√d)]
    {π : ℤ√d} (h : (Zsqrtd.norm π).natAbs.Prime) : Prime π := by
  have hne : π ≠ 0 := by
    rintro rfl
    exact h.ne_zero (by rw [Zsqrtd.norm_zero, Int.natAbs_zero])
  have hnu : ¬ IsUnit π := by
    rw [← Zsqrtd.norm_eq_one_iff]
    exact h.ne_one
  apply Irreducible.prime
  refine ⟨hnu, fun a b hab => ?_⟩
  have hmn : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
      = (Zsqrtd.norm π).natAbs := by
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
  rcases h.eq_one_or_self_of_dvd _ ⟨_, hmn.symm⟩ with ha | ha
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
  · refine Or.inr (Zsqrtd.norm_eq_one_iff.mp ?_)
    have hcancel : (Zsqrtd.norm π).natAbs * (Zsqrtd.norm b).natAbs
        = (Zsqrtd.norm π).natAbs * 1 := by
      rw [ha] at hmn
      rw [mul_one]
      exact hmn
    exact mul_left_cancel₀ h.ne_zero hcancel

/-- **The norm respects divisibility in $\mathbb{Z}[\sqrt{d}]$.** Let $d$ be an integer and let
$N(a + b\sqrt{d}) = a^2 - db^2$ be the norm on the ring $\mathbb{Z}[\sqrt{d}]$ of formal
expressions $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ and $\sqrt{d}^2 = d$. If $x$ divides $y$ in
$\mathbb{Z}[\sqrt{d}]$, then $|N(x)|$ divides $|N(y)|$. -/
public theorem natAbs_norm_dvd_of_dvd {a b : ℤ√d} (h : a ∣ b) :
    (Zsqrtd.norm a).natAbs ∣ (Zsqrtd.norm b).natAbs := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact dvd_mul_right _ _

/-- **Only zero has norm zero in $\mathbb{Z}[\sqrt d]$ for $d < 0$.** Let $d < 0$ be an integer and
let $N(a + b\sqrt d) = a^2 - db^2$ be the norm on the ring $\mathbb{Z}[\sqrt d]$ of elements
$a + b\sqrt d$ ($a, b \in \mathbb{Z}$). If $\alpha \in \mathbb{Z}[\sqrt d]$ satisfies
$|N(\alpha)| = 0$, then $\alpha = 0$. -/
public theorem eq_zero_of_norm_natAbs_eq_zero (hd : d < 0) {x : ℤ√d}
    (h : (Zsqrtd.norm x).natAbs = 0) : x = 0 :=
  (Zsqrtd.norm_eq_zero_iff hd x).mp (Int.natAbs_eq_zero.mp h)

/-- **Cancelling a factor of coprime norm.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Let $u$ and $v$ be coprime natural
numbers with $u \ne 0$. If $\beta, \beta_0, \gamma \in \mathbb{Z}[\sqrt d]$ satisfy
$|N(\beta)| \mid u$, $|N(\gamma)| = v$ and $\beta \mid \beta_0\gamma$, then $\beta \mid \beta_0$. -/
public theorem dvd_of_coprime_norms [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    (hd : d < 0) {u v : ℕ} (huv : Nat.Coprime u v)
    (hu : u ≠ 0) :
    ∀ (m : ℕ) (β' : ℤ√d),
      (Zsqrtd.norm β').natAbs = m → m ∣ u →
      ∀ (β₀' γ₀ : ℤ√d), (Zsqrtd.norm γ₀).natAbs = v →
        β' ∣ β₀' * γ₀ → β' ∣ β₀' := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ihm β' hm hmu β₀' γ₀ hγ₀ hdvd
  by_cases hu' : IsUnit β'
  · exact hu'.dvd
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmu
      exact hu hmu
    have hβ0 : β' ≠ 0 := by
      rintro rfl
      rw [Zsqrtd.norm_zero,
        Int.natAbs_zero] at hm
      exact hm0 hm.symm
    obtain ⟨ϖ, hϖirr, hϖβ⟩ :=
      WfDvdMonoid.exists_irreducible_factor hu' hβ0
    have hϖprime : Prime ϖ :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖirr
    have hϖ0 : ϖ ≠ 0 := hϖprime.ne_zero
    have hϖdvd : ϖ ∣ β₀' * γ₀ := dvd_trans hϖβ hdvd
    rcases hϖprime.dvd_mul.mp hϖdvd with h | h
    · obtain ⟨c, rfl⟩ := hϖβ
      obtain ⟨δ, rfl⟩ := h
      have hcd : c ∣ δ * γ₀ := by
        have h2 := hdvd
        rw [show (ϖ * δ) * γ₀ = ϖ * (δ * γ₀) from by ring] at h2
        exact (mul_dvd_mul_iff_left hϖ0).mp h2
      have hnorm :
          (Zsqrtd.norm ϖ).natAbs * (Zsqrtd.norm c).natAbs = m := by
        have h3 := hm
        rw [Zsqrtd.norm_mul, Int.natAbs_mul] at h3
        exact h3
      have hϖn0 : (Zsqrtd.norm ϖ).natAbs ≠ 0 :=
        fun hz => hϖ0 (eq_zero_of_norm_natAbs_eq_zero hd hz)
      have hϖn1 : (Zsqrtd.norm ϖ).natAbs ≠ 1 :=
        fun h1 => hϖprime.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h1)
      have h2 : 2 ≤ (Zsqrtd.norm ϖ).natAbs := by omega
      have hclt : (Zsqrtd.norm c).natAbs < m := by
        have hle : (Zsqrtd.norm c).natAbs * 2 ≤ m := by
          calc (Zsqrtd.norm c).natAbs * 2
              ≤ (Zsqrtd.norm c).natAbs * (Zsqrtd.norm ϖ).natAbs := by
                gcongr
            _ = m := by rw [mul_comm]; exact hnorm
        omega
      have hcm : (Zsqrtd.norm c).natAbs ∣ u := by
        apply dvd_trans _ hmu
        exact ⟨_, by rw [mul_comm]; exact hnorm.symm⟩
      have hcdvd := ihm _ hclt c rfl hcm δ γ₀ hγ₀ hcd
      exact mul_dvd_mul_left _ hcdvd
    · exfalso
      have h1 : (Zsqrtd.norm ϖ).natAbs ∣ u := by
        have h10 := natAbs_norm_dvd_of_dvd hϖβ
        rw [hm] at h10
        exact dvd_trans h10 hmu
      have h2 : (Zsqrtd.norm ϖ).natAbs ∣ v := by
        have h20 := natAbs_norm_dvd_of_dvd h
        rw [hγ₀] at h20
        exact h20
      have h3 : (Zsqrtd.norm ϖ).natAbs ∣ 1 := by
        have hg := huv.gcd_eq_one
        have hd := Nat.dvd_gcd h1 h2
        rwa [hg] at hd
      have h4 : (Zsqrtd.norm ϖ).natAbs = 1 := Nat.dvd_one.mp h3
      exact hϖprime.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h4)

/-- **Primes of $\mathbb{Z}[\sqrt{d}]$ have prime-power norm.** Let $d < 0$ be an integer and let
$N(a + b\sqrt{d}) = a^2 - db^2$ be the norm on the ring $\mathbb{Z}[\sqrt{d}]$ of numbers
$a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$. For every prime $\varpi$ of $\mathbb{Z}[\sqrt{d}]$
there are a prime number $\ell$ and a natural number $s \ne 0$ such that $|N(\varpi)| = \ell^s$
and $\varpi$ divides $\ell$ in $\mathbb{Z}[\sqrt{d}]$. -/
public theorem prime_pow_norm_of_prime (hd : d < 0) {ϖ : ℤ√d} (hprime : Prime ϖ) :
    ∃ ℓ s : ℕ, ℓ.Prime ∧ s ≠ 0 ∧ (Zsqrtd.norm ϖ).natAbs = ℓ ^ s ∧
      ϖ ∣ (ℓ : ℤ√d) := by
  have hϖ0 : ϖ ≠ 0 := hprime.ne_zero
  have hn0 : (Zsqrtd.norm ϖ).natAbs ≠ 0 :=
    fun hz => hϖ0 (eq_zero_of_norm_natAbs_eq_zero hd hz)
  have hn1 : (Zsqrtd.norm ϖ).natAbs ≠ 1 :=
    fun h1 => hprime.not_isUnit (Zsqrtd.norm_eq_one_iff.mp h1)
  have hϖdvd : ϖ ∣ (((Zsqrtd.norm ϖ).natAbs : ℕ) : ℤ√d) := by
    have hnn := Zsqrtd.norm_nonneg hd.le ϖ
    have hnc : (((Zsqrtd.norm ϖ).natAbs : ℕ) : ℤ) = Zsqrtd.norm ϖ :=
      Int.natAbs_of_nonneg hnn
    have hnc2 : (((Zsqrtd.norm ϖ).natAbs : ℕ) : ℤ√d)
        = (Zsqrtd.norm ϖ : ℤ√d) := by
      have h2 := congrArg (Int.cast : ℤ → ℤ√d) hnc
      simp only [Int.cast_natCast] at h2
      exact h2
    rw [hnc2, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right ϖ _
  have hfac := Nat.prod_factorization_pow_eq_self hn0
  have hcast : (((Zsqrtd.norm ϖ).natAbs : ℕ) : ℤ√d)
      = ∏ ℓ ∈ (Zsqrtd.norm ϖ).natAbs.factorization.support,
        ((ℓ : ℤ√d) ^ ((Zsqrtd.norm ϖ).natAbs.factorization ℓ)) := by
    conv_lhs => rw [← hfac]
    simp only [Finsupp.prod, Nat.cast_prod, Nat.cast_pow]
  rw [hcast] at hϖdvd
  obtain ⟨ℓ, hℓmem, hℓdvd⟩ := (hprime.dvd_finsetProd_iff _).mp hϖdvd
  have hℓprime : ℓ.Prime := by
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hℓmem
    exact hℓmem.1
  have hℓdvd1 : ϖ ∣ (ℓ : ℤ√d) := hprime.dvd_of_dvd_pow hℓdvd
  have hnorm : (Zsqrtd.norm ϖ).natAbs ∣ ℓ ^ 2 := by
    have h := natAbs_norm_dvd_of_dvd hℓdvd1
    rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast,
      ← pow_two] at h
    exact h
  obtain ⟨s, hs2, hseq⟩ := (Nat.dvd_prime_pow hℓprime).mp hnorm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hseq
    exact hn1 hseq
  exact ⟨ℓ, s, hℓprime, hs0, hseq, hℓdvd1⟩

/-- **Splitting an element along coprime norms.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Let $u$ and $v$ be coprime nonzero
natural numbers. Every $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = uv$ factors as
$\alpha = \beta\gamma$ with $|N(\beta)| = u$ and $|N(\gamma)| = v$. -/
public theorem exists_factor_of_coprime [UniqueFactorizationMonoid (ℤ√d)]
    (hd : d < 0) {u v : ℕ} (huv : Nat.Coprime u v)
    (hu : u ≠ 0) (hv : v ≠ 0) (α : ℤ√d)
    (hα : (Zsqrtd.norm α).natAbs = u * v) :
    ∃ β γ : ℤ√d, β * γ = α ∧ (Zsqrtd.norm β).natAbs = u ∧
      (Zsqrtd.norm γ).natAbs = v := by
  classical
  have huv' : u * v ≠ 0 := mul_ne_zero hu hv
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [Zsqrtd.norm_zero,
      Int.natAbs_zero] at hα
    exact huv' hα.symm
  obtain ⟨f, hirr, hassoc⟩ := WfDvdMonoid.exists_factors α hα0
  have hpp : ∀ ϖ ∈ f, ∃ ℓ s : ℕ, ℓ.Prime ∧ s ≠ 0 ∧
      (Zsqrtd.norm ϖ).natAbs = ℓ ^ s := by
    intro ϖ hϖ
    obtain ⟨ℓ, s, hℓ, hs0, hseq, -⟩ :=
      prime_pow_norm_of_prime hd
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hirr ϖ hϖ))
    exact ⟨ℓ, s, hℓ, hs0, hseq⟩
  have hassoc_norm : (Zsqrtd.norm f.prod).natAbs
      = (Zsqrtd.norm α).natAbs := by
    obtain ⟨w, hw⟩ := hassoc
    have hcon := congrArg (fun x => (Zsqrtd.norm x).natAbs) hw
    rw [Zsqrtd.norm_mul, Int.natAbs_mul] at hcon
    have hw1 : (Zsqrtd.norm (w : ℤ√d)).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr w.isUnit
    rw [hw1, mul_one] at hcon
    exact hcon
  have hnorm_prod : ∀ s : Multiset (ℤ√d),
      (Zsqrtd.norm s.prod).natAbs
        = (s.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp only [Multiset.map_cons, Multiset.prod_cons, Zsqrtd.norm_mul,
        Int.natAbs_mul, ih]
  have hmem : ∀ ϖ ∈ f, (Zsqrtd.norm ϖ).natAbs ∣ u * v := by
    intro ϖ hϖ
    have h1 : ϖ ∣ f.prod := Multiset.dvd_prod hϖ
    have h2 := natAbs_norm_dvd_of_dvd h1
    rw [hassoc_norm, hα] at h2
    exact h2
  have hside : ∀ ϖ ∈ f,
      (Zsqrtd.norm ϖ).natAbs ∣ u ∨ (Zsqrtd.norm ϖ).natAbs ∣ v := by
    intro ϖ hϖ
    obtain ⟨ℓ, s, hℓprime, hs0, hseq⟩ := hpp ϖ hϖ
    have hdvd : ℓ ^ s ∣ u * v := by
      have h := hmem ϖ hϖ
      rwa [hseq] at h
    have hℓdvd : ℓ ∣ u * v := by
      have h1 : ℓ ∣ ℓ ^ s := by
        nth_rewrite 1 [← pow_one ℓ]
        exact pow_dvd_pow ℓ (by omega)
      exact dvd_trans h1 hdvd
    rcases (hℓprime.dvd_mul).mp hℓdvd with hℓu | hℓv
    · left
      rw [hseq]
      have hcop : Nat.Coprime (ℓ ^ s) v :=
        (huv.coprime_dvd_left hℓu).pow_left s
      exact hcop.dvd_of_dvd_mul_right hdvd
    · right
      rw [hseq]
      have hcop : Nat.Coprime (ℓ ^ s) u :=
        (huv.symm.coprime_dvd_left hℓv).pow_left s
      rw [mul_comm u v] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
  set p : ℤ√d → Prop := fun ϖ => (Zsqrtd.norm ϖ).natAbs ∣ u with hp
  set g₁ := f.filter p with hg₁
  set g₂ := f.filter (fun a => ¬ p a) with hg₂
  have hprod : g₁.prod * g₂.prod = f.prod :=
    Multiset.prod_filter_mul_prod_filter_not p
  have hmem1 : ∀ ϖ ∈ g₁, (Zsqrtd.norm ϖ).natAbs ∣ u := by
    intro ϖ hϖ
    exact (Multiset.mem_filter.mp hϖ).2
  have hmemf1 : ∀ ϖ ∈ g₁, ϖ ∈ f := by
    intro ϖ hϖ
    exact (Multiset.mem_filter.mp hϖ).1
  have hmem2 : ∀ ϖ ∈ g₂, (Zsqrtd.norm ϖ).natAbs ∣ v := by
    intro ϖ hϖ
    have hmem := Multiset.mem_filter.mp hϖ
    rcases hside ϖ hmem.1 with h | h
    · exact absurd h hmem.2
    · exact h
  have hmemf2 : ∀ ϖ ∈ g₂, ϖ ∈ f := by
    intro ϖ hϖ
    exact (Multiset.mem_filter.mp hϖ).1
  have hAB : (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
        (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod = u * v := by
    rw [← hnorm_prod, ← hnorm_prod, ← Int.natAbs_mul, ← Zsqrtd.norm_mul,
      hprod, hassoc_norm, hα]
  have hA : (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ∣ u := by
    have hdvd : (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ∣ u * v := by
      rw [← hAB]
      exact dvd_mul_right _ _
    have hcop : Nat.Coprime
        (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod v := by
      rw [Nat.coprime_multiset_prod_left_iff]
      intro n hn
      obtain ⟨ϖ, hϖ, rfl⟩ := Multiset.mem_map.mp hn
      obtain ⟨ℓ, s, hℓprime, hs0, hseq⟩ := hpp ϖ (hmemf1 ϖ hϖ)
      have hℓu : ℓ ∣ u := by
        have h1 : ℓ ∣ ℓ ^ s := by
          nth_rewrite 1 [← pow_one ℓ]
          exact pow_dvd_pow ℓ (by omega)
        have h2 : ℓ ^ s ∣ u := by
          rw [← hseq]
          exact hmem1 ϖ hϖ
        exact dvd_trans h1 h2
      have h2 : Nat.Coprime (ℓ ^ s) v :=
        (huv.coprime_dvd_left hℓu).pow_left s
      rw [hseq]
      exact h2
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hB : (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ∣ v := by
    have hdvd : (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ∣ u * v := by
      rw [← hAB]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime
        (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod u := by
      rw [Nat.coprime_multiset_prod_left_iff]
      intro n hn
      obtain ⟨ϖ, hϖ, rfl⟩ := Multiset.mem_map.mp hn
      obtain ⟨ℓ, s, hℓprime, hs0, hseq⟩ := hpp ϖ (hmemf2 ϖ hϖ)
      have hℓv : ℓ ∣ v := by
        have h1 : ℓ ∣ ℓ ^ s := by
          nth_rewrite 1 [← pow_one ℓ]
          exact pow_dvd_pow ℓ (by omega)
        have h2 : ℓ ^ s ∣ v := by
          rw [← hseq]
          exact hmem2 ϖ hϖ
        exact dvd_trans h1 h2
      have h2 : Nat.Coprime (ℓ ^ s) u :=
        (huv.symm.coprime_dvd_left hℓv).pow_left s
      rw [hseq]
      exact h2
    have hdvd2 : (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ∣ v * u := by
      rwa [mul_comm u v] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd2
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hne : (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
      (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod ≠ 0 := by
    rw [hAB]
    exact huv'
  have hab : a * b = 1 := by
    have h := hAB
    rw [ha, hb] at h
    have h2 : ((g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
        (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod) * (a * b)
        = (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
          (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod := by
      linear_combination -h
    have h3 : ((g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
        (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod) * (a * b)
        = ((g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod *
          (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod) * 1 := by
      rw [mul_one]
      exact h2
    exact mul_left_cancel₀ hne h3
  have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab.symm⟩
  have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by rw [mul_comm]; exact hab.symm⟩
  have hAeq : (g₁.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod = u := by
    rw [ha, ha1, mul_one]
  have hBeq : (g₂.map (fun ϖ => (Zsqrtd.norm ϖ).natAbs)).prod = v := by
    rw [hb, hb1, mul_one]
  obtain ⟨w, hw⟩ := hassoc
  refine ⟨g₁.prod, g₂.prod * (w : ℤ√d), ?_, ?_, ?_⟩
  · rw [← mul_assoc, hprod]
    exact hw
  · rw [hnorm_prod]
    exact hAeq
  · rw [Zsqrtd.norm_mul, Int.natAbs_mul, hnorm_prod,
      Zsqrtd.norm_eq_one_iff.mpr w.isUnit, mul_one]
    exact hBeq

/-- **Counting a norm class generated by one element.** Let $d$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of formal sums $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is an integral domain
with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for each
$m \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = m$ is finite. Let
$n \in \mathbb{N}$ and let $s \ne 0$ satisfy $|N(s)| = n$. If every $\alpha$ with $|N(\alpha)| = n$
equals $us$ for some unit $u$, then exactly $k$ elements $\alpha$ satisfy $|N(\alpha)| = n$. -/
public theorem card_repr_of_shape [IsDomain (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {n : ℕ} (s : ℤ√d)
    (hs : (Zsqrtd.norm s).natAbs = n) (hs0 : s ≠ 0)
    (hclass : ∀ α : ℤ√d, (Zsqrtd.norm α).natAbs = n →
      ∃ u : ℤ√d, IsUnit u ∧ α = u * s) :
    Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = n} = k := by
  have hnorm : ∀ i : Fin k, (Zsqrtd.norm (unitVal i * s)).natAbs = n := by
    intro i
    rw [Zsqrtd.norm_mul, Int.natAbs_mul,
      Zsqrtd.norm_eq_one_iff.mpr (IsUnit.of_mul_eq_one _ (hinv i)), one_mul]
    exact hs
  have hbij : Function.Bijective (fun i : Fin k =>
      (⟨unitVal i * s, hnorm i⟩ :
        {α : ℤ√d // (Zsqrtd.norm α).natAbs = n})) := by
    constructor
    · intro i j hij
      have h : unitVal i * s = unitVal j * s := congrArg Subtype.val hij
      have h2 : unitVal i = unitVal j := mul_right_cancel₀ hs0 h
      exact hinj h2
    · rintro ⟨α, hα⟩
      obtain ⟨u, hu, rfl⟩ := hclass α hα
      obtain ⟨i, rfl⟩ := hcomplete u hu
      exact ⟨i, rfl⟩
  have h := Fintype.card_of_bijective hbij
  rw [Fintype.card_fin] at h
  exact h.symm

/-- **Norm counts are multiplicative up to units.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for
each $n \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = n$ is
finite, and let $r(n)$ be its size. If $u$ and $v$ are coprime nonzero natural numbers, then
$r(u)\,r(v) = k\,r(uv)$. -/
public theorem card_mul_of_coprime [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    (hd : d < 0) {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {u v : ℕ} (huv : Nat.Coprime u v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = u} *
      Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = v}
      = k * Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = u * v} := by
  classical
  have hφ : ∀ p : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u} ×
      {α : ℤ√d // (Zsqrtd.norm α).natAbs = v},
      (Zsqrtd.norm (p.1.1 * p.2.1)).natAbs = u * v := by
    intro p
    rw [Zsqrtd.norm_mul, Int.natAbs_mul, p.1.2, p.2.2]
  set φ : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u} ×
      {α : ℤ√d // (Zsqrtd.norm α).natAbs = v} →
      {α : ℤ√d // (Zsqrtd.norm α).natAbs = u * v} :=
    fun p => ⟨p.1.1 * p.2.1, hφ p⟩ with hφdef
  have hfib : ∀ y : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u * v},
      Fintype.card {x : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u} ×
        {α : ℤ√d // (Zsqrtd.norm α).natAbs = v} // φ x = y} = k := by
    intro y
    obtain ⟨α, hα⟩ := y
    obtain ⟨β₀, γ₀, hmul, hβ₀, hγ₀⟩ :=
      exists_factor_of_coprime hd huv hu hv α hα
    have hβ00 : β₀ ≠ 0 := fun hz =>
      hu (by rw [← hβ₀, hz, Zsqrtd.norm_zero,
        Int.natAbs_zero])
    have hγ00 : γ₀ ≠ 0 := fun hz =>
      hv (by rw [← hγ₀, hz, Zsqrtd.norm_zero,
        Int.natAbs_zero])
    have hN1 : ∀ i : Fin k,
        (Zsqrtd.norm (unitVal i * β₀)).natAbs = u := by
      intro i
      rw [Zsqrtd.norm_mul, Int.natAbs_mul,
        Zsqrtd.norm_eq_one_iff.mpr (IsUnit.of_mul_eq_one _ (hinv i)), one_mul]
      exact hβ₀
    have hN2 : ∀ i : Fin k,
        (Zsqrtd.norm (unitValInv i * γ₀)).natAbs = v := by
      intro i
      rw [Zsqrtd.norm_mul, Int.natAbs_mul,
        Zsqrtd.norm_eq_one_iff.mpr (IsUnit.of_mul_eq_one_right _ (hinv i)), one_mul]
      exact hγ₀
    have hmem : ∀ i : Fin k, φ (⟨unitVal i * β₀, hN1 i⟩,
        ⟨unitValInv i * γ₀, hN2 i⟩) = ⟨α, hα⟩ := by
      intro i
      apply Subtype.ext
      change (unitVal i * β₀) * (unitValInv i * γ₀) = α
      rw [← hmul, mul_mul_mul_comm, hinv, one_mul]
    have hbij : Function.Bijective (fun i : Fin k =>
        (⟨((⟨unitVal i * β₀, hN1 i⟩ :
          {α : ℤ√d // (Zsqrtd.norm α).natAbs = u}),
          (⟨unitValInv i * γ₀, hN2 i⟩ :
          {α : ℤ√d // (Zsqrtd.norm α).natAbs = v})), hmem i⟩ :
          {x : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u} ×
            {α : ℤ√d // (Zsqrtd.norm α).natAbs = v} //
            φ x = ⟨α, hα⟩})) := by
      constructor
      · intro i j hij
        have h : unitVal i * β₀ = unitVal j * β₀ :=
          congrArg (fun x => (x.1.1).1) hij
        have h2 : unitVal i = unitVal j := mul_right_cancel₀ hβ00 h
        exact hinj h2
      · rintro ⟨⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩, hmem'⟩
        have heq : β * γ = α := congrArg Subtype.val hmem'
        have hdvd : β ∣ β₀ * γ₀ := ⟨γ, by rw [hmul, heq]⟩
        have hβdvd := dvd_of_coprime_norms hd huv hu _ β hβ (dvd_refl u) β₀ γ₀
          hγ₀ hdvd
        obtain ⟨w, hw⟩ := hβdvd
        have hw1 : (Zsqrtd.norm w).natAbs = 1 := by
          have h := congrArg (fun x => (Zsqrtd.norm x).natAbs) hw
          rw [hβ₀, Zsqrtd.norm_mul, Int.natAbs_mul, hβ] at h
          have h2 : u * (Zsqrtd.norm w).natAbs = u * 1 := by
            rw [mul_one]
            exact h.symm
          exact mul_left_cancel₀ hu h2
        have hwu : IsUnit w := Zsqrtd.norm_eq_one_iff.mp hw1
        obtain ⟨η, rfl⟩ := hwu
        have hβeq : β = β₀ * ((η⁻¹ : (ℤ√d)ˣ) : ℤ√d) := by
          have h := congrArg (· * ((η⁻¹ : (ℤ√d)ˣ) : ℤ√d)) hw
          rw [mul_assoc, Units.mul_inv, mul_one] at h
          exact h.symm
        have hγeq : γ = (η : ℤ√d) * γ₀ := by
          have hcan : ((η⁻¹ : (ℤ√d)ˣ) : ℤ√d) * γ = γ₀ := by
            apply mul_left_cancel₀ hβ00
            rw [← mul_assoc, ← hβeq, heq, hmul]
          have h2 := congrArg ((η : ℤ√d) * ·) hcan
          rwa [← mul_assoc, Units.mul_inv, one_mul] at h2
        obtain ⟨i, hi⟩ :=
          hcomplete ((η⁻¹ : (ℤ√d)ˣ) : ℤ√d) η⁻¹.isUnit
        have hinv : unitValInv i = (η : ℤ√d) := by
          have h1 : unitValInv i * unitVal i = 1 := by rw [mul_comm]; exact hinv i
          rw [hi] at h1
          have h2 := congrArg (· * (η : ℤ√d)) h1
          rwa [mul_assoc, Units.inv_mul, mul_one, one_mul] at h2
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change ((⟨unitVal i * β₀, hN1 i⟩ :
          {α : ℤ√d // (Zsqrtd.norm α).natAbs = u}),
          (⟨unitValInv i * γ₀, hN2 i⟩ :
          {α : ℤ√d // (Zsqrtd.norm α).natAbs = v})) = (⟨β, hβ⟩, ⟨γ, hγ⟩)
        refine Prod.ext ?_ ?_ <;> apply Subtype.ext
        · change unitVal i * β₀ = β
          rw [hi, hβeq]
          ring
        · change unitValInv i * γ₀ = γ
          rw [hinv]
          exact hγeq.symm
    have h := Fintype.card_of_bijective hbij
    rw [Fintype.card_fin] at h
    exact h.symm
  have h1 : Fintype.card ({α : ℤ√d // (Zsqrtd.norm α).natAbs = u} ×
      {α : ℤ√d // (Zsqrtd.norm α).natAbs = v})
      = ∑ _y : {α : ℤ√d // (Zsqrtd.norm α).natAbs = u * v}, k := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv φ), Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro y _
    exact hfib y
  rw [Fintype.card_prod, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id] at h1
  rw [mul_comm k _]
  exact h1

/-- **The norm of a power in $\mathbb{Z}[\sqrt{d}]$.** Let $d$ be an integer and let
$N(a + b\sqrt{d}) = a^2 - db^2$ be the norm on the ring $\mathbb{Z}[\sqrt{d}]$ of formal
expressions $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ and $\sqrt{d}^2 = d$. Then
$N(x^n) = N(x)^n$ for every $x \in \mathbb{Z}[\sqrt{d}]$ and every natural number $n$. -/
public theorem norm_pow (x : ℤ√d) (n : ℕ) : Zsqrtd.norm (x ^ n) = Zsqrtd.norm x ^ n :=
  map_pow Zsqrtd.normMonoidHom x n

/-- **Elements whose norm is a power of a ramified two.** Let $d < 0$ be an integer such that the
ring $\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique
factorization domain, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Suppose
$2 = \varepsilon\rho^2$ for a unit $\varepsilon$ and a prime $\rho$ with $|N(\rho)| = 2$. Then for
every $e \in \mathbb{N}$, every $\alpha$ with $|N(\alpha)| = 2^e$ equals $u\rho^e$ for some unit
$u$. -/
public theorem exists_unit_mul_pow_of_norm_two_pow
    [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    (hd : d < 0) {ρ ε : ℤ√d} (hρ : Prime ρ) (hρnorm : (Zsqrtd.norm ρ).natAbs = 2)
    (hε : IsUnit ε) (htwo : (2 : ℤ√d) = ε * ρ ^ 2) (e : ℕ) (α : ℤ√d)
    (hα : (Zsqrtd.norm α).natAbs = 2 ^ e) :
    ∃ u : ℤ√d, IsUnit u ∧ α = u * ρ ^ e := by
  revert α hα
  induction e with
  | zero =>
    intro α hα
    refine ⟨α, Zsqrtd.norm_eq_one_iff.mp ?_, by simp⟩
    simpa using hα
  | succ e ih =>
    intro α hα
    have h2e : (2 : ℕ) ^ (e + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [Zsqrtd.norm_zero,
        Int.natAbs_zero] at hα
      exact h2e hα.symm
    have hαnu : ¬ IsUnit α := by
      intro hu
      have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
      rw [hα] at h1
      have hlt := (e + 1).lt_two_pow_self
      omega
    obtain ⟨ϖ, hϖirr, hϖα⟩ :=
      WfDvdMonoid.exists_irreducible_factor hαnu hα0
    have hϖprime : Prime ϖ :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖirr
    obtain ⟨β, rfl⟩ := hϖα
    have hϖdvd : ϖ ∣ ((2 ^ (e + 1) : ℕ) : ℤ√d) := by
      have hαnorm : Zsqrtd.norm (ϖ * β) = ((2 ^ (e + 1) : ℕ) : ℤ) := by
        have hnn := Zsqrtd.norm_nonneg hd.le (ϖ * β)
        have h := Int.natAbs_of_nonneg hnn
        rw [hα] at h
        exact h.symm
      have h2 : ϖ * β * star (ϖ * β) = ((2 ^ (e + 1) : ℕ) : ℤ√d) := by
        have h := (Zsqrtd.norm_eq_mul_conj (ϖ * β)).symm
        rw [hαnorm] at h
        exact_mod_cast h
      have h1 : ϖ ∣ ϖ * β * star (ϖ * β) :=
        dvd_mul_of_dvd_left (dvd_mul_right ϖ β) _
      rwa [h2] at h1
    have hcast : ((2 ^ (e + 1) : ℕ) : ℤ√d) = (2 : ℤ√d) ^ (e + 1) := by
      norm_cast
    rw [hcast, htwo, mul_pow] at hϖdvd
    have hunit : IsUnit (ε ^ (e + 1)) := hε.pow _
    rcases hϖprime.dvd_mul.mp hϖdvd with h | h
    · exfalso
      exact hϖprime.not_isUnit
        (isUnit_of_dvd_one (dvd_trans h (isUnit_iff_dvd_one.mp hunit)))
    · have hdvd : ϖ ∣ ρ :=
        hϖprime.dvd_of_dvd_pow (hϖprime.dvd_of_dvd_pow h)
      have hass : Associated ϖ ρ :=
        hϖprime.associated_of_dvd hρ hdvd
      have hϖnorm : (Zsqrtd.norm ϖ).natAbs = 2 := by
        obtain ⟨w, hw⟩ := hass
        have hcon := congrArg (fun x => (Zsqrtd.norm x).natAbs) hw
        rw [Zsqrtd.norm_mul, Int.natAbs_mul] at hcon
        have hw1 : (Zsqrtd.norm (w : ℤ√d)).natAbs = 1 :=
          Zsqrtd.norm_eq_one_iff.mpr w.isUnit
        rw [hw1, mul_one] at hcon
        rwa [hρnorm] at hcon
      have hβ : (Zsqrtd.norm β).natAbs = 2 ^ e := by
        have hα2 := hα
        rw [Zsqrtd.norm_mul, Int.natAbs_mul, hϖnorm, pow_succ'] at hα2
        exact mul_left_cancel₀ (by norm_num) hα2
      obtain ⟨u, hu, hβeq⟩ := ih β hβ
      obtain ⟨w, hw⟩ := hass
      have hϖ : ϖ = ρ * ((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) := by
        rw [← hw]
        simp [mul_assoc, Units.mul_inv]
      refine ⟨((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) * u,
        IsUnit.mul w⁻¹.isUnit hu, ?_⟩
      rw [hβeq, hϖ, pow_succ']
      ring

/-- **Norm counts at powers of a ramified two.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for
each $n \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = n$ is
finite, and let $r(n)$ be its size. If $2 = \varepsilon\rho^2$ for a unit $\varepsilon$ and a
prime $\rho$ with $|N(\rho)| = 2$, then $r(2^e) = k$ for every $e \in \mathbb{N}$. -/
public theorem card_norm_two_pow [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    (hd : d < 0) {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {ρ ε : ℤ√d} (hρ : Prime ρ)
    (hρnorm : (Zsqrtd.norm ρ).natAbs = 2) (hε : IsUnit ε) (htwo : (2 : ℤ√d) = ε * ρ ^ 2)
    (e : ℕ) : Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = 2 ^ e} = k :=
  card_repr_of_shape unitVal unitValInv hinv hinj hcomplete (ρ ^ e)
    (by rw [norm_pow, Int.natAbs_pow, hρnorm]) (pow_ne_zero e hρ.ne_zero)
    (exists_unit_mul_pow_of_norm_two_pow hd hρ hρnorm hε htwo e)

/-- **Peeling an inert prime off an element of norm $q^f$.** Let $d < 0$ be an integer such that
the ring $\mathbb{Z}[\sqrt{d}]$ of numbers $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ is a unique
factorization domain, with norm $N(a + b\sqrt{d}) = a^2 - db^2$. Let $q$ be a natural number
that is prime in $\mathbb{Z}[\sqrt{d}]$, let $f$ be a natural number, and let
$\alpha \in \mathbb{Z}[\sqrt{d}]$ be nonzero and not a unit with $|N(\alpha)| = q^f$. Then
$\alpha = wq\beta$ for some unit $w$ and some $\beta \in \mathbb{Z}[\sqrt{d}]$ with
$q^2 \cdot |N(\beta)| = q^f$. -/
public theorem inert_peel [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)] {q : ℕ}
    (hd : d < 0) (hqprime : Prime (q : ℤ√d))
    {f : ℕ} {α : ℤ√d} (hα : (Zsqrtd.norm α).natAbs = q ^ f)
    (hαnu : ¬ IsUnit α) (hα0 : α ≠ 0) :
    ∃ β : ℤ√d, ∃ w : (ℤ√d)ˣ, α = (w : ℤ√d) * (q : ℤ√d) * β ∧
      (q * q) * (Zsqrtd.norm β).natAbs = q ^ f := by
  obtain ⟨ϖ, hϖirr, hϖα⟩ :=
    WfDvdMonoid.exists_irreducible_factor hαnu hα0
  have hϖprime : Prime ϖ :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖirr
  obtain ⟨β, rfl⟩ := hϖα
  have hϖdvd : ϖ ∣ ((q ^ f : ℕ) : ℤ√d) := by
    have hαnorm : Zsqrtd.norm (ϖ * β) = ((q ^ f : ℕ) : ℤ) := by
      have hnn := Zsqrtd.norm_nonneg hd.le (ϖ * β)
      have h := Int.natAbs_of_nonneg hnn
      rw [hα] at h
      exact h.symm
    have h2 : ϖ * β * star (ϖ * β) = ((q ^ f : ℕ) : ℤ√d) := by
      have h := (Zsqrtd.norm_eq_mul_conj (ϖ * β)).symm
      rw [hαnorm] at h
      exact_mod_cast h
    have h1 : ϖ ∣ ϖ * β * star (ϖ * β) :=
      dvd_mul_of_dvd_left (dvd_mul_right ϖ β) _
    rwa [h2] at h1
  have hcast : ((q ^ f : ℕ) : ℤ√d) = (q : ℤ√d) ^ f := by norm_cast
  rw [hcast] at hϖdvd
  have hdvd : ϖ ∣ (q : ℤ√d) := hϖprime.dvd_of_dvd_pow hϖdvd
  have hass : Associated ϖ (q : ℤ√d) :=
    hϖprime.associated_of_dvd hqprime hdvd
  obtain ⟨w, hw⟩ := hass
  have hϖ : ϖ = (q : ℤ√d) * ((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) := by
    rw [← hw]
    simp [mul_assoc, Units.mul_inv]
  have hϖnorm : (Zsqrtd.norm ϖ).natAbs = q * q := by
    have hcon := congrArg (fun x => (Zsqrtd.norm x).natAbs) hw
    rw [Zsqrtd.norm_mul, Int.natAbs_mul] at hcon
    have hw1 : (Zsqrtd.norm (w : ℤ√d)).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr w.isUnit
    rw [hw1, mul_one] at hcon
    have hqq : (Zsqrtd.norm (q : ℤ√d)).natAbs = q * q := by
      rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast]
    rwa [hqq] at hcon
  refine ⟨β, w⁻¹, ?_, ?_⟩
  · rw [hϖ]
    ring
  · have hα2 := hα
    rw [Zsqrtd.norm_mul, Int.natAbs_mul, hϖnorm] at hα2
    exact hα2

/-- **Elements of norm $q^{2n}$ over an inert prime.** Let $d < 0$ be an integer such that the
ring $\mathbb{Z}[\sqrt{d}]$ of numbers $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ is a unique
factorization domain, with norm $N(a + b\sqrt{d}) = a^2 - db^2$. Let $q$ be a prime number that
is also prime in $\mathbb{Z}[\sqrt{d}]$. Then for every natural number $n$, every
$\alpha \in \mathbb{Z}[\sqrt{d}]$ with $|N(\alpha)| = q^{2n}$ is of the form $\alpha = uq^n$ for
some unit $u$. -/
public theorem inert_even [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)] {q : ℕ} [Fact q.Prime]
    (hd : d < 0) (hqprime : Prime (q : ℤ√d))
    (n : ℕ) (α : ℤ√d) (hα : (Zsqrtd.norm α).natAbs = q ^ (2 * n)) :
    ∃ u : ℤ√d, IsUnit u ∧ α = u * (q : ℤ√d) ^ n := by
  revert α hα
  induction n with
  | zero =>
    intro α hα
    refine ⟨α, Zsqrtd.norm_eq_one_iff.mp ?_, by simp⟩
    simpa using hα
  | succ n ih =>
    intro α hα
    have hq : q.Prime := Fact.out
    have hq0 : q ≠ 0 := hq.ne_zero
    have hexp : 2 * (n + 1) ≠ 0 := by omega
    have hqf0 : q ^ (2 * (n + 1)) ≠ 0 := pow_ne_zero _ hq0
    have hqf1 : q ^ (2 * (n + 1)) ≠ 1 := by
      intro hz
      have hdvd : q ∣ 1 := hz ▸ dvd_pow_self q hexp
      exact hq.ne_one (Nat.dvd_one.mp hdvd)
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [Zsqrtd.norm_zero,
        Int.natAbs_zero] at hα
      exact hqf0 hα.symm
    have hαnu : ¬ IsUnit α := by
      intro hu
      have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
      rw [hα] at h1
      exact hqf1 h1
    obtain ⟨β, w, hαeq, hnormβ⟩ := inert_peel hd hqprime hα hαnu hα0
    have hexpand : q ^ (2 * (n + 1)) = (q * q) * q ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 + 2 * n from by omega, pow_add, pow_two]
    rw [hexpand] at hnormβ
    have hβ : (Zsqrtd.norm β).natAbs = q ^ (2 * n) :=
      mul_left_cancel₀ (mul_ne_zero hq0 hq0) hnormβ
    obtain ⟨u, hu, hβeq⟩ := ih β hβ
    refine ⟨(w : ℤ√d) * u, IsUnit.mul w.isUnit hu, ?_⟩
    rw [hαeq, hβeq, pow_succ']
    ring

/-- **No element has norm $q^{2n+1}$ over an inert prime.** Let $d < 0$ be an integer such that
the ring $\mathbb{Z}[\sqrt{d}]$ of numbers $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ is a unique
factorization domain, with norm $N(a + b\sqrt{d}) = a^2 - db^2$. Let $q$ be a prime number that
is also prime in $\mathbb{Z}[\sqrt{d}]$. Then for every natural number $n$, no
$\alpha \in \mathbb{Z}[\sqrt{d}]$ satisfies $|N(\alpha)| = q^{2n+1}$. -/
public theorem inert_odd [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)] {q : ℕ} [Fact q.Prime]
    (hd : d < 0) (hqprime : Prime (q : ℤ√d)) :
    ∀ (n : ℕ) (α : ℤ√d),
      (Zsqrtd.norm α).natAbs = q ^ (2 * n + 1) → False := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih α hα
  have hq : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hq.ne_zero
  have hexp : 2 * n + 1 ≠ 0 := by omega
  have hqf0 : q ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hq0
  have hqf1 : q ^ (2 * n + 1) ≠ 1 := by
    intro hz
    have hdvd : q ∣ 1 := hz ▸ dvd_pow_self q hexp
    exact hq.ne_one (Nat.dvd_one.mp hdvd)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [Zsqrtd.norm_zero, Int.natAbs_zero] at hα
    exact hqf0 hα.symm
  have hαnu : ¬ IsUnit α := by
    intro hu
    have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hα] at h1
    exact hqf1 h1
  obtain ⟨β, w, hαeq, hnormβ⟩ := inert_peel hd hqprime hα hαnu hα0
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hdvd : q * q ∣ q := by
      rw [show (2 : ℕ) * 0 + 1 = 1 from rfl] at hnormβ
      simp only [pow_one] at hnormβ
      exact ⟨_, hnormβ.symm⟩
    have hle : q * q ≤ q := Nat.le_of_dvd hq.pos hdvd
    have hq1 : q ≤ 1 := by
      have hle2 : q * q ≤ q * 1 := by rwa [mul_one]
      exact le_of_mul_le_mul_left hle2 hq.pos
    have hlt := hq.one_lt
    omega
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hexpand : q ^ (2 * (n' + 1) + 1) = (q * q) * q ^ (2 * n' + 1) := by
      rw [show 2 * (n' + 1) + 1 = 2 + (2 * n' + 1) from by omega, pow_add,
        pow_two]
    rw [hexpand] at hnormβ
    have hβ : (Zsqrtd.norm β).natAbs = q ^ (2 * n' + 1) :=
      mul_left_cancel₀ (mul_ne_zero hq0 hq0) hnormβ
    exact ih n' (by omega) β hβ

/-- **Norm counts at an inert prime.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for
each $n \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = n$ is
finite, and let $r(n)$ be its size. If $q$ is a prime number that is also a prime element of
$\mathbb{Z}[\sqrt d]$, then for every $f \in \mathbb{N}$ we have $r(q^f) = k$ when $f$ is even and
$r(q^f) = 0$ when $f$ is odd. -/
public theorem card_norm_inert_pow [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    (hd : d < 0) {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {q f : ℕ} [Fact q.Prime]
    (hqprime : Prime (q : ℤ√d)) :
    Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = q ^ f} = if Even f then k else 0 := by
  have hq : q.Prime := Fact.out
  by_cases hf : Even f
  · obtain ⟨m, rfl⟩ := hf
    rw [ite_eq_left ⟨m, rfl⟩]
    have hqcast : (q : ℤ√d) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hpow0 : (q : ℤ√d) ^ m ≠ 0 := pow_ne_zero m hqcast
    refine card_repr_of_shape unitVal unitValInv hinv hinj hcomplete ((q : ℤ√d) ^ m) ?_ hpow0 ?_
    · have hnorm : ∀ j : ℕ,
          Zsqrtd.norm ((q : ℤ√d) ^ j) = ((q : ℤ) ^ j) ^ 2 := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ', Zsqrtd.norm_mul, ih, Zsqrtd.norm_natCast]
          ring
      rw [hnorm, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, pow_two,
        ← pow_add]
    · intro α hα
      have hα2 : (Zsqrtd.norm α).natAbs = q ^ (2 * m) := by
        rw [two_mul]
        exact hα
      obtain ⟨u, hu, rfl⟩ := inert_even hd hqprime m α hα2
      exact ⟨u, hu, rfl⟩
  · rw [ite_eq_right hf]
    have hodd : Odd f := by
      rcases Nat.even_or_odd f with h | h
      · exact absurd h hf
      · exact h
    obtain ⟨t, rfl⟩ := hodd
    change Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = q ^ (2 * t + 1)}
      = 0
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨α, hα⟩ => inert_odd hd hqprime t α hα⟩

/-- **Elements of norm $p^e$ over a split prime.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt{d}]$ of numbers $a + b\sqrt{d}$ with $a, b \in \mathbb{Z}$ is a unique
factorization domain, with norm $N(a + b\sqrt{d}) = a^2 - db^2$ and conjugation
$\overline{a + b\sqrt{d}} = a - b\sqrt{d}$. Let $p$ be a prime number and let $\pi$ be a prime of
$\mathbb{Z}[\sqrt{d}]$ with $N(\pi) = p$ and $p = \pi\bar{\pi}$ such that $\bar{\pi}$ is also
prime. Then for every natural number $e$, every $\alpha \in \mathbb{Z}[\sqrt{d}]$ with
$|N(\alpha)| = p^e$ is of the form $\alpha = u\pi^j\bar{\pi}^k$ for some unit $u$ and natural
numbers $j, k$ with $j + k = e$. -/
public theorem exists_unit_mul_split_pow [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    (hd : d < 0) {p : ℕ} [Fact p.Prime]
    {π : ℤ√d} (hnorm : Zsqrtd.norm π = p) (hprime : Prime π)
    (hmul : (p : ℤ√d) = π * star π)
    (hπbar_prime : Prime (star π)) :
    ∀ (e' : ℕ) (α : ℤ√d),
      (Zsqrtd.norm α).natAbs = p ^ e' →
      ∃ u : ℤ√d,
        IsUnit u ∧ ∃ j k : ℕ, j + k = e' ∧ α = u * π ^ j * star π ^ k := by
  have hp : p.Prime := Fact.out
  have hπ0 : π ≠ 0 := hprime.ne_zero
  have hnorm_bar : Zsqrtd.norm (star π) = (p : ℤ) := by
    rw [Zsqrtd.norm_conj, hnorm]
  have hassoc_norm : ∀ {a b : ℤ√d}, Associated a b →
      (Zsqrtd.norm a).natAbs = (Zsqrtd.norm b).natAbs := by
    intro a b hass
    obtain ⟨w, hw⟩ := hass
    have hcon := congrArg (fun x => (Zsqrtd.norm x).natAbs) hw
    rw [Zsqrtd.norm_mul, Int.natAbs_mul] at hcon
    have hw1 : (Zsqrtd.norm (w : ℤ√d)).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr w.isUnit
    rw [hw1, mul_one] at hcon
    exact hcon
  intro e'
  induction e' with
  | zero =>
    intro α hα
    have hu : IsUnit α := Zsqrtd.norm_eq_one_iff.mp (by simpa using hα)
    exact ⟨α, hu, 0, 0, rfl, by simp⟩
  | succ e ih =>
    intro α hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      have h0 : Zsqrtd.norm (0 : ℤ√d) = 0 := Zsqrtd.norm_zero
      rw [h0, Int.natAbs_zero] at hα
      exact pow_ne_zero _ hp.ne_zero hα.symm
    have hαnu : ¬ IsUnit α := by
      intro hu
      have h1 : (Zsqrtd.norm α).natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
      rw [hα] at h1
      have hdvd : p ∣ 1 := h1 ▸ dvd_pow_self p (Nat.succ_ne_zero e)
      exact hp.ne_one (Nat.dvd_one.mp hdvd)
    obtain ⟨ϖ, hϖirr, hϖα⟩ := WfDvdMonoid.exists_irreducible_factor hαnu hα0
    have hϖprime : Prime ϖ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖirr
    obtain ⟨β, rfl⟩ := hϖα
    have hϖ_dvd_pe : ϖ ∣ ((p ^ (e + 1) : ℕ) : ℤ√d) := by
      have hαnorm : Zsqrtd.norm (ϖ * β) = ((p ^ (e + 1) : ℕ) : ℤ) := by
        have hnn := Zsqrtd.norm_nonneg hd.le (ϖ * β)
        have h := Int.natAbs_of_nonneg hnn
        rw [hα] at h
        exact h.symm
      have h2 : ϖ * β * star (ϖ * β) = ((p ^ (e + 1) : ℕ) : ℤ√d) := by
        have h := (Zsqrtd.norm_eq_mul_conj (ϖ * β)).symm
        rw [hαnorm] at h
        exact_mod_cast h
      have h1 : ϖ ∣ ϖ * β * star (ϖ * β) :=
        dvd_mul_of_dvd_left (dvd_mul_right ϖ β) _
      rwa [h2] at h1
    have hpe : ((p ^ (e + 1) : ℕ) : ℤ√d) = π ^ (e + 1) * star π ^ (e + 1) := by
      rw [Nat.cast_pow, hmul, mul_pow]
    rw [hpe] at hϖ_dvd_pe
    have hβnorm : ∀ {ϖn : ℕ}, (Zsqrtd.norm ϖ).natAbs = ϖn →
        ϖn * (Zsqrtd.norm β).natAbs = p ^ (e + 1) := by
      intro ϖn hϖn
      rw [Zsqrtd.norm_mul, Int.natAbs_mul, hϖn] at hα
      exact hα
    rcases hϖprime.dvd_mul.mp hϖ_dvd_pe with h | h
    · have hdvd : ϖ ∣ π := hϖprime.dvd_of_dvd_pow h
      have hass : Associated ϖ π := hϖprime.associated_of_dvd hprime hdvd
      have hϖnorm : (Zsqrtd.norm ϖ).natAbs = p := by
        rw [hassoc_norm hass, hnorm, Int.natAbs_natCast]
      have hβ : (Zsqrtd.norm β).natAbs = p ^ e := by
        have hmul := hβnorm hϖnorm
        rw [pow_succ'] at hmul
        exact mul_left_cancel₀ hp.ne_zero hmul
      obtain ⟨u, hu, j, k, hjk, hβeq⟩ := ih β hβ
      obtain ⟨w, hw⟩ := hass
      have hϖ : ϖ = π * ((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) := by
        rw [← hw]
        simp [mul_assoc, Units.mul_inv]
      refine ⟨((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) * u,
        IsUnit.mul w⁻¹.isUnit hu, j + 1, k, by omega, ?_⟩
      rw [hϖ, hβeq]
      ring
    · have hdvd : ϖ ∣ star π := hϖprime.dvd_of_dvd_pow h
      have hass : Associated ϖ (star π) :=
        hϖprime.associated_of_dvd hπbar_prime hdvd
      have hϖnorm : (Zsqrtd.norm ϖ).natAbs = p := by
        rw [hassoc_norm hass, hnorm_bar, Int.natAbs_natCast]
      have hβ : (Zsqrtd.norm β).natAbs = p ^ e := by
        have hmul := hβnorm hϖnorm
        rw [pow_succ'] at hmul
        exact mul_left_cancel₀ hp.ne_zero hmul
      obtain ⟨u, hu, j, k, hjk, hβeq⟩ := ih β hβ
      obtain ⟨w, hw⟩ := hass
      have hϖ : ϖ = star π * ((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) := by
        rw [← hw]
        simp [mul_assoc, Units.mul_inv]
      refine ⟨((w⁻¹ : (ℤ√d)ˣ) : ℤ√d) * u,
        IsUnit.mul w⁻¹.isUnit hu, j, k + 1, by omega, ?_⟩
      rw [hϖ, hβeq]
      ring

/-- **Norm counts at a split prime.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for
each $n \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = n$ is
finite, and let $r(n)$ be its size. Let $p$ be a prime number and $\pi \in \mathbb{Z}[\sqrt d]$
with $N(\pi) = p$ and $p = \pi\bar\pi$, where $\overline{a + b\sqrt d} = a - b\sqrt d$. If $\pi$
and $\bar\pi$ are prime and $\bar\pi$ is not associated to $\pi$, then $r(p^e) = k(e + 1)$ for
every $e \in \mathbb{N}$. -/
public theorem card_norm_split_pow [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    (hd : d < 0) {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {p e : ℕ} [Fact p.Prime] {π : ℤ√d}
    (hnorm : Zsqrtd.norm π = p) (hprime : Prime π) (hmul : (p : ℤ√d) = π * star π)
    (hπbar_prime : Prime (star π)) (hnassoc : ¬ Associated (star π) π) :
    Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = p ^ e} = k * (e + 1) := by
  have hp : p.Prime := Fact.out
  have hπ0 : π ≠ 0 := hprime.ne_zero
  have hnorm_bar : Zsqrtd.norm (star π) = (p : ℤ) := by
    rw [Zsqrtd.norm_conj, hnorm]
  have hπbar0 : star π ≠ 0 := hπbar_prime.ne_zero
  have hπ_ndvd_bar : ¬ π ∣ star π :=
    fun h => hnassoc (hprime.associated_of_dvd hπbar_prime h).symm
  have hbar_ndvd_pi : ¬ star π ∣ π :=
    fun h => hnassoc (hπbar_prime.associated_of_dvd hprime h)
  have hexists := exists_unit_mul_split_pow hd hnorm hprime hmul hπbar_prime
  -- uniqueness, case j < j'
  have hlt : ∀ (u u' : ℤ√d) (j j' : ℕ), IsUnit u → IsUnit u' →
      j ≤ e → j' ≤ e → j < j' →
      u * π ^ j * star π ^ (e - j) = u' * π ^ j' * star π ^ (e - j') →
      False := by
    intro u u' j j' hu hu' hje hj'e hlt heq
    have hle : j ≤ j' := le_of_lt hlt
    have hj' : π ^ j' = π ^ j * π ^ (j' - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    have he : star π ^ (e - j) = star π ^ (e - j') * star π ^ (j' - j) := by
      have hsub : e - j = (e - j') + (j' - j) := by omega
      rw [hsub, pow_add]
    rw [hj', he] at heq
    have hc0 : π ^ j * star π ^ (e - j') ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hπbar0)
    have hcancel : u * star π ^ (j' - j) = u' * π ^ (j' - j) := by
      apply mul_left_cancel₀ hc0
      linear_combination heq
    have hπdvd : π ∣ u * star π ^ (j' - j) := by
      rw [hcancel]
      have h1le : 1 ≤ j' - j := by omega
      have hpdvd : π ∣ π ^ (j' - j) := by
        have h := pow_dvd_pow π h1le
        rwa [pow_one] at h
      obtain ⟨c, hc⟩ := hpdvd
      exact ⟨u' * c, by rw [hc]; ring⟩
    rcases hprime.dvd_mul.mp hπdvd with h | h
    · have hu1 : u ∣ 1 := isUnit_iff_dvd_one.mp hu
      exact hprime.not_isUnit (isUnit_of_dvd_one (h.trans hu1))
    · exact hπ_ndvd_bar (hprime.dvd_of_dvd_pow h)
  -- uniqueness, case j' < j
  have hgt : ∀ (u u' : ℤ√d) (j j' : ℕ), IsUnit u → IsUnit u' →
      j ≤ e → j' ≤ e → j' < j →
      u * π ^ j * star π ^ (e - j) = u' * π ^ j' * star π ^ (e - j') →
      False := by
    intro u u' j j' hu hu' hje hj'e hlt heq
    have hle : j' ≤ j := le_of_lt hlt
    have hj : π ^ j = π ^ j' * π ^ (j - j') := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    have he : star π ^ (e - j') = star π ^ (e - j) * star π ^ (j - j') := by
      have hsub : e - j' = (e - j) + (j - j') := by omega
      rw [hsub, pow_add]
    rw [hj, he] at heq
    have hc0 : π ^ j' * star π ^ (e - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hπbar0)
    have hcancel : u * π ^ (j - j') = u' * star π ^ (j - j') := by
      apply mul_left_cancel₀ hc0
      linear_combination heq
    have hπdvd : star π ∣ u * π ^ (j - j') := by
      rw [hcancel]
      have h1le : 1 ≤ j - j' := by omega
      have hpdvd : star π ∣ star π ^ (j - j') := by
        have h := pow_dvd_pow (star π) h1le
        rwa [pow_one] at h
      obtain ⟨c, hc⟩ := hpdvd
      exact ⟨u' * c, by rw [hc]; ring⟩
    rcases hπbar_prime.dvd_mul.mp hπdvd with h | h
    · have hu1 : u ∣ 1 := isUnit_iff_dvd_one.mp hu
      exact hπbar_prime.not_isUnit (isUnit_of_dvd_one (h.trans hu1))
    · exact hbar_ndvd_pi (hπbar_prime.dvd_of_dvd_pow h)
  have huniq : ∀ (u u' : ℤ√d) (j j' : ℕ), IsUnit u → IsUnit u' →
      j ≤ e → j' ≤ e →
      u * π ^ j * star π ^ (e - j) = u' * π ^ j' * star π ^ (e - j') →
      j = j' ∧ u = u' := by
    intro u u' j j' hu hu' hje hj'e heq
    have hjeq : j = j' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hlt u u' j j' hu hu' hje hj'e h heq
      · exact hgt u u' j j' hu hu' hje hj'e h heq
    subst hjeq
    refine ⟨rfl, ?_⟩
    have hc0 : π ^ j * star π ^ (e - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hπbar0)
    apply mul_left_cancel₀ hc0
    linear_combination heq
  have hunit : ∀ i, IsUnit (unitVal i) := fun i => IsUnit.of_mul_eq_one _ (hinv i)
  have hnorm_pow : ∀ (x : ℤ√d) (j : ℕ),
      Zsqrtd.norm (x ^ j) = (Zsqrtd.norm x) ^ j := by
    intro x j
    induction j with
    | zero => simp
    | succ n ih => simp [pow_succ', Zsqrtd.norm_mul, ih]
  have hφnorm : ∀ (i : Fin k) (j : Fin (e + 1)),
      (Zsqrtd.norm (unitVal i * π ^ (j : ℕ) * star π ^ (e - (j : ℕ)))).natAbs
        = p ^ e := by
    intro i j
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, Int.natAbs_mul, Int.natAbs_mul]
    have hu1 : (Zsqrtd.norm (unitVal i)).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr (hunit i)
    have hπj : (Zsqrtd.norm (π ^ (j : ℕ))).natAbs = p ^ (j : ℕ) := by
      rw [hnorm_pow, hnorm, Int.natAbs_pow, Int.natAbs_natCast]
    have hπbar : (Zsqrtd.norm (star π ^ (e - (j : ℕ)))).natAbs
        = p ^ (e - (j : ℕ)) := by
      rw [hnorm_pow, hnorm_bar, Int.natAbs_pow, Int.natAbs_natCast]
    rw [hu1, hπj, hπbar, one_mul, ← pow_add]
    congr 1
    exact Nat.add_sub_cancel' (Nat.le_of_lt_succ j.2)
  let phi_map : Fin k × Fin (e + 1) →
      {α : ℤ√d // (Zsqrtd.norm α).natAbs = p ^ e} := fun t =>
    ⟨unitVal t.1 * π ^ (t.2 : ℕ) * star π ^ (e - (t.2 : ℕ)), hφnorm t.1 t.2⟩
  have hbij : Function.Bijective phi_map := by
    constructor
    · intro t t' h
      have hval : unitVal t.1 * π ^ (t.2 : ℕ) * star π ^ (e - (t.2 : ℕ)) =
          unitVal t'.1 * π ^ (t'.2 : ℕ) * star π ^ (e - (t'.2 : ℕ)) :=
        congrArg Subtype.val h
      have hjle : (t.2 : ℕ) ≤ e := Nat.le_of_lt_succ t.2.2
      have hjle' : (t'.2 : ℕ) ≤ e := Nat.le_of_lt_succ t'.2.2
      obtain ⟨hjeq, hueq⟩ :=
        huniq _ _ _ _ (hunit t.1) (hunit t'.1) hjle hjle' hval
      exact Prod.ext (hinj hueq) (Fin.ext hjeq)
    · rintro ⟨α, hα⟩
      obtain ⟨u, hu, j, k, hjk, hαeq⟩ := hexists e α hα
      obtain ⟨i, hiu⟩ := hcomplete u hu
      refine ⟨(i, ⟨j, by omega⟩), ?_⟩
      apply Subtype.ext
      change unitVal i * π ^ j * star π ^ (e - j) = α
      have hk : k = e - j := by omega
      rw [hiu, ← hk]
      exact hαeq.symm
  have hcard := Fintype.card_of_bijective hbij
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  exact hcard.symm

/-- **Norm counts determined by prime powers.** Let $d < 0$ be an integer such that the ring
$\mathbb{Z}[\sqrt d]$ of elements $a + b\sqrt d$ ($a, b \in \mathbb{Z}$) is a unique factorization
domain with exactly $k$ units, and let $N(a + b\sqrt d) = a^2 - db^2$ be the norm. Assume that for
each $n \in \mathbb{N}$ the set of $\alpha \in \mathbb{Z}[\sqrt d]$ with $|N(\alpha)| = n$ is
finite, and let $r(n)$ be its size. Let $D : \mathbb{N} \to \mathbb{Z}$ satisfy $D(1) = 1$ and
$D(mn) = D(m)\,D(n)$ for all coprime $m, n$. If $r(p^e) = k\,D(p^e)$ for every prime $p$ and every
$e \ge 1$, then $r(n) = k\,D(n)$ for every $n \ne 0$. -/
public theorem card_norm_eq_mul_of_prime_pow [IsDomain (ℤ√d)] [UniqueFactorizationMonoid (ℤ√d)]
    [∀ n : ℕ, Fintype {α : ℤ√d // (Zsqrtd.norm α).natAbs = n}]
    (hd : d < 0) {k : ℕ} (unitVal unitValInv : Fin k → ℤ√d)
    (hinv : ∀ i, unitVal i * unitValInv i = 1) (hinj : Function.Injective unitVal)
    (hcomplete : ∀ u : ℤ√d, IsUnit u → ∃ i, unitVal i = u) {D : ℕ → ℤ} (hD1 : D 1 = 1)
    (hDmul : ∀ {m n : ℕ}, Nat.Coprime m n → D (m * n) = D m * D n)
    (hpp : ∀ {p e : ℕ}, p.Prime → 0 < e →
      (Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = p ^ e} : ℤ) = k * D (p ^ e))
    {n : ℕ} (hn : n ≠ 0) :
    (Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = n} : ℤ) = k * D n := by
  have hk0 : (k : ℤ) ≠ 0 := by
    have h1 := card_repr_of_shape unitVal unitValInv hinv hinj hcomplete (1 : ℤ√d)
      (show (Zsqrtd.norm (1 : ℤ√d)).natAbs = 1 by simp) one_ne_zero
      (fun α hα => ⟨α, Zsqrtd.norm_eq_one_iff.mp hα, by simp⟩)
    have hpos : 0 < Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = 1} :=
      Fintype.card_pos_iff.mpr ⟨⟨1, by simp⟩⟩
    omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [card_repr_of_shape unitVal unitValInv hinv hinj hcomplete (1 : ℤ√d)
      (show (Zsqrtd.norm (1 : ℤ√d)).natAbs = 1 by simp) one_ne_zero
      (fun α hα => ⟨α, Zsqrtd.norm_eq_one_iff.mp hα, by simp⟩), hD1, mul_one]
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  set e := n.factorization p with he
  have hepos : 0 < e := hpprime.factorization_pos_of_dvd hn hpdvd
  set m := p ^ e with hm
  obtain ⟨c, hc⟩ : m ∣ n := Nat.ordProj_dvd n p
  have hm0 : m ≠ 0 := pow_ne_zero _ hpprime.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hn (by rw [hc, mul_zero])
  by_cases hc1 : c = 1
  · subst hc1
    rw [mul_one] at hc
    rw [hc]
    exact hpp hpprime hepos
  have hm1 : 1 < m := Nat.one_lt_pow hepos.ne' hpprime.one_lt
  have hcop : Nat.Coprime m c := by
    have hndvd : ¬ p ∣ c := by
      have h := Nat.not_dvd_ordCompl hpprime hn
      rwa [← he, ← hm, hc, Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hm0)] at h
    exact (hpprime.coprime_iff_not_dvd.mpr hndvd).pow_left e
  have hm_lt : m < n := by
    rw [hc]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hm0) (by omega)
  have hc_lt : c < n := by
    rw [hc]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hc0) hm1
  have h := card_mul_of_coprime hd unitVal unitValInv hinv hinj hcomplete hcop hm0 hc0
  have hZ : (Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = m} : ℤ) *
      Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = c}
      = k * Fintype.card {α : ℤ√d // (Zsqrtd.norm α).natAbs = m * c} := by
    exact_mod_cast h
  rw [ih m hm_lt hm0, ih c hc_lt hc0] at hZ
  rw [hc, hDmul hcop]
  apply mul_left_cancel₀ hk0
  rw [← hZ]
  ring

end

end Zsqrtd
