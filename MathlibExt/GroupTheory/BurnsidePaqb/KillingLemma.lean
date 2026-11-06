/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.Norm.Transitivity
public import MathlibExt.GroupTheory.BurnsidePaqb.CentralCharacter
public import MathlibExt.GroupTheory.BurnsidePaqb.CyclotomicField

/-!
Norm/killing stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/KillingLemma.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- **Character value as the sum of characteristic roots.** Let $\rho$ be a representation of a
group $G$ on a finite-dimensional complex vector space, with character $\chi$, and let $g \in G$.
Then $\chi(g)$ is the sum of the roots of the characteristic polynomial of $\rho(g)$, counted
with multiplicity. -/
theorem character_eq_sum_roots {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g = (ρ g).charpoly.roots.sum := by
  change LinearMap.trace ℂ V (ρ g) = _
  exact Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)

omit [Fintype G] in
/-- **Characteristic roots are killed by the order of the element.** Let $G$ be a group, $V$ a
finite-dimensional complex vector space, $\rho$ a representation of $G$ on $V$, and $g \in G$
an element of order $n$, where $n = 0$ if $g$ has infinite order. Then every root $\mu$ of the
characteristic polynomial of $\rho(g)$ satisfies $\mu^n = 1$; in particular, when $g$ has finite
order, $\mu$ is a root of unity. -/
theorem charpoly_root_pow_orderOf {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) (μ : ℂ)
    (hμ : μ ∈ (ρ g).charpoly.roots) : μ ^ orderOf g = 1 := by
  have hne : (ρ g).charpoly ≠ 0 :=
    Polynomial.Monic.ne_zero (LinearMap.charpoly_monic (ρ g))
  have heig : Module.End.HasEigenvalue (ρ g) μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      ((Polynomial.mem_roots hne).mp hμ)
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector heig
  have hpow := Module.End.HasEigenvector.pow_apply hv (orderOf g)
  have hone : (ρ g : Module.End ℂ V) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hone] at hpow
  have h1v : ((1 : Module.End ℂ V)) v = v := rfl
  rw [h1v] at hpow
  have hv0 : v ≠ 0 := hv.2
  have hsub : (μ ^ orderOf g - 1) • v = 0 := by
    rw [sub_smul, ← hpow, one_smul, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

omit [Fintype G] in
/-- **Eigenvalues of a finite group representation have modulus one.** Let $G$ be a finite
group, $V$ a finite-dimensional complex vector space and $\rho$ a representation of $G$ on $V$.
For every $g \in G$, every root $\mu$ of the characteristic polynomial of $\rho(g)$ satisfies
$|\mu| = 1$. -/
theorem charpoly_root_norm_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Finite G] (ρ : Representation ℂ G V) (g : G) (μ : ℂ)
    (hμ : μ ∈ (ρ g).charpoly.roots) : ‖μ‖ = 1 := by
  have hpow := charpoly_root_pow_orderOf ρ g μ hμ
  have hm : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hnorm : ‖μ‖ ^ orderOf g = 1 := by
    rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg μ) hm).mp hnorm

/-- **Real part of a product with a conjugate.** For complex numbers $a$ and $b$,
$\operatorname{Re} a \operatorname{Re} b + \operatorname{Im} a \operatorname{Im} b =
\operatorname{Re}(a \bar{b})$. -/
theorem re_mul_conj (a b : ℂ) :
    a.re * b.re + a.im * b.im = (a * starRingEnd ℂ b).re := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Product of a unit complex number with a conjugate unit.** For complex numbers $a$ and $b$
with $|a| = |b| = 1$, we have $|a \bar{b}| = 1$. -/
theorem norm_mul_conj_eq_one (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a * starRingEnd ℂ b‖ = 1 := by
  rw [norm_mul, ha, Complex.norm_conj, hb, mul_one]

/-- **Cancelling a unit-modulus conjugate.** Let $a, b \in \mathbb{C}$ with $|b| = 1$. If
$a \bar{b} = 1$, then $a = b$. -/
theorem eq_of_mul_conj_eq_one (a b : ℂ) (hb : ‖b‖ = 1)
    (h : a * starRingEnd ℂ b = 1) : a = b := by
  have h2 := congrArg (· * b) h
  rw [mul_assoc, mul_comm (starRingEnd ℂ b) b, Complex.mul_conj] at h2
  have hnsq : Complex.normSq b = 1 := by
    rw [← Complex.sq_norm, hb, one_pow]
  rw [hnsq, Complex.ofReal_one, mul_one, one_mul] at h2
  exact h2

/-- **Real part of a unit complex number other than $1$.** If $w \in \mathbb{C}$ satisfies
$|w| = 1$ and $w \neq 1$, then $\operatorname{Re} w < 1$. -/
theorem re_lt_one_of_ne_one (w : ℂ) (hw : ‖w‖ = 1) (hne : w ≠ 1) :
    w.re < 1 := by
  have hle : w.re ≤ 1 := by
    calc w.re ≤ ‖w‖ := Complex.re_le_norm w
      _ = 1 := hw
  have hne' : w.re ≠ 1 := by
    intro hre1
    apply hne
    have him : w.im = 0 := by
      have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
        rw [pow_two, pow_two, ← Complex.normSq_apply, ← Complex.sq_norm, hw, one_pow]
      rw [hre1, one_pow] at hsq
      have h0 : w.im ^ 2 = 0 := by linarith
      exact sq_eq_zero_iff.mp h0
    rw [Complex.ext_iff]
    exact ⟨hre1, by simp [him]⟩
  exact lt_of_le_of_ne hle hne'

/-- **Strict triangle inequality for unit complex numbers.** Let $\mu_1, \dots, \mu_n$ be complex
numbers with $|\mu_i| = 1$ for every $i$, not all equal. Then
$\left|\sum_{i=1}^{n} \mu_i\right| < n$. -/
theorem abs_sum_roots_of_unity_lt {n : ℕ} (μ : Fin n → ℂ)
    (hmod : ∀ i, ‖μ i‖ = 1) (hne : ∃ i j, μ i ≠ μ j) :
    ‖∑ i, μ i‖ < n := by
  have hexpand : ‖∑ i, μ i‖ ^ 2
      = (∑ i, (μ i).re) * (∑ i, (μ i).re) + (∑ i, (μ i).im) * (∑ i, (μ i).im) := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  have e1 : (∑ i, (μ i).re) * (∑ i, (μ i).re) + (∑ i, (μ i).im) * (∑ i, (μ i).im)
      = ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
        ((μ p.1).re * (μ p.2).re + (μ p.1).im * (μ p.2).im) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [← Finset.sum_add_distrib]
    have hprod : (∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          ((μ p.1).re * (μ p.2).re + (μ p.1).im * (μ p.2).im))
        = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          ((μ i).re * (μ j).re + (μ i).im * (μ j).im) :=
      Finset.sum_product _ _ _
    rw [hprod]
  have e2 : (n : ℝ) ^ 2
      = ∑ _p ∈ ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))), 1 := by
    simp [Finset.sum_const, pow_two]
  have hsq : ‖∑ i, μ i‖ ^ 2 < (n : ℝ) ^ 2 := by
    rw [hexpand, e1, e2]
    refine Finset.sum_lt_sum ?_ ?_
    · intro p _
      change (μ p.1).re * (μ p.2).re + (μ p.1).im * (μ p.2).im ≤ 1
      rw [re_mul_conj]
      calc (μ p.1 * starRingEnd ℂ (μ p.2)).re
          ≤ ‖μ p.1 * starRingEnd ℂ (μ p.2)‖ := Complex.re_le_norm _
        _ = 1 := norm_mul_conj_eq_one _ _ (hmod _) (hmod _)
    · obtain ⟨i, j, hij⟩ := hne
      refine ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩, ?_⟩
      change (μ i).re * (μ j).re + (μ i).im * (μ j).im < 1
      rw [re_mul_conj]
      apply re_lt_one_of_ne_one
      · exact norm_mul_conj_eq_one _ _ (hmod _) (hmod _)
      · intro hw
        exact hij (eq_of_mul_conj_eq_one _ _ (hmod _) hw)
  have hnn : (0 : ℝ) ≤ ‖∑ i, μ i‖ := norm_nonneg _
  have hlt := abs_lt_of_sq_lt_sq hsq (Nat.cast_nonneg n)
  rw [abs_of_nonneg hnn] at hlt
  exact hlt

omit [Fintype G] in
/-- **Character values are algebraic integers.** Let $\rho$ be a representation of a finite group
$G$ on a finite-dimensional complex vector space, with character $\chi$. Then $\chi(g)$ is an
algebraic integer for every $g \in G$.

Each value $\chi(g)$ is a sum of roots of unity. -/
theorem character_isIntegral {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Finite G] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (ρ.character g) := by
  rw [character_eq_sum_roots ρ g]
  refine IsIntegral.multiset_sum (fun μ hμ => ?_)
  apply IsIntegral.of_pow (orderOf_pos g)
  rw [charpoly_root_pow_orderOf ρ g μ hμ]
  exact isIntegral_one

/-- **Integrality of the normalized character value at a coprime class.** Let $G$ be a finite
group, let $\rho$ be an irreducible representation of $G$ on a nonzero finite-dimensional complex
vector space $V$, with character $\chi$, and let $g \in G$. If the size of the conjugacy class of
$g$ is coprime to $\dim V$, then $\chi(g)/\chi(1)$ is an algebraic integer.

Source: Bielefeld Theorem 5, integrality step. -/
theorem charDivDeg_isIntegral_of_coprime {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (g : G)
    (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
    IsIntegral ℤ (ρ.character g / ρ.character 1) := by
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hχ1 : ρ.character 1 = (Module.finrank ℂ V : ℂ) := Representation.char_one ρ
  have hχ1ne : ρ.character 1 ≠ 0 := by
    rw [hχ1]
    exact_mod_cast ne_of_gt hpos
  have hω := classSum_centralScalar_isIntegral ρ g
  have hχ := character_isIntegral ρ g
  obtain ⟨a, b, hab⟩ := hcop.symm.isCoprime
  have habC : (a : ℂ) * Module.finrank ℂ V + (b : ℂ) * (conjClass g).card = 1 := by
    exact_mod_cast hab
  have key : ρ.character g / ρ.character 1
      = (b : ℂ) * ((conjClass g).card * ρ.character g / ρ.character 1)
        + (a : ℂ) * ρ.character g := by
    have e : (b : ℂ) * ((conjClass g).card * ρ.character g / ρ.character 1)
          + (a : ℂ) * ρ.character g
        = ρ.character g * ((a : ℂ) * ρ.character 1 + (b : ℂ) * (conjClass g).card)
          / ρ.character 1 := by
      field_simp
      ring
    have h1 : (a : ℂ) * ρ.character 1 + (b : ℂ) * (conjClass g).card = 1 := by
      rw [hχ1]
      exact habC
    rw [e, h1, mul_one]
  rw [key]
  exact ((isIntegral_intCast b).mul hω).add ((isIntegral_intCast a).mul hχ)

/-- **Sum of two distinct unit complex numbers.** If $a$ and $b$ are distinct complex numbers
with $|a| = |b| = 1$, then $|a + b| < 2$. -/
theorem abs_add_two_ne_unit_lt_two {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hne : a ≠ b) : ‖a + b‖ < 2 := by
  have e : ‖a + b‖ ^ 2 = 2 + 2 * (a * starRingEnd ℂ b).re := by
    have na : a.re ^ 2 + a.im ^ 2 = 1 := by
      have h := congrArg (· ^ 2) ha
      rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
      simpa [pow_two] using h
    have nb : b.re ^ 2 + b.im ^ 2 = 1 := by
      have h := congrArg (· ^ 2) hb
      rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
      simpa [pow_two] using h
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      ← re_mul_conj]
    linear_combination na + nb
  have hre : (a * starRingEnd ℂ b).re < 1 := by
    apply re_lt_one_of_ne_one _ (norm_mul_conj_eq_one _ _ ha hb)
    intro hw
    exact hne (eq_of_mul_conj_eq_one _ _ hb hw)
  have hsq : ‖a + b‖ ^ 2 < (2 : ℝ) ^ 2 := by
    rw [e]
    nlinarith [hre]
  have hnn : (0 : ℝ) ≤ ‖a + b‖ := norm_nonneg _
  have hlt := abs_lt_of_sq_lt_sq hsq (by norm_num)
  rwa [abs_of_nonneg hnn] at hlt

/-- **Strict triangle inequality for unit complex numbers, multiset form.** Let $s$ be a finite
multiset of complex numbers, each of absolute value $1$, containing two distinct elements. Then
the absolute value of the sum of $s$ is strictly less than the number of elements of $s$,
counted with multiplicity. -/
theorem abs_multiset_sum_lt (s : Multiset ℂ) (hunit : ∀ μ ∈ s, ‖μ‖ = 1)
    (hne : ∃ a ∈ s, ∃ b ∈ s, a ≠ b) : ‖s.sum‖ < s.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  have ea : a ::ₘ (s.erase a) = s := Multiset.cons_erase ha
  have hbe : b ∈ s.erase a := (Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb
  have eb : b ::ₘ ((s.erase a).erase b) = s.erase a := Multiset.cons_erase hbe
  set t := (s.erase a).erase b with ht
  rw [← ea, ← eb]
  have hunit' : ∀ μ ∈ a ::ₘ b ::ₘ t, ‖μ‖ = 1 := by
    rw [eb, ea]
    exact hunit
  have ha1 : ‖a‖ = 1 := hunit' a (Multiset.mem_cons_self a _)
  have hb1' : ‖b‖ = 1 :=
    hunit' b (Multiset.mem_cons_of_mem (Multiset.mem_cons_self b t))
  have ht : ∀ μ ∈ t, ‖μ‖ = 1 := fun μ hm =>
    hunit' μ (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm))
  rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons,
    Multiset.card_cons]
  have h1 : ‖a + b‖ < 2 := abs_add_two_ne_unit_lt_two ha1 hb1' hab
  have h2 : ‖t.sum‖ ≤ (t.card : ℝ) := by
    apply (norm_multiset_sum_le t).trans
    simpa using Multiset.sum_le_card_nsmul (t.map fun μ => ‖μ‖) 1 (fun r hr => by
      rw [Multiset.mem_map] at hr
      obtain ⟨μ, hμ, rfl⟩ := hr
      exact (ht μ hμ).le)
  have h3 : ‖a + (b + t.sum)‖ ≤ ‖a + b‖ + ‖t.sum‖ := by
    calc ‖a + (b + t.sum)‖ = ‖(a + b) + t.sum‖ := by rw [add_assoc]
      _ ≤ ‖a + b‖ + ‖t.sum‖ := norm_add_le _ _
  calc ‖a + (b + t.sum)‖ ≤ ‖a + b‖ + ‖t.sum‖ := h3
    _ < 2 + t.card := add_lt_add_of_lt_of_le h1 h2
    _ = (((t.card + 1 + 1 : ℕ)) : ℝ) := by push_cast; ring

omit [Fintype G] in
/-- **Number of characteristic roots of a representation matrix.** Let $G$ be a group, $V$ a
finite-dimensional complex vector space, $\rho$ a representation of $G$ on $V$ and $g \in G$.
The characteristic polynomial of $\rho(g)$ has exactly $\dim_{\mathbb{C}} V$ roots in
$\mathbb{C}$, counted with multiplicity. -/
theorem charpoly_roots_card {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    (ρ g).charpoly.roots.card = Module.finrank ℂ V := by
  have hsplit : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have hcard := hsplit.natDegree_eq_card_roots.symm
  rwa [LinearMap.charpoly_natDegree] at hcard

omit [Fintype G] in
/-- **Characteristic roots are not all equal below the degree.** Let $G$ be a finite group, let
$\rho$ be a representation of $G$ on a nonzero finite-dimensional complex vector space $V$, with
character $\chi$, and let $g \in G$. If $|\chi(g)| < \dim V$, then the characteristic polynomial
of $\rho(g)$ has two distinct roots. -/
theorem char_roots_not_all_equal {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] [Finite G] (ρ : Representation ℂ G V) (g : G)
    (hlt : ‖ρ.character g‖ < Module.finrank ℂ V) :
    ∃ a ∈ (ρ g).charpoly.roots, ∃ b ∈ (ρ g).charpoly.roots, a ≠ b := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hcard := charpoly_roots_card ρ g
  have hne0 : (ρ g).charpoly.roots ≠ 0 := by
    intro hz
    rw [hz] at hcard
    simp at hcard
    omega
  obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero hne0
  have hall : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀ := fun μ hμ => hcon μ hμ μ₀ hμ₀
  have hsum : (ρ g).charpoly.roots.sum
      = (ρ g).charpoly.roots.card • μ₀ := by
    rw [Multiset.eq_replicate_card.mpr hall, Multiset.sum_replicate, Multiset.card_replicate]
  have hχ : ρ.character g = (ρ g).charpoly.roots.card • μ₀ := by
    rw [character_eq_sum_roots, hsum]
  have hμunit : ‖μ₀‖ = 1 := charpoly_root_norm_eq_one ρ g μ₀ hμ₀
  rw [hχ, hcard, nsmul_eq_mul, norm_mul, hμunit, Complex.norm_natCast,
    mul_one] at hlt
  exact lt_irrefl _ hlt

omit [Fintype G] in
/-- **Character values lie in a cyclotomic field.** Let $\rho$ be a representation of a group $G$
on a finite-dimensional complex vector space, with character $\chi$, and let $g \in G$ have
finite order $m$. Then $\chi(g)$ lies in the subfield of $\mathbb{C}$ generated over $\mathbb{Q}$
by the $m$-th roots of unity. -/
theorem char_mem_cycSubfield {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G)
    (hm : orderOf g ≠ 0) : ρ.character g ∈ cycSubfield (orderOf g) := by
  rw [character_eq_sum_roots ρ g]
  exact IntermediateField.multiset_sum_mem _ _ (fun μ hμ =>
    mem_cycSubfield_of_pow_eq_one _ hm μ
      (charpoly_root_pow_orderOf ρ g μ hμ))

/-- **Characteristic roots as elements of the cyclotomic field.** Let $m$ be a positive integer,
let $\rho$ be a representation of a finite group $G$ on a finite-dimensional complex vector
space $V$, and let $g \in G$ be such that every root $\mu$ of the characteristic polynomial of
$\rho(g)$ satisfies $\mu^m = 1$. Each such root $\mu$ is regarded as an element of the subfield
$K \subseteq \mathbb{C}$ obtained by adjoining the $m$-th roots of unity to $\mathbb{Q}$. -/
noncomputable def conjRootElem (m : ℕ) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (hmg : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ m = 1)
    (x : { μ : ℂ // μ ∈ (ρ g).charpoly.roots }) : cycSubfield m :=
  ⟨x.1, mem_cycSubfield_of_pow_eq_one m hm x.1 (hmg x.1 x.2)⟩

omit [Fintype G] in
/-- **Field embeddings applied to character values.** Let $G$ be a group, $\rho$ a
representation of $G$ on a finite-dimensional complex vector space $V$ with character $\chi$,
let $m$ be a positive integer, and let $g \in G$ be such that every root $\mu$ of the
characteristic polynomial of $\rho(g)$ satisfies $\mu^m = 1$. Let $K \subseteq \mathbb{C}$ be the
field obtained by adjoining the $m$-th roots of unity to $\mathbb{Q}$, and suppose
$\chi(g) \in K$. Then for every $\mathbb{Q}$-algebra homomorphism $\sigma : K \to \mathbb{C}$ we
have $\sigma(\chi(g)) = \sum_\mu \sigma(\mu)$, where the sum runs over the roots $\mu$ of the
characteristic polynomial of $\rho(g)$, counted with multiplicity, each regarded as an element
of $K$. -/
theorem embedding_char_eq_conj_sum (m : ℕ) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (hmg : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ m = 1)
    (hχ : ρ.character g ∈ cycSubfield m)
    (σ : cycSubfield m →ₐ[ℚ] ℂ) :
    σ ⟨ρ.character g, hχ⟩
      = (((ρ g).charpoly.roots.attach.map
        (fun x => σ (conjRootElem m hm ρ g hmg x))).sum) := by
  have hsum : (cycSubfield m).val
        (((ρ g).charpoly.roots.attach.map (conjRootElem m hm ρ g hmg)).sum)
      = ρ.character g := by
    rw [map_multiset_sum]
    have hmap : (((ρ g).charpoly.roots.attach.map
            (conjRootElem m hm ρ g hmg)).map ⇑(cycSubfield m).val)
        = (ρ g).charpoly.roots.attach.map Subtype.val := by
      rw [Multiset.map_map]
      have hcomp : (⇑(cycSubfield m).val ∘ conjRootElem m hm ρ g hmg)
          = Subtype.val := by
        ext x
        exact IntermediateField.val_mk _ _
      rw [hcomp]
    rw [hmap, Multiset.attach_map_val]
    exact (character_eq_sum_roots ρ g).symm
  have key : (⟨ρ.character g, hχ⟩ : cycSubfield m)
      = (((ρ g).charpoly.roots.attach.map
        (conjRootElem m hm ρ g hmg)).sum) := by
    apply Subtype.ext
    change ρ.character g = (((ρ g).charpoly.roots.attach.map
      (conjRootElem m hm ρ g hmg)).sum : cycSubfield m).val
    rw [← hsum]
    rfl
  rw [key, map_multiset_sum, Multiset.map_map]
  rfl

/-- **Character vanishing from coprimality and a strict norm bound.** Let $G$ be a finite group,
let $\rho$ be an irreducible representation of $G$ on a nonzero finite-dimensional complex vector
space $V$, with character $\chi$, and let $g \in G$. If the size of the conjugacy class of $g$ is
coprime to $\dim V$ and $|\chi(g)| < \dim V$, then $\chi(g) = 0$.

Source: Bielefeld Theorem 5, norm step. -/
theorem char_eq_zero_of_coprime_of_norm_lt {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (g : G)
    (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V))
    (hlt : ‖ρ.character g‖ < Module.finrank ℂ V) :
    ρ.character g = 0 := by
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hm : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hχ1 : ρ.character 1 = (Module.finrank ℂ V : ℂ) := Representation.char_one ρ
  have hdCne : ((Module.finrank ℂ V : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  set m := orderOf g with hmdef
  set K := cycSubfield m with hKdef
  have : IsScalarTower ℤ ℚ K := IsScalarTower.of_algebraMap_eq fun x => by simp
  have : IsScalarTower ℤ K ℂ := IsScalarTower.of_algebraMap_eq fun x => by simp
  have : Algebra.IsSeparable ℚ K := (isGalois_iff.mp inferInstance).1
  have hχmem : ρ.character g ∈ K := char_mem_cycSubfield ρ g hm
  have hdKne : ((Module.finrank ℂ V : ℕ) : K) ≠ 0 := by
    intro hz
    apply hdCne
    have h2 := congrArg (fun z : K => (z : ℂ)) hz
    simpa using h2
  set α : K := ⟨ρ.character g, hχmem⟩ / (Module.finrank ℂ V : K) with hαdef
  have hαC : (α : ℂ) = ρ.character g / ρ.character 1 := by
    have e : K.val α = ρ.character g / ρ.character 1 := by
      rw [hαdef, map_div₀ _ _ _, IntermediateField.val_mk, map_natCast, hχ1]
    simpa using e
  have hαint : IsIntegral ℤ α := by
    have hαintC : IsIntegral ℤ (α : ℂ) := by
      rw [hαC]
      exact charDivDeg_isIntegral_of_coprime ρ g hcop
    have hiff := isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ) (x := α)
    rw [IntermediateField.algebraMap_apply] at hiff
    exact hiff.mp hαintC
  set N : ℚ := Algebra.norm ℚ α with hNdef
  have hNint : IsIntegral ℤ N := Algebra.isIntegral_norm ℚ hαint
  have hNprod : algebraMap ℚ ℂ N = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hmg : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ m = 1 :=
    fun μ hμ => charpoly_root_pow_orderOf ρ g μ hμ
  have hle : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ≤ 1 := by
    intro σ
    have hσd : σ (Module.finrank ℂ V : K) = (Module.finrank ℂ V : ℂ) :=
      map_natCast σ _
    have hσα : σ α = (((ρ g).charpoly.roots.attach.map
            (fun x => σ (conjRootElem m hm ρ g hmg x))).sum)
          / (Module.finrank ℂ V : ℂ) := by
      rw [hαdef, map_div₀ _ _ _, hσd]
      congr 1
      exact embedding_char_eq_conj_sum m hm ρ g hmg hχmem σ
    have hcard : (((ρ g).charpoly.roots.attach.map
            (fun x => σ (conjRootElem m hm ρ g hmg x))).card)
        = Module.finrank ℂ V := by
      rw [Multiset.card_map, Multiset.card_attach, charpoly_roots_card]
    have hunit : ∀ w ∈ ((ρ g).charpoly.roots.attach.map
          (fun x => σ (conjRootElem m hm ρ g hmg x))), ‖w‖ = 1 := by
      intro w hw
      rw [Multiset.mem_map] at hw
      obtain ⟨x, _, rfl⟩ := hw
      refine Complex.norm_eq_one_of_pow_eq_one ?_ hm
      rw [← map_pow]
      have hx : ((conjRootElem m hm ρ g hmg x) ^ m : K) = 1 := by
        rw [Subtype.ext_iff]
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        change x.1 ^ m = 1
        exact hmg x.1 x.2
      rw [hx, map_one]
    have hle2 : ‖(((ρ g).charpoly.roots.attach.map
            (fun x => σ (conjRootElem m hm ρ g hmg x))).sum)‖
        ≤ (Module.finrank ℂ V : ℝ) := by
      have h := (norm_multiset_sum_le _).trans
        (Multiset.sum_le_card_nsmul
          (((ρ g).charpoly.roots.attach.map
            (fun x => σ (conjRootElem m hm ρ g hmg x))).map fun w => ‖w‖) 1
          (fun r hr => by
            rw [Multiset.mem_map] at hr
            obtain ⟨w, hw, rfl⟩ := hr
            exact (hunit w hw).le))
      simpa only [Multiset.card_map, hcard, nsmul_eq_mul, mul_one] using h
    rw [hσα, norm_div, Complex.norm_natCast]
    exact div_le_one_of_le₀ hle2 (Nat.cast_nonneg _)
  have hσ0 : ‖K.val α‖ < 1 := by
    have e : K.val α = (α : ℂ) := rfl
    rw [e, hαC, norm_div, hχ1, Complex.norm_natCast,
      div_lt_one (Nat.cast_pos.mpr hpos)]
    exact hlt
  have hprod : ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖ < 1 := by
    have hleNN : ∀ σ ∈ (Finset.univ : Finset (K →ₐ[ℚ] ℂ)), ‖σ α‖₊ ≤ 1 :=
      fun σ _ => by exact_mod_cast hle σ
    have hltNN : ∃ σ ∈ (Finset.univ : Finset (K →ₐ[ℚ] ℂ)), ‖σ α‖₊ < 1 :=
      ⟨K.val, Finset.mem_univ _, by exact_mod_cast hσ0⟩
    have hNN : ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖₊ < 1 := by
      rw [nnnorm_prod]
      exact (Finset.prod_lt_one_iff_of_le_one hleNN).mpr hltNN
    exact_mod_cast hNN
  have hNlt : |N| < 1 := by
    have h1 : ‖algebraMap ℚ ℂ N‖ < 1 := by rw [hNprod]; exact hprod
    rw [eq_ratCast] at h1
    rw [Complex.norm_ratCast, ← Rat.cast_abs] at h1
    exact_mod_cast h1
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hNint
  have hcast : (n : ℚ) = N := by simpa using hn
  have hn0 : n = 0 := by
    have h3 : |(n : ℚ)| < 1 := by rw [hcast]; exact hNlt
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h3
    exact Int.abs_lt_one_iff.mp h3
  have hNeq : N = 0 := by rw [← hcast, hn0, Int.cast_zero]
  have hprod0 : ∏ σ : K →ₐ[ℚ] ℂ, σ α = 0 := by
    rw [← hNprod, hNeq, map_zero]
  obtain ⟨σ, -, hσ0⟩ := Finset.prod_eq_zero_iff.mp hprod0
  have hα0 : α = 0 :=
    not_ne_iff.mp (fun hne => (map_ne_zero σ).mpr hne hσ0)
  have hχ0 : (α : ℂ) = 0 := by rw [hα0]; rfl
  rw [hαC] at hχ0
  have hχ1ne : ρ.character 1 ≠ 0 := by
    rw [hχ1]; exact_mod_cast ne_of_gt hpos
  rcases div_eq_zero_iff.mp hχ0 with h | h
  · exact h
  · exact absurd h hχ1ne

/-- **Burnside's vanishing theorem for coprime class sizes.** Let $G$ be a finite group, let
$\rho$ be an irreducible representation of $G$ on a nonzero finite-dimensional complex vector
space $V$, with character $\chi$, and let $g \in G$. If the size of the conjugacy class of $g$
is coprime to $\dim V$, then $|\chi(g)| = \dim V$ or $\chi(g) = 0$.

Since $\chi(1) = \dim V$, the first alternative says that $g$ lies in the center $Z(\chi)$ of
$\chi$, the set of $h \in G$ with $|\chi(h)| = \chi(1)$.

Source: Bielefeld Theorem 5. -/
theorem burnside_coprime_vanish {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (g : G)
    (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
    ‖ρ.character g‖ = Module.finrank ℂ V ∨ ρ.character g = 0 := by
  have hle : ‖ρ.character g‖ ≤ Module.finrank ℂ V := by
    rw [character_eq_sum_roots]
    refine (norm_multiset_sum_le (ρ g).charpoly.roots).trans ?_
    simpa only [Multiset.card_map, charpoly_roots_card, nsmul_eq_mul, mul_one] using
      Multiset.sum_le_card_nsmul ((ρ g).charpoly.roots.map fun μ => ‖μ‖) 1
        (fun r hr => by
          rw [Multiset.mem_map] at hr
          obtain ⟨μ, hμ, rfl⟩ := hr
          exact (charpoly_root_norm_eq_one ρ g μ hμ).le)
  by_cases h : ‖ρ.character g‖ = Module.finrank ℂ V
  · exact Or.inl h
  · exact Or.inr (char_eq_zero_of_coprime_of_norm_lt ρ g hcop
      (lt_of_le_of_ne hle h))

end

end BurnsidePaqb
