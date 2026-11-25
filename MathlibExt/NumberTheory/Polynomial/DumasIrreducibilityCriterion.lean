/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Use

namespace MetaMathlibExt

@[expose] public section

/-- Scaled ultrametric bound for a finite sum: if every nonzero term `t x`
satisfies `B ≤ n * v (t x)`, and the sum is nonzero, then so does the sum. -/
private lemma dumas_aux_scaled (p : ℕ) [Fact (Nat.Prime p)] (ι : Type*) [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (t : ι → ℚ) (S : Finset ι) (B : ℤ)
    (hS : ∑ x ∈ S, t x ≠ 0)
    (h : ∀ x ∈ S, t x ≠ 0 → B ≤ (n : ℤ) * padicValRat p (t x)) :
    B ≤ (n : ℤ) * padicValRat p (∑ x ∈ S, t x) := by
  have main : ∀ S : Finset ι, (∑ x ∈ S, t x ≠ 0) →
      (∀ x ∈ S, t x ≠ 0 → B ≤ (n : ℤ) * padicValRat p (t x)) →
      B ≤ (n : ℤ) * padicValRat p (∑ x ∈ S, t x) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro hS _
      simp at hS
    | insert a s has ih =>
      intro hS h
      rw [Finset.sum_insert has] at hS ⊢
      by_cases ha : t a = 0
      · rw [ha, zero_add]
        apply ih
        · simpa [ha] using hS
        · intro x hx hxne
          exact h x (Finset.mem_insert_of_mem hx) hxne
      · by_cases hR : ∑ x ∈ s, t x = 0
        · rw [hR, add_zero]
          exact h a (Finset.mem_insert_self a s) ha
        · have h1 : B ≤ (n : ℤ) * padicValRat p (t a) :=
            h a (Finset.mem_insert_self a s) ha
          have h2 : B ≤ (n : ℤ) * padicValRat p (∑ x ∈ s, t x) :=
            ih hR (fun x hx hxne => h x (Finset.mem_insert_of_mem hx) hxne)
          have h3 : min (padicValRat p (t a)) (padicValRat p (∑ x ∈ s, t x)) ≤
              padicValRat p (t a + ∑ x ∈ s, t x) :=
            padicValRat.min_le_padicValRat_add hS
          have hnn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast le_of_lt hn
          rcases le_total (padicValRat p (t a)) (padicValRat p (∑ x ∈ s, t x)) with hle | hle
          · rw [min_eq_left hle] at h3
            calc B ≤ (n : ℤ) * padicValRat p (t a) := h1
            _ ≤ (n : ℤ) * padicValRat p (t a + ∑ x ∈ s, t x) :=
                mul_le_mul_of_nonneg_left h3 hnn
          · rw [min_eq_right hle] at h3
            calc B ≤ (n : ℤ) * padicValRat p (∑ x ∈ s, t x) := h2
            _ ≤ (n : ℤ) * padicValRat p (t a + ∑ x ∈ s, t x) :=
                mul_le_mul_of_nonneg_left h3 hnn
  exact main S hS h

/-- Scaled unique-minimum principle: if `t j0` is the unique Strict minimizer
of the scaled valuation among nonzero terms, the sum is nonzero and attains it. -/
private lemma dumas_aux_eq_scaled (p : ℕ) [Fact (Nat.Prime p)] (ι : Type*) [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (t : ι → ℚ) (S : Finset ι) (j0 : ι)
    (hj0 : j0 ∈ S) (h0 : t j0 ≠ 0)
    (hmin : ∀ x ∈ S, x ≠ j0 → t x ≠ 0 →
      (n : ℤ) * padicValRat p (t j0) < (n : ℤ) * padicValRat p (t x)) :
    (∑ x ∈ S, t x ≠ 0) ∧
      (n : ℤ) * padicValRat p (∑ x ∈ S, t x) = (n : ℤ) * padicValRat p (t j0) := by
  have hsum : ∑ x ∈ S, t x = t j0 + ∑ x ∈ S.erase j0, t x :=
    (Finset.add_sum_erase S t hj0).symm
  by_cases hR : ∑ x ∈ S.erase j0, t x = 0
  · constructor
    · rw [hsum, hR, add_zero]; exact h0
    · rw [hsum, hR, add_zero]
  · have hRbound : (n : ℤ) * padicValRat p (t j0) + 1 ≤
        (n : ℤ) * padicValRat p (∑ x ∈ S.erase j0, t x) := by
      apply dumas_aux_scaled p ι n hn _ _ _ hR
      intro x hx hxne
      have hxS : x ∈ S := Finset.mem_of_mem_erase hx
      have xne : x ≠ j0 := Finset.ne_of_mem_erase hx
      have hlt := hmin x hxS xne hxne
      omega
    have hne : ∑ x ∈ S, t x ≠ 0 := by
      intro hcon
      rw [hsum] at hcon
      have e : t j0 = -(∑ x ∈ S.erase j0, t x) := eq_neg_of_add_eq_zero_left hcon
      have e2 : padicValRat p (t j0) = padicValRat p (∑ x ∈ S.erase j0, t x) := by
        rw [e, padicValRat.neg]
      have e3 : (n : ℤ) * padicValRat p (t j0) =
          (n : ℤ) * padicValRat p (∑ x ∈ S.erase j0, t x) := by rw [e2]
      omega
    have hne' : t j0 + ∑ x ∈ S.erase j0, t x ≠ 0 := by
      rw [← hsum]; exact hne
    have hlt : padicValRat p (t j0) < padicValRat p (∑ x ∈ S.erase j0, t x) := by
      by_contra hc
      push_neg at hc
      have hle : (n : ℤ) * padicValRat p (∑ x ∈ S.erase j0, t x) ≤
          (n : ℤ) * padicValRat p (t j0) :=
        mul_le_mul_of_nonneg_left hc (by exact_mod_cast Nat.zero_le n)
      omega
    refine ⟨hne, ?_⟩
    have heq := padicValRat.add_eq_of_lt hne' h0 hR hlt
    rw [hsum, heq]

/-- Existence of a smallest-index minimizer of `φ` on a nonempty finset. -/
private lemma dumas_minimizer (S : Finset ℕ) (hne : S.Nonempty) (φ : ℕ → ℤ) :
    ∃ j0 ∈ S, (∀ j ∈ S, φ j0 ≤ φ j) ∧ ∀ j ∈ S, φ j = φ j0 → j0 ≤ j := by
  obtain ⟨j1, hj1, hmin⟩ := Finset.exists_min_image S φ hne
  have hmem1 : j1 ∈ S.filter (fun j => φ j = φ j1) :=
    Finset.mem_filter.mpr ⟨hj1, rfl⟩
  set j0 : ℕ := (S.filter (fun j => φ j = φ j1)).min' ⟨j1, hmem1⟩ with hj0def
  have hj0mem : j0 ∈ S.filter (fun j => φ j = φ j1) := Finset.min'_mem _ _
  have hj0val : φ j0 = φ j1 := (Finset.mem_filter.mp hj0mem).2
  refine ⟨j0, Finset.mem_of_mem_filter _ hj0mem, ?_, ?_⟩
  · intro j hj
    have h1 : φ j1 ≤ φ j := hmin j hj
    omega
  · intro j hj hjeq
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj, by omega⟩)

/-- **Dumas irreducibility criterion.** Let $p$ be a prime, write $v_p$ for the $p$-adic
valuation on $\mathbb{Q}$, and let $f = a_0 + a_1 x + \dots + a_n x^n \in \mathbb{Z}[x]$ have
degree $n \ge 1$, with $a_0 \ne 0$ and $a_n \ne 0$. Suppose that no integer $k > 1$ dividing $n$
divides $v_p(a_0) - v_p(a_n)$, that is, $\gcd(v_p(a_0) - v_p(a_n), n) = 1$, and that for every
$0 \le i \le n$ with $a_i \ne 0$,
$n \, v_p(a_i) \ge (n - i) \, v_p(a_0) + i \, v_p(a_n)$.
Then $f$ is irreducible as a polynomial in $\mathbb{Q}[x]$.

Geometrically, the hypotheses say that the Newton polygon of $f$ with respect to $p$ is the single
segment from $(0, v_p(a_0))$ to $(n, v_p(a_n))$ and has no lattice points other than its
endpoints. Zero coefficients contribute no points to the Newton polygon, so the inequality is
required only for nonzero $a_i$.

Source: Randell Heyman, *On the Number of Polynomials of Bounded Height that
Satisfy the Dumas Criterion*, Journal of Integer Sequences 17 (2014), Article
14.2.4, Dumas criterion statement (label `f(x)`), lines 96–102,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Heyman/heyman2.tex>.
Exact algebraic form: Martin Juras, arXiv:1505.07633v1, lines 67–100.
Proves `Wanted` entry `irreducible_of_dumas_padic_criterion`.
-/
theorem irreducible_of_dumas_padic_criterion
  (p : ℕ)
  (hp : Nat.Prime p)
  (f : Polynomial ℤ)
  (hdeg : 0 < f.natDegree)
  (h0 : f.coeff 0 ≠ 0)
  (hlead : f.coeff f.natDegree ≠ 0)
  (hno_int : ∀ k : ℕ, 1 < k → k ∣ f.natDegree →
    ¬ (k : ℤ) ∣ padicValRat p ((f.coeff 0 : ℤ) : ℚ) - padicValRat p ((f.coeff f.natDegree : ℤ) : ℚ))
  (hline : ∀ i : ℕ, i ≤ f.natDegree → f.coeff i ≠ 0 →
    (f.natDegree : ℤ) * padicValRat p ((f.coeff i : ℤ) : ℚ) ≥
      ((f.natDegree - i : ℕ) : ℤ) * padicValRat p ((f.coeff 0 : ℤ) : ℚ) +
        (i : ℤ) * padicValRat p ((f.coeff f.natDegree : ℤ) : ℚ))
  : Irreducible (f.map (Int.castRingHom ℚ)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set n : ℕ := f.natDegree with hn_def
  set fq : Polynomial ℚ := f.map (Int.castRingHom ℚ) with hfq_def
  set v0 : ℤ := padicValRat p ((f.coeff 0 : ℤ) : ℚ) with hv0_def
  set vn : ℤ := padicValRat p ((f.coeff n : ℤ) : ℚ) with hvn_def
  set D : ℤ := vn - v0 with hD_def
  have hcoeff : ∀ i : ℕ, fq.coeff i = ((f.coeff i : ℤ) : ℚ) := by
    intro i
    have h : fq.coeff i = (Int.castRingHom ℚ) (f.coeff i) := by
      rw [hfq_def, Polynomial.coeff_map]
    have h2 : (Int.castRingHom ℚ) (f.coeff i) = ((f.coeff i : ℤ) : ℚ) := rfl
    exact h.trans h2
  have hleadQ : fq.coeff n ≠ 0 := by
    rw [hcoeff n]
    exact_mod_cast hlead
  have hfq_ne : fq ≠ 0 := by
    intro hcon
    rw [hcon] at hleadQ
    simp at hleadQ
  have hnat : fq.natDegree = n := by
    have hle : fq.natDegree ≤ f.natDegree := by
      rw [hfq_def]
      exact Polynomial.natDegree_map_le
    have hge : n ≤ fq.natDegree := Polynomial.le_natDegree_of_ne_zero hleadQ
    omega
  refine ⟨?_, ?_⟩
  · intro hu
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hfq_ne,
      hnat] at hu
    have hn0 : n = 0 := by exact_mod_cast hu
    omega
  · intro G H hGH
    by_cases hG : IsUnit G
    · exact Or.inl hG
    · by_cases hH : IsUnit H
      · exact Or.inr hH
      · exfalso
        have hG0 : G ≠ 0 := by
          intro hcon
          rw [hcon, zero_mul] at hGH
          exact hfq_ne hGH
        have hH0 : H ≠ 0 := by
          intro hcon
          rw [hcon, mul_zero] at hGH
          exact hfq_ne hGH
        have hdeg1 : ∀ P : Polynomial ℚ, P ≠ 0 → ¬ IsUnit P → 1 ≤ P.natDegree := by
          intro P hP0 hPu
          by_contra hc
          push_neg at hc
          have h0 : P.natDegree = 0 := by omega
          have hC : P = Polynomial.C (P.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero h0
          have hcoeff0 : P.coeff 0 = 0 := by
            by_contra hc2
            push_neg at hc2
            have huC : IsUnit (Polynomial.C (P.coeff 0)) :=
              Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc2)
            rw [← hC] at huC
            exact hPu huC
          have hPz : P = 0 := by
            rw [hC, hcoeff0, Polynomial.C_0]
          exact hP0 hPz
        have hr : 1 ≤ G.natDegree := hdeg1 G hG0 hG
        have hs : 1 ≤ H.natDegree := hdeg1 H hH0 hH
        have hrs : G.natDegree + H.natDegree = n := by
          have h1 : (G * H).natDegree = G.natDegree + H.natDegree :=
            Polynomial.natDegree_mul hG0 hH0
          rw [← hGH, hnat] at h1
          exact h1.symm
        have hG0ne : G.coeff 0 ≠ 0 := by
          have hA : fq.coeff 0 ≠ 0 := by
            rw [hcoeff 0]
            exact_mod_cast h0
          rw [hGH, Polynomial.mul_coeff_zero] at hA
          exact (mul_ne_zero_iff.mp hA).1
        have hH0ne : H.coeff 0 ≠ 0 := by
          have hA : fq.coeff 0 ≠ 0 := by
            rw [hcoeff 0]
            exact_mod_cast h0
          rw [hGH, Polynomial.mul_coeff_zero] at hA
          exact (mul_ne_zero_iff.mp hA).2
        have hGrne : G.coeff G.natDegree ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hG0
        have hHsne : H.coeff H.natDegree ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hH0
        have hv0eq : v0 = padicValRat p (G.coeff 0) + padicValRat p (H.coeff 0) := by
          rw [hv0_def, ← hcoeff 0, hGH, Polynomial.mul_coeff_zero]
          exact padicValRat.mul hG0ne hH0ne
        have hvn_eq : vn = padicValRat p (G.coeff G.natDegree) +
            padicValRat p (H.coeff H.natDegree) := by
          have hnn : (G * H).natDegree = n := by
            rw [← hGH, hnat]
          have hlc : (G * H).coeff n =
              G.coeff G.natDegree * H.coeff H.natDegree := by
            have hlm := Polynomial.leadingCoeff_mul G H
            have g1 : G.leadingCoeff = G.coeff G.natDegree := rfl
            have g2 : H.leadingCoeff = H.coeff H.natDegree := rfl
            rw [g1, g2] at hlm
            have e2 : (G * H).coeff (G * H).natDegree = (G * H).coeff n := by
              rw [hnn]
            rw [← e2]
            exact hlm
          rw [hvn_def, ← hcoeff n, hGH, hlc]
          exact padicValRat.mul hGrne hHsne
        obtain ⟨j0, hj0mem, hj0min, hj0small⟩ := dumas_minimizer
          ((Finset.range (G.natDegree + 1)).filter (fun j => G.coeff j ≠ 0))
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), hG0ne⟩⟩
          (fun j => (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D)
        obtain ⟨k0, hk0mem, hk0min, hk0small⟩ := dumas_minimizer
          ((Finset.range (H.natDegree + 1)).filter (fun k => H.coeff k ≠ 0))
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), hH0ne⟩⟩
          (fun k => (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D)
        have hj0le : j0 ≤ G.natDegree := by
          have hmem := hj0mem
          rw [Finset.mem_filter, Finset.mem_range] at hmem
          omega
        have hj0ne : G.coeff j0 ≠ 0 := by
          have hmem := hj0mem
          rw [Finset.mem_filter] at hmem
          exact hmem.2
        have hk0le : k0 ≤ H.natDegree := by
          have hmem := hk0mem
          rw [Finset.mem_filter, Finset.mem_range] at hmem
          omega
        have hk0ne : H.coeff k0 ≠ 0 := by
          have hmem := hk0mem
          rw [Finset.mem_filter] at hmem
          exact hmem.2
        set Vg : ℤ := (n : ℤ) * padicValRat p (G.coeff j0) - (j0 : ℤ) * D with hVg
        set Vh : ℤ := (n : ℤ) * padicValRat p (H.coeff k0) - (k0 : ℤ) * D with hVh
        have hg_le : ∀ j : ℕ, G.coeff j ≠ 0 → j ≤ G.natDegree →
            Vg ≤ (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D := by
          intro j hjne hjle
          have hmem : j ∈ (Finset.range (G.natDegree + 1)).filter
              (fun j => G.coeff j ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjne⟩
          exact hj0min j hmem
        have hh_le : ∀ k : ℕ, H.coeff k ≠ 0 → k ≤ H.natDegree →
            Vh ≤ (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D := by
          intro k hkne hkle
          have hmem : k ∈ (Finset.range (H.natDegree + 1)).filter
              (fun k => H.coeff k ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hkne⟩
          exact hk0min k hmem
        have hg_small : ∀ j : ℕ, G.coeff j ≠ 0 → j ≤ G.natDegree →
            (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D = Vg → j0 ≤ j := by
          intro j hjne hjle hjeq
          have hmem : j ∈ (Finset.range (G.natDegree + 1)).filter
              (fun j => G.coeff j ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjne⟩
          apply hj0small j hmem
          have hjeq2 : (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D =
              (n : ℤ) * padicValRat p (G.coeff j0) - (j0 : ℤ) * D := by
            rw [hVg] at hjeq
            exact hjeq
          exact hjeq2
        have hh_small : ∀ k : ℕ, H.coeff k ≠ 0 → k ≤ H.natDegree →
            (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D = Vh → k0 ≤ k := by
          intro k hkne hkle hkeq
          have hmem : k ∈ (Finset.range (H.natDegree + 1)).filter
              (fun k => H.coeff k ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hkne⟩
          apply hk0small k hmem
          have hkeq2 : (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D =
              (n : ℤ) * padicValRat p (H.coeff k0) - (k0 : ℤ) * D := by
            rw [hVh] at hkeq
            exact hkeq
          exact hkeq2
        have hg_strict : ∀ j : ℕ, G.coeff j ≠ 0 → j ≤ G.natDegree → j < j0 →
            Vg < (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D := by
          intro j hjne hjle hlt
          have hle := hg_le j hjne hjle
          by_contra hc
          push_neg at hc
          have heq : (n : ℤ) * padicValRat p (G.coeff j) - (j : ℤ) * D = Vg := by
            omega
          have hle2 := hg_small j hjne hjle heq
          omega
        have hh_strict : ∀ k : ℕ, H.coeff k ≠ 0 → k ≤ H.natDegree → k < k0 →
            Vh < (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D := by
          intro k hkne hkle hlt
          have hle := hh_le k hkne hkle
          by_contra hc
          push_neg at hc
          have heq : (n : ℤ) * padicValRat p (H.coeff k) - (k : ℤ) * D = Vh := by
            omega
          have hle2 := hh_small k hkne hkle heq
          omega
        have hlower : ∀ i : ℕ, fq.coeff i ≠ 0 →
            Vg + Vh + (i : ℤ) * D ≤ (n : ℤ) * padicValRat p (fq.coeff i) := by
          intro i hi
          have hsum_i : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
              (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x) = (G * H).coeff i :=
            (Polynomial.coeff_mul G H i).symm
          have hSi : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
              (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x) ≠ 0 := by
            have h := hi
            rw [hGH, Polynomial.coeff_mul] at h
            exact h
          have hper : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i,
              (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x ≠ 0 →
              Vg + Vh + (i : ℤ) * D ≤
                (n : ℤ) * padicValRat p
                  ((fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x) := by
            intro x hx hxne
            show Vg + Vh + (i : ℤ) * D ≤
              (n : ℤ) * padicValRat p (G.coeff x.1 * H.coeff x.2)
            have hadd : x.1 + x.2 = i :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp hx
            have htermne : G.coeff x.1 * H.coeff x.2 ≠ 0 := hxne
            obtain ⟨hg, hh⟩ := mul_ne_zero_iff.mp htermne
            have h1 : x.1 ≤ G.natDegree := by
              by_contra hc
              push_neg at hc
              exact hg (Polynomial.coeff_eq_zero_of_natDegree_lt hc)
            have h2 : x.2 ≤ H.natDegree := by
              by_contra hc
              push_neg at hc
              exact hh (Polynomial.coeff_eq_zero_of_natDegree_lt hc)
            have g1 := hg_le x.1 hg h1
            have g2 := hh_le x.2 hh h2
            have haddz : (x.1 : ℤ) + (x.2 : ℤ) = (i : ℤ) := by exact_mod_cast hadd
            have haddD : (x.1 : ℤ) * D + (x.2 : ℤ) * D = (i : ℤ) * D := by
              rw [← add_mul, haddz]
            have hmul : padicValRat p (G.coeff x.1 * H.coeff x.2) =
                padicValRat p (G.coeff x.1) + padicValRat p (H.coeff x.2) :=
              padicValRat.mul hg hh
            rw [hmul, mul_add]
            omega
          have hbound := dumas_aux_scaled p (ℕ × ℕ) n hdeg _ _ _ hSi hper
          rw [hsum_i, ← hGH] at hbound
          exact hbound
        have histar_le : j0 + k0 ≤ n := by omega
        have hmin : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (j0 + k0),
            x ≠ (j0, k0) →
            (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x ≠ 0 →
            (n : ℤ) * padicValRat p
              ((fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) (j0, k0)) <
            (n : ℤ) * padicValRat p
              ((fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x) := by
          intro x hx hxne htermne
          show (n : ℤ) * padicValRat p (G.coeff (j0, k0).1 * H.coeff (j0, k0).2) <
            (n : ℤ) * padicValRat p (G.coeff x.1 * H.coeff x.2)
          have hadd : x.1 + x.2 = j0 + k0 :=
            Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          have htermne' : G.coeff x.1 * H.coeff x.2 ≠ 0 := htermne
          obtain ⟨hg, hh⟩ := mul_ne_zero_iff.mp htermne'
          have h1 : x.1 ≤ G.natDegree := by
            by_contra hc
            push_neg at hc
            exact hg (Polynomial.coeff_eq_zero_of_natDegree_lt hc)
          have h2 : x.2 ≤ H.natDegree := by
            by_contra hc
            push_neg at hc
            exact hh (Polynomial.coeff_eq_zero_of_natDegree_lt hc)
          have hne : x.1 ≠ j0 ∨ x.2 ≠ k0 := by
            by_contra hc
            push_neg at hc
            apply hxne
            exact Prod.ext_iff.mpr hc
          have hmul0 : padicValRat p (G.coeff (j0, k0).1 * H.coeff (j0, k0).2) =
              padicValRat p (G.coeff j0) + padicValRat p (H.coeff k0) :=
            padicValRat.mul hj0ne hk0ne
          have hmulx : padicValRat p (G.coeff x.1 * H.coeff x.2) =
              padicValRat p (G.coeff x.1) + padicValRat p (H.coeff x.2) :=
            padicValRat.mul hg hh
          rw [hmul0, hmulx, mul_add, mul_add]
          have haddz : (x.1 : ℤ) + (x.2 : ℤ) = (j0 : ℤ) + (k0 : ℤ) := by
            exact_mod_cast hadd
          have haddD : (x.1 : ℤ) * D + (x.2 : ℤ) * D =
              (j0 : ℤ) * D + (k0 : ℤ) * D := by
            rw [← add_mul, ← add_mul, haddz]
          rcases hne with hne1 | hne2
          · by_cases hcase : x.1 < j0
            · have g1 := hg_strict x.1 hg h1 hcase
              have g2 := hh_le x.2 hh h2
              omega
            · have hlt2 : x.2 < k0 := by omega
              have g1 := hg_le x.1 hg h1
              have g2 := hh_strict x.2 hh h2 hlt2
              omega
          · by_cases hcase : x.2 < k0
            · have g1 := hg_le x.1 hg h1
              have g2 := hh_strict x.2 hh h2 hcase
              omega
            · have hlt1 : x.1 < j0 := by omega
              have g1 := hg_strict x.1 hg h1 hlt1
              have g2 := hh_le x.2 hh h2
              omega
        have hterm0 : (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) (j0, k0) ≠ 0 :=
          mul_ne_zero_iff.mpr ⟨hj0ne, hk0ne⟩
        have hstar := dumas_aux_eq_scaled p (ℕ × ℕ) n hdeg
          (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2)
          (Finset.HasAntidiagonal.antidiagonal (j0 + k0)) (j0, k0)
          (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl) hterm0 hmin
        obtain ⟨hstar_ne, hstar_eq⟩ := hstar
        have hsum_eq : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (j0 + k0),
            (fun x : ℕ × ℕ => G.coeff x.1 * H.coeff x.2) x) =
            fq.coeff (j0 + k0) := by
          have h := Polynomial.coeff_mul G H (j0 + k0)
          rw [hGH]
          exact h.symm
        have hA : fq.coeff (j0 + k0) ≠ 0 := by
          rw [← hsum_eq]
          exact hstar_ne
        have ha_ne : f.coeff (j0 + k0) ≠ 0 := by
          intro hcon
          apply hA
          rw [hcoeff (j0 + k0), hcon, Int.cast_zero]
        have hval : (n : ℤ) * padicValRat p (fq.coeff (j0 + k0)) =
            Vg + Vh + ((j0 + k0 : ℕ) : ℤ) * D := by
          rw [← hsum_eq, hstar_eq]
          show (n : ℤ) * padicValRat p (G.coeff (j0, k0).1 * H.coeff (j0, k0).2) =
            Vg + Vh + ((j0 + k0 : ℕ) : ℤ) * D
          have hmul0 : padicValRat p (G.coeff (j0, k0).1 * H.coeff (j0, k0).2) =
              padicValRat p (G.coeff j0) + padicValRat p (H.coeff k0) :=
            padicValRat.mul hj0ne hk0ne
          rw [hmul0, mul_add]
          have ecast : ((j0 + k0 : ℕ) : ℤ) = (j0 : ℤ) + (k0 : ℤ) :=
            Nat.cast_add _ _
          rw [ecast, add_mul, hVg, hVh]
          ring
        have hline_inst := hline (j0 + k0) histar_le ha_ne
        rw [← hcoeff (j0 + k0)] at hline_inst
        have hsub : ((n - (j0 + k0) : ℕ) : ℤ) = (n : ℤ) - ((j0 + k0 : ℕ) : ℤ) :=
          Nat.cast_sub histar_le
        rw [hsub, hval] at hline_inst
        have hge : (n : ℤ) * v0 ≤ Vg + Vh := by
          have e1 : ((n : ℤ) - ((j0 + k0 : ℕ) : ℤ)) * v0 =
              (n : ℤ) * v0 - ((j0 + k0 : ℕ) : ℤ) * v0 := sub_mul _ _ _
          have e2 : ((j0 + k0 : ℕ) : ℤ) * vn - ((j0 + k0 : ℕ) : ℤ) * D =
              ((j0 + k0 : ℕ) : ℤ) * v0 := by
            rw [hD_def]; ring
          omega
        have h0val : Vg + Vh ≤ (n : ℤ) * v0 := by
          have hA0 : fq.coeff 0 ≠ 0 := by
            rw [hcoeff 0]
            exact_mod_cast h0
          have h := hlower 0 hA0
          have e0 : padicValRat p (fq.coeff 0) = v0 := by
            rw [hcoeff 0]
          rw [e0, Nat.cast_zero, zero_mul, add_zero] at h
          exact h
        have heq0 : Vg + Vh = (n : ℤ) * v0 := by omega
        have hg0le := hg_le 0 hG0ne (Nat.zero_le _)
        have hh0le := hh_le 0 hH0ne (Nat.zero_le _)
        have hgRle := hg_le G.natDegree hGrne le_rfl
        have hhSle := hh_le H.natDegree hHsne le_rfl
        have hrs_z : ((G.natDegree : ℕ) : ℤ) + ((H.natDegree : ℕ) : ℤ) = (n : ℤ) := by
          exact_mod_cast hrs
        have e00 : ((0 : ℕ) : ℤ) * D = 0 := by simp
        have edist0 : (n : ℤ) * (padicValRat p (G.coeff 0) + padicValRat p (H.coeff 0)) =
            (n : ℤ) * padicValRat p (G.coeff 0) +
            (n : ℤ) * padicValRat p (H.coeff 0) := mul_add _ _ _
        have econg0 : (n : ℤ) * v0 =
            (n : ℤ) * (padicValRat p (G.coeff 0) + padicValRat p (H.coeff 0)) := by
          rw [hv0eq]
        have eg0' : Vg = (n : ℤ) * padicValRat p (G.coeff 0) := by omega
        have eRS : ((G.natDegree : ℕ) : ℤ) * D + ((H.natDegree : ℕ) : ℤ) * D =
            (n : ℤ) * D := by
          rw [← add_mul, hrs_z]
        have edistn : (n : ℤ) * (padicValRat p (G.coeff G.natDegree) +
            padicValRat p (H.coeff H.natDegree)) =
            (n : ℤ) * padicValRat p (G.coeff G.natDegree) +
            (n : ℤ) * padicValRat p (H.coeff H.natDegree) := mul_add _ _ _
        have econgn : (n : ℤ) * vn =
            (n : ℤ) * (padicValRat p (G.coeff G.natDegree) +
              padicValRat p (H.coeff H.natDegree)) := by
          rw [hvn_eq]
        have ev0D : (n : ℤ) * v0 = (n : ℤ) * vn - (n : ℤ) * D := by
          rw [hD_def]; ring
        have egR : Vg = (n : ℤ) * padicValRat p (G.coeff G.natDegree) -
            ((G.natDegree : ℕ) : ℤ) * D := by omega
        have hdiv : (n : ℤ) ∣ ((G.natDegree : ℕ) : ℤ) * D := by
          use padicValRat p (G.coeff G.natDegree) - padicValRat p (G.coeff 0)
          have hsplit : (n : ℤ) * (padicValRat p (G.coeff G.natDegree) -
              padicValRat p (G.coeff 0)) =
              (n : ℤ) * padicValRat p (G.coeff G.natDegree) -
              (n : ℤ) * padicValRat p (G.coeff 0) := mul_sub _ _ _
          omega
        have hcop : Nat.Coprime n D.natAbs := by
          by_contra hc
          have hgne : Nat.gcd n D.natAbs ≠ 1 := fun h => hc h
          have hpos : 0 < Nat.gcd n D.natAbs := by
            by_contra hz
            push_neg at hz
            have hz0 : Nat.gcd n D.natAbs = 0 := by omega
            have h1 := Nat.gcd_dvd_left n D.natAbs
            rw [hz0] at h1
            rw [zero_dvd_iff] at h1
            omega
          have hg1 : 1 < Nat.gcd n D.natAbs := by omega
          have hgdvd : ((Nat.gcd n D.natAbs : ℕ) : ℤ) ∣ D := by
            have h1 : Nat.gcd n D.natAbs ∣ D.natAbs := Nat.gcd_dvd_right n D.natAbs
            have h2 : ((Nat.gcd n D.natAbs : ℕ) : ℤ) ∣ ((D.natAbs : ℕ) : ℤ) := by
              exact_mod_cast h1
            exact Int.dvd_natAbs.mp h2
          have hfin : ((Nat.gcd n D.natAbs : ℕ) : ℤ) ∣ v0 - vn := by
            have h3 : v0 - vn = -D := by
              rw [hD_def]; ring
            rw [h3]
            exact dvd_neg.mpr hgdvd
          exact hno_int _ hg1 (Nat.gcd_dvd_left n D.natAbs) hfin
        have hNr : n ∣ G.natDegree := by
          have h1 : n ∣ G.natDegree * D.natAbs := by
            have h2 : ((n : ℕ) : ℤ) ∣ (((G.natDegree * D.natAbs : ℕ)) : ℤ) := by
              rw [Nat.cast_mul, Int.natCast_natAbs]
              have habs : D ∣ |D| := by
                rcases abs_choice D with h | h
                · rw [h]
                · rw [h]; exact dvd_neg.mpr dvd_rfl
              have h4 : ((G.natDegree : ℕ) : ℤ) * D ∣
                  ((G.natDegree : ℕ) : ℤ) * |D| := mul_dvd_mul_left _ habs
              exact dvd_trans hdiv h4
            exact Int.natCast_dvd_natCast.mp h2
          exact Nat.Coprime.dvd_of_dvd_mul_right hcop h1
        have hle : n ≤ G.natDegree := Nat.le_of_dvd (by omega) hNr
        omega

end
end MetaMathlibExt
