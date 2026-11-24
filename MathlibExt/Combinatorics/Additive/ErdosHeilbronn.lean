/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Nullstellensatz
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# The Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune theorem)

For a prime `p` and a nonempty `A ⊆ ℤ_p`, the sums `a + a'` of two distinct elements of `A` take at
least `min(p, 2|A| - 3)` values. Erdős and Heilbronn conjectured this; Dias da Silva and Hamidoune
proved it (for `h`-fold sums of distinct elements in general, stated as the wanted
`MetaMathlibExt.dias_da_silva_hamidoune`; this file proves its case `h = 2`), and Alon, Nathanson
and Ruzsa found the polynomial proof presented in N. Alon,
"Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999), Section 4, which is the proof
formalized here.

## Proof

Reduce to `2|A| - 3 ≤ p` by passing to a subset. If the restricted sumset had at most
`m = 2|A| - 4` elements, put it inside a set `C` of exactly `m` elements and consider
`Q = (x₁ - x₀) ∏_{c ∈ C} (x₀ + x₁ - c)`, which vanishes on `A × (A \ {a})`. Its total degree is
`m + 1 = (|A| - 1) + (|A| - 2)`, and the coefficient of `x₀^{|A|-1} x₁^{|A|-2}` is that of
`(x₁ - x₀)(x₀ + x₁)^m`, namely `C(m, |A|-1) - C(m, |A|-2)`, which is a nonzero multiple of a
Catalan number and is not divisible by `p` because `m < p`. The Combinatorial Nullstellensatz
(Mathlib's `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`) gives a contradiction.
-/

@[expose] public section

open Finset MvPolynomial

namespace MathlibExt.Combinatorics.Additive.ErdosHeilbronn

/-- A sum of two distinct elements of `A` lies in the restricted sumset `2^∧ A`
(`MetaMathlibExt.restrictedSumset 2 A`). -/
private theorem add_mem_restrictedSumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} {a b : G} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    a + b ∈ MetaMathlibExt.restrictedSumset 2 A := by
  unfold MetaMathlibExt.restrictedSumset
  refine mem_image.2 ⟨{a, b}, mem_powersetCard.2 ⟨?_, card_pair hab⟩, sum_pair hab⟩
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

private theorem restrictedSumset_mono {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A B : Finset G} (h : A ⊆ B) :
    MetaMathlibExt.restrictedSumset 2 A ⊆ MetaMathlibExt.restrictedSumset 2 B := by
  unfold MetaMathlibExt.restrictedSumset
  exact image_subset_image (powersetCard_mono h)

section Coefficients

variable {R : Type*} [CommRing R]

private theorem single_add_single_eq_iff (a b c d : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b = Finsupp.single 0 c + Finsupp.single 1 d)
      ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem coeff_add_pow (m a b : ℕ) :
    ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ m).coeff
        (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b)
      = if a + b = m then (m.choose a : R) else 0 := by
  rw [add_pow, coeff_sum]
  have hterm : ∀ k ∈ range (m + 1),
      ((X 0 : MvPolynomial (Fin 2) R) ^ k * X 1 ^ (m - k) *
        (m.choose k : MvPolynomial (Fin 2) R)).coeff
          (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b)
        = if k = a ∧ m - k = b then (m.choose k : R) else 0 := by
    intro k _
    rw [show ((m.choose k : ℕ) : MvPolynomial (Fin 2) R) = C (m.choose k : R) from
      (map_natCast C _).symm]
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_comm, C_mul_monomial,
      coeff_monomial]
    simp only [mul_one]
    by_cases h : k = a ∧ m - k = b
    · rw [ite_eq_left ((single_add_single_eq_iff _ _ _ _).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((single_add_single_eq_iff _ _ _ _).1 h')), ite_eq_right h]
  rw [Finset.sum_congr rfl hterm]
  by_cases hab : a + b = m
  · rw [ite_eq_left hab, Finset.sum_eq_single a]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro k _ hk; rw [ite_eq_right (fun h => hk h.1)]
    · intro ha; exfalso; exact ha (mem_range.2 (by omega))
  · rw [ite_eq_right hab]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ite_eq_right]
    rintro ⟨rfl, h2⟩
    simp at hk
    omega

/-- The coefficient of `x₀^{n-1} x₁^{n-2}` in `(x₁ - x₀)(x₀ + x₁)^{2n-4}`. -/
private theorem coeff_main (n : ℕ) (hn : 2 ≤ n) :
 ((X 1 - X 0 : MvPolynomial (Fin 2) R) * (X 0 + X 1) ^ (2 * n - 4)).coeff
      (Finsupp.single (0 : Fin 2) (n - 1) + Finsupp.single 1 (n - 2))
      = ((2 * n - 4).choose (n - 1) : R) - ((2 * n - 4).choose (n - 2) : R) := by
  classical
  rw [sub_mul, coeff_sub, coeff_X_mul', coeff_X_mul']
  congr 1
  · by_cases h3 : 3 ≤ n
    · rw [ite_eq_left (by simp; omega)]
      have : Finsupp.single (0 : Fin 2) (n - 1) + Finsupp.single 1 (n - 2) - Finsupp.single 1 1
          = Finsupp.single 0 (n - 1) + Finsupp.single 1 (n - 3) := by
        ext i; fin_cases i <;> simp; omega
      rw [this, coeff_add_pow, ite_eq_left (by omega)]
    · have hn2 : n = 2 := by omega
      subst hn2
      rw [ite_eq_right (by simp)]
      simp
  · rw [ite_eq_left (by simp; omega)]
    have : Finsupp.single (0 : Fin 2) (n - 1) + Finsupp.single 1 (n - 2) - Finsupp.single 0 1
        = Finsupp.single 0 (n - 2) + Finsupp.single 1 (n - 2) := by
      ext i; fin_cases i <;> simp; omega
    rw [this, coeff_add_pow, ite_eq_left (by omega)]

end Coefficients

/-- The difference of consecutive central binomial coefficients is not divisible by a prime
`p > 2k`: `(k + 1) (C(2k, k+1) - C(2k, k)) = -C(2k, k)`. -/
private theorem choose_sub_ne_zero {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : 2 * k < p) :
    (((2 * k).choose (k + 1) : ℕ) : ZMod p) - (((2 * k).choose k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hid : (2 * k).choose (k + 1) * (k + 1) = (2 * k).choose k * k := by
    have := Nat.choose_succ_right_eq (2 * k) k
    rw [this]; congr 1; omega
  have hcast := congrArg (Nat.cast : ℕ → ZMod p) hid
  push_cast at hcast
  rw [sub_eq_zero.1 h] at hcast
  have h0 : (((2 * k).choose k : ℕ) : ZMod p) = 0 := by linear_combination hcast
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hfac : p ∣ (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [← this]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h0 _) _
  have hpP : p.Prime := Fact.out
  rw [Nat.Prime.dvd_factorial hpP] at hfac
  omega

/-- **Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune theorem).** If `p` is a prime and `A` a
nonempty subset of `ℤ_p`, then the restricted sumset `2^∧ A = {a + a' : a, a' ∈ A, a ≠ a'}`
(`MetaMathlibExt.restrictedSumset 2 A`) satisfies `|2^∧ A| ≥ min(p, 2|A| - 3)` (N. Alon,
"Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999), Theorem 4.3, attributed there
to J. A. Dias da Silva and Y. O. Hamidoune, Bull. London Math. Soc. 26 (1994); the proof is the
paper's, through its Theorem 4.1 with `k = 1` and `h = x₁ - x₀`). Natural-number subtraction makes
the bound `0` when `|A| = 1`, where the paper's `2|A| - 3` is negative. -/
theorem min_le_card_restrictedSumset {p : ℕ} (hp : p.Prime) {A : Finset (ZMod p)}
    (hA : A.Nonempty) : min p (2 * A.card - 3) ≤ (MetaMathlibExt.restrictedSumset 2 A).card := by
  have := Fact.mk hp
  -- Reduction to `2|A| - 3 ≤ p`.
  suffices key : ∀ B : Finset (ZMod p), 2 ≤ B.card → 2 * B.card - 3 ≤ p →
      2 * B.card - 3 ≤ (MetaMathlibExt.restrictedSumset 2 B).card by
    rcases Nat.lt_or_ge A.card 2 with h1 | h2
    · have : 2 * A.card - 3 = 0 := by omega
      simp [this]
    by_cases hle : 2 * A.card - 3 ≤ p
    · exact (min_le_right _ _).trans (key A h2 hle)
    · -- pass to a subset `B ⊆ A` with `2|B| - 3 = p` (here `p` is odd since `p ≥ 2|A| - 2 ≥ 2`).
      push Not at hle
      have hp2 : p ≠ 2 := by
        intro h; subst h
        have := Finset.card_le_univ A
        simp at this
        omega
      have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hp2
      obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (n := (p + 3) / 2)
        (by omega)
      have hB := key B (by omega) (by omega)
      calc min p (2 * A.card - 3) ≤ p := min_le_left _ _
        _ = 2 * B.card - 3 := by omega
        _ ≤ (MetaMathlibExt.restrictedSumset 2 B).card := hB
        _ ≤ (MetaMathlibExt.restrictedSumset 2 A).card := card_le_card (restrictedSumset_mono hBA)
  intro B hB2 hBp
  by_contra hlt
  push Not at hlt
  set n := B.card with hn
  set m := 2 * n - 4 with hm
  -- A set `C ⊇ 2^∧ B` of exactly `m` elements.
  have hmp : m ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  obtain ⟨C, hSC, hCcard⟩ :=
    Finset.exists_superset_card_eq (s := MetaMathlibExt.restrictedSumset 2 B) (n := m)
      (by omega) hmp
  obtain ⟨a, ha⟩ : B.Nonempty := by rw [← card_pos]; omega
  set S : Fin 2 → Finset (ZMod p) := ![B, B.erase a] with hS
  set Q : MvPolynomial (Fin 2) (ZMod p) :=
    (X 1 - X 0) * ∏ c ∈ C, (X 0 + X 1 - MvPolynomial.C c) with hQ
  set t : Fin 2 →₀ ℕ := Finsupp.single 0 (n - 1) + Finsupp.single 1 (n - 2) with ht
  have htdeg : t.degree = m + 1 := by
    simp only [ht, Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.add_apply,
      Finsupp.single_apply]
    simp; omega
  -- `Q` vanishes on `B × (B \ {a})`.
  have hvanish : ∀ s : Fin 2 → ZMod p, (∀ i, s i ∈ S i) → eval s Q = 0 := by
    intro s hs
    have h0 : s 0 ∈ B := by simpa [hS] using hs 0
    have h1 : s 1 ∈ B := by simpa [hS] using (Finset.mem_erase.1 (by simpa [hS] using hs 1)).2
    simp only [hQ, map_mul, map_sub, map_prod, map_add, eval_X, eval_C]
    by_cases heq : s 0 = s 1
    · rw [heq, sub_self, zero_mul]
    · rw [Finset.prod_eq_zero (hSC (add_mem_restrictedSumset h0 h1 heq)) (sub_self _), mul_zero]
  -- The coefficient of `t` in `Q`.
  have hcoeff : Q.coeff t = ((2 * n - 4).choose (n - 1) : ZMod p) -
      ((2 * n - 4).choose (n - 2) : ZMod p) := by
    -- `∏ (s - c) = s^m + R` with `deg R < m` (or `R = 0`), via the monic polynomial `∏ (Y - c)`.
    set g : Polynomial (ZMod p) := ∏ c ∈ C, (Polynomial.X - Polynomial.C c) with hg
    have hgmon : g.Monic := Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C c
    have hgdeg : g.natDegree = m := by
      rw [hg, Polynomial.natDegree_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C c]
      simp [hCcard]
    set h := g - Polynomial.X ^ m with hh
    have haeval : ∏ c ∈ C, (X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) (ZMod p)) =
        (X 0 + X 1) ^ m + Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) h := by
      rw [hh, map_sub, map_pow, Polynomial.aeval_X, add_sub_cancel, hg, map_prod]
      refine Finset.prod_congr rfl fun c _ => ?_
      simp [Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hdegR : (Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) h).totalDegree
        ≤ h.natDegree := by
      rw [Polynomial.aeval_eq_sum_range]
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
      rw [Finset.mem_range] at hi
      refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
      have : (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
        (totalDegree_add _ _).trans (by simp [totalDegree_X])
      calc i * (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ i * 1 :=
            Nat.mul_le_mul_left _ this
        _ ≤ h.natDegree := by omega
    have hzero : ((X 1 - X 0) *
        Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) h).coeff t = 0 := by
      by_cases h0 : h = 0
      · rw [h0, map_zero, mul_zero]; rfl
      have hm0 : m ≠ 0 := by
        intro hm0
        apply h0
        have hC0 : C = ∅ := by rw [← card_eq_zero]; omega
        rw [hh, hm0, pow_zero, hg, hC0, prod_empty, sub_self]
      have hlt : h.natDegree < m := by
        have hdeg : h.degree < g.degree := by
          refine Polynomial.degree_sub_lt_left ?_ hgmon.ne_zero ?_
          · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hgmon.ne_zero, hgdeg]
          · rw [hgmon.leadingCoeff, Polynomial.leadingCoeff_X_pow]
        rw [Polynomial.degree_eq_natDegree hgmon.ne_zero, hgdeg] at hdeg
        exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg
      apply coeff_eq_zero_of_totalDegree_lt
      have h1 : (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
        (totalDegree_sub _ _).trans (by simp [totalDegree_X])
      have : t.degree = ∑ i ∈ t.support, t i := rfl
      rw [← this, htdeg]
      calc ((X 1 - X 0) *
            Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) h).totalDegree
          ≤ (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)).totalDegree +
            (Polynomial.aeval (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod p)) h).totalDegree :=
            totalDegree_mul _ _
        _ < m + 1 := by omega
    rw [hQ, haeval, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hzero, add_zero]
    exact coeff_main (R := ZMod p) n hB2
  have hcoeff_ne : Q.coeff t ≠ 0 := by
    rw [hcoeff]
    have := choose_sub_ne_zero (p := p) (n - 2) (by omega)
    rwa [show 2 * (n - 2) = 2 * n - 4 by omega, show n - 2 + 1 = n - 1 by omega] at this
  have htot : Q.totalDegree = t.degree := by
    refine le_antisymm ?_ ?_
    · rw [htdeg, hQ]
      refine (totalDegree_mul _ _).trans ?_
      have h1 : (X 1 - X 0 : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
        (totalDegree_sub _ _).trans (by simp [totalDegree_X])
      have h2 : (∏ c ∈ C,
          (X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) (ZMod p))).totalDegree ≤ m := by
        refine (totalDegree_finsetProd _ _).trans ?_
        calc ∑ c ∈ C, (X 0 + X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) (ZMod p)).totalDegree
            ≤ ∑ _c ∈ C, 1 := Finset.sum_le_sum fun c _ =>
              (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans
                (by simp [totalDegree_X])) (by simp [totalDegree_C]))
          _ = m := by simp [hCcard]
      omega
    · have : t.degree = ∑ i ∈ t.support, t i := rfl
      rw [this]
      exact le_totalDegree (mem_support_iff.2 hcoeff_ne)
  obtain ⟨s, hs, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero Q t hcoeff_ne htot S
    (fun i => by
      fin_cases i
      · simp [hS, ht]; omega
      · simp [hS, ht, Finset.card_erase_of_mem ha]; omega)
  exact hne (hvanish s hs)

/-- **Dias da Silva–Hamidoune theorem for `h = 2`.** The case `h = 2` of the wanted
`MetaMathlibExt.dias_da_silva_hamidoune`, in its form: for a prime `p` and `A ⊆ ℤ_p` with
`2 ≤ |A|`, `|2^∧ A| ≥ min(p, 2|A| - 2² + 1)` (J. Bhanja, *Sumsets with a Minimum Number of
Distinct Terms*, INTEGERS 25 (2025), Article A12, Theorem 2 with `h = 2`; N. Alon, "Combinatorial
Nullstellensatz", Combin. Probab. Comput. 8 (1999), Theorem 4.3). It is
`min_le_card_restrictedSumset`, since `2|A| - 4 + 1 = 2|A| - 3` when `|A| ≥ 2`. -/
theorem dias_da_silva_hamidoune_two {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (hk : 2 ≤ A.card) :
    min p (2 * A.card - 2 ^ 2 + 1) ≤ (MetaMathlibExt.restrictedSumset 2 A).card := by
  have : 2 * A.card - 2 ^ 2 + 1 = 2 * A.card - 3 := by omega
  rw [this]
  exact min_le_card_restrictedSumset hp hA

end MathlibExt.Combinatorics.Additive.ErdosHeilbronn
