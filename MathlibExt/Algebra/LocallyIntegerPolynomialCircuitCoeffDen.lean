/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.Span
public import MathlibExt.Algebra.Polynomial.FactorialEvalBound
public import MathlibExt.Algebra.Polynomial.InterpolationPolyExchange
public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
public import MathlibExt.Algebra.Polynomial.LowDegreeInterpolant
public import MathlibExt.Data.Nat.ProgressionIntersection

/-!
# Denominator of the top coefficient on a circuit

The top interpolation coefficient of a circuit has a nontrivial denominator that divides
all differences of its nodes.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41 (arXiv `2401.17955`, TeX source read), Lemma 7,
with the circuit definition preceding it.
-/

open Polynomial

namespace MetaMathlibExt

private theorem interpolationPoly_sub_erase (f : ℤ → ℤ) (S : Finset ℤ) {a : ℤ}
    (ha : a ∈ S) :
    interpolationPoly S f -
      C ((interpolationPoly S f).coeff (S.card - 1)) *
        Lagrange.nodal (S.erase a) (fun z : ℤ => (z : ℚ)) =
      interpolationPoly (S.erase a) f := by
  have hcard : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
  refine eq_of_degrees_lt_of_eval_index_eq (S.erase a)
    (v := fun z : ℤ => (z : ℚ)) Int.cast_injective.injOn ?_
    (degree_interpolationPoly_lt _ _) ?_
  · rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub, coeff_C_mul]
    rcases hm.eq_or_lt with rfl | hlt
    · have hmonic : (Lagrange.nodal (S.erase a) fun z : ℤ => (z : ℚ)).coeff
          (S.erase a).card = 1 := by
        simpa only [Lagrange.natDegree_nodal] using
          (Lagrange.nodal_monic (s := S.erase a) (v := fun z : ℤ => (z : ℚ))).coeff_natDegree
      rw [hmonic, hcard, mul_one, sub_self]
    · have hP : (interpolationPoly S f).coeff m = 0 := by
        apply coeff_eq_zero_of_degree_lt
        refine (degree_interpolationPoly_lt S f).trans_le ?_
        have hpos := Finset.card_pos.mpr ⟨a, ha⟩
        exact_mod_cast (by omega : S.card ≤ m)
      have hN : (Lagrange.nodal (S.erase a) fun z : ℤ => (z : ℚ)).coeff m = 0 := by
        apply coeff_eq_zero_of_degree_lt
        rw [Lagrange.degree_nodal]
        exact_mod_cast hlt
      rw [hP, hN, mul_zero, sub_zero]
  · intro z hz
    rw [eval_sub, eval_mul, eval_C, Lagrange.eval_nodal_at_node hz, mul_zero, sub_zero,
      eval_interpolationPoly f (Finset.mem_of_mem_erase hz), eval_interpolationPoly f hz]

@[expose] public section

/-- **Denominator of the top coefficient on a circuit.** Let $f : \mathbb{Z} \to \mathbb{Z}$, and
for a finite set $Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation
polynomial of $f$ on $Y$. Let $X \subseteq \mathbb{Z}$ be a finite circuit for $f$: $f_X$ does not
have integer coefficients, but $f_{X \setminus \{a\}}$ has integer coefficients for every
$a \in X$. Let $c$ be the coefficient of $x^{|X|-1}$ in $f_X$ and let $q \ge 1$ be the denominator
of $c$ in lowest terms. Then $q \ne 1$, so $c$ is not an integer, and $q$ divides $a - b$ for all
$a, b \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 7 (`integers-2025-A41-lem-7`), with the circuit definition preceding it. -/
public theorem circuit_coeff_den (f : ℤ → ℤ) (X : Finset ℤ)
    (hX : interpolationPoly X f ∉ Polynomial.lifts (Int.castRingHom ℚ))
    (hmin : ∀ a ∈ X, interpolationPoly (X.erase a) f ∈ Polynomial.lifts (Int.castRingHom ℚ)) :
    ((interpolationPoly X f).coeff (X.card - 1)).den ≠ 1 ∧
      ∀ a ∈ X, ∀ b ∈ X, (((interpolationPoly X f).coeff (X.card - 1)).den : ℤ) ∣ a - b := by
  have hne : X.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hX
    exact hX (by simp [interpolationPoly, Lagrange.interpolate])
  obtain ⟨a₀, ha₀⟩ := hne
  constructor
  · intro hc
    have hcint : (Int.castRingHom ℚ) ((interpolationPoly X f).coeff (X.card - 1)).num =
        (interpolationPoly X f).coeff (X.card - 1) := Rat.intCast_num_of_den_eq_one hc
    obtain ⟨p, hp⟩ := (mem_lifts _).mp (hmin a₀ ha₀)
    apply hX
    refine (mem_lifts _).mpr
      ⟨p + C ((interpolationPoly X f).coeff (X.card - 1)).num *
        Lagrange.nodal (X.erase a₀) id, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hp]
    have hmap : (Lagrange.nodal (X.erase a₀) id : ℤ[X]).map (Int.castRingHom ℚ) =
        Lagrange.nodal (X.erase a₀) (fun z : ℤ => (z : ℚ)) := by
      simp [Lagrange.nodal, Polynomial.map_prod]
    rw [hmap, hcint, ← interpolationPoly_sub_erase f X ha₀,
      sub_add_cancel]
  · intro a ha b hb
    by_cases hab : a = b
    · simp [hab]
    let S := (X.erase a).erase b
    have hb' : b ∈ X.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    have hSa : a ∉ S := by simp [S]
    have hSb : b ∉ S := by simp [S]
    have hBa : insert b S = X.erase a := Finset.insert_erase hb'
    have hAB : insert a (insert b S) = X := by rw [hBa, Finset.insert_erase ha]
    have hAa : insert a S = X.erase b := by
      dsimp [S]
      rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hab, ha⟩)]
    have hcard : S.card + 1 = X.card - 1 := by
      have h₁ := Finset.card_erase_of_mem ha
      have h₂ := Finset.card_erase_of_mem hb'
      have hpos := Finset.card_pos.mpr ⟨b, hb'⟩
      dsimp [S]
      omega
    have hex := interpolationPoly_exchange S hSa hSb f
    rw [hAB, hAa, hBa, hcard] at hex
    have hN : (∏ z ∈ S, (Polynomial.X - C (z : ℚ))).coeff S.card = 1 := by
      simpa only [← Lagrange.nodal_eq, Lagrange.natDegree_nodal] using
        (Lagrange.nodal_monic (s := S) (v := fun z : ℤ => (z : ℚ))).coeff_natDegree
    have hcoeff := congrArg (fun p : ℚ[X] => p.coeff S.card) hex
    rw [coeff_add, coeff_C_mul, hN, mul_one] at hcoeff
    obtain ⟨u, hu⟩ := (lifts_iff_coeff_lifts _).mp (hmin b hb) S.card
    obtain ⟨v, hv⟩ := (lifts_iff_coeff_lifts _).mp (hmin a ha) S.card
    change (u : ℚ) = _ at hu
    change (v : ℚ) = _ at hv
    have hmul : (interpolationPoly X f).coeff (X.card - 1) * ((a - b : ℤ) : ℚ) =
        ((u - v : ℤ) : ℚ) := by
      rw [Int.cast_sub, Int.cast_sub, hu, hv]
      exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hcoeff.symm)
    have hdiff : ((a - b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hab)
    have hc : (interpolationPoly X f).coeff (X.card - 1) = Rat.divInt (u - v) (a - b) := by
      rw [Rat.divInt_eq_div]
      exact (eq_div_iff hdiff).mpr hmul
    rw [hc]
    exact Rat.den_dvd _ _

end

end MetaMathlibExt
