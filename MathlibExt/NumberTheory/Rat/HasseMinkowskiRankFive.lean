/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Isotropic
public import MathlibExt.NumberTheory.Rat.LocalGlobal
public import MathlibExt.LinearAlgebra.QuadraticForm.Isotropic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The inductive step of the Hasse–Minkowski theorem in rank at least five

Let $n \ge 5$ and let $a_1, \dots, a_n$ be nonzero rationals such that
$f = a_1 x_1^2 + \dots + a_n x_n^2$ has a nonzero zero over $\mathbb{R}$ and over every
$\mathbb{Q}_p$. Assuming the Hasse–Minkowski theorem for diagonal forms in $n - 2$ and $n - 1$
variables, $f$ has a nonzero zero over $\mathbb{Q}$
(`Rat.exists_diagonal_eq_zero_of_rank_ge_five`). On the way we show that the square classes
$x \mathbb{Q}_v^{\times 2}$, $x \ne 0$, are open in $\mathbb{Q}_v$ (`Rat.Place.isOpen_squareClass`).

The proof follows A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013,
Lecture 11, proof of Theorem 11.12, case $n \ge 5$, p. 5, and its footnote 1,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>.

* Put $g = \langle a_3, \dots, a_n \rangle$. Outside the infinite place, the prime $2$ and the
  primes dividing a numerator or a denominator of $a_3, \dots, a_n$, the form $g$ has unit
  coefficients in at least three variables and so a nonzero zero
  (`HilbertSymbol.diagonal_unit_isotropic`). Let $T$ be the finite set of places where $g$ has no
  nonzero zero. If $T = \emptyset$, the case $n - 2$ gives a rational zero of $g$, hence of $f$.
* For $v \in T$ a local zero of $f$ gives $x_v, y_v$ with $t_v = a_1 x_v^2 + a_2 y_v^2 \ne 0$ and
  $-t_v$ represented by $g$ over $\mathbb{Q}_v$.
* The square classes are open (a $p$-adic number within $|2|_p^2$ of $1$ is a square by Hensel's
  lemma, a real number within $1$ of $1$ is positive), so weak approximation gives rationals $x, y$
  with $t = a_1 x^2 + a_2 y^2 \in t_v \mathbb{Q}_v^{\times 2}$ for all $v \in T$.
* Then $\langle t, a_3, \dots, a_n \rangle$ has a nonzero zero at every place, and the case $n - 1$
  gives a rational zero $(s, x_3, \dots, x_n)$; the vector $(s x, s y, x_3, \dots, x_n)$ is a
  nonzero rational zero of $f$.
-/

set_option autoImplicit false

@[expose] public section

namespace Rat

namespace Place

/-- A `p`-adic number within `‖2‖ ^ 2` of `1` is a square (Hensel's lemma for `X ^ 2 - w`). -/
private theorem hm5_padic_sq {p : ℕ} [Fact p.Prime] {w : ℚ_[p]}
    (hw : ‖w - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2) : ∃ z : ℚ_[p], w = z ^ 2 := by
  have h2 : ‖(2 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) 2
  have hlt : ‖w - 1‖ < 1 := hw.trans_le (pow_le_one₀ (norm_nonneg _) h2)
  have hw1 : ‖w‖ ≤ 1 := by
    calc ‖w‖ = ‖(w - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖w - 1‖ ‖(1 : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le hlt.le norm_one.le
  set u : ℤ_[p] := ⟨w, hw1⟩ with hu
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := Polynomial.X ^ 2 - Polynomial.C u) (a := 1) (by
    have e1 : ‖Polynomial.aeval (1 : ℤ_[p]) (Polynomial.X ^ 2 - Polynomial.C u)‖ = ‖w - 1‖ := by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [← norm_neg, neg_sub]
      rfl
    have e2 : ‖Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u))‖ = ‖(2 : ℚ_[p])‖ := by
      have e : Polynomial.aeval (1 : ℤ_[p])
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u)) = 2 := by
        simp [one_add_one_eq_two]
      rw [e]
      rfl
    rw [e1, e2]
    exact hw)
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 = u := by
    simpa [sub_eq_zero] using hz
  have := congrArg (fun r : ℤ_[p] => (r : ℚ_[p])) hz'
  simpa [hu] using this.symm

/-- At every place `v` there is `δ > 0` such that every element of `ℚ_v` within `δ` of `1` is a
square. -/
private theorem hm5_exists_sq (v : Place) :
    ∃ δ > 0, ∀ w : CompletedField v, ‖w - 1‖ < δ → ∃ z : CompletedField v, w = z ^ 2 := by
  cases v with
  | infinite =>
    refine ⟨1, one_pos, fun w hw => ?_⟩
    have hw' : |(w : ℝ) - 1| < 1 := hw
    have h0 : (0 : ℝ) ≤ w := by linarith [(abs_lt.1 hw').1]
    exact ⟨Real.sqrt w, (Real.sq_sqrt h0).symm⟩
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    exact ⟨‖(2 : ℚ_[p.1])‖ ^ 2, pow_pos (norm_pos_iff.2 two_ne_zero) 2,
      fun w hw => hm5_padic_sq hw⟩

/-- **Square classes in a completion of `ℚ` are open.** Let `v` be a place of `ℚ` and let
`x ≠ 0` in `ℚ_v`. Then the square class `x ℚ_v^{×2} = {x z ^ 2 | z ∈ ℚ_v, z ≠ 0}` is an open subset
of `ℚ_v`.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013,
Lecture 11, footnote 1 on p. 5, <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem isOpen_squareClass (v : Place) {x : CompletedField v} (hx : x ≠ 0) :
    IsOpen {y : CompletedField v | ∃ z : CompletedField v, z ≠ 0 ∧ y = x * z ^ 2} := by
  obtain ⟨δ, hδ, hsq⟩ := hm5_exists_sq v
  rw [Metric.isOpen_iff]
  rintro _ ⟨z₀, hz₀, rfl⟩
  have hy₀ : x * z₀ ^ 2 ≠ 0 := mul_ne_zero hx (pow_ne_zero _ hz₀)
  have hpos : 0 < ‖x * z₀ ^ 2‖ := norm_pos_iff.2 hy₀
  refine ⟨min δ 1 * ‖x * z₀ ^ 2‖, mul_pos (lt_min hδ one_pos) hpos, fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hw : ‖y / (x * z₀ ^ 2) - 1‖ < min δ 1 := by
    rw [div_sub_one hy₀, norm_div, div_lt_iff₀ hpos]
    exact hy
  obtain ⟨w, hw'⟩ := hsq _ (hw.trans_le (min_le_left _ _))
  have hne : y / (x * z₀ ^ 2) ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, norm_one] at hw
    exact lt_irrefl _ (hw.trans_le (min_le_right _ _))
  refine ⟨z₀ * w, mul_ne_zero hz₀ ?_, ?_⟩
  · rintro rfl
    exact hne (by rw [hw']; ring)
  · rw [div_eq_iff hy₀] at hw'
    rw [hw']
    ring

/-- The diagonal form with coefficients `c` has a nonzero zero over `ℚ_v`. -/
private def HM5Iso (v : Place) {m : ℕ} (c : Fin m → ℚ) : Prop :=
  ∃ x : Fin m → CompletedField v, x ≠ 0 ∧ ∑ i, embedding v (c i) * x i ^ 2 = 0

end Place

open Place

section Field

variable {K : Type*} [Field K]

/-- If `a₀ x₀ ^ 2 + a₁ x₁ ^ 2 + g(z) = 0` nontrivially and `g` has no nonzero zero, there are `x, y`
with `t = a₀ x ^ 2 + a₁ y ^ 2 ≠ 0` and `-t` represented by `g`. -/
private theorem hm5_split (h2 : (2 : K) ≠ 0) {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) {k : ℕ}
    (b : Fin k → K) (j : Fin k) (hj : b j ≠ 0)
    (haniso : ∀ w : Fin k → K, ∑ i, b i * w i ^ 2 = 0 → w = 0) {x₀ x₁ : K} {z : Fin k → K}
    (hne : ¬(x₀ = 0 ∧ x₁ = 0 ∧ z = 0)) (hz : a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + ∑ i, b i * z i ^ 2 = 0) :
    ∃ x y : K, a₀ * x ^ 2 + a₁ * y ^ 2 ≠ 0 ∧
      ∃ w : Fin k → K, ∑ i, b i * w i ^ 2 = -(a₀ * x ^ 2 + a₁ * y ^ 2) := by
  classical
  by_cases hs : a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 = 0
  · have hz0 : z = 0 := haniso z (by linear_combination hz - hs)
    obtain ⟨x, y, hxy⟩ := exists_mul_sq_add_mul_sq_eq_of_isotropic h2 h₀ h₁
      (fun h => hne ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2, hz0⟩) hs (-b j)
    refine ⟨x, y, by rw [hxy]; exact neg_ne_zero.2 hj, Pi.single j 1, ?_⟩
    rw [hxy, neg_neg]
    simp [Pi.single_apply]
  · exact ⟨x₀, x₁, hs, z, by linear_combination hz⟩

end Field

/-- Outside `2` and the primes dividing a numerator or a denominator of the `b i`, the diagonal form
with nonzero coefficients `b` in more than two variables has a nonzero `p`-adic zero. -/
private theorem hm5_isoAt_of_not_mem {k : ℕ} (hk : 2 < k) (b : Fin k → ℚ) (hb : ∀ i, b i ≠ 0)
    (p : Nat.Primes) (hp : p.1 ∉ insert 2
      (Finset.univ.biUnion fun i => ((b i).num.natAbs * (b i).den).primeFactors)) :
    HM5Iso (.finite p) b := by
  have : Fact p.1.Prime := ⟨p.2⟩
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and, not_or,
    not_exists] at hp
  have hnorm : ∀ i, ‖(b i : ℚ_[p.1])‖ = 1 := fun i => Padic.norm_ratCast_eq_one_of_not_dvd fun hd =>
    hp.2 i (Nat.mem_primeFactors.2 ⟨p.2, hd,
      mul_ne_zero (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 (hb i))) (b i).den_ne_zero⟩)
  obtain ⟨x, hx, hs⟩ := HilbertSymbol.diagonal_unit_isotropic p.1 hp.1 hk
    fun i => PadicInt.mkUnits (hnorm i)
  exact ⟨x, hx, (by simpa only [PadicInt.mkUnits_eq] using hs :
    ∑ i, (b i : ℚ_[p.1]) * x i ^ 2 = 0)⟩

/-- The inductive step in components: `a₀ x₀ ^ 2 + a₁ x₁ ^ 2 + ∑ b i z i ^ 2`, `k > 2`. -/
private theorem hm5_main {k : ℕ} (hk : 2 < k) {a₀ a₁ : ℚ} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0)
    {b : Fin k → ℚ} (hb : ∀ i, b i ≠ 0)
    (hloc : ∀ v : Place, ∃ (x₀ x₁ : CompletedField v) (z : Fin k → CompletedField v),
      ¬(x₀ = 0 ∧ x₁ = 0 ∧ z = 0) ∧
        embedding v a₀ * x₀ ^ 2 + embedding v a₁ * x₁ ^ 2 + ∑ i, embedding v (b i) * z i ^ 2 = 0)
    (ih₁ : (∀ v, HM5Iso v b) → ∃ z : Fin k → ℚ, z ≠ 0 ∧ ∑ i, b i * z i ^ 2 = 0)
    (ih₂ : ∀ t : ℚ, t ≠ 0 → (∀ v : Place, ∃ (s : CompletedField v) (z : Fin k → CompletedField v),
      ¬(s = 0 ∧ z = 0) ∧ embedding v t * s ^ 2 + ∑ i, embedding v (b i) * z i ^ 2 = 0) →
      ∃ (s : ℚ) (z : Fin k → ℚ), ¬(s = 0 ∧ z = 0) ∧ t * s ^ 2 + ∑ i, b i * z i ^ 2 = 0) :
    ∃ (x₀ x₁ : ℚ) (z : Fin k → ℚ), ¬(x₀ = 0 ∧ x₁ = 0 ∧ z = 0) ∧
      a₀ * x₀ ^ 2 + a₁ * x₁ ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
  classical
  -- the finite set of places where `g = ⟨b⟩` may fail to be isotropic
  let P : Finset ℕ :=
    insert 2 (Finset.univ.biUnion fun i => ((b i).num.natAbs * (b i).den).primeFactors)
  let S₀ : Finset Place := insert .infinite ((P.subtype Nat.Prime).image Place.finite)
  have hgood : ∀ v, v ∉ S₀ → HM5Iso v b := by
    intro v hv
    cases v with
    | infinite => exact absurd (Finset.mem_insert_self _ _) hv
    | finite p =>
      exact hm5_isoAt_of_not_mem hk b hb p fun hp =>
        hv (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_subtype.2 hp)))
  -- the places where `g` is anisotropic
  let T : Finset Place := S₀.filter fun v => ¬HM5Iso v b
  have hT : ∀ v, v ∉ T → HM5Iso v b := by
    intro v hv
    by_cases hvS : v ∈ S₀
    · by_contra h
      exact hv (Finset.mem_filter.2 ⟨hvS, h⟩)
    · exact hgood v hvS
  by_cases hTne : T.Nonempty
  swap
  · obtain ⟨z, hz, hsum⟩ := ih₁ fun v => hT v fun hv => hTne ⟨v, hv⟩
    exact ⟨0, 0, z, fun h => hz h.2.2, by simpa using hsum⟩
  -- the local elements `t_v`
  have h2 : ∀ v : Place, (2 : CompletedField v) ≠ 0 := fun v => by
    cases v <;> exact two_ne_zero
  have hemb : ∀ (v : Place) {q : ℚ}, q ≠ 0 → embedding v q ≠ 0 :=
    fun v _ hq => (map_ne_zero _).2 hq
  have hdata : ∀ v : T, ∃ x y : CompletedField v.1,
      embedding v.1 a₀ * x ^ 2 + embedding v.1 a₁ * y ^ 2 ≠ 0 ∧
        ∃ w : Fin k → CompletedField v.1,
          ∑ i, embedding v.1 (b i) * w i ^ 2 =
            -(embedding v.1 a₀ * x ^ 2 + embedding v.1 a₁ * y ^ 2) := by
    rintro ⟨v, hv⟩
    have haniso : ∀ w : Fin k → CompletedField v, ∑ i, embedding v (b i) * w i ^ 2 = 0 → w = 0 := by
      intro w hw
      by_contra hw0
      exact (Finset.mem_filter.1 hv).2 ⟨w, hw0, hw⟩
    obtain ⟨x₀, x₁, z, hne, hz⟩ := hloc v
    exact hm5_split (h2 v) (hemb v h₀) (hemb v h₁) _ ⟨0, by omega⟩ (hemb v (hb _)) haniso hne hz
  choose xv yv htv wv hwv using hdata
  -- weak approximation in the open square classes
  let W : Set (((v : T) → CompletedField v.1) × ((v : T) → CompletedField v.1)) :=
    {e | ∀ v : T, embedding v.1 a₀ * e.1 v ^ 2 + embedding v.1 a₁ * e.2 v ^ 2 ∈
      {u | ∃ z : CompletedField v.1, z ≠ 0 ∧
        u = (embedding v.1 a₀ * xv v ^ 2 + embedding v.1 a₁ * yv v ^ 2) * z ^ 2}}
  have hW : IsOpen W := by
    simp only [W, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun v => ?_
    exact (isOpen_squareClass v.1 (htv v)).preimage (by fun_prop)
  have hWne : W.Nonempty := ⟨(xv, yv), fun v => ⟨1, one_ne_zero, by ring⟩⟩
  obtain ⟨⟨x, y⟩, hxy⟩ :=
    ((denseRange_embedding_pi T).prodMap (denseRange_embedding_pi T)).exists_mem_open hW hWne
  set t : ℚ := a₀ * x ^ 2 + a₁ * y ^ 2 with ht
  have hloct : ∀ v : T, ∃ z : CompletedField v.1, z ≠ 0 ∧
      embedding v.1 t = (embedding v.1 a₀ * xv v ^ 2 + embedding v.1 a₁ * yv v ^ 2) * z ^ 2 := by
    intro v
    obtain ⟨z, hz, h⟩ := hxy v
    exact ⟨z, hz, by rw [ht, map_add, map_mul, map_mul, map_pow, map_pow]; exact h⟩
  have ht0 : t ≠ 0 := by
    obtain ⟨v, hv⟩ := hTne
    obtain ⟨z, hz, h⟩ := hloct ⟨v, hv⟩
    intro h0
    rw [h0, map_zero] at h
    exact mul_ne_zero (htv _) (pow_ne_zero 2 hz) h.symm
  -- the form `⟨t, b⟩` is isotropic everywhere
  obtain ⟨s, z, hsz, hsum⟩ := ih₂ t ht0 fun v => by
    by_cases hv : v ∈ T
    · obtain ⟨c, -, h⟩ := hloct ⟨v, hv⟩
      refine ⟨1, fun i => c * wv ⟨v, hv⟩ i, fun h' => one_ne_zero h'.1, ?_⟩
      have hs : ∑ i, embedding v (b i) * (c * wv ⟨v, hv⟩ i) ^ 2 =
          c ^ 2 * ∑ i, embedding v (b i) * wv ⟨v, hv⟩ i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hs, hwv ⟨v, hv⟩, h]
      ring
    · obtain ⟨w, hw0, hw⟩ := hT v hv
      exact ⟨0, w, fun h => hw0 h.2, by simpa using hw⟩
  refine ⟨s * x, s * y, z, fun h => ?_, by rw [ht] at hsum; linear_combination hsum⟩
  have hs : s ≠ 0 := fun hs => hsz ⟨hs, h.2.2⟩
  have hx : x = 0 := (mul_eq_zero.1 h.1).resolve_left hs
  have hy : y = 0 := (mul_eq_zero.1 h.2.1).resolve_left hs
  exact ht0 (by rw [ht, hx, hy]; ring)

end Rat

open Rat Rat.Place in
/-- **Hasse–Minkowski in rank `n ≥ 5` from ranks `n - 2` and `n - 1`.** Let `n ≥ 5` and assume
the Hasse–Minkowski theorem for diagonal forms over `ℚ` in `m = n - 2` and `m = n - 1` variables:
for every `b : Fin m → ℚ` with nonzero entries, if `∑ i, b i * x i ^ 2 = 0` has a solution
`x ≠ 0` in `ℝ` and in `ℚ_[p]` for every prime `p`, then it has one in `ℚ`. Let
`a : Fin n → ℚ` have nonzero entries. If `∑ i, a i * x i ^ 2 = 0` has a solution `x ≠ 0` in `ℝ` and
in `ℚ_[p]` for every prime `p`, then it has a solution `x ≠ 0` in `ℚ`.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013,
Lecture 11, proof of Theorem 11.12, case `n ≥ 5`, p. 5,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem Rat.exists_diagonal_eq_zero_of_rank_ge_five {n : ℕ} (hn : 5 ≤ n)
    (ih : ∀ m : ℕ, (m = n - 2 ∨ m = n - 1) → ∀ b : Fin m → ℚ, (∀ i, b i ≠ 0) →
      (∃ x : Fin m → ℝ, x ≠ 0 ∧ ∑ i, (b i : ℝ) * x i ^ 2 = 0) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin m → ℚ_[p], x ≠ 0 ∧ ∑ i, (b i : ℚ_[p]) * x i ^ 2 = 0) →
      ∃ x : Fin m → ℚ, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0)
    (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hreal : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : 2 < k := by omega
  have hloc : ∀ v : Place, ∃ (x₀ x₁ : CompletedField v) (z : Fin k → CompletedField v),
      ¬(x₀ = 0 ∧ x₁ = 0 ∧ z = 0) ∧ embedding v (a 0) * x₀ ^ 2 + embedding v (a 1) * x₁ ^ 2 +
        ∑ i, embedding v (a i.succ.succ) * z i ^ 2 = 0 := by
    intro v
    obtain ⟨x, hx, hs⟩ : ∃ x : Fin (k + 2) → CompletedField v, x ≠ 0 ∧
        ∑ i, embedding v (a i) * x i ^ 2 = 0 := by
      cases v with
      | infinite => exact hreal
      | finite p =>
        have : Fact p.1.Prime := ⟨p.2⟩
        exact hpadic p.1
    refine ⟨x 0, x 1, fun i => x i.succ.succ, fun h0 => hx (funext fun i => ?_), ?_⟩
    · refine Fin.cases h0.1 (fun j => Fin.cases ?_ (fun l => congrFun h0.2.2 l) j) i
      simpa using h0.2.1
    · simpa [Fin.sum_univ_succ, add_assoc] using hs
  have ih₁ : (∀ v, HM5Iso v fun i : Fin k => a i.succ.succ) →
      ∃ z : Fin k → ℚ, z ≠ 0 ∧ ∑ i, a i.succ.succ * z i ^ 2 = 0 := fun h =>
    ih k (Or.inl (by omega)) _ (fun i => ha _) (h .infinite)
      fun p _ => h (.finite ⟨p, Fact.out⟩)
  have ih₂ : ∀ t : ℚ, t ≠ 0 → (∀ v : Place, ∃ (s : CompletedField v)
      (z : Fin k → CompletedField v), ¬(s = 0 ∧ z = 0) ∧
        embedding v t * s ^ 2 + ∑ i, embedding v (a i.succ.succ) * z i ^ 2 = 0) →
      ∃ (s : ℚ) (z : Fin k → ℚ), ¬(s = 0 ∧ z = 0) ∧
        t * s ^ 2 + ∑ i, a i.succ.succ * z i ^ 2 = 0 := by
    intro t ht h
    have hc : ∀ i, (Fin.cons t (fun i : Fin k => a i.succ.succ) : Fin (k + 1) → ℚ) i ≠ 0 :=
      fun i => Fin.cases ht (fun j => ha _) i
    have hl : ∀ v : Place, ∃ x : Fin (k + 1) → CompletedField v, x ≠ 0 ∧
        ∑ i, embedding v ((Fin.cons t (fun i : Fin k => a i.succ.succ) : Fin (k + 1) → ℚ) i) *
          x i ^ 2 = 0 := by
      intro v
      obtain ⟨s, z, hne, hs⟩ := h v
      refine ⟨Fin.cons s z, fun h0 => hne ⟨by simpa using congrFun h0 0,
        funext fun i => by simpa using congrFun h0 i.succ⟩, ?_⟩
      simpa [Fin.sum_univ_succ] using hs
    obtain ⟨w, hw, hsum⟩ := ih (k + 1) (Or.inr (by omega)) _ hc (hl .infinite)
      fun p _ => hl (.finite ⟨p, Fact.out⟩)
    refine ⟨w 0, fun i => w i.succ, fun h0 => hw (funext fun i => ?_), ?_⟩
    · exact Fin.cases h0.1 (fun j => congrFun h0.2 j) i
    · simpa [Fin.sum_univ_succ] using hsum
  obtain ⟨x₀, x₁, z, hne, hz⟩ := hm5_main hk (ha 0) (ha 1) (fun i => ha _) hloc ih₁ ih₂
  refine ⟨Fin.cons x₀ (Fin.cons x₁ z), fun h0 => hne ⟨by simpa using congrFun h0 0,
    by simpa using congrFun h0 1, funext fun i => by simpa using congrFun h0 i.succ.succ⟩, ?_⟩
  simpa [Fin.sum_univ_succ, add_assoc] using hz
