/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Isotropic
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TernaryPlaces
public import MathlibExt.NumberTheory.Rat.HasseMinkowskiTernary
public import MathlibExt.NumberTheory.Rat.PrescribedSquareClasses
public import MathlibExt.NumberTheory.Rat.LocalGlobal
public import MathlibExt.LinearAlgebra.QuadraticForm.Isotropic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The Hasse–Minkowski theorem for diagonal quaternary forms over `ℚ`

Let $a_1, a_2, a_3, a_4$ be nonzero rationals. If
$a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2 + a_4 x_4^2 = 0$ has a solution other than $0$ over
$\mathbb{R}$ and over $\mathbb{Q}_p$ for every prime $p$, then it has one over $\mathbb{Q}$
(`Rat.exists_quaternary_eq_zero_of_forall_local`). This is the case $n = 4$ of the
Hasse–Minkowski theorem, and the proof follows A. V. Sutherland, *18.782 Introduction to
Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, §11.3, proof of Theorem 11.12, case $n = 4$,
p. 5, <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>.

* Let $S$ consist of the infinite place and the primes dividing $2 a_1 a_2 a_3 a_4$. At every
  place $v$ there is $t_v \ne 0$ in $\mathbb{Q}_v$ represented by $\langle a_1, a_2 \rangle$ with
  $-t_v$ represented by $\langle a_3, a_4 \rangle$: take the value of $a_1 x_1^2 + a_2 x_2^2$ at a
  local zero; if it vanishes, one of the two binary forms has a nonzero zero and so represents
  every element of $\mathbb{Q}_v$.
* Lemma 11.11 (`Rat.Place.exists_mem_squareClass`) gives $t \in \mathbb{Q}^\times$ and a prime
  $p_0 \notin S$ with $t \in t_v \mathbb{Q}_v^{\times 2}$ for $v \in S$ and $|t|_p = 1$ for the
  primes $p \notin S \cup \{p_0\}$.
* The ternary forms $\langle a_1, a_2, -t \rangle$ and $\langle a_3, a_4, t \rangle$ have nonzero
  zeros over $\mathbb{Q}_v$ for every $v \ne p_0$: for $v \in S$ by the choice of $t$, and for
  $v = p \notin S \cup \{p_0\}$ because $p$ is odd and all coefficients are $p$-adic units
  (`HilbertSymbol.diagonal_unit_isotropic`). Corollary 11.5
  (`Rat.Place.exists_ternary_eq_zero_of_forall_ne`) adds $v = p_0$, and the ternary case
  (`Rat.exists_ternary_eq_zero_of_forall_local`) gives rational zeros of both forms.
* If the last coordinate of one of these rational zeros is $0$, it is a nonzero zero of
  $\langle a_1, a_2 \rangle$ or of $\langle a_3, a_4 \rangle$, and hence of the quaternary form.
  Otherwise $\langle a_1, a_2 \rangle$ represents $t$ and $\langle a_3, a_4 \rangle$ represents
  $-t$ over $\mathbb{Q}$, and adding the two representations gives a zero, nonzero as $t \ne 0$.
-/

set_option autoImplicit false

@[expose] public section

namespace Rat

section Field

variable {K : Type*} [Field K]

/-- From a nonzero zero of `a₁ x₁ ^ 2 + a₂ x₂ ^ 2 + a₃ x₃ ^ 2 + a₄ x₄ ^ 2`, an element `t ≠ 0`
represented by `a₁ x ^ 2 + a₂ y ^ 2` with `-t` represented by `a₃ x ^ 2 + a₄ y ^ 2`. -/
private theorem hmq_exists_split {a₁ a₂ a₃ a₄ : K} (h2 : (2 : K) ≠ 0) (h₁ : a₁ ≠ 0)
    (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0)
    (h : ∃ x₁ x₂ x₃ x₄ : K, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0) :
    ∃ t : K, t ≠ 0 ∧ (∃ x y : K, a₁ * x ^ 2 + a₂ * y ^ 2 = t) ∧
      ∃ x y : K, a₃ * x ^ 2 + a₄ * y ^ 2 = -t := by
  obtain ⟨x₁, x₂, x₃, x₄, hne, hz⟩ := h
  by_cases hs : a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 = 0
  · have hs' : a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0 := by linear_combination hz - hs
    by_cases h12 : x₁ = 0 ∧ x₂ = 0
    · have h34 : ¬(x₃ = 0 ∧ x₄ = 0) := fun h34 => hne ⟨h12.1, h12.2, h34.1, h34.2⟩
      exact ⟨a₁, h₁, ⟨1, 0, by ring⟩,
        exists_mul_sq_add_mul_sq_eq_of_isotropic h2 h₃ h₄ (fun h => h34 (Prod.mk.inj h)) hs' _⟩
    · exact ⟨-a₃, neg_ne_zero.2 h₃,
        exists_mul_sq_add_mul_sq_eq_of_isotropic h2 h₁ h₂ (fun h => h12 (Prod.mk.inj h)) hs _,
        1, 0, by ring⟩
  · exact ⟨_, hs, ⟨x₁, x₂, rfl⟩, x₃, x₄, by linear_combination hz⟩

/-- If `a x ^ 2 + b z ^ 2` represents `t` and `s = t y ^ 2`, then `a x ^ 2 + b z ^ 2 - s w ^ 2`
has a nonzero zero. -/
private theorem hmq_ternary_of_rep {a b t s y : K} (hs : s = t * y ^ 2)
    (h : ∃ x z : K, a * x ^ 2 + b * z ^ 2 = t) :
    ∃ x z w : K, ¬(x = 0 ∧ z = 0 ∧ w = 0) ∧ a * x ^ 2 + b * z ^ 2 + -s * w ^ 2 = 0 := by
  obtain ⟨x, z, hxz⟩ := h
  exact ⟨x * y, z * y, 1, fun h => one_ne_zero h.2.2, by rw [hs, ← hxz]; ring⟩

end Field

/-- A diagonal ternary form over `ℚ_[p]`, `p` odd, whose coefficients have norm `1` has a nonzero
zero. -/
private theorem hmq_padic_ternary {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c : ℚ_[p]}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨x, hx, hsum⟩ := HilbertSymbol.diagonal_unit_isotropic p hp (by norm_num : 2 < 3)
    ![PadicInt.mkUnits ha, PadicInt.mkUnits hb, PadicInt.mkUnits hc]
  refine ⟨x 0, x 1, x 2, fun h => hx ?_, ?_⟩
  · funext i
    fin_cases i
    exacts [h.1, h.2.1, h.2.2]
  · simpa [Fin.sum_univ_three, PadicInt.mkUnits_eq] using hsum

/-- A prime `p` outside the prime factors of `|num a| * den a`, `a ≠ 0`, does not divide it. -/
private theorem hmq_not_dvd {p : ℕ} (hp : p.Prime) {a : ℚ} (ha : a ≠ 0)
    (h : p ∉ (a.num.natAbs * a.den).primeFactors) : ¬p ∣ a.num.natAbs * a.den :=
  fun hd => h (Nat.mem_primeFactors.2
    ⟨hp, hd, mul_ne_zero (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 ha)) a.den_ne_zero⟩)

end Rat

open Rat Rat.Place in
/-- **Hasse–Minkowski theorem for diagonal quaternary forms over `ℚ`.** Let `a₁`, `a₂`, `a₃`, `a₄`
be nonzero rationals. If `a₁ x₁ ^ 2 + a₂ x₂ ^ 2 + a₃ x₃ ^ 2 + a₄ x₄ ^ 2 = 0` has a solution
`(x₁, x₂, x₃, x₄) ≠ (0, 0, 0, 0)` in `ℝ` and in `ℚ_[p]` for every prime `p`, then it has a solution
`(x₁, x₂, x₃, x₄) ≠ (0, 0, 0, 0)` in `ℚ`.

This is the case `n = 4` of A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT,
Fall 2013, Lecture 11, Theorem 11.12, following the proof of that case given there, p. 5. -/
theorem Rat.exists_quaternary_eq_zero_of_forall_local {a₁ a₂ a₃ a₄ : ℚ} (h₁ : a₁ ≠ 0)
    (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0)
    (hreal : ∃ x₁ x₂ x₃ x₄ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x₁ x₂ x₃ x₄ : ℚ_[p],
      ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0) :
    ∃ x₁ x₂ x₃ x₄ : ℚ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0 := by
  classical
  -- local zeros at every place
  have hloc : ∀ v : Place, ∃ x₁ x₂ x₃ x₄ : CompletedField v,
      ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧ embedding v a₁ * x₁ ^ 2 + embedding v a₂ * x₂ ^ 2 +
        embedding v a₃ * x₃ ^ 2 + embedding v a₄ * x₄ ^ 2 = 0 := by
    intro v
    cases v with
    | infinite => exact hreal
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      exact hpadic p.1
  have h2 : ∀ v : Place, (2 : CompletedField v) ≠ 0 := fun v => by
    cases v <;> exact two_ne_zero
  have hemb : ∀ (v : Place) {a : ℚ}, a ≠ 0 → embedding v a ≠ 0 :=
    fun v _ ha => (map_ne_zero _).2 ha
  -- the local elements `t_v`
  choose t ht0 hrep₁ hrep₂ using fun v => hmq_exists_split (h2 v) (hemb v h₁) (hemb v h₂)
    (hemb v h₃) (hemb v h₄) (hloc v)
  -- the finite set of places `S`
  let P : Finset ℕ := insert 2 ((a₁.num.natAbs * a₁.den).primeFactors ∪
    (a₂.num.natAbs * a₂.den).primeFactors ∪ (a₃.num.natAbs * a₃.den).primeFactors ∪
    (a₄.num.natAbs * a₄.den).primeFactors)
  let S : Finset Place := insert .infinite ((P.subtype Nat.Prime).image Place.finite)
  have hP : ∀ p : Nat.Primes, Place.finite p ∉ S → p.1 ∉ P := fun p hp hmem =>
    hp (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_subtype.2 hmem)))
  -- Lemma 11.11
  obtain ⟨q, p₀, hq0, -, hsq, habs⟩ :=
    Place.exists_mem_squareClass S fun v => Units.mk0 (t v.1) (ht0 v.1)
  -- the primes outside `S ∪ {p₀}`
  have hout : ∀ p : Nat.Primes, Place.finite p ∉ S → p ≠ p₀ →
      haveI : Fact p.1.Prime := ⟨p.2⟩
      p.1 ≠ 2 ∧ ‖(a₁ : ℚ_[p.1])‖ = 1 ∧ ‖(a₂ : ℚ_[p.1])‖ = 1 ∧ ‖(a₃ : ℚ_[p.1])‖ = 1 ∧
        ‖(a₄ : ℚ_[p.1])‖ = 1 ∧ ‖(q : ℚ_[p.1])‖ = 1 := by
    intro p hpS hpq
    have : Fact p.1.Prime := ⟨p.2⟩
    have hp := hP p hpS
    simp only [P, Finset.mem_insert, Finset.mem_union, not_or] at hp
    obtain ⟨hp2, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hp₄⟩ := hp
    have hq := habs p hpS hpq
    rw [← Place.embedding_norm_eq_absoluteValue] at hq
    exact ⟨hp2, Padic.norm_ratCast_eq_one_of_not_dvd (hmq_not_dvd p.2 h₁ hp₁),
      Padic.norm_ratCast_eq_one_of_not_dvd (hmq_not_dvd p.2 h₂ hp₂),
      Padic.norm_ratCast_eq_one_of_not_dvd (hmq_not_dvd p.2 h₃ hp₃),
      Padic.norm_ratCast_eq_one_of_not_dvd (hmq_not_dvd p.2 h₄ hp₄), hq⟩
  -- the forms `⟨a₁, a₂, -q⟩` and `⟨a₃, a₄, q⟩` at the places other than `p₀`
  have hg₁ : ∀ v : Place, v ≠ .finite p₀ → ∃ x y z : CompletedField v,
      ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        embedding v a₁ * x ^ 2 + embedding v a₂ * y ^ 2 + embedding v (-q) * z ^ 2 = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · obtain ⟨y, hy⟩ := hsq ⟨v, hvS⟩
      rw [Units.val_mk0] at hy
      rw [map_neg]
      exact hmq_ternary_of_rep hy (hrep₁ v)
    · cases v with
      | infinite => exact absurd (Finset.mem_insert_self _ _) hvS
      | finite p =>
        have : Fact p.1.Prime := ⟨p.2⟩
        obtain ⟨hp2, ha₁, ha₂, -, -, hq⟩ := hout p hvS fun h => hv (h ▸ rfl)
        exact hmq_padic_ternary hp2 ha₁ ha₂ (by rw [map_neg, norm_neg]; exact hq)
  have hg₂ : ∀ v : Place, v ≠ .finite p₀ → ∃ x y z : CompletedField v,
      ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        embedding v a₃ * x ^ 2 + embedding v a₄ * y ^ 2 + embedding v q * z ^ 2 = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · obtain ⟨y, hy⟩ := hsq ⟨v, hvS⟩
      rw [Units.val_mk0] at hy
      have hy' : -embedding v q = -t v * y ^ 2 := by rw [hy]; ring
      simpa only [neg_neg] using hmq_ternary_of_rep hy' (hrep₂ v)
    · cases v with
      | infinite => exact absurd (Finset.mem_insert_self _ _) hvS
      | finite p =>
        have : Fact p.1.Prime := ⟨p.2⟩
        obtain ⟨hp2, -, -, ha₃, ha₄, hq⟩ := hout p hvS fun h => hv (h ▸ rfl)
        exact hmq_padic_ternary hp2 ha₃ ha₄ hq
  -- Corollary 11.5 and the ternary case
  have hG₁ := Place.exists_ternary_eq_zero_of_forall_ne h₁ h₂ (neg_ne_zero.2 hq0) _ hg₁
  have hG₂ := Place.exists_ternary_eq_zero_of_forall_ne h₃ h₄ hq0 _ hg₂
  obtain ⟨y₁, y₂, z, hne₁, hz₁⟩ := Rat.exists_ternary_eq_zero_of_forall_local h₁ h₂
    (neg_ne_zero.2 hq0) (hG₁ .infinite) fun p _ => hG₁ (.finite ⟨p, Fact.out⟩)
  obtain ⟨y₃, y₄, w, hne₂, hz₂⟩ := Rat.exists_ternary_eq_zero_of_forall_local h₃ h₄ hq0
    (hG₂ .infinite) fun p _ => hG₂ (.finite ⟨p, Fact.out⟩)
  -- combining the two rational zeros
  by_cases hz : z = 0
  · subst hz
    exact ⟨y₁, y₂, 0, 0, fun h => hne₁ ⟨h.1, h.2.1, rfl⟩, by linear_combination hz₁⟩
  by_cases hw : w = 0
  · subst hw
    exact ⟨0, 0, y₃, y₄, fun h => hne₂ ⟨h.2.2.1, h.2.2.2, rfl⟩, by linear_combination hz₂⟩
  have e₁ : a₁ * (y₁ / z) ^ 2 + a₂ * (y₂ / z) ^ 2 = q := by
    field_simp
    linear_combination hz₁
  have e₂ : a₃ * (y₃ / w) ^ 2 + a₄ * (y₄ / w) ^ 2 = -q := by
    field_simp
    linear_combination hz₂
  refine ⟨y₁ / z, y₂ / z, y₃ / w, y₄ / w, fun h => hq0 ?_, by linear_combination e₁ + e₂⟩
  rw [h.1, h.2.1] at e₁
  simpa using e₁.symm
