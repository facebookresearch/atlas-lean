/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/FraserKakeya.lean` (leanprover/lean-eval, revision 38361be):
the definitions and the statement of Fraser's theorem.
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison (lean-eval submission).

ATLAS moved these declarations from the wanted library and supplied their proofs.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

/-!
# Fourier decay for finite-field Kakeya sets

Fraser's theorem gives a probability measure on each Kakeya set with Fourier coefficients of
norm at most `1/q` away from zero. This bound is asymptotically sharp in every dimension at least
two. We average translates of lines for the upper bound. For sharpness we project onto a planar
Kakeya set of size at most `q * (q + 3) / 2` and apply the finite Plancherel identity.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FraserKakeyaWanted
namespace Combinatorics
namespace FraserKakeyaProblem

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F]

set_option linter.dupNamespace false in
/-- **Coordinate space.** For a type $F$ and a natural number $d$, $F^d$ denotes the set of
$d$-tuples $(x_1, \dots, x_d)$ of elements of $F$, that is, functions from a $d$-element index set
to $F$.

In this module $F$ is a finite field, so $F^d$ is the $d$-dimensional vector space over $F$. -/
abbrev Space (F : Type*) (d : ℕ) := Fin d → F

set_option linter.dupNamespace false in
/-- **Dot product.** Let $F$ be a finite field and $d$ a natural number. For $x, y \in F^d$, the
dot product is $x \cdot y = \sum_{i} x_i y_i \in F$, the sum running over the $d$ coordinates. -/
def dot {d : ℕ} (x y : Space F d) : F :=
  ∑ i, x i * y i

set_option linter.dupNamespace false in
/-- **Affine line.** Let $F$ be a finite field and $d$ a natural number. For $y, x \in F^d$, the
affine line with base point $y$ and direction $x$ is the set $\{y + a x : a \in F\} \subseteq F^d$.
When $x = 0$ this set is the single point $\{y\}$. -/
def affineLine {d : ℕ} (y x : Space F d) : Set (Space F d) :=
  {z | ∃ a : F, z = y + a • x}

set_option linter.dupNamespace false in
/-- **Kakeya set.** Let $F$ be a finite field and $d$ a natural number. A set $K \subseteq F^d$ is a
Kakeya set if for every $x \in F^d$ there is $y \in F^d$ such that the affine line
$\{y + a x : a \in F\}$ is contained in $K$; that is, $K$ contains a line in every direction. -/
def IsKakeya {d : ℕ} (K : Set (Space F d)) : Prop :=
  ∀ x : Space F d, ∃ y : Space F d, affineLine y x ⊆ K

set_option linter.dupNamespace false in
/-- **Probability measure supported on a set.** Let $F$ be a finite field, $d$ a natural number
and $K \subseteq F^d$. A function $\mu : F^d \to \mathbb{R}$ is a probability measure on $K$ if
$\mu(x) \ge 0$ for every $x \in F^d$, $\sum_{x \in F^d} \mu(x) = 1$, and $\mu(x) \ne 0$ implies
$x \in K$. -/
def IsProbabilityMeasureOn {d : ℕ} (K : Set (Space F d))
    (μ : Space F d → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧ ∀ x, μ x ≠ 0 → x ∈ K

set_option linter.dupNamespace false in
/-- **Finite-field Fourier transform.** Let $F$ be a finite field, $d$ a natural number and $\chi$
an additive character of $F$ with values in $\mathbb{C}$. For $\mu : F^d \to \mathbb{R}$ and
$\xi \in F^d$, the Fourier transform of $\mu$ at $\xi$ is
$\hat{\mu}(\xi) = \sum_{x \in F^d} \chi(-\xi \cdot x)\, \mu(x) \in \mathbb{C}$, where
$\xi \cdot x$ is the dot product.

The definition allows any character; it is used with a nontrivial one. -/
noncomputable def fourier {d : ℕ} (χ : AddChar F ℂ) (μ : Space F d → ℝ)
    (ξ : Space F d) : ℂ :=
  ∑ x, χ (-(dot ξ x)) * (μ x : ℂ)

open Finset

private def pushWeight {A B : Type*} [Fintype A] [DecidableEq B]
    (p : A → B) (w : A → ℝ) (b : B) : ℝ :=
  ∑ a with p a = b, w a

private lemma sum_pushWeight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → B) (w : A → ℝ) : ∑ b, pushWeight p w b = ∑ a, w a :=
  Finset.sum_fiberwise univ p w

private lemma sum_mul_pushWeight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → B) (w : A → ℝ) (g : B → ℂ) :
    ∑ b, g b * (pushWeight p w b : ℂ) = ∑ a, g (p a) * (w a : ℂ) := by
  simp only [pushWeight, Complex.ofReal_sum, mul_sum]
  rw [← Finset.sum_fiberwise univ p (fun a => g (p a) * (w a : ℂ))]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]

-- A nonzero linear functional has a kernel of index q.
private lemma card_perpendicular [DecidableEq F] {d : ℕ} {ξ : Space F d} (hξ : ξ ≠ 0) :
    (univ.filter (fun x => dot ξ x = 0)).card * Fintype.card F = Fintype.card (Space F d) := by
  let L : Space F d →+ F := (dotProductBilin F F ξ).toAddMonoidHom
  have hs : Function.Surjective L := by
    obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by simpa [funext_iff] using hξ
    intro a
    refine ⟨Pi.single i (a / ξ i), ?_⟩
    change ξ ⬝ᵥ Pi.single i (a / ξ i) = a
    rw [dotProduct_single]
    field_simp
  have hc := AddSubgroup.card_ker_mul_card_of_surjective hs
  simp only [Nat.card_eq_fintype_card] at hc
  rw [← Fintype.card_subtype]
  exact hc

private lemma line_sum_norm [DecidableEq F] {d : ℕ} (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (ξ y x : Space F d) :
    ‖∑ a : F, χ (-dot ξ (y + a • x))‖ =
      if dot ξ x = 0 then (Fintype.card F : ℝ) else 0 := by
  change ‖∑ a : F, χ (-(ξ ⬝ᵥ (y + a • x)))‖ = _
  simp_rw [dotProduct_add, dotProduct_smul, smul_eq_mul, neg_add, ← mul_neg,
    AddChar.map_add_eq_mul, ← Finset.mul_sum, AddChar.sum_mulShift _ hχ]
  by_cases h : dot ξ x = 0 <;> simp_all [dot, dotProduct]

private lemma upper_bound {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (χ : AddChar F ℂ) (hχ : χ ≠ 1) :
    ∃ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ ∧
      ∀ ξ : Space F d, ξ ≠ 0 → ‖fourier χ μ ξ‖ ≤ (Fintype.card F : ℝ)⁻¹ := by
  classical
  -- Choose one line for every vector, including the singleton for the zero vector.
  choose y hy using hK
  let p (v : Space F d × F) := y v.1 + v.2 • v.1
  let n : ℝ := Fintype.card (Space F d × F)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let w (_ : Space F d × F) := n⁻¹
  refine ⟨pushWeight p w, ⟨fun b => sum_nonneg fun _ _ => inv_nonneg.mpr hn.le, ?_, ?_⟩, ?_⟩
  · rw [sum_pushWeight]
    simp only [w, sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  · intro b hb
    by_contra h
    apply hb
    apply sum_eq_zero
    intro v hv
    exact (h ((mem_filter.mp hv).2 ▸ hy v.1 ⟨v.2, rfl⟩)).elim
  intro ξ hξ
  have hperp := card_perpendicular hξ
  have hcount : ((univ.filter (fun x => dot ξ x = 0)).card : ℝ) * Fintype.card F =
      (Fintype.card (Space F d) : ℝ) := by exact_mod_cast hperp
  rw [fourier, sum_mul_pushWeight]
  simp only [w, ← sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ (∑ x : Space F d, ‖∑ a : F, χ (-dot ξ (p (x, a)))‖) * n⁻¹ :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = (Fintype.card (Space F d) : ℝ) * n⁻¹ := by
      simp only [p, line_sum_norm χ (.of_ne_one hχ), ← sum_filter, sum_const, nsmul_eq_mul,
        hcount]
    _ = (Fintype.card F : ℝ)⁻¹ := by
      dsimp [n]
      rw [Fintype.card_prod, Nat.cast_mul]
      field_simp

-- Fixing one root m gives the line of slope m in the sum/product plane.
private def coefficients : Sym2 F → F × F :=
  Sym2.lift ⟨fun a b => (a + b, a * b), fun a b => Prod.ext (add_comm a b) (mul_comm a b)⟩

private def planeSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (F × F) :=
  univ.image coefficients ∪ univ.image (fun t : F => (0, t))

private lemma planeSet_card [DecidableEq F] :
    2 * (planeSet F).card ≤ Fintype.card F * (Fintype.card F + 3) := by
  have h : (planeSet F).card ≤ Fintype.card (Sym2 F) + Fintype.card F :=
    (card_union_le _ _).trans (add_le_add (card_image_le.trans_eq card_univ)
      (card_image_le.trans_eq card_univ))
  rw [Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel] at h
  nlinarith [Nat.div_mul_le_self ((Fintype.card F + 1) * Fintype.card F) 2]

private lemma cylinder_kakeya [DecidableEq F] {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    IsKakeya {x : Space F d | (x i, x j) ∈ planeSet F} := by
  intro v
  by_cases hi : v i = 0
  · refine ⟨0, ?_⟩
    rintro _ ⟨a, rfl⟩
    apply mem_union_right
    exact mem_image.mpr ⟨a * v j, mem_univ _, by simp [hi]⟩
  let m := v j / v i
  have hm : m * v i = v j := div_mul_cancel₀ _ hi
  refine ⟨Pi.single j (-(m * m)), ?_⟩
  rintro _ ⟨a, rfl⟩
  apply mem_union_left
  refine mem_image.mpr ⟨s(m, a * v i - m), mem_univ _, ?_⟩
  change (m + (a * v i - m), m * (a * v i - m)) = _
  apply Prod.ext
  · simp [Pi.single_eq_of_ne hij]
  · simp
    linear_combination a * hm

omit [Fintype F] in
private lemma lift_character [Finite F] {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) (ψ : AddChar (F × F) ℂ) (hψ : ψ ≠ 1) :
    ∃ ξ : Space F d, ξ ≠ 0 ∧ ∀ x, χ (-dot ξ x) = ψ (x i, x j) := by
  let _ := Fintype.ofFinite F
  have hs : Function.Surjective χ.mulShift :=
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hχ, AddChar.card_eq.symm⟩).surjective
  obtain ⟨a, ha⟩ := hs (ψ.compAddMonoidHom (AddMonoidHom.inl F F))
  obtain ⟨b, hb⟩ := hs (ψ.compAddMonoidHom (AddMonoidHom.inr F F))
  have hp (u v : F) : χ (a * u + b * v) = ψ (u, v) := by
    rw [AddChar.map_add_eq_mul, ← AddChar.mulShift_apply, ← AddChar.mulShift_apply, ha, hb]
    change ψ (u, 0) * ψ (0, v) = ψ (u, v)
    rw [← AddChar.map_add_eq_mul]
    simp
  refine ⟨Pi.single i (-a) + Pi.single j (-b), ?_, fun x => ?_⟩
  · intro h
    have ha0 : a = 0 := by simpa [Pi.single_eq_of_ne hij] using congrFun h i
    have hb0 : b = 0 := by simpa [Pi.single_eq_of_ne hij.symm] using congrFun h j
    apply hψ
    ext ⟨u, v⟩
    simpa [ha0, hb0] using (hp u v).symm
  · change χ (-((Pi.single i (-a) + Pi.single j (-b)) ⬝ᵥ x)) = _
    simpa [add_dotProduct, single_dotProduct, add_comm] using hp (x i) (x j)

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted
open MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

private lemma large_coefficient {S : Finset (F × F)} (ν : F × F → ℝ)
    (hν : ∑ x, ν x = 1) (hs : ∀ x ∉ S, ν x = 0) {κ : ℝ}
    (hsize : S.card * (1 + κ ^ 2) < (Fintype.card F : ℝ) ^ 2) :
    ∃ ψ : AddChar (F × F) ℂ, ψ ≠ 1 ∧
      κ * (Fintype.card F : ℝ)⁻¹ ≤ ‖dftFun (fun x => (ν x : ℂ)) ψ‖ := by
  classical
  let q : ℝ := Fintype.card F
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  let T := dftFun (fun x => (ν x : ℂ))
  have hT : T 1 = 1 := by simp [T, dftFun, ← Complex.ofReal_sum, hν]
  by_contra! h
  -- Separate the unit Fourier coefficient from the small nontrivial coefficients.
  have henergy : ∑ ψ, ‖T ψ‖ ^ 2 ≤ 1 + κ ^ 2 := by
    have hpoint (ψ : AddChar (F × F) ℂ) : ‖T ψ‖ ^ 2 ≤
        (if ψ = 1 then 1 else 0) + (κ * q⁻¹) ^ 2 := by
      split_ifs with he
      · simp [he, hT, sq_nonneg]
      · simp only [zero_add]
        exact pow_le_pow_left₀ (norm_nonneg _) (h ψ he).le 2
    calc
      _ ≤ ∑ ψ, ((if ψ = 1 then 1 else 0) + (κ * q⁻¹) ^ 2) :=
        sum_le_sum fun ψ _ => hpoint ψ
      _ = 1 + κ ^ 2 := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
          AddChar.card_eq, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
        change 1 + q * q * (κ * q⁻¹) ^ 2 = _
        field_simp
  have hp : ∑ ψ, ‖T ψ‖ ^ 2 = q ^ 2 * ∑ x, ν x ^ 2 := by
    dsimp only [T]
    rw [sum_norm_sq_dftFun]
    simp [q, pow_two]
  have hmass : ∑ x ∈ S, ν x = 1 := by
    rw [← hν]
    exact sum_subset (subset_univ _) fun x _ hx => hs x hx
  have hcs : 1 ≤ (S.card : ℝ) * ∑ x, ν x ^ 2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s := S) (f := ν)
    rw [hmass, one_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => sq_nonneg (ν x)))
      (Nat.cast_nonneg _))
  rw [hp] at henergy
  change (S.card : ℝ) * (1 + κ ^ 2) < q ^ 2 at hsize
  nlinarith [mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg S.card),
    mul_le_mul_of_nonneg_left hcs (sq_nonneg q)]

private lemma sharp_bound {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1) :
    ∃ Q : ℕ, ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F →
        ∃ K : Set (Space F d), IsKakeya K ∧
          ∀ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ →
            ∃ ξ : Space F d, ξ ≠ 0 ∧
              κ * (Fintype.card F : ℝ)⁻¹ ≤
                ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F) μ ξ‖ := by
  have hgap : 0 < 1 - κ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hκ') (by linarith : 0 < 1 + κ)]
  obtain ⟨Q, hQ⟩ := exists_nat_gt (3 * (1 + κ ^ 2) / (1 - κ ^ 2))
  refine ⟨Q, fun F _ _ _ hq => ?_⟩
  classical
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let p (x : Space F d) := (x i, x j)
  refine ⟨{x | p x ∈ planeSet F}, cylinder_kakeya hij, fun μ hμ => ?_⟩
  let q : ℝ := Fintype.card F
  have hqpos : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hlarge : 3 * (1 + κ ^ 2) < q * (1 - κ ^ 2) :=
    (div_lt_iff₀ hgap).mp (hQ.trans_le (Nat.cast_le.mpr hq))
  have hc : 2 * ((planeSet F).card : ℝ) ≤ q * (q + 3) := by
    dsimp [q]
    exact_mod_cast planeSet_card (F := F)
  have hsize : (planeSet F).card * (1 + κ ^ 2) < q ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hlarge hqpos,
      mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 1 + κ ^ 2)]
  let ν := pushWeight p μ
  have hν : ∑ z, ν z = 1 := (sum_pushWeight p μ).trans hμ.2.1
  have hs (z : F × F) (hz : z ∉ planeSet F) : ν z = 0 := by
    apply sum_eq_zero
    intro x hx
    exact not_ne_iff.mp fun h => hz ((mem_filter.mp hx).2 ▸ hμ.2.2 x h)
  obtain ⟨ψ, hψ, hψκ⟩ := large_coefficient ν hν hs hsize
  let χ := AddChar.FiniteField.primitiveChar_to_Complex F
  obtain ⟨ξ, hξ, heval⟩ := lift_character hij χ
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F) ψ hψ
  refine ⟨ξ, hξ, ?_⟩
  have htransform : dftFun (fun z => (ν z : ℂ)) ψ = fourier χ μ ξ := by
    rw [dftFun, fourier, sum_mul_pushWeight p μ]
    exact sum_congr rfl fun x _ => by rw [heval x]
  rwa [← htransform]

set_option linter.dupNamespace false in
/-- **Fraser's Fourier decay theorem for finite-field Kakeya sets.** Let $F$ be a finite field
with $q$ elements, let $d \ge 2$ be a natural number, let $K \subseteq F^d$ be a Kakeya set and let
$\chi$ be a nontrivial additive character of $F$ with values in $\mathbb{C}$. Then, first, there is
a probability measure $\mu$ on $K$ whose Fourier transform $\hat{\mu}$ with respect to $\chi$
satisfies $|\hat{\mu}(\xi)| \le q^{-1}$ for every nonzero $\xi \in F^d$. Second, this bound is
sharp: for every real $\kappa$ with $0 < \kappa < 1$ there is a natural number $Q$ such that for
every finite field $F'$ with $q' \ge Q$ elements there is a Kakeya set $K' \subseteq (F')^d$ such
that every probability measure $\mu$ on $K'$ has a nonzero $\xi \in (F')^d$ at which its Fourier
transform $\hat{\mu}$ with respect to a fixed primitive additive character of $F'$ satisfies
$|\hat{\mu}(\xi)| \ge \kappa \, q'^{-1}$.

Source: J.M. Fraser, 'Fourier analytic properties of Kakeya sets in finite fields', Bull. London
Math. Soc. 58(5) (2026); DOI 10.1112/blms.70367; arXiv:2505.09464. Via leanprover/lean-eval@38361be,
problem `fraser_kakeya_fourier_decay`. -/
public theorem fraser_kakeya_fourier_decay_and_sharp
    {d : ℕ} (_hd : 2 ≤ d) {K : Set (Space F d)} (_hK : IsKakeya K)
    (χ : AddChar F ℂ) (_hχ : χ ≠ 1) :
    (∃ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ ∧
      ∀ ξ : Space F d, ξ ≠ 0 →
        ‖fourier χ μ ξ‖ ≤ (Fintype.card F : ℝ)⁻¹) ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 →
      ∃ Q : ℕ, ∀ (F' : Type*) [Field F'] [Fintype F'] [DecidableEq F'],
        Q ≤ Fintype.card F' →
          ∃ K' : Set (Space F' d), IsKakeya K' ∧
            ∀ μ : Space F' d → ℝ, IsProbabilityMeasureOn K' μ →
              ∃ ξ : Space F' d, ξ ≠ 0 ∧
                κ * (Fintype.card F' : ℝ)⁻¹ ≤
                  ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F') μ ξ‖) :=
  ⟨upper_bound _hK χ _hχ, fun _ hκ hκ' => sharp_bound _hd hκ hκ'⟩

end FraserKakeyaProblem
end Combinatorics

end MathlibExt.Combinatorics.FraserKakeyaWanted
