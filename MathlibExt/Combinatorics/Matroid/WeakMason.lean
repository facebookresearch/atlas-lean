/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/StrongMason.lean` (leanprover/lean-eval, revision 38361be):
the definition of the number of independent sets of a given size.
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison (lean-eval submission).
-/

module

public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Set.PowersetCard
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.MvPolynomial
import MathlibExt.Combinatorics.Matroid.IndependenceLorentzian

/-!
# Mason's conjecture: log-concavity of independent set numbers

K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of Math.
188 (2018), 381–452 (arXiv:1511.02888v2), Conjecture 1.2 and Theorem 9.9 (3): the numbers
`f_k(M)` of `k`-element independent sets of a matroid form a log-concave sequence (the
Welsh–Mason conjecture). The ultra log-concave strengthening is
`WantedExt.Combinatorics.StrongMasonWanted.strong_mason_conjecture`.

The proof uses the Lorentzian independence generating polynomial and the Hessian argument of
Anari, Liu, Oveis Gharan and Vinzant, *Log-concave polynomials III* (arXiv:1811.01600).
Evaluating at the boundary where the homogenising variable is zero isolates the three counts.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

set_option linter.dupNamespace false in
/-- **Number of independent sets of a given size.** For a finite matroid $M$ and a natural
number $k$, this is the number of independent sets of $M$ with exactly $k$ elements. -/
noncomputable def independentSetCount {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) : ℕ :=
  {I ∈ Set.powersetCard α k | M.Indep I}.ncard

end MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

end

namespace MathlibExt.Combinatorics.WeakMasonWanted

open Matrix Finset
open MathlibExt.Combinatorics.Matroid.MConvex (indicatorVec indicatorVec_apply)
open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

section

variable {ι : Type*} [Fintype ι]

private def bilinear {R : Type*} [CommSemiring R] (A : Matrix ι ι R) (u v : ι → R) : R :=
  u ⬝ᵥ (A *ᵥ v)

-- Expand a vector orthogonal to the common direction in a symmetric eigenvector basis.
private lemma nonpos_of_eigenvectors (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (t : ι → ℝ) (v : ι → ℝ) (hv : v ⬝ᵥ t = 0)
    (h : ∀ (a : ι → ℝ) (lam : ℝ), A *ᵥ a = lam • a → 0 < lam →
      ∃ c : ℝ, a = c • t) : bilinear A v v ≤ 0 := by
  classical
  let hH := Matrix.isHermitian_iff_isSymm.mpr hA
  let b := hH.eigenvectorBasis
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  let e : ι → ι → ℝ := fun j => ⇑(b j)
  let r : ι → ℝ := fun j => b.repr w j
  have hvsum : ∑ j, r j • e j = v := by
    have hsum := congrArg (WithLp.linearEquiv 2 ℝ (ι → ℝ))
      (b.sum_repr w)
    simpa [r, e, w] using hsum
  unfold bilinear
  rw [← hvsum, Matrix.mulVec_sum]
  rw [hvsum]
  rw [dotProduct_sum]
  apply Finset.sum_nonpos
  intro i _
  rw [Matrix.mulVec_smul, dotProduct_smul]
  have he : A *ᵥ e i = hH.eigenvalues i • e i := hH.mulVec_eigenvectorBasis i
  rw [he, dotProduct_smul]
  by_cases hi : 0 < hH.eigenvalues i
  · obtain ⟨c, hc⟩ := h (e i) _ he hi
    rw [hc, dotProduct_smul, hv]
    simp
  · have hd : v ⬝ᵥ e i = r i := by
      change v ⬝ᵥ ⇑(b i) = (b.repr w) i
      rw [OrthonormalBasis.repr_apply_apply]
      simpa [w] using (EuclideanSpace.inner_eq_star_dotProduct (b i) w).symm
    rw [hd]
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) (sq_nonneg (r i))
    simpa only [smul_eq_mul, pow_two, mul_assoc, mul_left_comm] using this

-- The quadratic inequality forces a positive eigenvalue to be at least one.
-- At a maximal signed ratio to the fixed vector, weighted averaging propagates equality
-- across every edge. The connectivity assumption then makes the ratio constant.
private lemma same_eigenvector_of_pos (B : Matrix ι ι ℝ) (t : ι → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (ht : ∀ i, 0 ≤ t i) (hBt : B *ᵥ t = t)
    (hzero : ∀ i, t i = 0 → ∀ j, B i j = 0)
    (hc : ∀ s : ι → Prop, (∃ i, 0 < t i ∧ s i) → (∃ i, 0 < t i ∧ ¬ s i) →
      ∃ i j, s i ∧ ¬ s j ∧ 0 < t j ∧ 0 < B i j)
    (hquad : ∀ a : ι → ℝ, bilinear B a a ≤ (B *ᵥ a) ⬝ᵥ (B *ᵥ a))
    (a : ι → ℝ) (lam : ℝ) (he : B *ᵥ a = lam • a) (hl : 0 < lam) :
    ∃ c : ℝ, a = c • t := by
  classical
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hnorm : 0 < a ⬝ᵥ a := by
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    simpa only [dotProduct, pow_two] using
      (Finset.sum_pos' (fun j (_ : j ∈ (univ : Finset ι)) => sq_nonneg (a j))
        ⟨i, mem_univ i, sq_pos_of_ne_zero hi⟩)
  have hlam : 1 ≤ lam := by
    have hh := hquad a
    dsimp [bilinear] at hh
    rw [he, smul_dotProduct, dotProduct_smul] at hh
    simp only [smul_eq_mul] at hh
    nlinarith [mul_pos hl hnorm]
  have ha0 (i : ι) (hi : t i = 0) : a i = 0 := by
    have hb : (B *ᵥ a) i = 0 := by simp [Matrix.mulVec, dotProduct, hzero i hi]
    have hmul : lam * a i = 0 := (congrFun he i).symm.trans hb
    exact (mul_eq_zero.mp hmul).resolve_left hl.ne'
  let r : ι → ℝ := fun i => a i / t i
  have har (i : ι) : a i = t i * r i := by
    by_cases hi : t i = 0
    · simp [hi, ha0 i hi]
    · dsimp [r]
      field_simp
  have hav (i : ι) : ∑ j, B i j * t j * r j = lam * t i * r i := by
    have hh := congrFun he i
    change ∑ j, B i j * a j = lam * a i at hh
    calc
      _ = ∑ j, B i j * a j := sum_congr rfl (fun j _ => by rw [har j]; ring)
      _ = _ := by rw [hh, har i]; ring
  have hst (i : ι) : ∑ j, B i j * t j = t i := congrFun hBt i
  have hmax (s : ℝ) (hsign : s = 1 ∨ s = -1) (i : ι)
      (hi : 0 < s * r i) (hi' : ∀ j, s * r j ≤ s * r i) :
      ∀ j, 0 < B i j → 0 < t j → r j = r i := by
    intro j hij hj
    have hsum : ∑ l, B i l * t l * (s * r i - s * r l) ≤ 0 := by
      simp only [mul_sub, sum_sub_distrib]
      have h₁ : ∑ l, (B i l * t l * (s * r i)) = t i * (s * r i) := by
        rw [← sum_mul, hst]
      have h₂ : ∑ l, (B i l * t l * (s * r l)) = s * (lam * t i * r i) := by
        rw [← hav, mul_sum]
        apply sum_congr rfl
        intro l _
        ring
      rw [h₁, h₂]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (mul_nonneg (ht i) hi.le)]
    have hterm : B i j * t j * (s * r i - s * r j) ≤ 0 :=
      (single_le_sum (fun l _ => mul_nonneg (mul_nonneg (hB i l) (ht l))
        (sub_nonneg.mpr (hi' l))) (mem_univ j)).trans hsum
    have hh := (nonpos_of_mul_nonpos_right hterm (mul_pos hij hj))
    rcases hsign with rfl | rfl <;> linarith [hi' j]
  have hnonzero : ∃ i, r i ≠ 0 := by
    by_contra! h
    exact ha (funext fun i => by simp [har i, h i])
  obtain ⟨j, hj⟩ := hnonzero
  have huniv : (univ : Finset ι).Nonempty := ⟨j, mem_univ j⟩
  have hprop (s : ℝ) (hsign : s = 1 ∨ s = -1) (hj : 0 < s * r j) :
      ∃ c : ℝ, a = c • t := by
    obtain ⟨i, -, hi⟩ := exists_max_image univ (fun l => s * r l) huniv
    have hi' (l : ι) : s * r l ≤ s * r i := hi l (mem_univ l)
    have hip : 0 < s * r i := hj.trans_le (hi' j)
    have hit : 0 < t i := by
      by_contra! h
      have hit0 := le_antisymm h (ht i)
      simp [r, hit0] at hip
    refine ⟨r i, funext fun l => ?_⟩
    by_cases hlt : 0 < t l
    · have hli : r l = r i := by
        by_contra hne
        obtain ⟨a, b, ha, hb, hbt, hab⟩ :=
          hc (fun j => r j = r i) ⟨i, hit, rfl⟩ ⟨l, hlt, hne⟩
        change r a = r i at ha
        change r b ≠ r i at hb
        apply hb
        rw [← ha]
        exact hmax s hsign a (by simpa only [ha] using hip)
          (fun j => by simpa only [ha] using hi' j) b hab hbt
      rw [har l, hli]
      exact mul_comm _ _
    · have hlt0 := le_antisymm (le_of_not_gt hlt) (ht l)
      simp [hlt0, ha0 l hlt0]
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact hprop (-1) (Or.inr rfl) (by linarith)
  · exact hprop 1 (Or.inl rfl) (by simpa using hj)


-- Normalize by the square roots of the row weights. Zero weights correspond to zero rows
-- and columns, so they contribute nothing to the quadratic form.
private lemma local_to_global (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (hn : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hc : ∀ s : ι → Prop, (∃ i, 0 < (A *ᵥ x) i ∧ s i) →
      (∃ i, 0 < (A *ᵥ x) i ∧ ¬ s i) →
      ∃ i j, s i ∧ ¬ s j ∧ 0 < (A *ᵥ x) j ∧ 0 < A i j)
    (hloc : ∀ u : ι → ℝ, bilinear A u u ≤
      ∑ i, (A *ᵥ u) i ^ 2 * x i / (A *ᵥ x) i)
    (v : ι → ℝ) (hv : bilinear A v x = 0) : bilinear A v v ≤ 0 := by
  let w : ι → ℝ := fun i => Real.sqrt ((A *ᵥ x) i / x i)
  let B : Matrix ι ι ℝ := fun i j => A i j / w i / w j
  let scale (u : ι → ℝ) : ι → ℝ := fun i => u i * w i
  let unscale (u : ι → ℝ) : ι → ℝ := fun i => u i / w i
  have hAx (i : ι) : 0 ≤ (A *ᵥ x) i :=
    sum_nonneg fun j _ => mul_nonneg (hn i j) (hx j).le
  have hw (i : ι) : 0 ≤ w i := Real.sqrt_nonneg _
  have hw2 (i : ι) : w i ^ 2 = (A *ᵥ x) i / x i :=
    Real.sq_sqrt (div_nonneg (hAx i) (hx i).le)
  have hwAx (i : ι) : (A *ᵥ x) i = x i * w i ^ 2 := by
    rw [hw2]
    rw [mul_div_cancel₀ _ (hx i).ne']
  have hzero (i : ι) (hi : w i = 0) (j : ι) : A i j = 0 := by
    have hi' : (A *ᵥ x) i = 0 := by simp [hwAx i, hi]
    have hle : A i j * x j ≤ (A *ᵥ x) i :=
      single_le_sum (fun l _ => mul_nonneg (hn i l) (hx l).le) (mem_univ j)
    exact le_antisymm (nonpos_of_mul_nonpos_left (hi' ▸ hle) (hx j)) (hn i j)
  have hsym : B.IsSymm := by
    ext i j
    change A j i / w j / w i = A i j / w i / w j
    rw [hA.apply i j]
    ring
  have hBn (i j : ι) : 0 ≤ B i j := div_nonneg (div_nonneg (hn i j) (hw i)) (hw j)
  have hmul (u : ι → ℝ) (i : ι) : (B *ᵥ u) i = (A *ᵥ unscale u) i / w i := by
    change ∑ j, A i j / w i / w j * u j = (∑ j, A i j * (u j / w j)) / w i
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    ring
  have hform (u : ι → ℝ) : bilinear B u u = bilinear A (unscale u) (unscale u) := by
    unfold bilinear dotProduct
    apply sum_congr rfl
    intro i _
    rw [hmul]
    dsimp [unscale]
    ring
  have hcscale (u : ι → ℝ) : A *ᵥ unscale (scale u) = A *ᵥ u := by
    funext i
    apply sum_congr rfl
    intro j _
    change A i j * unscale (scale u) j = A i j * u j
    by_cases hj : w j = 0
    · rw [← hA.apply i j, hzero j hj i, zero_mul, zero_mul]
    · simp [scale, unscale, hj]
  have hback (u : ι → ℝ) : bilinear B (scale u) (scale u) = bilinear A u u := by
    rw [hform]
    change (∑ i, unscale (scale u) i * (A *ᵥ unscale (scale u)) i) = _
    rw [hcscale]
    apply sum_congr rfl
    intro i _
    by_cases hi : w i = 0
    · have hz : (A *ᵥ u) i = 0 := by simp [Matrix.mulVec, dotProduct, hzero i hi]
      rw [hz, mul_zero, mul_zero]
    · simp [scale, unscale, hi]
  have horth : scale v ⬝ᵥ scale x = 0 := by
    rw [← hv]
    apply sum_congr rfl
    intro i _
    change v i * w i * (x i * w i) = v i * (A *ᵥ x) i
    rw [hwAx i]
    ring
  have hBt : B *ᵥ scale x = scale x := by
    funext i
    rw [hmul, hcscale, hwAx]
    change x i * w i ^ 2 / w i = x i * w i
    by_cases hi : w i = 0
    · simp [hi]
    · field_simp
  have hBquad (u : ι → ℝ) : bilinear B u u ≤ (B *ᵥ u) ⬝ᵥ (B *ᵥ u) := by
    rw [hform]
    apply (hloc (unscale u)).trans_eq
    apply sum_congr rfl
    intro i _
    rw [hmul, hwAx]
    by_cases hi : w i = 0
    · simp [hi]
    · field_simp [(hx i).ne']
  rw [← hback]
  apply nonpos_of_eigenvectors B hsym (scale x) _ horth
  apply same_eigenvector_of_pos B (scale x) hBn (fun i => mul_nonneg (hx i).le (hw i))
    hBt ?_ ?_ hBquad
  · intro i hi j
    have hwi : w i = 0 := (mul_eq_zero.mp hi).resolve_left (hx i).ne'
    simp [B, hwi]
  · intro s h₁ h₂
    have ht (i : ι) : 0 < scale x i ↔ 0 < (A *ᵥ x) i := by
      rw [hwAx]
      change 0 < x i * w i ↔ 0 < x i * w i ^ 2
      rw [mul_pos_iff_of_pos_left (hx i), mul_pos_iff_of_pos_left (hx i)]
      exact ⟨fun h => pow_pos h _, fun h => (hw i).lt_of_ne
        (fun hz => by simp [← hz] at h)⟩
    obtain ⟨i, j, hi, hj, hjpos, hij⟩ := hc s
      (by simpa only [ht] using h₁) (by simpa only [ht] using h₂)
    have posWeight (a b : ι) (hab : 0 < A a b) : 0 < w a := by
      by_contra! h
      rw [hzero a (le_antisymm h (hw a)) b] at hab
      exact (lt_irrefl 0) hab
    exact ⟨i, j, hi, hj, (ht j).mpr hjpos, div_pos (div_pos hij (posWeight i j hij))
      (posWeight j i (hA.apply i j ▸ hij))⟩


open Finsupp MvPolynomial UpperHalfPlane
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials

private noncomputable def hessian (f : MvPolynomial ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => eval x (pderiv i (pderiv j f))

omit [Fintype ι] in
private lemma hessian_symm (f : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (hessian f x).IsSymm :=
  Matrix.IsSymm.ext_iff.mpr fun i j => congrArg (eval x) (pderiv_comm j i f)

omit [Fintype ι] in
private lemma eval_nonneg_of_coeff {f : MvPolynomial ι ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x f := by
  rw [eval_eq]
  exact sum_nonneg fun m _ => mul_nonneg (hf m) (prod_nonneg fun i _ => pow_nonneg (hx i) _)

omit [Fintype ι] in
private lemma eval_pos_of_coeff {f : MvPolynomial ι ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) {m : ι →₀ ℕ} (hm : 0 < f.coeff m) :
    0 < eval x f := by
  rw [eval_eq]
  exact sum_pos' (fun m _ => mul_nonneg (hf m)
    (prod_nonneg fun i _ => pow_nonneg (hx i).le _))
    ⟨m, MvPolynomial.mem_support_iff.mpr hm.ne', mul_pos hm (prod_pos fun i _ => pow_pos (hx i) _)⟩

omit [Fintype ι] in
private lemma pderiv_coeff_nonneg {f : MvPolynomial ι ℝ} (hf : ∀ m, 0 ≤ f.coeff m) (i : ι)
    (m : ι →₀ ℕ) : 0 ≤ (pderiv i f).coeff m := by
  rw [coeff_pderiv]
  exact mul_nonneg (hf _) (by positivity)

omit [Fintype ι] in
private lemma hessian_nonneg {f : MvPolynomial ι ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i j : ι) : 0 ≤ hessian f x i j :=
  eval_nonneg_of_coeff (pderiv_coeff_nonneg (pderiv_coeff_nonneg hf j) i) hx

omit [Fintype ι] in
private lemma hessian_pos_of_monomial {f : MvPolynomial ι ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) {m : ι →₀ ℕ} (hm : m ∈ f.support)
    {i j : ι} (hij : i ≠ j) (hi : 0 < m i) (hj : 0 < m j) : 0 < hessian f x i j := by
  classical
  change 0 < eval x (pderiv i (pderiv j f))
  let a := m - Finsupp.single j 1
  let b := a - Finsupp.single i 1
  have ha : a + Finsupp.single j 1 = m := sub_add_single_one_cancel hj.ne'
  have hab : b + Finsupp.single i 1 = a :=
    sub_add_single_one_cancel (by simpa [a, Finsupp.tsub_apply, Ne.symm hij] using hi.ne')
  apply eval_pos_of_coeff (pderiv_coeff_nonneg (pderiv_coeff_nonneg hf j) i) hx (m := b)
  rw [coeff_pderiv, coeff_pderiv, hab, ha]
  have h := lt_of_le_of_ne (hf m) (Ne.symm (MvPolynomial.mem_support_iff.mp hm))
  positivity

private lemma active_monomial {f : MvPolynomial ι ℝ} {x : ι → ℝ} {i : ι}
    (hi : 0 < (hessian f x *ᵥ x) i) : ∃ m ∈ f.support, 0 < m i := by
  by_contra! h
  have hd : pderiv i f = 0 := by
    ext m
    rw [coeff_pderiv]
    change _ = 0
    have ha : 0 < ((m + Finsupp.single i 1 : ι →₀ ℕ)) i := by simp
    have hb := MvPolynomial.notMem_support_iff.mp (fun hm => (h _ hm).not_gt ha)
    rw [hb, zero_mul]
  have hz : ∀ j, hessian f x i j = 0 := by
    intro j
    simp [hessian, pderiv_comm i j f, hd]
  simp [Matrix.mulVec, dotProduct, hz] at hi

-- At a positive point, each monomial containing two variables gives a Hessian edge.
-- If a partition separated the graph, an M-convex exchange between monomials on its
-- two sides would produce a monomial containing variables on both sides.
private lemma hessian_connected {d : ℕ} {f : MvPolynomial ι ℝ} (hdeg : f.IsHomogeneous d)
    (hd : 2 ≤ d) (hf : ∀ m, 0 ≤ f.coeff m)
    (hm : MathlibExt.Combinatorics.Matroid.MConvex.IsMConvex (f.support : Set (ι →₀ ℕ)))
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) (s : ι → Prop)
    (h₁ : ∃ i, 0 < (hessian f x *ᵥ x) i ∧ s i)
    (h₂ : ∃ i, 0 < (hessian f x *ᵥ x) i ∧ ¬ s i) :
    ∃ i j, s i ∧ ¬ s j ∧ 0 < (hessian f x *ᵥ x) j ∧ 0 < hessian f x i j := by
  classical
  by_contra h
  have hsplit {m : ι →₀ ℕ} (hm : m ∈ f.support) {i j : ι} (hi : 0 < m i) (hj : 0 < m j)
      (hsi : s i) (hsj : ¬ s j) : False := by
    have hij : i ≠ j := fun he => hsj (he ▸ hsi)
    have hp := hessian_pos_of_monomial hf hx hm hij hi hj
    apply h
    refine ⟨i, j, hsi, hsj, ?_, hp⟩
    have hp' : 0 < hessian f x j i := by rwa [(hessian_symm f x).apply]
    exact sum_pos' (fun l _ => mul_nonneg (hessian_nonneg hf (fun a => (hx a).le) j l)
      (hx l).le) ⟨i, mem_univ i, mul_pos hp' (hx i)⟩
  obtain ⟨i, hi, hsi⟩ := h₁
  obtain ⟨j, hj, hsj⟩ := h₂
  obtain ⟨a, ha, hai⟩ := active_monomial hi
  obtain ⟨b, hb, hbj⟩ := active_monomial hj
  have hasa (r : ι) (hr : 0 < a r) : s r := by
    by_contra hsr
    exact hsplit ha hai hr hsi hsr
  have hbsb (r : ι) (hr : 0 < b r) : ¬ s r := fun hsr => hsplit hb hr hbj hsr hsj
  have hbi : b i = 0 := by
    by_contra hbi
    exact hbsb i (Nat.pos_of_ne_zero hbi) hsi
  obtain ⟨r, hbr, hr⟩ := hm a ha b hb i (by simpa [hbi] using hai)
  have hrs := hbsb r (Nat.zero_le _ |>.trans_lt hbr)
  have hleft : a - Finsupp.single i 1 ≠ 0 := by
    intro he
    have hsi' : a = Finsupp.single i 1 := by
      have hh := sub_add_single_one_cancel hai.ne'
      simpa [he] using hh.symm
    have hda := hdeg (MvPolynomial.mem_support_iff.mp ha)
    rw [show (1 : ι → ℕ) = fun _ => 1 from rfl, ← degree_eq_weight_one, hsi',
      Finsupp.degree_single] at hda
    omega
  obtain ⟨l, hl⟩ : ∃ l, 0 < ((a - Finsupp.single i 1 : ι →₀ ℕ)) l := by
    by_contra! h
    exact hleft (Finsupp.ext fun l => Nat.eq_zero_of_le_zero (h l))
  have hla : 0 < a l := hl.trans_le (by rw [Finsupp.tsub_apply]; exact tsub_le_self)
  exact hsplit hr (by simp only [Finsupp.add_apply]; omega)
    (by simp only [Finsupp.add_apply, single_eq_same]; omega) (hasa l hla) hrs

private lemma eval_euler {K : Type*} [CommSemiring K] [Algebra ℝ K]
    {f : MvPolynomial ι ℝ} {d : ℕ} (hd : f.IsHomogeneous d) (z : ι → K) :
    ∑ i, z i * aeval z (pderiv i f) = (d : K) * aeval z f := by
  simpa only [map_sum, map_mul, aeval_X, map_nsmul, nsmul_eq_mul, map_natCast] using
    congrArg (aeval z) hd.sum_X_mul_pderiv

private lemma hessian_mulVec {f : MvPolynomial ι ℝ} {d : ℕ} (hd : f.IsHomogeneous d)
    (x : ι → ℝ) (i : ι) :
    (hessian f x *ᵥ x) i = (↑(d - 1) : ℝ) * eval x (pderiv i f) := by
  change ∑ j, eval x (pderiv i (pderiv j f)) * x j = _
  simpa only [pderiv_comm i _, mul_comm _ (x _), aeval_eq_eval] using
    eval_euler (hd.pderiv (i := i)) x

private lemma hessian_at_quadratic {n : ℕ} {f : MvPolynomial (Fin n) ℝ} (hf : f.IsHomogeneous 2)
    (x : Fin n → ℝ) (z : Fin n → ℂ) :
    ∑ i, ∑ j, (hessian f x i j : ℂ) * z i * z j = 2 * aeval z f := by
  have hc (i j : Fin n) : aeval z (pderiv i (pderiv j f)) = (hessian f x i j : ℂ) := by
    have hd : (pderiv i (pderiv j f)).IsHomogeneous 0 := hf.pderiv.pderiv
    have hdegree : (pderiv i (pderiv j f)).totalDegree = 0 := by
      rwa [totalDegree_zero_iff_isHomogeneous]
    have h := totalDegree_eq_zero_iff_eq_C.mp hdegree
    change aeval z (pderiv i (pderiv j f)) = (eval x (pderiv i (pderiv j f)) : ℂ)
    rw [h, aeval_C, eval_C]
    rfl
  have he (i : Fin n) : ∑ j, z j * (hessian f x i j : ℂ) = aeval z (pderiv i f) := by
    simpa only [← hc, pderiv_comm i _, Nat.cast_one, one_mul] using
      eval_euler (show (pderiv i f).IsHomogeneous 1 from hf.pderiv) z
  calc
    _ = ∑ i, z i * (∑ j, z j * (hessian f x i j : ℂ)) := by
      simp only [Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [he]
      simpa using eval_euler hf z


private lemma bilinear_add_left {R : Type*} [CommSemiring R]
    (A : Matrix ι ι R) (u v w : ι → R) :
    bilinear A (u + v) w = bilinear A u w + bilinear A v w :=
  add_dotProduct _ _ _

private lemma bilinear_add_right {R : Type*} [CommSemiring R]
    (A : Matrix ι ι R) (u v w : ι → R) :
    bilinear A u (v + w) = bilinear A u v + bilinear A u w := by
  simp only [bilinear, mulVec_add, dotProduct_add]

private lemma bilinear_smul_left {R : Type*} [CommSemiring R]
    (A : Matrix ι ι R) (c : R) (u v : ι → R) :
    bilinear A (c • u) v = c * bilinear A u v :=
  smul_dotProduct _ _ _

private lemma bilinear_smul_right {R : Type*} [CommSemiring R]
    (A : Matrix ι ι R) (c : R) (u v : ι → R) :
    bilinear A u (c • v) = c * bilinear A u v := by
  simp only [bilinear, mulVec_smul, dotProduct_smul, smul_eq_mul]

-- A positive quadratic value on the orthogonal hyperplane would yield a zero at a point
-- with positive imaginary part, by scaling the real part to cancel the imaginary part's value.
private lemma stable_quadratic_nonpos {n : ℕ} (f : H n 2)
    (hf : IsStable f.1) (hn : ∀ m, 0 ≤ f.1.coeff m)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (v : Fin n → ℝ)
    (hv : bilinear (hessian f.1 x) v x = 0) : bilinear (hessian f.1 x) v v ≤ 0 := by
  rcases hf with hf | hf
  · simp [bilinear, hessian, hf, Matrix.mulVec, dotProduct]
  by_contra! hpos
  let A := hessian f.1 x
  have hnA := hessian_nonneg hn (fun i => (hx i).le)
  have hqx : 0 ≤ bilinear A x x := by
    change 0 ≤ ∑ i, x i * (∑ j, A i j * x j)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hx i).le
      (Finset.sum_nonneg fun j _ => mul_nonneg (hnA i j) (hx j).le)
  let r := Real.sqrt (bilinear A x x / bilinear A v v)
  have hsq : r ^ 2 * bilinear A v v = bilinear A x x := by
    rw [Real.sq_sqrt (div_nonneg hqx hpos.le), div_mul_cancel₀ _ hpos.ne']
  let z : Fin n → ℍ := fun i => ⟨(r * v i : ℝ) + x i * Complex.I, by simpa using hx i⟩
  let v' : Fin n → ℂ := Complex.ofReal ∘ v
  let x' : Fin n → ℂ := Complex.ofReal ∘ x
  let A' := A.map Complex.ofReal
  let z' : Fin n → ℂ := (r : ℂ) • v' + Complex.I • x'
  have hz : ((↑) : ℍ → ℂ) ∘ z = z' := by
    ext i : 1
    simp [z, z', v', x', mul_comm (x i : ℂ) Complex.I]
  have hmap (a b : Fin n → ℝ) :
      ((bilinear A a b : ℝ) : ℂ) = bilinear A' (Complex.ofReal ∘ a) (Complex.ofReal ∘ b) := by
    change Complex.ofRealHom (a ⬝ᵥ A *ᵥ b) = _
    rw [RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec Complex.ofRealHom A b i
  have hzero : bilinear A' z' z' = 0 := by
    have hv' : bilinear A x v = 0 := (hessian_symm f.1 x).dotProduct_mulVec_comm.trans hv
    have hsq' : (r : ℂ) ^ 2 * ((bilinear A v v : ℝ) : ℂ) = ((bilinear A x x : ℝ) : ℂ) := by
      exact_mod_cast hsq
    dsimp only [z']
    rw [bilinear_add_left, bilinear_add_right, bilinear_add_right]
    simp only [bilinear_smul_left, bilinear_smul_right]
    rw [← hmap v v, ← hmap v x, ← hmap x v, ← hmap x x, hv, hv']
    push_cast
    linear_combination hsq' + ((bilinear A x x : ℝ) : ℂ) * Complex.I_sq
  have he := hessian_at_quadratic f.2 x z'
  have hsum : (∑ i, ∑ j, (hessian f.1 x i j : ℂ) * z' i * z' j) = bilinear A' z' z' := by
    rw [bilinear, dot_mulVec_eq_sum_sum, Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    change A' j i * z' j * z' i = z' j * A' j i * z' i
    rw [mul_comm (A' j i)]
  rw [hsum, hzero] at he
  apply hf z
  rw [hz]
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

private lemma reverse_cauchy_div (A : Matrix ι ι ℝ) (hA : A.IsSymm) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hn : ∀ i j, 0 ≤ A i j)
    (h : ∀ v, bilinear A v x = 0 → bilinear A v v ≤ 0) (v : ι → ℝ) :
    bilinear A v v ≤ bilinear A v x ^ 2 / bilinear A x x := by
  have hAx (i : ι) : 0 ≤ (A *ᵥ x) i :=
    sum_nonneg fun j _ => mul_nonneg (hn i j) (hx j).le
  have hnonneg : 0 ≤ bilinear A x x :=
    sum_nonneg fun i _ => mul_nonneg (hx i).le (hAx i)
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have hz : A *ᵥ x = 0 := by
      ext i
      have hm : x i * (A *ᵥ x) i = 0 := (sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hx i).le (hAx i))).mp hzero.symm i (mem_univ i)
      exact (mul_eq_zero.mp hm).resolve_left (hx i).ne'
    have hv : bilinear A v x = 0 := by simp [bilinear, hz]
    simpa [hzero.symm] using h v hv
  · let c := -(bilinear A v x / bilinear A x x)
    have hc : c * bilinear A x x = -bilinear A v x := by dsimp [c]; field_simp
    have horth : bilinear A (v + c • x) x = 0 := by
      rw [bilinear_add_left, bilinear_smul_left, hc, add_neg_cancel]
    have hbound := h _ horth
    simp only [bilinear_add_left, bilinear_add_right, bilinear_smul_left, bilinear_smul_right]
      at hbound
    have hsym : bilinear A x v = bilinear A v x := hA.dotProduct_mulVec_comm
    rw [hsym, hc, add_neg_cancel, mul_zero, add_zero] at hbound
    have hratio : c * bilinear A v x = -(bilinear A v x ^ 2 / bilinear A x x) := by
      dsimp [c]
      ring
    rw [hratio] at hbound
    linarith


-- Euler's identity expresses the Hessian as a weighted sum of its coordinate derivatives.
-- The quadratic estimates on those derivatives give the local-to-global hypothesis.
private lemma lorentzian_hessian_nonpos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ (d : ℕ) (f : H n (d + 2)), f ∈ L n (d + 2) →
      ∀ v, bilinear (hessian f.1 x) v x = 0 → bilinear (hessian f.1 x) v v ≤ 0 := by
  intro d
  induction d with
  | zero =>
    intro f hf
    exact stable_quadratic_nonpos f hf.1 hf.2 x hx
  | succ d ih =>
    intro f hf v hv
    change f ∈ L n (d + 3) at hf
    obtain ⟨⟨hconv, hcoeff⟩, hpartial⟩ := hf
    let A := hessian f.1 x
    let D (i : Fin n) : H n (d + 2) := ⟨pderiv i f.1, f.2.pderiv⟩
    let B (i : Fin n) := hessian (D i).1 x
    let c : ℝ := (d : ℝ) + 1
    have hc : 0 < c := by dsimp [c]; positivity
    have hsym : A.IsSymm := hessian_symm f.1 x
    apply local_to_global A hsym (hessian_nonneg hcoeff (fun i => (hx i).le)) x hx
      (hessian_connected f.2 (by omega) hcoeff hconv hx) _ v hv
    intro u
    have hrow (i : Fin n) : B i *ᵥ x = c • (fun j => A j i) := by
      ext j
      exact hessian_mulVec (D i).2 x j |>.trans (by simp [c, A, D, hessian])
    have hperm (i j l : Fin n) : B i j l = B l j i :=
      congrArg (eval x ∘ pderiv j) (pderiv_comm l i f.1)
    have hcomb : ∑ i, x i • B i = c • A := by
      ext j l
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      calc
        _ = (B l *ᵥ x) j :=
          sum_congr rfl fun i _ => by rw [hperm i j l]; exact mul_comm _ _
        _ = _ := congrFun (hrow l) j
    have hform (i : Fin n) (w : Fin n → ℝ) : bilinear (B i) w x = c * (A *ᵥ w) i := by
      rw [bilinear, hrow, dotProduct_smul]
      congr 1
      exact sum_congr rfl fun j _ => by
        change w j * A j i = A i j * w j
        rw [hsym.apply i j, mul_comm]
    have htotal : ∑ i, x i * bilinear (B i) u u = c * bilinear A u u := by
      have ht := congrArg (fun R : Matrix (Fin n) (Fin n) ℝ => bilinear R u u) hcomb
      simpa only [bilinear, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
        dotProduct_smul, smul_eq_mul] using ht
    have hlocal (i : Fin n) : bilinear (B i) u u ≤
        (c * (A *ᵥ u) i) ^ 2 / (c * (A *ᵥ x) i) := by
      have hh := reverse_cauchy_div (B i) (hessian_symm _ _) x hx
        (hessian_nonneg (pderiv_coeff_nonneg hcoeff i) (fun j => (hx j).le))
        (ih (D i) (hpartial i)) u
      simpa only [hform] using hh
    apply (mul_le_mul_iff_of_pos_left hc).mp
    rw [← htotal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ x i * ((c * (A *ᵥ u) i) ^ 2 / (c * (A *ᵥ x) i)) :=
        mul_le_mul_of_nonneg_left (hlocal i) (hx i).le
      _ = _ := by
        by_cases hzero : (A *ᵥ x) i = 0
        · simp [hzero]
        · field_simp [hc.ne']

-- Approach a nonnegative point by strictly positive points and pass the inequality to the limit.
private lemma lorentzian_hessian_bound {n d : ℕ} (f : H n (d + 2)) (hf : f ∈ L n (d + 2))
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (v : Fin n → ℝ) :
    bilinear (hessian f.1 x) v v * bilinear (hessian f.1 x) x x ≤
      bilinear (hessian f.1 x) v x ^ 2 := by
  let z (t : ℝ) : Fin n → ℝ := fun i => x i + t
  have hz : Continuous z := continuous_pi fun _ => continuous_const.add continuous_id
  have hz0 : z 0 = x := funext fun i => add_zero (x i)
  have hb (u w : ℝ → Fin n → ℝ) (hu : Continuous u) (hw : Continuous w) :
      Continuous (fun t => bilinear (hessian f.1 (z t)) (u t) (w t)) := by
    simp only [bilinear, Matrix.dot_mulVec_eq_sum_sum]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp hu).mul (MvPolynomial.continuous_eval _ |>.comp hz)).mul
        ((continuous_apply j).comp hw)
  have hleft := (hb (fun _ => v) (fun _ => v) continuous_const continuous_const).mul
    (hb z z hz hz)
  have hright := (hb (fun _ => v) z continuous_const hz).pow 2
  have hlimit := le_of_tendsto_of_tendsto (hleft.continuousWithinAt (s := Set.Ioi 0) (x := 0))
    (hright.continuousWithinAt (s := Set.Ioi 0) (x := 0)) ?_
  · simpa only [Pi.mul_apply, Pi.pow_apply, hz0] using hlimit
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hzt (i : Fin n) : 0 < z t i := add_pos_of_nonneg_of_pos (hx i) ht
    have hn : ∀ m, 0 ≤ f.1.coeff m := by
      cases d with
      | zero => exact hf.2
      | succ d => exact hf.1.2
    let A := hessian f.1 (z t)
    have hnA := hessian_nonneg hn (fun i => (hzt i).le)
    have hq : 0 ≤ bilinear A (z t) (z t) := by
      change 0 ≤ ∑ i, z t i * (∑ j, A i j * z t j)
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hzt i).le
        (Finset.sum_nonneg (s := univ) fun j _ => mul_nonneg (hnA i j) (hzt j).le)
    rcases hq.eq_or_lt with hq | hq
    · change bilinear A v v * bilinear A (z t) (z t) ≤ _
      rw [← hq, mul_zero]
      exact sq_nonneg _
    · exact (le_div_iff₀ hq).mp
        (reverse_cauchy_div A (hessian_symm _ _) (z t) hzt hnA
          (lorentzian_hessian_nonpos (z t) hzt d f hf) v)


private lemma count_mapEmbedding {α β : Type*} (M : Matroid α) [M.Finite] (f : α ↪ β)
    (k : ℕ) : independentSetCount (M.mapEmbedding f) k = independentSetCount M k := by
  symm
  apply Set.BijOn.ncard_eq (f := Finset.map f)
  refine ⟨?_, (Finset.map_injective f).injOn, ?_⟩
  · rintro I ⟨hi, hI⟩
    exact ⟨by simpa using hi, by rw [Finset.coe_map]; exact hI.mapEmbedding f⟩
  · rintro J ⟨hj, hJ⟩
    rw [Matroid.mapEmbedding_indep_iff] at hJ
    let I := J.preimage f f.injective.injOn
    have hmap : I.map f = J := by
      apply Finset.coe_injective
      rw [Finset.coe_map, Finset.coe_preimage, Set.image_preimage_eq_iff.mpr hJ.2]
    refine ⟨I, ⟨?_, ?_⟩, hmap⟩
    · simpa [← Finset.card_map f, hmap] using hj
    · simpa [I] using hJ.1

open Classical in
private lemma count_eq_finset_card {n : ℕ} (M : Matroid (Fin n)) (k : ℕ) :
    independentSetCount M k =
      ((univ.filter fun I : Finset (Fin n) => M.Indep (I : Set (Fin n))).filter
        (fun I => I.card = k)).card := by
  classical
  rw [independentSetCount, ← Set.ncard_coe_finset]
  congr 1
  ext I
  simp [and_comm]

private lemma count_eq_zero_of_lt {n : ℕ} (M : Matroid (Fin n)) {k : ℕ} (h : n < k) :
    independentSetCount M k = 0 := by
  classical
  rw [count_eq_finset_card, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro I _ hi
  have hn : I.card ≤ n := by simpa using I.card_le_univ
  omega

private noncomputable def indepExponent {n : ℕ} (I : Finset (Fin n)) : Fin (n + 1) →₀ ℕ :=
  Finsupp.single 0 (n - I.card) + indicatorVec (I.map (Fin.succEmb n))

private lemma indepExponent_zero {n : ℕ} (I : Finset (Fin n)) :
    indepExponent I 0 = n - I.card := by
  simp [indepExponent, indicatorVec_apply]

private lemma indepExponent_degree {n : ℕ} (I : Finset (Fin n)) :
    (indepExponent I).degree = n := by
  classical
  rw [indepExponent, Finsupp.degree_eq_sum]
  simp only [Finsupp.add_apply, sum_add_distrib, ← Finsupp.degree_eq_sum,
    Finsupp.degree_single]
  rw [Finsupp.degree_eq_sum]
  simp_rw [indicatorVec_apply]
  rw [Finset.sum_boole]
  have hfilter : univ.filter (· ∈ I.map (Fin.succEmb n)) = I.map (Fin.succEmb n) := by
    ext i
    simp
  rw [hfilter, Finset.card_map]
  exact Nat.sub_add_cancel (by simpa using I.card_le_univ)

private noncomputable def independenceForm {n : ℕ} (M : Matroid (Fin n)) : H (n + 1) n :=
  open Classical in
  ⟨∑ I ∈ univ.filter (fun I : Finset (Fin n) => M.Indep (I : Set (Fin n))),
      monomial (indepExponent I) (1 : ℝ),
    IsHomogeneous.sum _ _ _ (fun I _ => isHomogeneous_monomial _ (indepExponent_degree I))⟩

private lemma independenceForm_mem_L {n : ℕ} (M : Matroid (Fin n)) :
    independenceForm M ∈ L (n + 1) n :=
  MathlibExt.Combinatorics.LorentzianToolboxWanted.independenceGeneratingPolynomial_mem_L M _ rfl

private lemma pderiv_iterate_monomial {ι : Type*} (i : ι) (m : ι →₀ ℕ) (c : ℝ) (r : ℕ) :
    (pderiv i)^[r] (monomial m c) =
      monomial (m - Finsupp.single i r) (c * ((m i).descFactorial r : ℝ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_monomial, tsub_tsub, ← Finsupp.single_add,
      Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]
    push_cast
    ring_nf

private lemma pderiv_iterate_sum {ι κ : Type*} (i : ι) (r : ℕ) (s : Finset κ)
    (g : κ → MvPolynomial ι ℝ) :
    (pderiv i)^[r] (∑ a ∈ s, g a) = ∑ a ∈ s, (pderiv i)^[r] (g a) := by
  induction r with
  | zero => simp
  | succ r ih => simp only [Function.iterate_succ_apply', ih, map_sum]

private def boundary (n : ℕ) : Fin (n + 1) → ℝ := Fin.cons 0 (fun _ => 1)

-- Each set of size `k` contributes `(n - k)!` after differentiating and setting the
-- homogenising variable to zero. Every other term vanishes.
private lemma eval_independenceForm {n : ℕ} (M : Matroid (Fin n)) {k : ℕ} (hk : k ≤ n) :
    eval (boundary n) ((pderiv 0)^[n - k] (independenceForm M).1) =
      ((n - k).factorial : ℝ) * independentSetCount M k := by
  classical
  change eval (boundary n) ((pderiv 0)^[n - k] (∑ I ∈ univ.filter _,
    monomial (indepExponent I) (1 : ℝ))) = _
  rw [pderiv_iterate_sum, map_sum]
  simp only [pderiv_iterate_monomial, indepExponent_zero, one_mul, eval_monomial, Finsupp.prod_pow,
    Fin.prod_univ_succ, boundary, Fin.cons_zero, Fin.cons_succ, one_pow, prod_const_one, mul_one,
    Finsupp.tsub_apply, Finsupp.single_eq_same]
  rw [count_eq_finset_card, ← nsmul_eq_mul', ← sum_const,
    Finset.sum_filter (s := univ.filter fun I : Finset (Fin n) => M.Indep (I : Set (Fin n)))]
  apply sum_congr rfl
  intro I _
  split_ifs with h
  · rw [h, Nat.descFactorial_self]
    simp
  · have hcard : I.card ≤ n := by simpa using I.card_le_univ
    obtain h | h := lt_or_gt_of_ne h
    · rw [zero_pow (by omega)]
      simp
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

private lemma iterate_to_degree {n d e : ℕ} (f : H n e) (hd : 2 ≤ d) (hde : d ≤ e)
    (hf : f ∈ L n e) (i : Fin n) :
    ∃ g : H n d, g.1 = (pderiv i)^[e - d] f.1 ∧ g ∈ L n d := by
  induction e with
  | zero => omega
  | succ e ih =>
    by_cases he : d = e + 1
    · subst d
      exact ⟨f, by simp, hf⟩
    · have hde' : d ≤ e := by omega
      obtain ⟨j, rfl⟩ : ∃ j, e = j + 2 := ⟨e - 2, by omega⟩
      have hf' : ⟨pderiv i f.1, f.2.pderiv⟩ ∈ L n (j + 2) := hf.2 i
      obtain ⟨g, hg, hL⟩ := ih ⟨_, f.2.pderiv⟩ hde' hf'
      refine ⟨g, ?_, hL⟩
      rwa [show j + 2 + 1 - d = j + 2 - d + 1 by omega, Function.iterate_succ_apply]


private lemma finite_logConcave {n : ℕ} (M : Matroid (Fin n)) (k : ℕ) (hk : 1 ≤ k) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) ≤
      independentSetCount M k ^ 2 := by
  by_cases hkn : ¬ k < n
  · rw [count_eq_zero_of_lt M (by omega : n < k + 1), mul_zero]
    exact Nat.zero_le _
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let r : ℕ := n - (j + 2)
  let x := boundary n
  let v : Fin (n + 1) → ℝ := Pi.single 0 1
  obtain ⟨f, hf, hL⟩ := iterate_to_degree (independenceForm M)
    (by omega : 2 ≤ j + 2) (by omega : j + 2 ≤ n) (independenceForm_mem_L M) 0
  have hEval (s : ℕ) (hs : s ≤ 2) :
      eval x ((pderiv 0)^[s] f.1) =
        ((r + s).factorial : ℝ) * independentSetCount M (j + 2 - s) := by
    have hsub : s + r = n - (j + 2 - s) := by dsimp [r]; omega
    rw [hf, ← Function.iterate_add_apply, hsub, eval_independenceForm M (by omega), ← hsub,
      Nat.add_comm s r]
  have hval : eval x f.1 = (r.factorial : ℝ) * independentSetCount M (j + 2) :=
    hEval 0 (by decide)
  have hD : eval x (pderiv 0 f.1) = ((r + 1).factorial : ℝ) * independentSetCount M (j + 1) := by
    simpa only [Function.iterate_one, show j + 2 - 1 = j + 1 by omega] using hEval 1 (by decide)
  have hDD : eval x (pderiv 0 (pderiv 0 f.1)) =
      ((r + 2).factorial : ℝ) * independentSetCount M j := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, Nat.add_sub_cancel] using
      hEval 2 (by decide)
  have hx (i : Fin (n + 1)) : 0 ≤ x i := by
    cases i using Fin.cases <;> simp [x, boundary]
  let A := hessian f.1 x
  have hvv : bilinear A v v = eval x (pderiv 0 (pderiv 0 f.1)) := by
    simp [bilinear, v, Matrix.mulVec, dotProduct, Pi.single_apply, A, hessian]
  have hvx : bilinear A v x = (↑(j + 1) : ℝ) * eval x (pderiv 0 f.1) := by
    change v ⬝ᵥ A *ᵥ x = _
    rw [show v ⬝ᵥ A *ᵥ x = (A *ᵥ x) 0 by simp [v, dotProduct, Pi.single_apply]]
    exact hessian_mulVec f.2 x 0
  have hxx : bilinear A x x = (↑(j + 1) : ℝ) * (↑(j + 2) : ℝ) * eval x f.1 := by
    change ∑ i, x i * (A *ᵥ x) i = _
    dsimp only [A]
    simp_rw [hessian_mulVec f.2 x]
    change (∑ i, x i * ((↑(j + 1) : ℝ) * eval x (pderiv i f.1))) = _
    have he := eval_euler f.2 x
    rw [aeval_eq_eval] at he
    rw [mul_assoc, ← he, Finset.mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have hineq := lorentzian_hessian_bound f hL x hx v
  change bilinear A v v * bilinear A x x ≤ bilinear A v x ^ 2 at hineq
  rw [hvv, hvx, hxx, hDD, hD, hval, Nat.factorial_succ (r + 1), Nat.factorial_succ r] at hineq
  push_cast at hineq
  let a : ℝ := independentSetCount M j
  let b : ℝ := independentSetCount M (j + 1)
  let c : ℝ := independentSetCount M (j + 2)
  let p : ℝ := (j : ℝ) + 1
  let q : ℝ := (r : ℝ) + 1
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hnormalized : (p + 1) * (q + 1) * (a * c) ≤ p * q * b ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < p * q * (r.factorial : ℝ) ^ 2 by positivity)).mp
    dsimp [a, b, c, p, q]
    convert hineq using 1 <;> ring
  have hab : a * c ≤ b ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left (mul_pos hp hq)).mp
    refine (mul_le_mul_of_nonneg_right ?_ (by dsimp [a, c]; positivity)).trans hnormalized
    nlinarith
  rw [Nat.add_sub_cancel]
  dsimp [a, b, c] at hab
  exact_mod_cast hab

end

/-- **Log-concavity of the independent set numbers of a matroid** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Theorem 9.9 (3),
answering Conjecture 1.2 of Welsh and Mason). For every finite matroid `M` and every `k ≥ 1`,
`f_{k-1}(M) f_{k+1}(M) ≤ f_k(M)^2`, where `f_k(M)` is the number of independent sets of size
`k`. (AHK state `1 ≤ k ≤ r`, where `r + 1` is the rank; for larger `k` the factor
`f_{k+1}(M)` vanishes, so the inequality is trivial.) -/
public theorem independentSetCount_logConcave {α : Type*} (M : _root_.Matroid α) [M.Finite]
    (k : ℕ) (hk : 1 ≤ k) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) ≤
      independentSetCount M k ^ 2 := by
  classical
  let _ : Fintype M.E := M.ground_finite.fintype
  let e := Fintype.equivFin M.E
  let N := M.restrictSubtype M.E
  let f : M.E ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hM : N.mapEmbedding f = M := M.map_val_restrictSubtype_ground_eq
  have hcount (j : ℕ) : independentSetCount (N.mapEquiv e) j = independentSetCount M j := by
    calc
      independentSetCount (N.mapEquiv e) j = independentSetCount N j :=
        count_mapEmbedding N e.toEmbedding j
      _ = independentSetCount (N.mapEmbedding f) j := (count_mapEmbedding N f j).symm
      _ = independentSetCount M j := by simp only [hM]
  simpa only [hcount] using finite_logConcave (N.mapEquiv e) k hk

end MathlibExt.Combinatorics.WeakMasonWanted
