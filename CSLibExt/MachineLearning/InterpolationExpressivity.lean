/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.OneHiddenLayerNet
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-sample expressivity of two-layer ReLU networks

A two-layer ReLU network with `n` hidden units interpolates arbitrary labels
on any `n` distinct points: a separating direction makes the projected points
distinct, midpoints interleave biases between the sorted projections, and the
resulting triangular system is solved for the output weights.
-/

public section

namespace Cslib.MachineLearning.InterpolationExpressivity

open Cslib.MachineLearning.OneHiddenLayerNet

/-- A separating direction: for distinct sample points, some direction has
pairwise distinct inner products with the points. Proved by evaluating along
a moment curve above all roots of the pairwise difference polynomials. -/
theorem exists_separating_direction (n d : ℕ)
    (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Function.Injective z) :
    ∃ a : EuclideanSpace ℝ (Fin d),
      Function.Injective (fun i => @inner ℝ _ _ a (z i)) := by
  set P : Fin n → Fin n → Polynomial ℝ := fun i j => ∑ k : Fin d,
    Polynomial.monomial k.val ((z i).ofLp k - (z j).ofLp k) with hP
  set pairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2) with hpairs
  set S : Finset ℝ :=
    pairs.biUnion (fun p => (P p.1 p.2).roots.toFinset) with hS
  obtain ⟨B, hB⟩ := Finset.bddAbove S
  set t : ℝ := B + 1 with ht
  have ht_gt : ∀ s ∈ S, s < t := by
    intro s hs
    have hle : s ≤ B := hB (Finset.mem_coe.mpr hs)
    rw [ht]
    exact lt_of_le_of_lt hle (lt_add_one _)
  have heval : ∀ i j, i ≠ j → (P i j).eval t ≠ 0 := by
    intro i j hij
    have hne : z i ≠ z j := hz.ne hij
    obtain ⟨k0, hk0⟩ : ∃ k, (z i).ofLp k ≠ (z j).ofLp k := by
      by_contra hcon
      have hforall : ∀ k, (z i).ofLp k = (z j).ofLp k :=
        fun k => by_contra (fun hk => hcon ⟨k, hk⟩)
      exact hne (WithLp.ofLp_injective 2 (funext hforall))
    have hcoeff : (P i j).coeff k0.val
        = (z i).ofLp k0 - (z j).ofLp k0 := by
      have h := map_sum (Polynomial.lcoeff ℝ k0.val)
        (fun k : Fin d =>
          (Polynomial.monomial k.val) ((z i).ofLp k - (z j).ofLp k))
        Finset.univ
      simp only [hP, Polynomial.lcoeff_apply] at h ⊢
      have hmain : (∑ k : Fin d,
            ((Polynomial.monomial k.val) ((z i).ofLp k - (z j).ofLp k)).coeff
            k0.val)
          = (((Polynomial.monomial k0.val)
            ((z i).ofLp k0 - (z j).ofLp k0)).coeff k0.val) :=
        Finset.sum_eq_single_of_mem k0 (Finset.mem_univ k0)
          (fun k _ hkne => by
            rw [Polynomial.coeff_monomial]
            apply ite_eq_right
            exact fun hval => hkne (Fin.ext_iff.mpr hval))
      rw [h, hmain, Polynomial.coeff_monomial, ite_eq_left rfl]
    have hPne : P i j ≠ 0 := by
      intro hzero
      rw [hzero] at hcoeff
      simp only [Polynomial.coeff_zero] at hcoeff
      exact sub_ne_zero.mpr hk0 hcoeff.symm
    have htroots : t ∉ (P i j).roots := by
      intro hmem
      have hmemS : t ∈ S := by
        simp only [hS, Finset.mem_biUnion]
        refine ⟨(i, j), ?_, ?_⟩
        · simp only [hpairs, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa using hij
        · change t ∈ (P i j).roots.toFinset
          rw [Multiset.mem_toFinset]
          exact hmem
      have hlt := ht_gt t hmemS
      simp at hlt
    rw [Polynomial.mem_roots hPne, Polynomial.IsRoot.def] at htroots
    exact htroots
  refine ⟨WithLp.toLp 2 (fun k : Fin d => t ^ k.val), fun i j hij => ?_⟩
  have hij' : inner ℝ (WithLp.toLp 2 (fun k : Fin d => t ^ k.val)) (z i)
      = inner ℝ (WithLp.toLp 2 (fun k : Fin d => t ^ k.val)) (z j) := hij
  by_contra hneij
  have h0 : (P i j).eval t = 0 := by
    have heval_eq : (P i j).eval t = inner ℝ
        (WithLp.toLp 2 (fun k : Fin d => t ^ k.val)) (z i - z j) := by
      simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
        PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro k _
      have hsub : ((z i - z j).ofLp k) = (z i).ofLp k - (z j).ofLp k :=
        PiLp.sub_apply _ _ _ k
      have hreal : ∀ x y : ℝ, inner ℝ x y = y * x := fun x y => by simp
      rw [hsub, hreal]
    rw [heval_eq, inner_sub_right, hij', sub_self]
  exact heval i j hneij h0

/-- Triangular interpolation in sum form: for interleaved biases and points,
every right-hand side is hit. The matrix is lower triangular with positive
diagonal, hence invertible. -/
theorem interleaving_interpolation (n : ℕ) (b x : Fin n → ℝ)
    (hdiag : ∀ i, b i < x i) (htri : ∀ i j, i < j → x i < b j)
    (y : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, ∀ i, (∑ j, w j * (x i - b j)⁺) = y i := by
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => (x i - b j)⁺ with hA
  have hAij : ∀ i j, A i j = (x i - b j)⁺ := fun i j => by
    rw [hA]
    exact Matrix.of_apply _ _ _
  have htriA : A.IsLowerTriangular := fun i j hij => by
    have hij' : i < j := hij
    rw [hAij i j, posPart_eq_zero]
    exact sub_nonpos.mpr (le_of_lt (htri i j hij'))
  have hdiagA : ∀ i, A.diag i ≠ 0 := fun i => by
    have hdi : A.diag i = (x i - b i)⁺ := hAij i i
    rw [hdi]
    exact ne_of_gt (posPart_pos (sub_pos.mpr (hdiag i)))
  have hdet : A.det ≠ 0 :=
    (Matrix.IsLowerTriangular.det_ne_zero_iff htriA).mpr hdiagA
  refine ⟨Matrix.mulVec A⁻¹ y, fun i => ?_⟩
  have hsol : Matrix.mulVec A (Matrix.mulVec A⁻¹ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hdet),
      Matrix.one_mulVec]
  have hi := congrFun hsol i
  simp only [Matrix.mulVec_apply_eq_sum, hAij] at hi
  have hi2 : (∑ j, (Matrix.mulVec A⁻¹ y) j * (x i - b j)⁺)
      = (∑ j, (x i - b j)⁺ * (Matrix.mulVec A⁻¹ y) j) :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hi2]
  exact hi

/-- Interpolation by a shared-direction ReLU sum: for distinct points, some
direction, biases and output weights hit every label vector. -/
theorem exists_interpolating_weights (n d : ℕ)
    (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Function.Injective z)
    (y : Fin n → ℝ) :
    ∃ (a : EuclideanSpace ℝ (Fin d)) (b w : Fin n → ℝ),
      ∀ i, (∑ j, w j * (inner ℝ a (z i) - b j)⁺) = y i := by
  obtain ⟨a, ha⟩ := exists_separating_direction n d z hz
  set x' : Fin n → ℝ := fun i => inner ℝ a (z i)
  have hax' : Function.Injective x' := ha
  set s : Finset ℝ := Finset.univ.map ⟨x', hax'⟩ with hs
  have hcard : s.card = n := by
    rw [hs, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  set e : Fin n ↪o ℝ := s.orderEmbOfFin hcard
  set x : Fin n → ℝ := fun k => e k
  have hxmono : StrictMono x := fun k l h => e.strictMono h
  have hpre : ∀ k, ∃ i, x' i = x k := by
    intro k
    have hmem : e k ∈ s := Finset.orderEmbOfFin_mem s hcard k
    rw [hs, Finset.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    exact ⟨i, hi⟩
  choose σ hσ using hpre
  have hσinj : Function.Injective σ := by
    intro k l hkl
    have h1 : x k = x l := by rw [← hσ k, ← hσ l, hkl]
    exact hxmono.injective h1
  set τ : Fin n ≃ Fin n :=
    Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  have hcmem : ∀ k : Fin n, k.val ≠ 0 → k.val - 1 < n := fun k _ => by
    have hlt := k.isLt
    exact lt_of_le_of_lt (Nat.sub_le _ _) hlt
  set c : Fin n → ℝ := fun k =>
    if h : k.val = 0 then x k - 2 else x ⟨k.val - 1, hcmem k h⟩ with hc
  set b : Fin n → ℝ := fun k => (x k + c k) / 2 with hb
  have hb_lt : ∀ k, b k < x k := by
    intro k
    have hcx : c k < x k := by
      simp only [hc]
      by_cases hk0 : k.val = 0
      · rw [dite_eq_left hk0]
        linarith
      · rw [dite_eq_right hk0]
        apply hxmono
        change k.val - 1 < k.val
        exact Nat.sub_one_lt hk0
    simp only [hb]
    linarith
  have hbx : ∀ k l, k < l → x k < b l := by
    intro k l hkl
    have hcl : x k ≤ c l := by
      simp only [hc]
      by_cases hl0 : l.val = 0
      · rw [dite_eq_left hl0]
        exfalso
        have h1 : k.val < l.val := hkl
        rw [hl0] at h1
        exact absurd h1 (Nat.not_lt_zero _)
      · rw [dite_eq_right hl0]
        apply hxmono.monotone
        change k.val ≤ l.val - 1
        have h1 : k.val < l.val := hkl
        exact Nat.le_sub_one_of_lt h1
    have hlt2 : x k < x l := hxmono hkl
    simp only [hb]
    linarith
  obtain ⟨w, hw⟩ :=
    interleaving_interpolation n b x hb_lt hbx (fun k => y (σ k))
  have hsymm : ∀ i, σ (τ.symm i) = i :=
    fun i => Equiv.ofBijective_apply_symm_apply σ _ i
  refine ⟨a, b, w, fun i => ?_⟩
  have hL2 : (∑ j, w j * (x (τ.symm i) - b j)⁺) = y (σ (τ.symm i)) :=
    hw (τ.symm i)
  rw [hsymm i] at hL2
  have hxi2 : inner ℝ a (z i) = x (τ.symm i) := by
    have e1 : x' i = x' (σ (τ.symm i)) := by rw [hsymm i]
    have e2 : x' (σ (τ.symm i)) = x (τ.symm i) := hσ _
    exact e1.trans e2
  rw [hxi2]
  exact hL2

/-- Finite-sample expressivity in the paper's sense: on any `n` distinct
points in `d` dimensions, some two-layer ReLU network with `n` hidden units
fits arbitrary labels. The construction shares one direction `a` (`d`
entries) across all hidden units, with thresholds `b` (`n` entries) and
output weights `w` (`n` entries): `2 * n + d` weights in total. The network
receives `-b j` as its hidden biases, as in `max {<a, x> - b j, 0}`. -/
theorem exists_interpolating_net (n d : ℕ)
    (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Function.Injective z)
    (y : Fin n → ℝ) :
    ∃ (a : EuclideanSpace ℝ (Fin d)) (b w : Fin n → ℝ),
      ∀ i, (oneHiddenLayerNet d n (fun x => x⁺) (fun _ => a) (fun j => -b j) w).forward
        2 (z i) 0 = y i := by
  obtain ⟨a, b, w, hcore⟩ := exists_interpolating_weights n d z hz y
  refine ⟨a, b, w, fun i => ?_⟩
  have hfw := forward_oneHiddenLayerNet d n (fun x => x⁺) (fun _ => a)
    (fun j => -b j) w (z i)
  rw [hfw]
  simpa only [← sub_eq_add_neg] using hcore i

end Cslib.MachineLearning.InterpolationExpressivity

end
