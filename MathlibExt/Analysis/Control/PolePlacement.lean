/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.Polynomial.Monic

/-!
# Pole placement

For a linear control system `ẋ = A x + B u` over a field `𝕜` satisfying the Kalman rank condition
`Span {A^i B u : u ∈ U, 0 ≤ i < n} = 𝕜ⁿ`, every monic polynomial of degree `n` is the
characteristic polynomial of `A + B K` for some linear state feedback `u = K x`: the
pole-shifting theorem (Wonham 1967; Coron, *Control and Nonlinearity*, AMS 2007, Theorem 10.1;
Sontag, *Mathematical Control Theory*, 2nd ed., Theorem 13).

* `exists_charpoly_add_smulRight_eq`: the single-input case. The proof follows Ackermann's
  formula: with `q` the linear form that takes the value `1` on `A^{n-1} b` and `0` on
  `b, …, A^{n-2} b`, the feedback `K = - q ∘ P(A)` gives `q ∘ P(A + b K) = 0`, hence
  `P(A + b K) = 0`, and `b` stays a cyclic vector of `A + b K`.
* `exists_span_pow_add_comp_eq_top`: Heymann's lemma, which reduces several inputs to one
  (Coron, Lemma 10.3, following Hautus's proof).
* `exists_charpoly_add_comp_eq`: the pole-shifting theorem.
-/

open Polynomial Module

@[expose] public section

namespace MathlibExt.Analysis.Control

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The span of `b, F b, …, F^{j-1} b`. -/
private def krylov (F : Module.End 𝕜 V) (b : V) (j : ℕ) : Submodule 𝕜 V :=
  Submodule.span 𝕜 ((fun i => (F ^ i) b) '' Set.Iio j)

private theorem pow_mem_krylov (F : Module.End 𝕜 V) (b : V) {i j : ℕ} (h : i < j) :
    (F ^ i) b ∈ krylov F b j :=
  Submodule.subset_span ⟨i, h, rfl⟩

private theorem krylov_mono (F : Module.End 𝕜 V) (b : V) {j j' : ℕ} (h : j ≤ j') :
    krylov F b j ≤ krylov F b j' :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

private theorem pow_apply_mem_krylov (F : Module.End 𝕜 V) (b : V) {j : ℕ} (k : ℕ) {x : V}
    (hx : x ∈ krylov F b j) : (F ^ k) x ∈ krylov F b (j + k) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [← Module.End.mul_apply, ← pow_add]
    exact pow_mem_krylov F b (by simp only [Set.mem_Iio] at hi; omega)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

private theorem mem_krylov_succ (F : Module.End 𝕜 V) (b : V) {j : ℕ} {x : V}
    (hx : x ∈ krylov F b (j + 1)) : ∃ c : 𝕜, ∃ s ∈ krylov F b j, x = c • (F ^ j) b + s := by
  have hset : (fun i => (F ^ i) b) '' Set.Iio (j + 1) =
      insert ((F ^ j) b) ((fun i => (F ^ i) b) '' Set.Iio j) := by
    ext y
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, rfl⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨j, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
  rw [krylov, hset] at hx
  exact Submodule.mem_span_insert.1 hx

/-- Evaluation of a polynomial written as `X^n + ∑_{i<n} c_i X^i` at an endomorphism. -/
private theorem aeval_monic_form_apply (F : Module.End 𝕜 V) (n : ℕ) (c : ℕ → 𝕜) (x : V) :
    aeval F (X ^ n + ∑ i ∈ Finset.range n, C (c i) * X ^ i) x =
      (F ^ n) x + ∑ i ∈ Finset.range n, c i • (F ^ i) x := by
  simp [map_sum, LinearMap.sum_apply, Module.End.mul_apply]

/-- **Pole placement for single-input systems** (Wonham 1967; Coron, *Control and
Nonlinearity*, AMS 2007, Theorem 10.1 with `m = 1`; Sontag, *Mathematical Control Theory*,
2nd ed., Theorem 13). Let `A` be an endomorphism of an `n`-dimensional vector space `V` over a
field and `b ∈ V` with `Span {b, A b, …, A^{n-1} b} = V` (the Kalman rank condition for the
single-input system `ẋ = A x + b u`). Then for every monic polynomial `P` of degree `n` there is a
linear form `K` such that the closed-loop operator `A + b K`, `x ↦ A x + K(x) b`, has
characteristic polynomial `P`. -/
theorem exists_charpoly_add_smulRight_eq [FiniteDimensional 𝕜 V] (A : Module.End 𝕜 V) (b : V)
    (hb : Submodule.span 𝕜 (Set.range fun i : Fin (finrank 𝕜 V) => (A ^ (i : ℕ)) b) = ⊤)
    (P : 𝕜[X]) (hP : P.Monic) (hdeg : P.natDegree = finrank 𝕜 V) :
    ∃ K : Module.Dual 𝕜 V, (A + K.smulRight b).charpoly = P := by
  set n := finrank 𝕜 V with hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · refine ⟨0, ?_⟩
    rw [eq_one_of_monic_natDegree_zero hP (hdeg.trans h0)]
    exact eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
      ((LinearMap.charpoly_natDegree _).trans h0)
  -- The cyclic basis and the last coordinate form `q`.
  set v : Fin n → V := fun i => (A ^ (i : ℕ)) b with hv
  let β : Basis (Fin n) 𝕜 V := basisOfTopLeSpanOfCardEqFinrank v hb.ge (by simp [hn])
  have hβ : ∀ i, β i = v i := fun i => by simp [β]
  let last : Fin n := ⟨n - 1, by omega⟩
  let q : Module.Dual 𝕜 V := β.coord last
  have hq : ∀ i < n, q ((A ^ i) b) = if i = n - 1 then 1 else 0 := by
    intro i hi
    have : (A ^ i) b = β ⟨i, hi⟩ := by rw [hβ]
    rw [this]
    simp only [q, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, last,
      Fin.ext_iff]
  have hqK : ∀ x ∈ krylov A b (n - 1), q x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      simp only [Set.mem_Iio] at hi
      rw [hq i (by omega), ite_eq_right (by omega)]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul a y _ hy => rw [map_smul, hy, smul_zero]
  -- The feedback and the closed loop.
  set K : Module.Dual 𝕜 V := -(q ∘ₗ aeval A P) with hK
  set A' : Module.End 𝕜 V := A + K.smulRight b with hA'
  have hA'x : ∀ x, A' x = A x + K x • b := fun x => by simp [hA']
  have hstep : ∀ j, j ≤ n - 1 → ∀ x, q ((A' ^ j) x) = q ((A ^ j) x) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj x
      rw [pow_succ, Module.End.mul_apply, ih (by omega), hA'x, map_add, map_smul, map_add,
        map_smul, hq j (by omega), ite_eq_right (by omega), smul_zero, add_zero, pow_succ,
        Module.End.mul_apply]
  have htop : ∀ x, q ((A' ^ n) x) = q ((A ^ n) x) + K x := by
    intro x
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1, pow_succ, Module.End.mul_apply]
    rw [hstep (n - 1) le_rfl, hA'x, map_add, map_smul, map_add, map_smul,
      hq (n - 1) (by omega), ite_eq_left rfl, smul_eq_mul, mul_one, ← Module.End.mul_apply,
      ← pow_succ, ← hn1]
  have hPform := hP.as_sum
  rw [hdeg] at hPform
  have hPA : ∀ (F : Module.End 𝕜 V) x,
      aeval F P x = (F ^ n) x + ∑ i ∈ Finset.range n, P.coeff i • (F ^ i) x := by
    intro F x
    conv_lhs => rw [hPform]
    exact aeval_monic_form_apply F n (fun i => P.coeff i) x
  have hqP : ∀ x, q (aeval A' P x) = 0 := by
    intro x
    have hKx : K x = -(q ((A ^ n) x) + ∑ i ∈ Finset.range n, P.coeff i * q ((A ^ i) x)) := by
      rw [hK, LinearMap.neg_apply, LinearMap.comp_apply, hPA, map_add, map_sum]
      simp [map_smul]
    rw [hPA, map_add, map_sum, htop, hKx]
    have : ∑ i ∈ Finset.range n, q (P.coeff i • (A' ^ i) x) =
        ∑ i ∈ Finset.range n, P.coeff i * q ((A ^ i) x) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hstep i (by simp at hi; omega), smul_eq_mul]
    rw [this]
    ring
  -- Separation: the forms `q ∘ A^i`, `i < n`, separate points.
  have hsep : ∀ y, (∀ i < n, q ((A ^ i) y) = 0) → y = 0 := by
    have key : ∀ j ≤ n, ∀ y ∈ krylov A b j, (∀ i < n, q ((A ^ i) y) = 0) → y = 0 := by
      intro j
      induction j with
      | zero =>
        intro _ y hy _
        simpa [krylov] using hy
      | succ j ih =>
        intro hj y hy hq0
        obtain ⟨c, s, hs, rfl⟩ := mem_krylov_succ A b hy
        have hc : c = 0 := by
          have h1 := hq0 (n - 1 - j) (by omega)
          rw [map_add, map_smul, map_add, map_smul, ← Module.End.mul_apply, ← pow_add,
            show n - 1 - j + j = n - 1 by omega, hq (n - 1) (by omega), ite_eq_left rfl,
            hqK _ (by
              have := pow_apply_mem_krylov A b (n - 1 - j) hs
              rwa [show j + (n - 1 - j) = n - 1 by omega] at this),
            add_zero, smul_eq_mul, mul_one] at h1
          exact h1
        subst hc
        rw [zero_smul, zero_add] at hq0 ⊢
        exact ih (by omega) s hs hq0
    intro y hy
    refine key n le_rfl y ?_ hy
    have : krylov A b n = ⊤ := by
      rw [eq_top_iff, ← hb]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact pow_mem_krylov A b i.2
    rw [this]; exact Submodule.mem_top
  -- `P` annihilates the closed loop.
  have hPA' : aeval A' P = 0 := by
    ext x
    apply hsep
    intro i hi
    have hc : A' ^ i * aeval A' P = aeval A' P * A' ^ i := by
      have := congrArg (aeval A') (mul_comm (X ^ i : 𝕜[X]) P)
      simpa only [map_mul, aeval_X_pow] using this
    rw [← hstep i (by omega), ← Module.End.mul_apply, hc, Module.End.mul_apply, hqP]
  -- `b` is a cyclic vector of the closed loop.
  have hcyc : ∀ j, krylov A b j ≤ krylov A' b j := by
    intro j
    induction j with
    | zero =>
      intro y hy
      have : krylov A b 0 = ⊥ := by simp [krylov]
      rw [this, Submodule.mem_bot] at hy
      rw [hy]; exact Submodule.zero_mem _
    | succ j ih =>
      intro y hy
      obtain ⟨c, s, hs, rfl⟩ := mem_krylov_succ A b hy
      refine Submodule.add_mem _ (Submodule.smul_mem _ c ?_) (krylov_mono A' b j.le_succ (ih hs))
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using pow_mem_krylov A' b (show 0 < 1 by omega)
      · have hj' : j = (j - 1) + 1 := by omega
        have hmem : (A ^ (j - 1)) b ∈ krylov A' b j := ih (pow_mem_krylov A b (by omega))
        have h1 := pow_apply_mem_krylov A' b 1 hmem
        have hb1 : b ∈ krylov A' b (j + 1) := by
          simpa using pow_mem_krylov A' b (show 0 < j + 1 by omega)
        have : (A ^ j) b = A' ((A ^ (j - 1)) b) - K ((A ^ (j - 1)) b) • b := by
          rw [hA'x, add_sub_cancel_right, ← Module.End.mul_apply, ← pow_succ', ← hj']
        rw [this]
        exact Submodule.sub_mem _ (by simpa using h1) (Submodule.smul_mem _ _ hb1)
  have hli : LinearIndependent 𝕜 fun i : Fin n => (A' ^ (i : ℕ)) b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hn])
    intro y _
    have hyK : y ∈ krylov A' b n := by
      apply hcyc
      have : krylov A b n = ⊤ := by
        rw [eq_top_iff, ← hb]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        exact pow_mem_krylov A b i.2
      rw [this]; exact Submodule.mem_top
    refine Submodule.span_le.2 ?_ hyK
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  -- Compare coefficients with the characteristic polynomial.
  have hχ := (LinearMap.charpoly_monic A').as_sum
  rw [LinearMap.charpoly_natDegree] at hχ
  have hCH : aeval A' A'.charpoly = 0 := LinearMap.aeval_self_charpoly A'
  have hcoeff : ∀ i < n, A'.charpoly.coeff i = P.coeff i := by
    have h1 := congrArg (fun f : Module.End 𝕜 V => f b) hCH
    have h2 := congrArg (fun f : Module.End 𝕜 V => f b) hPA'
    simp only [LinearMap.zero_apply] at h1 h2
    rw [hχ, aeval_monic_form_apply] at h1
    rw [hPA] at h2
    have hsum : ∑ i : Fin n, (A'.charpoly.coeff i - P.coeff i) • (A' ^ (i : ℕ)) b = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [Fin.sum_univ_eq_sum_range (fun i => A'.charpoly.coeff i • (A' ^ i) b),
        Fin.sum_univ_eq_sum_range (fun i => P.coeff i • (A' ^ i) b)]
      have e1 := eq_neg_of_add_eq_zero_right h1
      have e2 := eq_neg_of_add_eq_zero_right h2
      rw [e1, e2, sub_self]
    intro i hi
    have := Fintype.linearIndependent_iff.1 hli _ hsum ⟨i, hi⟩
    exact sub_eq_zero.1 this
  refine ⟨K, ?_⟩
  rw [hχ, hPform]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [hcoeff i (Finset.mem_range.1 hi)]

/-- **Heymann's lemma** (Heymann 1968, in the proof of Hautus; Coron, *Control and
Nonlinearity*, AMS 2007, Lemma 10.3). If the linear control system `ẋ = A x + B u` on an
`n`-dimensional space `V` satisfies the Kalman rank condition
`Span {A^i B u : u ∈ U, 0 ≤ i < n} = V`, then there are a control direction `f ∈ U` and a linear
feedback `C : V → U` such that the single-input system `ẋ = (A + B C) x + (B f) v` satisfies the
Kalman rank condition: `B f, (A + B C) B f, …, (A + B C)^{n-1} B f` span `V`. -/
theorem exists_span_pow_add_comp_eq_top [FiniteDimensional 𝕜 V] {U : Type*} [AddCommGroup U]
    [Module 𝕜 U] (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (hK : Submodule.span 𝕜 {x | ∃ i < finrank 𝕜 V, ∃ u : U, x = (A ^ i) (B u)} = ⊤) :
    ∃ (f : U) (C : V →ₗ[𝕜] U), Submodule.span 𝕜
      (Set.range fun i : Fin (finrank 𝕜 V) => ((A + B ∘ₗ C) ^ (i : ℕ)) (B f)) = ⊤ := by
  set n := finrank 𝕜 V with hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have : Subsingleton V := Module.finrank_zero_iff.1 h0
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  -- A control direction with `B f ≠ 0`.
  obtain ⟨f, hf⟩ : ∃ f : U, B f ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hbot : Submodule.span 𝕜 {x | ∃ i < n, ∃ u : U, x = (A ^ i) (B u)} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, -, u, rfl⟩
      rw [hall u, map_zero]
    rw [hK] at hbot
    have : Subsingleton V := subsingleton_of_forall_eq 0 fun y => by
      have : y ∈ (⊥ : Submodule 𝕜 V) := hbot ▸ Submodule.mem_top
      simpa using this
    have := Module.finrank_zero_of_subsingleton (R := 𝕜) (M := V)
    omega
  -- Chains `B f = x₀, x₁, …, x_{k-1}` with `x_{j+1} ∈ A x_j + B U`, linearly independent.
  let P : ℕ → Prop := fun k => ∃ x : ℕ → V, ∃ u : ℕ → U, x 0 = B f ∧
    (∀ j, j + 1 < k → x (j + 1) = A (x j) + B (u j)) ∧ LinearIndependent 𝕜 fun i : Fin k => x i
  have hP1 : P 1 := ⟨fun _ => B f, fun _ => 0, rfl, fun j hj => by omega,
    linearIndependent_unique_iff.2 hf⟩
  have hbound : ∀ k, P k → k ≤ n := by
    rintro k ⟨x, u, -, -, hli⟩
    simpa using hli.fintype_card_le_finrank
  classical
  set k := Nat.findGreatest P n with hk_def
  have hk1 : 1 ≤ k := Nat.le_findGreatest hpos hP1
  obtain ⟨x, u, hx0, hrec, hli⟩ := Nat.findGreatest_spec hpos hP1
  rw [← hk_def] at hrec hli
  set E := Submodule.span 𝕜 (Set.range fun i : Fin k => x i) with hE_def
  have hxE : ∀ j < k, x j ∈ E := fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  -- Maximality: the chain cannot be extended.
  have hext : ∀ w : U, A (x (k - 1)) + B w ∈ E := by
    intro w
    by_contra hw
    set y := A (x (k - 1)) + B w
    have hP : P (k + 1) := by
      refine ⟨fun j => if j < k then x j else y, fun j => if j < k - 1 then u j else w,
        by simp [show 0 < k by omega, hx0], ?_, ?_⟩
      · intro j hj
        by_cases hjk : j + 1 < k
        · simp [hjk, show j < k by omega, show j < k - 1 by omega, hrec j hjk]
        · have hjk' : j = k - 1 := by omega
          subst hjk'
          simp [show ¬ (k - 1 + 1 < k) by omega, show k - 1 < k by omega, y]
      · have : (fun i : Fin (k + 1) => if (i : ℕ) < k then x i else y) =
            Fin.snoc (fun i : Fin k => x i) y := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp
          · simp
        rw [this]
        exact hli.finSnoc hw
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) (hbound _ hP) hP
  have hBE : ∀ w : U, B w ∈ E := by
    intro w
    have h1 := hext w
    have h2 := hext 0
    rw [map_zero, add_zero] at h2
    have := Submodule.sub_mem _ h1 h2
    simpa using this
  have hAxE : ∀ j < k, A (x j) ∈ E := by
    intro j hj
    by_cases hjk : j + 1 < k
    · have : A (x j) = x (j + 1) - B (u j) := by rw [hrec j hjk]; abel
      rw [this]
      exact Submodule.sub_mem _ (hxE _ hjk) (hBE _)
    · have hj' : j = k - 1 := by omega
      have := hext 0
      rwa [map_zero, add_zero, ← hj'] at this
  have hAE : ∀ y ∈ E, A y ∈ E := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact hAxE i i.2
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hgen : ∀ i (w : U), (A ^ i) (B w) ∈ E := by
    intro i
    induction i with
    | zero => simpa using hBE
    | succ i ih => intro w; rw [pow_succ', Module.End.mul_apply]; exact hAE _ (ih w)
  have hEtop : E = ⊤ := by
    rw [eq_top_iff, ← hK]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, w, rfl⟩
    exact hgen i w
  have hkn : k = n := by
    have h := finrank_span_eq_card hli
    rw [← hE_def, hEtop, finrank_top] at h
    simpa using h.symm
  -- The feedback `C x_j = u_j` for `j < k - 1`.
  let β : Basis (Fin k) 𝕜 V := Basis.mk hli (by rw [← hE_def, hEtop])
  let C : V →ₗ[𝕜] U := β.constr 𝕜 fun i : Fin k => if (i : ℕ) + 1 < k then u i else 0
  have hC : ∀ j, j + 1 < k → C (x j) = u j := by
    intro j hj
    have : x j = β ⟨j, by omega⟩ := by simp [β]
    rw [this, Basis.constr_basis]
    simp [hj]
  have hpow : ∀ j < k, ((A + B ∘ₗ C) ^ j) (B f) = x j := by
    intro j
    induction j with
    | zero => intro _; simp [hx0]
    | succ j ih =>
      intro hj
      rw [pow_succ', Module.End.mul_apply, ih (by omega), LinearMap.add_apply,
        LinearMap.comp_apply, hC j hj, hrec j hj]
  refine ⟨f, C, ?_⟩
  rw [← hEtop, hE_def]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < k := by have := i.2; omega
    exact ⟨⟨i, hi⟩, (hpow i hi).symm⟩
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) < n := by have := i.2; omega
    exact ⟨⟨i, hi⟩, hpow i i.2⟩

/-- **Pole-shifting theorem** (Wonham 1967; Coron, *Control and Nonlinearity*, AMS 2007,
Theorem 10.1, over `ℝ`; Sontag, *Mathematical Control Theory*, 2nd ed., Theorem 13, over any
field). If the linear control system `ẋ = A x + B u` on an `n`-dimensional space `V` with
control space `U` satisfies the Kalman rank condition `Span {A^i B u : u ∈ U, 0 ≤ i < n} = V`,
then every monic polynomial of degree `n` is the characteristic polynomial of `A + B K` for some
linear feedback `K : V → U`. -/
theorem exists_charpoly_add_comp_eq [FiniteDimensional 𝕜 V] {U : Type*} [AddCommGroup U]
    [Module 𝕜 U] (A : Module.End 𝕜 V) (B : U →ₗ[𝕜] V)
    (hK : Submodule.span 𝕜 {x | ∃ i < finrank 𝕜 V, ∃ u : U, x = (A ^ i) (B u)} = ⊤)
    (P : 𝕜[X]) (hP : P.Monic) (hdeg : P.natDegree = finrank 𝕜 V) :
    ∃ K : V →ₗ[𝕜] U, (A + B ∘ₗ K).charpoly = P := by
  obtain ⟨f, C, hcyc⟩ := exists_span_pow_add_comp_eq_top A B hK
  obtain ⟨K₁, hK₁⟩ := exists_charpoly_add_smulRight_eq (A + B ∘ₗ C) (B f) hcyc P hP hdeg
  refine ⟨C + K₁.smulRight f, ?_⟩
  have : A + B ∘ₗ (C + K₁.smulRight f) = A + B ∘ₗ C + K₁.smulRight (B f) := by
    ext y
    simp [add_assoc]
  rw [this, hK₁]

end MathlibExt.Analysis.Control
