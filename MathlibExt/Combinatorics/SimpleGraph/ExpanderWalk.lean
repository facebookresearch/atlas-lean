/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The hitting property of expander walks

A random walk on a spectral expander with parameter `λ` that starts at a uniformly random vertex
stays inside a vertex set of density `μ` for `t + 1` consecutive times with probability at most
`(μ + λ (1 - μ)) ^ (t + 1)` (S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical
Computer Science 7 (2012), Theorem 4.17). The proof follows Vadhan: the probability is
`(1 / N) 1ᵀ (P M)^t 1_B` with `P` the projection onto `B` and `M = A / d` (Claim 4.20), and
`‖P M y‖ ≤ (μ + λ (1 - μ)) ‖y‖` for every `y` supported on `B` (Claim 4.21, proved here by
splitting `M y` as `(1 - λ) ȳ 1 + (λ ȳ 1 + M y⊥)`, which is Vadhan's matrix decomposition
`M = (1 - λ) J + λ E` applied to `y`).
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.SpectralExpander

open EndpointMapMultigraph (indicator)

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Weight of a vertex sequence: vertex weights `f` times step weights `M`. -/
private noncomputable def seqWeight (f : V → ℝ) (M : V → V → ℝ) {t : ℕ}
    (x : Fin (t + 1) → V) : ℝ :=
  (∏ i, f (x i)) * ∏ i : Fin t, M (x i.castSucc) (x i.succ)

omit [Fintype V] in
private lemma seqWeight_cons (f : V → ℝ) (M : V → V → ℝ) {t : ℕ} (v : V)
    (x : Fin (t + 1) → V) :
    seqWeight f M (Fin.cons v x : Fin (t + 2) → V) = f v * M v (x 0) * seqWeight f M x := by
  simp only [seqWeight, Fin.prod_univ_succ (n := t + 1), Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_succ (n := t), Fin.castSucc_zero, ← Fin.succ_castSucc]
  ring

/-- Probability vector of staying in `f`'s support, started at each vertex. -/
private noncomputable def stay (f : V → ℝ) (M : V → V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | t + 1 => fun v => f v * ∑ u, M v u * stay f M t u

private lemma sum_seqWeight_cons (f : V → ℝ) (M : V → V → ℝ) (t : ℕ) (v : V) :
    ∑ x : Fin t → V, seqWeight f M (Fin.cons v x : Fin (t + 1) → V) = stay f M t v := by
  induction t generalizing v with
  | zero => simp [seqWeight, stay]
  | succ t ih =>
    simp only [seqWeight_cons, stay]
    rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← ih u, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change f v * M v u * seqWeight f M (Fin.cons u y) = f v * (M v u * seqWeight f M (Fin.cons u y))
    ring

private lemma dot_self_nonneg (x : V → ℝ) : 0 ≤ x ⬝ᵥ x := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

private lemma dot_le_sqrt_mul (x y : V → ℝ) : x ⬝ᵥ y ≤ √(x ⬝ᵥ x) * √(y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have h' : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by simpa [dotProduct, sq] using h
  rw [← Real.sqrt_mul (dot_self_nonneg x)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h')

private lemma sqrt_dot_add_le (x y : V → ℝ) :
    √((x + y) ⬝ᵥ (x + y)) ≤ √(x ⬝ᵥ x) + √(y ⬝ᵥ y) := by
  rw [Real.sqrt_le_left (by positivity)]
  have hx := Real.sq_sqrt (dot_self_nonneg x)
  have hy := Real.sq_sqrt (dot_self_nonneg y)
  have hxy := dot_le_sqrt_mul x y
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm y x] at *
  nlinarith

/-- **Hitting property of expander walks.** Let `G` be a `d`-regular graph, `d ≥ 1`, that is a
spectral expander with parameter `λ`, and let `B` be a vertex set of density `μ = |B| / N`. A
random walk `V₀, V₁, …, V_t` with `t` steps from a uniformly random start vertex stays inside `B`
at all `t + 1` times with probability at most `(μ + λ (1 - μ)) ^ (t + 1)` (S. Vadhan,
*Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7 (2012),
Theorem 4.17, where the walk `V₁, …, V_t` has `t - 1` steps and the bound is
`(μ + λ (1 - μ)) ^ t`). -/
theorem walkProb_forall_mem_le [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {lam : ℝ} (h : IsSpectralExpander G d lam) (hd : 0 < d) (B : Finset V) (t : ℕ) :
    walkProb G d t (fun w => ∀ i, w i ∈ B) ≤
      ((B.card / Fintype.card V : ℝ) + lam * (1 - B.card / Fintype.card V)) ^ (t + 1) := by
  classical
  obtain ⟨hreg, hlam, hb⟩ := h
  set A := G.adjMatrix ℝ with hA
  set N : ℝ := (Fintype.card V : ℝ) with hN
  set μ : ℝ := B.card / N with hμ
  set ρ : ℝ := μ + lam * (1 - μ) with hρ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hAnn : ∀ u v, 0 ≤ A u v := fun u v => by
    simp only [hA, SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
  -- The walk probability is at most `1`.
  have hle1 : walkProb G d t (fun w => ∀ i, w i ∈ B) ≤ walkProb G d t (fun _ => True) := by
    unfold walkProb
    refine Finset.sum_le_sum fun w _ => ?_
    have : 0 ≤ (1 / N) * ∏ i : Fin t, A (w i.castSucc) (w i.succ) / d :=
      mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => div_nonneg (hAnn _ _) hdR.le)
    split_ifs <;> simp_all
  rcases isEmpty_or_nonempty V with hV | hV
  · have : walkProb G d t (fun w => ∀ i, w i ∈ B) = 0 := by
      unfold walkProb
      have : IsEmpty (Fin (t + 1) → V) := by
        refine ⟨fun w => hV.false (w 0)⟩
      simp
    rw [this]
    have hN0 : N = 0 := by simp [hN]
    have : ρ = lam := by simp [hρ, hμ, hN0]
    rw [this]; positivity
  have hNpos : 0 < N := by simp only [hN]; exact_mod_cast Fintype.card_pos
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one hNpos]
    exact (by exact_mod_cast Finset.card_le_univ B : (B.card : ℝ) ≤ Fintype.card V)
  have hρμ : μ ≤ ρ := by nlinarith
  have hρ0 : 0 ≤ ρ := hμ0.trans hρμ
  by_cases hl1 : 1 < lam
  · have h1 : 1 ≤ ρ := by nlinarith
    calc _ ≤ walkProb G d t (fun _ => True) := hle1
      _ = 1 := walkProb_true hreg hd t
      _ ≤ ρ ^ (t + 1) := one_le_pow₀ h1
  push Not at hl1
  set f : V → ℝ := indicator B with hf
  set M : V → V → ℝ := fun v u => A v u / d with hM
  have hf01 : ∀ v, f v * f v = f v := fun v => by by_cases hv : v ∈ B <;> simp [hf, indicator, hv]
  have hff : f ⬝ᵥ f = B.card := by
    rw [dotProduct, Finset.sum_congr rfl fun v _ => hf01 v]
    simp [hf, indicator]
  -- Step 1 (Vadhan, Claim 4.20): the probability is `(1 / N) ∑_v stay t v`.
  have ha : walkProb G d t (fun w => ∀ i, w i ∈ B) = (1 / N) * ∑ v, stay f M t v := by
    unfold walkProb
    have : ∀ w : Fin (t + 1) → V,
        (if ∀ i, w i ∈ B then (1 / N) * ∏ i : Fin t, A (w i.castSucc) (w i.succ) / d else 0) =
          (1 / N) * seqWeight f M w := by
      intro w
      simp only [seqWeight]
      split_ifs with hw
      · have hp : ∏ i, f (w i) = 1 := Finset.prod_eq_one fun i _ => by simp [hf, indicator, hw i]
        rw [hp, one_mul]
      · push Not at hw
        obtain ⟨i, hi⟩ := hw
        have hp : ∏ i, f (w i) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hf, indicator, hi])
        rw [hp, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl fun w _ => this w, ← Finset.mul_sum,
      ← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
    exact congrArg _ (Finset.sum_congr rfl fun v _ => sum_seqWeight_cons f M t v)
  -- Row and column sums of `A`.
  have hrow : ∀ v, ∑ u, A v u = d := fun v => by
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simp only [mulVec, dotProduct, Function.const_apply, mul_one] at this
    exact this
  have hcol : ∀ u, ∑ v, A v u = d := fun u => by
    rw [← hrow u]
    exact Finset.sum_congr rfl fun v _ => by simp only [hA, SimpleGraph.adjMatrix_apply, G.adj_comm]
  -- Step 2 (Vadhan, Claim 4.21): `P M` contracts vectors supported on `B` by the factor `ρ`.
  have hstep : ∀ y : V → ℝ, (∀ v, v ∉ B → y v = 0) →
      √((fun v => f v * ∑ u, M v u * y u) ⬝ᵥ (fun v => f v * ∑ u, M v u * y u)) ≤
        ρ * √(y ⬝ᵥ y) := by
    intro y hy
    set s := ∑ u, y u
    set ybar := s / N
    set yp : V → ℝ := fun u => y u - ybar with hyp
    have hyp0 : ∑ u, yp u = 0 := by
      simp only [hyp, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [ybar, ← hN]; field_simp; ring
    set z : V → ℝ := fun v => lam * ybar + (A *ᵥ yp) v / d with hz
    have hyy' : ∀ u, y u = yp u + ybar := fun u => by simp [hyp]
    have hMy : ∀ v, ∑ u, M v u * y u = (1 - lam) * ybar + z v := by
      intro v
      calc ∑ u, M v u * y u = ∑ u, (A v u * yp u / d + ybar * (A v u / d)) :=
            Finset.sum_congr rfl fun u _ => by rw [hyy' u]; simp only [hM]; ring
        _ = (∑ u, A v u * yp u) / d + ybar * ((∑ u, A v u) / d) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div]
        _ = (1 - lam) * ybar + z v := by
            rw [hrow v, div_self hdR.ne']
            simp only [hz, mulVec, dotProduct]
            ring
    have hsplit : (fun v => f v * ∑ u, M v u * y u) =
        ((1 - lam) * ybar) • f + (fun v => f v * z v) := by
      funext v; simp only [hMy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hsplit]
    refine (sqrt_dot_add_le _ _).trans ?_
    -- The constant part.
    have hs : |s| ≤ √(B.card : ℝ) * √(y ⬝ᵥ y) := by
      have hsf : s = f ⬝ᵥ y := by
        simp only [s, dotProduct]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v ∈ B
        · simp [hf, indicator, hv]
        · simp [hf, indicator, hv, hy v hv]
      have h2 : s ^ 2 ≤ (f ⬝ᵥ f) * (y ⬝ᵥ y) := by
        rw [hsf]
        simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f y
      rw [hff] at h2
      rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
      exact Real.abs_le_sqrt h2
    have h1 : √((((1 - lam) * ybar) • f) ⬝ᵥ (((1 - lam) * ybar) • f)) ≤
        (1 - lam) * μ * √(y ⬝ᵥ y) := by
      rw [smul_dotProduct, dotProduct_smul, hff, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← sq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
        abs_of_nonneg (by linarith : 0 ≤ 1 - lam)]
      have hyb : |ybar| * √(B.card : ℝ) ≤ μ * √(y ⬝ᵥ y) := by
        simp only [ybar, abs_div, abs_of_pos hNpos, hμ]
        have hB : √(B.card : ℝ) * √(B.card : ℝ) = B.card :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
        calc |s| * √(B.card : ℝ) ≤ √(B.card : ℝ) * √(y ⬝ᵥ y) * √(B.card : ℝ) :=
              mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
          _ = _ := by rw [mul_comm (√(B.card : ℝ)) _, mul_assoc, hB]; ring
      calc (1 - lam) * |ybar| * √(B.card : ℝ) = (1 - lam) * (|ybar| * √(B.card : ℝ)) := by ring
        _ ≤ (1 - lam) * (μ * √(y ⬝ᵥ y)) :=
            mul_le_mul_of_nonneg_left hyb (by linarith)
        _ = _ := by ring
    -- The orthogonal part.
    have hAyp : ∑ v, (A *ᵥ yp) v = 0 := by
      simp only [mulVec, dotProduct]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum, hyp0, mul_zero]
    have hzz : z ⬝ᵥ z ≤ lam ^ 2 * (y ⬝ᵥ y) := by
      have hb' := hb yp hyp0
      have hyy : y ⬝ᵥ y = yp ⬝ᵥ yp + ybar ^ 2 * N := by
        have e1 : y ⬝ᵥ y = ∑ u, (yp u * yp u + 2 * ybar * yp u + ybar ^ 2) :=
          Finset.sum_congr rfl fun u _ => by rw [hyy' u]; ring
        rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hyp0,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, dotProduct]
        ring
      have hz' : z ⬝ᵥ z = lam ^ 2 * ybar ^ 2 * N + 2 * lam * ybar * (∑ v, (A *ᵥ yp) v) / d +
          ((A *ᵥ yp) ⬝ᵥ (A *ᵥ yp)) / d ^ 2 := by
        have e1 : z ⬝ᵥ z = ∑ v, (lam ^ 2 * ybar ^ 2 + 2 * lam * ybar / d * (A *ᵥ yp) v +
            (A *ᵥ yp) v * (A *ᵥ yp) v / d ^ 2) :=
          Finset.sum_congr rfl fun v _ => by simp only [hz]; field_simp; ring
        rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← hN, ← Finset.mul_sum, ← Finset.sum_div, dotProduct]
        ring
      rw [hz', hAyp, hyy, mul_zero, zero_div, add_zero]
      have : ((A *ᵥ yp) ⬝ᵥ (A *ᵥ yp)) / d ^ 2 ≤ lam ^ 2 * (yp ⬝ᵥ yp) := by
        rw [div_le_iff₀ (by positivity)]
        calc _ ≤ ((d : ℝ) * lam) ^ 2 * (yp ⬝ᵥ yp) := hb'
          _ = _ := by ring
      linarith [this]
    have h2 : √((fun v => f v * z v) ⬝ᵥ (fun v => f v * z v)) ≤ lam * √(y ⬝ᵥ y) := by
      have hle : (fun v => f v * z v) ⬝ᵥ (fun v => f v * z v) ≤ z ⬝ᵥ z := by
        simp only [dotProduct]
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : v ∈ B
        · simp [hf, indicator, hv]
        · have : f v = 0 := by simp [hf, indicator, hv]
          rw [this, zero_mul, mul_zero]
          exact mul_self_nonneg _
      calc _ ≤ √(z ⬝ᵥ z) := Real.sqrt_le_sqrt hle
        _ ≤ √(lam ^ 2 * (y ⬝ᵥ y)) := Real.sqrt_le_sqrt hzz
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam]
    calc _ ≤ (1 - lam) * μ * √(y ⬝ᵥ y) + lam * √(y ⬝ᵥ y) := add_le_add h1 h2
      _ = ρ * √(y ⬝ᵥ y) := by rw [hρ]; ring
  -- Step 3: iterate.
  have hsupp : ∀ t v, v ∉ B → stay f M t v = 0 := by
    intro t v hv
    cases t with
    | zero => simp [stay, hf, indicator, hv]
    | succ t => simp [stay, hf, indicator, hv]
  have hnorm : ∀ t, √(stay f M t ⬝ᵥ stay f M t) ≤ ρ ^ t * √(B.card : ℝ) := by
    intro t
    induction t with
    | zero => simp [stay, hff]
    | succ t ih =>
      have := hstep (stay f M t) (hsupp t)
      calc √(stay f M (t + 1) ⬝ᵥ stay f M (t + 1)) ≤ ρ * √(stay f M t ⬝ᵥ stay f M t) := this
        _ ≤ ρ * (ρ ^ t * √(B.card : ℝ)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = _ := by ring
  have hsum : ∑ v, stay f M t v ≤ B.card * ρ ^ t := by
    have heq : ∑ v, stay f M t v = f ⬝ᵥ stay f M t := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ B
      · simp [hf, indicator, hv]
      · rw [hsupp t v hv]; simp
    rw [heq]
    calc _ ≤ √(f ⬝ᵥ f) * √(stay f M t ⬝ᵥ stay f M t) := dot_le_sqrt_mul _ _
      _ ≤ √(B.card : ℝ) * (ρ ^ t * √(B.card : ℝ)) := by
          rw [hff]; exact mul_le_mul_of_nonneg_left (hnorm t) (Real.sqrt_nonneg _)
      _ = _ := by
          rw [mul_comm (ρ ^ t), ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [ha]
  calc 1 / N * ∑ v, stay f M t v ≤ 1 / N * (B.card * ρ ^ t) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = μ * ρ ^ t := by rw [hμ]; ring
    _ ≤ ρ * ρ ^ t := mul_le_mul_of_nonneg_right hρμ (pow_nonneg hρ0 _)
    _ = ρ ^ (t + 1) := by ring

/-- **Spectral expanders have logarithmic diameter.** Let `G` be a `d`-regular graph, `d ≥ 1`, on
`N` vertices that is a spectral expander with parameter `λ`, and let `ℓ` satisfy `λ^ℓ N < 1`.
Then any two vertices `s` and `t` are joined by a walk of length exactly `ℓ`; in particular `G`
is connected with diameter at most `ℓ`, which is `O(log N / log (1 / λ))` for `λ < 1`
(O. Reingold, *Undirected ST-connectivity in log-space*, ECCC TR04-094 (2004), Proposition 2.2,
proved there through vertex expansion; S. Vadhan, *Pseudorandomness* (2012), Problem 4.2 (3)).
The proof is spectral: `(A^ℓ)_{s t} ≥ d^ℓ (1 / N - λ^ℓ) > 0`, and `(A^ℓ)_{s t}` counts the walks
of length `ℓ` from `s` to `t`. -/
theorem exists_walk_length_eq_of_pow_mul_lt {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {lam : ℝ} (h : IsSpectralExpander G d lam) (hd : 0 < d) {ℓ : ℕ}
    (hℓ : lam ^ ℓ * Fintype.card V < 1) (s t : V) : ∃ p : G.Walk s t, p.length = ℓ := by
  classical
  obtain ⟨hreg, hlam, hb⟩ := h
  have hrow : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
    funext v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simpa using this
  set A := G.adjMatrix ℝ with hA
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : 0 < N := by simp only [hN]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- `A` preserves the vectors orthogonal to the constants.
  have hpres : ∀ x : V → ℝ, ∑ i, x i = 0 → ∑ i, (A *ᵥ x) i = 0 := by
    intro x hx
    have : ∑ i, (A *ᵥ x) i = (1 : V → ℝ) ⬝ᵥ (A *ᵥ x) := by simp [dotProduct]
    rw [this, dotProduct_mulVec, ← mulVec_transpose, G.transpose_adjMatrix, hrow,
      smul_dotProduct, one_dotProduct, hx, smul_zero]
  have hpow : ∀ k : ℕ, ∀ x : V → ℝ, ∑ i, x i = 0 →
      ∑ i, ((A ^ k) *ᵥ x) i = 0 ∧
        ((A ^ k) *ᵥ x) ⬝ᵥ ((A ^ k) *ᵥ x) ≤ (((d : ℝ) * lam) ^ 2) ^ k * (x ⬝ᵥ x) := by
    intro k
    induction k with
    | zero => intro x hx; simp [hx]
    | succ k ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      rw [pow_succ', ← mulVec_mulVec]
      refine ⟨hpres _ h1, ?_⟩
      calc _ ≤ ((d : ℝ) * lam) ^ 2 * (((A ^ k) *ᵥ x) ⬝ᵥ ((A ^ k) *ᵥ x)) := hb _ h1
        _ ≤ ((d : ℝ) * lam) ^ 2 * ((((d : ℝ) * lam) ^ 2) ^ k * (x ⬝ᵥ x)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = _ := by ring
  have hpow1' : ∀ k : ℕ, (A ^ k) *ᵥ (1 : V → ℝ) = ((d : ℝ) ^ k) • (1 : V → ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hrow, smul_smul, pow_succ]
  have hpow1 := hpow1' ℓ
  -- Decompose `e_t = (1 / N) 1 + x`.
  set x : V → ℝ := fun w => (if w = t then 1 else 0) - 1 / N with hx
  have hxsum : ∑ i, x i = 0 := by
    simp only [hx, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    field_simp
    ring
  have hxx : x ⬝ᵥ x ≤ 1 := by
    have : ∀ w, x w * x w = (if w = t then 1 else 0) * (1 - 2 / N) + (1 / N) ^ 2 := by
      intro w; by_cases hw : w = t <;> simp [hx, hw] <;> ring
    rw [dotProduct, Finset.sum_congr rfl fun w _ => this w, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]
    have : 1 * (1 - 2 / N) + N * (1 / N) ^ 2 = 1 - 1 / N := by field_simp; ring
    rw [this]
    have : 0 < 1 / N := by positivity
    linarith
  have het : (fun w => if w = t then (1 : ℝ) else 0) = (1 / N) • (1 : V → ℝ) + x := by
    funext w; simp [hx]
  have hentry : (A ^ ℓ) s t = ((A ^ ℓ) *ᵥ fun w => if w = t then (1 : ℝ) else 0) s := by
    simp [mulVec, dotProduct]
  obtain ⟨-, hnorm⟩ := hpow ℓ x hxsum
  set y := (A ^ ℓ) *ᵥ x
  have hys : |y s| ≤ ((d : ℝ) * lam) ^ ℓ := by
    have h1 : y s ^ 2 ≤ y ⬝ᵥ y := by
      rw [dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ s), sq]
      have : 0 ≤ ∑ i ∈ Finset.univ.erase s, y i * y i :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg _
      linarith
    have h2 : y ⬝ᵥ y ≤ (((d : ℝ) * lam) ^ ℓ) ^ 2 := by
      calc _ ≤ (((d : ℝ) * lam) ^ 2) ^ ℓ * (x ⬝ᵥ x) := hnorm
        _ ≤ (((d : ℝ) * lam) ^ 2) ^ ℓ * 1 := mul_le_mul_of_nonneg_left hxx (by positivity)
        _ = _ := by ring
    exact abs_le_of_sq_le_sq' (h1.trans h2) (by positivity) |> fun h => abs_le.mpr h
  have hpos : 0 < (A ^ ℓ) s t := by
    rw [hentry, het, mulVec_add, mulVec_smul, hpow1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    have hlow := (abs_le.mp hys).1
    have hdl : ((d : ℝ) * lam) ^ ℓ = (d : ℝ) ^ ℓ * lam ^ ℓ := mul_pow _ _ _
    have hdpos : 0 < (d : ℝ) ^ ℓ := pow_pos hdR ℓ
    have : (d : ℝ) ^ ℓ * lam ^ ℓ < (d : ℝ) ^ ℓ * (1 / N) := by
      apply mul_lt_mul_of_pos_left _ hdpos
      rw [lt_div_iff₀ hNpos]; linarith
    nlinarith
  rw [hA, SimpleGraph.adjMatrix_pow_apply_eq_card_walk] at hpos
  have hcard : 0 < Fintype.card {p : G.Walk s t | p.length = ℓ} := by exact_mod_cast hpos
  obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hcard
  exact ⟨p, hp⟩

end MathlibExt.Combinatorics.SpectralExpander
