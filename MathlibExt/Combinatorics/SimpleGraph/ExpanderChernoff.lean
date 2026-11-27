/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander
public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Chernoff bound for expander walks

The empirical mean of a bounded function along a random walk on a spectral expander has
exponentially small probability of deviating from its uniform mean by at least `λ + ε`.
-/

public section

open Finset Matrix
open scoped Function

namespace MathlibExt.GraphTheory.SpectralExpanderWanted

open MathlibExt.Combinatorics.SpectralExpander

variable {V : Type*} [Fintype V]

private noncomputable abbrev euclideanNorm (x : V → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ V)‖

private lemma euclideanNorm_sq (x : V → ℝ) : euclideanNorm x ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, sq]

private lemma abs_dot_le (x y : V → ℝ) : |x ⬝ᵥ y| ≤ euclideanNorm x * euclideanNorm y := by
  simpa only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply', conj_trivial, mul_comm,
    dotProduct] using abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ V)
      (WithLp.toLp 2 y)

private lemma euclideanNorm_mul_le (b x : V → ℝ) {B : ℝ}
    (hB₀ : 0 ≤ B) (hB : ∀ v, b v ^ 2 ≤ B) :
    euclideanNorm (b * x) ≤ √B * euclideanNorm x := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    mul_pow, Real.sq_sqrt hB₀, euclideanNorm_sq, euclideanNorm_sq]
  simp only [dotProduct, mul_sum, Pi.mul_apply]
  exact sum_le_sum fun v _ => by
    simpa only [mul_mul_mul_comm, sq] using mul_le_mul_of_nonneg_right (hB v) (sq_nonneg (x v))

private noncomputable def diagonalStep (M : Matrix V V ℝ) (b x : V → ℝ) : V → ℝ :=
  b * (M *ᵥ (b * x))

private lemma diagonalStep_norm_le [Nonempty V] {M : Matrix V V ℝ}
    (hsym : Mᵀ = M) (hrow : M *ᵥ (1 : V → ℝ) = 1) {lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hb : IsSpectralBound M lam)
    (b : V → ℝ) {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ v, b v ^ 2 ≤ B) (x : V → ℝ) :
    euclideanNorm (diagonalStep M b x) ≤
      ((1 - lam) * ((1 / Fintype.card V : ℝ) * (b ⬝ᵥ b)) + lam * B) * euclideanNorm x := by
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let y := b * x
  let m : ℝ := (∑ v, y v) / N
  let z : V → ℝ := y - m • 1
  -- The remainder after removing `(1 - lam)` times the constant projection contracts by `lam`.
  let r : V → ℝ := (lam * m) • 1 + M *ᵥ z
  have hsum : ∑ v, z v = 0 := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, m]
    change (∑ v, y v) - N * ((∑ v, y v) / N) = 0
    field_simp
    ring
  have hMz : (1 : V → ℝ) ⬝ᵥ (M *ᵥ z) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hrow, one_dotProduct, hsum]
  have hy : y = m • 1 + z := by simp [z]
  have hones : (1 : V → ℝ) ⬝ᵥ 1 = N := by simp [N, dotProduct]
  have hy₂ : y ⬝ᵥ y = m ^ 2 * N + z ⬝ᵥ z := by
    rw [hy, add_dotProduct, dotProduct_add, dotProduct_add]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_one, one_dotProduct, hsum, mul_zero, add_zero, zero_add, Pi.smul_apply,
      Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul]
    change m * (N * m) + z ⬝ᵥ z = _
    ring
  have hr₂ : r ⬝ᵥ r = (lam * m) ^ 2 * N + (M *ᵥ z) ⬝ᵥ (M *ᵥ z) := by
    simp [r, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (M *ᵥ z) 1, hMz, hones]
    ring
  have hr : euclideanNorm r ≤ lam * euclideanNorm y := by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hlam₀ (norm_nonneg _)),
      mul_pow, euclideanNorm_sq, euclideanNorm_sq, hr₂, hy₂]
    linarith only [hb z hsum]
  have hsplit : diagonalStep M b x = ((1 - lam) * m) • b + b * r := by
    change b * (M *ᵥ y) = _
    rw [hy, mulVec_add, mulVec_smul, hrow]
    funext v
    simp only [r, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    ring
  have hmean : m = (b ⬝ᵥ x) / N := by rfl
  have hfirst :
      euclideanNorm (((1 - lam) * m) • b) ≤
        ((1 - lam) * ((1 / N) * (b ⬝ᵥ b))) * euclideanNorm x := by
    rw [show euclideanNorm (((1 - lam) * m) • b) =
        |(1 - lam) * m| * euclideanNorm b by
      simp only [euclideanNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlam₁), hmean, abs_div, abs_of_pos hN,
      ← euclideanNorm_sq]
    calc
      _ ≤ (1 - lam) * ((euclideanNorm b * euclideanNorm x) / N) * euclideanNorm b := by
        gcongr
        exact abs_dot_le b x
      _ = _ := by ring
  have hsecond : euclideanNorm (b * r) ≤ lam * B * euclideanNorm x := by
    calc
      _ ≤ √B * euclideanNorm r := euclideanNorm_mul_le b r hB₀ hB
      _ ≤ √B * (lam * (√B * euclideanNorm x)) := by
        gcongr
        exact hr.trans (mul_le_mul_of_nonneg_left (euclideanNorm_mul_le b x hB₀ hB) hlam₀)
      _ = lam * (√B * √B) * euclideanNorm x := by ring
      _ = _ := by rw [Real.mul_self_sqrt hB₀]
  rw [hsplit]
  refine (norm_add_le (WithLp.toLp 2 _) (WithLp.toLp 2 _)).trans
    ((add_le_add hfirst hsecond).trans_eq ?_)
  change _ = ((1 - lam) * ((1 / N) * (b ⬝ᵥ b)) + lam * B) * euclideanNorm x
  ring

/-- Expanding the iterated diagonal and transition operators gives the weighted walk sum. -/
private lemma sum_weighted_walks (M : Matrix V V ℝ) (b : V → ℝ) (t : ℕ) :
    (∑ w : Fin (t + 1) → V, (∏ i, b (w i) ^ 2) *
        ∏ i : Fin t, M (w i.castSucc) (w i.succ)) = b ⬝ᵥ (diagonalStep M b)^[t] b := by
  let weight (k : ℕ) (w : Fin (k + 1) → V) : ℝ :=
    (∏ i, b (w i) ^ 2) * ∏ i : Fin k, M (w i.castSucc) (w i.succ)
  have cons (k : ℕ) (v : V) (w : Fin (k + 1) → V) :
      weight (k + 1) (Fin.cons v w) = b v ^ 2 * (M v (w 0) * weight k w) := by
    simp only [weight, Fin.prod_univ_succ (n := k + 1), Fin.prod_univ_succ (n := k),
      Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
    ring
  have fromVertex (k : ℕ) (v : V) :
      (∑ w : Fin k → V, weight k (Fin.cons v w)) = b v * ((diagonalStep M b)^[k] b) v := by
    induction k generalizing v with
    | zero => simp [weight, pow_two]
    | succ k ih =>
      rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, cons, Fin.cons_zero, ← mul_sum, ih]
      rw [Function.iterate_succ_apply']
      simp only [diagonalStep, Pi.mul_apply, mulVec, dotProduct, mul_sum]
      refine sum_congr rfl fun u _ => ?_
      ring
  change ∑ w, weight t w = _
  rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, fromVertex, dotProduct]

/-- Exponential moment of a sum of centred observations along the walk. -/
private lemma exponentialMoment_le [Nonempty V] {M : Matrix V V ℝ}
    (hsym : Mᵀ = M) (hrow : M *ᵥ (1 : V → ℝ) = 1) {lam : ℝ}
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hb : IsSpectralBound M lam)
    (g : V → ℝ) (hg : ∀ v, |g v| ≤ 1) (hgsum : ∑ v, g v = 0)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (t : ℕ) :
    (1 / Fintype.card V : ℝ) *
        (∑ w : Fin (t + 1) → V, Real.exp (s * ∑ i, g (w i)) *
          ∏ i : Fin t, M (w i.castSucc) (w i.succ)) ≤
      Real.exp ((s * lam + s ^ 2) * (t + 1)) := by
  let b : V → ℝ := fun v => Real.exp (s * g v / 2)
  let a : ℝ := s * lam + s ^ 2
  let B : ℝ := 1 + s + s ^ 2
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; positivity
  have hb_exp (v : V) : b v ^ 2 = Real.exp (s * g v) := by
    change Real.exp (s * g v / 2) ^ 2 = _
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpoint (v : V) : b v ^ 2 ≤ 1 + s * g v + s ^ 2 := by
    have h := calc
      |s * g v| = s * |g v| := by rw [abs_mul, abs_of_nonneg hs₀]
      _ ≤ s := by simpa using mul_le_mul_of_nonneg_left (hg v) hs₀
    have hsq : (s * g v) ^ 2 ≤ s ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hs₀])
    rw [hb_exp]
    linarith only [le_abs_self (Real.exp (s * g v) - 1 - s * g v),
      Real.abs_exp_sub_one_sub_id_le (h.trans hs₁), hsq]
  have hB (v : V) : b v ^ 2 ≤ B := by
    have hv : g v ≤ 1 := (le_abs_self _).trans (hg v)
    dsimp [B]
    linarith only [hpoint v, mul_le_mul_of_nonneg_left hv hs₀]
  have hmean : (1 / N) * (b ⬝ᵥ b) ≤ 1 + s ^ 2 := by
    rw [one_div, inv_mul_le_iff₀ hN]
    calc
      b ⬝ᵥ b = ∑ v, b v ^ 2 := by simp [dotProduct, pow_two]
      _ ≤ ∑ v, (1 + s * g v + s ^ 2) := sum_le_sum fun v _ => hpoint v
      _ = N * (1 + s ^ 2) := by
        simp only [sum_add_distrib, ← mul_sum, hgsum, mul_zero, add_zero, sum_const,
          card_univ, nsmul_eq_mul]
        change N * 1 + N * s ^ 2 = _
        ring
  have hmean' : (1 / N) * (b ⬝ᵥ b) ≤ Real.exp a := calc
    _ ≤ 1 + s ^ 2 := hmean
    _ ≤ a + 1 := by dsimp [a]; nlinarith only [mul_nonneg hs₀ hlam₀]
    _ ≤ Real.exp a := Real.add_one_le_exp a
  have hstep (x : V → ℝ) :
      euclideanNorm (diagonalStep M b x) ≤ Real.exp a * euclideanNorm x := by
    apply (diagonalStep_norm_le hsym hrow hlam₀ hlam₁ hb b (by dsimp [B]; positivity) hB x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ (1 - lam) * (1 + s ^ 2) + lam * B :=
        add_le_add_left (mul_le_mul_of_nonneg_left hmean (sub_nonneg.mpr hlam₁)) _
      _ = a + 1 := by dsimp [a, B]; ring
      _ ≤ Real.exp a := Real.add_one_le_exp a
  have hiterate (k : ℕ) :
      euclideanNorm ((diagonalStep M b)^[k] b) ≤ Real.exp a ^ k * euclideanNorm b := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      exact (hstep _).trans ((mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le).trans_eq
        (mul_assoc _ _ _).symm)
  have hprod (w : Fin (t + 1) → V) :
      Real.exp (s * ∑ i, g (w i)) = ∏ i, b (w i) ^ 2 := by
    rw [mul_sum, Real.exp_sum]
    simp only [hb_exp]
  simp only [hprod]
  rw [sum_weighted_walks]
  change (1 / N) * (b ⬝ᵥ (diagonalStep M b)^[t] b) ≤ _
  calc
    _ ≤ (1 / N) * (euclideanNorm b * (Real.exp a ^ t * euclideanNorm b)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ((le_abs_self _).trans (abs_dot_le b _)).trans
        (mul_le_mul_of_nonneg_left (hiterate t) (norm_nonneg _))
    _ = ((1 / N) * (b ⬝ᵥ b)) * Real.exp a ^ t := by rw [← euclideanNorm_sq]; ring
    _ ≤ Real.exp a * Real.exp a ^ t :=
      mul_le_mul_of_nonneg_right hmean' (by positivity)
    _ = _ := by rw [← pow_succ', ← Real.exp_nat_mul, Nat.cast_succ]; dsimp [a]; congr 1; ring

private lemma upperTail_le [Nonempty V] {M : Matrix V V ℝ}
    (hsym : Mᵀ = M) (hrow : M *ᵥ (1 : V → ℝ) = 1) (hnonneg : ∀ v u, 0 ≤ M v u)
    {lam : ℝ} (hlam : 0 ≤ lam) (hb : IsSpectralBound M lam)
    (g : V → ℝ) (hg : ∀ v, |g v| ≤ 1) (hgsum : ∑ v, g v = 0)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    (∑ w : Fin (t + 1) → V, if (lam + ε) * (t + 1) ≤ ∑ i, g (w i)
      then (1 / Fintype.card V : ℝ) * ∏ i : Fin t, M (w i.castSucc) (w i.succ) else 0) ≤
      Real.exp (-(1 / 4 * ε ^ 2 * (t + 1))) := by
  let n : ℝ := (t : ℝ) + 1
  have hn : 0 < n := by dsimp [n]; positivity
  by_cases he : lam + ε ≤ 1
  · let s := ε / 2
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hmoment := exponentialMoment_le hsym hrow hlam (by linarith) hb g hg hgsum hs
      (show s ≤ 1 from by dsimp [s]; linarith) t
    let K := Real.exp (-(s * ((lam + ε) * n)))
    let p (w : Fin (t + 1) → V) := (1 / Fintype.card V : ℝ) *
      ∏ i : Fin t, M (w i.castSucc) (w i.succ)
    have hp (w : Fin (t + 1) → V) : 0 ≤ p w :=
      mul_nonneg (by positivity) (prod_nonneg fun i _ => hnonneg _ _)
    have hmarkov (w : Fin (t + 1) → V) :
        (if (lam + ε) * n ≤ ∑ i, g (w i) then p w else 0) ≤
          (K * Real.exp (s * ∑ i, g (w i))) * p w := by
      split_ifs with hw
      · apply le_mul_of_one_le_left (hp w)
        dsimp [K]
        rw [← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
        linarith only [mul_le_mul_of_nonneg_left hw hs]
      · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (hp w)
    calc
      _ ≤ ∑ w, (K * Real.exp (s * ∑ i, g (w i))) * p w :=
        sum_le_sum fun w _ => hmarkov w
      _ = K * ((1 / Fintype.card V : ℝ) *
          (∑ w : Fin (t + 1) → V, Real.exp (s * ∑ i, g (w i)) *
            ∏ i : Fin t, M (w i.castSucc) (w i.succ))) := by
        simp only [mul_sum]
        refine sum_congr rfl fun w _ => ?_
        dsimp [p]
        ring
      _ ≤ K * Real.exp ((s * lam + s ^ 2) * n) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = _ := by
        dsimp [K, s, n]
        rw [← Real.exp_add]
        congr 1
        ring
  · have hempty (w : Fin (t + 1) → V) : ¬ (lam + ε) * n ≤ ∑ i, g (w i) := by
      have hsum : ∑ i, g (w i) ≤ n := calc
        _ ≤ ∑ _ : Fin (t + 1), (1 : ℝ) :=
          sum_le_sum fun i _ => (le_abs_self _).trans (hg (w i))
        _ = n := by simp [n]
      exact not_le.mpr (hsum.trans_lt (lt_mul_of_one_lt_left hn (lt_of_not_ge he)))
    change (∑ w : Fin (t + 1) → V, if (lam + ε) * n ≤ ∑ i, g (w i)
      then _ else 0) ≤ _
    simp only [hempty, ite_false, sum_const_zero]
    exact (Real.exp_pos _).le

/-- **Chernoff bound for expander walks.** There is an absolute constant `C > 0` with the
following property. Let `G` be a `d`-regular graph, `d ≥ 1`, on a nonempty vertex set, that is a
spectral expander with parameter `λ`, let `f : V → [0, 1]` have mean `μ(f) = (1 / N) ∑_v f(v)`,
and let `V₀, …, V_t` be a random walk with `t` steps from a uniformly random start vertex. Then
for every `ε > 0`,
`Pr[|(1 / (t + 1)) ∑_{i ≤ t} f(Vᵢ) - μ(f)| ≥ λ + ε] ≤ 2 exp(-C ε² (t + 1))` (S. Vadhan,
*Pseudorandomness* (2012), Theorem 4.22, `2 e^{-Ω(ε² t)}` for a walk `V₁, …, V_t` of `t` vertices;
the bound is due to D. Gillman, SIAM J. Comput. 27 (1998)). -/
theorem chernoff_bound_expander_walk :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (d : ℕ) (lam : ℝ) (hG : IsSpectralExpander G d lam) (hd : 0 < d)
      (f : V → ℝ), (∀ v, 0 ≤ f v ∧ f v ≤ 1) → ∀ (t : ℕ) (ε : ℝ), 0 < ε →
        walkProb G d hG.1 hd t (fun w => lam + ε ≤
            |(1 / (t + 1 : ℝ)) * ∑ i, f (w i) - (1 / Fintype.card V : ℝ) * ∑ v, f v|) ≤
          2 * Real.exp (-(C * ε ^ 2 * (t + 1))) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro V _ _ _ G _ d lam hG hd f hf t ε hε
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let M : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ
  have hM (v u : V) : M v u = G.adjMatrix ℝ v u / d := by
    simp [M, div_eq_mul_inv, mul_comm]
  have hMmul (x : V → ℝ) : M *ᵥ x = (d : ℝ)⁻¹ • (G.adjMatrix ℝ *ᵥ x) :=
    smul_mulVec _ _ _
  have hsym : Mᵀ = M := by
    rw [show M = (d : ℝ)⁻¹ • G.adjMatrix ℝ from rfl, transpose_smul, G.transpose_adjMatrix]
  have hrow : M *ᵥ (1 : V → ℝ) = 1 := by
    rw [hMmul]
    funext v
    have hv := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hG.1 (v := v)
    change (G.adjMatrix ℝ *ᵥ (1 : V → ℝ)) v = (d : ℝ) * 1 at hv
    simp [hv, hdR.ne']
  have hnonneg (v u : V) : 0 ≤ M v u := by
    rw [hM]
    apply div_nonneg _ hdR.le
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hb : IsSpectralBound M lam := by
    intro x hx
    rw [hMmul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]
    calc
      _ ≤ (d : ℝ)⁻¹ ^ 2 * (((d : ℝ) * lam) ^ 2 * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left (hG.2.2 x hx) (sq_nonneg _)
      _ = _ := by rw [← mul_assoc, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ hdR.ne', one_mul]
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; positivity
  let μ : ℝ := (1 / N) * ∑ v, f v
  let g : V → ℝ := fun v => f v - μ
  have hμ₀ : 0 ≤ μ := mul_nonneg (by positivity) (sum_nonneg fun v _ => (hf v).1)
  have hμ₁ : μ ≤ 1 := by
    dsimp only [μ]
    rw [one_div, inv_mul_le_iff₀ hN, mul_one]
    exact (sum_le_sum fun v _ => (hf v).2).trans_eq (by simp [N])
  have hg (v : V) : |g v| ≤ 1 := by
    apply abs_le.mpr
    dsimp only [g]
    exact ⟨by linarith [(hf v).1], by linarith [(hf v).2]⟩
  have hgsum : ∑ v, g v = 0 := by
    simp only [g, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    change (∑ v, f v) - N * ((1 / N) * ∑ v, f v) = 0
    rw [← mul_assoc, mul_one_div_cancel hN.ne', one_mul, sub_self]
  let n : ℝ := (t : ℝ) + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hcenter (w : Fin (t + 1) → V) :
      (1 / n) * (∑ i, f (w i)) - μ = (∑ i, g (w i)) / n := by
    simp only [g, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_succ]
    change _ = ((∑ i, f (w i)) - n * μ) / n
    field_simp
  have hevent (w : Fin (t + 1) → V) :
      lam + ε ≤ |(1 / n) * ∑ i, f (w i) - μ| ↔
        (lam + ε) * n ≤ ∑ i, g (w i) ∨ (lam + ε) * n ≤ ∑ i, -g (w i) := by
    rw [hcenter, abs_eq_max_neg, le_max_iff, ← neg_div, le_div_iff₀ hn, le_div_iff₀ hn,
      sum_neg_distrib]
  let tail (u : V → ℝ) :=
    ∑ w : Fin (t + 1) → V, if (lam + ε) * n ≤ ∑ i, u (w i)
      then (1 / N) * ∏ i : Fin t, M (w i.castSucc) (w i.succ) else 0
  have htail (u : V → ℝ) (hu : ∀ v, |u v| ≤ 1) (hsum : ∑ v, u v = 0) :
      tail u ≤ Real.exp (-(1 / 4 * ε ^ 2 * n)) :=
    upperTail_le hsym hrow hnonneg hG.2.1 hb u hu hsum hε t
  calc
    _ ≤ tail g + tail (-g) := by
      unfold walkProb
      change (∑ w : Fin (t + 1) → V, if lam + ε ≤ |(1 / n) * ∑ i, f (w i) - μ|
        then _ else 0) ≤ _
      dsimp only [tail, Pi.neg_apply]
      rw [← sum_add_distrib]
      simp only [hevent, ← hM]
      refine sum_le_sum fun w _ => ?_
      have hw : 0 ≤ (1 / N) * ∏ i : Fin t, M (w i.castSucc) (w i.succ) :=
        mul_nonneg (by positivity) (prod_nonneg fun i _ => hnonneg _ _)
      by_cases h₁ : (lam + ε) * n ≤ ∑ i, g (w i) <;>
        by_cases h₂ : (lam + ε) * n ≤ ∑ i, -g (w i) <;>
        simp only [h₁, h₂, true_or, false_or, ite_true, ite_false, zero_add, add_zero] <;>
        first | exact le_rfl | exact le_add_of_nonneg_right hw
    _ ≤ _ := by
      have hneg : ∀ v, |(-g) v| ≤ 1 := by simpa only [Pi.neg_apply, abs_neg] using hg
      have hnegsum : ∑ v, (-g) v = 0 := by simp [hgsum]
      simpa only [two_mul] using add_le_add (htail g hg hgsum) (htail (-g) hneg hnegsum)

end MathlibExt.GraphTheory.SpectralExpanderWanted
