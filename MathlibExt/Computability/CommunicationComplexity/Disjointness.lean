/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Minimax
import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Randomized communication complexity of set disjointness

Alice holds `x ∈ {0,1}^n`, Bob holds `y ∈ {0,1}^n`, and they must decide whether the sets with
characteristic vectors `x` and `y` intersect. Kalyanasundaram and Schnitger proved that every
randomized protocol with error bounded away from `1/2` needs `Ω(n)` bits, and Razborov gave a
distributional proof. This is the lower bound behind the streaming space lower bounds of Alon,
Matias and Szegedy.

The proof of `randComplexity_disjFn_ge` gives the constant `(1 - 2 * ε) ^ 2 / 32`.
Assign each coordinate independently to one of the players and give that player a uniform bit.
The resulting inputs are disjoint. Compare forcing both bits at one coordinate to zero with
forcing them both to one. The rectangle lemma bounds the decrease in each leaf's probability by
the biases of that coordinate under the two possible assignments. A depth-`k` tree has at most
`2 ^ k` leaves, so an exponential moment bound controls the sum of these biases. Averaging over
the public coins then compares the tree depth with the protocol's distinguishing advantage.
-/

@[expose] public section

namespace MathlibExt.Computability.CommunicationComplexity

/-- **Set intersection function.** `disjFn n x y` is `true` iff the subsets of `{1, …, n}` with
characteristic vectors `x` and `y` intersect; this is the function `DISₙ` of N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), Section 3 (its negation is set disjointness). -/
def disjFn (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (∃ i, x i = true ∧ y i = true)

namespace disjFn

open BooleanCube Finset
open scoped BigOperators

variable {n : ℕ}

private abbrev BitProtocol (n : ℕ) := Protocol (BoolCube n) (BoolCube n)

-- Exponential moment of the signed agreement with a fixed word on the uniform cube.
private lemma moment (w : BoolCube n) (r : ℝ) :
    (𝔼 x : BoolCube n, Real.exp (r * ∑ i, cubeVal (w i) * cubeVal (x i))) ≤
      Real.exp (n * (r ^ 2 / 2)) := by
  have bit (a : Bool) : ∑ b : Bool, Real.exp (r * (cubeVal a * cubeVal b)) =
      2 * Real.cosh r := by
    cases a <;> simp [cubeVal, Real.cosh_eq] <;> ring
  rw [expect_eq_sum_div_two_pow]
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun i b => Real.exp (r * (cubeVal (w i) * cubeVal b)))]
  simp_rw [bit, prod_const, card_univ, Fintype.card_fin, mul_pow]
  rw [mul_div_cancel_left₀ _ (by positivity), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq r) _

private lemma exp_expect_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    Real.exp (𝔼 x, f x) ≤ 𝔼 x, Real.exp (f x) := by
  let m := 𝔼 x, f x
  have h := expect_le_expect (s := univ) (f := fun x => f x - m + 1)
    (g := fun x => Real.exp (f x - m)) fun x _ => Real.add_one_le_exp _
  simp_rw [expect_add_distrib, expect_sub_distrib, Fintype.expect_const, Real.exp_sub,
    ← expect_div] at h
  have hm : 𝔼 x, f x = m := rfl
  rw [hm, sub_self, zero_add, le_div_iff₀ (Real.exp_pos m), one_mul] at h
  exact h

-- Signed mass on the fiber T x = t, weighted by the sign of the i-th input bit.
private noncomputable def bias {α : Type*} [DecidableEq α] (T : BoolCube n → α)
    (i : Fin n) (t : α) : ℝ := 𝔼 x, if T x = t then cubeVal (x i) else 0

-- At each leaf, predict each bit by the sign of its bias. The expected score is the sum
-- of the absolute biases, and its exponential moment is bounded by summing over all leaves.
private lemma bias_bound {α : Type*} [DecidableEq α] (L : Finset α) (T : BoolCube n → α)
    (hT : ∀ x, T x ∈ L) (k : ℕ) (hL : L.card ≤ 2 ^ k) (r : ℝ) :
    r * ∑ i, ∑ t ∈ L, |bias T i t| ≤ k + n * (r ^ 2 / 2) := by
  let w (t : α) (i : Fin n) := decide (0 ≤ bias T i t)
  let score (t : α) (x : BoolCube n) := ∑ i, cubeVal (w t i) * cubeVal (x i)
  have hsign (t : α) (i : Fin n) : cubeVal (w t i) * bias T i t = |bias T i t| := by
    by_cases h : 0 ≤ bias T i t
    · simp [w, h, abs_of_nonneg h]
    · simp [w, h, abs_of_neg (lt_of_not_ge h)]
  have hscore : (𝔼 x, score (T x) x) = ∑ i, ∑ t ∈ L, |bias T i t| := by
    simp_rw [← hsign, bias, mul_expect, mul_ite, mul_zero, ← expect_sum_comm]
    simp [score, hT]
  apply Real.exp_le_exp.mp
  rw [← hscore, Finset.mul_expect, Real.exp_add]
  refine (exp_expect_le _).trans ?_
  calc
    _ ≤ 𝔼 x, ∑ t ∈ L, Real.exp (r * score t x) := expect_le_expect fun x _ =>
      single_le_sum (fun t _ => (Real.exp_pos _).le) (hT x)
    _ ≤ ∑ _t ∈ L, Real.exp (n * (r ^ 2 / 2)) := by
      rw [expect_sum_comm]
      exact sum_le_sum fun t _ => moment (w t) r
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      gcongr
      calc (L.card : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hL
           _ ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num)
             (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
           _ = Real.exp k := by rw [← Real.exp_nat_mul]; simp

-- The selector d assigns each coordinate to one player, who receives a uniform bit there.
-- Forcing both players' bits at i lets us compare disjoint and singly intersecting inputs.
private def masked (d s : BoolCube n) (owner : Bool) : BoolCube n :=
  fun j => if d j = owner then s j else false

private def forced (d s : BoolCube n) (i : Fin n) (owner b : Bool) : BoolCube n :=
  Function.update (masked d s owner) i b

private lemma forced_disj (d s : BoolCube n) (i : Fin n) (b : Bool) :
    disjFn n (forced d s i true b) (forced d s i false b) = b := by
  cases b
  · simp only [disjFn, decide_eq_false_iff_not, not_exists, not_and]
    intro j
    by_cases hj : j = i
    · simp [hj, forced]
    · cases hd : d j <;> simp [forced, Function.update_of_ne hj, masked, hd]
  · simp only [disjFn, decide_eq_true_eq]
    exact ⟨i, by simp [forced], by simp [forced]⟩

private def mix (d x y : BoolCube n) : BoolCube n := fun j => if d j then x j else y j

private lemma pair_expect (f : BoolCube n → BoolCube n → ℝ) :
    (𝔼 z : BoolCube n × BoolCube n, f z.1 z.2) = 𝔼 x, 𝔼 y, f x y := by
  rw [← univ_product_univ, expect_product']

private lemma expect_mix (d : BoolCube n) (f : BoolCube n → ℝ) :
    (𝔼 s, f s) = 𝔼 x, 𝔼 y, f (mix d x y) := by
  let swap (z : BoolCube n × BoolCube n) := (mix d z.1 z.2, mix d z.2 z.1)
  have hinv : Function.Involutive swap := by
    intro z
    apply Prod.ext <;> funext j <;> cases hd : d j <;> simp [swap, mix, hd]
  calc
    _ = 𝔼 z : BoolCube n × BoolCube n, f z.1 := by
      rw [pair_expect (fun x _ => f x)]; simp_rw [Fintype.expect_const]
    _ = 𝔼 z : BoolCube n × BoolCube n, f (mix d z.1 z.2) :=
      (Fintype.expect_bijective swap hinv.bijective _ (fun z => f z.1) (fun _ => rfl)).symm
    _ = _ := pair_expect (fun x y => f (mix d x y))

private noncomputable def mass (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool)
    (a b : Bool) : ℝ := 𝔼 s,
  if p.transcript (forced d s i true a) (forced d s i false b) = t then 1 else 0

private lemma mass_nonneg (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool)
    (a b : Bool) :
    0 ≤ mass p d i t a b :=
  expect_nonneg fun _ _ => by split <;> norm_num

-- After fixing d, the remaining random bits of the two players are independent.
-- The rectangle property therefore factors each transcript mass into two one-player masses.
private lemma mass_cross (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool) :
    mass p d i t false false * mass p d i t true true =
      mass p d i t true false * mass p d i t false true := by
  classical
  let A (a : Bool) (x : BoolCube n) : Prop := ∃ y, p.transcript (forced d x i true a) y = t
  let B (b : Bool) (y : BoolCube n) : Prop := ∃ x, p.transcript x (forced d y i false b) = t
  have fac (a b : Bool) : mass p d i t a b =
      (𝔼 x, if A a x then (1 : ℝ) else 0) * (𝔼 y, if B b y then (1 : ℝ) else 0) := by
    rw [mass, expect_mix d, Fintype.expect_mul_expect]
    refine expect_congr rfl fun x _ => expect_congr rfl fun y _ => ?_
    have hx : masked d (mix d x y) true = masked d x true := by
      funext j; cases hd : d j <;> simp [masked, mix, hd]
    have hy : masked d (mix d x y) false = masked d y false := by
      funext j; cases hd : d j <;> simp [masked, mix, hd]
    rw [forced, forced, hx, hy]
    have hrect : p.transcript (forced d x i true a) (forced d y i false b) = t ↔
        A a x ∧ B b y := p.transcript_eq_iff ..
    change (if p.transcript (forced d x i true a) (forced d y i false b) = t then 1 else 0) = _
    by_cases hA : A a x <;> by_cases hB : B b y <;> simp [hrect, hA, hB]
  simp_rw [fac]
  ring

-- For a nonnegative rank-one table, the decrease along its diagonal is bounded by
-- the absolute changes along the two edges from the first entry.
private lemma deficit_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (h : a * e = b * c) : a - e ≤ |a - b| + |a - c| := by
  by_cases hz : a = 0
  · rw [hz]
    linarith [abs_nonneg (0 - b), abs_nonneg (0 - c)]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  by_cases hab : a ≤ b
  · have hce : c ≤ e := le_of_mul_le_mul_left
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hab) hc]) ha'
    linarith [le_abs_self (a - c), abs_nonneg (a - b)]
  by_cases hac : a ≤ c
  · have hbe : b ≤ e := le_of_mul_le_mul_left
      (by nlinarith [mul_nonneg hb (sub_nonneg.mpr hac)]) ha'
    linarith [le_abs_self (a - b), abs_nonneg (a - c)]
  rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_of_nonneg (by linarith : 0 ≤ a - c)]
  apply le_of_mul_le_mul_left _ ha'
  nlinarith [mul_nonneg (by linarith : 0 ≤ a - b) (by linarith : 0 ≤ a - c)]

private def trace (p : BitProtocol n) (d s : BoolCube n) : List Bool :=
  p.transcript (masked d s true) (masked d s false)

private lemma two_bias {α : Type*} [DecidableEq α] (T : BoolCube n → α) (i : Fin n) (t : α) :
    2 * bias T i t =
      (𝔼 s, if T (Function.update s i true) = t then (1 : ℝ) else 0) -
      (𝔼 s, if T (Function.update s i false) = t then (1 : ℝ) else 0) := by
  let f (s : BoolCube n) := if T s = t then cubeVal (s i) else 0
  change 2 * (𝔼 s, f s) = _
  rw [two_mul]
  calc
    _ = (𝔼 s, (f s + f (flipCoord s i))) := by rw [expect_add_distrib, expect_comp_flipCoord]
    _ = _ := by
      rw [← expect_sub_distrib]
      refine expect_congr rfl fun s _ => ?_
      have h := Function.update_eq_self i s
      cases hs : s i <;> rw [hs] at h <;>
        simp [f, flipCoord, hs, h] <;> split_ifs <;> norm_num

private lemma masked_update (d s : BoolCube n) (i : Fin n) (b owner : Bool) :
    masked d (Function.update s i b) owner = forced d s i owner (decide (d i = owner) && b) := by
  funext j
  by_cases hj : j = i
  · subst j; cases hd : d i <;> cases owner <;> simp [masked, forced, hd]
  · simp [masked, forced, Function.update_of_ne hj]

private lemma forced_flip (d s : BoolCube n) (i : Fin n) (owner b : Bool) :
    forced (flipCoord d i) s i owner b = forced d s i owner b := by
  funext j
  by_cases hj : j = i
  · simp [hj, forced]
  · simp [forced, Function.update_of_ne hj, masked, flipCoord_apply_of_ne _ hj]

private lemma mass_flip (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool)
    (a b : Bool) :
    mass p (flipCoord d i) i t a b = mass p d i t a b := by simp only [mass, forced_flip]

private lemma bias_eq_diff (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool) :
    2 * bias (trace p d) i t =
      mass p d i t (d i) (!d i) - mass p d i t false false := by
  rw [two_bias]
  cases hd : d i <;> simp [mass, trace, masked_update, hd]

-- Flipping the selector at i exchanges which player receives the free bit there.
-- The two assignments thus give the two edge differences of the same table.
private lemma mass_gap (p : BitProtocol n) (d : BoolCube n) (i : Fin n) (t : List Bool) :
    mass p d i t false false - mass p d i t true true ≤
      2 * (|bias (trace p d) i t| + |bias (trace p (flipCoord d i)) i t|) := by
  have h := deficit_le (mass_nonneg p d i t false false) (mass_nonneg p d i t true false)
    (mass_nonneg p d i t false true) (mass_nonneg p d i t true true) (mass_cross p d i t)
  have h₁ := congrArg abs (bias_eq_diff p d i t)
  have h₂ := congrArg abs (bias_eq_diff p (flipCoord d i) i t)
  rw [abs_sub_comm (mass p d i t false false) (mass p d i t true false),
    abs_sub_comm (mass p d i t false false) (mass p d i t false true)] at h
  cases hd : d i <;> simp [abs_mul, hd, mass_flip] at h₁ h₂ <;> linarith

private noncomputable def rejecting (p : BitProtocol n) : Finset (List Bool) := by
  classical
  exact p.leaves.filter fun t => ∃ x y, p.transcript x y = t ∧ p.eval x y = false

private def reject (p : BitProtocol n) (x y : BoolCube n) : ℝ := if p.eval x y = false then 1 else 0

private lemma reject_sum (p : BitProtocol n) (x y : BoolCube n) :
    reject p x y = ∑ t ∈ rejecting p, if p.transcript x y = t then 1 else 0 := by
  classical
  have hm : p.transcript x y ∈ rejecting p ↔ p.eval x y = false := by
    simp only [rejecting, mem_filter, p.transcript_mem_leaves, true_and]
    refine ⟨?_, fun h => ⟨x, y, rfl, h⟩⟩
    rintro ⟨x', y', ht, he⟩
    exact (p.eval_eq_of_transcript_eq ht).symm.trans he
  simp [reject, hm]

private def advantage (p : BitProtocol n) (d s : BoolCube n) (i : Fin n) : ℝ :=
  reject p (forced d s i true false) (forced d s i false false) -
    reject p (forced d s i true true) (forced d s i false true)

private lemma advantage_le (p : BitProtocol n) (d : BoolCube n) (i : Fin n) :
    (𝔼 s, advantage p d s i) ≤
      2 * ((∑ t ∈ p.leaves, |bias (trace p d) i t|) +
        ∑ t ∈ p.leaves, |bias (trace p (flipCoord d i)) i t|) := by
  have hsum (b : Bool) : (𝔼 s, reject p (forced d s i true b) (forced d s i false b)) =
      ∑ t ∈ rejecting p, mass p d i t b b := by
    simp_rw [reject_sum, mass, expect_sum_comm]
  simp only [advantage, expect_sub_distrib, hsum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ rejecting p, 2 * (|bias (trace p d) i t| +
          |bias (trace p (flipCoord d i)) i t|) := sum_le_sum fun t _ => mass_gap p d i t
    _ ≤ ∑ t ∈ p.leaves, 2 * (|bias (trace p d) i t| +
          |bias (trace p (flipCoord d i)) i t|) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun _ _ _ => by positivity
    _ = _ := by rw [← mul_sum, sum_add_distrib]

private noncomputable def gap (p : BitProtocol n) : ℝ :=
  ∑ i, 𝔼 d, 𝔼 s, advantage p d s i

private lemma gap_le (p : BitProtocol n) {r : ℝ} (hr : 0 ≤ r) :
    r * gap p ≤ 4 * (p.depth + n * (r ^ 2 / 2)) := by
  let B (d : BoolCube n) (i : Fin n) := ∑ t ∈ p.leaves, |bias (trace p d) i t|
  have hi (i : Fin n) : (𝔼 d, 𝔼 s, advantage p d s i) ≤ 4 * (𝔼 d, B d i) := by
    calc
      _ ≤ 𝔼 d, 2 * (B d i + B (flipCoord d i) i) :=
        expect_le_expect fun d _ => advantage_le p d i
      _ = _ := by
        rw [← mul_expect, expect_add_distrib, expect_comp_flipCoord (fun d => B d i) i]
        ring
  calc
    _ ≤ r * ∑ i, 4 * (𝔼 d, B d i) := mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hi i) hr
    _ = 4 * (𝔼 d, r * ∑ i, B d i) := by rw [← mul_sum, ← expect_sum_comm, ← mul_expect]; ring
    _ ≤ 4 * (𝔼 _d : BoolCube n, ((p.depth : ℝ) + n * (r ^ 2 / 2))) := by
      gcongr with d
      exact bias_bound p.leaves (trace p d) (fun _ => p.transcript_mem_leaves ..) p.depth
        p.card_leaves_le r
    _ = _ := by rw [Fintype.expect_const]

private lemma expected_advantage (P : RandomizedProtocol (BoolCube n) (BoolCube n)) {ε : ℝ}
    (herr : ∀ x y, P.error (disjFn n) x y ≤ ε) (d s : BoolCube n) (i : Fin n) :
    1 - 2 * ε ≤ ∑ p ∈ P.weights.support, P.weights p * advantage p d s i := by
  let X := forced d s i true
  let Y := forced d s i false
  have h (p : BitProtocol n) : advantage p d s i =
      1 - errorIndicator p (disjFn n) (X false) (Y false) -
        errorIndicator p (disjFn n) (X true) (Y true) := by
    change reject p (X false) (Y false) - reject p (X true) (Y true) = _
    have hdis (b : Bool) : disjFn n (X b) (Y b) = b := forced_disj d s i b
    cases h₀ : p.eval (X false) (Y false) <;> cases h₁ : p.eval (X true) (Y true) <;>
      norm_num [reject, errorIndicator, hdis, h₀, h₁]
  simp_rw [h, mul_sub, mul_one, sum_sub_distrib]
  have ht : ∑ p ∈ P.weights.support, P.weights p = 1 := P.total
  rw [ht]
  change _ ≤ 1 - P.error (disjFn n) (X false) (Y false) - P.error (disjFn n) (X true) (Y true)
  linarith [herr (X false) (Y false), herr (X true) (Y true)]

private lemma cost_bound (P : RandomizedProtocol (BoolCube n) (BoolCube n)) {ε : ℝ} (hε : ε < 1 / 2)
    (herr : ∀ x y, P.error (disjFn n) x y ≤ ε) :
    (1 - 2 * ε) ^ 2 / 32 * n ≤ P.cost := by
  let r := (1 - 2 * ε) / 4
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hlo : n * (1 - 2 * ε) ≤ ∑ p ∈ P.weights.support, P.weights p * gap p := by
    calc
      _ = ∑ _i : Fin n, 𝔼 _d : BoolCube n, 𝔼 _s : BoolCube n, (1 - 2 * ε) := by
        simp_rw [Fintype.expect_const]; simp; ring
      _ ≤ ∑ i : Fin n, 𝔼 d, 𝔼 s, ∑ p ∈ P.weights.support, P.weights p * advantage p d s i :=
        sum_le_sum fun i _ => expect_le_expect fun d _ => expect_le_expect fun s _ =>
          expected_advantage P herr d s i
      _ = _ := by
        simp_rw [expect_sum_comm, ← mul_expect]
        rw [sum_comm]
        simp only [gap, Finset.mul_sum]
  have hup : r * (∑ p ∈ P.weights.support, P.weights p * gap p) ≤
      4 * (P.cost + n * (r ^ 2 / 2)) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ P.weights.support, P.weights p * (4 * (P.cost + n * (r ^ 2 / 2))) := by
        refine sum_le_sum fun p hp => ?_
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (P.weights_nonneg p)
        have hd : p.depth ≤ P.cost := Finset.le_sup hp
        exact (gap_le p hr).trans (by gcongr)
      _ = _ := by
        rw [← sum_mul, show ∑ p ∈ P.weights.support, P.weights p = 1 from P.total, one_mul]
  have hbound := (mul_le_mul_of_nonneg_left hlo hr).trans hup
  dsimp [r] at hbound
  linarith only [hbound]

end disjFn

/-- **Randomized communication complexity of disjointness.** For every fixed `0 ≤ ε < 1/2` there
is `c > 0` such that `randComplexity (disjFn n) ε ≥ c n` for every `n`. Here `randComplexity` is
the least worst-case depth of a public-coin protocol (a distribution over deterministic protocols)
with error at most `ε` on every input.

This is the linear lower bound of B. Kalyanasundaram and G. Schnitger, "The probabilistic
communication complexity of set intersection", SIAM J. Discrete Math. 5 (1992) 545–557, and of
A. A. Razborov, "On the distributional complexity of disjointness", Theoret. Comput. Sci. 106
(1992) 385–390, as quoted in N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999),
Section 3 ("for any fixed `ε < 1/2`, `C_ε(DIS_n) ≥ Ω(n)`"; "Razborov exhibited a simple measure
`μ` … and showed that for this measure `D_ε(DIS_n | μ) ≥ Ω(n)`"). The public-coin form follows
from Razborov's distributional bound: every public-coin protocol of error `ε'` on every input has
`μ`-error at most `ε'`, so its depth is at least the distributional complexity
(`distComplexity_le_randComplexity`), which is `Ω(n)` at Razborov's fixed small error `ε'`. A
protocol with error `ε < 1/2` reaches error `ε'` by taking the majority answer of `O_ε(1)`
independent runs, which multiplies the depth by a constant depending only on `ε`. -/
theorem randComplexity_disjFn_ge :
    ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * n ≤ randComplexity (disjFn n) ε := by
  intro ε hε hhalf
  refine ⟨(1 - 2 * ε) ^ 2 / 32, by positivity [show 0 < 1 - 2 * ε by linarith], fun n => ?_⟩
  obtain ⟨q, hq⟩ := Protocol.exists_computes (disjFn n)
  obtain ⟨P, hc, he⟩ := Nat.sInf_mem
    (s := {k | ∃ P : RandomizedProtocol (Fin n → Bool) (Fin n → Bool),
      P.cost ≤ k ∧ ∀ x y, P.error (disjFn n) x y ≤ ε})
    ⟨_, Convexity.StdSimplex.single q, le_rfl, fun x y => by
      simp [RandomizedProtocol.error, errorIndicator, hq x y, hε]⟩
  exact (disjFn.cost_bound P hhalf he).trans (by exact_mod_cast hc)

end MathlibExt.Computability.CommunicationComplexity
