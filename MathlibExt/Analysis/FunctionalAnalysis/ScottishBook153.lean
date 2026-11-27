/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Mazur's Problem 153 has a negative answer

Mazur's Problem 153 from the Scottish Book asks whether every continuous function
`f : [0,1]² → ℝ` can be approximated uniformly, to any accuracy `ε > 0`, by finite sums
`∑ k, c k * f (a k, y) * f (x, b k)` of products of sections of `f`.
`ScottishBookProblem153Claim` states the affirmative answer, and `mazur153_refuted` proves that
it fails: some continuous function on the square is not such a uniform limit.

## Proof outline

The proof combines A. M. Davie's construction of a Banach space without the approximation
property with the passage from such a space to a continuous function of two variables.

* *Davie's vectors.* Level `n` has `4 * 2 ^ n` points and as many real Walsh characters
  (orthogonal `±1`-valued functions), grouped in `2 ^ n` blocks of four. In each block one
  character is chosen as a `σ`-character, two as `τ`-characters, and the fourth is not used. The
  vector `e n j` is a signed `σ`-character on level `n` plus a `τ`-character on level `n - 1`.
  The block choices and the signs come from a finite averaging argument (Hoeffding's lemma for
  uniform choices from finite sets), which keeps the relevant character sums of order
  `n * (3 / 2) ^ n` instead of `2 ^ n`.
* *A nuclear trace.* The column `Ψ n g`, for a point `g` of level `n`, is an explicit
  combination of the vectors `e (n + 1) i` and, for `n > 0`, `e n j`. These generating vectors
  have indices `n + 1` and `n`, but the coordinate support of the column is one level wider:
  since `e k l` with `k > 0` has its `τ`-part on level `k - 1`, the column `Ψ n g` is supported
  on levels `n - 1`, `n` and `n + 1` for `n > 0`, and on levels `0` and `1` for `n = 0`
  (compare (2.4)–(2.6) in Casazza, García and Johnson). Its sup norm is at most
  `(4 * n + 11) * (3 / 4) ^ n`. With the weights `2 ^ (-(n + 2))`, the trace
  `∑ (n, g), 2 ^ (-(n + 2)) * Ψ n g (n, g)` equals `1`, while
  `∑ (n, g), 2 ^ (-(n + 2)) * v (n, g) * Ψ n g = 0` for every vector `v` in the span of the
  `e k l` (a telescoping identity between consecutive levels).
* *A function on the square.* Place the points of all levels at the peaks of tent functions
  `T i` with disjoint supports and let `f (s, t) = ∑ Z i m * T i s * T m t`, where `Z i m` is the
  `i`-th coordinate of the rescaled column `m`. Then `f` is continuous, and the bounded
  functional `F ↦ ∑ m, w m * F (P m, P m)` (weights `w m`, peaks `P m`) is `1` on `f` and `0` on
  every product `(s, t) ↦ f (a, t) * f (s, b)`. So no finite sum of such products is uniformly
  closer to `f` than the reciprocal of the total weight.

## Implementation notes

Davie uses abelian groups of order `3 * 2 ^ n` with their complex characters, split into `2 ^ n`
characters of type `σ` and `2 ^ (n + 1)` of type `τ`. Here the groups are Boolean, the
characters are real, and blocks of four with one unused character replace the partition into
thirds, so the construction stays real-valued and the averaging argument only needs uniform
choices from finite sets.

All auxiliary declarations are private.

## References

* A. M. Davie, The approximation problem for Banach spaces, Bull. London Math. Soc. 5 (1973),
  261–266.
* P. G. Casazza, C. L. García, W. B. Johnson, An example of an asymptotically Hilbertian space
  which fails the approximation property, arXiv:math/0006134, Section 2, which reproduces
  Davie's construction in detail; the vectors, functionals and estimates here follow it.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

/-- **Mazur's Problem 153.** The claim of Mazur's Problem 153 from the Scottish Book, in its
original form: for every continuous function $f \colon [0,1]^2 \to \mathbb{R}$ and every real
$\varepsilon > 0$ there are a natural number $n$, points
$a_1, \dots, a_n, b_1, \dots, b_n \in [0,1]$ and real numbers $c_1, \dots, c_n$ such that

$$\Bigl| f(x, y) - \sum_{k=1}^n c_k \, f(a_k, y) \, f(x, b_k) \Bigr| \le \varepsilon$$

for all $x, y \in [0,1]$. -/
def ScottishBookProblem153Claim : Prop :=
  ∀ (f : C(↥(Set.Icc (0 : ℝ) 1) × ↥(Set.Icc (0 : ℝ) 1), ℝ)) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (a b : Fin n → ↥(Set.Icc (0 : ℝ) 1)) (c : Fin n → ℝ),
      ∀ (x y : ↥(Set.Icc (0 : ℝ) 1)),
        -- `dist` here is `|f (x, y) - ∑ k, c k * f (a k, y) * f (x, b k)|` by `Real.dist_eq`.
        dist (f (x, y)) (∑ k, c k * f (a k, y) * f (x, b k)) ≤ ε

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

end

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

/-! ### Boolean index types and Walsh characters -/

/-- An index type with `2 ^ n` elements: `J 0 = Unit` and `J (n + 1) = J n × Bool`. -/
private def J : ℕ → Type
  | 0 => Unit
  | n + 1 => J n × Bool

private instance instFintypeJ : ∀ n, Fintype (J n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := instFintypeJ n; inferInstanceAs (Fintype (J n × Bool))

private instance instDecEqJ : ∀ n, DecidableEq (J n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => letI := instDecEqJ n; inferInstanceAs (DecidableEq (J n × Bool))

private instance instInhabitedJ : ∀ n, Inhabited (J n)
  | 0 => inferInstanceAs (Inhabited Unit)
  | n + 1 => letI := instInhabitedJ n; inferInstanceAs (Inhabited (J n × Bool))

private theorem card_J (n : ℕ) : Fintype.card (J n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (J n × Bool) = _
    rw [Fintype.card_prod, ih, Fintype.card_bool, pow_succ]

private theorem sum_J_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : J (n + 1) → M) :
    ∑ i, f i = ∑ j : J n, ∑ b : Bool, f (j, b) :=
  Fintype.sum_prod_type (γ := M) (α₁ := J n) (α₂ := Bool) f

/-- The Walsh character `W k a x = (-1) ^ #{i | a i ∧ x i}` on `J k`. -/
private def W : (k : ℕ) → J k → J k → ℝ
  | 0, _, _ => 1
  | k + 1, a, x => W k a.1 x.1 * (if a.2 && x.2 then -1 else 1)

private theorem W_mul_self (k : ℕ) (a x : J k) : W k a x * W k a x = 1 := by
  induction k with
  | zero => simp [W]
  | succ k ih =>
    rcases a with ⟨a1, a2⟩
    rcases x with ⟨x1, x2⟩
    have h1 := ih a1 x1
    simp only [W]
    split_ifs <;> nlinarith

private theorem abs_W_le (k : ℕ) (a x : J k) : |W k a x| ≤ 1 := by
  have h := W_mul_self k a x
  nlinarith [abs_mul_abs_self (W k a x), abs_nonneg (W k a x)]

private theorem W_orth (k : ℕ) (a b : J k) :
    ∑ x, W k a x * W k b x = if a = b then (2 : ℝ) ^ k else 0 := by
  induction k with
  | zero =>
    rw [ite_eq_left (show a = b from rfl)]
    simp [W, card_J]
  | succ k ih =>
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    rw [sum_J_succ]
    simp only [W]
    have hsplit : ∀ x1 : J k, ∑ x2 : Bool,
        W k a1 x1 * (if a2 && x2 then (-1 : ℝ) else 1) * (W k b1 x1 * (if b2 && x2 then -1 else 1))
        = (W k a1 x1 * W k b1 x1) *
          ∑ x2 : Bool, (if a2 && x2 then (-1 : ℝ) else 1) * (if b2 && x2 then -1 else 1) := by
      intro x1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => by ring
    simp_rw [hsplit, ← Finset.sum_mul, ih]
    have key : ((a1, a2) : J (k + 1)) = (b1, b2) ↔ a1 = b1 ∧ a2 = b2 := by
      constructor
      · intro h
        exact ⟨congrArg (fun p : J k × Bool => p.1) h, congrArg (fun p : J k × Bool => p.2) h⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    split_ifs with h1 hab hab
    · obtain ⟨-, rfl⟩ := key.mp hab
      cases a2 <;> norm_num [pow_succ]
    · have h2 : a2 ≠ b2 := fun h2 => hab (key.mpr ⟨h1, h2⟩)
      cases a2 <;> cases b2 <;> simp_all
    · exact absurd (key.mp hab).1 h1
    · rw [zero_mul]

/-! ### A finite discrepancy bound -/

/-- Hoeffding's lemma for a finite uniform average. -/
private theorem sum_exp_mul_le {κ : Type*} [Fintype κ] (X : κ → ℝ) (hsum : ∑ c, X c = 0)
    (hbd : ∀ c, |X c| ≤ 1) (μ : ℝ) :
    ∑ c, Real.exp (μ * X c) ≤ Fintype.card κ * Real.exp (μ ^ 2 / 2) := by
  have hpt : ∀ c, Real.exp (μ * X c) ≤ Real.cosh μ + X c * Real.sinh μ := by
    intro c
    have h1 := (abs_le.mp (hbd c)).1
    have h2 := (abs_le.mp (hbd c)).2
    have ha : 0 ≤ (1 + X c) / 2 := by linarith
    have hb : 0 ≤ (1 - X c) / 2 := by linarith
    have hab : (1 + X c) / 2 + (1 - X c) / 2 = 1 := by ring
    have hconv := convexOn_exp.2 (Set.mem_univ μ) (Set.mem_univ (-μ)) ha hb hab
    simp only [smul_eq_mul] at hconv
    have hlin : (1 + X c) / 2 * μ + (1 - X c) / 2 * -μ = μ * X c := by ring
    rw [hlin] at hconv
    rw [Real.cosh_eq, Real.sinh_eq]
    linarith
  calc ∑ c, Real.exp (μ * X c) ≤ ∑ c, (Real.cosh μ + X c * Real.sinh μ) :=
        Finset.sum_le_sum fun c _ => hpt c
    _ = Fintype.card κ * Real.cosh μ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, add_zero,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Fintype.card κ * Real.exp (μ ^ 2 / 2) := by
        gcongr
        exact Real.cosh_le_exp_half_sq μ

/-- A finite discrepancy bound: independent choices with mean-zero bounded contributions. -/
private theorem exists_choice_abs_sum_le {ι T : Type*} [Fintype ι] [Fintype T]
    [Nonempty T] {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    (X : T → (i : ι) → κ i → ℝ) (hsum : ∀ t i, ∑ c, X t i c = 0)
    (hbd : ∀ t i c, |X t i c| ≤ 1) {l : ℝ} (hl : 0 < l) :
    ∃ x : (i : ι) → κ i, ∀ t, |∑ i, X t i (x i)| ≤
      Real.log (2 * Fintype.card T) / l + l * Fintype.card ι / 2 := by
  classical
  set E : ℝ := Real.exp (l ^ 2 / 2) ^ Fintype.card ι with hE
  have hEpos : 0 < E := pow_pos (Real.exp_pos _) _
  -- the moment bound for one test and one sign
  have hmom : ∀ (t : T) (μ : ℝ), μ ^ 2 = l ^ 2 →
      ∑ x : (i : ι) → κ i, Real.exp (μ * ∑ i, X t i (x i)) ≤
        Fintype.card ((i : ι) → κ i) * E := by
    intro t μ hμ
    have hprod : ∀ x : (i : ι) → κ i, Real.exp (μ * ∑ i, X t i (x i)) =
        ∏ i, Real.exp (μ * X t i (x i)) := by
      intro x
      rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun i c => Real.exp (μ * X t i c))]
    calc ∏ i, ∑ c, Real.exp (μ * X t i c)
        ≤ ∏ i, ((Fintype.card (κ i) : ℝ) * Real.exp (l ^ 2 / 2)) := by
          apply Finset.prod_le_prod₀
          · intro i _
            exact Finset.sum_nonneg fun c _ => (Real.exp_pos _).le
          · intro i _
            have := sum_exp_mul_le (X t i) (hsum t i) (hbd t i) μ
            rwa [hμ] at this
      _ = Fintype.card ((i : ι) → κ i) * E := by
          rw [Finset.prod_mul_distrib, Fintype.card_pi, Nat.cast_prod, Finset.prod_const,
            Finset.card_univ]
  set F : ((i : ι) → κ i) → ℝ := fun x =>
    ∑ t, (Real.exp (l * ∑ i, X t i (x i)) + Real.exp (-l * ∑ i, X t i (x i))) with hF
  have hsumF : ∑ x, F x ≤ ∑ _x : (i : ι) → κ i, 2 * Fintype.card T * E := by
    rw [hF, Finset.sum_comm]
    calc ∑ t, ∑ x : (i : ι) → κ i, (Real.exp (l * ∑ i, X t i (x i)) +
          Real.exp (-l * ∑ i, X t i (x i)))
        ≤ ∑ _t : T, (Fintype.card ((i : ι) → κ i) * E + Fintype.card ((i : ι) → κ i) * E) := by
          apply Finset.sum_le_sum
          intro t _
          rw [Finset.sum_add_distrib]
          exact add_le_add (hmom t l rfl) (hmom t (-l) (by ring))
      _ = ∑ _x : (i : ι) → κ i, 2 * Fintype.card T * E := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsumF
  refine ⟨x, fun t => ?_⟩
  set S := ∑ i, X t i (x i) with hS
  have hterm : Real.exp (l * |S|) ≤ 2 * Fintype.card T * E := by
    have h1 : Real.exp (l * |S|) ≤ Real.exp (l * S) + Real.exp (-l * S) := by
      rcases abs_cases S with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; linarith [Real.exp_pos (-l * S)]
      · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (l * S)]
    have h2 : Real.exp (l * S) + Real.exp (-l * S) ≤ F x := by
      rw [hF]
      exact Finset.single_le_sum (f := fun t => Real.exp (l * ∑ i, X t i (x i)) +
        Real.exp (-l * ∑ i, X t i (x i))) (fun t _ => by positivity) (Finset.mem_univ t)
    linarith
  have hT : (0 : ℝ) < 2 * Fintype.card T := by
    have := Fintype.card_pos (α := T)
    positivity
  have hlog := Real.log_le_log (Real.exp_pos _) hterm
  rw [Real.log_exp, Real.log_mul hT.ne' hEpos.ne', hE, Real.log_pow, Real.log_exp] at hlog
  have hrhs : (Real.log (2 * Fintype.card T) / l + l * Fintype.card ι / 2) * l =
      Real.log (2 * Fintype.card T) + Fintype.card ι * (l ^ 2 / 2) := by
    field_simp
  have key : |S| * l ≤ (Real.log (2 * Fintype.card T) / l + l * Fintype.card ι / 2) * l := by
    rw [hrhs]
    linarith
  exact le_of_mul_le_mul_right key hl

/-! ### The `σ`- and `τ`-characters of a level -/

private theorem W_orth_self (k : ℕ) (a : J k) : ∑ x, W k a x * W k a x = (2 : ℝ) ^ k := by
  rw [W_orth, ite_eq_left rfl]

private theorem W_orth_ne {k : ℕ} {a b : J k} (h : a ≠ b) : ∑ x, W k a x * W k b x = 0 := by
  rw [W_orth, ite_eq_right h]

/-- Signs as reals. -/
private def sg (b : Bool) : ℝ := if b then 1 else -1

private theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> norm_num [sg]

private theorem abs_sg (b : Bool) : |sg b| = 1 := by cases b <;> norm_num [sg]

/-- The `σ`-characters of level `n`. -/
private def sig (n : ℕ) (cn : J n → Bool × Bool) (j : J n) : J (n + 2) → ℝ :=
  W (n + 2) ((j, (cn j).1), (cn j).2)

/-- The `τ`-characters of level `n`, indexed by `J (n + 1)`. -/
private def tau (n : ℕ) (cn : J n → Bool × Bool) (i : J (n + 1)) : J (n + 2) → ℝ :=
  W (n + 2) ((i.1, Bool.xor (cn i.1).1 (!i.2)), Bool.xor (cn i.1).2 i.2)

private theorem sig_orth (n : ℕ) (cn : J n → Bool × Bool) (j j' : J n) :
    ∑ x, sig n cn j x * sig n cn j' x = if j = j' then (2 : ℝ) ^ (n + 2) else 0 := by
  by_cases hj : j = j'
  · subst hj
    rw [ite_eq_left rfl]
    exact W_orth_self _ _
  · rw [ite_eq_right hj]
    apply W_orth_ne
    intro h
    exact hj (congrArg (fun p : (J n × Bool) × Bool => p.1.1) h)

private theorem tau_orth (n : ℕ) (cn : J n → Bool × Bool) (i i' : J (n + 1)) :
    ∑ x, tau n cn i x * tau n cn i' x = if i = i' then (2 : ℝ) ^ (n + 2) else 0 := by
  by_cases hi : i = i'
  · subst hi
    rw [ite_eq_left rfl]
    exact W_orth_self _ _
  · rw [ite_eq_right hi]
    apply W_orth_ne
    intro h
    apply hi
    rcases i with ⟨i1, b⟩
    rcases i' with ⟨i1', b'⟩
    have h1 : i1 = i1' := congrArg (fun p : (J n × Bool) × Bool => p.1.1) h
    subst h1
    have h2 := congrArg (fun p : (J n × Bool) × Bool => p.2) h
    simp only at h2
    have hb : b = b' := by
      clear h
      revert h2
      generalize (cn i1).2 = c2
      cases b <;> cases b' <;> cases c2 <;> simp
    subst hb
    rfl

private theorem sig_tau_orth (n : ℕ) (cn : J n → Bool × Bool) (j : J n) (i : J (n + 1)) :
    ∑ x, sig n cn j x * tau n cn i x = 0 := by
  apply W_orth_ne
  intro h
  rcases i with ⟨i1, b⟩
  have h1 : j = i1 := congrArg (fun p : (J n × Bool) × Bool => p.1.1) h
  subst h1
  have h2 := congrArg (fun p : (J n × Bool) × Bool => p.1.2) h
  have h3 := congrArg (fun p : (J n × Bool) × Bool => p.2) h
  simp only at h2 h3
  clear h
  revert h2 h3
  generalize (cn j).1 = c1
  generalize (cn j).2 = c2
  cases b <;> cases c1 <;> cases c2 <;> simp

private theorem abs_sig_le (n : ℕ) (cn : J n → Bool × Bool) (j : J n) (x : J (n + 2)) :
    |sig n cn j x| ≤ 1 := abs_W_le _ _ _

private theorem abs_tau_le (n : ℕ) (cn : J n → Bool × Bool) (i : J (n + 1)) (x : J (n + 2)) :
    |tau n cn i x| ≤ 1 := abs_W_le _ _ _

private theorem sig_mul_self (n : ℕ) (cn : J n → Bool × Bool) (j : J n) (x : J (n + 2)) :
    sig n cn j x * sig n cn j x = 1 := W_mul_self _ _ _

private theorem tau_mul_self (n : ℕ) (cn : J n → Bool × Bool) (i : J (n + 1)) (x : J (n + 2)) :
    tau n cn i x * tau n cn i x = 1 := W_mul_self _ _ _

/-! ### Davie's vectors and the columns `Ψ` -/

section Vectors

variable (c : (n : ℕ) → J n → Bool × Bool) (s : (n : ℕ) → J n → Bool)

/-- Davie's vectors `e k l`, as functions of a level `m` and a point of `J (m + 2)`. -/
private def ev : (k : ℕ) → J k → (m : ℕ) → J (m + 2) → ℝ
  | 0, l, m, h => if hm : m = 0 then sg (s 0 l) * sig 0 (c 0) l (hm ▸ h) else 0
  | k + 1, l, m, h =>
      if hm : m = k + 1 then sg (s (k + 1) l) * sig (k + 1) (c (k + 1)) l (hm ▸ h)
      else if hm' : m = k then tau k (c k) l (hm' ▸ h) else 0

private theorem ev_self (k : ℕ) (l : J k) (h : J (k + 2)) :
    ev c s k l k h = sg (s k l) * sig k (c k) l h := by
  cases k <;> simp [ev]

private theorem ev_pred (k : ℕ) (l : J (k + 1)) (h : J (k + 2)) :
    ev c s (k + 1) l k h = tau k (c k) l h := by
  simp [ev]

private theorem ev_far (k : ℕ) (l : J k) (m : ℕ) (h : J (m + 2)) (h1 : m ≠ k) (h2 : m + 1 ≠ k) :
    ev c s k l m h = 0 := by
  cases k with
  | zero => simp [ev, h1]
  | succ k =>
    have h2' : m ≠ k := fun h => h2 (by omega)
    simp [ev, h1, h2']

end Vectors

section Psi

variable (c : (n : ℕ) → J n → Bool × Bool) (s : (n : ℕ) → J n → Bool)

/-- The columns `Ψ n g` of the nuclear representation. -/
private noncomputable def Psi (n : ℕ) (g : J (n + 2)) (m : ℕ) (h : J (m + 2)) : ℝ :=
  (1 / 2 ^ (n + 1)) * ∑ i : J (n + 1), tau n (c n) i g * ev c s (n + 1) i m h -
    if n = 0 then 0 else (1 / 2 ^ n) * ∑ j : J n, sg (s n j) * sig n (c n) j g * ev c s n j m h

private theorem Psi_same (n : ℕ) (g h : J (n + 2)) :
    Psi c s n g n h = (1 / 2 ^ (n + 1)) * ∑ i : J (n + 1), tau n (c n) i g * tau n (c n) i h -
      if n = 0 then 0 else (1 / 2 ^ n) * ∑ j : J n, sig n (c n) j g * sig n (c n) j h := by
  unfold Psi
  congr 1
  · simp only [ev_pred]
  · split_ifs
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_self]
      have := sg_mul_self (s n j)
      linear_combination (sig n (c n) j g * sig n (c n) j h) * this

private theorem Psi_succ (n : ℕ) (g : J (n + 2)) (h : J (n + 1 + 2)) :
    Psi c s n g (n + 1) h = (1 / 2 ^ (n + 1)) *
      ∑ i : J (n + 1), sg (s (n + 1) i) * sig (n + 1) (c (n + 1)) i h * tau n (c n) i g := by
  unfold Psi
  have h0 : ∀ j : J n, ev c s n j (n + 1) h = 0 := fun j =>
    ev_far c s n j (n + 1) h (by omega) (by omega)
  simp only [h0, mul_zero, Finset.sum_const_zero, ev_self]
  split_ifs <;> simp only [sub_zero] <;>
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

private theorem Psi_pred (k : ℕ) (g : J (k + 1 + 2)) (h : J (k + 2)) :
    Psi c s (k + 1) g k h = -((1 / 2 ^ (k + 1)) *
      ∑ j : J (k + 1), sg (s (k + 1) j) * sig (k + 1) (c (k + 1)) j g * tau k (c k) j h) := by
  unfold Psi
  have h0 : ∀ i : J (k + 1 + 1), ev c s (k + 1 + 1) i k h = 0 := fun i =>
    ev_far c s (k + 1 + 1) i k h (by omega) (by omega)
  simp only [h0, mul_zero, Finset.sum_const_zero, ev_pred, ite_eq_right (Nat.succ_ne_zero k)]
  ring

private theorem Psi_far (n : ℕ) (g : J (n + 2)) (m : ℕ) (h : J (m + 2)) (h1 : m ≠ n)
    (h2 : m ≠ n + 1) (h3 : m + 1 ≠ n) : Psi c s n g m h = 0 := by
  unfold Psi
  have hA : ∀ i : J (n + 1), ev c s (n + 1) i m h = 0 := fun i =>
    ev_far c s (n + 1) i m h h2 (by omega)
  have hB : ∀ j : J n, ev c s n j m h = 0 := fun j => ev_far c s n j m h h1 h3
  simp [hA, hB]

private theorem Psi_zero_self (g : J (0 + 2)) : Psi c s 0 g 0 g = 1 := by
  rw [Psi_same]
  simp only [tau_mul_self, Finset.sum_const, Finset.card_univ, card_J]
  norm_num

private theorem Psi_succ_self (n : ℕ) (g : J (n + 1 + 2)) : Psi c s (n + 1) g (n + 1) g = 0 := by
  rw [Psi_same]
  simp only [tau_mul_self, sig_mul_self, Finset.sum_const, Finset.card_univ, card_J,
    ite_eq_right (Nat.succ_ne_zero n), nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

/-- The operator `v ↦ ∑ n < L, ∑ g, 2 ^ (-(n + 2)) * v n g * Ψ n g`, evaluated at `(m, h)`. -/
private noncomputable def Uop (L : ℕ) (v : (n : ℕ) → J (n + 2) → ℝ) (m : ℕ) (h : J (m + 2)) : ℝ :=
  ∑ n ∈ Finset.range L, ∑ g : J (n + 2), (1 / 2 ^ (n + 2)) * v n g * Psi c s n g m h

end Psi

/-! ### The telescoping identity -/

private theorem sum_mul_sum_comm {α ι : Type*} [Fintype α] [Fintype ι] (u : α → ℝ) (v : ι → α → ℝ)
    (w : ι → ℝ) : ∑ g, u g * ∑ i, v i g * w i = ∑ i, (∑ g, u g * v i g) * w i := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring

section U1

variable (c : (n : ℕ) → J n → Bool × Bool) (s : (n : ℕ) → J n → Bool)

private theorem sum_sig_mul_Psi (n : ℕ) (l : J n) (m : ℕ) (h : J (m + 2)) :
    ∑ g, sig n (c n) l g * Psi c s n g m h =
      if n = 0 then 0 else -4 * (sg (s n l) * ev c s n l m h) := by
  unfold Psi
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hA : ∑ g, sig n (c n) l g *
      ((1 / 2 ^ (n + 1)) * ∑ i, tau n (c n) i g * ev c s (n + 1) i m h) = 0 := by
    have e1 : ∀ g, sig n (c n) l g *
        ((1 / 2 ^ (n + 1)) * ∑ i, tau n (c n) i g * ev c s (n + 1) i m h) =
        (1 / 2 ^ (n + 1)) * (sig n (c n) l g * ∑ i, tau n (c n) i g * ev c s (n + 1) i m h) :=
      fun g => by ring
    simp_rw [e1, ← Finset.mul_sum, sum_mul_sum_comm, sig_tau_orth, zero_mul,
      Finset.sum_const_zero, mul_zero]
  rw [hA, zero_sub]
  split_ifs with hn
  · simp
  · have e2 : ∀ g, sig n (c n) l g *
        ((1 / 2 ^ n) * ∑ j, sg (s n j) * sig n (c n) j g * ev c s n j m h) =
        (1 / 2 ^ n) * (sig n (c n) l g * ∑ j, sig n (c n) j g * (sg (s n j) * ev c s n j m h)) := by
      intro g
      rw [mul_left_comm]
      congr 2
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e2, ← Finset.mul_sum, sum_mul_sum_comm, sig_orth, ite_mul, zero_mul,
      Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ l)]
    rw [pow_add]
    field_simp
    ring

private theorem sum_tau_mul_Psi (n : ℕ) (i' : J (n + 1)) (m : ℕ) (h : J (m + 2)) :
    ∑ g, tau n (c n) i' g * Psi c s n g m h = 2 * ev c s (n + 1) i' m h := by
  unfold Psi
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hB : ∑ g, tau n (c n) i' g *
      (if n = 0 then 0 else (1 / 2 ^ n) * ∑ j, sg (s n j) * sig n (c n) j g * ev c s n j m h)
      = 0 := by
    split_ifs
    · simp
    · have e2 : ∀ g, tau n (c n) i' g *
          ((1 / 2 ^ n) * ∑ j, sg (s n j) * sig n (c n) j g * ev c s n j m h) =
          (1 / 2 ^ n) *
            (tau n (c n) i' g * ∑ j, sig n (c n) j g * (sg (s n j) * ev c s n j m h)) := by
        intro g
        rw [mul_left_comm]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [e2, ← Finset.mul_sum, sum_mul_sum_comm]
      have e3 : ∀ j, ∑ g, tau n (c n) i' g * sig n (c n) j g = 0 := fun j => by
        simp_rw [mul_comm (tau n (c n) i' _)]
        exact sig_tau_orth n (c n) j i'
      simp [e3]
  rw [hB, sub_zero]
  have e1 : ∀ g, tau n (c n) i' g *
      ((1 / 2 ^ (n + 1)) * ∑ i, tau n (c n) i g * ev c s (n + 1) i m h) =
      (1 / 2 ^ (n + 1)) * (tau n (c n) i' g * ∑ i, tau n (c n) i g * ev c s (n + 1) i m h) :=
    fun g => by ring
  simp_rw [e1, ← Finset.mul_sum, sum_mul_sum_comm, tau_orth, ite_mul, zero_mul,
    Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i')]
  rw [pow_succ, pow_succ]
  field_simp
  ring

private theorem Uop_ev (k : ℕ) (l : J k) (L : ℕ) (hL : k + 1 ≤ L) (m : ℕ) (h : J (m + 2)) :
    Uop c s L (ev c s k l) m h = 0 := by
  unfold Uop
  have hT : ∀ n, n ≠ k → n + 1 ≠ k →
      ∑ g : J (n + 2), (1 / 2 ^ (n + 2)) * ev c s k l n g * Psi c s n g m h = 0 := by
    intro n h1 h2
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ev_far c s k l n g h1 h2]
    ring
  have hTk : ∑ g : J (k + 2), (1 / 2 ^ (k + 2)) * ev c s k l k g * Psi c s k g m h =
      if k = 0 then 0 else -((1 / 2 ^ k) * ev c s k l m h) := by
    simp_rw [ev_self]
    have e1 : ∀ g, (1 / 2 ^ (k + 2)) * (sg (s k l) * sig k (c k) l g) * Psi c s k g m h =
        ((1 / 2 ^ (k + 2)) * sg (s k l)) * (sig k (c k) l g * Psi c s k g m h) :=
      fun g => by ring
    simp_rw [e1, ← Finset.mul_sum, sum_sig_mul_Psi]
    split_ifs
    · ring
    · have hsg := sg_mul_self (s k l)
      rw [pow_add]
      field_simp
      linear_combination (-(4 : ℝ) * ev c s k l m h) * hsg
  cases k with
  | zero =>
    rw [Finset.sum_eq_single 0]
    · rw [hTk, ite_eq_left rfl]
    · intro n _ hn
      exact hT n hn (by omega)
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
  | succ k =>
    rw [Finset.sum_eq_add (k + 1) k (by omega) ?_ ?_ ?_]
    · rw [hTk, ite_eq_right (Nat.succ_ne_zero k)]
      have hTp : ∑ g : J (k + 2), (1 / 2 ^ (k + 2)) * ev c s (k + 1) l k g * Psi c s k g m h =
          (1 / 2 ^ (k + 1)) * ev c s (k + 1) l m h := by
        simp_rw [ev_pred]
        have e1 : ∀ g, (1 / 2 ^ (k + 2)) * tau k (c k) l g * Psi c s k g m h =
            (1 / 2 ^ (k + 2)) * (tau k (c k) l g * Psi c s k g m h) := fun g => by ring
        simp_rw [e1, ← Finset.mul_sum, sum_tau_mul_Psi]
        rw [pow_succ (2 : ℝ) (k + 1)]
        field_simp
      rw [hTp]
      ring
    · intro n _ hn
      exact hT n hn.1 (fun h' => hn.2 (by omega))
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0

private theorem Uop_comb (L : ℕ) (v : (n : ℕ) → J (n + 2) → ℝ) {ι ι' : Type*} [Fintype ι]
    [Fintype ι']
    (a : ι → ℝ) (u : ι → (n : ℕ) → J (n + 2) → ℝ) (a' : ι' → ℝ)
    (u' : ι' → (n : ℕ) → J (n + 2) → ℝ)
    (hv : ∀ n g, v n g = ∑ i, a i * u i n g - ∑ j, a' j * u' j n g) (m : ℕ) (h : J (m + 2)) :
    Uop c s L v m h = ∑ i, a i * Uop c s L (u i) m h - ∑ j, a' j * Uop c s L (u' j) m h := by
  unfold Uop
  simp_rw [hv, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring

private theorem Uop_Psi (n0 : ℕ) (g0 : J (n0 + 2)) (m : ℕ) (h : J (m + 2)) :
    Uop c s (n0 + 2) (Psi c s n0 g0) m h = 0 := by
  by_cases hn0 : n0 = 0
  · subst hn0
    rw [Uop_comb c s 2 (Psi c s 0 g0) (fun i : J 1 => (1 / 2 ^ 1) * tau 0 (c 0) i g0)
      (fun i => ev c s 1 i) (fun _ : Fin 0 => (0 : ℝ)) (fun _ => fun _ _ => 0)]
    · simp [Uop_ev c s 1 _ 2 (le_refl _)]
    · intro n g
      simp only [Psi, Finset.mul_sum, Finset.univ_eq_empty, Finset.sum_empty, ite_true, sub_zero]
      exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Uop_comb c s (n0 + 2) (Psi c s n0 g0)
      (fun i : J (n0 + 1) => (1 / 2 ^ (n0 + 1)) * tau n0 (c n0) i g0)
      (fun i => ev c s (n0 + 1) i)
      (fun j : J n0 => (1 / 2 ^ n0) * (sg (s n0 j) * sig n0 (c n0) j g0))
      (fun j => ev c s n0 j)]
    · simp [Uop_ev c s (n0 + 1) _ (n0 + 2) (le_refl _), Uop_ev c s n0 _ (n0 + 2) (by omega)]
    · intro n g
      simp only [Psi, ite_eq_right hn0, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun j _ => by ring

end U1

/-! ### Choice of the blocks and of the signs -/

section Bounds

private theorem log_two_pow_le (k : ℕ) : Real.log ((2 : ℝ) ^ k) ≤ k := by
  rw [Real.log_pow]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

private theorem geom_aux (n : ℕ) :
    (3 / 4 : ℝ) ^ n * ((2 / 3) ^ n * 2 ^ n) = 1 ∧ (2 / 3 : ℝ) ^ n ≤ (3 / 4) ^ n := by
  refine ⟨?_, pow_le_pow_left₀ (by norm_num) (by norm_num) n⟩
  rw [← mul_pow, ← mul_pow]
  norm_num

private theorem E1_arith_core (L a b q : ℝ) (n : ℝ) (hapos : 0 < a) (hbpos : 0 < b)
    (hq : q * (a * b) = 1) (ha : a ≤ q) (hL : L ≤ 2 * n + 5) :
    2 / b * (L / a + a * b / 2) ≤ (4 * n + 11) * q := by
  have e : 2 / b * (L / a + a * b / 2) = 2 * L * q + a := by
    field_simp
    linear_combination (-2 * L) * hq
  rw [e]
  have hqpos : 0 < q := by nlinarith
  nlinarith

private theorem E1_arith (n : ℕ) (L : ℝ) (hL : L ≤ 2 * n + 5) :
    2 / 2 ^ n * (L / (2 / 3) ^ n + (2 / 3) ^ n * (2 ^ n : ℕ) / 2) ≤
      (4 * n + 11) * (3 / 4) ^ n := by
  obtain ⟨hq, ha⟩ := geom_aux n
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; rfl
  rw [hcast]
  exact E1_arith_core L _ _ _ n (by positivity) (by positivity) hq ha hL

private theorem E2_arith_core (L a b q : ℝ) (N : ℝ) (hapos : 0 < a) (hbpos : 0 < b)
    (hq : q * (a * b) = 1) (ha : a ≤ q) (hL : L ≤ 2 * N + 4) :
    L / a + a * b / 2 ≤ b * ((2 * N + 5) * q) := by
  have hqpos : 0 < q := by nlinarith
  have e : L / a = L * q * b := by
    field_simp
    linear_combination (-L) * hq
  rw [e]
  have h1 : L * q * b ≤ (2 * N + 4) * q * b := by gcongr
  have h2 : a * b / 2 ≤ q * b := by nlinarith
  nlinarith

private theorem E2_arith (N : ℕ) (L : ℝ) (hL : L ≤ 2 * N + 4) :
    L / (2 / 3) ^ N + (2 / 3) ^ N * (2 ^ N : ℕ) / 2 ≤ 2 ^ N * ((2 * N + 5) * (3 / 4) ^ N) := by
  obtain ⟨hq, ha⟩ := geom_aux N
  have hcast : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; rfl
  rw [hcast]
  exact E2_arith_core L _ _ _ N (by positivity) (by positivity) hq ha hL

private theorem abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  simpa using mul_le_mul hx hy (abs_nonneg _) zero_le_one

private theorem exists_choice_E1 (n : ℕ) : ∃ cn : J n → Bool × Bool, ∀ g h : J (n + 2),
    |(1 / 2 ^ (n + 1)) * ∑ i : J (n + 1), tau n cn i g * tau n cn i h -
      (1 / 2 ^ n) * ∑ j : J n, sig n cn j g * sig n cn j h| ≤ (4 * n + 11) * (3 / 4) ^ n := by
  let P : J n → Bool × Bool → J (n + 2) × J (n + 2) → ℝ := fun j d t =>
    W (n + 2) ((j, d.1), d.2) t.1 * W (n + 2) ((j, d.1), d.2) t.2
  let Q : J n → Bool × Bool → Bool → J (n + 2) × J (n + 2) → ℝ := fun j d b t =>
    W (n + 2) ((j, Bool.xor d.1 (!b)), Bool.xor d.2 b) t.1 *
      W (n + 2) ((j, Bool.xor d.1 (!b)), Bool.xor d.2 b) t.2
  let Y : J (n + 2) × J (n + 2) → J n → Bool × Bool → ℝ := fun t j d =>
    (1 / 2 ^ (n + 1)) * ∑ b : Bool, Q j d b t - (1 / 2 ^ n) * P j d t
  have hP : ∀ j d t, |P j d t| ≤ 1 := fun j d t => abs_mul_le_one (abs_W_le _ _ _) (abs_W_le _ _ _)
  have hQ : ∀ j d b t, |Q j d b t| ≤ 1 := fun j d b t =>
    abs_mul_le_one (abs_W_le _ _ _) (abs_W_le _ _ _)
  have hYsum : ∀ t j, ∑ d : Bool × Bool, Y t j d = 0 := by
    intro t j
    simp only [Y, Q, P, Fintype.sum_prod_type, Fintype.sum_bool, Bool.not_true, Bool.not_false,
      Bool.xor_true, Bool.xor_false]
    rw [pow_succ]
    field_simp
    ring
  have hYbd : ∀ t j d, |Y t j d| ≤ 2 / 2 ^ n := by
    intro t j d
    have h1 : |∑ b : Bool, Q j d b t| ≤ 2 := by
      rw [Fintype.sum_bool]
      calc |Q j d true t + Q j d false t| ≤ |Q j d true t| + |Q j d false t| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (hQ _ _ _ _) (hQ _ _ _ _)
        _ = 2 := by norm_num
    calc |Y t j d| ≤ |(1 / 2 ^ (n + 1)) * ∑ b : Bool, Q j d b t| + |(1 / 2 ^ n) * P j d t| :=
          abs_sub _ _
      _ = (1 / 2 ^ (n + 1)) * |∑ b : Bool, Q j d b t| + (1 / 2 ^ n) * |P j d t| := by
          rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 ^ (n + 1) by positivity),
            abs_of_pos (show (0 : ℝ) < 1 / 2 ^ n by positivity)]
      _ ≤ (1 / 2 ^ (n + 1)) * 2 + (1 / 2 ^ n) * 1 := by
          gcongr
          exact hP _ _ _
      _ = 2 / 2 ^ n := by
          rw [pow_succ]
          field_simp
          ring
  let X : J (n + 2) × J (n + 2) → J n → Bool × Bool → ℝ := fun t j d => (2 ^ n / 2) * Y t j d
  have hXsum : ∀ t j, ∑ d : Bool × Bool, X t j d = 0 := fun t j => by
    simp only [X, ← Finset.mul_sum, hYsum, mul_zero]
  have hXbd : ∀ t j d, |X t j d| ≤ 1 := by
    intro t j d
    simp only [X]
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 2 ^ n / 2 * |Y t j d| ≤ 2 ^ n / 2 * (2 / 2 ^ n) := by gcongr; exact hYbd t j d
      _ = 1 := by field_simp
  have hl : (0 : ℝ) < (2 / 3) ^ n := by positivity
  obtain ⟨x, hx⟩ := exists_choice_abs_sum_le X hXsum hXbd hl
  refine ⟨x, fun g h => ?_⟩
  have hid : (1 / 2 ^ (n + 1)) * ∑ i : J (n + 1), tau n x i g * tau n x i h -
      (1 / 2 ^ n) * ∑ j : J n, sig n x j g * sig n x j h = ∑ j, Y (g, h) j (x j) := by
    rw [sum_J_succ]
    simp only [Y, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have hX : ∑ j, X (g, h) j (x j) = (2 ^ n / 2) * ∑ j, Y (g, h) j (x j) := by
    simp only [X, Finset.mul_sum]
  have hbound := hx (g, h)
  rw [hX] at hbound
  rw [hid]
  have hcardT : Fintype.card (J (n + 2) × J (n + 2)) = 2 ^ (n + 2) * 2 ^ (n + 2) := by
    rw [Fintype.card_prod, card_J]
  rw [hcardT, card_J] at hbound
  have hlog : Real.log (2 * ((2 ^ (n + 2) * 2 ^ (n + 2) : ℕ) : ℝ)) ≤ 2 * n + 5 := by
    have : (2 * ((2 ^ (n + 2) * 2 ^ (n + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (2 * n + 5) := by
      push_cast
      ring
    rw [this]
    have := log_two_pow_le (2 * n + 5)
    push_cast at this
    linarith
  have key : |∑ j, Y (g, h) j (x j)| ≤ 2 / 2 ^ n *
      (Real.log (2 * ((2 ^ (n + 2) * 2 ^ (n + 2) : ℕ) : ℝ)) / (2 / 3) ^ n +
        (2 / 3) ^ n * (2 ^ n : ℕ) / 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n / 2)] at hbound
    have h2 : |∑ j, Y (g, h) j (x j)| = 2 / 2 ^ n * (2 ^ n / 2 * |∑ j, Y (g, h) j (x j)|) := by
      field_simp
    rw [h2]
    gcongr
  exact key.trans (E1_arith n _ hlog)

private theorem exists_signs_E2 (k : ℕ) (ck : J k → Bool × Bool) (ck1 : J (k + 1) → Bool × Bool) :
    ∃ sk : J (k + 1) → Bool, ∀ (x : J (k + 1 + 2)) (y : J (k + 2)),
      |∑ j : J (k + 1), sg (sk j) * sig (k + 1) ck1 j x * tau k ck j y| ≤
        2 ^ (k + 1) * ((2 * ((k + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (k + 1)) := by
  let X : J (k + 1 + 2) × J (k + 2) → J (k + 1) → Bool → ℝ := fun t j b =>
    sg b * sig (k + 1) ck1 j t.1 * tau k ck j t.2
  have hXsum : ∀ t j, ∑ b : Bool, X t j b = 0 := by
    intro t j
    simp only [X, Fintype.sum_bool, sg]
    norm_num
  have hXbd : ∀ t j b, |X t j b| ≤ 1 := by
    intro t j b
    simp only [X]
    rw [mul_assoc, abs_mul, abs_sg, one_mul]
    exact abs_mul_le_one (abs_sig_le _ _ _ _) (abs_tau_le _ _ _ _)
  have hl : (0 : ℝ) < (2 / 3) ^ (k + 1) := by positivity
  obtain ⟨sk, hsk⟩ := exists_choice_abs_sum_le X hXsum hXbd hl
  refine ⟨sk, fun x y => ?_⟩
  have hbound := hsk (x, y)
  have hcardT : Fintype.card (J (k + 1 + 2) × J (k + 2)) = 2 ^ (k + 1 + 2) * 2 ^ (k + 2) := by
    rw [Fintype.card_prod, card_J, card_J]
  rw [hcardT, card_J] at hbound
  have hlog : Real.log (2 * ((2 ^ (k + 1 + 2) * 2 ^ (k + 2) : ℕ) : ℝ)) ≤
      2 * ((k + 1 : ℕ) : ℝ) + 4 := by
    have : (2 * ((2 ^ (k + 1 + 2) * 2 ^ (k + 2) : ℕ) : ℝ)) = (2 : ℝ) ^ (2 * k + 6) := by
      push_cast
      ring
    rw [this]
    have := log_two_pow_le (2 * k + 6)
    push_cast at this ⊢
    linarith
  exact hbound.trans (E2_arith (k + 1) _ hlog)

end Bounds

/-! ### The columns are small -/

section Davie

private theorem abs_Psi_le (c : (n : ℕ) → J n → Bool × Bool) (s : (n : ℕ) → J n → Bool)
    (hc : ∀ n (g h : J (n + 2)),
      |(1 / 2 ^ (n + 1)) * ∑ i : J (n + 1), tau n (c n) i g * tau n (c n) i h -
        (1 / 2 ^ n) * ∑ j : J n, sig n (c n) j g * sig n (c n) j h| ≤ (4 * n + 11) * (3 / 4) ^ n)
    (hs : ∀ k (x : J (k + 1 + 2)) (y : J (k + 2)),
      |∑ j : J (k + 1), sg (s (k + 1) j) * sig (k + 1) (c (k + 1)) j x * tau k (c k) j y| ≤
        2 ^ (k + 1) * ((2 * ((k + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (k + 1)))
    (n : ℕ) (g : J (n + 2)) (m : ℕ) (h : J (m + 2)) :
    |Psi c s n g m h| ≤ (4 * n + 11) * (3 / 4) ^ n := by
  have hq : (0 : ℝ) < (3 / 4) ^ n := by positivity
  by_cases h1 : m = n
  · subst h1
    rw [Psi_same]
    by_cases hm : m = 0
    · subst hm
      rw [ite_eq_left rfl, sub_zero]
      have hb : |∑ i : J (0 + 1), tau 0 (c 0) i g * tau 0 (c 0) i h| ≤ 2 := by
        calc |∑ i : J (0 + 1), tau 0 (c 0) i g * tau 0 (c 0) i h|
            ≤ ∑ i : J (0 + 1), |tau 0 (c 0) i g * tau 0 (c 0) i h| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : J (0 + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ =>
              abs_mul_le_one (abs_tau_le _ _ _ _) (abs_tau_le _ _ _ _)
          _ = 2 := by simp [card_J]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 ^ (0 + 1))]
      norm_num
      linarith
    · rw [ite_eq_right hm]
      exact hc m g h
  by_cases h2 : m = n + 1
  · subst h2
    rw [Psi_succ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ (n + 1))]
    have hb := hs n h g
    calc 1 / 2 ^ (n + 1) *
          |∑ i : J (n + 1), sg (s (n + 1) i) * sig (n + 1) (c (n + 1)) i h * tau n (c n) i g|
        ≤ 1 / 2 ^ (n + 1) * (2 ^ (n + 1) * ((2 * ((n + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (n + 1))) := by
          gcongr
      _ = (2 * ((n + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (n + 1) := by field_simp
      _ ≤ (4 * n + 11) * (3 / 4) ^ n := by
          push_cast
          rw [pow_succ]
          nlinarith
  by_cases h3 : m + 1 = n
  · subst h3
    rw [Psi_pred, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ (m + 1))]
    have hb := hs m g h
    calc 1 / 2 ^ (m + 1) *
          |∑ j : J (m + 1), sg (s (m + 1) j) * sig (m + 1) (c (m + 1)) j g * tau m (c m) j h|
        ≤ 1 / 2 ^ (m + 1) * (2 ^ (m + 1) * ((2 * ((m + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (m + 1))) := by
          gcongr
      _ = (2 * ((m + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (m + 1) := by field_simp
      _ ≤ (4 * ((m + 1 : ℕ) : ℝ) + 11) * (3 / 4) ^ (m + 1) := by
          have hx : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hq' : (0 : ℝ) < (3 / 4) ^ (m + 1) := by positivity
          nlinarith
  rw [Psi_far c s n g m h h1 h2 h3, abs_zero]
  positivity

private theorem exists_davie : ∃ Ψ : (n : ℕ) → J (n + 2) → (m : ℕ) → J (m + 2) → ℝ,
    (∀ n g m h, |Ψ n g m h| ≤ (4 * n + 11) * (3 / 4) ^ n) ∧
    (∀ n g m h, n + 2 ≤ m → Ψ n g m h = 0) ∧
    (∀ g, Ψ 0 g 0 g = 1) ∧ (∀ n g, Ψ (n + 1) g (n + 1) g = 0) ∧
    (∀ n0 g0 m h, ∑ n ∈ Finset.range (n0 + 2), ∑ g : J (n + 2),
      (1 / 2 ^ (n + 2)) * Ψ n0 g0 n g * Ψ n g m h = 0) := by
  choose c hc using exists_choice_E1
  let s : (n : ℕ) → J n → Bool := fun n => match n with
    | 0 => fun _ => true
    | k + 1 => Classical.choose (exists_signs_E2 k (c k) (c (k + 1)))
  have hs : ∀ k (x : J (k + 1 + 2)) (y : J (k + 2)),
      |∑ j : J (k + 1), sg (s (k + 1) j) * sig (k + 1) (c (k + 1)) j x * tau k (c k) j y| ≤
        2 ^ (k + 1) * ((2 * ((k + 1 : ℕ) : ℝ) + 5) * (3 / 4) ^ (k + 1)) := fun k =>
    Classical.choose_spec (exists_signs_E2 k (c k) (c (k + 1)))
  refine ⟨Psi c s, abs_Psi_le c s hc hs, ?_, Psi_zero_self c s, Psi_succ_self c s, ?_⟩
  · intro n g m h hm
    exact Psi_far c s n g m h (by omega) (by omega) (by omega)
  · intro n0 g0 m h
    exact Uop_Psi c s n0 g0 m h

end Davie

/-! ### From a summable trace to a function on the square -/

section Reduction

/-- A pointwise sum of continuous functions is continuous when at each point at most one of them
is nonzero and, for every `ε > 0`, only finitely many of them take a value of size at least `ε`. -/
private theorem continuous_tsum_of_disjoint {X ι : Type*} [TopologicalSpace X] (u : ι → X → ℝ)
    (hu : ∀ q, Continuous (u q)) (hdisj : ∀ x q q', u q x ≠ 0 → u q' x ≠ 0 → q = q')
    (hsmall : ∀ ε > 0, {q | ∃ x, ε ≤ |u q x|}.Finite) :
    Continuous fun x => ∑' q, u q x := by
  classical
  apply continuous_of_uniform_approx_of_continuous
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  set S := (hsmall (ε / 2) (half_pos hε)).toFinset with hS
  refine ⟨fun x => ∑ q ∈ S, u q x, continuous_multiset_sum _ fun q _ => hu q, fun x => hεV ?_⟩
  change dist (∑' q, u q x) (∑ q ∈ S, u q x) < ε
  by_cases hx : ∃ q, u q x ≠ 0
  · obtain ⟨q0, hq0⟩ := hx
    have hzero : ∀ q, q ≠ q0 → u q x = 0 := fun q hq => by
      by_contra h
      exact hq (hdisj x q q0 h hq0)
    rw [tsum_eq_single q0 hzero]
    by_cases hq0S : q0 ∈ S
    · rw [Finset.sum_eq_single_of_mem q0 hq0S fun q _ hq => hzero q hq, dist_self]
      exact hε
    · rw [Finset.sum_eq_zero fun q hq => hzero q (ne_of_mem_of_not_mem hq hq0S)]
      have hlt : |u q0 x| < ε / 2 := by
        by_contra h
        exact hq0S ((Set.Finite.mem_toFinset _).2 ⟨x, not_lt.mp h⟩)
      rw [Real.dist_eq, sub_zero]
      linarith
  · push Not at hx
    simp [hx, hε]

/-- The peak `2 ^ (-k)` of the `k`-th tent. -/
private noncomputable def tentPt (k : ℕ) : ℝ := (1 / 2) ^ k

/-- The half-width `2 ^ (-(k + 2))` of the `k`-th tent. -/
private noncomputable def tentRad (k : ℕ) : ℝ := (1 / 2) ^ (k + 2)

/-- The `k`-th tent function; different tents have disjoint supports (`tent_disjoint`). -/
private noncomputable def tent (k : ℕ) (x : ℝ) : ℝ := max 0 (1 - |x - tentPt k| / tentRad k)

private theorem tentRad_pos (k : ℕ) : 0 < tentRad k := by unfold tentRad; positivity

private theorem continuous_tent (k : ℕ) : Continuous (tent k) := by
  unfold tent
  fun_prop

private theorem tent_nonneg (k : ℕ) (x : ℝ) : 0 ≤ tent k x := le_max_left _ _

private theorem tent_le_one (k : ℕ) (x : ℝ) : tent k x ≤ 1 := by
  unfold tent
  apply max_le zero_le_one
  have : 0 ≤ |x - tentPt k| / tentRad k := div_nonneg (abs_nonneg _) (tentRad_pos k).le
  linarith

private theorem tent_self (k : ℕ) : tent k (tentPt k) = 1 := by
  simp [tent]

private theorem abs_sub_lt_of_tent_ne_zero {k : ℕ} {x : ℝ} (h : tent k x ≠ 0) :
    |x - tentPt k| < tentRad k := by
  by_contra hle
  push Not at hle
  apply h
  unfold tent
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ (tentRad_pos k), one_mul]
  exact hle

private theorem tent_disjoint {k k' : ℕ} {x : ℝ} (h : tent k x ≠ 0) (h' : tent k' x ≠ 0) :
    k = k' := by
  have hk := abs_sub_lt_of_tent_ne_zero h
  have hk' := abs_sub_lt_of_tent_ne_zero h'
  have key : ∀ a b : ℕ, a < b → |x - tentPt a| < tentRad a → |x - tentPt b| < tentRad b →
      False := by
    intro a b hab ha hb
    have h1 : tentPt b ≤ (1 / 2) ^ (a + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
    have h2 : tentRad b ≤ (1 / 2) ^ (a + 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have e1 : tentPt a = 2 * (1 / 2 : ℝ) ^ (a + 1) := by unfold tentPt; rw [pow_succ]; ring
    have e2 : tentRad a = (1 / 2 : ℝ) ^ (a + 1) / 2 := by unfold tentRad; rw [pow_succ]; ring
    have e3 : (1 / 2 : ℝ) ^ (a + 3) = (1 / 2 : ℝ) ^ (a + 1) / 4 := by
      rw [pow_add _ (a + 1) 2]; ring
    rw [abs_lt] at ha hb
    rw [e1] at ha
    rw [e2] at ha
    rw [e3] at h2
    have hpos : (0 : ℝ) < (1 / 2) ^ (a + 1) := by positivity
    linarith [ha.1, ha.2, hb.1, hb.2]
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact (key k k' hlt hk hk').elim
  · exact heq
  · exact (key k' k hgt hk' hk).elim

private theorem tentPt_mem (k : ℕ) : tentPt k ∈ Set.Icc (0 : ℝ) 1 := by
  unfold tentPt
  exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

end Reduction

section Reduction2

/-- Every point lies in the support of at most one tent. -/
private theorem exists_tent_decomp {I : Type*} [Nonempty I] [DecidableEq I] (enc : I → ℕ)
    (henc : Function.Injective enc) (x : ℝ) :
    ∃ (i0 : I) (κ : ℝ), 0 ≤ κ ∧ κ ≤ 1 ∧ ∀ i, tent (enc i) x = if i = i0 then κ else 0 := by
  by_cases hx : ∃ i, tent (enc i) x ≠ 0
  · obtain ⟨i0, hi0⟩ := hx
    refine ⟨i0, tent (enc i0) x, tent_nonneg _ _, tent_le_one _ _, fun i => ?_⟩
    split_ifs with h
    · rw [h]
    · by_contra hne
      exact h (henc (tent_disjoint hne hi0))
  · push Not at hx
    exact ⟨Classical.arbitrary I, 0, le_rfl, zero_le_one, fun i => by simp [hx i]⟩

/-- The passage to the square: a matrix `Z` that tends to `0` at infinity, together with summable
weights `w ≥ 0` such that `∑ m, w m * Z m m = 1` and `∑ m, w m * (Z i m * Z m m') = 0` for all
`i` and `m'`, yields a continuous function on the square that is not a uniform limit of sums of
products of its sections. -/
private theorem not_claim_of_matrix {I : Type*} [Countable I] [Nonempty I] (Z : I → I → ℝ)
    (w : I → ℝ)
    (hZ1 : ∀ i m, |Z i m| ≤ 1) (hZ0 : ∀ ε > 0, {p : I × I | ε ≤ |Z p.1 p.2|}.Finite)
    (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) (htr : ∑' m, w m * Z m m = 1)
    (hU : ∀ i0 m0, ∑' m, w m * (Z i0 m * Z m m0) = 0) :
    ¬ ScottishBookProblem153Claim := by
  classical
  intro hclaim
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat I
  -- the single-tent decomposition of each coordinate
  choose ι κ hκ0 hκ1 hκ using exists_tent_decomp enc henc
  let I01 := ↥(Set.Icc (0 : ℝ) 1)
  let u : I × I → I01 × I01 → ℝ := fun q x =>
    Z q.1 q.2 * tent (enc q.1) (x.1 : ℝ) * tent (enc q.2) (x.2 : ℝ)
  have hu : ∀ q, Continuous (u q) := fun q => by
    simp only [u]
    exact (continuous_const.mul ((continuous_tent _).comp
      (continuous_subtype_val.comp continuous_fst))).mul
      ((continuous_tent _).comp (continuous_subtype_val.comp continuous_snd))
  have hu_eq : ∀ q x, u q x = Z q.1 q.2 * (if q.1 = ι x.1 then κ x.1 else 0) *
      (if q.2 = ι x.2 then κ x.2 else 0) := fun q x => by
    simp only [u, hκ]
  have hdisj : ∀ x q q', u q x ≠ 0 → u q' x ≠ 0 → q = q' := by
    intro x q q' h h'
    rw [hu_eq] at h h'
    have a1 : q.1 = ι x.1 := by by_contra hc; simp [hc] at h
    have a2 : q.2 = ι x.2 := by by_contra hc; simp [hc] at h
    have b1 : q'.1 = ι x.1 := by by_contra hc; simp [hc] at h'
    have b2 : q'.2 = ι x.2 := by by_contra hc; simp [hc] at h'
    exact Prod.ext (a1.trans b1.symm) (a2.trans b2.symm)
  have hsmall : ∀ ε > 0, {q | ∃ x, ε ≤ |u q x|}.Finite := by
    intro ε hε
    refine (hZ0 ε hε).subset ?_
    rintro q ⟨x, hx⟩
    simp only [Set.mem_ofPred_eq]
    refine hx.trans ?_
    simp only [u, abs_mul]
    have t1 := tent_le_one (enc q.1) x.1
    have t2 := tent_le_one (enc q.2) x.2
    rw [abs_of_nonneg (tent_nonneg _ _), abs_of_nonneg (tent_nonneg _ _)]
    have := abs_nonneg (Z q.1 q.2)
    have := tent_nonneg (enc q.1) x.1
    have := tent_nonneg (enc q.2) x.2
    nlinarith [mul_le_mul t1 t2 (tent_nonneg _ _) zero_le_one]
  let f : C(I01 × I01, ℝ) := ⟨fun x => ∑' q, u q x, continuous_tsum_of_disjoint u hu hdisj hsmall⟩
  -- closed form of `f`
  have hf : ∀ x y : I01, f (x, y) = κ x * κ y * Z (ι x) (ι y) := by
    intro x y
    change ∑' q, u q (x, y) = _
    rw [tsum_eq_single (ι x, ι y)]
    · rw [hu_eq]; simp only [ite_true]; ring
    · intro q hq
      rw [hu_eq]
      by_cases h1 : q.1 = ι x
      · have h2 : q.2 ≠ ι y := fun h2 => hq (Prod.ext h1 h2)
        simp [h2]
      · simp [h1]
  have hfb : ∀ x y : I01, |f (x, y)| ≤ 1 := by
    intro x y
    rw [hf, abs_mul, abs_mul, abs_of_nonneg (hκ0 x), abs_of_nonneg (hκ0 y)]
    have := hZ1 (ι x) (ι y)
    have := hκ0 x; have := hκ0 y; have := hκ1 x; have := hκ1 y
    have := abs_nonneg (Z (ι x) (ι y))
    nlinarith [mul_le_mul (hκ1 x) (hκ1 y) (hκ0 y) zero_le_one]
  -- the evaluation points
  let P : I → I01 := fun m => ⟨tentPt (enc m), tentPt_mem _⟩
  have hιP : ∀ m, ι (P m) = m ∧ κ (P m) = 1 := by
    intro m
    have hm := hκ (P m) m
    have h1 : tent (enc m) (tentPt (enc m)) = 1 := tent_self _
    simp only [P] at hm
    rw [h1] at hm
    by_cases h : m = ι (P m)
    · rw [ite_eq_left h] at hm
      exact ⟨h.symm, hm.symm⟩
    · rw [ite_eq_right h] at hm
      exact absurd hm one_ne_zero
  have hfP : ∀ i m, f (P i, P m) = Z i m := by
    intro i m
    rw [hf, (hιP i).1, (hιP i).2, (hιP m).1, (hιP m).2]
    ring
  have hfa : ∀ (a : I01) (m : I), f (a, P m) = κ a * Z (ι a) m := by
    intro a m
    rw [hf, (hιP m).1, (hιP m).2]
    ring
  have hfb' : ∀ (b : I01) (m : I), f (P m, b) = κ b * Z m (ι b) := by
    intro b m
    rw [hf, (hιP m).1, (hιP m).2]
    ring
  -- apply the claim
  set S := ∑' m, w m with hS
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  have hε : (0 : ℝ) < 1 / (2 * (S + 1)) := by positivity
  obtain ⟨n, a, b, c, hF⟩ := hclaim f _ hε
  have hsum1 : Summable fun m => w m * f (P m, P m) :=
    Summable.of_norm_bounded hw fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m)]
      exact mul_le_of_le_one_right (hw0 m) (hfb _ _)
  have hsum2 : ∀ k : Fin n, Summable fun m => w m * (f (a k, P m) * f (P m, b k)) := fun k =>
    Summable.of_norm_bounded hw fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m), abs_mul]
      refine mul_le_of_le_one_right (hw0 m) ?_
      have := hfb (a k) (P m); have := hfb (P m) (b k)
      nlinarith [abs_nonneg (f (a k, P m)), abs_nonneg (f (P m, b k))]
  have hzero : ∀ k : Fin n, ∑' m, w m * (f (a k, P m) * f (P m, b k)) = 0 := by
    intro k
    simp_rw [hfa, hfb']
    have : ∀ m, w m * (κ (a k) * Z (ι (a k)) m * (κ (b k) * Z m (ι (b k)))) =
        (κ (a k) * κ (b k)) * (w m * (Z (ι (a k)) m * Z m (ι (b k)))) := fun m => by ring
    simp_rw [this]
    rw [tsum_mul_left, hU, mul_zero]
  let G : I → ℝ := fun m => w m * (f (P m, P m) - ∑ k, c k * f (a k, P m) * f (P m, b k))
  have hG1 : ∑' m, G m = 1 := by
    have e : ∀ m, G m = w m * f (P m, P m) - ∑ k, c k * (w m * (f (a k, P m) * f (P m, b k))) :=
      fun m => by
        simp only [G, mul_sub, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [e]
    rw [Summable.tsum_sub hsum1 (summable_sum fun k _ => (hsum2 k).mul_left (c k)),
      Summable.tsum_finsetSum fun k _ => (hsum2 k).mul_left (c k)]
    simp_rw [tsum_mul_left, hzero, mul_zero, Finset.sum_const_zero, sub_zero, hfP]
    exact htr
  have hGb : ∀ m, |G m| ≤ w m * (1 / (2 * (S + 1))) := by
    intro m
    simp only [G]
    rw [abs_mul, abs_of_nonneg (hw0 m)]
    have := hF (P m) (P m)
    rw [Real.dist_eq] at this
    exact mul_le_mul_of_nonneg_left this (hw0 m)
  have hGs : Summable fun m => |G m| :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hGb (hw.mul_right _)
  have hle : |∑' m, G m| ≤ S * (1 / (2 * (S + 1))) := by
    calc |∑' m, G m| ≤ ∑' m, |G m| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := G) (by simpa using hGs)
      _ ≤ ∑' m, w m * (1 / (2 * (S + 1))) := Summable.tsum_le_tsum hGb hGs (hw.mul_right _)
      _ = S * (1 / (2 * (S + 1))) := by rw [tsum_mul_right]
  rw [hG1, abs_one] at hle
  have : S * (1 / (2 * (S + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  linarith

end Reduction2

/-! ### Proof of the main theorem -/

private theorem summable_rho :
    Summable fun n : ℕ => ((n : ℝ) + 1) * ((4 * n + 11) * (3 / 4) ^ n) := by
  have hr : ‖(3 / 4 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left 4
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left 15
  have h0 := (summable_pow_mul_geometric_of_norm_lt_one 0 hr).mul_left 11
  convert (h2.add h1).add h0 using 1
  ext n
  ring

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

/--
**Negative answer to Mazur's Problem 153.** There are a continuous function
$f \colon [0,1]^2 \to \mathbb{R}$ and a real number $\varepsilon > 0$ such that for every natural
number $n$, all points $a_1, \dots, a_n, b_1, \dots, b_n \in [0,1]$ and all real numbers
$c_1, \dots, c_n$ there are $x, y \in [0,1]$ with

$$\Bigl| f(x, y) - \sum_{k=1}^n c_k \, f(a_k, y) \, f(x, b_k) \Bigr| > \varepsilon.$$

That is, the approximation scheme of Mazur's Problem 153 fails.

Source: S. Mazur, Problem 153 of the Scottish
Book; refuted via P. Enflo's counterexample to the approximation problem in
Banach spaces, Acta Math. 130 (1973), 309–317, DOI 10.1007/BF02392270; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015). This is the original bivariate-function form of the problem, distinct
from its consequence for the approximation property. The proof adapts
A. M. Davie's construction of a Banach space failing the approximation
property, The approximation problem for Banach spaces, Bull. London Math. Soc.
5 (1973), 261–266, DOI 10.1112/blms/5.3.261, as reproduced in Section 2 of
P. G. Casazza, C. L. García, W. B. Johnson, An example of an asymptotically
Hilbertian space which fails the approximation property, arXiv:math/0006134,
with real Walsh characters in place of complex group characters.
-/
theorem mazur153_refuted : ¬ ScottishBookProblem153Claim := by
  obtain ⟨Ψ, hbd, hsupp, htr0, htr1, hU⟩ := exists_davie
  let B : ℕ → ℝ := fun n => (4 * n + 11) * (3 / 4) ^ n
  let ρ : ℕ → ℝ := fun n => ((n : ℝ) + 1) * B n
  have hB : ∀ n, 0 < B n := fun n => by positivity
  have hρ : ∀ n, 0 < ρ n := fun n => by positivity
  let Z : (Σ n : ℕ, J (n + 2)) → (Σ n : ℕ, J (n + 2)) → ℝ := fun i m =>
    Ψ m.1 m.2 i.1 i.2 / ρ m.1
  let w : (Σ n : ℕ, J (n + 2)) → ℝ := fun m => ρ m.1 / 2 ^ (m.1 + 2)
  have hZle : ∀ i m, |Z i m| ≤ 1 / ((m.1 : ℝ) + 1) := by
    intro i m
    simp only [Z, abs_div, abs_of_pos (hρ _)]
    rw [div_le_div_iff₀ (hρ _) (by positivity)]
    have := hbd m.1 m.2 i.1 i.2
    simp only [ρ]
    nlinarith [hB m.1]
  have hfinI : ∀ K : ℕ, {i : Σ n : ℕ, J (n + 2) | i.1 ≤ K}.Finite := by
    intro K
    refine (((Finset.range (K + 1)).sigma fun _ => Finset.univ).finite_toSet).subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    simp only [Finset.coe_sigma, Finset.coe_range, Finset.coe_univ, Set.mem_sigma_iff,
      Set.mem_Iio, Set.mem_univ, and_true]
    omega
  apply not_claim_of_matrix Z w
  · intro i m
    refine (hZle i m).trans ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m.1 : (0 : ℝ) ≤ m.1)]
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ((hfinI (N + 1)).prod (hfinI N)).subset ?_
    rintro ⟨i, m⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    have hm : m.1 ≤ N := by
      have h1 := (hZle i m).trans' hp
      rw [le_div_iff₀ (by positivity)] at h1
      have h2 : ((m.1 : ℝ) + 1) ≤ 1 / ε := by
        rw [le_div_iff₀ hε]
        linarith
      have h3 : (m.1 : ℝ) < N := by linarith
      exact_mod_cast h3.le
    have hi : i.1 ≤ m.1 + 1 := by
      by_contra hc
      have hz : Z i m = 0 := by
        simp only [Z]
        rw [hsupp m.1 m.2 i.1 i.2 (by omega), zero_div]
      rw [hz, abs_zero] at hp
      linarith
    exact ⟨show i.1 ≤ N + 1 by omega, show m.1 ≤ N from hm⟩
  · intro m
    exact (div_pos (hρ _) (by positivity)).le
  · rw [summable_sigma_of_nonneg fun m => (div_pos (hρ _) (by positivity)).le]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e : ∀ n : ℕ, ∑' g : J (n + 2), w ⟨n, g⟩ = ρ n := by
      intro n
      rw [tsum_fintype]
      simp only [w, Finset.sum_const, Finset.card_univ, card_J, nsmul_eq_mul]
      push_cast
      field_simp
    exact summable_rho.congr fun n => (e n).symm
  · have hterm : ∀ m : Σ n : ℕ, J (n + 2), w m * Z m m = Ψ m.1 m.2 m.1 m.2 / 2 ^ (m.1 + 2) := by
      intro m
      simp only [w, Z]
      field_simp [(hρ m.1).ne']
    simp_rw [hterm]
    rw [tsum_eq_sum (s := ({0} : Finset ℕ).sigma fun _ => Finset.univ)]
    · rw [Finset.sum_sigma, Finset.sum_singleton]
      simp only [htr0, Finset.sum_const, Finset.card_univ, card_J, nsmul_eq_mul]
      norm_num
    · rintro ⟨n, g⟩ hng
      simp only [Finset.mem_sigma, Finset.mem_singleton, Finset.mem_univ, and_true] at hng
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hng
      simp only [htr1, zero_div]
  · intro i0 m0
    have hterm : ∀ m : Σ n : ℕ, J (n + 2), w m * (Z i0 m * Z m m0) =
        (1 / ρ m0.1) * ((1 / 2 ^ (m.1 + 2)) * Ψ m0.1 m0.2 m.1 m.2 * Ψ m.1 m.2 i0.1 i0.2) := by
      intro m
      simp only [w, Z]
      field_simp [(hρ m.1).ne', (hρ m0.1).ne']
    simp_rw [hterm]
    rw [tsum_mul_left]
    rw [tsum_eq_sum (s := (Finset.range (m0.1 + 2)).sigma fun _ => Finset.univ)]
    · rw [Finset.sum_sigma, hU m0.1 m0.2 i0.1 i0.2, mul_zero]
    · rintro ⟨n, g⟩ hng
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true, not_lt] at hng
      rw [hsupp m0.1 m0.2 n g hng]
      ring

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted

end
