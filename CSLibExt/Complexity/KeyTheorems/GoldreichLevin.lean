/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Goldreich-Levin: hardcore predicate from one-way permutations

For a one-way permutation `π`, the inner product `⟨x, r⟩ = Σᵢ xᵢ · rᵢ (mod 2)` is a
*hardcore predicate* for the function `(x, r) ↦ (π x, r)`: no polynomial-size circuit can
predict `⟨x, r⟩` from `(π x, r)` with non-negligible advantage over `1 / 2`. Equivalently,
every one-way permutation has a hardcore bit, and one-way functions have hardcore
predicates. Circuits are non-uniform gate lists, as in the CVP file; the one-wayness
hypothesis is that every polynomial-size inverter family succeeds with negligible
probability (the canonical `Negligible` of the `Classes` file), and `π` itself is
computable by polynomial-size circuits.

The proof of `goldreich_levin` averages shifted predictor queries to recover each bit by
majority. Fixing the shifts and their guessed parities by averaging gives one non-uniform
inverter circuit at each length. This permits a polynomial loss in inversion success and
avoids having to test a list of guesses with the forward circuit. The proof uses neither the
bijectivity of `π` nor its computability by polynomial-size circuits; both hypotheses are kept
as part of the statement.

Source:
O. Goldreich and L. A. Levin, "A hard-core predicate for all one-way functions",
Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989),
25-32.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevin

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-- **Serialized circuit gates.** A serialized gate is a pair $(k, r)$ of a natural number $k$, the
kind of the gate, and a list $r$ of natural numbers, its references.

These pairs are read through the shared (kind, references) encoding of gates of flat Boolean
circuits. -/
abbrev GLGate := ℕ × List ℕ

/-- **Gate values of a serialized circuit.** For a list $C = (g_0, \dots, g_{m-1})$ of serialized
gates and a list $a = (a_0, \dots, a_{n-1})$ of Booleans, the gate values of $C$ on $a$ are the
list of gate values of the flat Boolean circuit on $n$ inputs whose $j$-th gate is decoded from the
(kind, references) pair $g_j$, evaluated on the assignment that gives input $i$ the value $a_i$.

A pair $(0, [i])$ with $i \ge n$ decodes to the constant false, so an input index out of range
reads as false. -/
def glCircuitEval (C : List GLGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Outputs of a serialized circuit.** For a list $C$ of serialized gates, a list $a$ of Booleans
and a natural number $k$, the outputs of $C$ on $a$ are the last $k$ entries of the gate values of
$C$ on $a$, or all of them when $C$ has fewer than $k$ gates. -/
def glCircuitOutputs (C : List GLGate) (assign : List Bool) (k : ℕ) : List Bool :=
  let vals := glCircuitEval C assign
  vals.drop (vals.length - k)

/-- **Inversion success probability of a circuit.** For a list $C$ of serialized gates and a map
$\pi$ from $n$-bit strings to $n$-bit strings, the inversion success probability of $C$ against
$\pi$ is the rational number $N / 2^n$, where $N$ is the number of $n$-bit strings $x$ such that
the outputs of $C$ on input $\pi(x)$, taken as its last $n$ gate values, are exactly $x$. -/
noncomputable def invertSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {x | glCircuitOutputs C (List.ofFn (π x)) n = List.ofFn x} : ℚ) /
    (2 : ℚ) ^ n

/-- **Inner product modulo 2.** For $n$-bit strings $x$ and $r$, their inner product modulo 2 is
true if and only if the number of indices $i < n$ with $x_i$ and $r_i$ both true is odd, that is,
$\langle x, r \rangle = \sum_{i < n} x_i r_i \bmod 2$. -/
def xorDot {n : ℕ} (x r : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => x i && r i)).card % 2 = 1)

/-- **Concatenation of two bitstrings.** For $n$-bit strings $y$ and $r$, their concatenation is the
$2n$-bit string whose bit $i$ is $y_i$ for $i < n$ and $r_{i - n}$ for $n \le i < 2n$. -/
def glPair {n : ℕ} (y r : Fin n → Bool) : Fin (2 * n) → Bool :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩
    else r ⟨i.val - n, by
      have hi := i.isLt
      omega⟩

/-- **Prediction success probability for the inner-product bit.** For a list $C$ of serialized
gates and a map $\pi$ from $n$-bit strings to $n$-bit strings, the prediction success probability
of $C$ against $\pi$ is the rational number $N / 2^{2n}$, where $N$ is the number of pairs
$(x, r)$ of $n$-bit strings such that $C$ has at least one gate and the value of its last gate on
the concatenation of $\pi(x)$ and $r$, a $2n$-bit input, equals the inner product of $x$ and $r$
modulo 2. -/
noncomputable def predictSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin n → Bool) |
    (glCircuitEval C (List.ofFn (glPair (π p.1) p.2))).getLast? =
      some (xorDot p.1 p.2)} : ℚ) / (2 : ℚ) ^ (2 * n)

open Finset
open scoped BigOperators

/-! ### Averaging the predictor over XOR shifts -/

private abbrev Word (n : ℕ) := Fin n → Bool

private def shift {n} (a b : Word n) : Word n := fun i => a i ^^ b i

private theorem shift_invol {n} (a : Word n) : Function.Involutive (shift a) := by
  intro b
  funext i
  simp [shift]

private theorem expect_shift {n} (f : Word n → ℚ) (a : Word n) :
    (𝔼 r, f (shift a r)) = 𝔼 r, f r :=
  Fintype.expect_bijective _ (shift_invol a).bijective _ _ (fun _ => rfl)

private def step {n} (a : Word n) (f : Word n → ℚ) (r : Word n) : ℚ :=
  (f r + f (shift a r)) / 2

private def smooth {n} (ds : List (Word n)) (f : Word n → ℚ) : Word n → ℚ :=
  ds.foldr step f

private theorem mean_step {n} (a : Word n) (f : Word n → ℚ) :
    (𝔼 r, step a f r) = 𝔼 r, f r := by
  simp only [step, ← expect_div, expect_add_distrib, expect_shift]
  ring

private theorem mean_smooth {n} (ds : List (Word n)) (f : Word n → ℚ) :
    (𝔼 r, smooth ds f r) = 𝔼 r, f r := by
  induction ds with
  | nil => rfl
  | cons a ds ih => exact (mean_step a _).trans ih

-- A random translation pairs two independently uniform masks. For a centered function the
-- cross term vanishes, so averaging the two values halves the mean square.
private theorem step_variance {n} (f : Word n → ℚ) (h : (𝔼 r, f r) = 0) :
    (𝔼 a, 𝔼 r, (step a f r) ^ 2) = (𝔼 r, (f r) ^ 2) / 2 := by
  rw [expect_comm]
  have he (r : Word n) (g : Word n → ℚ) :
      (𝔼 a, g (shift a r)) = 𝔼 a, g a := by
    calc
      _ = 𝔼 a, g (shift r a) := expect_congr rfl fun a _ =>
        congrArg g (funext fun _ => Bool.xor_comm _ _)
      _ = _ := expect_shift g r
  have hsq (r a : Word n) : (step a f r) ^ 2 =
      ((f r) ^ 2 + 2 * f r * f (shift a r) + (f (shift a r)) ^ 2) / 4 := by
    unfold step
    ring
  simp only [hsq, ← expect_div, expect_add_distrib, ← mul_expect, he _ f,
    show ∀ r, (𝔼 a, (f (shift a r)) ^ 2) = 𝔼 a, (f a) ^ 2 from
      fun r => he r (fun a => (f a) ^ 2), h, mul_zero, add_zero, Fintype.expect_const]
  ring

private theorem choose_directions {n} (h : Word n → Word n → ℚ)
    (hzero : ∀ x, (𝔼 r, h x r) = 0) (k : ℕ) :
    ∃ ds : List (Word n), ds.length = k ∧
      (𝔼 x, 𝔼 r, (smooth ds (h x) r) ^ 2) ≤ (𝔼 x, 𝔼 r, (h x r) ^ 2) / 2 ^ k := by
  induction k with
  | zero => exact ⟨[], rfl, by simp [smooth]⟩
  | succ k ih =>
    obtain ⟨ds, hlen, hv⟩ := ih
    have hhalf : (𝔼 a, 𝔼 x, 𝔼 r, (step a (smooth ds (h x)) r) ^ 2) =
        (𝔼 x, 𝔼 r, (smooth ds (h x) r) ^ 2) / 2 := by
      rw [expect_comm]
      simp_rw [step_variance _ ((mean_smooth ds (h _)).trans (hzero _)), ← expect_div]
    obtain ⟨a, -, ha⟩ := exists_le_of_expect_le univ_nonempty hhalf.le
    refine ⟨a :: ds, by simp [hlen], ha.trans ?_⟩
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right hv (by norm_num)

/-! ### Recovering bits from the shifted queries -/

private def bit (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bit_dot {n} (x r : Word n) :
    bit (xorDot x r) = ∑ i, bit (x i) * bit (r i) := by
  let s := univ.filter fun i => x i && r i
  have hc : (s.card : ZMod 2) = ∑ i, bit (x i) * bit (r i) := by
    rw [show s = _ from rfl, natCast_card_filter]
    apply sum_congr rfl
    intro i _
    cases x i <;> cases r i <;> rfl
  rw [← hc]
  change (if decide (s.card % 2 = 1) then 1 else 0) = _
  split_ifs with h
  · exact (ZMod.natCast_eq_one_iff_odd.mpr (Nat.odd_iff.mpr (of_decide_eq_true h))).symm
  · apply Eq.symm
    apply (ZMod.natCast_eq_zero_iff ..).mpr
    apply Nat.dvd_of_mod_eq_zero
    have := Nat.mod_lt s.card (by decide : 0 < 2)
    simp only [decide_eq_true_eq] at h
    omega

private theorem dot_shift {n} (x r s : Word n) :
    xorDot x (shift r s) = (xorDot x r ^^ xorDot x s) := by
  have hinj : Function.Injective bit := by decide
  have hadd : ∀ a b, bit (a ^^ b) = bit a + bit b := by decide
  apply hinj
  simp only [hadd, bit_dot, shift, mul_add, sum_add_distrib]

private def basis {n} (i : Fin n) : Word n := fun j => decide (j = i)

private theorem dot_basis {n} (x : Word n) (i : Fin n) : xorDot x (basis i) = x i := by
  apply (show Function.Injective bit by decide)
  rw [bit_dot]
  simp [bit, basis, mul_ite]

-- Each direction doubles the queries. Its guessed parity tells us whether adding that
-- direction changes the predicted inner product.
private def probes {n} : List (Word n × Bool) → Word n → Bool → List (Word n × Bool)
  | [], r, b => [(r, b)]
  | (d, t) :: ds, r, b => probes ds r b ++ probes ds (shift d r) (t ^^ b)

private theorem length_probes {n} (ds : List (Word n × Bool)) (r : Word n) (b : Bool) :
    (probes ds r b).length = 2 ^ ds.length := by
  induction ds generalizing r b with
  | nil => rfl
  | cons hd ds ih => simp [probes, ih, pow_succ, Nat.mul_two]

private def labelled {n} (ds : List (Word n)) (x : Word n) :=
  ds.map fun d => (d, xorDot x d)

private def indicator (b : Bool) : ℚ := if b then 1 else 0

private theorem probe_count {n} (ds : List (Word n)) (x : Word n) (p : Word n → Bool)
    (r : Word n) (b : Bool) :
    (((probes (labelled ds x) r b).countP (fun q =>
      (p q.1 ^^ q.2) == (xorDot x r ^^ b)) : ℕ) : ℚ) / 2 ^ ds.length =
    smooth ds (fun s => indicator (p s == xorDot x s)) r := by
  induction ds generalizing r b with
  | nil =>
    simp [probes, labelled, smooth, List.countP_singleton, indicator]
  | cons d ds ih =>
    have e : (xorDot x (shift d r) ^^ (xorDot x d ^^ b)) = (xorDot x r ^^ b) := by
      rw [dot_shift]
      cases xorDot x d <;> cases xorDot x r <;> cases b <;> rfl
    have ih' := ih (shift d r) (xorDot x d ^^ b)
    rw [e] at ih'
    change (((probes (labelled ds x) r b ++
      probes (labelled ds x) (shift d r) (xorDot x d ^^ b)).countP _ : ℕ) : ℚ) / _ =
      (smooth ds _ r + smooth ds _ (shift d r)) / 2
    rw [List.countP_append, Nat.cast_add, ← ih r b, ← ih', List.length_cons, pow_succ]
    ring

private theorem smooth_sub_const {n} (ds : List (Word n)) (f : Word n → ℚ) (c : ℚ) (r : Word n) :
    smooth ds (fun s => f s - c) r = smooth ds f r - c := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih =>
    change (smooth ds _ r + smooth ds _ (shift d r)) / 2 =
      (smooth ds f r + smooth ds f (shift d r)) / 2 - c
    rw [ih, ih]
    ring

private def recover {n} (ds : List (Word n × Bool)) (a : Word n) (b : Bool)
    (p : Word n → Bool) (i : Fin n) : Bool :=
  let l := probes ds (shift (basis i) a) b
  decide (l.length < 2 * l.countP fun q => p q.1 ^^ q.2)

private theorem count_majority {α} (l : List α) (f : α → Bool) (b : Bool)
    (h : decide (l.length < 2 * l.countP f) ≠ b) :
    2 * l.countP (fun q => f q == b) ≤ l.length := by
  cases b
  · have e : l.countP (fun q => f q == false) + l.countP f = l.length := by
      clear h
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.countP_cons, List.length_cons]
        cases f a <;> simp_all <;> omega
    simp only [ne_eq, Bool.not_eq_false, decide_eq_true_eq] at h
    omega
  · simpa using (show 2 * l.countP f ≤ l.length by simpa using h)

private theorem miss_le_half {n} (ds : List (Word n)) (x a : Word n) (p : Word n → Bool)
    (i : Fin n) (h : recover (labelled ds x) a (xorDot x a) p i ≠ x i) :
    smooth ds (fun r => indicator (p r == xorDot x r)) (shift (basis i) a) ≤ 1 / 2 := by
  have hg := count_majority _ _ _ h
  have ht := probe_count ds x p (shift (basis i) a) (xorDot x a)
  rw [dot_shift, dot_basis] at ht
  simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] at ht
  rw [← ht, div_le_iff₀ (by positivity)]
  rw [length_probes] at hg
  simp only [labelled, List.length_map] at hg
  have hc := (Nat.cast_le (α := ℚ)).mpr hg
  push_cast at hc
  unfold labelled
  linarith

private theorem choose_offset {n} (f : Word n → Word n → ℚ) :
    ∃ a : Word n, (𝔼 x, ∑ i : Fin n, (f x (shift (basis i) a)) ^ 2) ≤
      n * 𝔼 x, 𝔼 r, (f x r) ^ 2 := by
  suffices e : (𝔼 a, 𝔼 x, ∑ i : Fin n, (f x (shift (basis i) a)) ^ 2) =
      n * 𝔼 x, 𝔼 r, (f x r) ^ 2 by
    obtain ⟨a, -, ha⟩ := exists_le_of_expect_le univ_nonempty e.le
    exact ⟨a, ha⟩
  rw [expect_comm]
  simp_rw [expect_sum_comm, show ∀ (x : Word n) (i : Fin n),
    (𝔼 a, (f x (shift (basis i) a)) ^ 2) = 𝔼 a, (f x a) ^ 2 from
    fun x i => expect_shift (fun r => (f x r) ^ 2) _]
  simp

private def withAdvice {n} (ds : List (Word n)) (v : Word ds.length) :=
  List.ofFn fun i => (ds[i.val], v i)

private theorem advice_correct {n} (ds : List (Word n)) (x : Word n) :
    withAdvice ds (fun i => xorDot x ds[i.val]) = labelled ds x := by
  apply List.ext_getElem <;> simp [withAdvice, labelled]

-- The correct labels depend on the hidden word. Among the two possible offset labels and
-- the 2^k direction labelings, one fixed choice retains at least a 1/(2·2^k) share of wins.
private theorem choose_advice {n} (ds : List (Word n)) (a : Word n)
    (p : Word n → Word n → Bool) :
    ∃ (v : Word ds.length) (b : Bool),
      (𝔼 x, indicator (decide (recover (labelled ds x) a (xorDot x a) (p x) = x))) ≤
      (2 * 2 ^ ds.length) *
        𝔼 x, indicator (decide (recover (withAdvice ds v) a b (p x) = x)) := by
  let win (x : Word n) (t : Word ds.length × Bool) :=
    indicator (decide (recover (withAdvice ds t.1) a t.2 (p x) = x))
  have h (x : Word n) :
      indicator (decide (recover (labelled ds x) a (xorDot x a) (p x) = x)) ≤ ∑ t, win x t := by
    let t : Word ds.length × Bool := (fun i => xorDot x ds[i.val], xorDot x a)
    have e : win x t = _ := congrArg (fun ds =>
      indicator (decide (recover ds a (xorDot x a) (p x) = x))) (advice_correct ds x)
    rw [← e]
    exact single_le_sum (f := win x) (fun j _ => by
      dsimp [win, indicator]; split <;> norm_num) (mem_univ t)
  obtain ⟨t, -, ht⟩ := exists_le_of_le_expect (f := fun t => 𝔼 x, win x t) univ_nonempty le_rfl
  refine ⟨t.1, t.2, (expect_le_expect (fun x _ => h x)).trans ?_⟩
  rw [expect_sum_comm, ← Fintype.card_mul_expect]
  simpa [Fintype.card_fun, mul_comm (2 ^ ds.length : ℚ) 2] using
    mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (Fintype.card (Word ds.length × Bool)) (α := ℚ))

private theorem sampling_bound {n} (p : Word n → Word n → Bool) (k : ℕ) (δ : ℚ) (hδ : 0 < δ) :
    ∃ (dirs : List (Word n × Bool)) (a : Word n) (b : Bool), dirs.length = k ∧
      (𝔼 x, 𝔼 r, indicator (p x r == xorDot x r)) - 1 / 2 ≤ δ + n / (2 ^ k * δ ^ 2) +
      (2 * 2 ^ k) * 𝔼 x, indicator (decide (recover dirs a b (p x) = x)) := by
  let f (x r : Word n) := indicator (p x r == xorDot x r)
  let μ (x : Word n) := 𝔼 r, f x r
  let h (x r : Word n) := f x r - μ x
  have hf (x r : Word n) : 0 ≤ f x r ∧ f x r ≤ 1 := by
    dsimp [f, indicator]; split <;> norm_num
  have hm (x : Word n) : 0 ≤ μ x ∧ μ x ≤ 1 :=
    ⟨le_expect univ_nonempty (fun r _ => (hf x r).1),
      expect_le univ_nonempty (fun r _ => (hf x r).2)⟩
  have hzero (x : Word n) : (𝔼 r, h x r) = 0 := by
    simp [h, expect_sub_distrib, μ]
  have hv : (𝔼 x, 𝔼 r, (h x r) ^ 2) ≤ 1 := by
    refine expect_le univ_nonempty fun x _ => expect_le univ_nonempty fun r _ => ?_
    dsimp [h]
    obtain ⟨h₁, h₂⟩ := hf x r
    obtain ⟨h₃, h₄⟩ := hm x
    nlinarith [mul_nonneg (show 0 ≤ 1 - (f x r - μ x) by linarith)
      (show 0 ≤ 1 + (f x r - μ x) by linarith)]
  obtain ⟨ds, hk, hd⟩ := choose_directions h hzero k
  obtain ⟨a, ha⟩ := choose_offset (fun x => smooth ds (h x))
  let err (x : Word n) := ∑ i : Fin n, (smooth ds (h x) (shift (basis i) a)) ^ 2
  let good (x : Word n) := indicator (decide (recover (labelled ds x) a (xorDot x a) (p x) = x))
  have he : (𝔼 x, err x) ≤ n / 2 ^ k := by
    refine ha.trans ?_
    rw [div_eq_mul_inv (n : ℚ), ← one_div]
    exact mul_le_mul_of_nonneg_left
      (hd.trans (div_le_div_of_nonneg_right hv (by positivity))) (by positivity)
  -- On a word with advantage above δ, a wrong recovered bit contributes at least δ²
  -- to the sum of squared errors over the coordinate queries.
  have hx (x : Word n) : μ x ≤ (1 / 2 + δ) + err x / δ ^ 2 + good x := by
    have hpos : 0 ≤ err x := sum_nonneg (fun i _ => sq_nonneg _)
    have hquot := div_nonneg hpos (sq_nonneg δ)
    by_cases hw : recover (labelled ds x) a (xorDot x a) (p x) = x
    · have : good x = 1 := by simp [good, hw, indicator]
      linarith [(hm x).2]
    have hg : good x = 0 := by simp [good, hw, indicator]
    by_cases hh : μ x ≤ 1 / 2 + δ
    · linarith
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hs := miss_le_half ds x a (p x) i hi
    have hi' : (smooth ds (h x) (shift (basis i) a)) ^ 2 ≤ err x :=
      single_le_sum (f := fun j => (smooth ds (h x) (shift (basis j) a)) ^ 2)
        (fun j _ => sq_nonneg _) (mem_univ i)
    rw [show h x = fun r => f x r - μ x from rfl, smooth_sub_const] at hi'
    change smooth ds (f x) _ ≤ _ at hs
    have hdif : δ ≤ μ x - smooth ds (f x) (shift (basis i) a) := by linarith
    have hsq := pow_le_pow_left₀ hδ.le hdif 2
    have hbig : 1 ≤ err x / δ ^ 2 := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith [(hm x).2]
  obtain ⟨v, b, had⟩ := choose_advice ds a p
  refine ⟨withAdvice ds v, a, b, by simp [withAdvice, hk], ?_⟩
  have hall := expect_le_expect (s := univ) (fun x _ => hx x)
  simp only [expect_add_distrib, Fintype.expect_const, ← expect_div] at hall
  have := div_le_div_of_nonneg_right he (sq_nonneg δ)
  rw [div_div] at this
  rw [hk] at had
  change (𝔼 x, μ x) - 1 / 2 ≤ _
  change (𝔼 x, good x) ≤ _ at had
  linarith

/-! ### Compiling the decoder to serialized gates -/

private def eval {n} (C : List GLGate) (x : Word n) :=
  circuitEval (C.map (acGateOfPair (n := n))) x

private theorem eval_eq {n} (C : List GLGate) (x : Word n) :
    glCircuitEval C (List.ofFn x) = eval C x := by
  have aux {m : ℕ} (l : List Bool) (hl : l.length = m) (y : Word m)
      (hy : ∀ i : Fin l.length, l.getD i.val false = y (i.cast hl)) :
      glCircuitEval C l = eval C y := by
    subst m
    exact congrArg (circuitEval _) (funext hy)
  apply aux _ List.length_ofFn
  intro i
  rw [List.getD_eq_getElem _ _ i.isLt, List.getElem_ofFn]
  exact congrArg x (Fin.ext rfl)

private theorem eval_len {n} (C : List GLGate) (x : Word n) : (eval C x).length = C.length := by
  simp [eval]

private theorem eval_snoc {n} (C : List GLGate) (g : GLGate) (x : Word n) :
    eval (C ++ [g]) x = eval C x ++ [serialGateEval (eval C x) x g] := by
  simp [eval, circuitEval_append_singleton, gateValue_ofPair]

-- Offset all predecessor references when appending a predictor copy. Even a forward
-- reference still reads false, because its relocated index is beyond the current values.
private def embedGate {n} (s : Word n) (m : ℕ) : ACGate (2 * n) → GLGate
  | .var i => if h : i.val < n then (0, [i.val]) else
      (1, [if s ⟨i.val - n, by have := i.isLt; omega⟩ then 1 else 0])
  | .const b => (1, [if b then 1 else 0])
  | .notGate j => (2, [m + j])
  | .andGate js => (3, js.map (m + ·))
  | .orGate js => (4, js.map (m + ·))
  | .modGate _ _ => (1, [0])

private theorem decoded_noMod {n} (g : GLGate) (m : ℕ) (js : List ℕ) :
    acGateOfPair (n := n) g ≠ .modGate m js := by
  unfold acGateOfPair
  split <;> (try split) <;> simp

private theorem embed_gate_eval {n} (s y : Word n) (before vs : List Bool) (g : GLGate) :
    serialGateEval (before ++ vs) y (embedGate s before.length (acGateOfPair g)) =
      serialGateEval vs (glPair y s) g := by
  rw [gateValue_ofPair vs]
  generalize e : acGateOfPair (n := 2 * n) g = A
  have get (j : ℕ) : (before ++ vs).getD (before.length + j) false = vs.getD j false := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  cases A with
  | var i =>
    by_cases h : i.val < n
    · simp [embedGate, h, serialGateEval, gateValue, glPair]
    · cases hs : s ⟨i.val - n, by have := i.isLt; omega⟩ <;>
        simp [embedGate, h, serialGateEval, gateValue, glPair, hs]
  | const b => cases b <;> rfl
  | notGate j => simp only [embedGate, serialGateEval, gateValue, get]
  | andGate js =>
    simp only [embedGate, serialGateEval, gateValue, List.all_map, Function.comp_def, get]
  | orGate js =>
    simp only [embedGate, serialGateEval, gateValue, List.any_map, Function.comp_def, get]
  | modGate m js => exact (decoded_noMod g m js e).elim

private def embed {n} (s : Word n) (m : ℕ) (C : List GLGate) :=
  C.map fun g => embedGate s m (acGateOfPair g)

private theorem eval_embed {n} (s y : Word n) (D C : List GLGate) :
    eval (D ++ embed s D.length C) y = eval D y ++ eval C (glPair y s) := by
  induction C using List.reverseRecOn with
  | nil => simp [embed, eval, circuitEval]
  | append_singleton C g ih =>
    rw [show embed s D.length (C ++ [g]) = embed s D.length C ++
      [embedGate s D.length (acGateOfPair g)] by simp [embed], ← List.append_assoc, eval_snoc,
      eval_snoc C, ih, List.append_assoc]
    rw [← eval_len D y, embed_gate_eval]

private def HasWire {n} (C : List GLGate) (f : Word n → Bool) :=
  ∃ i < C.length, ∀ x, (eval C x).getD i false = f x

private theorem eval_prefix {n} {C D : List GLGate} (h : C <+: D) (x : Word n) :
    eval C x <+: eval D x := by
  obtain ⟨l, rfl⟩ := h
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [← List.append_assoc, eval_snoc]
    exact ih.trans (List.prefix_append ..)

private theorem has_mono {n} {C D : List GLGate} (h : C <+: D) {f : Word n → Bool}
    (hf : HasWire C f) : HasWire D f := by
  obtain ⟨i, hi, hf⟩ := hf
  refine ⟨i, hi.trans_le h.length_le, fun x => ?_⟩
  obtain ⟨vs, hvs⟩ := eval_prefix h x
  rw [← hvs, List.getD_append _ _ _ _ (by rwa [eval_len]), hf]

private def BuildsWires {n} (C : List GLGate) (cost : ℕ) (fs : List (Word n → Bool)) :=
  ∃ D : List GLGate, C <+: D ∧ D.length ≤ C.length + cost ∧ ∀ f ∈ fs, HasWire D f

private theorem builds_seq {n} (C : List GLGate) (fs : List (Word n → Bool)) (m : ℕ)
    (h : ∀ D, C <+: D → ∀ f ∈ fs, BuildsWires D m [f]) :
    BuildsWires C (fs.length * m) fs := by
  induction fs generalizing C with
  | nil => exact ⟨C, by simp, by simp, by simp⟩
  | cons f fs ih =>
    obtain ⟨D, hD, hcost, hf⟩ := h C (by simp) f (by simp)
    obtain ⟨D', hD', hc', hf'⟩ := ih D fun E hE g hg =>
      h E (hD.trans hE) g (by simp [hg])
    refine ⟨D', hD.trans hD', ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      omega
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact has_mono hD' (hf _ (by simp))
      · exact hf' _ hg

private theorem builds_gate {n} (C : List GLGate) (g : GLGate) (f : Word n → Bool)
    (h : ∀ x, serialGateEval (eval C x) x g = f x) : BuildsWires C 1 [f] := by
  refine ⟨C ++ [g], List.prefix_append .., by simp, ?_⟩
  intro f' hf'
  obtain rfl := List.mem_singleton.mp hf'
  refine ⟨C.length, by simp, fun x => ?_⟩
  rw [eval_snoc, List.getD_append_right _ _ _ _ (by simp [eval_len]), eval_len]
  simpa using h x

private def answer {n} (C : List GLGate) (y s : Word n) : Bool :=
  (eval C (glPair y s)).getLast?.getD false

private theorem builds_vote {n} (D C : List GLGate) (s : Word n) (b : Bool) :
    BuildsWires D (C.length + 1) [fun y => answer C y s ^^ b] := by
  let E := D ++ embed s D.length C
  let j := D.length + (C.length - 1)
  have hj (y : Word n) : (eval E y).getD j false = answer C y s := by
    dsimp only [E, j, answer]
    rw [eval_embed, List.getD_append_right _ _ _ _ (by simp [eval_len]), eval_len,
      Nat.add_sub_cancel_left, ← eval_len C (glPair y s)]
    simp [List.getLast?_eq_getElem?]
  let g : GLGate := if b then (2, [j]) else (4, [j])
  have hv (y : Word n) : serialGateEval (eval E y) y g = (answer C y s ^^ b) := by
    cases b <;> simp only [g, Bool.false_eq_true, ↓reduceIte, serialGateEval,
      List.any_cons, List.any_nil, Bool.or_false, hj, Bool.xor_true, Bool.xor_false]
  obtain ⟨D', hp, hl, hfs⟩ := builds_gate E g _ hv
  refine ⟨D', (List.prefix_append ..).trans hp, ?_, hfs⟩
  simpa [E, embed, Nat.add_assoc] using hl

private theorem builds_const {n} (C : List GLGate) (b : Bool) :
    BuildsWires C 1 [fun _ : Word n => b] := by
  apply builds_gate C (1, [if b then 1 else 0])
  intro x
  cases b <;> rfl

private theorem builds_threshold_step {n} (C : List GLGate) (f g v : Word n → Bool)
    (hf : HasWire C f) (hg : HasWire C g) (hv : HasWire C v) :
    BuildsWires C 2 [fun x => f x || (g x && v x)] := by
  obtain ⟨i, hi, hgi⟩ := hg
  obtain ⟨j, hj, hvj⟩ := hv
  have h₁ (x : Word n) : serialGateEval (eval C x) x (3, [i, j]) = (g x && v x) := by
    simp only [serialGateEval, List.all_cons, List.all_nil, Bool.and_true, hgi, hvj]
  obtain ⟨D, hD, hc, hw⟩ := builds_gate C _ _ h₁
  obtain ⟨b, hb, hw'⟩ := hw _ (List.mem_singleton_self _)
  obtain ⟨a, ha, hf'⟩ := has_mono hD hf
  have h₂ (x : Word n) : serialGateEval (eval D x) x (4, [a, b]) = (f x || (g x && v x)) := by
    simp only [serialGateEval, List.any_cons, List.any_nil, Bool.or_false, hf', hw']
  obtain ⟨E, hE, hc', hf''⟩ := builds_gate D _ _ h₂
  exact ⟨E, hD.trans hE, by omega, hf''⟩

-- Store the thresholds of the running count as wires. One AND and one OR update each
-- positive threshold when the next vote arrives.
private def thresholds {n} (fs : List (Word n → Bool)) (m : ℕ) :=
  (List.range (m + 1)).map fun k x => decide (k ≤ fs.countP fun f => f x)

private theorem build_thresholds {n} (fs : List (Word n → Bool)) (m : ℕ) (C : List GLGate)
    (hfs : ∀ f ∈ fs, HasWire C f) :
    BuildsWires C ((fs.length + 1) * ((m + 1) * 2)) (thresholds fs m) := by
  induction fs generalizing C with
  | nil =>
    have hb := builds_seq C (thresholds ([] : List (Word n → Bool)) m) 1 (by
      intro D _ f hf
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
      simpa using builds_const (n := n) D (decide (k = 0)))
    obtain ⟨D, hD, hc, hf⟩ := hb
    exact ⟨D, hD, by simp [thresholds] at hc ⊢; omega, hf⟩
  | cons f fs ih =>
    obtain ⟨D, hD, hc, ht⟩ := ih C (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    have hstep (E) (hE : D <+: E) (g) (hg : g ∈ thresholds (f :: fs) m) : BuildsWires E 2 [g] := by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      have hav (j : ℕ) (hj : j ≤ m) : HasWire E (fun x => decide (j ≤ fs.countP fun g => g x)) :=
        has_mono hE (ht _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))
      cases k with
      | zero =>
        obtain ⟨E', hp, hl, hf⟩ := builds_const (n := n) E true
        exact ⟨E', hp, by omega, by simpa using hf⟩
      | succ k =>
        have hk' := List.mem_range.mp hk
        have hv := has_mono (hD.trans hE) (hfs f (by simp))
        convert builds_threshold_step E _ _ f (hav (k + 1) (by omega)) (hav k (by omega)) hv using 3
        rename_i x
        simp only [List.countP_cons]
        cases f x <;> simp
        omega
    obtain ⟨E, hE, hc', hf⟩ := builds_seq D _ 2 hstep
    refine ⟨E, hD.trans hE, ?_, hf⟩
    simp only [thresholds, List.length_map, List.length_range] at hc'
    rw [List.length_cons, Nat.add_mul, one_mul]
    omega

private def bitCost (m gates : ℕ) := m * (gates + 1) + (m + 1) * ((m + 2) * 2)

private theorem builds_bit {n} (D C : List GLGate) (dirs : List (Word n × Bool)) (a : Word n)
    (b : Bool) (i : Fin n) :
    BuildsWires D (bitCost (2 ^ dirs.length) C.length)
      [fun y => recover dirs a b (answer C y) i] := by
  let qs := probes dirs (shift (basis i) a) b
  let fs := qs.map fun q => fun y => answer C y q.1 ^^ q.2
  have hlen : fs.length = 2 ^ dirs.length := by simp [fs, qs, length_probes]
  have hb := builds_seq D fs (C.length + 1) (by
    intro E _ f hf
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hf
    exact builds_vote E C q.1 q.2)
  obtain ⟨E, hp, hc, hv⟩ := hb
  obtain ⟨E', hp', hc', hv'⟩ := build_thresholds fs (fs.length + 1) E hv
  refine ⟨E', hp.trans hp', ?_, ?_⟩
  · rw [← hlen, bitCost]
    change E'.length ≤ E.length + (fs.length + 1) * ((fs.length + 2) * 2) at hc'
    omega
  intro f hf
  obtain rfl := List.mem_singleton.mp hf
  apply hv'
  refine List.mem_map.mpr ⟨fs.length / 2 + 1, List.mem_range.mpr (by omega), ?_⟩
  funext y
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [fs, List.countP_map, List.length_map, Function.comp_def, recover, qs,
    decide_eq_true_eq]
  omega

private theorem eval_readback {n} (D : List GLGate) (js : List ℕ) (y : Word n)
    (hj : ∀ j ∈ js, j < D.length) :
    eval (D ++ js.map (fun j => (4, [j]))) y =
      eval D y ++ js.map (fun j => (eval D y).getD j false) := by
  induction js using List.reverseRecOn with
  | nil => simp
  | append_singleton l j ih =>
    have hj' : j < D.length := hj _ (by simp)
    have h := ih (fun i hi => hj i (by simp [hi]))
    simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
    rw [eval_snoc, h]
    simp only [serialGateEval, List.any_cons, List.any_nil, Bool.or_false,
      List.getD_append _ _ _ _ (by rwa [eval_len] : j < (eval D y).length)]

private theorem inverter {n} (C : List GLGate) (dirs : List (Word n × Bool)) (a : Word n)
    (b : Bool) :
    ∃ D : List GLGate, D.length ≤ n * bitCost (2 ^ dirs.length) C.length + n ∧
      ∀ y, glCircuitOutputs D (List.ofFn y) n = List.ofFn (recover dirs a b (answer C y)) := by
  let f (i : Fin n) (y : Word n) := recover dirs a b (answer C y) i
  obtain ⟨E, -, hc, hw⟩ := builds_seq [] (List.ofFn f) _ (by
    intro D _ g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact builds_bit D C dirs a b i)
  have hav (i : Fin n) := hw (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  choose j hj he using hav
  let js := List.ofFn j
  refine ⟨E ++ js.map (fun k => (4, [k])), ?_, ?_⟩
  · simpa [js] using Nat.add_le_add_right hc n
  intro y
  have h := eval_readback E js y (fun k hk => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    exact hj i)
  rw [glCircuitOutputs, eval_eq, h]
  simp only [List.length_append, List.length_map, js, List.length_ofFn,
    Nat.add_sub_cancel, List.drop_left]
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => he i y))

private theorem density {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (𝔼 x, indicator (decide (P x))) = (Set.ncard {x | P x} : ℚ) / Fintype.card α := by
  have e : {x | P x} = (↑(univ.filter P) : Set α) := by ext; simp
  rw [Fintype.expect_eq_sum_div_card, e, Set.ncard_coe_finset]
  simp [indicator]

private theorem prediction_bound {n} (C : List GLGate) (π : Word n → Word n) :
    predictSucc C π ≤ 𝔼 x, 𝔼 r, indicator (answer C (π x) r == xorDot x r) := by
  rw [← expect_product', univ_product_univ]
  unfold predictSucc
  let P (q : Word n × Word n) := (eval C (glPair (π q.1) q.2)).getLast? = some (xorDot q.1 q.2)
  calc
    _ = 𝔼 q, indicator (decide (P q)) := by
      rw [density]
      simp only [P, eval_eq, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [show (2 : ℚ) ^ (2 * n) = 2 ^ n * 2 ^ n by rw [two_mul, pow_add]]
    _ ≤ _ := by
      apply expect_le_expect
      intro q _
      by_cases h : P q
      · have hh : (eval C (glPair (π q.1) q.2)).getLast? = some (xorDot q.1 q.2) := h
        simp [h, answer, hh]
      · simp [indicator, h]
        split <;> norm_num

/-! ### Inversion success and the asymptotic bound -/

private theorem finite_reduction {n} (C : List GLGate) (π : Word n → Word n) (k : ℕ)
    {δ : ℚ} (hδ : 0 < δ) : ∃ D : List GLGate,
      D.length ≤ n * bitCost (2 ^ k) C.length + n ∧
      predictSucc C π - 1 / 2 ≤ δ + n / (2 ^ k * δ ^ 2) + (2 * 2 ^ k) * invertSucc D π := by
  obtain ⟨dirs, a, b, hk, hs⟩ := sampling_bound (fun x => answer C (π x)) k δ hδ
  obtain ⟨D, hd, hout⟩ := inverter C dirs a b
  have he : (𝔼 x, indicator (decide (recover dirs a b (answer C (π x)) = x))) =
      invertSucc D π := by
    rw [density]
    simp [invertSucc, hout]
  rw [he] at hs
  exact ⟨D, hk ▸ hd, (sub_le_sub_right (prediction_bound C π) _).trans hs⟩

/-- **Goldreich-Levin: hardcore predicate from one-way permutations.** Let $\pi$ be a family of
bijections $\pi_n$ of the set of $n$-bit strings, one for each natural number $n$. Suppose that
$\pi$ is computable by polynomial-size circuits: there is a polynomial $q$ with natural number
coefficients such that for every $n$ some list of at most $q(n)$ serialized gates has, on every
$n$-bit string $x$, outputs (its last $n$ gate values) equal to $\pi_n(x)$. Suppose also that $\pi$
is one-way: for every polynomial $p$ with natural number coefficients and every family $(C_n)$ of
lists of serialized gates with at most $p(n)$ gates in $C_n$ for all $n$, the inversion success
probability of $C_n$ against $\pi_n$ is a negligible function of $n$. Then for every polynomial
$p$ with natural number coefficients and every family $(C'_n)$ of lists of serialized gates with
at most $p(n)$ gates in $C'_n$ for all $n$, the function $n \mapsto \max(0, s_n - 1/2)$ is
negligible, where $s_n$ is the prediction success probability of $C'_n$ against $\pi_n$ for the
inner product modulo 2.

Source: O.
Goldreich and L. A. Levin, "A hard-core predicate for all one-way functions",
Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989),
25-32. -/
public theorem goldreich_levin :
    ∀ (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool)),
    (∀ n, Function.Bijective (π n)) →
    (∃ pπ : Polynomial ℕ, ∀ n, ∃ Cπ : List GLGate, Cπ.length ≤ pπ.eval n ∧
      ∀ x, glCircuitOutputs Cπ (List.ofFn x) n = List.ofFn (π n x)) →
    (∀ (C : (n : ℕ) → List GLGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        Negligible (fun n => invertSucc (C n) (π n))) →
    ∀ (C' : (n : ℕ) → List GLGate) (p : Polynomial ℕ),
      (∀ n, (C' n).length ≤ p.eval n) →
        Negligible (fun n => max 0 (predictSucc (C' n) (π n) - 1 / 2)) := by
  intro π _ _ how C p hp c
  -- With δ = 1/n^(c+1), use polynomially many probes, at least n/δ³. Both the bias
  -- threshold and the sampling error are then at most δ.
  let d := 3 * (c + 1) + 1
  let k (n : ℕ) := Nat.log 2 (n ^ d + 1) + 1
  let δ (n : ℕ) : ℚ := 1 / (max n 1 : ℕ) ^ (c + 1)
  have hδ (n : ℕ) : 0 < δ n := by
    have hm : (0 : ℚ) < (max n 1 : ℕ) := by exact_mod_cast (by omega : 0 < max n 1)
    dsimp [δ]
    positivity
  choose D hlen hred using fun n => finite_reduction (C n) (π n) (k n) (hδ n)
  let m : Polynomial ℕ := 2 * (Polynomial.X ^ d + 1)
  have hM (n : ℕ) : 2 ^ (k n) ≤ 2 * (n ^ d + 1) := by
    have h := Nat.pow_log_le_self 2 (show n ^ d + 1 ≠ 0 by omega)
    dsimp [k]
    rw [pow_succ, Nat.mul_comm]
    omega
  have hpoly : ∀ n, (D n).length ≤
      (Polynomial.X * (m * (p + 1) + (m + 1) * ((m + 2) * 2)) + Polynomial.X).eval n := by
    intro n
    apply (hlen n).trans
    simp only [bitCost, m, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_ofNat]
    gcongr <;> first | apply hM | apply hp
  obtain ⟨N, hN⟩ := how D _ hpoly (d + (c + 1))
  refine ⟨max N 10, fun n hn => max_le (by positivity) ?_⟩
  have hn10 : 10 ≤ n := le_trans (le_max_right ..) hn
  have hpos : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnQ : (10 : ℚ) ≤ n := by exact_mod_cast hn10
  let u : ℚ := (n : ℚ) ^ (c + 1)
  let v : ℚ := (n : ℚ) ^ d
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hv1 : 1 ≤ v := one_le_pow₀ (by linarith : (1 : ℚ) ≤ n)
  have hvu : v = n * u ^ 3 := by
    dsimp [v, d, u]
    rw [Nat.mul_comm 3, pow_succ, pow_mul, mul_comm]
  have huM : (2 : ℚ) ^ (k n) ≤ 4 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr (hM n)
    push_cast at h
    change (2 : ℚ) ^ _ ≤ 2 * (v + 1) at h
    linarith
  have hlM : v ≤ (2 : ℚ) ^ (k n) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n ^ d + 1)
    change (n : ℚ) ^ d ≤ (2 : ℚ) ^ _
    exact_mod_cast (show n ^ d ≤ 2 ^ (k n) by exact (Nat.le_succ _).trans h.le)
  have hvar : n / ((2 : ℚ) ^ (k n) * (1 / u) ^ 2) ≤ 1 / u := by
    rw [le_div_iff₀ hu, div_mul_eq_mul_div, div_le_one (by positivity)]
    rw [one_div_pow, ← div_eq_mul_one_div, le_div_iff₀ (sq_pos_of_pos hu)]
    nlinarith only [hvu, hlM]
  have hi := hN n ((le_max_left ..).trans hn)
  rw [pow_add] at hi
  change invertSucc (D n) (π n) ≤ 1 / (v * u) at hi
  have hsucc : 2 * (2 : ℚ) ^ (k n) * invertSucc (D n) (π n) ≤ 8 / u := by
    calc
      _ ≤ 2 * (2 : ℚ) ^ (k n) * (1 / (v * u)) := by gcongr
      _ ≤ 2 * (4 * v) * (1 / (v * u)) := by gcongr
      _ = 8 / u := by field_simp; norm_num
  have hr := hred n
  have he : δ n = 1 / u := by unfold δ u; rw [max_eq_left (by omega : 1 ≤ n)]
  rw [he] at hr
  calc
    _ ≤ 1 / u + 1 / u + 8 / u := hr.trans (add_le_add (add_le_add le_rfl hvar) hsucc)
    _ = 10 / u := by ring
    _ ≤ 1 / (n : ℚ) ^ c := by
      dsimp [u]
      rw [pow_succ]
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ (n : ℚ) ^ c by positivity) (sub_nonneg.mpr hnQ)]

end MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevin
