/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# The perceptron mistake bound (Novikoff)

The perceptron (Rosenblatt 1958) learns a linear classifier `x ↦ sign (w ⬝ᵥ x)` from labelled
examples `(x, y)`, `x : ι → K`, `y : Bool` with label `sign y = ±1`. It starts from `w = 0` and
scans the examples; whenever the current weights do not classify an example strictly correctly,
`sign y * (w ⬝ᵥ x) ≤ 0`, it adds `sign y • x` to `w` (a mistake). `K` is any ordered commutative
ring (`ℚ`, `ℝ`, `ℤ`).

Main results:

* `mistakes_mul_sq_le` (Novikoff 1962): if every example satisfies `x ⬝ᵥ x ≤ R ^ 2` and some `u`
  separates them with margin `γ > 0`, `γ ≤ sign y * (u ⬝ᵥ x)`, then on any finite sequence of
  these examples the perceptron makes `k` mistakes with `k * γ ^ 2 ≤ (u ⬝ᵥ u) * R ^ 2`; for a unit
  `u` that is the textbook `k ≤ R² / γ²` (`mistakes_le_div` over a field).
* `train_converges`: repeating passes over the data until a pass makes no mistake (`train`)
  stops within any number `n` of passes with `(u ⬝ᵥ u) * R ^ 2 < n * γ ^ 2`, and returns weights
  that classify every example strictly correctly (`train_classifies`).

The proof follows Novikoff, *On convergence proofs on perceptrons* (1962); see also Shalev-Shwartz
and Ben-David, *Understanding Machine Learning*, Theorem 9.1. After `k` mistakes, `u ⬝ᵥ w ≥ k γ`
(each mistake adds at least `γ`) and `w ⬝ᵥ w ≤ k R ^ 2` (each mistake adds
`2 sign y (w ⬝ᵥ x) + x ⬝ᵥ x ≤ R ^ 2`); Cauchy-Schwarz `(u ⬝ᵥ w) ^ 2 ≤ (u ⬝ᵥ u) (w ⬝ᵥ w)` then gives
`k ^ 2 γ ^ 2 ≤ (u ⬝ᵥ u) k R ^ 2`. Squared norms are used throughout, so no square roots are needed.

## Cost model

No `TimeM` cost model: the measured quantity is the number of mistakes (weight updates), which
`run` counts in its state; each example costs one dot product. `train` makes at most `n` passes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Perceptron

open Matrix

variable {ι K : Type*} [Fintype ι] [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Sign of a Boolean label.** For a commutative ring $K$, the sign of a Boolean label $y$ is
the element $\operatorname{sign}(y) \in K$ equal to $1$ if $y$ is true and to $-1$ if $y$ is
false. -/
def sign (y : Bool) : K := if y then 1 else -1

/-- **Perceptron step.** Let $K$ be a commutative ring with a linear order, $\iota$ a finite type,
and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$. One perceptron step
takes a state $(w, m)$, made of weights $w \in K^\iota$ and a mistake count $m \in \mathbb{N}$, and
a labelled example $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean. If
$\operatorname{sign}(y)\,(w \cdot x) \le 0$, that is, $w$ does not classify the example strictly
correctly, the step returns $(w + \operatorname{sign}(y)\,x,\ m + 1)$ and counts a mistake;
otherwise it returns $(w, m)$ unchanged. -/
def step (s : (ι → K) × ℕ) (e : (ι → K) × Bool) : (ι → K) × ℕ :=
  if (sign e.2 : K) * (s.1 ⬝ᵥ e.1) ≤ 0 then (s.1 + (sign e.2 : K) • e.1, s.2 + 1) else s

/-- **Perceptron run.** Let $K$ be a commutative ring with a linear order and $\iota$ a finite type.
The run of the perceptron over a finite list $L$ of labelled examples $(x, y)$, with
$x \in K^\iota$ and $y$ a Boolean, from weights $w \in K^\iota$ with $m \in \mathbb{N}$ mistakes so
far is the pair of final weights and final mistake count obtained by applying the perceptron step
to each example of $L$ in order, starting from the state $(w, m)$. -/
def run (w : ι → K) (m : ℕ) (xs : List ((ι → K) × Bool)) : (ι → K) × ℕ :=
  xs.foldl step (w, m)

/-- **Perceptron training.** Given a finite list $D$ of labelled examples, a number $n$ of passes
and weights $w$, training returns nothing when $n = 0$. When $n = m + 1$, it runs one perceptron
pass over $D$ from $w$ with mistake count $0$; if that pass makes no mistake it returns $w$, and
otherwise it trains on $D$ for $m$ passes from the weights the pass produced. So training repeats
passes until one makes no mistake, for at most $n$ passes, and returns the weights of that pass,
or nothing if every pass made a mistake. -/
def train (xs : List ((ι → K) × Bool)) : ℕ → (ι → K) → Option (ι → K)
  | 0, _ => none
  | n + 1, w =>
      let r := run w 0 xs
      if r.2 = 0 then some w else train xs n r.1

omit [Fintype ι] [LinearOrder K] [IsStrictOrderedRing K] in
theorem sign_mul_sign (y : Bool) : (sign y : K) * sign y = 1 := by
  cases y <;> simp [sign]

/-! ## Bookkeeping -/

omit [IsStrictOrderedRing K] in
theorem step_of_mistake {w : ι → K} {m : ℕ} {e : (ι → K) × Bool}
    (h : (sign e.2 : K) * (w ⬝ᵥ e.1) ≤ 0) : step (w, m) e = (w + (sign e.2 : K) • e.1, m + 1) := by
  simp only [step, h, ↓reduceIte]

omit [IsStrictOrderedRing K] in
theorem step_of_correct {w : ι → K} {m : ℕ} {e : (ι → K) × Bool}
    (h : ¬ (sign e.2 : K) * (w ⬝ᵥ e.1) ≤ 0) : step (w, m) e = (w, m) := by
  simp only [step, h, ↓reduceIte]

omit [IsStrictOrderedRing K] in
/-- **The starting mistake count only shifts the final count.** Let $K$ be a commutative ring
with a linear order and $\iota$ a finite type, and let $L$ be a finite list of labelled examples
$(x, y)$ with $x \in K^\iota$ and $y$ a Boolean. For all weights $w \in K^\iota$ and every natural
number $m$, the perceptron run over $L$ from $w$ with $m$ mistakes so far ends with the same weights
as the run from $w$ with $0$ mistakes so far, and with mistake count $m + c$, where $c$ is the final
mistake count of the run from $w$ with $0$ mistakes so far. -/
theorem run_eq (xs : List ((ι → K) × Bool)) :
    ∀ (w : ι → K) (m : ℕ), run w m xs = ((run w 0 xs).1, m + (run w 0 xs).2) := by
  induction xs with
  | nil => intro w m; simp [run]
  | cons e xs ih =>
      intro w m
      simp only [run, List.foldl_cons] at ih ⊢
      by_cases hm : (sign e.2 : K) * (w ⬝ᵥ e.1) ≤ 0
      · rw [step_of_mistake hm, step_of_mistake hm, ih _ (m + 1), ih _ (0 + 1)]
        simp only [Prod.mk.injEq, true_and]; omega
      · rw [step_of_correct hm, step_of_correct hm, ih w m]

omit [IsStrictOrderedRing K] in
theorem run_append (w : ι → K) (m : ℕ) (xs ys : List ((ι → K) × Bool)) :
    run w m (xs ++ ys) = run (run w m xs).1 (run w m xs).2 ys := by
  simp [run, List.foldl_append]

omit [IsStrictOrderedRing K] in
/-- **A mistake-free pass classifies every example.** Let $K$ be a commutative ring with a linear
order, $\iota$ a finite type, and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on
$K^\iota$. Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$ and $y$ a
Boolean, and let $w \in K^\iota$. If the perceptron run over $L$ from weights $w$ with $0$ mistakes
so far ends with mistake count $0$, then every example $(x, y)$ in $L$ satisfies
$0 < \operatorname{sign}(y)\,(w \cdot x)$. -/
theorem classifies_of_run_eq_zero (xs : List ((ι → K) × Bool)) :
    ∀ w : ι → K, (run w 0 xs).2 = 0 → ∀ e ∈ xs, 0 < sign e.2 * (w ⬝ᵥ e.1) := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
      intro w h e' he'
      simp only [run, List.foldl_cons] at h
      by_cases hm : (sign e.2 : K) * (w ⬝ᵥ e.1) ≤ 0
      · rw [step_of_mistake hm,
          show (xs.foldl step (w + (sign e.2 : K) • e.1, 0 + 1)) = run _ (0 + 1) xs from rfl,
          run_eq] at h
        omega
      · rw [step_of_correct hm] at h
        rcases List.mem_cons.1 he' with rfl | he'
        · exact not_le.1 hm
        · exact ih w h e' he'

/-! ## Novikoff's mistake bound -/

variable {u : ι → K} {γ R : K}

/-- **Invariant of the perceptron run.** Let $K$ be a linearly ordered commutative ring, $\iota$ a
finite type, $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$, $u \in K^\iota$
and $\gamma, R \in K$. Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$
and $y$ a Boolean, such that every example in $L$ satisfies
$\gamma \le \operatorname{sign}(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. Let $w \in K^\iota$ and
$m \in \mathbb{N}$ satisfy $m \gamma \le u \cdot w$ and $w \cdot w \le m R^2$, and let the
perceptron run over $L$ from $w$ with $m$ mistakes so far end with weights $w'$ and mistake count
$m'$. Then $m' \gamma \le u \cdot w'$ and $w' \cdot w' \le m' R^2$. -/
theorem run_invariant (xs : List ((ι → K) × Bool))
    (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2) :
    ∀ (w : ι → K) (m : ℕ), (m : K) * γ ≤ u ⬝ᵥ w → w ⬝ᵥ w ≤ m * R ^ 2 →
      ((run w m xs).2 : K) * γ ≤ u ⬝ᵥ (run w m xs).1 ∧
        (run w m xs).1 ⬝ᵥ (run w m xs).1 ≤ (run w m xs).2 * R ^ 2 := by
  induction xs with
  | nil => intro w m h1 h2; exact ⟨h1, h2⟩
  | cons e xs ih =>
      intro w m h1 h2
      have ih' := ih (fun e' he' => hsep e' (List.mem_cons_of_mem _ he'))
        (fun e' he' => hR e' (List.mem_cons_of_mem _ he'))
      simp only [run, List.foldl_cons] at ih' ⊢
      by_cases hm : (sign e.2 : K) * (w ⬝ᵥ e.1) ≤ 0
      · rw [step_of_mistake hm]
        refine ih' _ _ ?_ ?_
        · have := hsep e List.mem_cons_self
          rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
          push_cast
          linarith
        · have hx := hR e List.mem_cons_self
          have hs := sign_mul_sign (K := K) e.2
          have hc : e.1 ⬝ᵥ w = w ⬝ᵥ e.1 := dotProduct_comm _ _
          simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
            smul_eq_mul, hc]
          push_cast
          nlinarith
      · rw [step_of_correct hm]
        exact ih' w m h1 h2

/-- Mathlib's Cauchy-Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`, read for the dot product. -/
private theorem dotProduct_sq_le (v w : ι → K) : (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  simpa [dotProduct, sq] using this

/-- **Novikoff's perceptron mistake bound.** Let $K$ be a linearly ordered commutative ring,
$\iota$ a finite type, $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$,
$u \in K^\iota$, and $\gamma, R \in K$ with $\gamma > 0$. Let $L$ be a finite list of labelled
examples $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean, such that every example in $L$ satisfies
$\gamma \le \operatorname{sign}(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. If the perceptron run
over $L$ from the zero weights with $0$ mistakes so far ends with mistake count $k$, then
$k \gamma^2 \le (u \cdot u) R^2$. -/
theorem mistakes_mul_sq_le (xs : List ((ι → K) × Bool))
    (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2)
    (hγ : 0 < γ) : ((run 0 0 xs).2 : K) * γ ^ 2 ≤ (u ⬝ᵥ u) * R ^ 2 := by
  obtain ⟨h1, h2⟩ := run_invariant xs hsep hR 0 0 (by simp) (by simp)
  set k : K := ((run 0 0 xs).2 : K)
  set w := (run 0 0 xs).1
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hcs := dotProduct_sq_le u w
  have huu : 0 ≤ u ⬝ᵥ u := by
    have := dotProduct_sq_le u u
    simpa [dotProduct, ← sq] using Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have hsq : (k * γ) ^ 2 ≤ (u ⬝ᵥ w) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  rcases hk.lt_or_eq with hk | hk
  · have : k * (k * γ ^ 2) ≤ k * ((u ⬝ᵥ u) * R ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hk
  · rw [← hk]; simp only [zero_mul]; positivity

/-- **Novikoff's mistake bound over an ordered field.** Let $F$ be a linearly ordered field,
$\iota$ a finite type, $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $F^\iota$,
$u \in F^\iota$, and $\gamma, R \in F$ with $\gamma > 0$. Let $L$ be a finite list of labelled
examples $(x, y)$ with $x \in F^\iota$ and $y$ a Boolean, such that every example in $L$ satisfies
$\gamma \le \operatorname{sign}(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. If the perceptron run
over $L$ from the zero weights with $0$ mistakes so far ends with mistake count $k$, then
$k \le (u \cdot u) R^2 / \gamma^2$; for a unit vector $u$ this is the textbook bound
$R^2 / \gamma^2$. -/
theorem mistakes_le_div {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {u : ι → F} {γ R : F} (xs : List ((ι → F) × Bool))
    (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2)
    (hγ : 0 < γ) : ((run 0 0 xs).2 : F) ≤ (u ⬝ᵥ u) * R ^ 2 / γ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact mistakes_mul_sq_le xs hsep hR hγ

/-! ## Training until a pass makes no mistake -/

omit [IsStrictOrderedRing K] in
/-- **Trained weights classify every example.** Let $K$ be a commutative ring with a linear order,
$\iota$ a finite type, and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$.
Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean. For
every natural number $n$ and all weights $w, v \in K^\iota$, if training on $L$ from $w$ with at
most $n$ passes returns $v$, then every example $(x, y)$ in $L$ satisfies
$0 < \operatorname{sign}(y)\,(v \cdot x)$. -/
theorem train_classifies (xs : List ((ι → K) × Bool)) :
    ∀ (n : ℕ) (w v : ι → K), train xs n w = some v → ∀ e ∈ xs, 0 < sign e.2 * (v ⬝ᵥ e.1)
  | 0, _, _, h => by simp [train] at h
  | n + 1, w, v, h => by
      simp only [train] at h
      split_ifs at h with h0
      · cases h; exact classifies_of_run_eq_zero xs w h0
      · exact train_classifies xs n _ v h

omit [IsStrictOrderedRing K] in
/-- **Every failed training pass adds a mistake.** Let $K$ be a commutative ring with a linear
order and $\iota$ a finite type, and let $L$ be a finite list of labelled examples $(x, y)$ with
$x \in K^\iota$ and $y$ a Boolean. For every natural number $n$ and all weights $w \in K^\iota$, if
training on $L$ from $w$ with at most $n$ passes returns no weights, then the perceptron run from
$w$ with $0$ mistakes so far over the concatenation of $n$ copies of $L$ ends with a mistake count
of at least $n$. -/
theorem le_run_of_train_eq_none (xs : List ((ι → K) × Bool)) :
    ∀ (n : ℕ) (w : ι → K), train xs n w = none →
      n ≤ (run w 0 (List.replicate n xs).flatten).2
  | 0, _, _ => Nat.zero_le _
  | n + 1, w, h => by
      simp only [train] at h
      split_ifs at h with h0
      have ih := le_run_of_train_eq_none xs n _ h
      rw [List.replicate_succ, List.flatten_cons, run_append, run_eq]
      omega

/-- **The perceptron converges.** Let $K$ be a linearly ordered commutative ring, let $\iota$ be a
finite index type, write $a \cdot b = \sum_{j \in \iota} a_j b_j$ for $a, b \in K^\iota$, and let
the label sign $s(y)$ be $1$ if the Boolean $y$ is true and $-1$ otherwise. Let $D$ be a finite
list of examples $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean, and let $u \in K^\iota$ and
$\gamma, R \in K$ with $\gamma > 0$ be such that every example $(x, y)$ of $D$ satisfies
$\gamma \le s(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. Then for every natural number $n$ with
$(u \cdot u) R^2 < n \gamma^2$, perceptron training on $D$ from the zero weights with at most $n$
passes returns some weights $v$, and $0 < s(y)\,(v \cdot x)$ for every example $(x, y)$ of $D$. -/
theorem train_converges (xs : List ((ι → K) × Bool))
    (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2)
    (hγ : 0 < γ) {n : ℕ} (hn : (u ⬝ᵥ u) * R ^ 2 < n * γ ^ 2) :
    ∃ v, train xs n 0 = some v ∧ ∀ e ∈ xs, 0 < sign e.2 * (v ⬝ᵥ e.1) := by
  cases h : train xs n 0 with
  | some v => exact ⟨v, rfl, train_classifies xs n 0 v h⟩
  | none =>
      exfalso
      have hle := le_run_of_train_eq_none xs n 0 h
      have hmem : ∀ e ∈ (List.replicate n xs).flatten, e ∈ xs := by
        intro e he
        obtain ⟨l, hl, he⟩ := List.mem_flatten.1 he
        rw [(List.eq_of_mem_replicate hl)] at he
        exact he
      have hb := mistakes_mul_sq_le _ (fun e he => hsep e (hmem e he))
        (fun e he => hR e (hmem e he)) hγ
      have : (n : K) * γ ^ 2 ≤ ((run 0 0 (List.replicate n xs).flatten).2 : K) * γ ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (by positivity)
      linarith

end Cslib.MachineLearning.Perceptron
