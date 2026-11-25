/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Extended continuants

For a bi-infinite integer sequence `x : ℤ → ℤ`, the extended continuant
`extendedContinuant x a b` has order `a` and start index `b`. Its recurrence in the order
gives the determinant identity `extendedContinuant_det` for every integer order and the entries
of the westbound matrix product. For table (33) with `σ ≡ 5 (mod 6)`,
`silentTerms_table_five_mod_six` evaluates the silent-term formulas.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Forward branch of the extended continuant.** For an integer sequence
$x : \mathbb{Z} \to \mathbb{Z}$ and an integer $b$, the forward branch with start index $b$ is the
sequence $(F_n)_{n \ge 0}$ of integers defined by $F_0 = 0$, $F_1 = 1$ and
$F_{n+2} = x_{b+n} F_{n+1} + F_n$. Its value $F_n$ is the extended continuant $K_{n-2}(x)_b$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definition 3 (right-adjusting recurrence). -/
public def extendedContinuantFwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => x (b + n) * extendedContinuantFwd x b (n + 1) + extendedContinuantFwd x b n

/-- **Backward branch of the extended continuant.** For an integer sequence
$x : \mathbb{Z} \to \mathbb{Z}$ and an integer $b$, the backward branch with start index $b$ is
the sequence $(B_m)_{m \ge 0}$ of integers defined by $B_0 = 1$, $B_1 = 0$ and
$B_{m+2} = -x_{b-1-m} B_{m+1} + B_m$. Its value $B_m$ is the extended continuant
$K_{-1-m}(x)_b$ of negative order $-1-m$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definition 4 (right-adjusting recurrence). -/
public def extendedContinuantBwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | m + 2 => -x (b - 1 - m) * extendedContinuantBwd x b (m + 1) + extendedContinuantBwd x b m

/-- **Extended continuants.** Let $x : \mathbb{Z} \to \mathbb{Z}$ be a bi-infinite integer sequence
and $b$ an integer. The extended continuant $K_a(x)_b$ of order $a \in \mathbb{Z}$ with start index
$b$ (the paper's $K_a(x)_b^{a+b}$) is the integer defined by $K_{-2}(x)_b = 0$, $K_{-1}(x)_b = 1$,
the forward recurrence $K_a(x)_b = x_{b+a} K_{a-1}(x)_b + K_{a-2}(x)_b$ for $a \ge 0$, and the
backward recurrence $K_a(x)_b = K_{a+2}(x)_b - x_{b+a+2} K_{a+1}(x)_b$ for $a \le -3$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public def extendedContinuant (x : ℤ → ℤ) (a b : ℤ) : ℤ :=
  if 0 ≤ a + 2 then extendedContinuantFwd x b (a + 2).toNat
  else extendedContinuantBwd x b (-1 - a).toNat

private theorem extendedContinuant_eq_fwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {n : ℕ}
    (h : a + 2 = n) : extendedContinuant x a b = extendedContinuantFwd x b n := by
  unfold extendedContinuant
  split_ifs
  · congr 1
    omega
  · omega

private theorem extendedContinuant_eq_bwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {m : ℕ}
    (h : a = -1 - m) : extendedContinuant x a b = extendedContinuantBwd x b m := by
  rcases m with _ | _ | m
  · rw [extendedContinuant_eq_fwd x b (n := 1) (by omega)]
    rfl
  · rw [extendedContinuant_eq_fwd x b (n := 0) (by omega)]
    rfl
  · unfold extendedContinuant
    split_ifs
    · omega
    · congr 1
      omega

/-- **Extended continuants of order $-2$ vanish.** For every bi-infinite integer sequence
$x : \mathbb{Z} \to \mathbb{Z}$ and every integer $b$, the extended continuant of order $-2$ with
start index $b$ is zero: $K_{-2}(x)_b = 0$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public theorem extendedContinuant_neg_two (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-2) b = 0 :=
  extendedContinuant_eq_fwd x b (n := 0) (by omega)

/-- **Extended continuant of order $-1$.** For every integer sequence
$x : \mathbb{Z} \to \mathbb{Z}$ and every integer $b$, the extended continuant of $x$ of order
$-1$ with start index $b$ equals $1$, that is, $K_{-1}(x)_b = 1$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public theorem extendedContinuant_neg_one (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-1) b = 1 :=
  extendedContinuant_eq_fwd x b (n := 1) (by omega)

/-- **The extended continuant of order $0$ is a single term.** For every bi-infinite integer
sequence $x : \mathbb{Z} \to \mathbb{Z}$ and every integer $b$, the extended continuant of order $0$
with start index $b$ is $K_0(x)_b = x_b$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Section 3.4 and Equation (13). -/
public theorem extendedContinuant_zero (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x 0 b = x b := by
  rw [extendedContinuant_eq_fwd x b (n := 2) (by omega)]
  simp [extendedContinuantFwd]

/-- **Recurrence for extended continuants.** For every bi-infinite integer sequence
$x : \mathbb{Z} \to \mathbb{Z}$ and all integers $a$ and $b$, the extended continuants $K_a(x)_b$
of order $a$ with start index $b$ satisfy
$K_a(x)_b = x_{b+a} K_{a-1}(x)_b + K_{a-2}(x)_b$.

For $a \le -1$ this is the paper's backward recurrence of Definition 4.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4 (RA versions). -/
public theorem extendedContinuant_recurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x (b + a) * extendedContinuant x (a - 1) b + extendedContinuant x (a - 2) b := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [extendedContinuant_eq_fwd x b (n := n + 2) (by omega),
      extendedContinuant_eq_fwd x b (n := n + 1) (by omega),
      extendedContinuant_eq_fwd x b (n := n) (by omega)]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, a = -1 - m := ⟨(-1 - a).toNat, by omega⟩
    rw [extendedContinuant_eq_bwd x b (m := m) hm,
      extendedContinuant_eq_bwd x b (m := m + 1) (by omega),
      extendedContinuant_eq_bwd x b (m := m + 2) (by omega)]
    have hx : b + a = b - 1 - m := by omega
    simp only [extendedContinuantBwd, hx]
    ring

/-- **Extended continuants of orders $-3$ to $-6$.** Let $x : \mathbb{Z} \to \mathbb{Z}$ be an
integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start index
$b$. For every integer $h$, $K_{-3}(x)_h = 1$, $K_{-4}(x)_h = -x_{h-2}$,
$K_{-5}(x)_h = 1 + x_{h-3} x_{h-2}$ and
$K_{-6}(x)_h = -(x_{h-4} + x_{h-2} + x_{h-4} x_{h-3} x_{h-2})$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 1. -/
public theorem extendedContinuant_neg_three_to_six (x : ℤ → ℤ) (h : ℤ) :
    extendedContinuant x (-3) h = 1 ∧ extendedContinuant x (-4) h = -x (h - 2) ∧
      extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) ∧
      extendedContinuant x (-6) h =
        -(x (h - 4) + x (h - 2) + x (h - 4) * x (h - 3) * x (h - 2)) := by
  have r := extendedContinuant_recurrence x
  have k1 := extendedContinuant_neg_one x h
  have k2 := extendedContinuant_neg_two x h
  have e1 := r (-1) h
  have e2 := r (-2) h
  have e3 := r (-3) h
  have e4 := r (-4) h
  norm_num at e1 e2 e3 e4
  rw [show h + -1 = h - 1 by ring] at e1
  rw [show h + -2 = h - 2 by ring] at e2
  rw [show h + -3 = h - 3 by ring] at e3
  rw [show h + -4 = h - 4 by ring] at e4
  have h3 : extendedContinuant x (-3) h = 1 := by rw [k1, k2] at e1; linarith
  have h4 : extendedContinuant x (-4) h = -x (h - 2) := by rw [k2, h3] at e2; linarith
  have h5 : extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) := by
    rw [h3, h4] at e3; linarith
  refine ⟨h3, h4, h5, ?_⟩
  rw [h4, h5] at e4
  linear_combination -e4

/-- **Reflection formula for the order of extended continuants.** Let
$x : \mathbb{Z} \to \mathbb{Z}$ be an integer sequence and write $K_a(x)_b$ for its extended
continuant of order $a$ with start index $b$. For all integers $h$ and $n$,
$$K_{-n}(x)_h = (-1)^{n+1} K_{n-4}(x)_{h-n+2}.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 1. -/
public theorem extendedContinuant_neg_order (x : ℤ → ℤ) (h n : ℤ) :
    extendedContinuant x (-n) h =
      ((n + 1).negOnePow : ℤ) * extendedContinuant x (n - 4) (h - n + 2) := by
  -- Index both solutions by the same right endpoint, h - k.
  let K (b k : ℤ) := extendedContinuant x (h - k - b) b
  have recurrence (b k : ℤ) : K b (k - 1) = x (h - k + 1) * K b k + K b (k + 1) := by
    dsimp only [K]
    convert extendedContinuant_recurrence x (h - (k - 1) - b) b using 1
    ring_nf
  let b := h - n + 2
  let D (k : ℤ) := K h k * K b (k - 1) - K h (k - 1) * K b k
  have flip (k : ℤ) : D (k + 1) = -D k := by
    dsimp only [D]
    rw [add_sub_cancel_right, recurrence h k, recurrence b k]
    ring
  -- The sign-corrected determinant is determined by its value at k = 2.
  let P (k : ℤ) := D k = ((k + 1).negOnePow : ℤ) * K b 2
  have step (k : ℤ) : P (k + 1) ↔ P k := by
    simp only [P, flip, Int.negOnePow_succ (k + 1), Units.val_neg, neg_mul, neg_inj]
  have base : P 2 := by
    change D 2 = -1 * K b 2
    simp only [D, K]
    ring_nf
    simp [extendedContinuant_neg_two, extendedContinuant_neg_one]
  have hn : P n := Int.inductionOn' n 2 base (fun k _ => (step k).2)
    (fun k _ ih => (step (k - 1)).1 (by simpa using ih))
  dsimp only [P, D, K, b] at hn
  ring_nf at hn ⊢
  simpa [extendedContinuant_neg_one, extendedContinuant_neg_two] using hn

/-- **Determinant identity for extended continuants.** Let $x : \mathbb{Z} \to \mathbb{Z}$ be an
integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start index
$b$. For every integer $n$,
$$K_n(x)_0 K_{n-2}(x)_1 - K_{n-1}(x)_1 K_{n-1}(x)_0 = (-1)^{n+1}.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 2. -/
public theorem extendedContinuant_det (x : ℤ → ℤ) (n : ℤ) :
    extendedContinuant x n 0 * extendedContinuant x (n - 2) 1 -
        extendedContinuant x (n - 1) 1 * extendedContinuant x (n - 1) 0 =
      ((n + 1).negOnePow : ℤ) := by
  let D (n : ℤ) := extendedContinuant x n 0 * extendedContinuant x (n - 2) 1 -
    extendedContinuant x (n - 1) 1 * extendedContinuant x (n - 1) 0
  -- Both continuants of order `n` expand with the same term `x n`, which cancels.
  have flip (n : ℤ) : D n = -D (n - 1) := by
    have h₀ := extendedContinuant_recurrence x n 0
    have h₁ := extendedContinuant_recurrence x (n - 1) 1
    rw [zero_add] at h₀
    rw [show 1 + (n - 1) = n by ring, show n - 1 - 1 = n - 2 by ring] at h₁
    dsimp only [D]
    rw [show n - 1 - 1 = n - 2 by ring]
    linear_combination extendedContinuant x (n - 2) 1 * h₀ -
      extendedContinuant x (n - 1) 0 * h₁
  -- So the determinant alternates in sign from its value `1` at order `-1`.
  have base : D (-1) = ((-1 + 1 : ℤ).negOnePow : ℤ) := by
    norm_num [D, extendedContinuant_neg_one, extendedContinuant_neg_two,
      (extendedContinuant_neg_three_to_six x 1).1]
  change D n = _
  refine Int.inductionOn' n (-1) base (fun k _ ih => ?_) (fun k _ ih => ?_)
  · rw [flip, add_sub_cancel_right, ih, Int.negOnePow_succ (k + 1), Units.val_neg]
  · rw [flip k, Int.negOnePow_succ, Units.val_neg, neg_inj] at ih
    rwa [sub_add_cancel]

/-- **Westbound matrix product of extended continuants.** Let $x : \mathbb{Z} \to \mathbb{Z}$ be a
bi-infinite integer sequence, write $K_a(x)_b$ for the extended continuant of order $a$ with start
index $b$, and put $M_i = \begin{pmatrix} 0 & 1 \\ 1 & -x_{-i} \end{pmatrix}$. Then for every
integer $n \ge 1$,

$$
M_n M_{n-1} \cdots M_1 =
\begin{pmatrix} K_{-n-1}(x)_0 & K_{-n-2}(x)_1 \\ K_{-n-2}(x)_0 & K_{-n-3}(x)_1 \end{pmatrix}.
$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 1. -/
public theorem extendedContinuant_westbound_matrix_prod (x : ℤ → ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    (List.ofFn fun i : Fin n => !![0, 1; 1, -x (-((n : ℤ) - i))]).prod =
      !![extendedContinuant x (-n - 1) 0, extendedContinuant x (-n - 2) 1;
        extendedContinuant x (-n - 2) 0, extendedContinuant x (-n - 3) 1] := by
  have step (a b : ℤ) :
      extendedContinuant x a b + -x (b + a) * extendedContinuant x (a - 1) b =
        extendedContinuant x (a - 2) b := by
    linear_combination extendedContinuant_recurrence x a b
  induction n, hn using Nat.le_induction with
  | base =>
    have h₀ := extendedContinuant_neg_three_to_six x 0
    have h₁ := extendedContinuant_neg_three_to_six x 1
    norm_num [List.ofFn_succ, extendedContinuant_neg_two, h₀.1, h₁.1, h₁.2.1]
  | succ n _ ih =>
    rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_succ,
      add_sub_add_right_eq_sub]
    rw [ih, Matrix.mul_fin_two]
    simp only [zero_mul, one_mul, zero_add]
    have h₀ := step (-(n : ℤ) - 1) 0
    have h₁ := step (-(n : ℤ) - 2) 1
    ring_nf at h₀ h₁ ⊢
    rw [h₀, h₁]

/-- **No silent sequences of even order.** Let $\sigma \ge 0$ be an even integer and write
$K_a(x)_b$ for the extended continuant of order $a$ with start index $b$. For all bi-infinite
integer sequences $x, z : \mathbb{Z} \to \mathbb{Z}$ it is not the case that
$K_{-i-\sigma-1}(x)_0 = K_i(z)_0$ and $K_{-i-\sigma-2}(x)_1 = K_{i-1}(z)_1$ for every natural
number $i$.

In the paper's terms: for even $\sigma$ no bi-infinite sequence $x$ is $\sigma$-silent, that is,
there is no sequence $z$ such that for every $i \ge 0$ the raw westbound convergent
$k_{-i-\sigma-1} = K_{-i-\sigma-1}(x)_0 / K_{-i-\sigma-2}(x)_1$ of $x$ is strictly equivalent
(equal numerators and equal denominators) to the raw convergent $d_i = K_i(z)_0 / K_{i-1}(z)_1$
of $z$. The BpCF conditions are not needed.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 4. -/
public theorem not_silent_of_even (x z : ℤ → ℤ) (σ : ℕ) (hσ : Even σ) :
    ¬ ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1 := by
  intro h
  obtain rfl | hpos := Nat.eq_zero_or_pos σ
  · have hd := (h 0).2
    norm_num [extendedContinuant_neg_two, extendedContinuant_neg_one] at hd
  -- Every westbound factor has determinant -1, so the even product has determinant 1.
  have hdet := congrArg (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) ℤ →* ℤ)
    (extendedContinuant_westbound_matrix_prod x σ hpos)
  rw [map_list_prod, List.map_ofFn] at hdet
  simp [Function.comp_def, Matrix.det_fin_two_of, List.ofFn_const, List.prod_replicate,
    hσ.neg_one_pow] at hdet
  -- Strict equivalence identifies the two rows with the first two eastbound convergents.
  have h₀ := h 0
  have h₁ := h 1
  norm_num at h₀ h₁
  ring_nf at h₀ h₁ hdet
  rw [h₀.1, h₀.2, h₁.1, h₁.2] at hdet
  have east := extendedContinuant_recurrence z 1 0
  norm_num [extendedContinuant_neg_one, extendedContinuant_zero] at east hdet
  linarith

-- Reflect the order to turn the right-end recurrence into a left-end recurrence.
private theorem silentTerms_table_five_mod_six.leftRecurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x b * extendedContinuant x (a - 1) (b + 1) + extendedContinuant x (a - 2) (b + 2) := by
  have reflect (j : ℤ) :
      extendedContinuant x (a - j) (b + j) =
        ((1 - a + j).negOnePow : ℤ) * extendedContinuant x (-a - 4 + j) (b + a + 2) := by
    convert extendedContinuant_neg_order x (b + j) (j - a) using 1 <;> ring_nf
  have r := extendedContinuant_recurrence x (-a - 2) (b + a + 2)
  have h₀ := reflect 0
  have h₁ := reflect 1
  have h₂ := reflect 2
  simp only [sub_zero, add_zero] at h₀
  rw [show 1 - a + 2 = (1 - a + 1) + 1 by ring, Int.negOnePow_succ, Int.negOnePow_succ,
    neg_neg] at h₂
  rw [Int.negOnePow_succ, Units.val_neg] at h₁
  rw [h₀, h₁, h₂]
  ring_nf at r ⊢
  rw [r]
  ring

set_option linter.unusedVariables false in
/-- **Silent-term formulas on table (33), case $\sigma \equiv 5 \pmod 6$.** Let $\sigma \ge 7$ be
an integer with $\sigma \equiv 5 \pmod 6$, let $c_1 \ne c_2$ be integers, and let
$x : \mathbb{Z} \to \mathbb{Z}$ be a bi-infinite integer sequence with $x_{-3} = x_0 + c_1$,
$x_{-2} = 1$, $x_{-1} = -1$ and, for all integers $4 \le m \le \sigma - 3$, $x_{-m} = -1$ if
$m \equiv 2 \pmod 3$ and $x_{-m} = 1$ otherwise. Write $K_a(x)_b$ for the extended continuant of
order $a$ with start index $b$, and put $z_0 = x_0 + c_2$ and
$w = -K_{\sigma-5}(x)_{-\sigma+3} - z_0 K_{\sigma-4}(x)_{-\sigma+3}$. Then $w \ne 0$ and
$-1 + K_{\sigma-6}(x)_{-\sigma+4} + z_0 K_{\sigma-5}(x)_{-\sigma+4} = (1 + c_2 - c_1) w$.

So formula (29) of Theorem 7, with $z_0 = x_0 + c_2$, gives $x_{-\sigma+1} = w \ne 0$ and
$x_{-\sigma+2} = 1 + c_2 - c_1$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 5 mod 6`). -/
public theorem silentTerms_table_five_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 5)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁) (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 2 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) - (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)
        ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        (1 + c₂ - c₁) * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)) := by
  let z := x 0 + c₂
  let F (m : ℤ) := extendedContinuant x (m - 2) (-m) + z * extendedContinuant x (m - 1) (-m)
  have step (m : ℤ) : F m = x (-m) * F (m - 1) + F (m - 2) := by
    dsimp only [F]
    rw [silentTerms_table_five_mod_six.leftRecurrence x (m - 2) (-m),
      silentTerms_table_five_mod_six.leftRecurrence x (m - 1) (-m)]
    ring_nf
  have f₀ : F 0 = z := by
    simp [F, extendedContinuant_neg_two, extendedContinuant_neg_one]
  have f₁ : F 1 = 1 - z := by
    norm_num [F, extendedContinuant_neg_one, extendedContinuant_zero, h1]
    ring
  have f₂ : F 2 = 1 := by
    have h := step 2
    norm_num [h2, f₁, f₀] at h
    omega
  let t := 1 + c₁ - c₂
  have f₃ : F 3 = t := by
    have h := step 3
    norm_num [h3, f₂, f₁, z] at h
    dsimp [t]
    omega
  have table (m : ℤ) (hm : 4 ≤ m) (hle : m ≤ σ - 3) :
      F m = (if m % 3 = 2 then -1 else 1) * F (m - 1) + F (m - 2) := by
    rw [step m, htab m hm hle]
  -- In each row the coefficients 1, -1, 1 send the pair (q, p) to (-q, p).
  have rowEnd (m : ℤ) (hm : 3 ≤ m) (hmod : m % 3 = 0) (hle : m + 2 ≤ σ - 3) :
      F (m + 1) = F m + F (m - 1) ∧ F (m + 2) = -F (m - 1) := by
    have r₁ := table (m + 1) (by omega) (by omega)
    have r₂ := table (m + 2) (by omega) hle
    rw [ite_eq_right (show (m + 1) % 3 ≠ 2 by omega), one_mul] at r₁
    rw [ite_eq_left (show (m + 2) % 3 = 2 by omega), neg_one_mul] at r₂
    grind
  have rows (n : ℕ) (hn : 3 * (n : ℤ) + 5 ≤ σ - 3) :
      F (3 * n + 4) = t + (-1 : ℤ) ^ n ∧ F (3 * n + 5) = -(-1 : ℤ) ^ n := by
    induction n with
    | zero =>
      have h := rowEnd 3 (by decide) (by decide) (by omega)
      norm_num at h ⊢
      grind
    | succ n ih =>
      obtain ⟨p, q⟩ := ih (by omega)
      have r := table (3 * n + 6) (by omega) (by omega)
      rw [ite_eq_right (show (3 * (n : ℤ) + 6) % 3 ≠ 2 by omega), one_mul] at r
      have h := rowEnd (3 * n + 6) (by omega) (by omega) (by omega)
      simp only [Nat.cast_succ, pow_succ]
      grind
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ = 6 * (k : ℤ) + 11 := ⟨((σ - 11) / 6).toNat, by omega⟩
  obtain ⟨u, v⟩ := rows (2 * k + 1) (by omega)
  have hsign : (-1 : ℤ) ^ (2 * k + 1) = -1 := (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_one_pow
  rw [hsign] at u v
  have hu : F (σ - 4) = t - 1 := by
    rw [show σ - 4 = 3 * ((2 * k + 1 : ℕ) : ℤ) + 4 by omega, u]
    ring
  have hv : F (σ - 3) = 1 := by
    rw [show σ - 3 = 3 * ((2 * k + 1 : ℕ) : ℤ) + 5 by omega, v]
    decide
  have hleft : -1 + F (σ - 4) = (1 + c₂ - c₁) * -F (σ - 3) := by
    rw [hu, hv]
    dsimp [t]
    ring
  have hne : -F (σ - 3) ≠ 0 := by rw [hv]; decide
  dsimp only [F, z] at hleft hne
  constructor
  · convert hne using 1
    ring_nf
  · convert hleft using 1 <;> ring_nf

end

end MetaMathlibExt
