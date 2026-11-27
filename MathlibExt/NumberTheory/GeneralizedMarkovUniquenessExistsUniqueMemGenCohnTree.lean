/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import MathlibExt.LinearAlgebra.Matrix.SpecialLinearGroupTrace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Vertices of generalized Cohn trees

Generalized Cohn triples and trees, built on the generalized Cohn matrices of
`MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul`, the fact that both children of a
generalized Cohn triple are generalized Cohn triples, and uniqueness of the tree parameter and
path of a triple whose middle Markov entry is largest.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5 and Proposition 3.17.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The matrix $S$ of the generalized Cohn triple relation.** For a natural number $k$, $S$
is the $2 \times 2$ integer matrix

$$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}.$$

It is the matrix in the relation $Q = PR - S$ that defines $k$-generalized Cohn triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def genCohnS (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(k : ℤ), 0; 3 * (k : ℤ) ^ 2 + 3 * k, k]

/-- **Generalized Cohn triple.** Let $k$ be a natural number and let $S$ be the integer matrix
with rows $(k, 0)$ and $(3k^2 + 3k, k)$. A triple $(P, Q, R)$ of integer $2 \times 2$ matrices is
a $k$-generalized Cohn triple associated with natural numbers $(a, b, c)$ when $P$, $Q$ and $R$
are $k$-generalized Cohn matrices, $Q = PR - S$, the $(1, 2)$-entries of $P$, $Q$ and $R$ are
$a$, $b$ and $c$ respectively, and $(a, b, c)$ is a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def IsGenCohnTriple (k : ℕ) (P Q R : Matrix (Fin 2) (Fin 2) ℤ) (a b c : ℕ) : Prop :=
  IsGenCohnMatrix k P ∧ IsGenCohnMatrix k Q ∧ IsGenCohnMatrix k R ∧ Q = P * R - genCohnS k ∧
    P 0 1 = a ∧ Q 0 1 = b ∧ R 0 1 = c ∧ IsGenMarkovTriple k a b c

/-- **The matrix $P_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $P_{1;\ell}$ is
the integer $2 \times 2$ matrix with first row $(\ell, 1)$ and second row
$(-\ell^2 + 2k\ell + 3\ell - 1, -\ell + 2k + 3)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnP1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ, 1; -ℓ ^ 2 + 2 * k * ℓ + 3 * ℓ - 1, -ℓ + 2 * k + 3]

/-- **The matrix $Q_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $Q_{1;\ell}$ is
the $2 \times 2$ integer matrix

$$\begin{pmatrix} k + \ell + 1 & 1 \\ k^2 - \ell^2 + 3k + \ell + 1 & k - \ell + 2 \end{pmatrix}.$$

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnQ1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![k + ℓ + 1, 1; (k : ℤ) ^ 2 - ℓ ^ 2 + 3 * k + ℓ + 1, k - ℓ + 2]

/-- **The matrix $R_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $R_{1;\ell}$ is
the $2 \times 2$ integer matrix

$$\begin{pmatrix} 2k + \ell + 2 & 1 \\ -\ell^2 - 2k\ell + 2k - \ell + 1 & -\ell + 1 \end{pmatrix}.$$

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnR1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2 * k + ℓ + 2, 1; -ℓ ^ 2 - 2 * k * ℓ + 2 * k - ℓ + 1, -ℓ + 1]

/-- **One step of the wide generalized Cohn tree.** Fix a natural number $k$ and let $S$ be the
matrix of the $k$-generalized Cohn triple relation. On triples $(P, Q, R)$ of $2 \times 2$
integer matrices, the left step (encoded by the Boolean false) sends $(P, Q, R)$ to its left
child $(P, PQ - S, Q)$, and the right step (encoded by true) sends it to its right child
$(Q, QR - S, R)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnStep (k : ℕ) : Bool →
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →
      Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ
  | false, (P, Q, _) => (P, P * Q - genCohnS k, Q)
  | true, (_, Q, R) => (Q, Q * R - genCohnS k, R)

/-- **Paths of generalized Cohn steps.** Fix a natural number $k$ and let $S$ be the integer
$2 \times 2$ matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$. For a triple $T$ of integer
$2 \times 2$ matrices and a path $w$, a finite sequence of left and right moves, this is the
triple obtained from $T$ by applying the moves of $w$ in order, where a left move sends
$(P, Q, R)$ to $(P, PQ - S, Q)$ and a right move sends $(P, Q, R)$ to $(Q, QR - S, R)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.10. -/
public def genCohnPath (k : ℕ)
    (T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ)
    (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  w.foldl (fun T d => genCohnStep k d T) T

/-- **The wide generalized Cohn tree.** Fix a natural number $k$ and an integer $\ell$, and let
$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}$. The wide $k$-generalized Cohn tree
$\mathrm{WGCT}(k, \ell)$ is the binary tree of triples of $2 \times 2$ integer matrices whose
root is $(P_{1;\ell}, Q_{1;\ell}, R_{1;\ell})$, where

$$P_{1;\ell}=\begin{pmatrix}\ell & 1\\ -\ell^2+2k\ell+3\ell-1 & -\ell+2k+3\end{pmatrix},$$

$$Q_{1;\ell}=\begin{pmatrix}k+\ell+1 & 1\\ k^2-\ell^2+3k+\ell+1 & k-\ell+2\end{pmatrix},$$

$$R_{1;\ell}=\begin{pmatrix}2k+\ell+2 & 1\\ -\ell^2-2k\ell+2k-\ell+1 & -\ell+1\end{pmatrix},$$

and in which a vertex $(P, Q, R)$ has left child $(P, PQ - S, Q)$ and right child
$(Q, QR - S, R)$. For a path $w$, a finite sequence of left and right steps, the vertex of
$\mathrm{WGCT}(k, \ell)$ at $w$ is the triple reached from the root by taking the steps of $w$ in
order; the empty path gives the root.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def wideGenCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  genCohnPath k (genCohnP1 k ℓ, genCohnQ1 k ℓ, genCohnR1 k ℓ) w

/-- **The $k$-generalized Cohn tree.** For $k \in \mathbb{N}$ and $\ell \in \mathbb{Z}$, the
$k$-generalized Cohn tree $\mathrm{GCT}(k, \ell)$ is the full subtree of the wide
$k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$ rooted at the left child of its root. For a
finite sequence $w$ of left and right moves, this is the vertex of $\mathrm{GCT}(k, \ell)$
reached from its root along $w$, that is, the vertex of $\mathrm{WGCT}(k, \ell)$ reached from
the root of $\mathrm{WGCT}(k, \ell)$ by one left move followed by the moves of $w$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  wideGenCohnTree k ℓ (false :: w)

private theorem markov_rotate {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    IsGenMarkovTriple k b c a := by
  refine ⟨h.2.1, h.2.2.1, h.1, ?_⟩
  linear_combination h.2.2.2

private theorem markov_swap {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    IsGenMarkovTriple k c b a := by
  refine ⟨h.2.2.1, h.2.1, h.1, ?_⟩
  linear_combination h.2.2.2

private theorem markov_jump {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    let d := (a ^ 2 + k * a * c + c ^ 2) / b
    IsGenMarkovTriple k a d c ∧ d * b = a ^ 2 + k * a * c + c ^ 2 ∧
      d + b + k * (a + c) = (3 + 3 * k) * a * c := by
  intro d
  have hs : a ^ 2 + k * a * c + c ^ 2 + (b + k * (a + c)) * b =
      (3 + 3 * k) * a * c * b := by linear_combination h.2.2.2
  have hdvd : b ∣ a ^ 2 + k * a * c + c ^ 2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left b (b + k * (a + c)))).mpr
    rw [hs]
    exact dvd_mul_left ..
  have hp : d * b = a ^ 2 + k * a * c + c ^ 2 := Nat.div_mul_cancel hdvd
  have hr : d + b + k * (a + c) = (3 + 3 * k) * a * c := by
    apply mul_right_cancel₀ h.2.1.ne'
    linear_combination hp + hs
  refine ⟨⟨h.1, ?_, h.2.2.1, ?_⟩, hp, hr⟩
  · apply Nat.pos_of_mul_pos_right (b := b)
    rw [hp]
    have ha := h.1
    positivity
  · linear_combination d * hr - hp

private theorem markov_child {k a b c : ℕ} (h : IsGenMarkovTriple k a b c)
    (hab : a < b) (hcb : c < b) (dir : Bool) :
    let t := genMarkovVieta k dir (a, b, c)
    IsGenMarkovTriple k t.1 t.2.1 t.2.2 ∧ t.1 < t.2.1 ∧ t.2.2 < t.2.1 := by
  cases dir
  · obtain ⟨ht, hp, _⟩ := markov_jump (markov_swap (markov_rotate h))
    dsimp [genMarkovVieta]
    have hx : b < (a ^ 2 + k * a * b + b ^ 2) / c := by
      by_contra hn
      have he : (a ^ 2 + k * a * b + b ^ 2) / c ≤ b := by omega
      have hm := Nat.mul_le_mul_right c he
      nlinarith only [hp, hm, Nat.mul_lt_mul_of_pos_left hcb h.2.1,
        Nat.zero_le (a ^ 2), Nat.zero_le (k * a * b)]
    exact ⟨ht, lt_trans hab hx, hx⟩
  · obtain ⟨ht, hp, _⟩ := markov_jump (markov_swap (markov_rotate (markov_rotate h)))
    dsimp [genMarkovVieta]
    have hx : b < (b ^ 2 + k * b * c + c ^ 2) / a := by
      by_contra hn
      have he : (b ^ 2 + k * b * c + c ^ 2) / a ≤ b := by omega
      have hm := Nat.mul_le_mul_right a he
      nlinarith only [hp, hm, Nat.mul_lt_mul_of_pos_left hab h.2.1,
        Nat.zero_le (c ^ 2), Nat.zero_le (k * b * c)]
    exact ⟨ht, hx, lt_trans hcb hx⟩

private theorem markov_descent {k a b c : ℕ} (h : IsGenMarkovTriple k a b c)
    (hac : a ≤ c) (hcb : c < b) :
    (a ^ 2 + k * a * c + c ^ 2) / b ≤ c := by
  obtain ⟨_, hp, hr⟩ := markov_jump h
  let d := (a ^ 2 + k * a * c + c ^ 2) / b
  have ha : (1 : ℤ) ≤ a := by exact_mod_cast h.1
  have hc : (0 : ℤ) < c := by exact_mod_cast h.2.2.1
  have hac' : (a : ℤ) ≤ c := by exact_mod_cast hac
  have hcb' : (c : ℤ) < b := by exact_mod_cast hcb
  have hp' : (d : ℤ) * b = (a : ℤ) ^ 2 + k * a * c + (c : ℤ) ^ 2 := by
    exact_mod_cast hp
  have hr' : (d : ℤ) + b + k * ((a : ℤ) + c) = (3 + 3 * (k : ℤ)) * a * c := by
    exact_mod_cast hr
  have hs : (a : ℤ) ^ 2 ≤ (c : ℤ) ^ 2 := by nlinarith
  have hk : (k : ℤ) * a * c ≤ (k : ℤ) * c * c := by
    nlinarith [mul_nonneg (Int.natCast_nonneg k) (mul_nonneg hc.le (sub_nonneg.mpr hac'))]
  have hm : (3 + 3 * (k : ℤ)) * (c : ℤ) ^ 2 ≤
      (3 + 3 * (k : ℤ)) * a * (c : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha)
      (mul_nonneg (by positivity : 0 ≤ 3 + 3 * (k : ℤ)) (sq_nonneg (c : ℤ)))]
  have hf : (a : ℤ) ^ 2 + ((k : ℤ) + 2) * (c : ℤ) ^ 2 + 2 * k * a * c ≤
      (3 + 3 * (k : ℤ)) * a * (c : ℤ) ^ 2 := by nlinarith
  have hid : ((c : ℤ) - b) * ((c : ℤ) - d) =
      (a : ℤ) ^ 2 + ((k : ℤ) + 2) * (c : ℤ) ^ 2 + 2 * k * a * c -
        (3 + 3 * (k : ℤ)) * a * (c : ℤ) ^ 2 := by
    linear_combination hp' - (c : ℤ) * hr'
  have hd : (d : ℤ) ≤ c := by
    by_contra hn
    have := mul_pos_of_neg_of_neg (by linarith : (c : ℤ) - b < 0) (by linarith : (c : ℤ) - d < 0)
    nlinarith
  exact_mod_cast hd

private theorem cohn_trace {k a : ℕ} {P : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnMatrix k P) (hp : P 0 1 = a) : P.trace = (3 + 3 * k) * a - k := by
  obtain ⟨_, n, hn, _, ht⟩ := h
  have he : n = a := by exact_mod_cast (hn.symm.trans hp)
  simpa only [he] using ht

private theorem det_add_cohnS (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) :
    (P + genCohnS k).det = P.det + k * P.trace - (3 * (k : ℤ) ^ 2 + 3 * k) * P 0 1 +
      (k : ℤ) ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, genCohnS]
  ring

private theorem trace_adjugate_cohnS (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) :
    (P.adjugate * genCohnS k).trace = k * P.trace -
      (3 * (k : ℤ) ^ 2 + 3 * k) * P 0 1 := by
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, genCohnS]
  ring

private theorem trace_adjugate_mul (P R : Matrix (Fin 2) (Fin 2) ℤ) :
    (P.adjugate * R).trace = P.trace * R.trace - (P * R).trace := by
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two]
  ring

private theorem markov_max_tie {k a c : ℕ} (h : IsGenMarkovTriple k a c c) (hac : a ≤ c) :
    a = 1 ∧ c = 1 := by
  have ha : (1 : ℤ) ≤ a := by exact_mod_cast h.1
  have hc : (1 : ℤ) ≤ c := by exact_mod_cast h.2.1
  have hac' : (a : ℤ) ≤ c := by exact_mod_cast hac
  have he : (a : ℤ) ^ 2 + ((k : ℤ) + 2) * (c : ℤ) ^ 2 + 2 * k * a * c =
      (3 + 3 * (k : ℤ)) * a * (c : ℤ) ^ 2 := by
    have he' := h.2.2.2
    have heZ : (a : ℤ) ^ 2 + (c : ℤ) ^ 2 + (c : ℤ) ^ 2 +
        k * ((c : ℤ) * c + (c : ℤ) * a + (a : ℤ) * c) =
          (3 + 3 * (k : ℤ)) * a * c * c := by exact_mod_cast he'
    linear_combination heZ
  have hs : (a : ℤ) ^ 2 ≤ (c : ℤ) ^ 2 := by nlinarith
  have hk : (k : ℤ) * a * c ≤ (k : ℤ) * c * c := by
    nlinarith [mul_nonneg (Int.natCast_nonneg k)
      (mul_nonneg (by linarith : (0 : ℤ) ≤ c) (sub_nonneg.mpr hac'))]
  have hle : (3 + 3 * (k : ℤ)) * a * (c : ℤ) ^ 2 ≤
      (3 + 3 * (k : ℤ)) * (c : ℤ) ^ 2 := by nlinarith
  have ha1 : (a : ℤ) = 1 := by
    have hp : 0 < (3 + 3 * (k : ℤ)) * (c : ℤ) ^ 2 := by positivity
    have hm : (a : ℤ) * ((3 + 3 * (k : ℤ)) * (c : ℤ) ^ 2) ≤
        1 * ((3 + 3 * (k : ℤ)) * (c : ℤ) ^ 2) := by nlinarith only [hle]
    have : (a : ℤ) ≤ 1 := le_of_mul_le_mul_right hm hp
    omega
  have hkc : (k : ℤ) * c ≤ (k : ℤ) * (c : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (Int.natCast_nonneg k)
      (mul_nonneg (by linarith : (0 : ℤ) ≤ c) (by linarith : 0 ≤ (c : ℤ) - 1))]
  have hc1 : (c : ℤ) = 1 := by rw [ha1] at he; nlinarith
  exact ⟨by exact_mod_cast ha1, by exact_mod_cast hc1⟩

private theorem markov_descent_lt {k a b c : ℕ} (h : IsGenMarkovTriple k a b c)
    (hac : a < c) (hcb : c < b) : (a ^ 2 + k * a * c + c ^ 2) / b < c := by
  have hd := markov_descent h hac.le hcb
  obtain ⟨ht, _, _⟩ := markov_jump h
  by_contra hn
  have he : (a ^ 2 + k * a * c + c ^ 2) / b = c := by omega
  rw [he] at ht
  obtain ⟨ha, hc⟩ := markov_max_tie ht hac.le
  omega

private theorem markov_equal_endpoints {k a b : ℕ} (h : IsGenMarkovTriple k a b a)
    (hab : a < b) : a = 1 ∧ b = k + 2 := by
  obtain ⟨ht, _, _⟩ := markov_jump h
  have hd := markov_descent h le_rfl hab
  have ha := (markov_max_tie (markov_rotate ht) hd).2
  refine ⟨ha, ?_⟩
  subst a
  have he : (1 : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 ^ 2 +
      k * ((b : ℤ) * 1 + 1 * 1 + 1 * b) = (3 + 3 * (k : ℤ)) * 1 * b * 1 := by
    exact_mod_cast h.2.2.2
  have hf : ((b : ℤ) - 1) * ((b : ℤ) - (k + 2)) = 0 := by linear_combination he
  have hb : (b : ℤ) ≠ 1 := by exact_mod_cast (Nat.ne_of_gt hab)
  have := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hb)
  exact_mod_cast (sub_eq_zero.mp this)

private theorem cohn_root {k : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R 1 (k + 2) 1) :
    genCohnTree k (P 0 0) [] = (P, Q, R) := by
  obtain ⟨hP, _, hR, hQ, hp, hq, hr, _⟩ := h
  have tp := cohn_trace hP hp
  have tr := cohn_trace hR hr
  have dp := hP.1
  have dr := hR.1
  have hentry : (k : ℤ) + 2 = P 0 0 + R 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, genCohnS, hp, hr, hq] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hQ
  simp only [Matrix.det_fin_two, hp, hr] at dp dr
  simp only [Matrix.trace_fin_two] at tp tr
  norm_num only [Nat.cast_one, Nat.cast_add, Nat.cast_ofNat, mul_one, one_mul] at dp dr tp tr hp hr
  have heR : R 0 0 = k + P 0 0 + 1 := by linarith
  have heP : P 1 1 = -P 0 0 + 2 * k + 3 := by linarith
  have heR11 : R 1 1 = k - P 0 0 + 2 := by linarith
  rw [heP] at dp
  rw [heR, heR11] at dr
  have hP1 : P = genCohnP1 k (P 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [genCohnP1] <;> nlinarith only [heP, dp, hp]
  have hR1 : R = genCohnQ1 k (P 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [genCohnQ1] <;>
      nlinarith only [heR11, dr, hr, heR]
  simp only [genCohnTree, wideGenCohnTree, genCohnPath, List.foldl_cons, List.foldl_nil,
    genCohnStep]
  rw [← hP1, ← hR1, ← hQ]

private theorem cohn_left_parent {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    let d := (a ^ 2 + k * a * c + c ^ 2) / b
    let X := P.adjugate * (R + genCohnS k)
    IsGenCohnTriple k P R X a c d ∧ genCohnStep k false (P, R, X) = (P, Q, R) := by
  intro d X
  obtain ⟨hP, hQ, hR, he, hp, hq, hr, ht⟩ := h
  obtain ⟨hd, _, hs⟩ := markov_jump ht
  have tp := cohn_trace hP hp
  have tq := cohn_trace hQ hq
  have tr := cohn_trace hR hr
  have hsZ : (d : ℤ) + b + k * ((a : ℤ) + c) = (3 + 3 * (k : ℤ)) * a * c := by
    exact_mod_cast hs
  have hprod : P * R = Q + genCohnS k := (eq_sub_iff_add_eq.mp he).symm
  have hrel : R = P * X - genCohnS k := by
    dsimp only [X]
    rw [← mul_assoc, Matrix.mul_adjugate, hP.1, one_smul, one_mul, add_sub_cancel_right]
  have hx : X 0 1 = d := by
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hprod
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp, hr, hq, genCohnS] at hentry
    simp only [Matrix.trace_fin_two] at tp
    dsimp only [X]
    simp [Matrix.adjugate_fin_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      genCohnS, hp, hr]
    linear_combination (c : ℤ) * tp - hentry - hsZ
  have dx : X.det = 1 := by
    dsimp only [X]
    rw [Matrix.det_mul, Matrix.det_adjugate, hP.1, one_pow, one_mul, det_add_cohnS,
      hR.1, tr, hr]
    ring
  have tx : X.trace = (3 + 3 * k) * d - k := by
    dsimp only [X]
    rw [mul_add, Matrix.trace_add, trace_adjugate_mul, trace_adjugate_cohnS, hprod,
      Matrix.trace_add, tp, tq, tr, hp]
    simp only [genCohnS, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination -(3 + 3 * (k : ℤ)) * hsZ
  refine ⟨⟨hP, hR, ⟨dx, d, hx, ⟨a, c, hd⟩, tx⟩, hrel, hp, hr, hx, ?_⟩, ?_⟩
  · exact markov_swap (markov_rotate hd)
  · simp only [genCohnStep]
    rw [← he]

private theorem cohn_right_parent {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    let d := (a ^ 2 + k * a * c + c ^ 2) / b
    let X := (P + genCohnS k) * R.adjugate
    IsGenCohnTriple k X P R d a c ∧ genCohnStep k true (X, P, R) = (P, Q, R) := by
  intro d X
  obtain ⟨hP, hQ, hR, he, hp, hq, hr, ht⟩ := h
  obtain ⟨hd, _, hs⟩ := markov_jump ht
  have tp := cohn_trace hP hp
  have tq := cohn_trace hQ hq
  have tr := cohn_trace hR hr
  have hsZ : (d : ℤ) + b + k * ((a : ℤ) + c) = (3 + 3 * (k : ℤ)) * a * c := by
    exact_mod_cast hs
  have hprod : P * R = Q + genCohnS k := (eq_sub_iff_add_eq.mp he).symm
  have hrel : P = X * R - genCohnS k := by
    dsimp only [X]
    rw [mul_assoc, Matrix.adjugate_mul, hR.1, one_smul, mul_one, add_sub_cancel_right]
  have hx : X 0 1 = d := by
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hprod
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp, hr, hq, genCohnS] at hentry
    simp only [Matrix.trace_fin_two] at tr
    dsimp only [X]
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, genCohnS, hp, hr]
    linear_combination (a : ℤ) * tr - hentry - hsZ
  have dx : X.det = 1 := by
    dsimp only [X]
    rw [Matrix.det_mul, Matrix.det_adjugate, hR.1, one_pow, mul_one, det_add_cohnS,
      hP.1, tp, hp]
    ring
  have tx : X.trace = (3 + 3 * k) * d - k := by
    dsimp only [X]
    rw [Matrix.trace_mul_comm, mul_add, Matrix.trace_add, trace_adjugate_mul,
      trace_adjugate_cohnS, Matrix.trace_mul_comm R P, hprod, Matrix.trace_add,
      tp, tq, tr, hr]
    simp only [genCohnS, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination -(3 + 3 * (k : ℤ)) * hsZ
  refine ⟨⟨⟨dx, d, hx, ⟨a, c, hd⟩, tx⟩, hP, hR, hrel, hx, hp, hr, ?_⟩, ?_⟩
  · exact markov_rotate (markov_swap hd)
  · simp only [genCohnStep]
    rw [← he]

private theorem det_sub_cohnS (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) :
    (P - genCohnS k).det = P.det - k * P.trace +
      (3 * (k : ℤ) ^ 2 + 3 * k) * P 0 1 + (k : ℤ) ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, genCohnS]
  ring

private theorem cohn_left_child {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    let e := (a ^ 2 + k * a * b + b ^ 2) / c
    IsGenCohnTriple k P (P * Q - genCohnS k) Q a e b := by
  intro e
  obtain ⟨hP, hQ, hR, he, hp, hq, hr, ht⟩ := h
  obtain ⟨hm, _, hs⟩ := markov_jump (markov_swap (markov_rotate ht))
  have tp := cohn_trace hP hp
  have tq := cohn_trace hQ hq
  have tr := cohn_trace hR hr
  have hsZ : (e : ℤ) + c + k * ((a : ℤ) + b) = (3 + 3 * (k : ℤ)) * a * b := by
    exact_mod_cast hs
  have hprod : P * R = Q + genCohnS k := (eq_sub_iff_add_eq.mp he).symm
  have hch : P * P = P.trace • P - 1 := by
    simpa only [pow_two] using
      SpecialLinearGroupTrace.sq_eq_trace_smul_sub_one ⟨P, hP.1⟩
  have hnew : P * Q = P.trace • (Q + genCohnS k) - R - P * genCohnS k := by
    rw [he, mul_sub, ← mul_assoc, hch, sub_mul, Matrix.smul_mul, one_mul, hprod]
    simp
  have hx : (P * Q - genCohnS k) 0 1 = e := by
    rw [hnew]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, genCohnS, hp, hq, hr, tp]
    linear_combination -hsZ
  have hi : P.adjugate * Q = R - P.adjugate * genCohnS k := by
    rw [he, mul_sub, ← mul_assoc, Matrix.adjugate_mul, hP.1, one_smul, one_mul]
  have tn : (P * Q - genCohnS k).trace = (3 + 3 * k) * e - k := by
    have hc := trace_adjugate_mul P Q
    rw [hi, Matrix.trace_sub, trace_adjugate_cohnS, tp, tq, tr, hp] at hc
    rw [Matrix.trace_sub]
    have ts : (genCohnS k).trace = (k : ℤ) + k := by simp [genCohnS, Matrix.trace_fin_two]
    rw [ts]
    linear_combination hc - (3 + 3 * (k : ℤ)) * hsZ
  have dn : (P * Q - genCohnS k).det = 1 := by
    have hsdet : (P * Q - genCohnS k).det = (P * Q).det - k * (P * Q).trace +
        (3 * (k : ℤ) ^ 2 + 3 * k) * (P * Q) 0 1 + (k : ℤ) ^ 2 := det_sub_cohnS k (P * Q)
    have hntrace : (P * Q).trace = (3 + 3 * k) * e + k := by
      rw [Matrix.trace_sub] at tn
      have ts : (genCohnS k).trace = (k : ℤ) + k := by simp [genCohnS, Matrix.trace_fin_two]
      rw [ts] at tn
      linarith
    have hnentry : (P * Q) 0 1 = e := by simpa [genCohnS] using hx
    rw [hsdet, Matrix.det_mul, hP.1, hQ.1, hntrace, hnentry]
    ring
  exact ⟨hP, ⟨dn, e, hx, ⟨a, b, hm⟩, tn⟩, hQ, rfl, hp, hx, hq, hm⟩

private def cohnFlip (P : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![P 1 1, P 0 1; P 1 0, P 0 0]

private theorem cohnFlip_invol (P : Matrix (Fin 2) (Fin 2) ℤ) :
    cohnFlip (cohnFlip P) = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem cohnFlip_mul (P Q : Matrix (Fin 2) (Fin 2) ℤ) :
    cohnFlip (P * Q) = cohnFlip Q * cohnFlip P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cohnFlip, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem cohnFlip_sub (P Q : Matrix (Fin 2) (Fin 2) ℤ) :
    cohnFlip (P - Q) = cohnFlip P - cohnFlip Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem cohnFlip_S (k : ℕ) : cohnFlip (genCohnS k) = genCohnS k := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem cohn_flip {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k (cohnFlip R) (cohnFlip Q) (cohnFlip P) c b a := by
  have hm : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, IsGenCohnMatrix k M →
      IsGenCohnMatrix k (cohnFlip M) := by
    intro M hM
    obtain ⟨hd, n, hn, ht, htr⟩ := hM
    refine ⟨?_, n, hn, ht, ?_⟩
    · simpa [cohnFlip, Matrix.det_fin_two, mul_comm] using hd
    · simpa [cohnFlip, Matrix.trace_fin_two, add_comm] using htr
  obtain ⟨hP, hQ, hR, he, hp, hq, hr, ht⟩ := h
  refine ⟨hm R hR, hm Q hQ, hm P hP, ?_, hr, hq, hp, markov_swap ht⟩
  rw [he, cohnFlip_sub, cohnFlip_mul, cohnFlip_S]

private theorem cohn_right_child {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k Q (Q * R - genCohnS k) R b
      ((b ^ 2 + k * b * c + c ^ 2) / a) c := by
  have he : (c ^ 2 + k * c * b + b ^ 2) / a = (b ^ 2 + k * b * c + c ^ 2) / a := by
    congr 1
    ring
  simpa only [cohnFlip_invol, cohnFlip_sub, cohnFlip_mul, cohnFlip_S, he] using
    cohn_flip (cohn_left_child (cohn_flip h))

/-- **Children of a generalized Cohn triple.** Let $k$ be a natural number, let $S$ be the integer
matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$, and let $(P, Q, R)$ be a $k$-generalized Cohn
triple associated with $(a, b, c)$. Then $(P, PQ - S, Q)$ is a $k$-generalized Cohn triple
associated with $(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$, and $(Q, QR - S, R)$ is a
$k$-generalized Cohn triple associated with $(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5. -/
public theorem IsGenCohnTriple.step {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P (P * Q - genCohnS k) Q a ((a ^ 2 + k * a * b + b ^ 2) / c) b ∧
      IsGenCohnTriple k Q (Q * R - genCohnS k) R b ((b ^ 2 + k * b * c + c ^ 2) / a) c :=
  ⟨cohn_left_child h, cohn_right_child h⟩

private def CohnVertex (k : ℕ)
    (T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ a b c : ℕ, IsGenCohnTriple k T.1 T.2.1 T.2.2 a b c ∧ a < b ∧ c < b

private theorem CohnVertex.step {k : ℕ}
    {T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ}
    (h : CohnVertex k T) (dir : Bool) : CohnVertex k (genCohnStep k dir T) := by
  obtain ⟨P, Q, R⟩ := T
  obtain ⟨a, b, c, ht, hab, hcb⟩ := h
  have hg := markov_child ht.2.2.2.2.2.2.2 hab hcb dir
  cases dir
  · exact ⟨a, _, b, cohn_left_child ht, hg.2⟩
  · exact ⟨b, _, c, cohn_right_child ht, hg.2⟩

private theorem cohn_wide_root (k : ℕ) (ℓ : ℤ) :
    IsGenCohnTriple k (genCohnP1 k ℓ) (genCohnQ1 k ℓ) (genCohnR1 k ℓ) 1 1 1 := by
  have hn : IsGenMarkovNumber k 1 := ⟨1, 1, isGenMarkovTriple_one_one_one k⟩
  have hP : IsGenCohnMatrix k (genCohnP1 k ℓ) := by
    refine ⟨?_, 1, rfl, hn, ?_⟩ <;>
      simp [genCohnP1, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
  have hQ : IsGenCohnMatrix k (genCohnQ1 k ℓ) := by
    refine ⟨?_, 1, rfl, hn, ?_⟩ <;>
      simp [genCohnQ1, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
  have hR : IsGenCohnMatrix k (genCohnR1 k ℓ) := by
    refine ⟨?_, 1, rfl, hn, ?_⟩ <;>
      simp [genCohnR1, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
  refine ⟨hP, hQ, hR, ?_, rfl, rfl, rfl, isGenMarkovTriple_one_one_one k⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [genCohnP1, genCohnQ1, genCohnR1, genCohnS] <;>
      ring

private theorem cohn_tree_vertex (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    CohnVertex k (genCohnTree k ℓ w) := by
  have hroot := cohn_left_child (cohn_wide_root k ℓ)
  have hroot' : CohnVertex k (genCohnTree k ℓ []) := by
    refine ⟨1, k + 2, 1, ?_, by omega, by omega⟩
    simpa [genCohnTree, wideGenCohnTree, genCohnPath, genCohnStep,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hroot
  change CohnVertex k (w.foldl (fun T d => genCohnStep k d T) (genCohnTree k ℓ []))
  exact w.foldlRecOn _ hroot' fun _ h dir _ => h.step dir

private theorem cohn_tree_append (k : ℕ) (ℓ : ℤ) (w : List Bool) (dir : Bool) :
    genCohnTree k ℓ (w ++ [dir]) = genCohnStep k dir (genCohnTree k ℓ w) := by
  simp [genCohnTree, wideGenCohnTree, genCohnPath, List.foldl_append]

private theorem cohn_step_order {k : ℕ}
    {T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ}
    (h : CohnVertex k T) :
    (genCohnStep k false T).1 0 1 < (genCohnStep k false T).2.2 0 1 ∧
      (genCohnStep k true T).2.2 0 1 < (genCohnStep k true T).1 0 1 := by
  obtain ⟨P, Q, R⟩ := T
  obtain ⟨a, b, c, ht, hab, hcb⟩ := h
  obtain ⟨_, _, _, _, hp, hq, hr, _⟩ := ht
  change P 0 1 < Q 0 1 ∧ R 0 1 < Q 0 1
  change P 0 1 = (a : ℤ) at hp
  change Q 0 1 = (b : ℤ) at hq
  change R 0 1 = (c : ℤ) at hr
  simp only [hp, hq, hr]
  exact ⟨by exact_mod_cast hab, by exact_mod_cast hcb⟩

private theorem cohn_step_injective {k : ℕ}
    {T U : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ}
    (hT : CohnVertex k T) (hU : CohnVertex k U) (dir : Bool)
    (he : genCohnStep k dir T = genCohnStep k dir U) : T = U := by
  obtain ⟨P, Q, R⟩ := T
  obtain ⟨P', Q', R'⟩ := U
  obtain ⟨_, _, _, ht, _, _⟩ := hT
  obtain ⟨_, _, _, hu, _, _⟩ := hU
  obtain ⟨hp, _, hr, ht, _, _, _, _⟩ := ht
  obtain ⟨_, _, _, hu, _, _, _, _⟩ := hu
  cases dir
  · have hP : P = P' := congrArg (fun t => t.1) he
    have hQ : Q = Q' := congrArg (fun t => t.2.2) he
    subst P'
    subst Q'
    have hm : P * R = P * R' := by
      simpa only [sub_add_cancel] using congrArg (· + genCohnS k) (ht.symm.trans hu)
    have heR := congrArg (P.adjugate * ·) hm
    simp only [← mul_assoc, Matrix.adjugate_mul, hp.1, one_smul, one_mul] at heR
    rw [heR]
  · have hQ : Q = Q' := congrArg (fun t => t.1) he
    have hR : R = R' := congrArg (fun t => t.2.2) he
    subst Q'
    subst R'
    have hm : P * R = P' * R := by
      simpa only [sub_add_cancel] using congrArg (· + genCohnS k) (ht.symm.trans hu)
    have heP := congrArg (· * R.adjugate) hm
    simp only [mul_assoc, Matrix.mul_adjugate, hr.1, one_smul, mul_one] at heP
    rw [heP]

private theorem cohn_tree_nil_order (k : ℕ) (ℓ : ℤ) :
    (genCohnTree k ℓ []).1 0 1 = (genCohnTree k ℓ []).2.2 0 1 := rfl

private theorem cohn_tree_injective {k : ℕ} {ℓ ℓ' : ℤ} {w w' : List Bool}
    (he : genCohnTree k ℓ w = genCohnTree k ℓ' w') : (ℓ, w) = (ℓ', w') := by
  induction w using List.reverseRecOn generalizing ℓ' w' with
  | nil =>
    induction w' using List.reverseRecOn with
    | nil =>
      have hl : ℓ = ℓ' := congrArg (fun t => t.1 0 0) he
      rw [hl]
    | append_singleton w' dir _ =>
      rw [cohn_tree_append] at he
      have ho := cohn_step_order (cohn_tree_vertex k ℓ' w')
      have hr := cohn_tree_nil_order k ℓ
      rw [he] at hr
      cases dir with
      | false => exact ((ne_of_lt ho.1) hr).elim
      | true => exact ((ne_of_gt ho.2) hr).elim
  | append_singleton w dir ih =>
    induction w' using List.reverseRecOn with
    | nil =>
      rw [cohn_tree_append] at he
      have ho := cohn_step_order (cohn_tree_vertex k ℓ w)
      have hr := cohn_tree_nil_order k ℓ'
      rw [← he] at hr
      cases dir with
      | false => exact ((ne_of_lt ho.1) hr).elim
      | true => exact ((ne_of_gt ho.2) hr).elim
    | append_singleton w' dir' _ =>
      rw [cohn_tree_append, cohn_tree_append] at he
      by_cases hd : dir = dir'
      · subst dir'
        have hh := cohn_step_injective (cohn_tree_vertex k ℓ w)
          (cohn_tree_vertex k ℓ' w') dir he
        have hp := ih hh
        obtain ⟨hl, hw⟩ := Prod.mk.inj hp
        rw [hl, hw]
      · cases dir with
        | false =>
          cases dir' with
          | false => exact (hd rfl).elim
          | true =>
            have ho := (cohn_step_order (cohn_tree_vertex k ℓ w)).1
            have ho' := (cohn_step_order (cohn_tree_vertex k ℓ' w')).2
            rw [he] at ho
            exact (lt_asymm ho ho').elim
        | true =>
          cases dir' with
          | true => exact (hd rfl).elim
          | false =>
            have ho := (cohn_step_order (cohn_tree_vertex k ℓ w)).2
            have ho' := (cohn_step_order (cohn_tree_vertex k ℓ' w')).1
            rw [he] at ho
            exact (lt_asymm ho ho').elim

private theorem cohn_exists {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) (hab : a < b) (hcb : c < b) :
    ∃ p : ℤ × List Bool, genCohnTree k p.1 p.2 = (P, Q, R) := by
  induction b using Nat.strong_induction_on generalizing a c P Q R with
  | ind b ih =>
    have ht := h.2.2.2.2.2.2.2
    rcases lt_trichotomy a c with hac | hac | hca
    · let d := (a ^ 2 + k * a * c + c ^ 2) / b
      obtain ⟨hp, hs⟩ := cohn_left_parent h
      have hd : d < c := markov_descent_lt ht hac hcb
      obtain ⟨⟨ℓ, w⟩, hw⟩ := ih c hcb hp hac hd
      refine ⟨(ℓ, w ++ [false]), ?_⟩
      rw [cohn_tree_append, hw, hs]
    · subst c
      obtain ⟨ha, hb⟩ := markov_equal_endpoints ht hab
      subst a
      subst b
      exact ⟨(P 0 0, []), cohn_root h⟩
    · let d := (a ^ 2 + k * a * c + c ^ 2) / b
      obtain ⟨hp, hs⟩ := cohn_right_parent h
      have heq : (c ^ 2 + k * c * a + a ^ 2) / b = d := by
        dsimp only [d]
        congr 1
        ring
      have hd : d < a := by
        simpa only [heq] using markov_descent_lt (markov_swap ht) hca hab
      obtain ⟨⟨ℓ, w⟩, hw⟩ := ih a hab hp hd hca
      refine ⟨(ℓ, w ++ [true]), ?_⟩
      rw [cohn_tree_append, hw, hs]

/-- **Cohn triples sit at a unique vertex of a Cohn tree.** Let $(P, Q, R)$ be a
$k$-generalized Cohn triple associated with $(a, b, c)$, where $b > \max\{a, c\}$. Then there is
exactly one pair $(\ell, w)$ of an integer $\ell$ and a path $w$ (a finite sequence of left and
right moves) such that $(P, Q, R)$ is the vertex of the $k$-generalized Cohn tree
$\mathrm{GCT}(k, \ell)$ reached along $w$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.17. -/
public theorem IsGenCohnTriple.existsUnique_mem_genCohnTree {k a b c : ℕ}
    {P Q R : Matrix (Fin 2) (Fin 2) ℤ} (h : IsGenCohnTriple k P Q R a b c) (hab : a < b)
    (hcb : c < b) : ∃! p : ℤ × List Bool, genCohnTree k p.1 p.2 = (P, Q, R)
    := by
  obtain ⟨p, hp⟩ := cohn_exists h hab hcb
  refine ⟨p, hp, ?_⟩
  rintro ⟨ℓ, w⟩ hw
  exact cohn_tree_injective (hw.trans hp.symm)

end

end MetaMathlibExt
