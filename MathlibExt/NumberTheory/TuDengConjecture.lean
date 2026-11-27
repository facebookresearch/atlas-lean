/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DigitalBinomialTheorem
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Tu-Deng conjecture

The theorem `tuDengConjecture_holds` bounds the number of modular pairs with small combined
binary digit sum. The proof follows Cusick's cyclic transfer matrix and coefficient inequalities.

Z. Tu and Y. Deng stated the conjecture in "A conjecture about binary strings and its applications
on constructing Boolean functions with optimal algebraic immunity", Des. Codes Cryptogr. 60
(2011), 1–14.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.TuDengConjectureWanted

open MetaMathlibExt (binDigitSum binDigitSum_two_mul binDigitSum_two_mul_add_one)

def tuDengConjecture : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ t : ZMod (2 ^ k - 1), t ≠ 0 →
    {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
      p.1 + p.2 = t ∧ binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

-- Subtraction from the all-ones word complements each of the k bits.
private theorem weight_complement (k a : ℕ) (ha : a < 2 ^ k) :
    binDigitSum (2 ^ k - 1 - a) + binDigitSum a = k := by
  induction k generalizing a with
  | zero =>
    simp at ha
    simp [ha]
  | succ k ih =>
    rw [pow_succ] at ha ⊢
    have hp := Nat.two_pow_pos k
    have h := ih (a / 2) (by omega)
    by_cases parity : a % 2 = 0
    · have hc : 2 ^ k * 2 - 1 - a = 2 * (2 ^ k - 1 - a / 2) + 1 := by omega
      conv_lhs => rw [hc, show a = 2 * (a / 2) by omega]
      simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2),
        binDigitSum_two_mul_add_one, binDigitSum_two_mul]
      omega
    · have hc : 2 ^ k * 2 - 1 - a = 2 * (2 ^ k - 1 - a / 2) := by omega
      rw [hc, binDigitSum_two_mul]
      have hw : binDigitSum a = binDigitSum (a / 2) + 1 := by
        conv_lhs => rw [show a = 2 * (a / 2) + 1 by omega, binDigitSum_two_mul_add_one]
      omega

-- For fixed a, the second residue is forced. Writing n = (2 ^ k - 1) - a.val turns
-- the pair condition into a strict weight drop under translation by t.
private theorem pairs_eq_drops (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) :
    {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
      p.1 + p.2 = t ∧ binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}.ncard =
    {n : ℕ | n < 2 ^ k ∧ binDigitSum ((n : ZMod (2 ^ k - 1)) + t).val < binDigitSum n}.ncard := by
  let M := 2 ^ k - 1
  have hpow := Nat.lt_two_pow_self (n := k)
  have : NeZero M := ⟨by dsimp [M]; omega⟩
  change {p : ZMod M × ZMod M | p.1 + p.2 = t ∧
      binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}.ncard =
    {n : ℕ | n < 2 ^ k ∧ binDigitSum ((n : ZMod M) + t).val < binDigitSum n}.ncard
  refine Set.ncard_congr (fun p _ => M - p.1.val) ?_ ?_ ?_
  · rintro ⟨a, b⟩ ⟨rfl, hw⟩
    have hal := a.val_lt
    have hc : ((M - a.val : ℕ) : ZMod M) = -a := by
      rw [Nat.cast_sub hal.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
    change M - a.val < 2 ^ k ∧
      binDigitSum (((M - a.val : ℕ) : ZMod M) + (a + b)).val < binDigitSum (M - a.val)
    rw [hc, neg_add_cancel_left]
    have h := weight_complement k a.val (by dsimp [M] at hal; omega)
    change binDigitSum a.val + binDigitSum b.val ≤ k - 1 at hw
    dsimp [M]
    omega
  · rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hs, _⟩ ⟨hs', _⟩ he
    change M - a.val = M - c.val at he
    have ha := a.val_lt
    have hc := c.val_lt
    have hac : a.val = c.val := by omega
    have hac' : a = c := by
      simpa only [ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : ZMod M)) hac
    subst c
    change a + b = t at hs
    change a + d = t at hs'
    exact Prod.ext rfl (add_left_cancel (hs.trans hs'.symm))
  · rintro n ⟨hn, hw⟩
    have hpos : 0 < n := by
      by_contra! hz
      simp_all
    have hsub : M - n < M := by dsimp [M]; omega
    have hnM : n ≤ M := by dsimp [M]; omega
    let a : ZMod M := (M - n : ℕ)
    have ha : a.val = M - n := ZMod.val_natCast_of_lt hsub
    have hcast : a = -(n : ZMod M) := by
      dsimp [a]
      rw [Nat.cast_sub hnM, ZMod.natCast_self, zero_sub]
    refine ⟨(a, n + t), ⟨?_, ?_⟩, ?_⟩
    · change a + (n + t) = t
      rw [hcast, neg_add_cancel_left]
    · change binDigitSum a.val + binDigitSum ((n : ZMod M) + t).val ≤ k - 1
      rw [ha]
      have h := weight_complement k n hn
      dsimp [M]
      omega
    · change M - a.val = n
      rw [ha]
      omega

noncomputable section

open MvPolynomial

/- The cyclic transfer matrix. Its rows and columns are the incoming and outgoing carries.
The monomials u and v mark weight changes of +1 and -1. -/
private abbrev P := MvPolynomial Bool ℤ

private abbrev Mat := Matrix (Fin 2) (Fin 2) P

private abbrev u : P := X true

private abbrev v : P := X false

private abbrev s : P := u + v - 1

private def letter : Bool → Mat
  | true => !![u, v; 0, 1]
  | false => !![1, 0; u, v]

private def mat (w : List Bool) : Mat := (w.map letter).prod

private theorem mat_append (w v' : List Bool) : mat (w ++ v') = mat w * mat v' := by
  simp [mat]

-- Cusick’s six polynomial states, in the order H, α, β, γ, δ, det. Keeping their
-- recurrences subtraction-free gives coefficientwise nonnegativity for every prefix.
private structure States where
  h : P
  α : P
  β : P
  γ : P
  δ : P
  d : P

private def initial : States := ⟨0, 0, 0, 0, 0, 1⟩

private def appendBit (p : States) : Bool → States
  | true => ⟨p.h + p.γ, u * p.α, p.β + v * p.α + p.d, u * p.γ, p.δ + v * p.γ, u * p.d⟩
  | false => ⟨p.h + p.β, p.α + u * p.β, v * p.β, p.γ + p.d + u * p.δ, v * p.δ, v * p.d⟩

private def states (w : List Bool) : States := w.foldl appendBit initial

private theorem states_append_singleton (w : List Bool) (b : Bool) :
    states (w ++ [b]) = appendBit (states w) b := by simp [states]

-- Recover the four entries of the word matrix from the six states. Appending a bit
-- verifies these identities and the trace factorization without polynomial division.
private def matrixFrom (p : States) : Mat :=
  !![p.d + v * p.α + (1 - v) * p.γ, v * p.β + (1 - v) * p.δ;
     (1 - u) * p.α + u * p.γ, p.d + (1 - u) * p.β + u * p.δ]

private theorem matrix_step (p : States) (b : Bool) :
    matrixFrom (appendBit p b) = matrixFrom p * letter b := by
  ext i j : 1
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [appendBit, matrixFrom, letter, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem matrix_eq (w : List Bool) : mat w = matrixFrom (states w) := by
  induction w using List.reverseRecOn with
  | nil => simp [mat, states, initial, matrixFrom, Matrix.one_fin_two]
  | append_singleton w b ih =>
    rw [mat_append, states_append_singleton, matrix_step, ih]
    simp [mat]

private theorem trace_step (p : States) (b : Bool) :
    (matrixFrom (appendBit p b)).trace - (appendBit p b).d =
      (matrixFrom p).trace - p.d + s * ((appendBit p b).h - p.h) := by
  cases b <;> simp [matrixFrom, appendBit, Matrix.trace_fin_two_of] <;> ring

private theorem trace_word (w : List Bool) :
    (mat w).trace - (states w).d = 1 + s * (states w).h := by
  rw [matrix_eq]
  induction w using List.reverseRecOn with
  | nil => simp [states, initial, matrixFrom, Matrix.trace_fin_two_of]
  | append_singleton w b ih =>
    rw [states_append_singleton, trace_step, ih]
    ring

private def CoeffsNonneg (p : P) : Prop := ∀ m, 0 ≤ p.coeff m

private theorem good_add {p q : P} (hp : CoeffsNonneg p) (hq : CoeffsNonneg q) :
    CoeffsNonneg (p + q) := by
  intro m
  simpa using add_nonneg (hp m) (hq m)

private theorem good_X_mul (i : Bool) {p : P} (hp : CoeffsNonneg p) : CoeffsNonneg (X i * p) := by
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split
  · apply hp
  · rfl

private theorem states_good (w : List Bool) :
    let p := states w
    CoeffsNonneg p.h ∧ CoeffsNonneg p.α ∧ CoeffsNonneg p.β ∧
      CoeffsNonneg p.γ ∧ CoeffsNonneg p.δ ∧ CoeffsNonneg p.d := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [states, List.foldl_nil, initial, CoeffsNonneg]
    simp [MvPolynomial.coeff_one, apply_ite]
  | append_singleton w b ih =>
    rcases ih with ⟨hh, ha, hb, hg, he, hd⟩
    rw [states_append_singleton]
    cases b with
    | true => exact ⟨good_add hh hg, good_X_mul _ ha, good_add (good_add hb (good_X_mul _ ha)) hd,
        good_X_mul _ hg, good_add he (good_X_mul _ hg), good_X_mul _ hd⟩
    | false => exact ⟨good_add hh hb, good_add ha (good_X_mul _ hb), good_X_mul _ hb,
        good_add (good_add hg hd) (good_X_mul _ he), good_X_mul _ he, good_X_mul _ hd⟩

private def detWord (w : List Bool) : P := (w.map (X (R := ℤ))).prod

private theorem det_append (w v' : List Bool) : detWord (w ++ v') = detWord w * detWord v' := by
  simp [detWord]

private theorem det_eq (w : List Bool) : detWord w = (states w).d := by
  induction w using List.reverseRecOn with
  | nil => simp [detWord, states, initial]
  | append_singleton w b ih =>
    rw [det_append, states_append_singleton, ih]
    cases b <;> simp [detWord, appendBit, mul_comm]

/- The differential decomposition. For dir = true this is the Euler derivation minus
the u-partial derivative. Choosing false gives the corresponding v-derivation. -/
private def wordDeriv (dir : Bool) (p : P) : P :=
  u * pderiv true p + v * pderiv false p - pderiv dir p

private theorem dd_add (d : Bool) (x y : P) :
    wordDeriv d (x + y) = wordDeriv d x + wordDeriv d y := by
  simp [wordDeriv, mul_add]
  ring

private theorem dd_sub (d : Bool) (x y : P) :
    wordDeriv d (x - y) = wordDeriv d x - wordDeriv d y := by
  simp [wordDeriv, mul_sub]
  ring

private theorem dd_mul (d : Bool) (x y : P) :
    wordDeriv d (x * y) = wordDeriv d x * y + x * wordDeriv d y := by
  simp [wordDeriv]
  ring

private theorem dd_zero (d : Bool) : wordDeriv d 0 = 0 := by simp [wordDeriv]

private theorem dd_one (d : Bool) : wordDeriv d 1 = 0 := by simp [wordDeriv]

private theorem dd_s (d : Bool) : wordDeriv d s = s := by
  cases d <;> simp [s, wordDeriv, u, v]

private theorem dd_mat_mul (d : Bool) (a b : Mat) :
    (a * b).map (wordDeriv d) = a.map (wordDeriv d) * b + a * b.map (wordDeriv d) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, dd_add, dd_mul]
  ring

private theorem dd_trace (d : Bool) (a : Mat) :
    wordDeriv d a.trace = (a.map (wordDeriv d)).trace := by
  simp [Matrix.trace_fin_two, dd_add]

private theorem local_quotient (dir b : Bool) (w : List Bool) :
    ∃ q : P, CoeffsNonneg q ∧
      ((letter b).map (wordDeriv dir) * mat w).trace - wordDeriv dir (X b) * detWord w = s * q := by
  let p := states w
  refine ⟨if dir then (if b then p.γ else p.δ) else (if b then p.α else p.β), ?_, ?_⟩
  · obtain ⟨_, ha, hb, hg, he, _⟩ := states_good w
    cases dir <;> cases b <;> assumption
  · rw [matrix_eq, det_eq]
    cases dir <;> cases b <;>
      simp [p, letter, matrixFrom, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        wordDeriv, u, v, s] <;> ring

-- Differentiate the prefix w and leave post fixed. Cyclicity puts the differentiated
-- factor first, so that each product-rule term has the local quotient just computed.
private theorem deriv_factor (dir : Bool) (w post : List Bool) :
    ∃ q : P, CoeffsNonneg q ∧
      ((mat w).map (wordDeriv dir) * mat post).trace -
        wordDeriv dir (detWord w) * detWord post = s * q := by
  induction w using List.reverseRecOn generalizing post with
  | nil =>
    refine ⟨0, fun m => by simp, ?_⟩
    have hz : (1 : Mat).map (wordDeriv dir) = 0 := by
      ext i j
      by_cases he : i = j <;> simp [he, dd_one, dd_zero]
    simp [mat, detWord, hz, dd_one]
  | append_singleton w b ih =>
    obtain ⟨q, hq, eq⟩ := ih ([b] ++ post)
    obtain ⟨r, hr, er⟩ := local_quotient dir b (post ++ w)
    refine ⟨q + r, good_add hq hr, ?_⟩
    have hm : mat [b] = letter b := by simp [mat]
    have hd : detWord [b] = X b := by simp [detWord]
    simp only [mat_append, det_append, hm, hd] at eq er ⊢
    rw [dd_mat_mul, dd_mul, add_mul, Matrix.trace_add, Matrix.mul_assoc,
      Matrix.mul_assoc (mat w), Matrix.trace_mul_comm (mat w), Matrix.mul_assoc]
    linear_combination eq + er

private theorem H_deriv_good (dir : Bool) (w : List Bool) :
    CoeffsNonneg ((states w).h + wordDeriv dir (states w).h) := by
  obtain ⟨q, hq, eq⟩ := deriv_factor dir w []
  have h := congrArg (wordDeriv dir) (trace_word w)
  rw [dd_sub, dd_trace, dd_add, dd_one, zero_add, dd_mul, dd_s, ← det_eq] at h
  simp only [mat, detWord, List.map_nil, List.prod_nil, mul_one] at eq
  change ((mat w).map (wordDeriv dir)).trace - wordDeriv dir (detWord w) = s * q at eq
  have hs : s ≠ 0 := by
    intro hz
    have h0 := congrArg (MvPolynomial.constantCoeff (R := ℤ)) hz
    norm_num [s, u, v] at h0
  have hh : (states w).h + wordDeriv dir (states w).h = q := by
    apply mul_left_cancel₀ hs
    rw [mul_add, ← h, eq]
  rwa [hh]

private def ij (i j : ℕ) : Bool →₀ ℕ := Finsupp.single true i + Finsupp.single false j

@[simp] private theorem ij_true (i j : ℕ) : ij i j true = i := by simp [ij]

@[simp] private theorem ij_false (i j : ℕ) : ij i j false = j := by simp [ij]

private theorem ij_eta (m : Bool →₀ ℕ) : ij (m true) (m false) = m := by
  ext b
  cases b <;> simp

private theorem ij_incr (b : Bool) (i j : ℕ) : Finsupp.single b 1 + ij i j =
    if b then ij (i + 1) j else ij i (j + 1) := by
  ext r
  cases r <;> cases b <;> simp [add_comm]

private theorem ij_decr (b : Bool) (i j : ℕ) : ij i j - Finsupp.single b 1 =
    if b then ij (i - 1) j else ij i (j - 1) := by
  ext r
  cases r <;> cases b <;> simp

private abbrev mono (i j : ℕ) (c : ℤ) : P := monomial (ij i j) c

private theorem X_mono (b : Bool) (i j : ℕ) (c : ℤ) :
    X b * mono i j c = if b then mono (i + 1) j c else mono i (j + 1) c := by
  rw [X, mono, monomial_mul_monomial, one_mul, ij_incr]
  cases b <;> rfl

-- Extend weights on bidegrees additively to polynomials over the integers.
private def moment (f : ℕ → ℕ → ℚ) : P →+ ℚ :=
  (Finsupp.liftAddHom (fun (m : Bool →₀ ℕ) => zmultiplesHom ℚ (f (m true) (m false)))).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

private theorem moment_mono (f : ℕ → ℕ → ℚ) (i j : ℕ) (c : ℤ) :
    moment f (mono i j c) = c * f i j := by
  change (mono i j c).coeff.sum _ = _
  rw [MvPolynomial.sum_monomial_eq (by simp)]
  simp [zsmul_eq_mul]

private abbrev half : ℚ := 1 / 2

-- Under u = x/2 and v = 1/(2x), take the mass of negative powers after shifting by d.
private def negativeWeight (d : ℤ) (i j : ℕ) : ℚ := if d + i < j then half ^ (i + j) else 0

-- The differential correction to the median is supported on the adjacent diagonal j = i + 1.
private def boundaryWeight (i j : ℕ) : ℚ := if j = i + 1 then half ^ (i + j + 2) / j else 0

private theorem lam_nonneg (i j : ℕ) : 0 ≤ boundaryWeight i j := by
  unfold boundaryWeight
  split
  · exact div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  · rfl

private theorem moment_ge {p : P} (hg : CoeffsNonneg p) {f : ℕ → ℕ → ℚ}
    (hf : ∀ i j, 0 ≤ f i j) :
    ∀ m, (p.coeff m : ℚ) * f (m true) (m false) ≤ moment f p := by
  intro m
  change _ ≤ ∑ x ∈ p.support, (p.coeff x : ℤ) • f (x true) (x false)
  simp only [zsmul_eq_mul]
  have hp (x : Bool →₀ ℕ) : 0 ≤ (p.coeff x : ℚ) * f (x true) (x false) :=
    mul_nonneg (by exact_mod_cast hg x) (hf ..)
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun x _ => hp x) hm
  · have h := MvPolynomial.notMem_support_iff.mp hm
    simp only [h, Int.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun x _ => hp x)

-- In (u + v - 1)H, terms away from the diagonal and its neighbor cancel in the negative
-- mass. Checking a monomial gives the median identity by linearity.
private theorem median_mono (i j : ℕ) (c : ℤ) :
    moment (negativeWeight 0) (s * mono i j c) =
      ((MvPolynomial.constantCoeff (mono i j c) : ℤ) : ℚ) / 2 -
      moment boundaryWeight (mono i j c + wordDeriv true (mono i j c)) := by
  have he : (ij i j = 0) ↔ i = 0 ∧ j = 0 := by
    constructor
    · intro h
      exact ⟨by simpa using congr($h true), by simpa using congr($h false)⟩
    · rintro ⟨rfl, rfl⟩
      simp [ij]
  have pd : pderiv true (mono i j c) = mono (i - 1) j (c * (i : ℤ)) := by
    simp [mono, pderiv_monomial, ij_decr]
  have eu (b : Bool) : X b * pderiv b (mono i j c) = (ij i j b) • mono i j c :=
    X_mul_pderiv_monomial
  rw [show s * mono i j c = u * mono i j c + v * mono i j c - mono i j c by ring,
    X_mono, X_mono]
  rw [wordDeriv, eu, eu, pd]
  simp only [Bool.false_eq_true, ↓reduceIte, map_add, map_sub, map_nsmul, ij_true, ij_false,
    moment_mono, MvPolynomial.constantCoeff_monomial, he, Int.cast_mul, Int.cast_natCast]
  simp only [negativeWeight, zero_add, Nat.cast_lt, boundaryWeight, nsmul_eq_mul, half]
  cases i with
  | zero =>
    cases j with
    | zero => norm_num; ring
    | succ j =>
      cases j with
      | zero => norm_num; ring
      | succ j => simp [pow_add]; ring
  | succ i =>
    have hi : (i : ℚ) + 1 ≠ 0 := by positivity
    have hi' : (i : ℚ) + 1 + 1 ≠ 0 := by positivity
    by_cases h : j = i + 1
    · subst j
      simp [pow_add]
      field_simp
    · by_cases h' : j = i + 1 + 1
      · subst j
        simp [pow_add]
        field_simp
        ring
      · by_cases hl : j < i + 1
        · simp (disch := omega) [ite_eq_right]
        · simp (disch := omega) [ite_eq_left, pow_add]
          ring

private theorem median (p : P) : moment (negativeWeight 0) (s * p) =
    ((MvPolynomial.constantCoeff p : ℤ) : ℚ) / 2 -
      moment boundaryWeight (p + wordDeriv true p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add, Int.cast_add, dd_add] at *
    linarith
  | monomial m c => simpa only [mono, ij_eta] using median_mono (m true) (m false) c

private theorem euler_coeff (p : P) (b : Bool) (e : Bool →₀ ℕ) :
    (X b * pderiv b p).coeff e = (e b : ℤ) * p.coeff e := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial m c =>
    rw [X_mul_pderiv_monomial, MvPolynomial.smul_monomial]
    simp only [nsmul_eq_mul, coeff_monomial]
    split
    · next h => rw [h]
    · simp

private theorem marked_coeff (p : P) (dir : Bool) (m : Bool →₀ ℕ) :
    (p + wordDeriv dir p).coeff m = ((m true : ℤ) + m false + 1) * p.coeff m -
      ((m dir : ℤ) + 1) * p.coeff (Finsupp.single dir 1 + m) := by
  simp [wordDeriv, euler_coeff, coeff_pderiv, add_comm m]
  ring

private theorem coeff_predecessor (w : List Bool) (i j : ℕ)
    (h : 0 < (states w).h.coeff (ij i (j + 1))) : 0 < (states w).h.coeff (ij i j) := by
  have h' := H_deriv_good false w (ij i j)
  rw [marked_coeff, ij_incr] at h'
  simp only [ij_true, ij_false, Bool.false_eq_true, ↓reduceIte] at h'
  by_contra! hle
  have h₁ : ((i : ℤ) + j + 1) * (states w).h.coeff (ij i j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
  have h₂ : 0 < ((j : ℤ) + 1) * (states w).h.coeff (ij i (j + 1)) :=
    mul_pos (by positivity) h
  omega

private theorem coeff_down (w : List Bool) {i j l : ℕ} (hle : j ≤ l)
    (h : 0 < (states w).h.coeff (ij i l)) : 0 < (states w).h.coeff (ij i j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction n with
  | zero => exact h
  | succ n ih => exact ih (by omega) (coeff_predecessor w i (j + n) h)

-- No monomial in p has u-degree at least n. This includes the zero polynomial when n = 0.
private def VanishesFrom (p : P) (n : ℕ) : Prop := ∀ i j, n ≤ i → p.coeff (ij i j) = 0

private theorem cut_add {p q : P} {n : ℕ} (hp : VanishesFrom p n) (hq : VanishesFrom q n) :
    VanishesFrom (p + q) n := by
  intro i j hi
  simp [hp i j hi, hq i j hi]

private theorem cut_weaken {p : P} {n : ℕ} (hp : VanishesFrom p n) : VanishesFrom p (n + 1) :=
  fun i j hi => hp i j (by omega)

private theorem cut_u {p : P} {n : ℕ} (hp : VanishesFrom p n) : VanishesFrom (u * p) (n + 1) := by
  rintro (_ | i) j hi
  · omega
  · rw [show ij (i + 1) j = Finsupp.single true 1 + ij i j by rw [ij_incr]; rfl, coeff_X_mul]
    exact hp i j (by omega)

private theorem cut_v {p : P} {n : ℕ} (hp : VanishesFrom p n) : VanishesFrom (v * p) n := by
  rintro i (_ | j) hi
  · simp [v, coeff_X_mul', Finsupp.mem_support_iff]
  · rw [show ij i (j + 1) = Finsupp.single false 1 + ij i j by rw [ij_incr]; rfl, coeff_X_mul]
    exact hp i j hi

private theorem state_cuts (w : List Bool) :
    let p := states w
    let r := w.count true
    VanishesFrom p.h r ∧ VanishesFrom p.α (r + 1) ∧ VanishesFrom p.β r ∧
      VanishesFrom p.γ (r + 1) ∧ VanishesFrom p.δ r ∧ VanishesFrom p.d (r + 1) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [states, List.foldl_nil, initial, List.count_nil]
    have hz (n : ℕ) : VanishesFrom 0 n := by intro i j h; simp
    refine ⟨hz _, hz _, hz _, hz _, hz _, ?_⟩
    intro i j hi
    simp only [MvPolynomial.coeff_one, ite_eq_right_iff]
    intro he
    have := congr($he true)
    simp at this
    omega
  | append_singleton w b ih =>
    rcases ih with ⟨hh, ha, hb, hg, he, hd⟩
    simp only [states_append_singleton, List.count_append]
    cases b with
    | true =>
      simp only [List.count_singleton_self]
      exact ⟨cut_add (cut_weaken hh) hg, cut_u ha,
        cut_add (cut_add (cut_weaken hb) (cut_v ha)) hd, cut_u hg,
        cut_add (cut_weaken he) (cut_v hg), cut_u hd⟩
    | false =>
      simp only [List.count_singleton]
      exact ⟨cut_add hh hb, cut_add ha (cut_u hb), cut_v hb,
        cut_add (cut_add hg hd) (cut_u he), cut_v he, cut_v hd⟩

private theorem det_mono (w : List Bool) : detWord w = mono (w.count true) (w.count false) 1 := by
  induction w with
  | nil => simp [detWord, mono, ij]
  | cons b w ih =>
    have hm : detWord (b :: w) = X b * detWord w := by simp [detWord]
    rw [hm, ih, X_mono]
    cases b <;> simp

-- After a rotation, the last two bits differ. Their updates put the entire determinant
-- monomial of the prefix into H, with positive coefficient.
private theorem corner (pre : List Bool) (b : Bool) :
    0 < (states (pre ++ [b, !b])).h.coeff (ij (pre.count true) (pre.count false)) := by
  let m := ij (pre.count true) (pre.count false)
  change 0 < (states _).h.coeff m
  have hd : (states pre).d.coeff m = 1 := by
    rw [← det_eq, det_mono]
    simp [mono, m, coeff_monomial]
  obtain ⟨hh, ha, hb, hg, he, _⟩ := states_good pre
  have huv := good_X_mul false ha m
  have hvu := good_X_mul true he m
  have h₁ := hh m
  have h₂ := hb m
  have h₃ := hg m
  rw [show pre ++ [b, !b] = (pre ++ [b]) ++ [!b] by simp, states_append_singleton,
    states_append_singleton]
  cases b <;> simp [appendBit, hd, u, v] <;> omega

private theorem split_word (w : List Bool) (ht : true ∈ w) (hf : false ∈ w) :
    ∃ xs ys b, w = xs ++ b :: (!b) :: ys := by
  induction w with
  | nil => cases ht
  | cons b w ih =>
    cases w with
    | nil => cases b <;> simp_all
    | cons c tail =>
      by_cases h : c = !b
      · exact ⟨[], tail, b, by simp [h]⟩
      have h' : b = c := by cases b <;> cases c <;> simp_all
      subst c
      obtain ⟨xs, ys, b', hw⟩ := ih (by simpa [or_assoc] using ht) (by simpa [or_assoc] using hf)
      exact ⟨b :: xs, ys, b', congrArg (b :: ·) hw⟩

private theorem mat_cons (b : Bool) (w : List Bool) : mat (b :: w) = letter b * mat w := by
  simp [mat]

private theorem mat_good (w : List Bool) (i j : Fin 2) : CoeffsNonneg (mat w i j) := by
  induction w generalizing i j with
  | nil =>
    by_cases h : i = j
    · simpa [mat, h, states, initial] using (states_good []).2.2.2.2.2
    · simp [mat, Matrix.one_apply_ne h, CoeffsNonneg]
  | cons b w ih =>
    rw [mat_cons]
    have h := good_add (good_X_mul true (ih 0 j)) (good_X_mul false (ih 1 j))
    cases b <;> fin_cases i
    · simpa [letter, Matrix.mul_apply, Fin.sum_univ_two] using ih 0 j
    · simpa [letter, Matrix.mul_apply, Fin.sum_univ_two] using h
    · simpa [letter, Matrix.mul_apply, Fin.sum_univ_two] using h
    · simpa [letter, Matrix.mul_apply, Fin.sum_univ_two] using ih 1 j

private theorem h0_le (b : Bool) (tail : List Bool) :
    MvPolynomial.constantCoeff (states (b :: tail)).h ≤ (1 : ℤ) := by
  let w := b :: tail
  have hdet : MvPolynomial.constantCoeff (detWord w) = 0 := by simp [w, detWord]
  have h := congrArg (MvPolynomial.constantCoeff (R := ℤ)) (trace_word w)
  have hnon := good_add (mat_good w 0 0) (mat_good w 1 1) 0
  change 0 ≤ MvPolynomial.constantCoeff (mat w 0 0 + mat w 1 1) at hnon
  simp only [← det_eq, map_sub, map_add, map_mul, Matrix.trace_fin_two, map_one, u, v,
    MvPolynomial.constantCoeff_X, hdet, zero_add, sub_zero, zero_sub, neg_one_mul] at h
  change MvPolynomial.constantCoeff (states w).h ≤ 1
  rw [map_add] at hnon
  omega

private theorem moment_nonneg {p : P} (hg : CoeffsNonneg p) {f : ℕ → ℕ → ℚ}
    (hf : ∀ i j, 0 ≤ f i j) :
    0 ≤ moment f p := by
  exact le_trans (mul_nonneg (by exact_mod_cast hg 0) (hf _ _)) (moment_ge hg hf 0)

-- When ones are in the minority the determinant also contributes negative mass. The
-- positive corner coefficient, propagated down its column, pays for this extra term.
private theorem trace_bound_pair (pre : List Bool) (b : Bool) :
    moment (negativeWeight 0) (mat (pre ++ [b, !b])).trace ≤ 1 / 2 := by
  let w := pre ++ [b, !b]
  let i := pre.count true
  let j := pre.count false
  have hr : w.count true = i + 1 := by cases b <;> simp [w, i]
  have hz : w.count false = j + 1 := by cases b <;> simp [w, j]
  have h0 : MvPolynomial.constantCoeff (states w).h ≤ (1 : ℤ) := by
    obtain ⟨c, v', h⟩ := List.exists_cons_of_ne_nil (show w ≠ [] by simp [w])
    rw [h]
    apply h0_le
  have h0' : ((MvPolynomial.constantCoeff (states w).h : ℤ) : ℚ) ≤ 1 := by exact_mod_cast h0
  have htr := trace_word w
  have ht : (mat w).trace = 1 + s * (states w).h + detWord w := by
    rw [← det_eq] at htr
    linear_combination htr
  have hone : (1 : P) = mono 0 0 1 := by simp [mono, ij]
  change moment (negativeWeight 0) (mat w).trace ≤ _
  rw [ht, det_mono, hr, hz, map_add, map_add, median, hone, moment_mono, moment_mono]
  simp only [Int.cast_one, one_mul]
  have hconst : negativeWeight 0 0 0 = 0 := by simp [negativeWeight]
  rw [hconst, zero_add]
  have hg := H_deriv_good true w
  by_cases hij : i < j
  · have hpos := coeff_down w (i := i) (j := i + 1) (l := j) hij (corner pre b)
    have hcut := (state_cuts w).1 (i + 1) (i + 1) (by omega)
    have hcoef := marked_coeff (states w).h true (ij i (i + 1))
    rw [ij_incr, ite_eq_left rfl, hcut, mul_zero, sub_zero, ij_true, ij_false] at hcoef
    have hl := moment_ge hg lam_nonneg (ij i (i + 1))
    rw [hcoef, ij_true, ij_false] at hl
    simp only [boundaryWeight, ↓reduceIte, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Nat.cast_succ, Int.cast_one] at hl
    have he (x : ℚ) : ((i : ℚ) + (i + 1) + 1) * x * (half ^ (i + (i + 1) + 2) / (i + 1)) =
        x * half ^ (i + i + 2) := by
      have hp : (i : ℚ) + 1 ≠ 0 := by positivity
      simp only [pow_add]
      field_simp
      ring
    rw [he] at hl
    have hx : (1 : ℚ) ≤ (states w).h.coeff (ij i (i + 1)) := by exact_mod_cast hpos
    have hpow : negativeWeight 0 (i + 1) (j + 1) ≤ half ^ (i + i + 2) := by
      simp only [negativeWeight, zero_add, Nat.cast_lt, ite_eq_left (by omega : i + 1 < j + 1)]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hl' := mul_le_mul_of_nonneg_right hx (show 0 ≤ half ^ (i + i + 2) by positivity)
    linarith
  · have hneg : negativeWeight 0 (i + 1) (j + 1) = 0 := by simp [negativeWeight, hij]
    rw [hneg, add_zero]
    linarith [moment_nonneg hg lam_nonneg]

private theorem trace_bound (w : List Bool) (ht : true ∈ w) (hf : false ∈ w) :
    moment (negativeWeight 0) (mat w).trace ≤ 1 / 2 := by
  obtain ⟨xs, ys, b, rfl⟩ := split_word w ht hf
  have h := trace_bound_pair (ys ++ xs) b
  have he : (mat (xs ++ b :: (!b) :: ys)).trace = (mat ((ys ++ xs) ++ [b, !b])).trace := by
    rw [show xs ++ b :: (!b) :: ys = (xs ++ [b, !b]) ++ ys by simp,
      mat_append, Matrix.trace_mul_comm]
    simp only [mat_append, Matrix.mul_assoc]
  rwa [he]

/- The transfer identity. Words are read least significant bit first. The linear
transfer counts choices of input with prescribed carries at the two ends. -/
private def wordValue : List Bool → ℕ
  | [] => 0
  | b :: w => 2 * wordValue w + b.toNat

private def digitWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => decide (n % 2 = 1) :: digitWord k (n / 2)

private theorem word_length (k n : ℕ) : (digitWord k n).length = k := by
  induction k generalizing n <;> simp_all [digitWord]

private theorem value_digits (k n : ℕ) (hn : n < 2 ^ k) : wordValue (digitWord k n) = n := by
  induction k generalizing n with
  | zero => simp_all [digitWord, wordValue]
  | succ k ih =>
    simp only [digitWord, wordValue]
    rw [ih _ (by rw [pow_succ] at hn; omega)]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

private theorem value_endpoints (w : List Bool) :
    (true ∉ w → wordValue w = 0) ∧ (false ∉ w → wordValue w + 1 = 2 ^ w.length) := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih =>
    cases b with
    | false => simpa [wordValue] using ih.1
    | true =>
      suffices ∀ h : false ∉ w, 2 * wordValue w + 1 + 1 = 2 ^ w.length * 2 by
        simpa [wordValue, pow_succ] using this
      intro h
      have := ih.2 h
      omega

private theorem moment_shift (d : ℤ) (b : Bool) (p : P) :
    moment (negativeWeight d) (X b * p) =
      half * moment (negativeWeight (if b then d + 1 else d - 1)) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
  | monomial m c =>
    rw [← ij_eta m]
    change moment (negativeWeight d) (X b * mono _ _ _) = half * moment _ (mono _ _ _)
    rw [X_mono]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, moment_mono, negativeWeight,
      Nat.cast_add, Nat.cast_one, pow_add, pow_one] <;> split_ifs <;> first | omega | ring

-- A block of width k has N = 2 ^ k. For input n and entering carry c, the output
-- with leaving carry e must be n + t + c - N * e in [0, N).
private def carryTerm (N t c e n : ℕ) (d : ℤ) : ℚ :=
  if N * e ≤ n + t + c ∧ n + t + c < N * e + N ∧
      d + binDigitSum (n + t + c - N * e) < binDigitSum n then 1 else 0

private theorem weight_bit (n b : ℕ) (hb : b < 2) :
    binDigitSum (2 * n + b) = binDigitSum n + b := by
  interval_cases b <;> simp

private theorem carry_bit (N t a b c e n : ℕ) (ha : a < 2) (d : ℤ) :
    carryTerm (2 * N) (2 * t + b) c e (2 * n + a) d =
      carryTerm N t ((a + b + c) / 2) e n (d + ((a + b + c) % 2 : ℕ) - a) := by
  simp only [carryTerm, mul_assoc, weight_bit n a ha]
  have hl : 2 * (N * e) ≤ 2 * n + a + (2 * t + b) + c ↔ N * e ≤ n + t + (a + b + c) / 2 := by omega
  have hu : 2 * n + a + (2 * t + b) + c < 2 * (N * e) + 2 * N ↔
      n + t + (a + b + c) / 2 < N * e + N := by omega
  simp only [hl, hu]
  by_cases h : N * e ≤ n + t + (a + b + c) / 2
  · have hs : 2 * n + a + (2 * t + b) + c - 2 * (N * e) =
        2 * (n + t + (a + b + c) / 2 - N * e) + (a + b + c) % 2 := by omega
    rw [hs, weight_bit _ _ (Nat.mod_lt _ (by decide))]
    push_cast
    split_ifs <;> first | rfl | omega
  · simp [h]

private theorem sum_bits (f : ℕ → ℚ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), f n =
      (∑ n ∈ Finset.range N, f (2 * n)) + ∑ n ∈ Finset.range N, f (2 * n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ (fun n => f (2 * n + 1))]
    ring

private def carrySum (N t c e : ℕ) (d : ℤ) : ℚ :=
  ∑ n ∈ Finset.range N, carryTerm N t c e n d

private theorem carry_step (N t b c e : ℕ) (d : ℤ) :
    carrySum (2 * N) (2 * t + b) c e d =
      carrySum N t ((b + c) / 2) e (d + ((b + c) % 2 : ℕ)) +
      carrySum N t ((1 + b + c) / 2) e (d + ((1 + b + c) % 2 : ℕ) - 1) := by
  unfold carrySum
  rw [sum_bits]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_zero, sub_zero] using
      carry_bit N t 0 b c e n (by decide) d
  · apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.cast_one] using carry_bit N t 1 b c e n (by decide) d

private theorem moment_one (d : ℤ) : moment (negativeWeight d) 1 = if d < 0 then 1 else 0 := by
  have h : (1 : P) = mono 0 0 1 := by simp [mono, ij]
  rw [h, moment_mono]
  simp [negativeWeight]

private theorem linear_transfer (w : List Bool) (c e : Fin 2) (d : ℤ) :
    (2 : ℚ) ^ w.length * moment (negativeWeight d) (mat w c e) =
      carrySum (2 ^ w.length) (wordValue w) c.val e.val d := by
  induction w generalizing c e d with
  | nil =>
    have hz (c e : ℕ) : carrySum 1 0 c e d = carryTerm 1 0 c e 0 d := by
      rw [carrySum, Finset.sum_range_one]
    fin_cases c <;> fin_cases e <;> simp [mat, wordValue, hz, carryTerm, moment_one]
  | cons b w ih =>
    simp only [List.length_cons, pow_succ', wordValue, carry_step, mat_cons]
    have h0 (d' : ℤ) : (2 : ℚ) ^ w.length * moment (negativeWeight d') (mat w 0 e) =
        carrySum (2 ^ w.length) (wordValue w) 0 e.val d' := ih 0 e d'
    have h1 (d' : ℤ) : (2 : ℚ) ^ w.length * moment (negativeWeight d') (mat w 1 e) =
        carrySum (2 ^ w.length) (wordValue w) 1 e.val d' := ih 1 e d'
    cases b <;> fin_cases c <;>
      norm_num [letter, Matrix.mul_apply, Fin.sum_univ_two, moment_shift]
    all_goals
      simp only [← h0, ← h1]
      ring

-- Taking the trace identifies the entering and leaving carries. At n + t = 2 ^ k - 1
-- both carries close, but the all-ones output cannot contribute a strict weight drop.
private theorem cyclic_term (k t n : ℕ) (ht : t < 2 ^ k - 1) (hn : n < 2 ^ k) :
    carryTerm (2 ^ k) t 0 0 n 0 + carryTerm (2 ^ k) t 1 1 n 0 =
      if binDigitSum ((n + t) % (2 ^ k - 1)) < binDigitSum n then 1 else 0 := by
  let M := 2 ^ k - 1
  change carryTerm (2 ^ k) t 0 0 n 0 + carryTerm (2 ^ k) t 1 1 n 0 =
    if binDigitSum ((n + t) % M) < binDigitSum n then 1 else 0
  have hN : 2 ^ k = M + 1 := by dsimp [M]; have := Nat.two_pow_pos k; omega
  have htop : binDigitSum M = k := by
    simpa [M] using weight_complement k 0 (Nat.two_pow_pos k)
  have hwt := weight_complement k n hn
  have hnwt : binDigitSum n ≤ k := by omega
  simp only [carryTerm, mul_zero, mul_one, Nat.zero_le, true_and, Nat.add_zero,
    Nat.sub_zero, zero_add, Nat.cast_lt]
  by_cases hlt : n + t < M
  · rw [Nat.mod_eq_of_lt hlt]
    simp [show n + t < 2 ^ k by omega, show ¬ 2 ^ k ≤ n + t + 1 by omega]
  · have hM : t < M := ht
    have hrest : n + t - M < M := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hrest]
    have hs : n + t + 1 - 2 ^ k = n + t - M := by omega
    rw [hs]
    have hno : ¬ (n + t < 2 ^ k ∧ binDigitSum (n + t) < binDigitSum n) := by
      rintro ⟨hlt', h⟩
      rw [show n + t = M by omega, htop] at h
      omega
    simp [hno, show 2 ^ k ≤ n + t + 1 by omega, show n + t + 1 < 2 ^ k + 2 ^ k by omega]

private theorem trace_counts (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) :
    let w := digitWord k t.val
    (2 : ℚ) ^ k * moment (negativeWeight 0) (mat w).trace =
      ({n : ℕ | n < 2 ^ k ∧
        binDigitSum ((n : ZMod (2 ^ k - 1)) + t).val < binDigitSum n}.ncard : ℚ) := by
  have hpow := Nat.lt_two_pow_self (n := k)
  have : NeZero (2 ^ k - 1) := ⟨by omega⟩
  have ht := t.val_lt
  let w := digitWord k t.val
  have hl : w.length = k := word_length ..
  have hv : wordValue w = t.val := value_digits _ _ (by omega)
  have hdiag (c : Fin 2) := linear_transfer w c c 0
  simp only [hl, hv] at hdiag
  let D := fun n : ℕ => binDigitSum ((n + t.val) % (2 ^ k - 1)) < binDigitSum n
  have he : {n : ℕ | n < 2 ^ k ∧ binDigitSum ((n : ZMod (2 ^ k - 1)) + t).val < binDigitSum n} =
      (↑((Finset.range (2 ^ k)).filter D) : Set ℕ) := by
    ext n
    simp [D, ZMod.val_add, ZMod.val_natCast, Nat.mod_add_mod]
  change (2 : ℚ) ^ k * moment (negativeWeight 0) (mat w).trace = _
  rw [he, Set.ncard_coe_finset, ← Finset.sum_boole, Matrix.trace_fin_two, map_add, mul_add,
    hdiag 0, hdiag 1]
  unfold carrySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact cyclic_term k t.val n ht (Finset.mem_range.mp hn)

/-- **Tu–Deng conjecture.** For every integer $k \ge 2$ and every nonzero residue $t$ modulo
$2^k - 1$, the number of pairs $(a, b)$ of residues modulo $2^k - 1$ with $a + b = t$ and
$w(a) + w(b) \le k - 1$ is at most $2^{k-1}$, where $w(a)$ is the binary digit sum of the
representative of $a$ in $\{0, 1, \dots, 2^k - 2\}$.

Source: T. W. Cusick, Proof of the Tu-Deng
Conjecture, arXiv:2608.14821 (2026), https://arxiv.org/abs/2608.14821. Moved from
`OpenConjectures/NumberTheory/TuDengConjecture`.
-/
theorem tuDengConjecture_holds : tuDengConjecture := by
  intro k hk t ht
  rw [pairs_eq_drops k hk t]
  have hpow := Nat.lt_two_pow_self (n := k)
  have : NeZero (2 ^ k - 1) := ⟨by omega⟩
  have hlt := t.val_lt
  have hnz : t.val ≠ 0 := by
    intro h
    apply ht
    rw [← ZMod.natCast_zmod_val t, h, Nat.cast_zero]
  let w := digitWord k t.val
  have hv : wordValue w = t.val := value_digits _ _ (by omega)
  have hl : w.length = k := word_length ..
  have he := value_endpoints w
  have ht' : true ∈ w := by
    by_contra h
    exact hnz (hv ▸ he.1 h)
  have hf' : false ∈ w := by
    by_contra h
    have he' := he.2 h
    rw [hl, hv] at he'
    omega
  have hb := mul_le_mul_of_nonneg_left (trace_bound w ht' hf') (show 0 ≤ (2 : ℚ) ^ k by positivity)
  have hfactor : (2 : ℚ) ^ k * (1 / 2) = 2 ^ (k - 1) := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
    ring
  rw [hfactor] at hb
  have hcount := trace_counts k hk t
  change (2 : ℚ) ^ k * moment (negativeWeight 0) (mat w).trace = _ at hcount
  rw [hcount] at hb
  exact_mod_cast hb

attribute [inherit_doc tuDengConjecture_holds] tuDengConjecture

end

end MathlibExt.NumberTheory.TuDengConjectureWanted
