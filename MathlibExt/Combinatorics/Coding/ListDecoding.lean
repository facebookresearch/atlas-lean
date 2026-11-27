/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingBall
public import Mathlib.Algebra.Order.Chebyshev
import Lean.Elab.Tactic.Omega

/-!
# List decoding: the Johnson bound and the counting converse

A code `C` of length `n` is *list decodable* from `e` errors with list size `L` when every
Hamming ball of radius `e` contains at most `L` codewords.

* `IsListDecodable C e L`: the definition (Guruswami, Rudra and Sudan, Definition 7.2.1, with the
  radius `ρn` written as an integer `e`).
* `johnson_bound` (**Johnson bound**, alphabet-free form): if every two distinct words of a list
  are at distance at least `d`, every word of the list is within distance `e` of a centre `y`,
  and `(n - e)² > n (n - d)`, then the list has at most
  `n (d - e) / ((n - e)² - n (n - d))` words; in particular at most `n · d`
  (`card_le_mul_of_johnson`, `isListDecodable_of_johnson`). The proof is the classical
  double-counting and Cauchy–Schwarz argument on agreements with `y`.
* `exists_mul_card_filter_ge`: for every code `C` some Hamming ball of radius `e` contains at
  least `|C| · Vol_q(n, e) / q ^ n` codewords. This averaging step is the proof of the converse
  half of the list-decoding capacity theorem.

## References

* S. M. Johnson, "A new upper bound for error-correcting codes", *IRE Transactions on
  Information Theory* 8 (1962), 203–207.
* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Definition 7.2.1, Theorems 7.3.1 and 7.3.3 (Section 7.3), and the proof of Theorem 7.4.2 (ii)
  (equations (7.12)–(7.17)).
* V. Guruswami, *List decoding of error-correcting codes*, Lecture Notes in Computer Science
  3282, Springer, 2004, Chapter 3.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.ListDecoding

open Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- **List-decodable code.** A code `C` of words of length `n` is list decodable from `e` errors
with list size `L` if every Hamming ball of radius `e` contains at most `L` codewords: for every
received word `y`, at most `L` codewords `c` satisfy `Δ(y, c) ≤ e` (Guruswami, Rudra and Sudan,
*Essential Coding Theory*, draft of August 26, 2025, Definition 7.2.1, where the radius is `ρn`
for a fraction `ρ`; here it is the integer `e`). -/
def IsListDecodable (C : Finset (Fin n → α)) (e L : ℕ) : Prop :=
  ∀ y : Fin n → α, (C.filter fun c => hammingDist y c ≤ e).card ≤ L

/-- **List decodability is monotone in the list size.** A code list decodable from `e` errors
with list size `L` is list decodable with every larger list size. -/
theorem IsListDecodable.mono {C : Finset (Fin n → α)} {e L L' : ℕ}
    (h : IsListDecodable C e L) (hL : L ≤ L') : IsListDecodable C e L' :=
  fun y => (h y).trans hL

/-- **Agreements of two words.** Two words of length `n` agree in `n - Δ(x, y)` coordinates. -/
theorem card_filter_eq (x y : Fin n → α) :
    (univ.filter fun j => x j = y j).card = n - hammingDist x y := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => x j = y j)
  rw [card_univ, Fintype.card_fin] at h
  have : hammingDist x y = (univ.filter fun j => ¬x j = y j).card := rfl
  omega

/-- The integer arithmetic closing the Johnson bound. With `A = ∑ⱼ mⱼ` and `B = ∑ⱼ mⱼ²`,
`L t ≤ A`, `A² ≤ n B`, `B ≤ A + L (L - 1) D` and `n D < t²`, `t ≤ n` give
`L (t² - n D) ≤ n (t - D)`. -/
private theorem johnson_arith {L A B n t D : ℤ} (hL : 0 ≤ L) (hn : 0 ≤ n) (ht : 0 ≤ t)
    (hD : 0 ≤ D) (htn : t ≤ n) (hLA : L * t ≤ A) (hCS : A ^ 2 ≤ n * B)
    (hB : B ≤ A + L * (L - 1) * D) (hJ : n * D < t ^ 2) :
    L * (t ^ 2 - n * D) ≤ n * (t - D) := by
  have htD : D < t := by
    by_contra h
    push Not at h
    nlinarith
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · subst hL0; nlinarith
  by_cases hcase : n ≤ A + L * t
  · -- `S ↦ S² - n S` is monotone beyond `n / 2`.
    have h1 : (L * t) ^ 2 - n * (L * t) ≤ A ^ 2 - n * A := by nlinarith
    have h2 : A ^ 2 - n * A ≤ n * (L * (L - 1) * D) := by nlinarith
    have h3 : L * (L * (t ^ 2 - n * D)) ≤ L * (n * (t - D)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hLpos
  · push Not at hcase
    have h2Lt : 2 * (L * t) < n := by linarith
    have h4 : 2 * (L * t ^ 2) ≤ n * t := by nlinarith
    have hL1 : 1 ≤ L := hLpos
    have hnD : 0 ≤ n * D := mul_nonneg hn hD
    have h5 : n * D ≤ L * (n * D) := by nlinarith
    have h6 : 0 ≤ n * t := mul_nonneg hn ht
    have e1 : L * (t ^ 2 - n * D) = L * t ^ 2 - L * (n * D) := by ring
    have e2 : n * (t - D) = n * t - n * D := by ring
    rw [e1, e2]
    linarith

/-- **Johnson bound** (alphabet-free form). Let `S` be a set of words of length `n` over a finite
alphabet, any two distinct at Hamming distance at least `d`, all within distance `e` of a word
`y`, where `e ≤ n`, `d ≤ n` and `n (n - d) < (n - e)²`. Then
`|S| · ((n - e)² - n (n - d)) ≤ n · ((n - e) - (n - d))`; under the hypotheses both differences
are positive (the natural-number subtractions do not truncate).

Equivalently, a code of minimum distance `d` has at most `n (d - e) / ((n - e)² - n (n - d))`
codewords in any ball of radius `e < n - √(n (n - d))`. This is the strict-inequality case of
Theorem 7.3.3 of Guruswami, Rudra and Sudan, *Essential Coding Theory* (draft of August 26,
2025), with an explicit list size. The proof double counts the pairs (codeword, coordinate) at
which a codeword agrees with `y` and applies Cauchy–Schwarz, as in the binary proof of Theorem
7.3.1 there. Source: S. M. Johnson, "A new upper bound for error-correcting codes", *IRE
Transactions on Information Theory* 8 (1962), 203–207. -/
theorem johnson_bound (S : Finset (Fin n → α)) (y : Fin n → α) {d e : ℕ} (hen : e ≤ n)
    (hdn : d ≤ n) (hdist : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hball : ∀ c ∈ S, hammingDist y c ≤ e) (hJ : n * (n - d) < (n - e) ^ 2) :
    S.card * ((n - e) ^ 2 - n * (n - d)) ≤ n * ((n - e) - (n - d)) := by
  classical
  -- `m j` codewords of `S` agree with `y` at coordinate `j`.
  set m : Fin n → ℕ := fun j => (S.filter fun c => c j = y j).card with hm
  set agr : (Fin n → α) → (Fin n → α) → ℕ :=
    fun c c' => (univ.filter fun j => c j = y j ∧ c' j = y j).card with hagr
  -- First moment: `∑ⱼ mⱼ = ∑_{c ∈ S} #{j | c j = y j}`.
  have hsum : ∑ j, m j = ∑ c ∈ S, (univ.filter fun j => c j = y j).card := by
    simp only [hm, card_filter]
    exact sum_comm
  -- Second moment: `∑ⱼ mⱼ² = ∑_{c, c' ∈ S} #{j | c j = y j ∧ c' j = y j}`.
  have hsq : ∑ j, m j ^ 2 = ∑ c ∈ S, ∑ c' ∈ S, agr c c' := by
    have : ∀ j, m j ^ 2 = ∑ c ∈ S, ∑ c' ∈ S,
        (if c j = y j ∧ c' j = y j then 1 else 0) := by
      intro j
      simp only [hm, card_filter, sq, sum_mul_sum]
      refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
      split_ifs <;> simp_all
    simp only [this, hagr, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]
  -- Lower bound on the first moment.
  have hlow : S.card * (n - e) ≤ ∑ j, m j := by
    rw [hsum, ← smul_eq_mul]
    refine card_nsmul_le_sum S _ (n - e) fun c hc => ?_
    rw [card_filter_eq, hammingDist_comm]
    have := hball c hc
    omega
  -- Upper bound on the second moment.
  have hup : ∑ j, m j ^ 2 ≤ ∑ j, m j + S.card * (S.card - 1) * (n - d) := by
    rw [hsq, hsum, mul_assoc, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_le_sum fun c hc => ?_
    rw [← add_sum_erase S _ hc]
    have hdiag : agr c c = (univ.filter fun j => c j = y j).card := by simp [hagr]
    rw [hdiag]
    refine Nat.add_le_add_left ?_ _
    calc ∑ c' ∈ S.erase c, agr c c' ≤ (S.erase c).card • (n - d) := by
          refine sum_le_card_nsmul _ _ _ fun c' hc' => ?_
          have hne : c' ≠ c := ne_of_mem_erase hc'
          have hsub : (univ.filter fun j => c j = y j ∧ c' j = y j) ⊆
              univ.filter fun j => c j = c' j := by
            intro j hj
            simp only [mem_filter, mem_univ, true_and] at hj ⊢
            rw [hj.1, hj.2]
          have h1 := card_le_card hsub
          rw [card_filter_eq] at h1
          have h2 := hdist c hc c' (mem_of_mem_erase hc') hne.symm
          simp only [hagr]
          omega
      _ = (S.card - 1) * (n - d) := by rw [card_erase_of_mem hc, smul_eq_mul]
  -- Cauchy–Schwarz.
  have hCS : (∑ j, m j) ^ 2 ≤ n * ∑ j, m j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := m)
    simpa [card_univ, Fintype.card_fin] using this
  -- Integer arithmetic.
  have htD : n - d < n - e := by
    by_contra h
    push Not at h
    have : (n - e) ^ 2 ≤ n * (n - d) :=
      calc (n - e) ^ 2 = (n - e) * (n - e) := sq _
        _ ≤ n * (n - d) := Nat.mul_le_mul (Nat.sub_le n e) h
    omega
  have key := johnson_arith (L := (S.card : ℤ)) (A := ((∑ j, m j : ℕ) : ℤ))
    (B := ((∑ j, m j ^ 2 : ℕ) : ℤ)) (n := (n : ℤ)) (t := ((n - e : ℕ) : ℤ))
    (D := ((n - d : ℕ) : ℤ)) (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast Nat.sub_le n e) (by exact_mod_cast hlow) (by exact_mod_cast hCS)
    (by
      have h' : ((∑ j, m j ^ 2 : ℕ) : ℤ) ≤
          ((∑ j, m j : ℕ) : ℤ) + ((S.card * (S.card - 1) * (n - d) : ℕ) : ℤ) := by
        rw [← Nat.cast_add]; exact_mod_cast hup
      have e3 : ((S.card * (S.card - 1) * (n - d) : ℕ) : ℤ) =
          (S.card : ℤ) * ((S.card : ℤ) - 1) * ((n - d : ℕ) : ℤ) := by
        rcases Nat.eq_zero_or_pos S.card with h0 | hpos
        · rw [h0]; simp
        · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]
      linarith)
    (by exact_mod_cast hJ)
  have e1 : (((n - e) ^ 2 - n * (n - d) : ℕ) : ℤ) =
      ((n - e : ℕ) : ℤ) ^ 2 - n * ((n - d : ℕ) : ℤ) := by
    rw [Nat.cast_sub hJ.le]; push_cast; ring
  have e2 : (((n - e) - (n - d) : ℕ) : ℤ) = ((n - e : ℕ) : ℤ) - ((n - d : ℕ) : ℤ) := by
    rw [Nat.cast_sub htD.le]
  have : ((S.card * ((n - e) ^ 2 - n * (n - d)) : ℕ) : ℤ) ≤
      ((n * ((n - e) - (n - d)) : ℕ) : ℤ) := by
    push_cast [e1, e2]
    exact key
  exact_mod_cast this

/-- **Johnson bound, list size `n · d`.** Under the hypotheses of `johnson_bound`, the list has
at most `n · d` words: the denominator `(n - e)² - n (n - d)` is a positive integer and the
numerator `n ((n - e) - (n - d))` is at most `n d` (Guruswami, Rudra and Sudan, *Essential Coding
Theory*, draft of August 26, 2025, Theorem 7.3.3 gives the list size `q n d`). -/
theorem card_le_mul_of_johnson (S : Finset (Fin n → α)) (y : Fin n → α) {d e : ℕ} (hen : e ≤ n)
    (hdn : d ≤ n) (hdist : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hball : ∀ c ∈ S, hammingDist y c ≤ e) (hJ : n * (n - d) < (n - e) ^ 2) :
    S.card ≤ n * d := by
  have h := johnson_bound S y hen hdn hdist hball hJ
  have hpos : 1 ≤ (n - e) ^ 2 - n * (n - d) := by omega
  calc S.card ≤ S.card * ((n - e) ^ 2 - n * (n - d)) := Nat.le_mul_of_pos_right _ hpos
    _ ≤ n * ((n - e) - (n - d)) := h
    _ ≤ n * d := Nat.mul_le_mul_left _ (by omega)

/-- **Every code is list decodable up to the Johnson radius.** A code of length `n` whose
distinct codewords are at distance at least `d ≤ n` is list decodable from `e ≤ n` errors with
list size `n · d` whenever `n (n - d) < (n - e)²`, that is `e < n - √(n (n - d))` (Guruswami,
Rudra and Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 7.3.3, strict
case, with list size `n d` in place of `q n d`). -/
theorem isListDecodable_of_johnson (C : Finset (Fin n → α)) {d e : ℕ} (hen : e ≤ n)
    (hdn : d ≤ n) (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hJ : n * (n - d) < (n - e) ^ 2) : IsListDecodable C e (n * d) := by
  intro y
  refine card_le_mul_of_johnson _ y hen hdn (fun c₁ h₁ c₂ h₂ hne => ?_) (fun c hc => ?_) hJ
  · exact hdist c₁ (mem_filter.mp h₁).1 c₂ (mem_filter.mp h₂).1 hne
  · exact (mem_filter.mp hc).2

/-- **Some ball holds many codewords** (the counting half of list-decoding capacity). For every
code `C` of length `n` over a nonempty alphabet with `q` letters and every radius `e`, some word
`y` has `|C| · Vol_q(n, e) ≤ q ^ n · |{c ∈ C : Δ(y, c) ≤ e}|`, where
`Vol_q(n, e) = ∑_{i=0}^{e} C(n, i) (q - 1) ^ i`. Averaging over a uniformly random centre, each
codeword lies in the ball with probability `Vol_q(n, e) / q ^ n` (Guruswami, Rudra and Sudan,
*Essential Coding Theory*, draft of August 26, 2025, Lemma 8.1.2, and equations (7.12)–(7.16) in
the proof of Theorem 7.4.2 (ii)). With `Vol_q(n, ρn) ≥ q ^ {H_q(ρ) n - o(n)}` it shows that codes
of rate `1 - H_q(ρ) + ε` are not list decodable from `ρn` errors with subexponential lists
(`MathlibExt.Combinatorics.Coding.ListDecodingCapacity.exists_many_in_ball`). -/
theorem exists_mul_card_filter_ge [Fintype α] [Nonempty α] (C : Finset (Fin n → α)) (e : ℕ) :
    ∃ y : Fin n → α,
      C.card * ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i ≤
        Fintype.card α ^ n * (C.filter fun c => hammingDist y c ≤ e).card := by
  classical
  set V := ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i with hV
  -- Double counting: `∑_y |C ∩ B(y, e)| = ∑_{c ∈ C} |B(c, e)| = |C| V`.
  have hdouble : ∑ y : Fin n → α, (C.filter fun c => hammingDist y c ≤ e).card = C.card * V := by
    have hball : ∀ c ∈ C, (Hamming.ball c e).card = V := by
      intro c _; rw [Hamming.card_ball, Fintype.card_fin]
    calc ∑ y : Fin n → α, (C.filter fun c => hammingDist y c ≤ e).card
        = ∑ c ∈ C, (Hamming.ball c e).card := by
          simp only [card_filter, Hamming.ball]
          rw [sum_comm]
          refine sum_congr rfl fun c _ => sum_congr rfl fun y _ => ?_
          rw [hammingDist_comm]
      _ = C.card * V := by rw [sum_congr rfl hball, sum_const, smul_eq_mul]
  have huniv : (univ : Finset (Fin n → α)).card = Fintype.card α ^ n := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨y, -, hy⟩ := exists_le_of_sum_le (s := (univ : Finset (Fin n → α)))
    (f := fun _ => C.card * V)
    (g := fun y => Fintype.card α ^ n * (C.filter fun c => hammingDist y c ≤ e).card)
    univ_nonempty (by
      rw [sum_const, ← mul_sum, hdouble, huniv, smul_eq_mul])
  exact ⟨y, hy⟩

end MathlibExt.Combinatorics.Coding.ListDecoding
