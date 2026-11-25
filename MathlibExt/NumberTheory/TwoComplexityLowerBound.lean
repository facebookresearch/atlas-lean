/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexityMax

/-!
# A logarithmic lower bound for the 2-complexity

We classify expression values above one quarter of the maximum for their size, and deduce
Zhang's lower bound of `Real.logb 2 n + 2` outside the exceptional forms.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private def bin (d : ℕ) := 2 ^ d + 1
private def tri (a b : ℕ) := 2 ^ b * bin a + 1

-- The indices record both the number of leaves and the value. In the last six cases, s
-- is a common binary shift. The two pair cases differ by one leaf.
private inductive Shape : ℕ → ℕ → Prop
  | small {k n} (h : 4 * n ≤ 2 ^ k) : Shape k n
  | max (k) : Shape k (2 ^ k)
  | pair (s d) (hs : 1 ≤ s) (hd : 1 ≤ d) : Shape (s + (d + 1)) (2 ^ s * bin d)
  | lowPair (s d) (hs : 1 ≤ s) : Shape (s + (d + 2)) (2 ^ s * bin d)
  | three (s a b) (hs : 1 ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b) :
      Shape (s + (a + b + 2)) (2 ^ s * tri a b)
  | rect (s d e) (hs : 2 ≤ s) (hd : 1 ≤ d) (hde : d ≤ e) (he : 2 ≤ e) :
      Shape (s + (d + e + 2)) (2 ^ s * (bin d * bin e))
  | adjacent (s b) (hs : 2 ≤ s) (hb : 1 ≤ b) :
      Shape (s + (b + 5)) (2 ^ s * (9 * 2 ^ b + 3))
  | last (s) (hs : 3 ≤ s) : Shape (s + 9) (2 ^ s * 135)

private theorem Shape.scale {k n : ℕ} (h : Shape k n) (t : ℕ) :
    Shape (t + k) (2 ^ t * n) := by
  cases h with
  | small h =>
    apply Shape.small
    rw [pow_add, mul_left_comm]
    exact Nat.mul_le_mul_left _ h
  | max k => simpa only [pow_add] using Shape.max (t + k)
  | pair s d hs hd =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.pair (t + s) d (by omega) hd
  | lowPair s d hs =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.lowPair (t + s) d (by omega)
  | three s a b hs ha hb =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.three (t + s) a b (by omega) ha hb
  | rect s d e hs hd hde he =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.rect (t + s) d e (by omega) hd hde he
  | adjacent s b hs hb =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.adjacent (t + s) b (by omega) hb
  | last s hs =>
    simpa only [pow_add, mul_assoc, Nat.add_assoc] using Shape.last (t + s) (by omega)

-- Increasing an exponent gap by t increases the value by at most a factor of 2^t.
private theorem bin_shift (d t : ℕ) : bin (d + t) ≤ 2 ^ t * bin d := by
  simp only [bin, pow_add, Nat.mul_add, mul_one, mul_comm (2 ^ d) (2 ^ t)]
  have := Nat.two_pow_pos t
  omega

private theorem tri_shift (a b u v : ℕ) :
    tri (a + u) (b + v) ≤ 2 ^ (u + v) * tri a b := by
  have h := Nat.mul_le_mul_left (2 ^ (b + v)) (bin_shift a u)
  have hp := Nat.two_pow_pos (u + v)
  simp only [tri, pow_add, Nat.mul_add, mul_one] at *
  linarith only [h, hp]

-- A product bound at the smallest possible gaps propagates to all larger gaps.
private theorem tri_product_small {a b d : ℕ} (a₀ b₀ d₀ : ℕ)
    (ha : a₀ ≤ a) (hb : b₀ ≤ b) (hd : d₀ ≤ d)
    (h : 4 * (tri a₀ b₀ * bin d₀) ≤ 2 ^ (a₀ + b₀ + d₀ + 3)) :
    Shape (a + b + d + 3) (tri a b * bin d) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hd
  apply Shape.small
  calc
    _ ≤ 4 * ((2 ^ (u + v) * tri a₀ b₀) * (2 ^ w * bin d₀)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (tri_shift ..) (bin_shift ..))
    _ = 2 ^ (u + v + w) * (4 * (tri a₀ b₀ * bin d₀)) := by simp only [pow_add]; ac_rfl
    _ ≤ _ := by
      rw [show a₀ + u + (b₀ + v) + (d₀ + w) + 3 = (u + v + w) + (a₀ + b₀ + d₀ + 3) by omega,
        pow_add 2 (u + v + w)]
      exact Nat.mul_le_mul_left _ h

private theorem bin_product_bound {d e f : ℕ} (d₀ e₀ f₀ : ℕ)
    (hd : d₀ ≤ d) (he : e₀ ≤ e) (hf : f₀ ≤ f)
    (h : bin d₀ * bin e₀ * bin f₀ ≤ 2 ^ (d₀ + e₀ + f₀ + 1)) :
    bin d * bin e * bin f ≤ 2 ^ (d + e + f + 1) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le he
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hf
  calc
    _ ≤ (2 ^ u * bin d₀) * (2 ^ v * bin e₀) * (2 ^ w * bin f₀) :=
      Nat.mul_le_mul (Nat.mul_le_mul (bin_shift ..) (bin_shift ..)) (bin_shift ..)
    _ = 2 ^ (u + v + w) * (bin d₀ * bin e₀ * bin f₀) := by simp only [pow_add]; ac_rfl
    _ ≤ _ := by
      rw [show d₀ + u + (e₀ + v) + (f₀ + w) + 1 = (u + v + w) + (d₀ + e₀ + f₀ + 1) by omega,
        pow_add 2 (u + v + w)]
      exact Nat.mul_le_mul_left _ h

private theorem two_bin_bound {d e : ℕ} (hd : 1 ≤ d) (he : 2 ≤ e) :
    bin d * bin e ≤ 2 ^ (d + e + 1) := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (Nat.pow_le_pow_right (n := 2) (by decide) hd)
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (Nat.pow_le_pow_right (n := 2) (by decide) he)
  simp only [bin, pow_add, hu, hv]
  ring_nf
  omega

private theorem Shape.half {k n : ℕ} (h : Shape k n) :
    n = 2 ^ k ∨ (∃ s d, 1 ≤ s ∧ 1 ≤ d ∧ k = s + (d + 1) ∧ n = 2 ^ s * bin d) ∨
      2 * n ≤ 2 ^ k := by
  cases h with
  | max k => exact Or.inl rfl
  | pair s d hs hd => exact Or.inr (Or.inl ⟨s, d, hs, hd, rfl, rfl⟩)
  | small h => exact Or.inr (Or.inr (by omega))
  | lowPair s d hs =>
    right; right
    have hp := Nat.two_pow_pos d
    simp only [pow_add, bin, Nat.mul_add, mul_one]
    nlinarith only [Nat.mul_le_mul_left (2 ^ s) hp]
  | three s a b hs ha hb =>
    right; right
    -- The leading term dominates the other two since both gaps are positive.
    have hab : 2 ^ b + 1 ≤ 2 ^ a * 2 ^ b := by
      have h₁ : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
      nlinarith only [Nat.mul_le_mul_right (2 ^ b) h₁, Nat.two_pow_pos b]
    simp only [tri, bin, pow_add, Nat.mul_add, mul_one]
    nlinarith only [Nat.mul_le_mul_left (2 ^ s) hab]
  | rect s d e hs hd hde he =>
    right; right
    have h := Nat.mul_le_mul_left (2 ^ s) (two_bin_bound hd he)
    simp only [pow_add, pow_one] at *
    nlinarith only [h]
  | adjacent s b hs hb =>
    right; right
    have hp := Nat.mul_le_mul_left (2 ^ s) (Nat.one_le_two_pow (n := b))
    simp only [pow_add, mul_one] at *
    ring_nf at hp ⊢
    omega
  | last s hs =>
    right; right
    rw [pow_add]
    omega

private theorem pair_product (s d e : ℕ) (hs : 2 ≤ s) (hd : 1 ≤ d) (he : 1 ≤ e) :
    Shape (s + (d + e + 2)) (2 ^ s * (bin d * bin e)) := by
  wlog hde : d ≤ e generalizing d e
  · simpa only [add_comm e d, mul_comm (bin e) (bin d)] using this e d he hd (by omega)
  by_cases h : 2 ≤ e
  · exact Shape.rect s d e hs hd hde h
  · obtain rfl : d = 1 := by omega
    obtain rfl : e = 1 := by omega
    exact Shape.pair s 3 (by omega) (by decide)

-- With three binomial factors, two gaps of one combine via 3 * 3 = 9. The only
-- other products above the quarter threshold have odd part 3 * 5 * 5 or 3 * 5 * 9.
private theorem three_bin_sorted (s d e f : ℕ) (hs : 3 ≤ s)
    (hd : 1 ≤ d) (hde : d ≤ e) (hef : e ≤ f) :
    Shape (s + (d + e + f + 3)) (2 ^ s * (bin d * bin e * bin f)) := by
  have small (h : bin d * bin e * bin f ≤ 2 ^ (d + e + f + 1)) :
      Shape (d + e + f + 3) (bin d * bin e * bin f) := by
    apply Shape.small
    rw [show d + e + f + 3 = (d + e + f + 1) + 2 by omega, pow_add]
    omega
  by_cases h₂ : 2 ≤ d
  · exact (small (bin_product_bound 2 2 2 h₂ (by omega) (by omega) (by decide))).scale s
  obtain rfl : d = 1 := by omega
  by_cases h₃ : 3 ≤ e
  · exact (small (bin_product_bound 1 3 3 hd h₃ (by omega) (by decide))).scale s
  by_cases h₁ : e = 1
  · subst e
    convert pair_product s 3 f (by omega) (by decide) (by omega) using 1 <;> first | omega | rfl
  obtain rfl : e = 2 := by omega
  by_cases h₄ : 4 ≤ f
  · exact (small (bin_product_bound 1 2 4 hd (by decide) h₄ (by decide))).scale s
  rcases (show f = 2 ∨ f = 3 by omega) with rfl | rfl
  · exact Shape.adjacent s 3 (by omega) (by decide)
  · exact Shape.last s hs

private theorem three_bin_product (s d e f : ℕ) (hs : 3 ≤ s)
    (hd : 1 ≤ d) (hde : d ≤ e) (hf : 1 ≤ f) :
    Shape (s + (d + e + f + 3)) (2 ^ s * (bin d * bin e * bin f)) := by
  rcases le_total e f with hef | hfe
  · exact three_bin_sorted s d e f hs hd hde hef
  rcases le_total d f with hdf | hfd
  · convert three_bin_sorted s d f e hs hd hdf hfe using 1 <;> first | omega | ac_rfl
  · convert three_bin_sorted s f d e hs hf hfd hde using 1 <;> first | omega | ac_rfl

private theorem three_mul_bin (s a b d : ℕ) (hs : 2 ≤ s)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d) :
    Shape (s + (a + b + d + 3)) (2 ^ s * (tri a b * bin d)) := by
  by_cases ha₃ : 3 ≤ a
  · exact (tri_product_small 3 1 1 ha₃ hb hd (by decide)).scale s
  by_cases hd₃ : 3 ≤ d
  · exact (tri_product_small 1 1 3 ha hb hd₃ (by decide)).scale s
  rcases (show a = 1 ∨ a = 2 by omega) with rfl | rfl
  · rcases (show d = 1 ∨ d = 2 by omega) with rfl | rfl
    · convert Shape.adjacent s b hs hb using 1
      · omega
      · simp only [tri, show bin 1 = 3 by decide]
        ring
    · by_cases hb₃ : 3 ≤ b
      · exact (tri_product_small 1 3 2 ha hb₃ (by decide) (by decide)).scale s
      rcases (show b = 1 ∨ b = 2 by omega) with rfl | rfl
      · exact Shape.three s 4 1 (by omega) (by decide) (by decide)
      · exact Shape.lowPair s 6 (by omega)
  · by_cases hd₂ : 2 ≤ d
    · exact (tri_product_small 2 1 2 (by decide) hb hd₂ (by decide)).scale s
    by_cases hb₂ : 2 ≤ b
    · exact (tri_product_small 2 2 1 (by decide) hb₂ hd (by decide)).scale s
    obtain rfl : b = 1 := by omega
    obtain rfl : d = 1 := by omega
    exact Shape.lowPair s 5 (by omega)

private theorem third_mul_bin {k n d : ℕ} (hn : 3 * n ≤ 2 ^ k) (hd : 1 ≤ d) :
    Shape (k + d + 1) (n * bin d) := by
  apply Shape.small
  have h₂ : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have h := Nat.mul_le_mul_right (2 ^ d) hn
  dsimp [bin]
  simp only [pow_add, pow_one]
  nlinarith only [h, Nat.mul_le_mul_left n h₂]

private theorem lowPair_mul_bin (s d f : ℕ) (hs : 1 ≤ s) (hf : 1 ≤ f) :
    Shape (s + (d + f + 3)) (2 ^ s * (bin d * bin f)) := by
  rcases d with _ | d
  · convert Shape.lowPair (s + 1) f (by omega) using 1
    · omega
    · simp only [pow_succ, show bin 0 = 2 by decide, mul_assoc]
  by_cases h : d + 1 = 1 ∧ f = 1
  · obtain ⟨hd, rfl⟩ := h
    rw [hd]
    exact Shape.lowPair s 3 hs
  have hbound : bin (d + 1) * bin f ≤ 2 ^ (d + 1 + f + 1) := by
    rcases le_total (d + 1) f with hdf | hfd
    · exact two_bin_bound (by omega) (by omega)
    · rw [mul_comm, Nat.add_comm (d + 1) f]
      exact two_bin_bound hf (by omega)
  apply Shape.scale (t := s)
  apply Shape.small
  rw [show d + 1 + f + 3 = (d + 1 + f + 1) + 2 by omega, pow_add]
  omega

private theorem Shape.mul_pair {k n : ℕ} (h : Shape k n) (j f : ℕ) (hj : 1 ≤ j) (hf : 1 ≤ f) :
    Shape (k + (j + (f + 1))) (n * (2 ^ j * bin f)) := by
  cases h with
  | small h =>
    apply Shape.small
    have hb : bin f ≤ 2 ^ (f + 1) := by
      simp only [bin, pow_succ]
      have := Nat.two_pow_pos f
      omega
    have hp := Nat.mul_le_mul h (Nat.mul_le_mul_left (2 ^ j) hb)
    simpa only [pow_add, mul_assoc] using hp
  | max k =>
    convert Shape.pair (k + j) f (by omega) hf using 1 <;> simp [pow_add, mul_assoc, add_assoc]
  | pair s d hs hd =>
    convert pair_product (s + j) d f (by omega) hd hf using 1 <;> first | omega | rw [pow_add]; ring
  | lowPair s d hs =>
    convert lowPair_mul_bin (s + j) d f (by omega) hf using 1 <;> first | omega | rw [pow_add]; ring
  | three s a b hs ha hb =>
    convert three_mul_bin (s + j) a b f (by omega) ha hb hf using 1 <;>
      first | omega | rw [pow_add]; ring
  | rect s d e hs hd hde he =>
    convert three_bin_product (s + j) d e f (by omega) hd hde hf using 1 <;>
      first | omega | rw [pow_add]; ring
  | adjacent s b hs hb =>
    have hp : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
    have ht : 3 * (9 * 2 ^ b + 3) ≤ 2 ^ (b + 5) := by rw [pow_add]; omega
    convert (third_mul_bin ht hf).scale (s + j) using 1 <;> first | omega | rw [pow_add]; ring
  | last s hs =>
    have ht : 3 * 135 ≤ 2 ^ 9 := by decide
    convert (third_mul_bin ht hf).scale (s + j) using 1 <;> first | omega | rw [pow_add]; ring

-- If both factors are at most half their respective maxima, their product is small.
-- Otherwise one factor is a power of two or a shifted binomial.
private theorem Shape.mul {a b x y : ℕ} (hx : Shape a x) (hy : Shape b y) :
    Shape (a + b) (x * y) := by
  rcases hx.half with rfl | ⟨s, d, hs, hd, rfl, rfl⟩ | hx'
  · exact hy.scale a
  · simpa only [add_comm b, mul_comm y] using hy.mul_pair s d hs hd
  rcases hy.half with rfl | ⟨s, d, hs, hd, rfl, rfl⟩ | hy'
  · simpa only [add_comm b, mul_comm (2 ^ b)] using hx.scale b
  · exact hx.mul_pair s d hs hd
  · apply Shape.small
    rw [pow_add]
    nlinarith only [Nat.mul_le_mul hx' hy']

private theorem lowPair_of_add_pow {b t : ℕ} (ht : 1 ≤ t) (htb : t ≤ b) :
    Shape (b + 2) (2 ^ t + 2 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htb
  convert Shape.lowPair t d ht using 1
  simp only [bin, pow_add]
  ring

private theorem add_two {b y : ℕ} (hb : 1 ≤ b) (he : 2 ∣ y) (hy : Shape b y) (hpos : 0 < y) :
    Shape (1 + b) (2 + y) := by
  rcases hy.half with rfl | ⟨s, d, hs, hd, rfl, rfl⟩ | hy'
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    cases d with
    | zero => exact Shape.max 2
    | succ d =>
      convert Shape.pair 1 (d + 1) (by decide) (by omega) using 1
      · omega
      · simp only [bin, pow_add, pow_one]
        ring
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hs
    cases b with
    | zero =>
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hd
      convert Shape.lowPair 2 d (by decide) using 1
      · omega
      · simp only [bin, pow_add, pow_one]
        ring
    | succ b =>
      convert Shape.three 1 d (b + 1) (by decide) hd (by omega) using 1
      · omega
      · simp only [tri, pow_add, pow_one]
        ring
  · by_cases h : 4 * (2 + y) ≤ 2 ^ (1 + b)
    · exact Shape.small h
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
    cases b with
    | zero => simp at hy' h; omega
    | succ b =>
      have he' : y = 2 ^ (b + 1) := by
        simp only [pow_add, pow_one] at h hy' ⊢
        omega
      rw [he']
      convert lowPair_of_add_pow (t := 1) (b := b + 1) (by decide) (by omega) using 1
      omega

-- With at least three leaves on each side a sum is small. With two leaves on the
-- smaller side, evenness leaves just two possible values above the quarter threshold.
private theorem add_shape {a b x y : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : Shape a x) (hy : Shape b y) (hex : 2 ∣ x) (hey : 2 ∣ y)
    (hx' : x ≤ 2 ^ a) (hy' : y ≤ 2 ^ b) (hpos : 0 < x) (hpos' : 0 < y) :
    Shape (a + b) (x + y) := by
  wlog hab : a ≤ b generalizing a b x y
  · simpa only [add_comm b a, add_comm y x] using
      this hb ha hy hx hey hex hy' hx' hpos' hpos (by omega)
  by_cases ha₁ : a = 1
  · subst a
    obtain rfl : x = 2 := by omega
    exact add_two hb hey hy hpos'
  by_cases ha₂ : a = 2
  · subst a
    by_cases h : 4 * (x + y) ≤ 2 ^ (2 + b)
    · exact Shape.small h
    have he : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega : b ≠ 0)
    have hsum : x + y = 2 ^ 1 + 2 ^ b ∨ x + y = 2 ^ 2 + 2 ^ b := by
      rw [pow_add] at h
      omega
    rw [Nat.add_comm 2 b]
    rcases hsum with h | h
    · rw [h]
      exact lowPair_of_add_pow (by decide) hb
    · rw [h]
      exact lowPair_of_add_pow (by decide) hab
  · apply Shape.small
    have h₁ : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    have h₂ : 2 ^ 3 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_add]
    nlinarith only [hx', hy', Nat.mul_le_mul_right (2 ^ b) h₁, Nat.mul_le_mul_left (2 ^ a) h₂]

private theorem build_shape {k n : ℕ} (h : CanBuild 2 k n) : 2 ∣ n ∧ 0 < n ∧ Shape k n := by
  induction h with
  | base => exact ⟨by decide, by decide, Shape.max 1⟩
  | add hx hy ihx ihy =>
    exact ⟨dvd_add ihx.1 ihy.1, add_pos ihx.2.1 ihy.2.1,
      add_shape hx.one_le hy.one_le ihx.2.2 ihy.2.2 ihx.1 ihy.1
        ((canBuild_max 2 _ (by decide) hx.one_le).2 _ hx)
        ((canBuild_max 2 _ (by decide) hy.one_le).2 _ hy) ihx.2.1 ihy.2.1⟩
  | mul _ _ ihx ihy => exact ⟨dvd_mul_of_dvd_left ihx.1 _, Nat.mul_pos ihx.2.1 ihy.2.1,
      ihx.2.2.mul ihy.2.2⟩

-- At cost m + 2 the leading exponent in each of the last four shapes is exactly m.
private theorem excluded_at_cost {m n k : ℕ} (h : Shape k n) (hk : k = m + 2)
    (hn : 2 ^ m < n) (hpow : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b)
    (hform : ¬ twoComplexityAddTwoForm m n) : False := by
  cases h with
  | small h =>
    rw [hk, pow_add] at h
    omega
  | max k =>
    apply hpow ⟨m + 1, m + 1, le_rfl, ?_⟩
    rw [hk, pow_succ 2 (m + 1)]
    omega
  | pair s d hs hd | lowPair s d hs =>
    apply hpow ⟨s, s + d, by omega, ?_⟩
    simp only [bin, pow_add]
    ring
  | three s a b hs ha hb =>
    obtain rfl : m = s + b + a := by omega
    apply hform (Or.inl ⟨s + b, s, by omega, by omega, hs, ?_⟩)
    simp only [tri, bin, pow_add]
    ring
  | rect s d e hs hd hde he =>
    obtain rfl : m = s + d + e := by omega
    rcases hde.eq_or_lt with rfl | hlt
    · apply hform (Or.inl ⟨s + d + 1, s, by omega, by omega, by omega, ?_⟩)
      simp only [bin, pow_add, pow_one]
      ring
    · apply hform (Or.inr (Or.inl ⟨s + e, s + d, s, by omega, by omega, by omega, hs,
        by omega, ?_⟩))
      simp only [bin, pow_add]
      ring
  | adjacent s b hs hb =>
    obtain rfl : m = s + b + 3 := by omega
    apply hform (Or.inr (Or.inr (Or.inl ⟨s + 1, by omega, by omega, ?_⟩)))
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
    simp only [pow_add, pow_one]
    ring
  | last s hs =>
    obtain rfl : m = s + 7 := by omega
    apply hform (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩)))
    rw [show s + 7 - 5 = s + 2 by omega, show s + 7 - 6 = s + 1 by omega, Nat.add_sub_cancel]
    simp only [pow_add, pow_one]
    ring

/-- **Lower bound $\log_2 n + 2$ for the 2-complexity (Zhang's Corollary 4).** Write $\|n\|_2$
for the 2-complexity of $n$: the least number of copies of $2$ from which $n$ can be built using
addition and multiplication, and $0$ if $n$ cannot be built. Let $m$ and $n$ be natural numbers
with $n$ even, $n \ge 1$ and $2^m < n \le 2^{m+1}$. Suppose that $n \ne 2^a + 2^b$ for all
natural numbers $a \le b$, and that $n$ has none of Zhang's four exceptional forms for $m$.
Then $\log_2 n + 2 \le \|n\|_2$, where $\log_2$ is the real base-2 logarithm.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 4. -/
public theorem logb_two_add_two_le (m n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1))
    (hpow : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b)
    (hform : ¬ twoComplexityAddTwoForm m n) :
    Real.logb 2 n + 2 ≤ (complexityL 2 n : ℝ) := by
  have hp (i : ℕ) : Real.logb 2 ((2 : ℝ) ^ i) = i := by
    simp [Real.logb_pow, Real.logb_self_eq_one]
  have hlo : (m : ℝ) < Real.logb 2 n := by
    rw [← hp m]
    exact Real.logb_lt_logb (by norm_num) (by positivity) (by exact_mod_cast hn1)
  have hhi : Real.logb 2 n ≤ (m : ℝ) + 1 := by
    rw [← Nat.cast_add_one, ← hp (m + 1)]
    exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn) (by exact_mod_cast hn2)
  have hl := logb_two_add_one_le n h2n hn hpow
  have hk : m + 1 < complexityL 2 n := by
    exact_mod_cast (show (m : ℝ) + 1 < (complexityL 2 n : ℝ) by linarith)
  have hb : ∃ k, CanBuild 2 k n := by
    by_contra h
    have := complexityL_eq_zero_iff.mpr h
    omega
  have hs := (build_shape (complexityL_spec hb)).2.2
  have hcost : m + 3 ≤ complexityL 2 n := by
    have : complexityL 2 n ≠ m + 2 := fun h => excluded_at_cost hs h hn1 hpow hform
    omega
  have : (m : ℝ) + 3 ≤ complexityL 2 n := by exact_mod_cast hcost
  linarith

end MathlibExt.NumberTheory.TwoComplexityWanted
