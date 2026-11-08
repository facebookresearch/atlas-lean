/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# Ulam words — wishlist

Statements from Paul Adutwum, Hopper Clark, Ro Emerson, Alexandra (Sasha) Sheydvasser,
Arseniy (Senia) Sheydvasser, and Axelle Tougouma, *Distributions of Ulam Words up to Length
30*, INTEGERS 25 (2025), Article A102 (arXiv:2410.01217v2).

Words over `{0, 1}` are `List Bool` with `false = 0`, `true = 1`. Following Bade, Cui,
Labelle, and Li (as quoted in Section 1 of the paper), `0` and `1` are Ulam, and a word
`w ≠ 0, 1` is Ulam iff there is exactly one pair of Ulam words `u₁ ≠ u₂` with `w = u₁ u₂`.
The integer `π(w)` of a word is its binary value, most significant letter first, written
`Nat.ofDigits 2 (w.reverse.map Bool.toNat)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Fuel-indexed Ulam test: `ulamWordAux f w` decides whether `w` is an Ulam word whenever
`w.length ≤ f`. A word of length `1` is Ulam; a longer word is Ulam iff exactly one split
position `k` gives two distinct Ulam halves `w.take (k + 1)` and `w.drop (k + 1)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def ulamWordAux : ℕ → List Bool → Bool
  | 0, _ => false
  | f + 1, w =>
    if w.length = 1 then true
    else
      ((List.range (w.length - 1)).countP fun k =>
        w.take (k + 1) != w.drop (k + 1) && ulamWordAux f (w.take (k + 1)) &&
          ulamWordAux f (w.drop (k + 1))) == 1

/-- `w` is an Ulam word.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def IsUlamWord (w : List Bool) : Prop :=
  ulamWordAux w.length w = true

/-- Ulam-ness is decidable.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public instance : DecidablePred IsUlamWord := fun w =>
  inferInstanceAs (Decidable (ulamWordAux w.length w = true))

/-- The paper's lists `U₂ = {01, 10}` and `U₃ = {001, 011, 100, 110}`, checked on all words
of length `2` and `3`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem isUlamWord_small :
    IsUlamWord [false] ∧ IsUlamWord [true] ∧ ¬ IsUlamWord [] ∧
      ¬ IsUlamWord [false, false] ∧ IsUlamWord [false, true] ∧ IsUlamWord [true, false] ∧
      ¬ IsUlamWord [true, true] ∧
      ¬ IsUlamWord [false, false, false] ∧ IsUlamWord [false, false, true] ∧
      ¬ IsUlamWord [false, true, false] ∧ IsUlamWord [false, true, true] ∧
      IsUlamWord [true, false, false] ∧ ¬ IsUlamWord [true, false, true] ∧
      IsUlamWord [true, true, false] ∧ ¬ IsUlamWord [true, true, true] := by
  decide

/-- The defining recursion for a word of length `4`: `0001` is Ulam (only the split
`0 · 001` has distinct Ulam halves) and `0011` is not (no split does).

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₄`). -/
public theorem isUlamWord_length_four_examples :
    IsUlamWord [false, false, false, true] ∧ ¬ IsUlamWord [false, false, true, true] ∧
      IsUlamWord [true, false, true, true] ∧ ¬ IsUlamWord [false, true, true, false] := by
  decide

/-- The number `#U_n` of Ulam words of length `n`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public def ulamWordCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).card

/-- `#U₁, …, #U₄ = 2, 2, 4, 8`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem ulamWordCount_small :
    ulamWordCount 1 = 2 ∧ ulamWordCount 2 = 2 ∧ ulamWordCount 3 = 4 ∧ ulamWordCount 4 = 8 := by
  decide

/-- The number of Ulam words `w` of length `n` with `π(w) = a` in `ZMod N`; the paper's
relative density is `ρ_{a,N}(n) = ulamResidueCount N n a / #U_n`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 3, definition of `ρ_{a,N}(n)`). -/
public def ulamResidueCount (N n : ℕ) (a : ZMod N) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool =>
    IsUlamWord (List.ofFn v) ∧
      ((Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat) : ℕ) : ZMod N) = a).card

/-- Residues of `π(U₂) = {1, 2}` modulo `3`: one word in each of the classes `1`, `2`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 6. -/
public theorem ulamResidueCount_three_two :
    ulamResidueCount 3 2 0 = 0 ∧ ulamResidueCount 3 2 1 = 1 ∧ ulamResidueCount 3 2 2 = 1 := by
  decide

/-- The sorted list `u₁ < ⋯ < u_k` of the integers `π(U_n)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, ordered elements of `π(U_n)`). -/
public def ulamValuesSorted (n : ℕ) : List ℕ :=
  ((Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).image
    fun v => Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat)).sort (· ≤ ·)

/-- `π(U₃) = {1, 3, 4, 6}` (from `U₃ = {001, 011, 100, 110}`).

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public theorem ulamValuesSorted_three :
    (ulamValuesSorted 3).toFinset = {1, 3, 4, 6} := by
  rw [ulamValuesSorted, Finset.sort_toFinset]
  decide

/-- The mean gap `μ_g(n) = (∑ᵢ (u_{i+1} - u_i)) / (k - 1)` of the sorted list
`u₁ < ⋯ < u_k` of `π(U_n)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, `μ_g(n)` as the mean of the gap distribution `p_n`). -/
public def ulamGapMean (n : ℕ) : ℚ :=
  (((List.zipWith (fun a b : ℕ => b - a) (ulamValuesSorted n)
      (ulamValuesSorted n).tail).sum : ℕ) : ℚ) /
    (((ulamValuesSorted n).length : ℚ) - 1)

/-- The stages `S₀ = {(2, 1)}`, `S_{n+1} = S_n ∪ (S_n + (2ⁿ, 0)) ∪ (S_n + (2ⁿ, 2ⁿ))` of the
discrete Sierpiński triangle.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4
(recursive definition of `S_n`). -/
public def discreteSierpinskiStage : ℕ → Set (ℕ × ℕ)
  | 0 => {(2, 1)}
  | n + 1 =>
    discreteSierpinskiStage n ∪ (fun p => (p.1 + 2 ^ n, p.2)) '' discreteSierpinskiStage n ∪
      (fun p => (p.1 + 2 ^ n, p.2 + 2 ^ n)) '' discreteSierpinskiStage n

/-- The discrete Sierpiński triangle `𝒮 = ⋃ₙ S_n`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public def discreteSierpinski : Set (ℕ × ℕ) :=
  ⋃ n, discreteSierpinskiStage n

/-- `S₁ = {(2, 1), (3, 1), (3, 2)}`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public theorem discreteSierpinskiStage_one :
    discreteSierpinskiStage 1 = {(2, 1), (3, 1), (3, 2)} := by
  ext p
  simp only [discreteSierpinskiStage, Set.image_singleton, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  norm_num
  tauto

/-- For `a + b ≥ 1`, `0^a 1⁴ 0^b` is Ulam iff `a + b ≡ 1 (mod 4)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 1. -/
public theorem_wanted isUlamWord_zeros_four_ones_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ List.replicate 4 true ++ List.replicate b false) ↔
      (a + b) % 4 = 1

/-- `#U_n² ≤ #U_n + #U_{n+1} + ⋯ + #U_{2n}`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 2. -/
public theorem_wanted ulamWordCount_sq_le_sum (n : ℕ) :
    ulamWordCount n ^ 2 ≤ ∑ i ∈ Finset.Icc n (2 * n), ulamWordCount i

/-- For `n ≥ 3`, `1³ 0^{n-3}` is Ulam iff `n ≡ 0` or `1 (mod 4)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 3. -/
public theorem_wanted isUlamWord_three_ones_zeros_iff (n : ℕ) (hn : 3 ≤ n) :
    IsUlamWord (List.replicate 3 true ++ List.replicate (n - 3) false) ↔
      n % 4 = 0 ∨ n % 4 = 1

/-- For all `n ≥ 6`, `#U_n ≥ 2n + 4`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 1. -/
public theorem_wanted two_mul_add_four_le_ulamWordCount (n : ℕ) (hn : 6 ≤ n) :
    2 * n + 4 ≤ ulamWordCount n

/-- `limsup #U_n / αⁿ = ∞` for every `1 < α < α₀`, where `α₀ = (#U₃₀ / (2 · 31))^{1/30}` is
the constant of the paper's proof (`n₁ = 30`); stated as: for every `C` and `N` some
`n ≥ N` has `C αⁿ ≤ #U_n`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 2. -/
public theorem_wanted ulamWordCount_limsup_div_pow_eq_top (α : ℝ) (hα : 1 < α)
    (hα₀ : α < ((ulamWordCount 30 : ℝ) / (2 * 31)) ^ ((1 : ℝ) / 30)) (C : ℝ) (N : ℕ) :
    ∃ n ≥ N, C * α ^ n ≤ ulamWordCount n

/-- `ρ(n)⁻¹ ≍ μ_g(n)`, where `ρ(n) = #U_n / 2ⁿ` and `μ_g(n)` is the mean gap of `π(U_n)`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 4 (first sentence). -/
public theorem_wanted ulamDensity_inv_isTheta_ulamGapMean :
    (fun n : ℕ => (2 : ℝ) ^ n / ulamWordCount n) =Θ[Filter.atTop]
      fun n => (ulamGapMean n : ℝ)

/-- For `n ≥ 1` there are `G(n - 1) = 2^{s₂(n-1)}` Ulam words of length `n` of the form
`0^a 1 0^b` (`G` is Gould's sequence, `s₂` the binary digit sum).

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 5
(Corollary 3.4 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted card_ulam_zeros_one_zeros (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range n).filter fun a =>
        IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (n - 1 - a) false)).card =
      2 ^ (Nat.digits 2 (n - 1)).sum

/-- `0^a 1² 0^b` is Ulam iff `a + b` is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 6
(Theorem 3.5 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_two_ones_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ List.replicate 2 true ++ List.replicate b false) ↔
      (a + b) % 2 = 1

/-- For `a + b ≥ 2`, `0^a 101 0^b` is Ulam iff `a + b` is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 7
(Theorem 3.6 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_one_zero_one_zeros_iff (a b : ℕ) (hab : 2 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true] ++ List.replicate b false) ↔
      (a + b) % 2 = 1

/-- `0^a 1 0^b` is Ulam iff `binom(a + b, a)` is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 8
(Theorem 3.4 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_one_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate b false) ↔
      Odd ((a + b).choose a)

/-- For `1 ≤ y ≤ x`, `1^y 0^{x-y}` is Ulam iff `(x, y) = (1, 1)` or `(x, y)` lies in the
discrete Sierpiński triangle `𝒮`.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 9
(precise form of Theorem 3). -/
public theorem_wanted isUlamWord_ones_zeros_iff_mem_discreteSierpinski (x y : ℕ) (hy : 1 ≤ y)
    (hyx : y ≤ x) :
    IsUlamWord (List.replicate y true ++ List.replicate (x - y) false) ↔
      (x, y) = (1, 1) ∨ (x, y) ∈ discreteSierpinski

/-- For `a + b ≥ 1`, `0^a 10101 0^b` is Ulam iff `a, b` are even and one of them is zero.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 10. -/
public theorem_wanted isUlamWord_zeros_10101_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true, false, true] ++
        List.replicate b false) ↔
      Even a ∧ Even b ∧ (a = 0 ∨ b = 0)

/-- Complement symmetry (corrected reading): if `w ∈ U_n` then its complement `ŵ` is in
`U_n` with `π(ŵ) = 2ⁿ - 1 - π(w)`; consequently `ρ_{a,N}(n) = ρ_{2ⁿ-1-a,N}(n)`, stated
with the common denominator `#U_n` cleared.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 11. -/
public theorem_wanted isUlamWord_map_not_and_ulamResidueCount_eq :
    (∀ w : List Bool, IsUlamWord w →
      IsUlamWord (w.map not) ∧
        Nat.ofDigits 2 ((w.map not).reverse.map Bool.toNat) +
            Nat.ofDigits 2 (w.reverse.map Bool.toNat) = 2 ^ w.length - 1) ∧
      ∀ (N n : ℕ) (a : ZMod N),
        ulamResidueCount N n a = ulamResidueCount N n (2 ^ n - 1 - a)

/-- For `n ≥ 1`, `ρ_{0,2}(n) = ρ_{1,2}(n)`, and for `a ∈ ℤ/3ℤ`, `ρ_{a,3}(n) = ρ_{-a,3}(n)`
if `n` is even and `ρ_{a,3}(n) = ρ_{1-a,3}(n)` if `n` is odd (corrected parity), stated
with the common denominator `#U_n` cleared.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102,
Corollary 2. -/
public theorem_wanted ulamResidueCount_mod_two_three (n : ℕ) (hn : 1 ≤ n) :
    ulamResidueCount 2 n 0 = ulamResidueCount 2 n 1 ∧
      ∀ a : ZMod 3, ulamResidueCount 3 n a =
        if Even n then ulamResidueCount 3 n (-a) else ulamResidueCount 3 n (1 - a)

end

end MetaMathlibExt
