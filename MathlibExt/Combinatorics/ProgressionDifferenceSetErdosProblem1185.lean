/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Progressions with common difference in a difference set

We refute Erdős Problem 1185 with three-term progressions and density at least one eighth.
The construction uses the second difference of a quadratic modulo the integers.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185Wanted

open Filter

/-- **Erdős Problem 1185: progressions with difference in a difference set.** This is the
statement that for every real $\delta > 0$ and every natural number $k \ge 3$ there is a natural
number $m \ge 1$ such that for all sufficiently large natural numbers $N$, whenever $A$ and $B$
are subsets of $\{1, \dots, N\}$ with $|A| \ge \delta N$ and $|B| \ge m$, there are natural
numbers $a$ and $d > 0$ such that $b_1 = b_2 + d$ for some $b_1, b_2 \in B$ and $a + i d \in A$
for every natural number $i < k$; that is, $A$ contains the $k$-term arithmetic progression
$a, a + d, \dots, a + (k - 1) d$, whose common difference $d$ is positive and lies in $B - B$. -/
def progressionWithDifferenceInDifferenceSet : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ m : ℕ, 1 ≤ m ∧ ∀ᶠ N : ℕ in atTop,
    ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N → δ * N ≤ A.card → m ≤ B.card →
      ∃ a d : ℕ, 0 < d ∧ (∃ b₁ ∈ B, ∃ b₂ ∈ B, b₂ + d = b₁) ∧ ∀ i < k, a + i * d ∈ A

/-- A real number lies within distance `ε` of an integer. -/
private def NearInteger (ε x : ℝ) : Prop :=
  ∃ z : ℤ, (z : ℝ) - ε < x ∧ x < (z : ℝ) + ε

/-- The quadratic coefficient can be chosen so the diagonal products are near
one eighth modulo one and the off-diagonal products are near zero. -/
private lemma exists_quadratic_coefficient (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : Finset ℕ) (q : ℚ), B.card = m ∧ (∀ b ∈ B, 0 < b) ∧
      ∀ x ∈ B, ∀ y ∈ B,
        NearInteger ε ((q : ℝ) * x * y - (if x = y then 1 / 8 else 0)) := by
  induction m generalizing ε with
  | zero =>
    exact ⟨∅, 0, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨B, q, hcard, hpos, hphase⟩ := ih (ε / 2) (by positivity)
    let M := B.sup id
    obtain ⟨L, hL⟩ := exists_nat_gt (max (M : ℝ) (M / (4 * ε)))
    let b := q.den * L
    have hLb : L ≤ b := by
      dsimp [b]
      exact Nat.le_mul_of_pos_left _ q.den_pos
    have hmax : max (M : ℝ) (M / (4 * ε)) < (b : ℝ) :=
      hL.trans_le (by exact_mod_cast hLb)
    have hMb : (M : ℝ) < (b : ℝ) := (le_max_left _ _).trans_lt hmax
    have hb : 0 < b := by exact_mod_cast (Nat.cast_nonneg (α := ℝ) M).trans_lt hMb
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hxb (x : ℕ) (hx : x ∈ B) : x < b := by
      have hxM : x ≤ M := Finset.le_sup (f := id) hx
      exact hxM.trans_lt (by exact_mod_cast hMb)
    have hbB : b ∉ B := fun h => (hxb b h).false
    -- The perturbation contributes exactly one eighth at the new diagonal.
    let r : ℚ := q + 1 / (8 * (b : ℚ) ^ 2)
    have hchange (x y : ℕ) :
        (r : ℝ) * x * y =
          (q : ℝ) * x * y + (x / (b : ℝ)) * (y / (b : ℝ)) / 8 := by
      dsimp [r]
      push_cast
      field_simp
    have herror (x y : ℕ) (hx : x ∈ B) (hy : y ≤ b) :
        0 ≤ (x / (b : ℝ)) * (y / (b : ℝ)) / 8 ∧
          (x / (b : ℝ)) * (y / (b : ℝ)) / 8 < ε / 2 := by
      have hxM : x ≤ M := Finset.le_sup (f := id) hx
      have hsmall : (M : ℝ) / (4 * ε) < (b : ℝ) := (le_max_right _ _).trans_lt hmax
      have hxratio : (x : ℝ) / b < 4 * ε := by
        apply (div_lt_iff₀ hbR).2
        calc
          (x : ℝ) ≤ M := by exact_mod_cast hxM
          _ < 4 * ε * (b : ℝ) := by
            rw [mul_comm]
            exact (div_lt_iff₀ (by positivity)).1 hsmall
      have hyratio : (y : ℝ) / b ≤ 1 := (div_le_one hbR).2 (by exact_mod_cast hy)
      refine ⟨by positivity, ?_⟩
      calc
        (x / (b : ℝ)) * (y / (b : ℝ)) / 8 ≤ (x / (b : ℝ)) * 1 / 8 := by
          gcongr
        _ < ε / 2 := by linarith only [hxratio]
    -- The old coefficient gives an integer whenever one factor is the new element.
    have hinteger (y : ℕ) :
        (q : ℝ) * b * y = ((q.num * (L : ℤ) * (y : ℤ) : ℤ) : ℝ) := by
      rw [Rat.cast_def q]
      dsimp [b]
      push_cast
      have hden : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
      field_simp
    have hmix (x : ℕ) (hx : x ∈ B) : NearInteger ε ((r : ℝ) * x * b) := by
      refine ⟨q.num * (L : ℤ) * (x : ℤ), ?_⟩
      have he := herror x b hx le_rfl
      rw [hchange, mul_right_comm (q : ℝ), hinteger]
      constructor <;> linarith only [hε, he.1, he.2]
    refine ⟨insert b B, r, by simp [hbB, hcard], ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hb
      · exact hpos x hx
    · intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hx <;>
        rcases Finset.mem_insert.mp hy with rfl | hy
      · refine ⟨q.num * (L : ℤ) * (b : ℤ), ?_⟩
        rw [ite_eq_left rfl, hchange, hinteger, div_self hbR.ne']
        constructor <;> linarith only [hε]
      · rw [ite_eq_right (hxb y hy).ne', sub_zero, mul_right_comm]
        exact hmix y hy
      · rw [ite_eq_right (hxb x hx).ne, sub_zero]
        exact hmix x hx
      · obtain ⟨z, hz₁, hz₂⟩ := hphase x hx y hy
        refine ⟨z, ?_⟩
        have he := herror x y hx (hxb y hy).le
        rw [hchange]
        constructor <;> linarith only [hε, hz₁, hz₂, he.1, he.2]

private lemma half_integer_difference {q : ℝ} {x y d : ℕ} (hd : y + d = x)
    (hx : NearInteger (1 / 64) (q * x * x - 1 / 8))
    (hy : NearInteger (1 / 64) (q * y * y - 1 / 8))
    (hxy : NearInteger (1 / 64) (q * x * y)) :
    NearInteger (1 / 8) (2 * q * (d : ℝ) ^ 2 - 1 / 2) := by
  obtain ⟨zx, hx₁, hx₂⟩ := hx
  obtain ⟨zy, hy₁, hy₂⟩ := hy
  obtain ⟨zxy, hxy₁, hxy₂⟩ := hxy
  have hdR : (x : ℝ) = (y : ℝ) + d := by exact_mod_cast hd.symm
  have hdiff : 2 * q * (d : ℝ) ^ 2 =
      2 * (q * x * x + q * y * y - 2 * (q * x * y)) := by
    rw [hdR]
    ring
  refine ⟨2 * (zx + zy - 2 * zxy), ?_⟩
  rw [hdiff]
  push_cast
  constructor <;> linarith only [hx₁, hx₂, hy₁, hy₂, hxy₁, hxy₂]

/-- The color of `n` specifies which eighth of the unit interval contains
the fractional part of `q * n ^ 2`. -/
private noncomputable def quadraticColor (q : ℝ) (n : ℕ) : ℕ :=
  ⌊8 * Int.fract (q * (n : ℝ) ^ 2)⌋₊

private lemma quadraticColor_lt (q : ℝ) (n : ℕ) : quadraticColor q n < 8 := by
  apply (Nat.floor_lt' (by decide)).2
  simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (q * (n : ℝ) ^ 2))
    (show (0 : ℝ) < 8 by norm_num)

private lemma integer_difference_of_same_color {q : ℝ} {a d c : ℕ}
    (h₀ : quadraticColor q a = c) (h₁ : quadraticColor q (a + d) = c)
    (h₂ : quadraticColor q (a + 2 * d) = c) :
    NearInteger (1 / 4) (2 * q * (d : ℝ) ^ 2) := by
  let f (n : ℕ) : ℝ := q * (n : ℝ) ^ 2
  have hbound (n : ℕ) (hn : quadraticColor q n = c) :
      (c : ℝ) ≤ 8 * Int.fract (f n) ∧ 8 * Int.fract (f n) < (c : ℝ) + 1 :=
    (Nat.floor_eq_iff (mul_nonneg (by norm_num) (Int.fract_nonneg (f n)))).1 hn
  obtain ⟨h₀lo, h₀hi⟩ := hbound a h₀
  obtain ⟨h₁lo, h₁hi⟩ := hbound (a + d) h₁
  obtain ⟨h₂lo, h₂hi⟩ := hbound (a + 2 * d) h₂
  have hdiff : 2 * q * (d : ℝ) ^ 2 = f a - 2 * f (a + d) + f (a + 2 * d) := by
    dsimp [f]
    push_cast
    ring
  refine ⟨⌊f a⌋ - 2 * ⌊f (a + d)⌋ + ⌊f (a + 2 * d)⌋, ?_⟩
  rw [hdiff]
  push_cast
  simp only [Int.fract] at h₀lo h₀hi h₁lo h₁hi h₂lo h₂hi
  constructor <;> linarith only [h₀lo, h₀hi, h₁lo, h₁hi, h₂lo, h₂hi]

private lemma incompatible_differences {x : ℝ} (h : NearInteger (1 / 4) x)
    (h' : NearInteger (1 / 8) (x - 1 / 2)) : False := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  obtain ⟨w, hw₁, hw₂⟩ := h'
  have hlo : 0 < z - w := by
    exact_mod_cast (show (0 : ℝ) < (z : ℝ) - (w : ℝ) by linarith only [hz₂, hw₁])
  have hhi : z - w < 1 := by
    exact_mod_cast (show (z : ℝ) - (w : ℝ) < 1 by linarith only [hz₁, hw₂])
  omega

/--
**Erdős Problem 1185 is false.** The following statement is false: for every real $\delta > 0$
and every natural number $k \ge 3$ there is a natural number $m \ge 1$ such that for all
sufficiently large natural numbers $N$, whenever $A$ and $B$ are subsets of $\{1, \dots, N\}$
with $|A| \ge \delta N$ and $|B| \ge m$, there are natural numbers $a$ and $d > 0$ such that
$b_1 = b_2 + d$ for some $b_1, b_2 \in B$ and $a + i d \in A$ for every natural number $i < k$.

The answer is negative already for $k = 3$: Furstenberg gave an infinite set $B$ such that
$B - B$ is not $2$-intersective, that is, some set of positive density contains no $3$-term
progression with common difference in $B - B$; truncating both sets at $N$ gives
counterexamples with $|B \cap [1, N]|$ unbounded.

Source: T. F. Bloom, Erdős Problems,
Problem #1185, https://www.erdosproblems.com/1185 (status SOLVED); resolution: H. Furstenberg,
Recurrence in Ergodic Theory and Combinatorial Number Theory, Princeton University Press (1981),
erdosproblems.com/1185: false already at k = 3, since Furstenberg gave an infinite set B such that B
- B is not 2-intersective.
-/
public theorem progressionWithDifferenceInDifferenceSet_refuted :
    ¬ progressionWithDifferenceInDifferenceSet := by
  intro h
  obtain ⟨m, -, hN⟩ := h (1 / 8) (by norm_num) 3 (by decide)
  obtain ⟨B, q, hcard, hpos, hphase⟩ := exists_quadratic_coefficient m (1 / 64) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hN
  let N := max N₀ (B.sup id)
  have hB : B ⊆ Finset.Icc 1 N := by
    intro b hb
    exact Finset.mem_Icc.2 ⟨hpos b hb, (Finset.le_sup (f := id) hb).trans (le_max_right _ _)⟩
  have hsize : (Finset.range 8).card • ((1 / 8 : ℝ) * N) ≤ ((Finset.Icc 1 N).card : ℝ) := by
    simp [nsmul_eq_mul]
  obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Finset.Icc 1 N) (t := Finset.range 8) (f := quadraticColor q)
    (fun n _ => Finset.mem_range.2 (quadraticColor_lt q n))
    (Finset.nonempty_range_iff.2 (by decide)) hsize
  let A := (Finset.Icc 1 N).filter (fun n => quadraticColor q n = c)
  obtain ⟨a, d, hd, ⟨x, hx, y, hy, hxy⟩, hap⟩ :=
    hN₀ N (le_max_left _ _) A B (Finset.filter_subset _ _) hB hc hcard.ge
  have hne : x ≠ y := by
    omega
  have hcolor (i : ℕ) (hi : i < 3) : quadraticColor q (a + i * d) = c :=
    (Finset.mem_filter.1 (hap i hi)).2
  apply incompatible_differences
  · exact integer_difference_of_same_color
      (by simpa using hcolor 0 (by decide)) (by simpa using hcolor 1 (by decide))
      (hcolor 2 (by decide))
  · exact half_integer_difference hxy
      (by simpa using hphase x hx x hx)
      (by simpa using hphase y hy y hy)
      (by simpa only [ite_eq_right hne, sub_zero] using hphase x hx y hy)

end MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185Wanted
