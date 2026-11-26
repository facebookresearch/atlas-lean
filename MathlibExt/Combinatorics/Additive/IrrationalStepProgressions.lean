/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Int.Interval

/-!
# Rational starts and irrational steps in arithmetic progressions

We also compare sums and differences of an initial integer interval and a separated
irrational-step progression by counting their images in the integer lattice.
-/

namespace MetaMathlibExt

/-- **Nonnegative integer points for a rational start and an irrational difference.** Let $x$ be
a rational number that is not a nonnegative integer, and let $d$ be an irrational real number.
Then $x + id$ is not a nonnegative integer for any natural number $i$, and $2x + jd$ is not a
nonnegative integer for any natural number $j \ge 1$.

As printed, the paper's Lemma 18 (ii) also claims $2x + 0 \cdot d \notin \mathbb{N}$, which fails
at $x = 1/2$ (where $2x = 1$); the paper's proof ("then $d \in \mathbb{Q}$") covers only $j \ge 1$,
and the condition that the denominator of $x$ be at least $3$ is attached only to part (iii).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem add_mul_not_mem_nat_of_rat_of_irrational (x d : ℝ)
    (hx : x ∈ Set.range ((↑) : ℚ → ℝ)) (hxn : x ∉ Set.range ((↑) : ℕ → ℝ)) (hd : Irrational d)
    (i j : ℕ) (hj : 1 ≤ j) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  obtain ⟨q, rfl⟩ := hx
  have not_mem (a : ℚ) {k : ℕ} (hk : k ≠ 0) :
      (a : ℝ) + k * d ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    exact ((hd.natCast_mul hk).ratCast_add a).ne_nat n hn.symm
  constructor
  · by_cases hi : i = 0
    · simpa [hi] using hxn
    · exact not_mem q hi
  · simpa using not_mem (2 * q) (Nat.ne_of_gt hj)

/-- **At most one nonnegative integer point on a progression with irrational difference.** Let $x$
and $d$ be real numbers with $d$ irrational. If $i$ and $j$ are natural numbers such that $x + id$
and $x + jd$ are both nonnegative integers, then $i = j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 8
(`integers-2026-A58-lem-8`). -/
public theorem eq_of_add_mul_irrational_mem_nat (x d : ℝ) (hirr : Irrational d) (i j : ℕ)
    (hi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  by_contra hij
  have hsub : (i : ℤ) - (j : ℤ) ≠ 0 := fun h => hij (Int.ofNat.inj (sub_eq_zero.mp h))
  have heq : (↑((i : ℤ) - (j : ℤ)) : ℝ) * d = ↑((a : ℤ) - (b : ℤ)) := by
    simpa only [Int.cast_sub, Int.cast_natCast, sub_mul, add_sub_add_left_eq_sub] using
      (congrArg₂ (fun y z : ℝ => y - z) ha hb).symm
  exact (hirr.intCast_mul hsub).ne_int _ heq

open scoped Pointwise

@[expose] public section

/-- **Initial integer interval.** For a natural number $n$, $I_n = \{0, 1, \ldots, n - 1\}$ is
the set of the first $n$ natural numbers, viewed as a finite set of real numbers; $I_0$ is empty.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realIntervalSet (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun i : ℕ => (i : ℝ)

/-- **Size of the interval $I_n$.** For every natural number $n$, the set
$I_n = \{0, 1, \dots, n - 1\}$ of real numbers has exactly $n$ elements.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realIntervalSet (n : ℕ) : (realIntervalSet n).card = n := by
  rw [realIntervalSet, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- **Finite arithmetic progression.** For a real number $x$, a natural number $m$ and a real
number $d$, $J(x, m, d)$ is the finite set of real numbers
$\{x + i d : i = 0, 1, \ldots, m\}$, that is, $x, x + d, \ldots, x + m d$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realAPSet (x : ℝ) (m : ℕ) (d : ℝ) : Finset ℝ :=
  (Finset.range (m + 1)).image fun i : ℕ => x + i * d

/-- **Size of the progression $J(x, m, d)$.** For a real number $x$, a natural number $m$ and a
real number $d \ne 0$, the progression $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$ has exactly
$m + 1$ elements.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realAPSet (x : ℝ) (m : ℕ) {d : ℝ} (hd : d ≠ 0) :
    (realAPSet x m d).card = m + 1 := by
  rw [realAPSet, Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  have : (i : ℝ) * d = j * d := by simpa using h
  exact_mod_cast mul_right_cancel₀ hd this

/-- **MSTD set.** A finite set $A$ of real numbers is an *MSTD set* (more sums than differences)
when its difference set has fewer elements than its sumset: $|A - A| < |A + A|$, where
$A + A = \{a + b : a, b \in A\}$ and $A - A = \{a - b : a, b \in A\}$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
def IsMSTDSet (A : Finset ℝ) : Prop :=
  (A - A).card < (A + A).card

/-- **A single point is not an MSTD set.** For every real number $a$, the set $\{a\}$ is not an
MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem not_isMSTDSet_singleton (a : ℝ) : ¬ IsMSTDSet {a} := by
  simp [IsMSTDSet]

end

private noncomputable def evalStep (d : ℝ) : (ℤ × ℤ) →+ ℝ where
  toFun p := (p.1 : ℝ) + (p.2 : ℝ) * d
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, add_mul]
    ac_rfl

private theorem evalStep_injective {d : ℝ} (hd : Irrational d) :
    Function.Injective (evalStep d) := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  change (a : ℝ) + (b : ℝ) * d = (c : ℝ) + (e : ℝ) * d at h
  have hbe : b = e := by
    by_contra hne
    apply (hd.intCast_mul (sub_ne_zero.mpr hne)).ne_int (c - a)
    simp only [Int.cast_sub, sub_mul]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h)
  subst e
  exact Prod.ext (by exact_mod_cast add_right_cancel h) rfl

private def horizontal (a : ℤ) : Finset (ℤ × ℤ) := Finset.Icc 0 a ×ˢ {0}
private def vertical (b x : ℤ) : Finset (ℤ × ℤ) := {x} ×ˢ Finset.Icc 0 b

private theorem lattice_card_add_le_card_sub (n m x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hx : n + 1 ≤ x) :
    let T := horizontal ((n : ℤ) - 1) ∪ vertical m x
    (T + T).card ≤ (T - T).card := by
  let a : ℤ := (n : ℤ) - 1
  let b : ℤ := m
  let c : ℤ := x
  let T := horizontal a ∪ vertical b c
  change (T + T).card ≤ (T - T).card
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  have hc : a < c := by dsimp [a, c]; omega
  let s₀ : Finset (ℤ × ℤ) := Finset.Icc 0 (2 * a) ×ˢ {0}
  let s₁ : Finset (ℤ × ℤ) := Finset.Icc c (c + a) ×ˢ Finset.Icc 0 b
  let s₂ : Finset (ℤ × ℤ) := {2 * c} ×ˢ Finset.Icc 0 (2 * b)
  -- Every sum comes from two horizontal points, one of each, or two vertical points.
  have hs : T + T ⊆ (s₀ ∪ s₁) ∪ s₂ := by
    rintro _ hp
    obtain ⟨⟨i, j⟩, hi, ⟨k, l⟩, hk, rfl⟩ := Finset.mem_add.mp hp
    simp only [T, horizontal, vertical, Finset.mem_union, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_singleton] at hi hk
    simp only [s₀, s₁, s₂, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton, Prod.fst_add, Prod.snd_add]
    rcases hi with hi | hi <;> rcases hk with hk | hk <;> omega
  have hs₀ : s₀.card = 2 * n - 1 := by
    simp only [s₀, a, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Icc]
    omega
  have hs₁ : s₁.card = n * (m + 1) := by
    simp only [s₁, Finset.card_product, Int.card_Icc]
    congr 1; dsimp [a, b]; omega
  have hs₂ : s₂.card = 2 * m + 1 := by
    simp only [s₂, b, Finset.card_product, Finset.card_singleton, one_mul, Int.card_Icc]
    omega
  have hsum : (T + T).card ≤ 2 * n - 1 + n * (m + 1) + (2 * m + 1) := by
    have h := Finset.card_le_card hs
    have h01 := Finset.card_union_le s₀ s₁
    have h012 := Finset.card_union_le (s₀ ∪ s₁) s₂
    omega
  let d₀ : Finset (ℤ × ℤ) := Finset.Icc (-a) a ×ˢ {0}
  let d₁ : Finset (ℤ × ℤ) := {0} ×ˢ (Finset.Icc (-b) b).erase 0
  let d₂ : Finset (ℤ × ℤ) := Finset.Icc (c - a) c ×ˢ Finset.Icc 1 b
  let d₃ : Finset (ℤ × ℤ) := Finset.Icc (-c) (a - c) ×ˢ Finset.Icc (-b) (-1)
  have memH (i : ℤ) (h₀ : 0 ≤ i) (h₁ : i ≤ a) : (i, 0) ∈ T :=
    Finset.mem_union_left _ (Finset.mk_mem_product (Finset.mem_Icc.mpr ⟨h₀, h₁⟩)
      (Finset.mem_singleton_self 0))
  have memV (j : ℤ) (h₀ : 0 ≤ j) (h₁ : j ≤ b) : (c, j) ∈ T :=
    Finset.mem_union_right _ (Finset.mk_mem_product (Finset.mem_singleton_self c)
      (Finset.mem_Icc.mpr ⟨h₀, h₁⟩))
  -- Count only cross-differences with nonzero step index; these cannot meet either axis.
  have hdiff : (d₀ ∪ d₁) ∪ (d₂ ∪ d₃) ⊆ T - T := by
    rintro ⟨i, j⟩ hp
    simp only [d₀, d₁, d₂, d₃, Finset.mem_union, Finset.mem_product, Finset.mem_erase,
      Finset.mem_Icc, Finset.mem_singleton] at hp
    rcases hp with (h | h) | (h | h)
    · refine Finset.mem_sub.mpr ⟨_, memH (max i 0) (by omega) (by omega), _,
        memH (max (-i) 0) (by omega) (by omega), ?_⟩
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · refine Finset.mem_sub.mpr ⟨_, memV (max j 0) (by omega) (by omega), _,
        memV (max (-j) 0) (by omega) (by omega), ?_⟩
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · refine Finset.mem_sub.mpr ⟨_, memV j (by omega) (by omega), _,
        memH (c - i) (by omega) (by omega), ?_⟩
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · refine Finset.mem_sub.mpr ⟨_, memH (i + c) (by omega) (by omega), _,
        memV (-j) (by omega) (by omega), ?_⟩
      apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hdisj₀ : Disjoint d₀ d₁ := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hi hj
    simp only [d₀, d₁, Finset.mem_product, Finset.mem_singleton, Finset.mem_erase,
      Finset.mem_Icc] at hi hj
    omega
  have hdisj₁ : Disjoint d₂ d₃ := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hi hj
    simp only [d₂, d₃, Finset.mem_product, Finset.mem_Icc] at hi hj
    omega
  have hdisj₂ : Disjoint (d₀ ∪ d₁) (d₂ ∪ d₃) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hi hj
    simp only [d₀, d₁, d₂, d₃, Finset.mem_union, Finset.mem_product, Finset.mem_erase,
      Finset.mem_Icc, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  have hd₀ : d₀.card = 2 * n - 1 := by
    simp only [d₀, a, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Icc]
    omega
  have hz : (0 : ℤ) ∈ Finset.Icc (-b) b := Finset.mem_Icc.mpr ⟨by omega, hb⟩
  have hd₁ : d₁.card = 2 * m := by
    simp only [d₁, Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_erase_of_mem hz, Int.card_Icc, b]
    omega
  have hd₂ : d₂.card = n * m := by
    simp only [d₂, Finset.card_product, Int.card_Icc]
    congr 1 <;> dsimp [a, b] <;> omega
  have hd₃ : d₃.card = n * m := by
    simp only [d₃, Finset.card_product, Int.card_Icc]
    congr 1 <;> dsimp [a, b] <;> omega
  have hsub := Finset.card_le_card hdiff
  rw [Finset.card_union_of_disjoint hdisj₂, Finset.card_union_of_disjoint hdisj₀,
    Finset.card_union_of_disjoint hdisj₁, hd₀, hd₁, hd₂, hd₃] at hsub
  have hnm := Nat.mul_le_mul_left n hm
  rw [Nat.mul_comm n 2, two_mul] at hnm
  rw [Nat.mul_add, Nat.mul_one] at hsum
  omega

private theorem image_horizontal (n : ℕ) (d : ℝ) :
    (horizontal ((n : ℤ) - 1)).image (evalStep d) = realIntervalSet n := by
  ext z
  constructor
  · intro h
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp h
    simp only [horizontal, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hij
    obtain ⟨hi, rfl⟩ := hij
    have hnat : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi.1
    exact Finset.mem_image.mpr ⟨i.toNat, Finset.mem_range.mpr (by omega), by
      change (i.toNat : ℝ) = (i : ℝ) + (0 : ℤ) * d
      rw [Int.cast_zero, zero_mul, add_zero]
      exact_mod_cast hnat⟩
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    have hi' := Finset.mem_range.mp hi
    refine Finset.mem_image.mpr ⟨((i : ℤ), 0), ?_, ?_⟩
    · simp only [horizontal, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
      exact ⟨⟨by omega, by omega⟩, trivial⟩
    · simp [evalStep]

private theorem image_vertical (m x : ℕ) (d : ℝ) :
    (vertical (m : ℤ) (x : ℤ)).image (evalStep d) = realAPSet (x : ℝ) m d := by
  ext z
  constructor
  · intro h
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp h
    simp only [vertical, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hij
    obtain ⟨rfl, hj⟩ := hij
    have hnat : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj.1
    have hjR : (j.toNat : ℝ) = j := by exact_mod_cast hnat
    exact Finset.mem_image.mpr ⟨j.toNat, Finset.mem_range.mpr (by omega), by
      simp only [evalStep, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_natCast, hjR]⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hj' := Finset.mem_range.mp hj
    refine Finset.mem_image.mpr ⟨((x : ℤ), (j : ℤ)), ?_, ?_⟩
    · simp only [vertical, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
      exact ⟨trivial, by omega⟩
    · simp [evalStep]

-- Retain the named positivity hypothesis of the source statement.
set_option linter.unusedVariables false in
/-- **Interval plus irrational-step progression with natural start is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$ and $x \ge n + 1$, and a positive
irrational real number $d$, the set $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 4
(`integers-2026-A58-lem-4`). -/
public theorem not_isMSTDSet_intervalAP_irrational_diff (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hirr : Irrational d)
    (hd : 0 < d) (hx : n + 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d) := by
  have hSub (s : Finset (ℤ × ℤ)) :
      s.image (evalStep d) - s.image (evalStep d) = (s - s).image (evalStep d) := by
    simp only [sub_eq_add_neg, Finset.image_add, Finset.image_neg]
  rw [IsMSTDSet, ← image_horizontal n d, ← image_vertical m x d, ← Finset.image_union,
    ← Finset.image_add (evalStep d), hSub,
    Finset.card_image_of_injective _ (evalStep_injective hirr),
    Finset.card_image_of_injective _ (evalStep_injective hirr), not_lt]
  exact lattice_card_add_le_card_sub n m x hn hm hx

end MetaMathlibExt
