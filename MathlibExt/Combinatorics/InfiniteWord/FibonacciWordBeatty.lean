/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
import all MathlibExt.Combinatorics.Words.CobhamUniformMorphism
import all MathlibExt.NumberTheory.Beatty.CountIncrement

/-!
# Beatty positions in the Fibonacci word and its morphic images

At positive one-based indices, this module describes the zeros of the infinite Fibonacci word and
of its image under `0 ↦ 10, 1 ↦ 01`, and the ones of its image under `0 ↦ 1, 1 ↦ 00`. It also
shows that every integer omitted by the golden-ratio Beatty sequence has both neighbors in it.

## References

* William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other Sequences*,
  INTEGERS 25 (2025), Article A29, pp. 1–17, Definition 1 and Lemma 2 (pp. 4–5).
* Kenneth B. Stolarsky, *Beatty Sequences, Continued Fractions, and Certain Shift Operators*,
  Canadian Mathematical Bulletin 19 (4) (1976), pp. 473–482, Theorem 1, credited by Wesley for
  the Beatty positions in the Fibonacci word (with the letters complemented).
* Michel Dekking, proof in OEIS [A287772](https://oeis.org/A287772), 28 December 2017,
  credited by Wesley for the positions of the ones in the image under `0 ↦ 1, 1 ↦ 00`.
* The formal proof uses `fibMorph_append` and `fibInf_agrees` from
  `MathlibExt.Combinatorics.InfiniteWord.FibonacciWord`, `getElem?_flatMap_uniform` from
  `MathlibExt.Combinatorics.Words.CobhamUniformMorphism`, and `strictMono_beattySeq` from
  `MathlibExt.NumberTheory.Beatty.CountIncrement`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Thue–Morse morphism $\mu$.** The morphism $\mu$ on binary words sends the letter $0$ to
the word $10$ and the letter $1$ to the word $01$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def thueMorseMorphism : Bool → List Bool
  | false => [true, false]
  | true => [false, true]

/-- **The morphism $\nu$.** The morphism $\nu$ is given on the letters $0$ and $1$ by
$\nu(0) = 1$ and $\nu(1) = 00$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def fibonacciNuMorphism : Bool → List Bool
  | false => [true]
  | true => [false, false]

/-- **Wesley's word $S$.** Let $\mu$ be the morphism of binary words with $0 \mapsto 10$ and
$1 \mapsto 01$, and let $f_0 = 0$, $f_1 = 01$, $f_2 = 010$, $\dots$ be the finite Fibonacci words.
The word $S$ is the infinite binary word, indexed from $0$, whose letter at index $n$ is the
letter at index $n$ of $\mu(f_{n+2})$.

Since each $f_k$ is a prefix of $f_{k+1}$, $S = \mu(F_\infty) = 1001101001\dots$, where
$F_\infty = 010010100\dots$ is the infinite Fibonacci word.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordS (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap thueMorseMorphism).getD n false

/-- **Wesley's word $T$.** Let $\nu$ be the morphism of binary words with $0 \mapsto 1$ and
$1 \mapsto 00$, and let $f_0 = 0$, $f_1 = 01$, $f_2 = 010$, $\dots$ be the finite Fibonacci words.
The word $T$ is the infinite binary word, indexed from $0$, whose letter at index $n$ is the
letter at index $n$ of $\nu(f_{n+2})$.

Since each $f_k$ is a prefix of $f_{k+1}$, $T = \nu(F_\infty) = 1001100100\dots$, where
$F_\infty = 010010100\dots$ is the infinite Fibonacci word.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
def wesleyWordT (n : ℕ) : Bool :=
  ((fibWord (n + 2)).flatMap fibonacciNuMorphism).getD n false

end

open scoped goldenRatio

namespace FibonacciWordBeatty

-- The number of positive Beatty positions strictly before the one-based position `k + 1`.
private noncomputable def zeroCount (k : ℕ) : ℕ := ⌊((k : ℝ) + 1) / φ⌋₊

private noncomputable def beattyLetter (k : ℕ) : Bool :=
  decide (zeroCount (k + 1) = zeroCount k)

private theorem zeroCount_cast (k : ℕ) : (zeroCount k : ℤ) = ⌊((k : ℝ) + 1) / φ⌋ :=
  Int.natCast_floor_eq_floor (by positivity)

private theorem one_div_lt_one : (1 : ℝ) / φ < 1 := by
  rw [div_lt_iff₀ Real.goldenRatio_pos, one_mul]
  exact Real.one_lt_goldenRatio

private theorem zeroCount_zero : zeroCount 0 = 0 := by
  simpa [zeroCount] using one_div_lt_one

private theorem zeroCount_succ (k : ℕ) :
    zeroCount (k + 1) = zeroCount k + if beattyLetter k then 0 else 1 := by
  have hfloor : ⌊(1 : ℝ) / φ⌋ = 0 :=
    Int.floor_eq_iff.mpr ⟨by simpa only [Int.cast_zero] using (show 0 ≤ (1 : ℝ) / φ by positivity),
      by simpa using one_div_lt_one⟩
  have h := Int.floor_add_eq_or (((k : ℝ) + 1) / φ) (1 / φ)
  rw [← add_div, hfloor, add_zero, ← zeroCount_cast k] at h
  rw [← show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 1 + 1 by simp,
    ← zeroCount_cast (k + 1)] at h
  rcases h with h | h
  · have he : zeroCount (k + 1) = zeroCount k := by exact_mod_cast h
    simp [beattyLetter, he]
  · have he : zeroCount (k + 1) = zeroCount k + 1 := by exact_mod_cast h
    simp [beattyLetter, he]

-- The next interval contains a Beatty position exactly when the counter increases.
private theorem beattyIndex_iff (k : ℕ) (m : ℤ) :
    beattySeq φ m = (k : ℤ) + 1 ↔ beattyLetter k = false ∧ m = (zeroCount k : ℤ) + 1 := by
  have hk : Irrational (((k : ℝ) + 1) / φ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.goldenRatio_irrational.natCast_div (m := k + 1) (Nat.succ_ne_zero k)
  have hks : Irrational (((k : ℝ) + 1 + 1) / φ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.goldenRatio_irrational.natCast_div (m := k + 1 + 1) (Nat.succ_ne_zero (k + 1))
  rw [beattySeq, Int.floor_eq_iff]
  push_cast
  rw [← div_le_iff₀ Real.goldenRatio_pos, ← lt_div_iff₀ Real.goldenRatio_pos]
  have hlo : (((k : ℝ) + 1) / φ ≤ m) ↔ (zeroCount k : ℤ) < m := by
    rw [zeroCount_cast, Int.floor_lt]
    exact ⟨fun h ↦ lt_of_le_of_ne h (hk.ne_int m), le_of_lt⟩
  have hhi : ((m : ℝ) < ((k : ℝ) + 1 + 1) / φ) ↔ m ≤ (zeroCount (k + 1) : ℤ) := by
    rw [zeroCount_cast, Int.le_floor]
    push_cast
    exact ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h (hks.ne_int m).symm⟩
  rw [hlo, hhi]
  have hs := zeroCount_succ k
  cases h : beattyLetter k <;> simp [h] at hs ⊢ <;> omega

private theorem beattyLetter_eq_false_iff (k : ℕ) :
    beattyLetter k = false ↔ ∃ m : ℤ, (k : ℤ) + 1 = beattySeq φ m := by
  simp only [eq_comm (a := (k : ℤ) + 1), beattyIndex_iff, exists_eq_right]

-- The `k`-th substitution block starts at the zero-based Beatty position for `k + 1`.
private noncomputable def fibBlockStart (k : ℕ) : ℕ := k + zeroCount k

private theorem beattySeq_eq_blockStart (k : ℕ) :
    beattySeq φ ((k : ℤ) + 1) = (fibBlockStart k : ℤ) + 1 := by
  have hφ : φ = 1 + 1 / φ := by
    rw [one_div, Real.inv_goldenRatio, ← sub_eq_add_neg]
    exact Real.one_sub_goldenRatio.symm
  have hmul : ((k : ℝ) + 1) * φ = (((k : ℤ) + 1 : ℤ) : ℝ) + ((k : ℝ) + 1) / φ := by
    calc
      _ = ((k : ℝ) + 1) * (1 + 1 / φ) := congrArg (((k : ℝ) + 1) * ·) hφ
      _ = _ := by push_cast; rw [mul_add, mul_one, mul_one_div]
  simp only [beattySeq, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [hmul, Int.floor_intCast_add, ← zeroCount_cast]
  simp only [fibBlockStart, Nat.cast_add]
  omega

private theorem beattyLetter_blockStart (k : ℕ) : beattyLetter (fibBlockStart k) = false :=
  (beattyIndex_iff (fibBlockStart k) ((k : ℤ) + 1)).mp (beattySeq_eq_blockStart k) |>.1

private theorem fibBlockStart_succ (k : ℕ) :
    fibBlockStart (k + 1) = fibBlockStart k + (fibSubst (beattyLetter k)).length := by
  have hs := zeroCount_succ k
  cases h : beattyLetter k <;> simp [fibSubst, fibBlockStart, h] at hs ⊢ <;> omega

private theorem beattyLetter_blockStart_add_one (k : ℕ) (hk : beattyLetter k = false) :
    beattyLetter (fibBlockStart k + 1) = true := by
  by_contra! hn
  have hb : beattyLetter (fibBlockStart k + 1) = false := by
    cases h : beattyLetter (fibBlockStart k + 1) <;> simp_all
  obtain ⟨m, hm⟩ := (beattyLetter_eq_false_iff _).mp hb
  have hmono : StrictMono (beattySeq φ) :=
    beatty_card_compl_between_succ_sub.strictMono_beattySeq Real.one_lt_goldenRatio.le
  have h₀ := beattySeq_eq_blockStart k
  have h₁ := beattySeq_eq_blockStart (k + 1)
  rw [fibBlockStart_succ, hk] at h₁
  simp only [fibSubst, List.length_cons, List.length_nil, Nat.cast_add,
    Nat.cast_one] at hm h₁
  have hl := hmono.lt_iff_lt.mp (show beattySeq φ ((k : ℤ) + 1) < beattySeq φ m by omega)
  have hr := hmono.lt_iff_lt.mp (show beattySeq φ m < beattySeq φ (((k + 1 : ℕ) : ℤ) + 1) by
    push_cast at h₁ ⊢
    omega)
  omega

private noncomputable abbrev beattyPrefix (k : ℕ) : List Bool :=
  List.ofFn (fun i : Fin k ↦ beattyLetter i)

private theorem fibMorph_beattyPrefix (k : ℕ) :
    fibMorph (beattyPrefix k) = beattyPrefix (fibBlockStart k) := by
  induction k with
  | zero => simp [fibBlockStart, zeroCount_zero, fibMorph]
  | succ k ih =>
    rw [show beattyPrefix (k + 1) = beattyPrefix k ++ [beattyLetter k] from List.ofFn_succ_last,
      fibMorph_append, ih, fibBlockStart_succ]
    simp only [fibMorph, List.append_nil]
    change _ = List.ofFn (n := fibBlockStart k + (fibSubst (beattyLetter k)).length) _
    rw [List.ofFn_add]
    congr 1
    cases h : beattyLetter k
    · simp [fibSubst, List.ofFn_succ, beattyLetter_blockStart,
        beattyLetter_blockStart_add_one k h]
    · simp [fibSubst, List.ofFn_succ, beattyLetter_blockStart]

private theorem fibWord_eq_beattyPrefix (m : ℕ) : fibWord m = beattyPrefix (fibWord m).length := by
  induction m with
  | zero =>
    have hb := beattyLetter_blockStart 0
    simpa [fibWord, List.ofFn_succ, fibBlockStart, zeroCount_zero] using hb
  | succ m ih =>
    have he : fibWord (m + 1) = beattyPrefix (fibBlockStart (fibWord m).length) :=
      calc
        _ = fibMorph (fibWord m) := rfl
        _ = fibMorph (beattyPrefix (fibWord m).length) := congrArg fibMorph ih
        _ = _ := fibMorph_beattyPrefix _
    have hl := congrArg List.length he
    simp only [List.length_ofFn] at hl
    exact he.trans (congrArg beattyPrefix hl.symm)

private theorem fibInf_eq_beattyLetter (k : ℕ) : fibInf k = beattyLetter k := by
  have hk := fibInf_bound k
  rw [← fibInf_agrees _ _ hk, fibWord_eq_beattyPrefix (k + 2)]
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

private theorem beattySeq_succ_le (m : ℤ) : beattySeq φ (m + 1) ≤ beattySeq φ m + 2 := by
  simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
  calc
    _ ≤ ⌊(m : ℝ) * φ + (2 : ℝ)⌋ :=
      Int.floor_mono (add_le_add_right Real.goldenRatio_lt_two.le _)
    _ = _ := by simp

private theorem beatty_missing_neighbors (n : ℤ) (hn : ∀ m : ℤ, n ≠ beattySeq φ m) :
    (∃ m' : ℤ, n + 1 = beattySeq φ m') ∧ ∃ m'' : ℤ, n - 1 = beattySeq φ m'' := by
  let m := ⌈(n : ℝ) / φ⌉
  have h₁ : n ≤ beattySeq φ m :=
    Int.le_floor.mpr ((div_le_iff₀ Real.goldenRatio_pos).mp (Int.le_ceil _))
  have h₂ : beattySeq φ (m - 1) < n := by
    apply Int.floor_lt.mpr
    rw [← lt_div_iff₀ Real.goldenRatio_pos, Int.cast_sub, Int.cast_one]
    change (⌈(n : ℝ) / φ⌉ : ℝ) - 1 < _
    linarith [Int.ceil_lt_add_one ((n : ℝ) / φ)]
  have hgap := beattySeq_succ_le (m - 1)
  rw [sub_add_cancel] at hgap
  have hne := hn m
  exact ⟨⟨m, by omega⟩, ⟨m - 1, by omega⟩⟩

private theorem wesleyWordS_get (i j : ℕ) (hj : j < 2) :
    wesleyWordS (2 * i + j) = (thueMorseMorphism (fibInf i)).getD j false := by
  have hlen (b : Bool) : (thueMorseMorphism b).length = 2 := by cases b <;> rfl
  have hi : i < (fibWord (2 * i + j + 2)).length := by
    have := fibInf_bound (2 * i + j)
    omega
  have h := getElem?_flatMap_uniform hlen (fibWord (2 * i + j + 2)) i j hj
  rw [getElem?_pos (fibWord (2 * i + j + 2)) i hi, Option.bind_some,
    ← List.getD_eq_getElem _ false hi, fibInf_agrees _ _ hi] at h
  rw [wesleyWordS, List.getD_eq_getElem?_getD, h, ← List.getD_eq_getElem?_getD]

private theorem wesleyWordS_beatty (k : ℕ) : wesleyWordS k = false ↔
    (Even (k + 1) ∧ ∃ m : ℤ, (((k + 1) / 2 : ℕ) : ℤ) = beattySeq φ m) ∨
      (Odd (k + 1) ∧ ∀ m : ℤ, ((((k + 1) + 1) / 2 : ℕ) : ℤ) ≠ beattySeq φ m) := by
  have heq : k = 2 * (k / 2) + k % 2 := by omega
  conv_lhs => rw [heq, wesleyWordS_get _ _ (by omega), fibInf_eq_beattyLetter]
  have hdiv : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
  rw [hdiv]
  by_cases h : k % 2 = 0
  · have ho : Odd (k + 1) := Nat.odd_iff.mpr (by omega)
    have hne : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr ho
    rw [h]
    simp only [hne, false_and, false_or, ho, true_and, Nat.cast_add, Nat.cast_one, ← not_exists,
      ← beattyLetter_eq_false_iff]
    cases beattyLetter (k / 2) <;> decide
  · have hm : k % 2 = 1 := by omega
    have he : Even (k + 1) := Nat.even_iff.mpr (by omega)
    have hno : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr he
    have hdiv' : (k + 1) / 2 = k / 2 + 1 := by omega
    rw [hm, hdiv']
    simp only [hno, false_and, or_false, he, true_and, Nat.cast_add, Nat.cast_one,
      ← beattyLetter_eq_false_iff]
    cases beattyLetter (k / 2) <;> decide

-- A zero contributes one letter to the image, and every other letter contributes two.
private theorem nuPrefix_length (k : ℕ) :
    ((beattyPrefix k).flatMap fibonacciNuMorphism).length + zeroCount k = 2 * k := by
  induction k with
  | zero => simp [zeroCount_zero]
  | succ k ih =>
    rw [show beattyPrefix (k + 1) = beattyPrefix k ++ [beattyLetter k] from List.ofFn_succ_last,
      List.flatMap_append, List.flatMap_singleton, List.length_append, zeroCount_succ]
    cases beattyLetter k <;> simp only [fibonacciNuMorphism, Bool.false_eq_true, ite_false,
      ite_true, List.length_cons, List.length_nil] <;> omega

private theorem nuPrefix_getD_true (k n : ℕ)
    (hn : ((beattyPrefix k).flatMap fibonacciNuMorphism).getD n false = true) :
    ∃ i < k, beattyLetter i = false ∧
      n = ((beattyPrefix i).flatMap fibonacciNuMorphism).length := by
  induction k with
  | zero => simp at hn
  | succ k ih =>
    rw [show beattyPrefix (k + 1) = beattyPrefix k ++ [beattyLetter k] from List.ofFn_succ_last,
      List.flatMap_append, List.flatMap_singleton] at hn
    by_cases h : n < ((beattyPrefix k).flatMap fibonacciNuMorphism).length
    · rw [List.getD_append _ _ _ _ h] at hn
      obtain ⟨i, hi, ha, hn⟩ := ih hn
      exact ⟨i, Nat.lt_succ_of_lt hi, ha, hn⟩
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)] at hn
      cases hb : beattyLetter k
      · have hk : n = ((beattyPrefix k).flatMap fibonacciNuMorphism).length := by
          cases hsub : n - ((beattyPrefix k).flatMap fibonacciNuMorphism).length with
          | zero => omega
          | succ j =>
            rw [hb, fibonacciNuMorphism, hsub, List.getD_cons_succ, List.getD_nil] at hn
            contradiction
        exact ⟨k, Nat.lt_succ_self k, hb, hk⟩
      · rw [hb, fibonacciNuMorphism, show [false, false] = List.replicate 2 false from rfl,
          List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] at hn
        contradiction

private theorem nuPrefix_getD_at_zero {k i : ℕ} (hi : i < k) (hb : beattyLetter i = false) :
    ((beattyPrefix k).flatMap fibonacciNuMorphism).getD
      ((beattyPrefix i).flatMap fibonacciNuMorphism).length false = true := by
  let r := k - (i + 1)
  have hk : k = i + 1 + r := by dsimp [r]; omega
  conv_lhs =>
    arg 1
    rw [hk]
  change ((List.ofFn (n := i + 1 + r) _).flatMap fibonacciNuMorphism).getD _ false = true
  rw [List.ofFn_add]
  change ((beattyPrefix (i + 1) ++ _).flatMap fibonacciNuMorphism).getD _ false = true
  rw [show beattyPrefix (i + 1) = beattyPrefix i ++ [beattyLetter i] from List.ofFn_succ_last,
    List.append_assoc, List.flatMap_append, List.getD_append_right _ _ _ _ le_rfl]
  simp [hb, fibonacciNuMorphism]

private theorem wesleyWordT_beatty (k : ℕ) : wesleyWordT k = true ↔
    ∃ m : ℤ, (k : ℤ) + 1 = 2 * beattySeq φ m - m := by
  let l := (fibWord (k + 2)).length
  have hl : k < l := fibInf_bound k
  change ((fibWord (k + 2)).flatMap fibonacciNuMorphism).getD k false = true ↔ _
  conv_lhs => rw [fibWord_eq_beattyPrefix (k + 2)]
  change ((beattyPrefix l).flatMap fibonacciNuMorphism).getD k false = true ↔ _
  constructor
  · intro h
    obtain ⟨i, -, hi, hk⟩ := nuPrefix_getD_true l k h
    refine ⟨(zeroCount i : ℤ) + 1, ?_⟩
    rw [(beattyIndex_iff i _).mpr ⟨hi, rfl⟩]
    have hlen := nuPrefix_length i
    omega
  · rintro ⟨m, hm⟩
    have hmpos : 0 < m := by
      by_contra! hn
      have hnonpos : (m : ℝ) ≤ 0 := by exact_mod_cast hn
      have hmul : (m : ℝ) * φ ≤ m := by
        simpa only [mul_one] using mul_le_mul_of_nonpos_left Real.one_lt_goldenRatio.le hnonpos
      have hmf : beattySeq φ m ≤ m := by
        simpa [beattySeq] using Int.floor_mono hmul
      omega
    have hmi : m ≤ beattySeq φ m :=
      Int.le_floor.mpr (le_mul_of_one_le_right (by exact_mod_cast hmpos.le)
        Real.one_lt_goldenRatio.le)
    let i := (beattySeq φ m).toNat - 1
    have hip : 0 < beattySeq φ m := hmpos.trans_le hmi
    have hi : (i : ℤ) + 1 = beattySeq φ m := by dsimp [i]; omega
    obtain ⟨hb, hm'⟩ := (beattyIndex_iff i m).mp hi.symm
    have hlen := nuPrefix_length i
    have hik : i < l := by omega
    have heq : k = ((beattyPrefix i).flatMap fibonacciNuMorphism).length := by omega
    rw [heq]
    exact nuPrefix_getD_at_zero hik hb

end FibonacciWordBeatty

open FibonacciWordBeatty in
/-- **Beatty-sequence descriptions of the words $F_\infty$, $S$ and $T$.** Let
$\varphi = (1 + \sqrt{5})/2$ be the golden ratio and $F_\infty = 010010100\cdots$ the infinite
Fibonacci word. Let $S = \mu(F_\infty)$ be its image under the morphism $\mu$ with $\mu(0) = 10$
and $\mu(1) = 01$, and $T = \nu(F_\infty)$ its image under the morphism $\nu$ with $\nu(0) = 1$
and $\nu(1) = 00$. For a word $W$ and an integer $n \ge 1$, write $W(n)$ for the $n$-th letter of
$W$, counting from $1$. Then:
(i) for every integer $n \ge 1$, $F_\infty(n) = 0$ if and only if $n = \lfloor m\varphi \rfloor$
for some integer $m$;
(ii) for every integer $n$, positive or not, if $n \ne \lfloor m\varphi \rfloor$ for every
integer $m$, then $n + 1 = \lfloor m'\varphi \rfloor$ and $n - 1 = \lfloor m''\varphi \rfloor$ for
some integers $m'$ and $m''$;
(iii) for every integer $n \ge 1$, $S(n) = 0$ if and only if either $n$ is even and
$n/2 = \lfloor m\varphi \rfloor$ for some integer $m$, or $n$ is odd and
$(n+1)/2 \ne \lfloor m\varphi \rfloor$ for every integer $m$;
(iv) for every integer $n \ge 1$, $T(n) = 1$ if and only if $n = 2\lfloor m\varphi \rfloor - m$
for some integer $m$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 2 (`integers-2025-A29-lem-2`). -/
public theorem fibonacciWord_beatty_properties :
    (∀ n : ℕ, 1 ≤ n → (fibInf (n - 1) = false ↔ ∃ m : ℤ, (n : ℤ) = ⌊m * Real.goldenRatio⌋)) ∧
    (∀ n : ℤ, (∀ m : ℤ, n ≠ ⌊m * Real.goldenRatio⌋) →
      (∃ m' : ℤ, n + 1 = ⌊m' * Real.goldenRatio⌋) ∧ ∃ m'' : ℤ, n - 1 = ⌊m'' * Real.goldenRatio⌋) ∧
    (∀ n : ℕ, 1 ≤ n → (wesleyWordS (n - 1) = false ↔
      (Even n ∧ ∃ m : ℤ, ((n / 2 : ℕ) : ℤ) = ⌊m * Real.goldenRatio⌋) ∨
        (Odd n ∧ ∀ m : ℤ, (((n + 1) / 2 : ℕ) : ℤ) ≠ ⌊m * Real.goldenRatio⌋))) ∧
    ∀ n : ℕ, 1 ≤ n → (wesleyWordT (n - 1) = true ↔
      ∃ m : ℤ, (n : ℤ) = 2 * ⌊m * Real.goldenRatio⌋ - m) := by
  refine ⟨?_, beatty_missing_neighbors, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.succ_sub_one, Nat.cast_succ, fibInf_eq_beattyLetter, beattySeq] using
      beattyLetter_eq_false_iff k
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.succ_sub_one, beattySeq] using wesleyWordS_beatty k
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.succ_sub_one, Nat.cast_succ, beattySeq] using wesleyWordT_beatty k

end MetaMathlibExt
