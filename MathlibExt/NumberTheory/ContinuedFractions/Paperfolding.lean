/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Seq.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continued fractions of paperfolding sums

The continued fraction of a paperfolding sum interleaves Cloitre's letters with the crease
terms in ruler order (`paperfoldingSum_contFrac_cloitre_ruler`). Each finite fold gives a partial
sum of the series. Since that interleaved word is the word $A_k$ followed by its final crease, the
partial quotients also begin with $A_k$ (`paperfoldingSum_contFrac_recursion`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Terms of the paperfolding sums.** For a sequence $x = (x_k)_{k \ge 0}$ of natural numbers,
the real numbers $s_k$ are defined by $s_0 = 1$ and $s_{k+1} = s_k^2 / x_k$, where the quotient is
read as $0$ when $x_k = 0$. They are the terms of the sums $S = \sum_k s_k$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public noncomputable def paperfoldingSumTerm (x : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => paperfoldingSumTerm x k ^ 2 / x k

/-- **First term of the paperfolding sums.** For every sequence $x$ of natural numbers, the term
$s_0$ of the paperfolding sum terms defined by $x$ equals $1$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_zero (x : ℕ → ℕ) : paperfoldingSumTerm x 0 = 1 := rfl

/-- **Recursion for the paperfolding sum terms.** For every sequence $x$ of natural numbers and
every $k \in \mathbb{N}$, the paperfolding sum terms defined by $x$ satisfy
$s_{k+1} = s_k^2 / x_k$, where the quotient is read as $0$ when $x_k = 0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_succ (x : ℕ → ℕ) (k : ℕ) :
    paperfoldingSumTerm x (k + 1) = paperfoldingSumTerm x k ^ 2 / x k := rfl

/-- **Second term of the paperfolding sums.** For every sequence $x$ of natural numbers with
$x_0 = 2$, the term $s_1$ of the paperfolding sum terms defined by $x$ equals $1/2$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_one (x : ℕ → ℕ) (hx0 : x 0 = 2) :
    paperfoldingSumTerm x 1 = 1 / 2 := by
  simp [paperfoldingSumTerm, hx0]

/-- **Interleaving creases into a Cloitre word.** Given a sequence $c : \mathbb{N} \to \mathbb{N}$
and a start index $j$, the crease interleaving of a finite word $w$ of natural numbers reads $w$
from left to right as letters $(2)$ and $(1, 1)$ and inserts $c_j, c_{j+1}, c_{j+2}, \dots$ after
the successive letters. Precisely, the empty word gives the empty word; a word $2, w'$ gives
$2, c_j$ followed by the interleaving of $w'$ from index $j + 1$; a word $1, 1, w'$ gives
$1, 1, c_j$ followed by the interleaving of $w'$ from index $j + 1$; and any other nonempty word
$a, w'$ gives $a$ followed by the interleaving of $w'$ from the same index $j$.

The last case is unreachable on the approximants $A_k$ of Cloitre's sequence.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14 (Cloitre's sequence occurs
one `[1, 1]` or `[2]` at a time, interleaved with crease terms). -/
public def cloitreCreaseInterleave (c : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | j, 2 :: l => 2 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, 1 :: 1 :: l => 1 :: 1 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, a :: l => a :: cloitreCreaseInterleave c j l

/-- **Crease interleaving of the Cloitre approximant $A_2$.** For every sequence
$c : \mathbb{N} \to \mathbb{N}$, the crease interleaving by $c$, from start index $1$, of the
approximant $A_2 = (1, 1, 2, 1, 1, 1, 1)$ of Cloitre's sequence is
$(1, 1, c_1, 2, c_2, 1, 1, c_3, 1, 1, c_4)$: each of the four letters $(1, 1)$, $(2)$, $(1, 1)$,
$(1, 1)$ of $A_2$ is followed by its crease $c_1$, $c_2$, $c_3$, $c_4$ in turn.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14. -/
public theorem cloitreCreaseInterleave_cloitreApprox_two (c : ℕ → ℕ) :
    cloitreCreaseInterleave c 1 (cloitreApprox 2) =
      [1, 1, c 1, 2, c 2, 1, 1, c 3, 1, 1, c 4] := rfl

/-- **Continued-fraction words of the paperfolding sums.** For a sequence $x = (x_k)_{k \ge 0}$ of
natural numbers, the finite words $A_k$ of natural numbers are defined by $A_0 = (1, 1)$ and
$A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$: the concatenation of $A_k$, the single letter
$\max(x_{k+1} - 1, 0)$ and the mirror image $A_k^r$ of $A_k$. The mirror image of a word reverses
it and then replaces a leading $2$ by $1, 1$, or two leading letters $1, 1$ by $2$, leaving any
other word unchanged.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public def paperfoldingContFracWord (x : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [1, 1]
  | k + 1 => paperfoldingContFracWord x k ++
      (x (k + 1) - 1) :: cloitreMirror (paperfoldingContFracWord x k)

/-- **The second paperfolding continued-fraction word.** For every sequence $x$ of natural numbers,
the continued-fraction word $A_1$ defined by $x$ is $(1, 1, \max(x_1 - 1, 0), 2)$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public theorem paperfoldingContFracWord_one (x : ℕ → ℕ) :
    paperfoldingContFracWord x 1 = [1, 1, x 1 - 1, 2] := rfl

/-- **The paperfolding continued-fraction word $A_2$ for constant $x_k = 6$.** Let $x_k = 6$
for every $k$, and let $A_0 = (1, 1)$ and $A_{k+1} = A_k\,(x_{k+1} - 1)\,A_k^r$, where the
mirror image $A^r$ of a word $A$ is obtained by reversing $A$ and then replacing a leading $2$
by $1, 1$, or two leading letters $1, 1$ by $2$, leaving any other word unchanged. Then
$A_2 = (1, 1, 5, 2, 5, 1, 1, 5, 1, 1)$.

This is the start of the paper's expansion of $6 \sum_{k \ge 0} 12^{-2^k}$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15 and Section 6. -/
public theorem paperfoldingContFracWord_const_six_two :
    paperfoldingContFracWord (fun _ => 6) 2 = [1, 1, 5, 2, 5, 1, 1, 5, 1, 1] := rfl

end

namespace paperfoldingSum_contFrac_cloitre_ruler

-- A leaf represents one whole letter, either [1, 1] or [2]. The height of a fork
-- specifies the crease separating its two children.
private inductive Fold : ℕ → Type
  | leaf (paired : Bool) : Fold 0
  | fork {k : ℕ} (left right : Fold k) : Fold (k + 1)

private def digits (sep : ℕ → List ℕ) : {k : ℕ} → Fold k → List ℕ
  | _, .leaf true => [1, 1]
  | _, .leaf false => [2]
  | _, .fork (k := k) l r => digits sep l ++ sep k ++ digits sep r

private def revFold : {k : ℕ} → Fold k → Fold k
  | _, .leaf b => .leaf b
  | _, .fork l r => .fork (revFold r) (revFold l)

private def flipFirst : {k : ℕ} → Fold k → Fold k
  | _, .leaf b => .leaf (!b)
  | _, .fork l r => .fork (flipFirst l) r

private def stage : (k : ℕ) → Fold k
  | 0 => .leaf true
  | k + 1 => .fork (stage k) (flipFirst (revFold (stage k)))

private theorem digits_rev {sep : ℕ → List ℕ} (hs : ∀ k, (sep k).reverse = sep k)
    {k : ℕ} (t : Fold k) : digits sep (revFold t) = (digits sep t).reverse := by
  induction t with
  | leaf b => cases b <;> rfl
  | fork l r hl hr => simp [revFold, digits, hl, hr, hs, List.append_assoc]

private theorem digits_flip (sep : ℕ → List ℕ) {k : ℕ} (t : Fold k) (s : List ℕ) :
    digits sep (flipFirst t) ++ s = cloitreComplementFirst (digits sep t ++ s) := by
  induction t generalizing s with
  | leaf b => cases b <;> rfl
  | fork l r hl _ =>
    simp only [digits, flipFirst, List.append_assoc]
    exact hl _

private theorem digits_mirror {sep : ℕ → List ℕ} (hs : ∀ k, (sep k).reverse = sep k)
    {k : ℕ} (t : Fold k) :
    digits sep (flipFirst (revFold t)) = cloitreMirror (digits sep t) := by
  simpa [digits_rev hs, cloitreMirror] using digits_flip sep (revFold t) []

private theorem stage_bare (k : ℕ) : digits (fun _ => []) (stage k) = cloitreApprox k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [stage, digits, digits_mirror (sep := fun _ => []) (fun _ => rfl), ih, cloitreApprox]

private def creases (x : ℕ → ℕ) (k : ℕ) := [x (k + 1) - 1]

private theorem stage_word (x : ℕ → ℕ) (k : ℕ) :
    digits (creases x) (stage k) = paperfoldingContFracWord x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [stage, digits, digits_mirror (sep := creases x) (fun _ => rfl), ih, creases,
      paperfoldingContFracWord, List.append_assoc]

private def ruler (x : ℕ → ℕ) (j : ℕ) := x (padicValNat 2 j + 1) - 1

private theorem ruler_middle (x : ℕ → ℕ) (m k : ℕ) :
    ruler x ((2 * m + 1) * 2 ^ k) = x (k + 1) - 1 := by
  have h : ¬ 2 ∣ 2 * m + 1 := by omega
  simp [ruler, Nat.padicValNat_def, Nat.multiplicity_mul (by omega : 2 * m + 1 ≠ 0)
    (by positivity : 2 ^ k ≠ 0), multiplicity_eq_zero_of_not_dvd h]

-- Process a complete dyadic interval of letters. Its last crease belongs to the
-- enclosing fold, so we retain that crease explicitly on the right.
private theorem interleave_digits (x : ℕ → ℕ) {k : ℕ} (t : Fold k) (m : ℕ) (s : List ℕ) :
    cloitreCreaseInterleave (ruler x) (m * 2 ^ k + 1) (digits (fun _ => []) t ++ s) =
      digits (creases x) t ++ ruler x ((m + 1) * 2 ^ k) ::
        cloitreCreaseInterleave (ruler x) ((m + 1) * 2 ^ k + 1) s := by
  induction t generalizing m s with
  | leaf b => cases b <;> simp [digits, cloitreCreaseInterleave]
  | @fork k l r hl hr =>
    have h₀ : m * 2 ^ (k + 1) = (2 * m) * 2 ^ k := by ring
    have h₁ : (m + 1) * 2 ^ (k + 1) = (2 * m + 1 + 1) * 2 ^ k := by ring
    simp only [digits, List.append_nil, List.append_assoc, h₀, h₁, hl, hr,
      ruler_middle, creases, List.cons_append, List.nil_append]

private theorem interleave_stage (x : ℕ → ℕ) (k : ℕ) :
    cloitreCreaseInterleave (ruler x) 1 (cloitreApprox k) =
      paperfoldingContFracWord x k ++ creases x k := by
  have h := interleave_digits x (stage k) 0 []
  have hm := ruler_middle x 0 k
  have hend : ruler x (2 ^ k) = x (k + 1) - 1 := by simpa using hm
  simpa [stage_bare, stage_word, cloitreCreaseInterleave, creases, hend]
    using h

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

private def digitMat (a : ℕ) : Mat := !![(a : ℝ), 1; 1, 0]

private def wordMat (w : List ℕ) : Mat := (w.map digitMat).prod

private theorem wordMat_append (u v : List ℕ) : wordMat (u ++ v) = wordMat u * wordMat v := by
  simp [wordMat]

private theorem wordMat_rev (w : List ℕ) : wordMat w.reverse = (wordMat w).transpose := by
  induction w with
  | nil => simp [wordMat]
  | cons a w ih =>
    have h : (digitMat a).transpose = digitMat a := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [List.reverse_cons, wordMat_append, ih]
    simp [wordMat, Matrix.transpose_mul, h]

-- Switching the first letter between [2] and [1, 1] replaces the bottom row
-- by the difference of the top and bottom rows.
private def toggle : Mat := !![1, 0; 1, -1]

private theorem wordMat_flip (sep : ℕ → List ℕ) {k : ℕ} (t : Fold k) :
    wordMat (digits sep (flipFirst t)) = toggle * wordMat (digits sep t) := by
  induction t with
  | leaf b =>
    cases b <;> norm_num [flipFirst, digits, wordMat, digitMat, toggle, Matrix.mul_fin_two]
  | fork l r hl _ => simp only [flipFirst, digits, wordMat_append, hl, mul_assoc]

local notation "word" => paperfoldingContFracWord

private def reflected (x : ℕ → ℕ) (k : ℕ) := digits (creases x) (flipFirst (revFold (stage k)))

private theorem word_succ (x : ℕ → ℕ) (k : ℕ) :
    word x (k + 1) = word x k ++ creases x k ++ reflected x k := by
  rw [← stage_word, ← stage_word]
  rfl

private theorem fold_matrix (x : ℕ → ℕ) (hx : ∀ k, 2 ≤ x k) (k : ℕ) (a b c d : ℝ)
    (hm : wordMat (word x k) = !![a, b; c, d]) (hd : a * d - b * c = 1) :
    wordMat (word x (k + 1)) =
      !![x (k + 1) * a ^ 2, x (k + 1) * a * c - 1;
         x (k + 1) * a * c + 1, x (k + 1) * c ^ 2] := by
  have hr : wordMat (reflected x k) = toggle * (wordMat (word x k)).transpose := by
    rw [reflected, wordMat_flip, digits_rev (sep := creases x) (fun _ => rfl),
      wordMat_rev, stage_word]
  have ht : (!![a, b; c, d] : Mat).transpose = !![a, c; b, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [word_succ, wordMat_append, wordMat_append, hr, hm, ht]
  simp only [creases, wordMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, digitMat, toggle, Matrix.mul_fin_two, Nat.cast_sub (by grind : 1 ≤ x (k + 1)),
    Nat.cast_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith only [hd]

-- For the finite word with matrix (a,b;c,d), 1/a is the most recent summand
-- and 1+c/a is the partial sum. Folding preserves determinant one.
private theorem partial_sum_matrix (x : ℕ → ℕ) (hx0 : x 0 = 2) (hx : ∀ k, 2 ≤ x k)
    (k : ℕ) : ∃ a b c d : ℝ, wordMat (word x k) = !![a, b; c, d] ∧
      0 < a ∧ a * d - b * c = 1 ∧ paperfoldingSumTerm x (k + 1) = 1 / a ∧
      ∑ i ∈ Finset.range (k + 2), paperfoldingSumTerm x i = 1 + c / a := by
  induction k with
  | zero =>
    refine ⟨2, 1, 1, 1, ?_, by norm_num, by norm_num, paperfoldingSumTerm_one x hx0, ?_⟩
    · norm_num [paperfoldingContFracWord, wordMat, digitMat, Matrix.mul_fin_two]
    · simp [Finset.sum_range_succ, paperfoldingSumTerm_zero, paperfoldingSumTerm_one x hx0]
  | succ k ih =>
    obtain ⟨a, b, c, d, hm, ha, hd, hs, hsum⟩ := ih
    let y : ℝ := x (k + 1)
    have hy : 0 < y := by
      dsimp [y]
      exact_mod_cast (show 0 < x (k + 1) by grind)
    have hs' : paperfoldingSumTerm x (k + 2) = 1 / (y * a ^ 2) := by
      rw [paperfoldingSumTerm_succ, hs]
      dsimp [y]
      ring
    refine ⟨y * a ^ 2, y * a * c - 1, y * a * c + 1, y * c ^ 2,
      fold_matrix x hx k a b c d hm hd, by positivity, by ring, hs', ?_⟩
    rw [Finset.sum_range_succ, hsum, hs']
    field_simp
    ring

-- The fractional part obtained by reading the word with a residual fraction t.
private noncomputable def value (w : List ℕ) (t : ℝ) : ℝ :=
  w.foldr (fun a r => ((a : ℝ) + r)⁻¹) t

private theorem value_append (u v : List ℕ) (t : ℝ) :
    value (u ++ v) t = value u (value v t) := by simp [value, List.foldr_append]

private theorem value_zero (w : List ℕ) (hw : ∀ n ∈ w, 0 < n) :
    0 < wordMat w 0 0 ∧ 0 ≤ wordMat w 1 0 ∧
      value w 0 = wordMat w 1 0 / wordMat w 0 0 := by
  induction w with
  | nil => simp [wordMat, value]
  | cons n w ih =>
    obtain ⟨ha, hc, hv⟩ := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    have hn : (0 : ℝ) < n := by exact_mod_cast hw n (by simp)
    change 0 < (digitMat n * wordMat w) 0 0 ∧ 0 ≤ (digitMat n * wordMat w) 1 0 ∧
      ((n : ℝ) + value w 0)⁻¹ = (digitMat n * wordMat w) 1 0 / (digitMat n * wordMat w) 0 0
    simp [digitMat, Matrix.mul_apply, Fin.sum_univ_two, hv, ha.le, add_div' _ _ _ ha.ne',
      show 0 < (n : ℝ) * wordMat w 0 0 + wordMat w 1 0 by positivity]

private theorem digits_pos (x : ℕ → ℕ) (hx : ∀ k, 2 ≤ x k) {k : ℕ} (t : Fold k) :
    ∀ a ∈ digits (creases x) t, 0 < a := by
  induction t with
  | leaf b => cases b <;> simp [digits]
  | fork l r hl hr =>
    simp only [digits, List.mem_append, creases, List.mem_singleton]
    grind

private theorem word_pos (x : ℕ → ℕ) (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    ∀ a ∈ word x k, 0 < a := stage_word x k ▸ digits_pos x hx (stage k)

private theorem digits_ne_nil (sep : ℕ → List ℕ) {k : ℕ} (t : Fold k) :
    digits sep t ≠ [] := by
  induction t with
  | leaf b => cases b <;> simp [digits]
  | fork l r hl _ => simp [digits, hl]

private theorem sum_eq_value (x : ℕ → ℕ) (hx0 : x 0 = 2) (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), paperfoldingSumTerm x i = 1 + value (word x k) 0 := by
  obtain ⟨a, b, c, d, hm, _, _, _, hs⟩ := partial_sum_matrix x hx0 hx k
  rw [hs, (value_zero _ (word_pos x hx k)).2.2, hm]
  rfl

private theorem summable_terms (x : ℕ → ℕ) (hx : ∀ k, 2 ≤ x k) :
    Summable (paperfoldingSumTerm x) := by
  have bound (n : ℕ) : 0 ≤ paperfoldingSumTerm x n ∧ paperfoldingSumTerm x n ≤ (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero => simp [paperfoldingSumTerm]
    | succ n ih =>
      have hx' : (2 : ℝ) ≤ x n := by exact_mod_cast hx n
      have hle : paperfoldingSumTerm x n ≤ 1 :=
        ih.2.trans (pow_le_one₀ (by norm_num) (by norm_num))
      rw [paperfoldingSumTerm_succ, pow_succ (1 / 2 : ℝ)]
      refine ⟨div_nonneg (sq_nonneg _) (by positivity),
        (div_le_iff₀ (by linarith : (0 : ℝ) < x n)).mpr ?_⟩
      calc
        paperfoldingSumTerm x n ^ 2 ≤ paperfoldingSumTerm x n := by nlinarith [ih.1]
        _ ≤ (1 / 2 : ℝ) ^ n := ih.2
        _ ≤ _ := by
          nlinarith [mul_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n) (sub_nonneg.mpr hx')]
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).of_nonneg_of_le
    (fun n => (bound n).1) (fun n => (bound n).2)

private theorem value_closed (w : List ℕ) (hw : ∀ n ∈ w, 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : value w t ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => exact ht
  | cons a w ih =>
    obtain ⟨hl, _⟩ := ih (fun n hn => hw n (List.mem_cons_of_mem _ hn))
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    change 0 ≤ ((a : ℝ) + value w t)⁻¹ ∧ ((a : ℝ) + value w t)⁻¹ ≤ 1
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩

private theorem value_continuous (w : List ℕ) (hw : ∀ n ∈ w, 0 < n) :
    ContinuousOn (value w) (Set.Icc (0 : ℝ) 1) := by
  induction w with
  | nil => exact continuousOn_id
  | cons a w ih =>
    have hw' := fun n hn => hw n (List.mem_cons_of_mem a hn)
    refine (continuousOn_const.add (ih hw')).inv₀ ?_
    intro t ht
    have ha : (0 : ℝ) < a := by exact_mod_cast hw a (by simp)
    exact (add_pos_of_pos_of_nonneg ha (value_closed w hw' ht).1).ne'

private theorem word_prefix (x : ℕ → ℕ) {k n : ℕ} (h : k ≤ n) :
    word x k <+: word x n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s ++ creases x n ++ reflected x n, by simp [word_succ, ← hs, List.append_assoc]⟩

-- The closed interval of possible tails is compact. Every sufficiently late
-- partial sum lies in its image under the prefix, hence so does the limit.
private theorem sum_in_cylinder (x : ℕ → ℕ) (hx0 : x 0 = 2) (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, 1 + value (word x k) t = ∑' n, paperfoldingSumTerm x n := by
  have hc := (isCompact_Icc.image_of_continuousOn
    (continuousOn_const.add (value_continuous _ (word_pos x hx k)) :
      ContinuousOn (fun t => 1 + value (word x k) t) (Set.Icc 0 1))).isClosed
  apply hc.mem_of_tendsto ((summable_terms x hx).tendsto_sum_tsum_nat.comp
    (Filter.tendsto_add_atTop_nat 2))
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  obtain ⟨s, hs⟩ := word_prefix x hn
  have hpos : ∀ a ∈ s, 0 < a := fun a ha =>
    word_pos x hx n a (hs ▸ List.mem_append_right _ ha)
  refine ⟨value s 0, value_closed _ hpos (by constructor <;> norm_num), ?_⟩
  change 1 + value (word x k) (value s 0) = ∑ i ∈ Finset.range (n + 2), paperfoldingSumTerm x i
  rw [sum_eq_value x hx0 hx, ← hs, value_append]

private theorem value_pos {a : ℕ} {r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) : 0 < ((a : ℝ) + r)⁻¹ := by
  positivity

private theorem value_open (w : List ℕ) (hw : ∀ n ∈ w, 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : value w t ∈ Set.Ioo (0 : ℝ) 1 := by
  induction w with
  | nil => exact ht
  | cons a w ih =>
    obtain ⟨hl, _⟩ := ih (fun n hn => hw n (List.mem_cons_of_mem _ hn))
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    exact ⟨value_pos (hw a (by simp)) hl.le, inv_lt_one_of_one_lt₀ (lt_add_of_le_of_pos ha hl)⟩

-- Two more positive digits turn even an endpoint of the closed tail interval
-- into an interior point. This avoids the two finite expansions of a rational.
private theorem reflected_tail_open (x : ℕ → ℕ) (hx : ∀ k, 2 ≤ x k) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    value (creases x k ++ reflected x k) t ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : reflected x k ≠ [] := digits_ne_nil _ _
  have hp : ∀ a ∈ reflected x k, 0 < a := digits_pos x hx _
  obtain ⟨a, s, hs⟩ := List.exists_cons_of_ne_nil hn
  rw [hs] at hp ⊢
  have hs₀ := (value_closed s (fun n hn => hp n (List.mem_cons_of_mem _ hn)) ht).1
  have hv := value_pos (hp a (by simp)) hs₀
  have hc : 1 ≤ x (k + 1) - 1 := by grind
  have hc' : (1 : ℝ) ≤ (x (k + 1) - 1 : ℕ) := by exact_mod_cast hc
  exact ⟨value_pos hc hv.le, inv_lt_one_of_one_lt₀ (lt_add_of_le_of_pos hc' hv)⟩

private theorem read_digits (w : List ℕ) (hw : ∀ n ∈ w, 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ) :
    (GenContFract.of ((b : ℝ) + value w t)).h = b ∧
      ∀ i (hi : i < w.length), (GenContFract.of ((b : ℝ) + value w t)).partDens.get? i =
        some (w[i] : ℝ) := by
  have floor_add (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) : ⌊(n : ℝ) + u⌋ = n := by
    rw [Int.floor_natCast_add, Int.floor_eq_zero_iff.mpr ⟨hu.1.le, hu.2⟩, add_zero]
  refine ⟨by simp [floor_add b (value_open w hw ht)], ?_⟩
  induction w generalizing b with
  | nil => simp
  | cons a w ih =>
    have hw' := fun n hn => hw n (List.mem_cons_of_mem a hn)
    have hr := value_open w hw' ht
    have hv := value_open (a :: w) hw ht
    have hf : Int.fract ((b : ℝ) + value (a :: w) t) = value (a :: w) t := by
      simp [Int.fract, floor_add b hv]
    have hinv : (value (a :: w) t)⁻¹ = a + value w t := inv_inv _
    intro i hi
    cases i with
    | zero =>
      have h := GenContFract.of_s_head (hf ▸ hv.1.ne')
      change (GenContFract.of ((b : ℝ) + value (a :: w) t)).s.get? 0 = _ at h
      rw [hf, hinv, floor_add a hr] at h
      simp [GenContFract.partDens, Stream'.Seq.map_get?, h]
    | succ i =>
      simp only [GenContFract.partDens, Stream'.Seq.map_get?, GenContFract.of_s_succ, hf, hinv,
        List.getElem_cons_succ]
      exact ih hw' a i (by simpa using hi)

end paperfoldingSum_contFrac_cloitre_ruler

open paperfoldingSum_contFrac_cloitre_ruler in
/-- **Continued fraction of a paperfolding sum in Cloitre and ruler order.** Let
$x = (x_k)_{k \ge 0}$ be natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be
the paperfolding sum terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued
fraction expansion $[a_0; a_1, a_2, \ldots]$. For $j \ge 1$ let $c_j = x_{\nu_2(j) + 1} - 1$, where
$\nu_2(j)$ is the exponent of $2$ in $j$. Then $a_0 = 1$, and for every $k$ the partial quotients
$a_1, a_2, \ldots$ begin with the word obtained from the $k$-th approximant $A_k$ of Cloitre's
sequence by splitting $A_k$ from the left into letters $1, 1$ and $2$ and inserting $c_j$ after
its $j$-th letter, for every $j$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14
(`jis-2026-26.3.6-thm-14`). -/
public theorem paperfoldingSum_contFrac_cloitre_ruler (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (cloitreCreaseInterleave (fun j => x (padicValNat 2 j + 1) - 1) 1
          (cloitreApprox k)).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((cloitreCreaseInterleave (fun j => x (padicValNat 2 j + 1) - 1) 1
            (cloitreApprox k))[i] : ℝ) := by
  obtain ⟨t, ht, hs⟩ := sum_in_cylinder x hx0 hx (k + 2)
  rw [word_succ x (k + 1), List.append_assoc, value_append] at hs
  have ht' := reflected_tail_open x hx (k + 1) ht
  rw [word_succ x k, value_append] at hs
  have hr := value_open (reflected x k) (digits_pos x hx _) ht'
  have hw : ∀ n ∈ paperfoldingContFracWord x k ++ creases x k, 0 < n := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact word_pos x hx _ n hn
    · simp only [creases, List.mem_singleton] at hn
      grind
  have hword := interleave_stage x k
  unfold ruler at hword
  simp only [hword, ← hs]
  simpa only [Nat.cast_one] using read_digits _ hw hr 1

open paperfoldingSum_contFrac_cloitre_ruler in
/-- **Continued fraction of a paperfolding sum via the words $A_k$.** Let $x = (x_k)_{k \ge 0}$ be
natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be the paperfolding sum
terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued fraction expansion
$[a_0; a_1, a_2, \ldots]$. Let $A_k$ be the continued-fraction words defined by $x$, so that
$A_0 = (1, 1)$ and $A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$, where the mirror image $A^r$ of a
word $A$ is obtained by reversing $A$ and then replacing a leading $2$ by $1, 1$, or two leading
letters $1, 1$ by $2$, leaving any other word unchanged. Then $a_0 = 1$, and for every $k$ the
partial quotients $a_1, a_2, \ldots$ begin with the word $A_k$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15
(`jis-2026-26.3.6-cor-15`). -/
public theorem paperfoldingSum_contFrac_recursion (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (paperfoldingContFracWord x k).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((paperfoldingContFracWord x k)[i] : ℝ) := by
  obtain ⟨hh, hpre⟩ := paperfoldingSum_contFrac_cloitre_ruler x hx0 hx k
  have hword := interleave_stage x k
  unfold ruler creases at hword
  rw [hword] at hpre
  refine ⟨hh, fun i hi => ?_⟩
  have h := hpre i (by simp only [List.length_append, List.length_singleton]; omega)
  rwa [List.getElem_append_left hi] at h

end MetaMathlibExt
