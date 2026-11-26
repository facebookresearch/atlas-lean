/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ContinuedFractions.Paperfolding
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continued fraction of a paperfolding sum via the words $A_k$

Corollary 15 of Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued
Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6. The simple continued fraction
of `S = ∑ sₖ` with `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ`, `x₀ = 2`, `xₖ ≥ 2` has `a₀ = 1` and its partial
quotients begin with the word `paperfoldingContFracWord x k` for every `k`
(`paperfoldingSum_contFrac_recursion`). The proof identifies the Cloitre-and-ruler word of
`paperfoldingSum_contFrac_cloitre_ruler` with `A_k` followed by its final crease, modelling both
sides as folds of a binary tree.
-/

namespace MetaMathlibExt

namespace paperfoldingSum_contFrac_recursionFold

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

private theorem interleave_eq_word_append (x : ℕ → ℕ) (k : ℕ) :
    cloitreCreaseInterleave (fun j => x (padicValNat 2 j + 1) - 1) 1 (cloitreApprox k) =
      paperfoldingContFracWord x k ++ [x (k + 1) - 1] := by
  have h := interleave_stage x k
  unfold ruler creases at h
  exact h

end paperfoldingSum_contFrac_recursionFold

@[expose] public section

open paperfoldingSum_contFrac_recursionFold in
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
  rw [interleave_eq_word_append] at hpre
  refine ⟨hh, fun i hi => ?_⟩
  have hi' : i < (paperfoldingContFracWord x k ++ [x (k + 1) - 1]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have h := hpre i hi'
  have hget : (paperfoldingContFracWord x k ++ [x (k + 1) - 1])[i] =
      (paperfoldingContFracWord x k)[i] :=
    List.getElem_append_left hi
  simpa [hget] using h

end

end MetaMathlibExt
