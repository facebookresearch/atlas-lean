/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.InfiniteWord.Factor
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse

/-!
# Reduced complexities for binary words

For a nonempty word, `alternations_muWord` counts the alternations of its Thue–Morse image
in terms of its length and its own alternations. The even and odd indices of the regular
paperfolding word follow the two recurrences `paperfoldingSeq_even` and `paperfoldingSeq_odd`.

## References

* John M. Campbell, James D. Currie, and Narad Rampersad,
  [Reduced Complexities for Sequences Over Finite Alphabets](https://math.colgate.edu/~integers/aa34/aa34.pdf),
  INTEGERS 26 (2026), Article A34, pp. 1–15, Sections 1 and 2.1 (paperfolding word and
  Toeplitz construction) and Lemma 1 (alternations in the Thue–Morse image).
* The proof of `paperfoldingSeq_even` is moved from the private lemma of the same name in
  `MathlibExt.Combinatorics.PaperfoldingReducedComplexity`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open MetaMathlibExt

/-- **Reduction of a binary word.** The reduction $\operatorname{red}(w)$ of a binary word $w$ is
the word obtained by collapsing each maximal run of equal consecutive letters of $w$ to a single
letter; for example $\operatorname{red}(0011101) = 0101$. -/
def redWord : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      if x = y then redWord (y :: xs) else x :: redWord (y :: xs)

/-- **Alternations of a binary word.** The number of alternations of a binary word $w$ is the
number of occurrences of the factors $01$ and $10$ in $w$, that is, the number of positions $i$
with $w_i \ne w_{i+1}$. -/
def alternations (w : List Bool) : ℕ :=
  (w.zip w.tail).countP (fun p => decide (p.1 ≠ p.2))

/-- **Extension of the Thue–Morse substitution to binary words.** The morphism $\mu$ sends each
letter to a word of length two, $\mu(0) = 01$ and $\mu(1) = 10$, and a binary word
$w_1 w_2 \cdots w_k$ to the concatenation $\mu(w_1) \mu(w_2) \cdots \mu(w_k)$. -/
def muWord (w : List Bool) : List Bool :=
  w.flatMap thueMorseSubstitution

/-- **Regular paperfolding sequence.** The regular paperfolding sequence $f = f_0 f_1 f_2 \cdots$
over $\{0, 1\}$ is indexed from $0$: for each $i$, write $i + 1 = m \cdot 2^k$ with $m$ odd; then
$f_i = 0$ if $m \equiv 1 \pmod 4$ and $f_i = 1$ if $m \equiv 3 \pmod 4$. -/
def paperfoldingSeq (i : ℕ) : Bool :=
  decide ((i + 1) / 2 ^ (Nat.factorization (i + 1) 2) % 4 ≠ 1)

/-- **Paperfolding letters at even indices.** The zero-indexed letter at $2j$ is `true`
exactly when $j$ is odd. -/
theorem paperfoldingSeq_even (j : ℕ) :
    paperfoldingSeq (2 * j) = decide (j % 2 = 1) := by
  have h : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_remainder j (by decide)
  rw [Bool.eq_iff_iff]
  simp only [paperfoldingSeq, h, pow_zero, Nat.div_one, decide_eq_true_eq]
  omega

/-- **Paperfolding letters at odd indices.** The zero-indexed letter at $2j+1$ equals
that at $j$, since $2j+2$ and $j+1$ have the same odd part. -/
theorem paperfoldingSeq_odd (j : ℕ) : paperfoldingSeq (2 * j + 1) = paperfoldingSeq j := by
  have h : (2 * (j + 1)).factorization 2 = (j + 1).factorization 2 + 1 := by
    rw [Nat.factorization_mul (by decide) (Nat.succ_ne_zero j), Finsupp.add_apply,
      Nat.prime_two.factorization_self, Nat.add_comm]
  simp only [paperfoldingSeq, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, h, pow_succ]
  rw [Nat.mul_comm (2 ^ _) 2, Nat.mul_div_mul_left _ _ (by decide : 0 < 2)]

/-- **Reduced factor complexity.** For a finite binary word $w$, let $\mathrm{red}(w)$ be the
word obtained from $w$ by collapsing each run of equal letters to a single letter. For an
infinite binary word $x = x_0 x_1 x_2 \cdots$ and a natural number $n$, the reduced factor
complexity $\rho^{\mathrm{red}}_x(n)$ is the number of distinct words $\mathrm{red}(w)$ as $w$
ranges over the length-$n$ factors of $x$. -/
noncomputable def rhoRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((fun v => redWord (List.ofFn v)) ''
    InfiniteWord.factorSet x n)

/-- **Reduced abelian complexity.** For a binary sequence $x = x_0 x_1 x_2 \cdots$ and
$n \in \mathbb{N}$, the reduced abelian complexity $\rho^{\mathrm{ab,red}}_x(n)$ is the number of
distinct pairs $(|\mathrm{red}(v)|, |\mathrm{red}(v)|_0)$, where $v$ ranges over the length-$n$
factors of $x$, $\mathrm{red}(v)$ is the reduction of $v$ (each run of equal letters collapsed to
a single letter) and $|w|_0$ is the number of letters $0$ in $w$. Equivalently, it counts the
reductions of length-$n$ factors of $x$ up to rearrangement of their letters. -/
noncomputable def rhoAbRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard
    ((fun v => ((redWord (List.ofFn v)).length,
      (redWord (List.ofFn v)).count false)) ''
    InfiniteWord.factorSet x n)

/-- **Reduced abelian complexity as a count over starting positions.** Count the distinct
pairs of reduction length and number of zeros by taking the range over all factor starts. -/
theorem rhoAbRed_eq_ncard_range (x : ℕ → Bool) (n : ℕ) :
    rhoAbRed x n = (Set.range fun i =>
      ((redWord (InfiniteWord.factorList x n i)).length,
        (redWord (InfiniteWord.factorList x n i)).count false)).ncard := by
  rw [rhoAbRed]
  congr 1
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi⟩ := (InfiniteWord.isFactor_iff_exists_factorList _ _).mp
      ((InfiniteWord.isFactor_ofFn_iff_mem_factorSet v x).mpr hv)
    rw [List.length_ofFn] at hi
    exact ⟨i, congrArg (fun w => ((redWord w).length, (redWord w).count false)) hi⟩
  · rintro ⟨i, rfl⟩
    let w := InfiniteWord.factorList x n i
    have hl : w.length = n := InfiniteWord.factorList_length x n i
    let v : Fin n → Bool := fun j => w[j.val]'(by simpa only [hl] using j.isLt)
    have hv : List.ofFn v = w := by
      apply List.ext_getElem
      · rw [List.length_ofFn, hl]
      · intro j hj₁ hj₂
        simp [v]
    have hfactor : InfiniteWord.IsFactor (List.ofFn v) x := by
      rw [hv, InfiniteWord.isFactor_iff_exists_factorList, hl]
      exact ⟨i, rfl⟩
    exact ⟨v, (InfiniteWord.isFactor_ofFn_iff_mem_factorSet v x).mp hfactor,
      congrArg (fun u => ((redWord u).length, (redWord u).count false)) hv⟩

/-- **Minimum number of alternations in Thue–Morse factors.** For a natural number $n$, $m_n$ is
the least number of alternations (positions where two adjacent letters differ) among the
length-$n$ factors of the Thue–Morse sequence. -/
noncomputable def minAlt (n : ℕ) : ℕ :=
  sInf ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

/-- **Maximum number of alternations in Thue–Morse factors.** For a natural number $n$, $M_n$ is
the largest number of alternations (positions where two adjacent letters differ) among the
length-$n$ factors of the Thue–Morse sequence. -/
noncomputable def maxAlt (n : ℕ) : ℕ :=
  sSup ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

private theorem alternations_cons_cons (a b : Bool) (w : List Bool) :
    alternations (a :: b :: w) = alternations (b :: w) + (if a = b then 0 else 1) := by
  simp [alternations, List.countP_cons]

private theorem muWord_cons (a : Bool) (w : List Bool) :
    muWord (a :: w) = a :: (!a) :: muWord w := by
  cases a <;> rfl

/-- **Alternations of the Thue–Morse image of a word.** Let $\mu$ be the morphism on binary words
with $\mu(0) = 01$ and $\mu(1) = 10$. If $w$ is a nonempty binary word of length $|w|$ with
$\alpha$ alternations (positions where two adjacent letters differ), then $\mu(w)$ has exactly
$2|w| - 1 - \alpha$ alternations.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 1. -/
theorem alternations_muWord (w : List Bool) (hw : w ≠ []) :
    (alternations (muWord w) : ℤ) =
      2 * (w.length : ℤ) - 1 - (alternations w : ℤ) := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    cases w with
    | nil => cases a <;> decide
    | cons b w =>
      specialize ih (List.cons_ne_nil b w)
      -- The new block alternates internally and alternates at the boundary exactly when a = b.
      cases a <;> cases b <;> simp [muWord_cons, alternations_cons_cons] at ih ⊢ <;> omega

end MathlibExt.Combinatorics.ReducedComplexitiesWanted
