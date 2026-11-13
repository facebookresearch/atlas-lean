/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Smarandache permutation sequence (A004741)

Formalizes the required definition clause for the Smarandache permutation
sequence (concept `jis_sem_23e7b5e48daf56d0a358ebfc`), as given in statement
`jis_c46e1d9809a20ee69374dac7` of source `jis_source_02ccad5fb16b7cd8775ba04c`
(Kimberling, JIS VOL25): the concatenation of the blocks
`(1, 3, ..., 2n - 1, 2n, 2n - 2, ..., 2)`, whose initial terms are
`(1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2, 1, 3, 5, 7, 8, 6, 4, 2, ...)`.

Source: Clark Kimberling, *Parasequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Blocks of the Smarandache permutation sequence.** For a natural number $n$, the $n$-th block
is the list of the odd numbers $1, 3, \ldots, 2n - 1$ in increasing order followed by the even
numbers $2n, 2n - 2, \ldots, 2$ in decreasing order; the $0$-th block is empty.

Source: concept `jis_sem_23e7b5e48daf56d0a358ebfc`, statement `jis_c46e1d9809a20ee69374dac7`. -/
def smarandacheBlock (n : ℕ) : List ℕ :=
  ((List.range n).map (fun k => 2 * k + 1)) ++ ((List.range n).map (fun k => 2 * (n - k)))

/-- **Prefix of the Smarandache permutation sequence.** For a natural number $N$, this is the
list of natural numbers obtained by concatenating, in order, the Smarandache blocks numbered
$1, 2, \dots, N$, where block $n$ is the list $(1, 3, \dots, 2n - 1, 2n, 2n - 2, \dots, 2)$ of the
odd numbers below $2n$ in increasing order followed by the even numbers from $2n$ down to $2$.
For $N = 0$ it is the empty list. -/
def smarandachePrefix (N : ℕ) : List ℕ :=
  ((List.range N).map (fun n => smarandacheBlock (n + 1))).flatten

/-- **Smarandache permutation sequence.** The Smarandache permutation sequence (OEIS A004741) is
the sequence $(a_i)_{i \ge 0}$ of natural numbers, indexed from $0$, obtained by concatenating
the blocks $(1, 3, \ldots, 2n - 1, 2n, 2n - 2, \ldots, 2)$ for $n = 1, 2, 3, \ldots$ in order; it
begins $1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2, \ldots$, so $a_0 = 1$.

Source: concept `jis_sem_23e7b5e48daf56d0a358ebfc`, statement `jis_c46e1d9809a20ee69374dac7`. -/
def smarandachePermutation (i : ℕ) : ℕ :=
  (smarandachePrefix (i + 1)).getD i 0

/-- **First block of the Smarandache permutation sequence.** The first block of the Smarandache
permutation sequence is $(1, 2)$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandacheBlock_one : smarandacheBlock 1 = [1, 2] := by rfl

/-- **Second block of the Smarandache permutation sequence.** The second block of the Smarandache
permutation sequence is $(1, 3, 4, 2)$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandacheBlock_two : smarandacheBlock 2 = [1, 3, 4, 2] := by rfl

/-- **Third block of the Smarandache permutation sequence.** The third block of the Smarandache
permutation sequence is $(1, 3, 5, 6, 4, 2)$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandacheBlock_three : smarandacheBlock 3 = [1, 3, 5, 6, 4, 2] := by rfl

/-- **Fourth block of the Smarandache permutation sequence.** The fourth block of the Smarandache
permutation sequence is $(1, 3, 5, 7, 8, 6, 4, 2)$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandacheBlock_four :
    smarandacheBlock 4 = [1, 3, 5, 7, 8, 6, 4, 2] := by rfl

/-- **Concatenation of the first three Smarandache blocks.** Concatenating the first three blocks
of the Smarandache permutation sequence gives $(1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2)$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandachePrefix_three :
    smarandachePrefix 3 = [1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2] := by rfl

/-- **Initial term of the Smarandache permutation sequence.** Indexing the Smarandache permutation
sequence $(a_i)_{i \ge 0}$ from $0$, its initial term is $a_0 = 1$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandachePermutation_zero : smarandachePermutation 0 = 1 := by rfl

/-- **Sixth term of the Smarandache permutation sequence.** Indexing the Smarandache permutation
sequence $(a_i)_{i \ge 0}$ from $0$, its sixth term is $a_5 = 2$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandachePermutation_five : smarandachePermutation 5 = 2 := by rfl

/-- **Twelfth term of the Smarandache permutation sequence.** Indexing the Smarandache permutation
sequence $(a_i)_{i \ge 0}$ from $0$, its twelfth term is $a_{11} = 2$.

Source: statement `jis_c46e1d9809a20ee69374dac7`. -/
theorem smarandachePermutation_eleven : smarandachePermutation 11 = 2 := by rfl

end MetaMathlibExt
