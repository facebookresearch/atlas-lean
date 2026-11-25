/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Infix

/-!
Square-free words: finite and infinite words with no ordinary square factor,
including the ternary-alphabet and fixed-length specializations.

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Khalyavin/khalyavin13.tex>,
<https://cs.uwaterloo.ca/journals/JIS/VOL4/GRIMM/words.tex>, and
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Sun/sun.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Square word.** A word $w$ over an alphabet $\alpha$ is a square if $w = xx$ for some nonempty
word $x$, where $xx$ denotes the concatenation of $x$ with itself.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public def IsWordSquare {α : Type*} (w : List α) : Prop :=
  ∃ x : List α, x ≠ [] ∧ w = x ++ x

/-- **Square-free finite word.** A finite word $w$ over an alphabet $\alpha$ is square-free if no
factor of $w$ is a square, where a factor of $w$ is a word $s$ with $w = psq$ for some words $p$
and $q$, and a square is a word $xx$ with $x$ nonempty.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public def IsSquareFreeWord {α : Type*} (w : List α) : Prop :=
  ∀ s : List α, s.IsInfix w → ¬ IsWordSquare s

/-- **Square-free infinite word.** An infinite word $u = u_0 u_1 u_2 \cdots$ over an alphabet
$\alpha$ is square-free if it contains no two adjacent equal nonempty blocks: for all $i \ge 0$ and
all $k \ge 1$ there is some $j < k$ with $u_{i+j} \ne u_{i+k+j}$.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public def IsInfiniteSquareFreeWord {α : Type*} (u : Nat → α) : Prop :=
  ∀ i k : Nat, 0 < k → ∃ j, j < k ∧ u (i + j) ≠ u (i + k + j)

/-- **The ternary alphabet for square-free words.** The ternary alphabet is the set $\{0, 1, 2\}$
of natural numbers less than $3$; its three letters play the role of $a$, $b$ and $c$.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public abbrev TernaryAlphabet := Fin 3

/-- **Square-free ternary words of length $n$.** For a natural number $n$, a finite word $w$ over
the ternary alphabet is a square-free ternary word of length $n$ if $w$ is square-free and $w$ has
length exactly $n$.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public def IsTernarySquareFreeLength (n : Nat) (w : List TernaryAlphabet) : Prop :=
  IsSquareFreeWord w ∧ w.length = n

/-- **Square-free infinite ternary word.** An infinite word $u = u_0 u_1 u_2 \cdots$ over the
ternary alphabet is a square-free infinite ternary word if it is square-free as an infinite word.

Source: concept `jis_sem_4970e15c0be600988a8749e5`; statements
`jis_7f73597782f1028e81df5432`, `jis_81478fffd0e6a2a59cc243c2`,
`jis_a592211f71121f0a58379b81`, `jis_b56e6494255fbd36cd0a6c2a`,
`jis_e3cd35b86f8a67dd6c99e98e`, `jis_fd4cce9bbb14d8135f72fbdc`. -/
public def IsInfiniteTernarySquareFreeWord (u : Nat → TernaryAlphabet) : Prop :=
  IsInfiniteSquareFreeWord u

/-- **Factors of square-free words are square-free.** If a finite word $v$ is square-free and $u$
is a factor of $v$, that is, $v = puq$ for some words $p$ and $q$, then $u$ is square-free. -/
public theorem IsSquareFreeWord.of_isInfix {α : Type*} {u v : List α}
    (hv : IsSquareFreeWord v) (huv : u.IsInfix v) : IsSquareFreeWord u := by
  intro s hs
  exact hv s (hs.trans huv)

/-- **Square-freeness via prefixes of suffixes.** A finite word $w$ is square-free if and only if,
for every prefix $s$ of a suffix of $w$ and every nonempty prefix $x$ of $s$, we have $s \ne xx$,
where $xx$ denotes the concatenation of $x$ with itself.

This form is directly decidable when letter equality is decidable. -/
public theorem isSquareFreeWord_iff_inits_tails {α : Type*} {w : List α} :
    IsSquareFreeWord w ↔
      ∀ s ∈ w.tails.flatMap List.inits, ∀ x ∈ s.inits, x ≠ [] → s ≠ x ++ x := by
  constructor
  · intro hw s hs x _ hx heq
    rw [List.mem_flatMap] at hs
    obtain ⟨t, ht, hs⟩ := hs
    have hsw : s.IsInfix w := ((List.mem_inits s t).mp hs).isInfix.trans
      ((List.mem_tails t w).mp ht).isInfix
    exact hw s hsw ⟨x, hx, heq⟩
  · intro h s hs ⟨x, hx, heq⟩
    rw [List.infix_iff_prefix_suffix] at hs
    obtain ⟨t, hst, htw⟩ := hs
    have hsmem : s ∈ w.tails.flatMap List.inits := by
      rw [List.mem_flatMap]
      exact ⟨t, (List.mem_tails t w).mpr htw, (List.mem_inits s t).mpr hst⟩
    exact h s hsmem x ((List.mem_inits x s).mpr ⟨x, heq.symm⟩) hx heq

end

end MetaMathlibExt
