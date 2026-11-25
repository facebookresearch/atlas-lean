/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Fibonacci substitution.** The Fibonacci substitution sends each letter of the binary
alphabet $\{0, 1\}$ to a finite binary word: it maps $0$ to $01$ and $1$ to $0$.

The letters $0$ and $1$ are represented by the Booleans false and true.

Source: concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibSubst : Bool → List Bool
  | false => [false, true]
  | true => [false]

/-- **Fibonacci morphism.** The Fibonacci morphism $\varphi$ extends the Fibonacci substitution
$\sigma$, which maps $0$ to $01$ and $1$ to $0$, to finite binary words by concatenation: $\varphi$
maps the empty word to the empty word, and $\varphi(bw) = \sigma(b)\varphi(w)$ for every letter
$b$ and every finite binary word $w$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibMorph : List Bool → List Bool
  | [] => []
  | b :: w => fibSubst b ++ fibMorph w

/-- **Finite Fibonacci words.** The finite Fibonacci words $f_n$, for natural numbers $n$, are
the words in the letters $0$ and $1$ defined by $f_0 = 0$ and $f_{n+1} = \varphi(f_n)$, where
$\varphi$ is the Fibonacci morphism, which replaces each letter $0$ by $01$ and each letter $1$
by $0$.

The first words are $0$, $01$, $010$, $01001$, $01001010$, and so on.

Source: concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibWord : ℕ → List Bool
  | 0 => [false]
  | n + 1 => fibMorph (fibWord n)

/-- **Infinite Fibonacci word.** Let $f_0 = 0$ and let $f_{k+1}$ be the image of $f_k$ under the
Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$), so that $f_0, f_1, f_2, \ldots$ are the finite
Fibonacci words $0, 01, 010, 01001, \ldots$. The one-sided infinite Fibonacci word is the infinite
binary word whose letter at index $n$ (indices start at $0$) is the letter of $f_{n+2}$ at index
$n$.

Each $f_k$ is a prefix of $f_{k+1}$ and $f_{n+2}$ has more than $n$ letters, so this word is the
limit of the finite Fibonacci words.

Source: concept `jis_sem_f409ef3715730614fd194b4d`; sources `jis_138e7e26819c0bf6a015b5e7`,
`jis_52830047049fa91220ac91eb`, `jis_2ff564e576beedc024b95b9a`. -/
def fibInf (n : ℕ) : Bool :=
  (fibWord (n + 2)).getD n false

/-- **The Fibonacci morphism respects concatenation.** Let $\varphi$ be the Fibonacci morphism on
finite binary words, induced by $0 \mapsto 01$ and $1 \mapsto 0$. For all finite binary words $a$
and $b$, $\varphi(ab) = \varphi(a)\varphi(b)$, where juxtaposition denotes concatenation.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibMorph_append : ∀ (a b : List Bool), fibMorph (a ++ b) = fibMorph a ++ fibMorph b
  | [], b => by simp [fibMorph]
  | x :: xs, b => by simp [fibMorph, fibMorph_append xs b, List.append_assoc]

/-- **The Fibonacci morphism does not shorten words.** Let $\varphi$ be the Fibonacci morphism on
finite binary words, induced by $0 \mapsto 01$ and $1 \mapsto 0$. For every finite binary word $w$,
the length of $\varphi(w)$ is at least the length of $w$, that is, $|w| \le |\varphi(w)|$.

The reason is that every letter maps to a nonempty word.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibMorph_length_ge : ∀ (w : List Bool), w.length ≤ (fibMorph w).length
  | [] => by simp [fibMorph]
  | false :: w => by
    have ih := fibMorph_length_ge w
    simp [fibMorph, fibSubst]
    omega
  | true :: w => by
    have ih := fibMorph_length_ge w
    simp [fibMorph, fibSubst]
    omega

/-- **Finite Fibonacci words begin with $0$.** Let $f_0 = 0$ and let $f_{k+1}$ be the image of
$f_k$ under the Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$). For every natural number $n$,
there is a finite binary word $t$ such that $f_n = 0t$, that is, the first letter of $f_n$ is $0$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_head : ∀ (n : ℕ), ∃ t, fibWord n = false :: t
  | 0 => ⟨[], rfl⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := fibWord_head n
    exact ⟨true :: fibMorph t, by simp [fibWord, ht, fibMorph, fibSubst]⟩

/-- **Lower bound on the length of the finite Fibonacci words.** Let $f_0 = 0$ and let $f_{k+1}$
be the image of $f_k$ under the Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$). For every
natural number $n$, the word $f_n$ has length at least $n + 1$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_length : ∀ (n : ℕ), n + 1 ≤ (fibWord n).length
  | 0 => by simp [fibWord]
  | n + 1 => by
    have ih := fibWord_length n
    obtain ⟨t, ht⟩ := fibWord_head n
    have hge := fibMorph_length_ge t
    have htlen : (fibWord n).length = t.length + 1 := by simp [ht]
    have hlen : (fibWord (n + 1)).length = 2 + (fibMorph t).length := by
      simp [fibWord, ht, fibMorph, fibSubst]
      omega
    omega

/-- **Consecutive finite Fibonacci words are nested.** For every natural number $n$, the $n$-th
finite Fibonacci word $f_n$ is a prefix of $f_{n+1}$: there is a finite word $t$ in the letters
$0$ and $1$ with $f_{n+1} = f_n t$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_nested_succ : ∀ (n : ℕ), ∃ t, fibWord (n + 1) = fibWord n ++ t
  | 0 => ⟨[true], rfl⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := fibWord_nested_succ n
    refine ⟨fibMorph t, ?_⟩
    calc fibWord (n + 1 + 1) = fibMorph (fibWord (n + 1)) := rfl
      _ = fibMorph (fibWord n ++ t) := by rw [ht]
      _ = fibMorph (fibWord n) ++ fibMorph t := fibMorph_append _ _
      _ = fibWord (n + 1) ++ fibMorph t := by
        rw [show fibMorph (fibWord n) = fibWord (n + 1) from rfl]

/-- **Earlier finite Fibonacci words are prefixes of later ones.** For all natural numbers
$n \le m$, the $n$-th finite Fibonacci word $f_n$ is a prefix of the $m$-th finite Fibonacci word
$f_m$: there is a finite word $t$ in the letters $0$ and $1$ with $f_m = f_n t$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_prefix : ∀ (n m : ℕ), n ≤ m → ∃ t, fibWord m = fibWord n ++ t
  | n, 0, h => by
    have hn : n = 0 := by omega
    subst hn
    exact ⟨[], by simp⟩
  | n, m + 1, h => by
    by_cases hn : n = m + 1
    · subst hn
      exact ⟨[], by simp⟩
    · have hle : n ≤ m := by omega
      obtain ⟨t, ht⟩ := fibWord_prefix n m hle
      obtain ⟨s, hs⟩ := fibWord_nested_succ m
      exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩

/-- **Appending a word does not change earlier letters.** Let $a$ and $t$ be finite words in the
letters $0$ and $1$, and let $k$ be a natural number smaller than the length of $a$. Then the
letter at position $k$ of the concatenation $a t$ equals the letter at position $k$ of $a$,
counting positions from $0$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem getD_append_prefix : ∀ (a t : List Bool) (k : ℕ),
    k < a.length → (a ++ t).getD k false = a.getD k false
  | [], _, _, hk => by simp at hk
  | _ :: _, _, 0, _ => by simp
  | x :: xs, t, k + 1, hk => by
    have hk' : k < xs.length := by simpa using hk
    have ih := getD_append_prefix xs t k hk'
    simpa using ih

/-- **Letters of the finite Fibonacci words stabilize.** Let $f_0 = 0$ and let $f_{k+1}$ be the
image of $f_k$ under the Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$). For all natural
numbers $n \le m$ and every index $i$ less than the length of $f_n$ (indices start at $0$), the
letter of $f_m$ at index $i$ equals the letter of $f_n$ at index $i$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_getD_eq (n m k : ℕ) (hle : n ≤ m) (hk : k < (fibWord n).length) :
    (fibWord m).getD k false = (fibWord n).getD k false := by
  obtain ⟨t, ht⟩ := fibWord_prefix n m hle
  rw [ht]
  exact getD_append_prefix (fibWord n) t k hk

/-- **The finite Fibonacci word of index $n + 2$ has more than $n$ letters.** Let $f_0 = 0$ and
let $f_{k+1}$ be the image of $f_k$ under the Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$).
For every natural number $n$, the length of $f_{n+2}$ is greater than $n$.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibInf_bound (n : ℕ) : n < (fibWord (n + 2)).length := by
  have h := fibWord_length (n + 2)
  omega

/-- **Finite Fibonacci words agree with the infinite Fibonacci word.** Let $f_0 = 0$ and let
$f_{k+1}$ be the image of $f_k$ under the Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$). For
all natural numbers $m$ and $n$ such that $n$ is less than the length of $f_m$, the letter of $f_m$
at index $n$ equals the letter at index $n$ of the one-sided infinite Fibonacci word (indices start
at $0$). In other words, every $f_m$ is a prefix of the infinite Fibonacci word.

Source: concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibInf_agrees (m n : ℕ) (hm : n < (fibWord m).length) :
    (fibWord m).getD n false = fibInf n := by
  unfold fibInf
  have hlen : n < (fibWord (n + 2)).length := fibInf_bound n
  let k := Nat.max m (n + 2)
  have hmk : m ≤ k := Nat.le_max_left m (n + 2)
  have hnk : n + 2 ≤ k := Nat.le_max_right m (n + 2)
  have h1 : (fibWord k).getD n false = (fibWord m).getD n false :=
    fibWord_getD_eq m k n hmk hm
  have h2 : (fibWord k).getD n false = (fibWord (n + 2)).getD n false :=
    fibWord_getD_eq (n + 2) k n hnk hlen
  rw [← h1]
  exact h2

end

end MetaMathlibExt
