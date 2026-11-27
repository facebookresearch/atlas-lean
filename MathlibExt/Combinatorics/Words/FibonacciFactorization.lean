/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

@[expose] public section

namespace MetaMathlibExt

/-- **Recurrence for the finite Fibonacci words.** Let $f_0, f_1, f_2, \ldots$ be the finite
Fibonacci words. For every natural number $n$, $f_{n+2} = f_{n+1} f_n$, where juxtaposition
denotes concatenation. -/
theorem fibWord_add_two (n : ℕ) : fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fibMorph (fibWord (n + 2)) = fibMorph (fibWord (n + 1)) ++ fibMorph (fibWord n)
    rw [ih, fibMorph_append]

/-- **Concatenating the finite Fibonacci words.** For every natural number $N$, prepending the
letters $0$ and $1$ to the concatenation $f_0 f_1 \cdots f_{N-1}$ of the first $N$ finite Fibonacci
words gives $f_{N+1}$: that is, $0\,1\,f_0 f_1 \cdots f_{N-1} = f_{N+1}$, where the concatenation
is empty when $N = 0$. -/
theorem fibWord_factorization (N : ℕ) :
    false :: true :: (List.range N).flatMap fibWord = fibWord (N + 1) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.cons_append,
      ← List.cons_append, ih, fibWord_add_two]

/-- **Finite Fibonacci words are prefixes of the infinite Fibonacci word.** For every natural
number $n$, the finite Fibonacci word $f_n$ is the word formed by the first $|f_n|$ letters of the
infinite Fibonacci word. -/
theorem fibWord_eq_ofFn_fibInf (n : ℕ) :
    fibWord n = List.ofFn (fun i : Fin (fibWord n).length => fibInf i) := by
  refine List.ext_getElem (by simp) fun i h _ => ?_
  rw [List.getElem_ofFn, ← fibInf_agrees n i h]
  simp [h]

private lemma ofFn_prefix_of_le {α : Type*} (g : ℕ → α) {k m : ℕ} (hkm : k ≤ m) :
    List.ofFn (fun i : Fin k => g i) <+: List.ofFn (fun i : Fin m => g i) := by
  rw [List.prefix_iff_getElem]
  exact ⟨by simpa using hkm, fun i hi => by simp⟩

/-- **Factorization of the infinite Fibonacci word into finite Fibonacci words.** Let $f$ be the
infinite Fibonacci word and let $f_0, f_1, f_2, \ldots$ be the finite Fibonacci words. For every
natural number $N$, the finite word $w_N = 0\,1\,f_0 f_1 \cdots f_{N-1}$ (so $w_0 = 01$) consists of
the first $|w_N|$ letters of $f$, and for every natural number $k$ the first $k$ letters of $f$
form a prefix of $w_N$ for some $N$. In this sense
$f = 0 \cdot 1 \cdot f_0 \cdot f_1 \cdot f_2 \cdots$.

Source: Gabriele Fici, "Factorizations of the Fibonacci Infinite Word", Journal of Integer
Sequences 18 (2015), Article 15.9.3, equation `fibo`. -/
theorem fibInf_factorization :
    (∀ N : ℕ,
      let w := false :: true :: (List.range N).flatMap fibWord
      w = List.ofFn (fun i : Fin w.length => fibInf i)) ∧
    ∀ k : ℕ, ∃ N : ℕ,
      List.ofFn (fun i : Fin k => fibInf i) <+:
        false :: true :: (List.range N).flatMap fibWord := by
  refine ⟨fun N => ?_, fun k => ⟨k, ?_⟩⟩
  · change false :: true :: (List.range N).flatMap fibWord = List.ofFn
      (fun i : Fin (false :: true :: (List.range N).flatMap fibWord).length => fibInf i)
    rw [fibWord_factorization]
    exact fibWord_eq_ofFn_fibInf (N + 1)
  · rw [fibWord_factorization, fibWord_eq_ofFn_fibInf (k + 1)]
    have := fibWord_length (k + 1)
    exact ofFn_prefix_of_le fibInf (by omega)

private lemma fibWord_bridge (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ n : ℕ, F (n + 2) = (fibWord n).map (fun b => cond b 1 0)
  | 0 => by simp [h_two, fibWord]
  | 1 => by rw [h_rec 0, h_two, h_one]; rfl
  | n + 2 => by
    rw [show n + 2 + 2 = (n + 1) + 3 by omega, h_rec (n + 1),
      fibWord_bridge F h_one h_two h_rec (n + 1), show n + 1 + 1 = n + 2 by omega,
      fibWord_bridge F h_one h_two h_rec n, fibWord_add_two, List.map_append]

private lemma fibWord_concat_eq (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ N : ℕ, (0 :: (List.range N).flatMap (fun n => F (n + 1))) = F (N + 2)
  | 0 => by simp [h_two]
  | N + 1 => by
    have hb : ∀ n : ℕ, F (n + 1 + 1) = (fibWord n).map (fun b => cond b 1 0) :=
      fibWord_bridge F h_one h_two h_rec
    rw [fibWord_bridge F h_one h_two h_rec (N + 1), ← fibWord_factorization,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [hb, h_one, List.map_flatMap]

/--
**The infinite Fibonacci word as $0$ followed by the finite Fibonacci words.** Let $f$ be an
infinite word over $\{0, 1\}$ and let $f_1, f_2, f_3, \ldots$ be finite words over $\{0, 1\}$ with
$f_1 = 1$, $f_2 = 0$ and $f_{n+3} = f_{n+2} f_{n+1}$ for every natural number $n$, such that for
every natural number $n$ the word $f_{n+2}$ consists of the first $|f_{n+2}|$ letters of $f$.
Then for every natural number $N$ the word $w_N = 0\,f_1 f_2 \cdots f_N$ (so $w_0 = 0$) consists of
the first $|w_N|$ letters of $f$, and for every natural number $k$ the first $k$ letters of $f$
form a prefix of $w_N$ for some $N$. In this sense $f = 0 \cdot f_1 \cdot f_2 \cdot f_3 \cdots$.

Proves `Wanted` entry `fibonacci_infinite_word_factorization`.

Source: Gabriele Fici, "Factorizations of the Fibonacci Infinite Word", Journal of Integer
Sequences 18 (2015), Article 15.9.3, Proposition lines 188-195 (equation `fibo`),
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Fici/fici5.tex>.
-/
theorem fibonacci_infinite_word_factorization
    (f : ℕ → Fin 2)
    (fibWord : ℕ → List (Fin 2))
    (h_one : fibWord 1 = [1])
    (h_two : fibWord 2 = [0])
    (h_rec : ∀ n : ℕ, fibWord (n + 3) = fibWord (n + 2) ++ fibWord (n + 1))
    (h_limit : ∀ n : ℕ,
      fibWord (n + 2) =
        List.ofFn (fun i : Fin (fibWord (n + 2)).length => f i)) :
    (∀ N : ℕ,
      let w := 0 :: (List.range N).flatMap (fun n => fibWord (n + 1))
      w = List.ofFn (fun i : Fin w.length => f i)) ∧
    ∀ k : ℕ, ∃ N : ℕ,
      List.IsPrefix
        (List.ofFn (fun i : Fin k => f i))
        (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) := by
  have heq : ∀ N : ℕ,
      (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) = fibWord (N + 2) :=
    fibWord_concat_eq fibWord h_one h_two h_rec
  refine ⟨?_, fun k => ⟨k, ?_⟩⟩
  · intro N
    change (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) =
      List.ofFn (fun i : Fin (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))).length => f i)
    rw [heq N]
    exact h_limit N
  · have hlen : k ≤ (fibWord (k + 2)).length := by
      rw [fibWord_bridge fibWord h_one h_two h_rec k, List.length_map]
      have := fibWord_length k
      omega
    rw [heq k, h_limit k]
    exact ofFn_prefix_of_le f hlen

end MetaMathlibExt
