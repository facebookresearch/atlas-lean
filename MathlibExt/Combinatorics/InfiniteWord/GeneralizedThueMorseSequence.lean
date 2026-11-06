/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Tactic.Ring

/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/

namespace MetaMathlibExt

@[expose] public section

namespace GeneralizedThueMorse

/-- **Cyclic letter shift.** For $L \in \mathbb{N}$ and letters $a, t$ of the alphabet
$\{0, \dots, L-1\}$, the cyclic shift of $a$ by $t$ is the letter $(a + t) \bmod L$. Writing the
letters as $a_0, \dots, a_{L-1}$, it sends $a_i$ to $a_{(i + t) \bmod L}$.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`,
statements `jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`). -/
public def shiftLetter {L : Nat} (a t : Fin L) : Fin L :=
  ⟨(a.val + t.val) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.2)⟩

/-- **Cyclic shift of a word.** Let $L$ be a natural number and let $t$ be a letter of the
alphabet $\{0, 1, \dots, L - 1\}$. The cyclic shift by $t$ of a word $w = a_1 a_2 \cdots a_n$
over this alphabet is the word $\sigma_t(a_1) \sigma_t(a_2) \cdots \sigma_t(a_n)$ of the same
length, where $\sigma_t(a) = (a + t) \bmod L$ is the cyclic shift of a letter.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statements
`jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`. -/
public def shiftWord {L : Nat} (t : Fin L) (w : List (Fin L)) : List (Fin L) :=
  List.map (fun a => shiftLetter a t) w

/-- **Letters of a cyclically shifted word.** Let $L$ be a natural number and let $t$ and $b$ be
letters of the alphabet $\{0, 1, \dots, L - 1\}$. For a letter $a$ write
$\sigma_t(a) = (a + t) \bmod L$ for its cyclic shift by $t$, and for a word $w$ over this
alphabet write $\sigma_t(w)$ for the word obtained by shifting each letter of $w$. Then $b$
occurs in $\sigma_t(w)$ if and only if $b = \sigma_t(a)$ for some letter $a$ occurring in $w$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`. -/
public theorem shiftWord_mem {L : Nat} (t : Fin L) (w : List (Fin L)) (b : Fin L) :
    b ∈ shiftWord t w ↔ ∃ a ∈ w, shiftLetter a t = b := by
  simp [shiftWord]

/-- **Cyclic shifting preserves word length.** For every $L \in \mathbb{N}$, every letter $t$ of
the alphabet $\{0, \dots, L-1\}$ and every finite word $w$ over that alphabet, the word obtained
from $w$ by shifting each letter cyclically by $t$ has the same length as $w$.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem shiftWord_length {L : Nat} (t : Fin L) (w : List (Fin L)) :
    (shiftWord t w).length = w.length := by
  simp [shiftWord]

/-- **Value of the cyclic letter shift.** For every $L \in \mathbb{N}$ and all letters $a, t$ of
the alphabet $\{0, \dots, L-1\}$, the cyclic shift of $a$ by $t$ is the letter
$(a + t) \bmod L$.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem shiftLetter_val {L : Nat} (a t : Fin L) :
    (shiftLetter a t).val = (a.val + t.val) % L :=
  rfl

/-- **Blocks of the generalized Thue–Morse sequence.** Let $L > 1$ and $k > 1$ be natural numbers,
take the letters $0, 1, \dots, L-1$ (the elements of $\mathbb{Z}/L\mathbb{Z}$), and let $\kappa$
assign a shift $\kappa(j, n) \in \mathbb{Z}/L\mathbb{Z}$ to each $j \in \{1, \dots, k-1\}$ and
each $n \ge 0$. For a word $w$ and $t \in \mathbb{Z}/L\mathbb{Z}$, let $f^t(w)$ be the word
obtained from $w$ by adding $t$ modulo $L$ to every letter. The blocks $A_n$ of the
$(L, k, \kappa)$-Thue–Morse sequence are the words given by $A_0 = 0$ (a word of one letter)
and $A_{n+1} = A_n \, f^{\kappa(1, n)}(A_n) \, f^{\kappa(2, n)}(A_n) \cdots
f^{\kappa(k-1, n)}(A_n)$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`. -/
public def block (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) : Nat → List (Fin L)
  | 0 => [⟨0, by omega⟩]
  | n + 1 =>
    let prev := block L k hL hk kappa n
    prev ++ List.flatten (List.map (fun j => shiftWord (kappa j n) prev) (List.finRange (k - 1)))

/-- **Length of a concatenation of equal-length lists.** Let $l$ be a list of lists over a type
and let $m \in \mathbb{N}$. If every list in $l$ has length $m$, then the concatenation of the
lists in $l$ has length $n \cdot m$, where $n$ is the number of lists in $l$.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem length_flatten_eq {α : Type} (l : List (List α)) (m : Nat)
    (h : ∀ x ∈ l, x.length = m) : l.flatten.length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x.length = m := h x (by simp)
    have hxs : ∀ y ∈ xs, y.length = m := fun y hy => h y (by simp [*])
    have hih := ih hxs
    have hflat : (List.flatten (x :: xs)).length = x.length + (List.flatten xs).length := by
      simp
    have hcons : (x :: xs).length = xs.length + 1 := by
      simp
    rw [hflat, hx, hih, hcons]
    ring

/-- **Length of the generalized Thue–Morse blocks.** Let $L > 1$ and $k > 1$ be natural numbers
and let $\kappa$ assign a shift $\kappa(j, n) \in \mathbb{Z}/L\mathbb{Z}$ to each
$j \in \{1, \dots, k-1\}$ and each $n \ge 0$. For every $n \ge 0$, the block $A_n$ of the
$(L, k, \kappa)$-Thue–Morse sequence has exactly $k^n$ letters.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`. -/
public theorem block_length (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (n : Nat) :
    (block L k hL hk kappa n).length = k ^ n := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
    have hmem : ∀ x ∈ List.map
        (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
        (List.finRange (k - 1)),
        x.length = (block L k hL hk kappa n).length := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact shiftWord_length _ _
    have hflen := length_flatten_eq _ _ hmem
    have hmap : (List.map
        (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
        (List.finRange (k - 1))).length = k - 1 := by
      simp
    have hunfold : block L k hL hk kappa (n + 1) =
        block L k hL hk kappa n ++
          List.flatten (List.map
            (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
            (List.finRange (k - 1))) :=
      rfl
    simp only [hunfold, List.length_append, ih, hflen, hmap, pow_succ]
    have e : k ^ n * k = k ^ n * ((k - 1) + 1) := by
      congr 1
      omega
    rw [e, mul_add, mul_one, Nat.mul_comm (k - 1) (k ^ n)]
    exact Nat.add_comm _ _

/-- **Each generalized Thue–Morse block is a prefix of the next.** Let $L > 1$ and $k > 1$ be
natural numbers and let $\kappa$ assign a shift $\kappa(j, n) \in \mathbb{Z}/L\mathbb{Z}$ to each
$j \in \{1, \dots, k-1\}$ and each $n \ge 0$. For every $n \ge 0$, the block $A_n$ of the
$(L, k, \kappa)$-Thue–Morse sequence is a prefix of $A_{n+1}$: there is a word $w$ with
$A_{n+1} = A_n w$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`. -/
public theorem block_prefix_succ (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (n : Nat) :
    ∃ tail, block L k hL hk kappa (n + 1) = block L k hL hk kappa n ++ tail :=
  ⟨_, rfl⟩

/-- **The generalized Thue–Morse blocks form a chain of prefixes.** Let $L > 1$ and $k > 1$ be
natural numbers and let $\kappa$ assign a shift $\kappa(j, n) \in \mathbb{Z}/L\mathbb{Z}$ to each
$j \in \{1, \dots, k-1\}$ and each $n \ge 0$. For all natural numbers $m \le n$, the block $A_m$
of the $(L, k, \kappa)$-Thue–Morse sequence is a prefix of $A_n$: there is a word $w$ with
$A_n = A_m w$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`. -/
public theorem block_prefix (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) {m n : Nat} (h : m ≤ n) :
    ∃ tail, block L k hL hk kappa n = block L k hL hk kappa m ++ tail := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact ⟨[], by simp⟩
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm
      exact ⟨[], by simp⟩
    · have hle : m ≤ n := by omega
      obtain ⟨tail, htail⟩ := ih hle
      obtain ⟨step, hstep⟩ := block_prefix_succ L k hL hk kappa n
      exact ⟨tail ++ step, by rw [hstep, htail, List.append_assoc]⟩

/-- **A crude exponential bound.** For every natural number $k > 1$ and every $m \in \mathbb{N}$,
we have $m < k^{m+1}$.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem lt_pow_succ_self {k : Nat} (hk : 1 < k) (m : Nat) : m < k ^ (m + 1) := by
  induction m with
  | zero => exact pow_pos (by omega) _
  | succ n ih =>
    have hpos : 0 < k ^ (n + 1) := pow_pos (by omega) _
    have hstep : k ^ (n + 1) < k ^ (n + 1) * k := lt_mul_of_one_lt_right hpos hk
    have hpow : k ^ ((n + 1) + 1) = k ^ (n + 1) * k := pow_succ k (n + 1)
    omega

/-- **Indexing into a concatenation.** Let $l_1$ and $l_2$ be lists over a type, and let $m$ be a
natural number less than the length of $l_1$. Then the entry at position $m$ of the concatenation
of $l_1$ followed by $l_2$ equals the entry at position $m$ of $l_1$ (positions start at $0$).

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem get_append_left {α : Type} (l₁ l₂ : List α) (m : Nat)
    (h : m < (l₁ ++ l₂).length) (hm : m < l₁.length) :
    (l₁ ++ l₂).get ⟨m, h⟩ = l₁.get ⟨m, hm⟩ := by
  induction l₁ generalizing m with
  | nil => simp at hm
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => exact ih m _ _

/-- **The infinite generalized Thue–Morse word.** Let $L, k \ge 2$, let
$\kappa : \{1, \dots, k-1\} \times \mathbb{N} \to \{0, \dots, L-1\}$ be a shift schedule, and let
$A_0, A_1, \dots$ be the blocks of the $(L, k, \kappa)$-Thue–Morse sequence. The infinite word
$A_\infty$ over the alphabet $\{0, \dots, L-1\}$ has, for every $m \in \mathbb{N}$, as its letter
at position $m$ (positions start at $0$) the letter at position $m$ of the block $A_{m+1}$,
which has $k^{m+1} > m$ letters.

The letter is read by checked indexing, with no default letter.

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public def infLetter (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m : Nat) : Fin L :=
  (block L k hL hk kappa (m + 1)).get
    ⟨m, by
      rw [block_length]
      exact lt_pow_succ_self hk m⟩

/-- **Later blocks agree with the infinite word.** Let $L, k \ge 2$, let
$\kappa : \{1, \dots, k-1\} \times \mathbb{N} \to \{0, \dots, L-1\}$ be a shift schedule, and let
$A_0, A_1, \dots$ be the blocks and $A_\infty$ the infinite word of the
$(L, k, \kappa)$-Thue–Morse sequence. For all $m, N \in \mathbb{N}$ with $m + 1 \le N$ and $m$
less than the length of $A_N$, the letter at position $m$ of $A_N$ equals the letter at
position $m$ of $A_\infty$ (positions start at $0$).

Source: JIS Definition 2.2 (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
public theorem infLetter_coherence (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m N : Nat) (hN : m + 1 ≤ N)
    (h : m < (block L k hL hk kappa N).length) :
    (block L k hL hk kappa N).get ⟨m, h⟩ = infLetter L k hL hk kappa m := by
  obtain ⟨tail, htail⟩ := block_prefix L k hL hk kappa hN
  have hm : m < (block L k hL hk kappa (m + 1)).length := by
    rw [block_length]
    exact lt_pow_succ_self hk m
  revert h
  rw [htail]
  intro h
  unfold infLetter
  exact get_append_left _ _ _ _ hm

/-- **Classical shift schedule.** The classical shift schedule is the map $\kappa$ that assigns
to the index $j = 1$ and every $n \in \mathbb{N}$ the letter $\kappa(1, n) = 1$ of the alphabet
$\{0, 1\}$. It is the schedule of the classical Thue–Morse sequence, the
$(L, k, \kappa)$-Thue–Morse sequence with $L = k = 2$.

Source: the classical $(2, 2, 1)$ example after JIS Definition 2.2 (concept
`jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
public def classicalKappa : Fin (2 - 1) → Nat → Fin 2 := fun _ _ => ⟨1, by decide⟩

/-- **Classical Thue–Morse blocks.** The classical Thue–Morse blocks are the blocks $A_n$ of the
$(2, 2, \kappa)$-Thue–Morse sequence with $\kappa(1, n) = 1$ for every $n \ge 0$. Thus $A_0$ is
the one-letter word $0$, and $A_{n+1}$ is $A_n$ followed by the word obtained from $A_n$ by
exchanging the letters $0$ and $1$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public def classicalBlock : Nat → List (Fin 2) :=
  block 2 2 (by decide) (by decide) classicalKappa

/-- **Length of the classical Thue–Morse blocks.** For every $n \in \mathbb{N}$, the classical
Thue–Morse block $A_n$ (the block $A_n$ of the $(L, k, \kappa)$-Thue–Morse sequence with
$L = k = 2$ and $\kappa(1, i) = 1$ for all $i \in \mathbb{N}$) has exactly $2^n$ letters.

Source: the classical $(2, 2, 1)$ example after JIS Definition 2.2 (concept
`jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
public theorem classical_length (n : Nat) : (classicalBlock n).length = 2 ^ n := by
  exact block_length 2 2 _ _ _ n

/-- **Classical Thue–Morse block of order 0.** The classical Thue–Morse block $A_0$ is the
one-letter word $0$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public theorem classical_A0 : classicalBlock 0 = [⟨0, by decide⟩] := by
  decide

/-- **Classical Thue–Morse block of order 1.** The classical Thue–Morse block $A_1$ is the word
$01$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public theorem classical_A1 : classicalBlock 1 = [⟨0, by decide⟩, ⟨1, by decide⟩] := by
  decide

/-- **Classical Thue–Morse block of order 2.** The classical Thue–Morse block $A_2$ is the word
$0110$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public theorem classical_A2 : classicalBlock 2 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by
  decide

/-- **Classical Thue–Morse block of order 3.** The classical Thue–Morse block $A_3$ is the word
$01101001$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public theorem classical_A3 : classicalBlock 3 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
     ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] := by
  decide

/-- **The classical Thue–Morse word begins with 01101001.** Let $A_\infty$ be the infinite word
of the $(2, 2, \kappa)$-Thue–Morse sequence with $\kappa(1, n) = 1$ for every $n \ge 0$. The
letters of $A_\infty$ at positions $0, 1, \dots, 7$ are $0, 1, 1, 0, 1, 0, 0, 1$, so $A_\infty$
begins with $01101001$.

Source: concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`. -/
public theorem classical_inf_init :
    infLetter 2 2 (by decide) (by decide) classicalKappa 0 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 1 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 2 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 3 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 4 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 5 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 6 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 7 = ⟨1, by decide⟩ := by
  decide

end GeneralizedThueMorse

end

end MetaMathlibExt
