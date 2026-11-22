/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Path

/-!
# Correctness of the PATH marking algorithm

`pathDec_eq_pathCheck`: the marking algorithm `pathCheck` of
`CSLibExt.Computability.Complexity.Path` decides PATH (Sipser, Theorem 7.14).

* The codec: `decodeP_eq_some` (`decodeP` reads back exactly the encodings `encodeP`).
* Soundness: a pass keeps every mark reachable from `s` (`markPass_sound`), and `initMarks n s`
  marks only `s`.
* Completeness: a pass marks `v` for every arc `(u, v)` with `u` marked (`markPass_closed`), so at
  a fixpoint of `markPass` the marks are closed under arcs. A pass either changes nothing or
  sets a new mark (`markPass_eq_or_count_lt`); there are at most `n` marks and `initMarks n s`
  has one, so `n` passes reach a fixpoint (`markPass_reachMarks`), without arguing about paths.
* `reachMarks_getD_iff`: after `n` passes, `t < n` is marked iff it is reachable from `s`.
-/

public section

namespace Cslib.Complexity.Path

open Cslib.CookLevin

/-! ### The instance codec -/

/-- **Decoding inverts the PATH instance encoding.** For natural numbers $s, t, n$ and a list $E$
of pairs of natural numbers, the PATH instance parser applied to the PATH instance encoding of
$(s, t, n, E)$ succeeds and returns $(s, t, n, E)$. -/
@[simp] theorem decodeP_encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) :
    decodeP (encodeP s t n es) = some (s, t, n, es) := by
  simp [decodeP, encodeP, Karp.decodeE_encodeE]

/-- **The PATH instance parser succeeds exactly on encodings.** For a bit string $x$, natural
numbers $s, t, n$ and a list $E$ of pairs of natural numbers, the PATH instance parser applied to
$x$ succeeds with result $(s, t, n, E)$ if and only if $x$ is the PATH instance encoding of
$(s, t, n, E)$. -/
theorem decodeP_eq_some {x : List Bool} {s t n : ℕ} {es : List (ℕ × ℕ)} :
    decodeP x = some (s, t, n, es) ↔ encodeP s t n es = x := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeP_encodeP s t n es⟩
  unfold decodeP at h
  split at h
  · simp at h
  · rename_i s' r hr
    split at h
    · simp at h
    · rename_i t' r' hr'
      cases he : Karp.decodeE r' with
      | none => simp [he] at h
      | some p =>
          obtain ⟨n', es'⟩ := p
          simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          rw [(readUnaryLength_eq_some_iff _ _ _).1 hr, (readUnaryLength_eq_some_iff _ _ _).1 hr',
            ← Karp.encodeE_of_decodeE he]
          rfl

/-- **The PATH instance encoding is injective.** Let $s, t, n, s', t', n'$ be natural numbers and
$E, E'$ lists of pairs of natural numbers. If the PATH instance encodings of $(s, t, n, E)$ and
$(s', t', n', E')$ are equal, then $s = s'$, $t = t'$, $n = n'$ and $E = E'$. -/
theorem encodeP_inj {s t n s' t' n' : ℕ} {es es' : List (ℕ × ℕ)}
    (h : encodeP s t n es = encodeP s' t' n' es') : s = s' ∧ t = t' ∧ n = n' ∧ es = es' := by
  simpa using congrArg decodeP h

/-! ### Marks -/

/-- **Setting an entry of a boolean list to true.** Let $m$ be a list of booleans and $v, w$
natural numbers, and read a position at or beyond the end of a list as $\mathrm{false}$. Set
the entry of $m$ at position $w$ to $\mathrm{true}$, leaving $m$ unchanged if $w$ is not less
than the length of $m$. Then position $v$ of the result holds $\mathrm{true}$ if and only if
position $v$ of $m$ holds $\mathrm{true}$, or $v = w$ and $w$ is less than the length of $m$. -/
theorem getD_set_true {m : List Bool} {w v : ℕ} :
    (m.set w true).getD v false = true ↔ m.getD v false = true ∨ (v = w ∧ w < m.length) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hwv : w = v
  · subst hwv
    by_cases hw : w < m.length
    · simp [hw]
    · simp [hw]
  · simp [hwv, Ne.symm hwv]

/-- **The initial marks mark exactly the source, if it is a vertex.** Let $n, s, v$ be natural
numbers, and read a position at or beyond the end of a list as $\mathrm{false}$. Position $v$ of
the initial marks for $n$ vertices and source $s$ holds $\mathrm{true}$ if and only if $v < n$
and $v = s$. -/
theorem initMarks_getD {n s v : ℕ} : (initMarks n s).getD v false = true ↔ v < n ∧ v = s := by
  by_cases hv : v < n
  · simp [initMarks, List.getD_eq_getElem?_getD, hv]
  · simp [initMarks, List.getD_eq_getElem?_getD, hv]

/-- **A marking pass preserves the length.** Let $n$ be a natural number, $E$ a list of pairs of
natural numbers and $m$ a list of booleans. A marking pass over $E$ for $n$ vertices, applied to
$m$, gives a list of the same length as $m$. -/
theorem length_markPass (n : ℕ) :
    ∀ (es : List (ℕ × ℕ)) (m : List Bool), (markPass n es m).length = m.length
  | [], _ => rfl
  | (_, _) :: es, m => by
      rw [markPass, length_markPass n es]
      split_ifs <;> simp

/-- **Marks persist through a pass.** Let $n, v \in \mathbb{N}$, let $E$ be a list of pairs of
natural numbers and let $m$ be a list of booleans. If $v < |m|$ and the $v$-th entry of $m$
(counting from $0$) is true, then the same holds for the result of the marking pass of $E$ with
bound $n$ on $m$. -/
theorem markPass_mono (n : ℕ) {v : ℕ} : ∀ (es : List (ℕ × ℕ)) {m : List Bool},
    m.getD v false = true → (markPass n es m).getD v false = true
  | [], _, h => h
  | (_, _) :: es, m, h => by
      rw [markPass]
      apply markPass_mono n es
      split_ifs
      · exact getD_set_true.2 (Or.inl h)
      · exact h

/-- **Soundness of a pass.** Let $n \in \mathbb{N}$, let $P$ be a property of natural numbers and
let $E$ be a list of pairs of natural numbers such that $P(u)$ implies $P(v)$ whenever
$(u, v) \in E$, $u < n$ and $v < n$. If $m$ is a list of booleans such that $P(v)$ holds for every
$v < |m|$ whose entry in $m$ is true, then $P(v)$ holds for every $v$ whose entry is true in the
result of the marking pass of $E$ with bound $n$ on $m$. -/
theorem markPass_sound {n : ℕ} {P : ℕ → Prop} : ∀ (es : List (ℕ × ℕ)),
    (∀ u v, (u, v) ∈ es → u < n → v < n → P u → P v) → ∀ {m : List Bool},
    (∀ v, m.getD v false = true → P v) → ∀ v, (markPass n es m).getD v false = true → P v
  | [], _, _, hm => hm
  | (a, b) :: es, hP, m, hm => by
      rw [markPass]
      refine markPass_sound es (fun u v h => hP u v (List.mem_cons_of_mem _ h)) ?_
      split_ifs with hab
      · intro v hv
        rcases getD_set_true.1 hv with hv | ⟨rfl, -⟩
        · exact hm v hv
        · exact hP _ _ List.mem_cons_self hab.1 hab.2.1 (hm a hab.2.2)
      · exact hm

/-- **A pass marks the heads of arcs with marked tails.** Let $n \in \mathbb{N}$, let $E$ be a
list of pairs of natural numbers and let $m$ be a list of booleans, where $m$ marks $w$ when
$w < |m|$ and the $w$-th entry of $m$ (counting from $0$) is true. If $(u, v) \in E$ with $u < n$
and $v < n$, $v < |m|$ and $m$ marks $u$, then the result of the marking pass of $E$ with bound $n$
on $m$ marks $v$. -/
theorem markPass_closed {n u v : ℕ} (hu : u < n) (hv : v < n) :
    ∀ {es : List (ℕ × ℕ)} {m : List Bool}, (u, v) ∈ es → v < m.length →
      m.getD u false = true → (markPass n es m).getD v false = true
  | [], _, hmem, _, _ => by simp at hmem
  | (a, b) :: es, m, hmem, hlen, hm => by
      rw [markPass]
      rcases List.mem_cons.1 hmem with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp only [hu, hv, hm, and_self, ↓reduceIte]
        exact markPass_mono n es (getD_set_true.2 (Or.inr ⟨rfl, hlen⟩))
      · apply markPass_closed hu hv h
        · split_ifs <;> simp [hlen]
        · split_ifs
          · exact getD_set_true.2 (Or.inl hm)
          · exact hm

/-- **Counting true entries of pointwise dominated boolean lists.** Let $l_1$ and $l_2$ be lists
of booleans of the same length such that every position holding $\mathrm{true}$ in $l_1$ also
holds $\mathrm{true}$ in $l_2$. Then $l_1$ has at most as many $\mathrm{true}$ entries as $l_2$,
and strictly fewer if $l_1 \ne l_2$. -/
theorem count_lt_of_getD_imp : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length →
    (∀ i, l₁.getD i false = true → l₂.getD i false = true) →
    l₁.count true ≤ l₂.count true ∧ (l₁ ≠ l₂ → l₁.count true < l₂.count true)
  | [], [], _, _ => ⟨le_rfl, fun h => (h rfl).elim⟩
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, hlen, hle => by
      have h0 : a = true → b = true := by simpa using hle 0
      have ih := count_lt_of_getD_imp (l₁ := l₁) (l₂ := l₂) (by simpa using hlen)
        (fun i h => by simpa using hle (i + 1) (by simpa using h))
      cases a <;> cases b <;> simp_all
      omega

/-- **A pass either changes nothing or adds a mark.** For every $n \in \mathbb{N}$, every list $E$
of pairs of natural numbers and every list $m$ of booleans, let $m'$ be the result of the marking
pass of $E$ with bound $n$ on $m$. Then $m' = m$, or $m'$ has strictly more entries equal to true
than $m$. -/
theorem markPass_eq_or_count_lt (n : ℕ) (es : List (ℕ × ℕ)) (m : List Bool) :
    markPass n es m = m ∨ m.count true < (markPass n es m).count true := by
  by_cases he : m = markPass n es m
  · exact Or.inl he.symm
  · exact Or.inr ((count_lt_of_getD_imp (length_markPass n es m).symm
      (fun _ => markPass_mono n es)).2 he)

/-- **Repeated marking passes preserve the length.** Let $n$ be a natural number, $E$ a list of
pairs of natural numbers and $m$ a list of booleans. For every natural number $k$, applying $k$
marking passes over $E$ for $n$ vertices to $m$ gives a list of the same length as $m$. -/
theorem length_iterate_markPass (n : ℕ) (es : List (ℕ × ℕ)) (m : List Bool) :
    ∀ k, ((markPass n es)^[k] m).length = m.length
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', length_markPass, length_iterate_markPass]

/-- **Marks survive repeated passes.** Let $n$ and $v$ be natural numbers, $E$ a list of pairs of
natural numbers and $m$ a list of booleans whose position $v$ holds $\mathrm{true}$ (positions at
or beyond the end read as $\mathrm{false}$). Then for every natural number $k$, position $v$
still holds $\mathrm{true}$ after $k$ marking passes over $E$ for $n$ vertices, starting from
$m$. -/
theorem iterate_markPass_mono (n : ℕ) (es : List (ℕ × ℕ)) {m : List Bool} {v : ℕ}
    (h : m.getD v false = true) : ∀ k, ((markPass n es)^[k] m).getD v false = true
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact markPass_mono n es (iterate_markPass_mono n es h k)

/-- **The final marks have one entry per vertex.** For natural numbers $n, s$ and a list $E$ of
pairs of natural numbers, the marks after $n$ marking passes over $E$ for $n$ vertices, starting
from the initial marks for source $s$, form a list of length $n$. -/
theorem length_reachMarks (n s : ℕ) (es : List (ℕ × ℕ)) : (reachMarks n s es).length = n := by
  rw [reachMarks, length_iterate_markPass]
  simp [initMarks]

/-- **Repeated passes reach a fixpoint.** Let $n, s \in \mathbb{N}$ with $s < n$ and let $E$ be a
list of pairs of natural numbers. Let $r$ be the list obtained from the initial marks (only $s$
marked among $0, \dots, n - 1$) by $n$ marking passes of $E$ with bound $n$. Then one more
marking pass of $E$ with bound $n$ leaves $r$ unchanged.

Each pass that changes the marks adds at least one mark, the initial marks contain one mark, and
there are at most $n$ marks. -/
theorem markPass_reachMarks {n s : ℕ} (es : List (ℕ × ℕ)) (hs : s < n) :
    markPass n es (reachMarks n s es) = reachMarks n s es := by
  have key : ∀ k, markPass n es ((markPass n es)^[k] (initMarks n s)) =
        (markPass n es)^[k] (initMarks n s) ∨
      (initMarks n s).count true + k ≤ ((markPass n es)^[k] (initMarks n s)).count true := by
    intro k
    induction k with
    | zero => exact Or.inr le_rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases markPass_eq_or_count_lt n es ((markPass n es)^[k] (initMarks n s)) with h | h
        · left
          rw [h, h]
        · rcases ih with ih | ih
          · rw [ih] at h
            exact absurd h (lt_irrefl _)
          · right
            omega
  have h1 : 0 < (initMarks n s).count true :=
    List.count_pos_iff.2 (List.mem_map.2 ⟨s, List.mem_range.2 hs, by simp⟩)
  rcases key n with h | h
  · exact h
  · have hle := List.count_le_length (a := true) (l := (markPass n es)^[n] (initMarks n s))
    rw [length_iterate_markPass] at hle
    simp only [initMarks, List.length_map, List.length_range] at hle
    exact absurd (h.trans hle) (by omega)

/-! ### Correctness -/

/-- **The final marks are exactly the reachable vertices.** Let $n, s, t \in \mathbb{N}$ with
$s < n$ and $t < n$, and let $E$ be a list of pairs of natural numbers. Start from the marks on
$0, \dots, n - 1$ in which only $s$ is marked and apply $n$ marking passes of $E$ with bound $n$.
Then $t$ is marked if and only if $t$ is reachable from $s$ in zero or more steps along the arcs
of $E$ below $n$, the pairs $(u, v) \in E$ with $u < n$ and $v < n$. -/
theorem reachMarks_getD_iff {n s t : ℕ} (es : List (ℕ × ℕ)) (hs : s < n) (ht : t < n) :
    (reachMarks n s es).getD t false = true ↔ Relation.ReflTransGen (arc n es) s t := by
  constructor
  · have key : ∀ k v, ((markPass n es)^[k] (initMarks n s)).getD v false = true →
        Relation.ReflTransGen (arc n es) s v := by
      intro k
      induction k with
      | zero =>
          intro v hv
          obtain ⟨-, rfl⟩ := initMarks_getD.1 hv
          exact .refl
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact markPass_sound es (fun u v huv hu hv h => h.tail ⟨huv, hu, hv⟩) ih
    exact key n t
  · intro h
    induction h with
    | refl => exact iterate_markPass_mono n es (initMarks_getD.2 ⟨hs, rfl⟩) n
    | tail _ hbc ih =>
        obtain ⟨hmem, hb, hc⟩ := hbc
        rw [← markPass_reachMarks es hs]
        exact markPass_closed hb hc hmem ((length_reachMarks n s es).symm ▸ ht) (ih hb)

/-- **The marking algorithm decides PATH.** For every bit string $x$, the marking algorithm
returns the same answer on $x$ as the decision problem PATH. -/
theorem pathDec_eq_pathCheck (x : List Bool) : pathDec x = pathCheck x := by
  rw [Bool.eq_iff_iff]
  simp only [pathDec, decide_eq_true_eq]
  unfold pathCheck
  cases h : decodeP x with
  | none =>
      simp only [Bool.false_eq_true, iff_false, not_exists, not_and]
      rintro s t n es rfl
      simp at h
  | some p =>
      obtain ⟨s, t, n, es⟩ := p
      obtain rfl := decodeP_eq_some.1 h
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨s', t', n', es', he, hs, ht, hr⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := encodeP_inj he.symm
        exact ⟨⟨hs, ht⟩, (reachMarks_getD_iff es hs ht).2 hr⟩
      · rintro ⟨⟨hs, ht⟩, hm⟩
        exact ⟨s, t, n, es, rfl, hs, ht, (reachMarks_getD_iff es hs ht).1 hm⟩

end Cslib.Complexity.Path
