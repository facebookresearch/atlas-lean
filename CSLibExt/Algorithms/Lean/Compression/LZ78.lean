/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Encoding


/-!
# LZ78 codec

The incremental parsing of J. Ziv and A. Lempel, *Compression of individual sequences via
variable-rate coding*, IEEE Trans. Inform. Theory 24(5) (1978), 530–536, Section II (the
parsing (12) and its coding, in the proof of Theorem 2), over a list-based dictionary, as an
instance of Mathlib's codec contract `Computability.Encoding`.

The parser cuts the input into phrases. Each phrase is the shortest nonempty prefix of the
unparsed input that is not an earlier phrase; if every nonempty prefix of the unparsed input is
an earlier phrase, the unparsed input is the last phrase. Each phrase becomes the next dictionary
entry, and an index points into the dictionary with the empty phrase in front: index `0` is the
empty phrase and index `j ≥ 1` the `j`-th phrase. A phrase is coded as the token `(i, some a)`,
where `a` is its last symbol and `i` is the index of the phrase without `a`, except a last phrase
that repeats an earlier one, which happens when the input ends inside a known phrase: that phrase
is coded as `(i, none)`, where `i` is its own index. The paper codes that last phrase like the
others.

`LZ78.decode` is a left inverse of `LZ78.encode`, not a validator: it rejects only dangling
indices, and it also accepts token lists that `LZ78.encode` never emits, such as an index-only
token before the end.
-/

@[expose] public section


namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- **LZ78 token.** An LZ78 token over a type $A$ is a pair `(i, s)` of a natural number `i` and
an optional symbol `s : Option A`. It stands for the dictionary entry at index `i`, where index
`0` is the empty phrase and index `j ≥ 1` is the `j`-th phrase, followed by the symbol `a` when
`s = some a` and by nothing when `s = none`. `LZ78.encode` emits an index-only token `(i, none)`
only as its last token, when the input ends inside a known phrase; `LZ78.decode` accepts one at
any position. -/
abbrev LZ78.Token (A : Type u) : Type u := ℕ × Option A

/-- Every proper prefix of a dictionary phrase is empty or a dictionary phrase. -/
private def LZ78.PrefixClosed {A : Type u} (dict : List (List A)) : Prop :=
  ∀ w ∈ dict, ∀ v : List A, v <+: w → v ≠ w → v = [] ∨ v ∈ dict

private theorem LZ78.prefixClosed_nil {A : Type u} : LZ78.PrefixClosed ([] : List (List A)) := by
  unfold LZ78.PrefixClosed
  intro w hw
  simp at hw

private theorem LZ78.prefixClosed_append_singleton {A : Type u} (dict : List (List A))
    (w0 : List A) (hclosed : LZ78.PrefixClosed dict)
    (hw : ∀ v : List A, v <+: w0 → v ≠ w0 → v = [] ∨ v ∈ dict) :
    LZ78.PrefixClosed (dict ++ [w0]) := by
  unfold LZ78.PrefixClosed
  intro u hu v hv hne
  simp only [List.mem_append, List.mem_singleton] at hu
  cases hu with
  | inl hmem =>
    cases hclosed u hmem v hv hne with
    | inl hnil => exact Or.inl hnil
    | inr hmem2 => exact Or.inr (List.mem_append_left _ hmem2)
  | inr heq =>
    subst heq
    cases hw v hv hne with
    | inl hnil => exact Or.inl hnil
    | inr hmem2 => exact Or.inr (List.mem_append_left _ hmem2)

/-- The index of a known phrase is at most the dictionary size. -/
private theorem LZ78.idxOf_le_length {A : Type u} [DecidableEq A] (dict : List (List A))
    (w : List A) (h : w = [] ∨ w ∈ dict) : ([] :: dict).idxOf w ≤ dict.length := by
  have hlt := List.idxOf_lt_length_iff.mpr (List.mem_cons.mpr h)
  rw [List.length_cons] at hlt
  omega

/-- **Next LZ78 phrase.** For a list of phrases $D$, a phrase $c$ and a finite list $x$, write
`ι v` for `([] :: D).idxOf v`, the first position of $v$ in the list $D$ with the empty phrase in
front (its length $|D| + 1$ when $v$ does not occur). If $x$ is empty, the result is the phrase
$c$, the token `(ι c, none)` and the empty list. If $x$ is a symbol $a$ followed by a list $x'$,
the result is that for the phrase `c ++ [a]` and $x'$ when `c ++ [a]` is an entry of $D$, and
otherwise the phrase `c ++ [a]`, the token `(ι c, some a)` and $x'$. -/
def LZ78.nextAux {A : Type u} [DecidableEq A] (dict : List (List A)) (cur : List A) :
    List A → List A × LZ78.Token A × List A
  | [] => (cur, (([] :: dict).idxOf cur, none), [])
  | a :: rest =>
    if cur ++ [a] ∈ dict then LZ78.nextAux dict (cur ++ [a]) rest
    else (cur ++ [a], (([] :: dict).idxOf cur, some a), rest)

private theorem LZ78.nextAux_append {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) : w ++ rest = cur ++ x := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      have hsub := ih _ _ _ _ h
      simpa [List.append_assoc] using hsub
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [List.append_assoc]

private theorem LZ78.nextAux_eq_nil {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) (hw : w = []) : cur = [] ∧ x = [] := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hw, rfl⟩
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      obtain ⟨hc, -⟩ := ih _ _ _ _ h hw
      simp at hc
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at hw

private theorem LZ78.nextAux_token {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) (hkn : cur = [] ∨ cur ∈ dict) :
    ∃ cur', (cur' = [] ∨ cur' ∈ dict) ∧ t.1 = ([] :: dict).idxOf cur' ∧
      w = cur' ++ t.2.toList := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨cur, hkn, rfl, by simp⟩
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      exact ih _ _ _ _ h (Or.inr hmem)
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨cur, hkn, rfl, rfl⟩

/-- An index-only token comes only with an exhausted input. -/
private theorem LZ78.nextAux_rest_eq_nil {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) (hnone : t.2 = none) : rest = [] := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      exact ih _ _ _ _ h hnone
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp at hnone

private theorem LZ78.nextAux_not_mem {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) (hrest : rest ≠ []) : w ∉ dict := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact absurd rfl hrest
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      exact ih _ _ _ _ h hrest
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hmem

private theorem LZ78.nextAux_prefix {A : Type u} [DecidableEq A] (dict : List (List A))
    (cur : List A) (x : List A) (w : List A) (t : LZ78.Token A) (rest : List A)
    (h : LZ78.nextAux dict cur x = (w, t, rest)) (v : List A) (hv : v <+: w) (hne : v ≠ w)
    (hkn : cur = [] ∨ cur ∈ dict) (hclosed : LZ78.PrefixClosed dict) :
    v = [] ∨ v ∈ dict := by
  induction x generalizing cur w t rest v with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases hkn with
    | inl hnil =>
      subst hnil
      exact Or.inl (List.prefix_nil.mp hv)
    | inr hmem => exact hclosed cur hmem v hv hne
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      exact ih _ _ _ _ h _ hv hne (Or.inr hmem)
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hle : v.length ≤ (cur ++ [a]).length := hv.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hle
      have hlen : v.length ≤ cur.length := by
        by_cases heq : v.length = cur.length + 1
        · have hlen2 : v.length = (cur ++ [a]).length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          exact absurd (hv.eq_of_length hlen2) hne
        · omega
      have hpre : v <+: cur :=
        List.prefix_of_prefix_length_le hv (List.prefix_append cur [a]) hlen
      by_cases heq2 : v = cur
      · subst heq2
        exact hkn
      · cases hkn with
        | inl hnil =>
          subst hnil
          exact Or.inl (List.prefix_nil.mp hpre)
        | inr hmem2 => exact hclosed cur hmem2 v hpre heq2

/-- **LZ78 phrases and tokens with fuel.** For a list of phrases $D$, a finite list $x$ and a
natural number $n$ (the fuel), the result is the pair of empty lists when $n = 0$ or $x$ is
empty. Otherwise, with `(w, t, x')` the next phrase of $x$ from the empty phrase
(`LZ78.nextAux D [] x`), it is the result for the list `D ++ [w]`, the rest $x'$ and the fuel
$n - 1$, with $w$ put in front of its phrases and $t$ in front of its tokens. Each step consumes
at least one symbol, so the fuel $|x| + 1$ parses all of $x$. -/
def LZ78.parseEncodeAux {A : Type u} [DecidableEq A] (dict : List (List A)) (x : List A) :
    ℕ → List (List A) × List (LZ78.Token A)
  | 0 => ([], [])
  | fuel + 1 =>
    match x with
    | [] => ([], [])
    | _ :: _ =>
      match LZ78.nextAux dict [] x with
      | (w, t, rest) =>
        match LZ78.parseEncodeAux (dict ++ [w]) rest fuel with
        | (phs, toks) => (w :: phs, t :: toks)

private theorem LZ78.parseEncodeAux_nil {A : Type u} [DecidableEq A] (dict : List (List A))
    (fuel : ℕ) : LZ78.parseEncodeAux dict [] fuel = ([], []) := by
  cases fuel <;> rfl

private theorem LZ78.aux_length {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) : toks.length = phs.length := by
  induction fuel generalizing dict x phs toks with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rfl
    | cons a r =>
      obtain ⟨w, t, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hsub2 := ih _ _ _ _ hsub
      simp only [List.length_cons, hsub2]

private theorem LZ78.aux_ne_nil {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (w : List A) (hw : w ∈ phs) :
    w ≠ [] := by
  induction fuel generalizing dict x phs toks w with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at hw
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp at hw
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [List.mem_cons] at hw
      cases hw with
      | inl heq2 =>
        rw [heq2]
        intro hnil
        obtain ⟨hc, hx⟩ := LZ78.nextAux_eq_nil dict [] (a :: r) w0 t0 rest hnext hnil
        simp at hx
      | inr hmem => exact ih _ _ _ _ hsub _ hmem

private theorem LZ78.aux_flatten {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (hfuel : x.length < fuel) :
    phs.flatten = x := by
  induction fuel generalizing dict x phs toks with
  | zero => simp at hfuel
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rfl
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hwx : w0 ≠ [] := by
        intro hnil
        obtain ⟨hc, hx⟩ := LZ78.nextAux_eq_nil dict [] (a :: r) w0 t0 rest hnext hnil
        simp at hx
      have hlen :=
        congrArg List.length (LZ78.nextAux_append dict [] (a :: r) w0 t0 rest hnext)
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      simp only [List.length_cons] at hfuel
      have hwlen : w0.length ≠ 0 := by simpa using hwx
      have hfuel' : rest.length < fuel := by omega
      have ihflat := ih _ _ _ _ hsub hfuel'
      simp only [List.flatten_cons, ihflat]
      have happ := LZ78.nextAux_append dict [] (a :: r) w0 t0 rest hnext
      simpa using happ

private theorem LZ78.aux_fst_le {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (i : ℕ) (hi : i < toks.length) :
    (toks[i]).1 ≤ dict.length + i := by
  induction fuel generalizing dict x phs toks i with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at hi
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp at hi
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases i with
      | zero =>
        rw [List.getElem_cons_zero]
        obtain ⟨cur', hkn', hidx, -⟩ :=
          LZ78.nextAux_token dict [] (a :: r) w0 t0 rest hnext (Or.inl rfl)
        rw [hidx]
        have hle := LZ78.idxOf_le_length dict cur' hkn'
        omega
      | succ j =>
        rw [List.getElem_cons_succ]
        have hi' : j < toks'.length := by simp only [List.length_cons] at hi ⊢; omega
        have ih' := ih _ _ _ _ hsub j hi'
        simp only [List.length_append, List.length_cons, List.length_nil] at ih'
        omega

private theorem LZ78.aux_isSome {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (t : LZ78.Token A)
    (ht : t ∈ toks.dropLast) : t.2.isSome := by
  induction fuel generalizing dict x phs toks with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at ht
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp at ht
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases toks' with
      | nil => simp at ht
      | cons t1 toks'' =>
        rw [List.dropLast_cons_cons, List.mem_cons] at ht
        rcases ht with h0 | ht
        · subst h0
          cases hs : t.2 with
          | some _ => rfl
          | none =>
            have hrest := LZ78.nextAux_rest_eq_nil dict [] (a :: r) w0 t rest hnext hs
            subst hrest
            rw [LZ78.parseEncodeAux_nil] at hsub
            simp at hsub
        · exact ih _ _ _ _ hsub ht

private theorem LZ78.aux_prefix_mem {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (hclosed : LZ78.PrefixClosed dict)
    (i : ℕ) (hi : i < phs.length) (v : List A) (hv : v <+: phs[i])
    (hne : v ≠ phs[i]) : v = [] ∨ v ∈ dict ++ phs.take i := by
  induction fuel generalizing dict x phs toks i v with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at hi
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp at hi
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hclosed' : LZ78.PrefixClosed (dict ++ [w0]) :=
        LZ78.prefixClosed_append_singleton dict w0 hclosed (fun u hu hne2 =>
          LZ78.nextAux_prefix dict [] (a :: r) w0 t0 rest hnext u hu hne2 (Or.inl rfl)
            hclosed)
      cases i with
      | zero =>
        rw [List.getElem_cons_zero] at hv hne
        cases LZ78.nextAux_prefix dict [] (a :: r) w0 t0 rest hnext v hv hne (Or.inl rfl)
          hclosed with
        | inl hnil => exact Or.inl hnil
        | inr hmem => exact Or.inr (List.mem_append_left _ hmem)
      | succ j =>
        rw [List.getElem_cons_succ] at hv hne
        have hi' : j < phs'.length := by simp only [List.length_cons] at hi ⊢; omega
        have ih' := ih _ _ _ _ hsub hclosed' j hi' v hv hne
        have happ : dict ++ (w0 :: phs').take (j + 1) = (dict ++ [w0]) ++ phs'.take j := by
          simp [List.take_succ_cons, List.append_assoc]
        rw [happ]
        exact ih'

private theorem LZ78.aux_nodup_dropLast {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) (hfuel : x.length < fuel)
    (hnodup : dict.Nodup) (hclosed : LZ78.PrefixClosed dict) :
    (dict ++ phs).dropLast.Nodup := by
  induction fuel generalizing dict x phs toks with
  | zero => simp at hfuel
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [List.append_nil]
      exact List.Nodup.sublist (List.dropLast_sublist dict) hnodup
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases phs' with
      | nil =>
        rw [List.dropLast_concat]
        exact hnodup
      | cons w2 phs'' =>
        have hwx : w0 ≠ [] := by
          intro hnil
          obtain ⟨hc, hx⟩ := LZ78.nextAux_eq_nil dict [] (a :: r) w0 t0 rest hnext hnil
          simp at hx
        have hlen :=
          congrArg List.length (LZ78.nextAux_append dict [] (a :: r) w0 t0 rest hnext)
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        simp only [List.length_cons] at hfuel
        have hwlen : w0.length ≠ 0 := by simpa using hwx
        have hfuel' : rest.length < fuel := by omega
        have hflat := LZ78.aux_flatten _ _ _ _ _ hsub hfuel'
        have hne2 := LZ78.aux_ne_nil _ _ _ _ _ hsub w2 (by simp)
        have hrest : rest ≠ [] := by
          rw [← hflat]
          simp [hne2]
        have hnotmem := LZ78.nextAux_not_mem dict [] (a :: r) w0 t0 rest hnext hrest
        have hnodup' : (dict ++ [w0]).Nodup := by
          rw [List.nodup_append]
          refine ⟨hnodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst hb
          intro heq2
          subst heq2
          exact hnotmem ha
        have hclosed' : LZ78.PrefixClosed (dict ++ [w0]) :=
          LZ78.prefixClosed_append_singleton dict w0 hclosed (fun u hu hne2 =>
            LZ78.nextAux_prefix dict [] (a :: r) w0 t0 rest hnext u hu hne2 (Or.inl rfl)
              hclosed)
        have ih' := ih _ _ _ _ hsub hfuel' hnodup' hclosed'
        have happ : dict ++ (w0 :: w2 :: phs'') = (dict ++ [w0]) ++ (w2 :: phs'') := by
          simp [List.append_assoc]
        rw [happ]
        exact ih'

/-- **LZ78 decoding from a dictionary.** For a list of phrases $D$ and a list of tokens, the
result is `some []` when there are no tokens. For a token `(i, s)` followed by tokens $T$, it is
`none` when $i > |D|$ (a dangling index). Otherwise, with $p$ the entry at position $i$ of the
list $D$ with the empty phrase in front and $w$ the phrase `p ++ s.toList` ($p$ followed by the
symbol of $s$, if any), it is `none` when decoding $T$ from the list `D ++ [w]` fails, and that
result with $w$ in front otherwise. -/
def LZ78.decodeAux {A : Type u} (dict : List (List A)) :
    List (LZ78.Token A) → Option (List (List A))
  | [] => some []
  | (i, s) :: ts =>
    match ([] :: dict)[i]? with
    | none => none
    | some p =>
      match LZ78.decodeAux (dict ++ [p ++ s.toList]) ts with
      | none => none
      | some ws => some ((p ++ s.toList) :: ws)

private theorem LZ78.aux_decode {A : Type u} [DecidableEq A] (dict : List (List A))
    (x : List A) (fuel : ℕ) (phs : List (List A)) (toks : List (LZ78.Token A))
    (heq : LZ78.parseEncodeAux dict x fuel = (phs, toks)) :
    LZ78.decodeAux dict toks = some phs := by
  induction fuel generalizing dict x phs toks with
  | zero =>
    simp only [LZ78.parseEncodeAux] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  | succ fuel ih =>
    cases x with
    | nil =>
      simp only [LZ78.parseEncodeAux] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rfl
    | cons a r =>
      obtain ⟨w0, t0, rest, hnext⟩ :
        ∃ w t rest, LZ78.nextAux dict [] (a :: r) = (w, t, rest) := ⟨_, _, _, rfl⟩
      obtain ⟨phs', toks', hsub⟩ :
        ∃ phs toks, LZ78.parseEncodeAux (dict ++ [w0]) rest fuel = (phs, toks) := ⟨_, _, rfl⟩
      simp only [LZ78.parseEncodeAux, hnext, hsub] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨i0, s0⟩ := t0
      obtain ⟨cur', hkn', hidx, hww⟩ :=
        LZ78.nextAux_token dict [] (a :: r) w0 (i0, s0) rest hnext (Or.inl rfl)
      have hget : ([] :: dict)[i0]? = some cur' := by
        rw [show i0 = ([] :: dict).idxOf cur' from hidx]
        exact List.getElem?_idxOf (List.mem_cons.mpr hkn')
      have hww' : w0 = cur' ++ s0.toList := hww
      subst hww'
      simp only [LZ78.decodeAux, hget, ih _ _ _ _ hsub]

/-- **LZ78 incremental parsing.** The LZ78 parse of a finite list $x$ is the list of phrases that
`LZ78.parseEncodeAux [] x (|x| + 1)` returns. Each phrase is the shortest nonempty prefix of the
unparsed input that is not an earlier phrase; if every nonempty prefix of the unparsed input is
an earlier phrase, the unparsed input is the last phrase. -/
def LZ78.parse {A : Type u} [DecidableEq A] (x : List A) : List (List A) :=
  (LZ78.parseEncodeAux [] x (x.length + 1)).1

/-- **LZ78 encoding.** The LZ78 encoding of a finite list $x$ is the list of tokens that
`LZ78.parseEncodeAux [] x (|x| + 1)` returns, one for each phrase of `LZ78.parse x`, with index
`0` for the empty phrase and index `j ≥ 1` for the `j`-th phrase. A last phrase that repeats an
earlier one, which happens exactly when the input ends inside a known phrase, is coded as
`(i, none)`, where `i` is its own index. Every other phrase is coded as `(i, some a)`, where `a`
is its last symbol and `i` is the index of the phrase without `a`, the empty phrase or an earlier
phrase. -/
def LZ78.encode {A : Type u} [DecidableEq A] (x : List A) : List (LZ78.Token A) :=
  (LZ78.parseEncodeAux [] x (x.length + 1)).2

private theorem LZ78.aux_parse_encode_eq {A : Type u} [DecidableEq A] (x : List A) :
    LZ78.parseEncodeAux [] x (x.length + 1) = (LZ78.parse x, LZ78.encode x) := rfl

/-- **LZ78 decoding.** The LZ78 decoding of a list of tokens reads them in order with a dictionary
that starts empty. A token `(i, s)` whose index `i` is at most the number of tokens before it is
decoded to the empty phrase (`i = 0`) or the `i`-th decoded phrase, followed by the symbol `a`
when `s = some a`; the decoded phrase becomes the next dictionary entry. The result is the
concatenation of the decoded phrases, or `none` when some token's index exceeds the number of
tokens before it. Decoding does not check that the tokens are ones `LZ78.encode` emits: it
accepts an index-only token `(i, none)` at any position, decoding it to the phrase at index `i`
and adding a copy of that phrase to the dictionary, and a token whose phrase is already in the
dictionary. -/
def LZ78.decode {A : Type u} (ts : List (LZ78.Token A)) : Option (List A) :=
  (LZ78.decodeAux [] ts).map List.flatten

/-- **LZ78 decoding inverts encoding.** For every type $A$ with decidable equality and every
finite list $x$ over $A$, decoding the LZ78 encoding of $x$ returns $x$:
`LZ78.decode (LZ78.encode x) = some x`. -/
theorem LZ78.decode_encode {A : Type u} [DecidableEq A] (x : List A) :
    LZ78.decode (LZ78.encode x) = some x := by
  have hde := LZ78.aux_decode [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
  unfold LZ78.decode
  rw [hde, Option.map_some]
  congr 1
  exact LZ78.aux_flatten [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    (Nat.lt_succ_self _)

/-- **LZ78 codec.** The LZ78 encoder `LZ78.encode` and decoder `LZ78.decode`, with the round trip
`LZ78.decode_encode`, as an instance of Mathlib's `Computability.Encoding` contract for finite
lists over a type $A$ with decidable equality, with LZ78 tokens as the code alphabet. -/
def LZ78.encoding {A : Type u} [DecidableEq A] :
    Computability.Encoding (List A) (LZ78.Token A) where
  encode := LZ78.encode
  decode := LZ78.decode
  decode_encode := LZ78.decode_encode

/-- **LZ78 phrases concatenate to the input.** For every finite list $x$, the concatenation of
the phrases of the LZ78 parse of $x$ is $x$. -/
theorem LZ78.flatten_parse {A : Type u} [DecidableEq A] (x : List A) :
    (LZ78.parse x).flatten = x := by
  exact LZ78.aux_flatten [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    (Nat.lt_succ_self _)

/-- **LZ78 phrases are nonempty.** For every finite list $x$, every phrase of the LZ78 parse of
$x$ is nonempty. -/
theorem LZ78.ne_nil_of_mem_parse {A : Type u} [DecidableEq A] {x w : List A}
    (hw : w ∈ LZ78.parse x) : w ≠ [] := by
  exact LZ78.aux_ne_nil [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) w hw

/-- **LZ78 phrases are distinct, except possibly the last.** For every finite list $x$, the
phrases of the LZ78 parse of $x$ other than the last are pairwise distinct. -/
theorem LZ78.nodup_dropLast_parse {A : Type u} [DecidableEq A] (x : List A) :
    (LZ78.parse x).dropLast.Nodup := by
  have h := LZ78.aux_nodup_dropLast [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    (Nat.lt_succ_self _) List.nodup_nil LZ78.prefixClosed_nil
  simpa using h

/-- **Proper prefixes of an LZ78 phrase are earlier phrases.** For every finite list $x$ and
every index $i$ below the number of phrases of its LZ78 parse, every proper prefix of the $i$-th
phrase (counting from $0$) is empty or one of the phrases before it. -/
theorem LZ78.prefix_mem_parse {A : Type u} [DecidableEq A] (x : List A) (i : ℕ)
    (hi : i < (LZ78.parse x).length) {v : List A} (hv : v <+: (LZ78.parse x)[i])
    (hne : v ≠ (LZ78.parse x)[i]) : v = [] ∨ v ∈ (LZ78.parse x).take i := by
  have h := LZ78.aux_prefix_mem [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    LZ78.prefixClosed_nil i hi v hv hne
  simpa using h

/-- **One LZ78 token per phrase.** For every finite list $x$, the LZ78 codec encodes $x$ into as
many tokens as the LZ78 parse of $x$ has phrases. -/
theorem LZ78.encoding_encode_length {A : Type u} [DecidableEq A] (x : List A) :
    ((LZ78.encoding (A := A)).encode x).length = (LZ78.parse x).length := by
  have h := LZ78.aux_length [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
  simpa [LZ78.encoding] using h

/-- **LZ78 token indices point backwards.** For every finite list $x$ and every index $i$ below
the number of tokens of its LZ78 encoding, the index of the $i$-th token (counting from $0$) is
at most $i$: it names the empty phrase or one of the $i$ phrases before it. -/
theorem LZ78.fst_encode_le {A : Type u} [DecidableEq A] (x : List A) (i : ℕ)
    (hi : i < (LZ78.encode x).length) : ((LZ78.encode x)[i]).1 ≤ i := by
  have h := LZ78.aux_fst_le [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) i hi
  simpa using h

/-- **Only the last LZ78 token can omit its symbol.** For every finite list $x$, every token of
the LZ78 encoding of $x$ other than the last carries a symbol: an index-only token `(i, none)`
can only be the last token. -/
theorem LZ78.isSome_snd_of_mem_dropLast_encode {A : Type u} [DecidableEq A] {x : List A}
    {t : LZ78.Token A} (ht : t ∈ (LZ78.encode x).dropLast) : t.2.isSome :=
  LZ78.aux_isSome [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) t ht

end Cslib.Algorithms.Lean
