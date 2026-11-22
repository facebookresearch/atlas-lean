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

LZ78 incremental parsing over a list-based dictionary, as an instance of the codec contract `Computability.Encoding` (Ziv-Lempel 1978, Sec. II-III).
-/

@[expose] public section


namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

abbrev LZ78.Token (A : Type u) : Type u := ℕ × Option A

/-- Extend a dictionary phrase by an optional symbol. -/
def LZ78.applySym {A : Type u} (p : List A) : Option A → List A
  | none => p
  | some a => p ++ [a]

private theorem LZ78.applySym_none {A : Type u} (p : List A) : LZ78.applySym p none = p := rfl

private theorem LZ78.applySym_some {A : Type u} (p : List A) (a : A) :
    LZ78.applySym p (some a) = p ++ [a] := rfl

/-- Dictionary index of a phrase: `0` for the empty phrase, position + 1 otherwise. -/
def LZ78.dictIdx {A : Type u} [DecidableEq A] (dict : List (List A)) (w : List A) : ℕ :=
  if w = [] then 0
  else
    match dict with
    | [] => 1
    | d :: ds => if w = d then 1 else LZ78.dictIdx ds w + 1

private theorem LZ78.dictIdx_nil_eq {A : Type u} [DecidableEq A] (dict : List (List A)) :
    LZ78.dictIdx dict [] = 0 := by
  unfold LZ78.dictIdx
  simp

private theorem LZ78.dictIdx_empty {A : Type u} [DecidableEq A] (a : A) (as : List A) :
    LZ78.dictIdx [] (a :: as) = 1 := by
  unfold LZ78.dictIdx
  simp

private theorem LZ78.dictIdx_cons_eq {A : Type u} [DecidableEq A] {d : List A}
    {ds : List (List A)} {w : List A} (hne : w ≠ []) (heq : w = d) :
    LZ78.dictIdx (d :: ds) w = 1 := by
  subst heq
  unfold LZ78.dictIdx
  simp [hne]

private theorem LZ78.dictIdx_cons_ne {A : Type u} [DecidableEq A] {d : List A}
    {ds : List (List A)} {w : List A} (hne : w ≠ []) (hne2 : w ≠ d) :
    LZ78.dictIdx (d :: ds) w = LZ78.dictIdx ds w + 1 := by
  rw [LZ78.dictIdx.eq_def]
  simp [hne, hne2]

private theorem LZ78.dictIdx_ge_one {A : Type u} [DecidableEq A] (dict : List (List A))
    (w : List A) (hne : w ≠ []) : 1 ≤ LZ78.dictIdx dict w := by
  induction dict with
  | nil =>
    cases w with
    | nil => exact absurd rfl hne
    | cons a as => simp [LZ78.dictIdx_empty a as]
  | cons d ds _ =>
    by_cases heq : w = d
    · subst heq
      simp [LZ78.dictIdx_cons_eq hne rfl]
    · rw [LZ78.dictIdx_cons_ne hne heq]
      omega

private theorem LZ78.dictIdx_le_length {A : Type u} [DecidableEq A] (dict : List (List A))
    (w : List A) (h : w = [] ∨ w ∈ dict) : LZ78.dictIdx dict w ≤ dict.length := by
  induction dict with
  | nil =>
    cases h with
    | inl hnil =>
      subst hnil
      rw [LZ78.dictIdx_nil_eq]
      exact Nat.zero_le _
    | inr hmem => simp at hmem
  | cons d ds ih =>
    cases h with
    | inl hnil =>
      subst hnil
      rw [LZ78.dictIdx_nil_eq]
      simp only [List.length_cons]
      omega
    | inr hmem =>
      by_cases hne : w = []
      · subst hne
        rw [LZ78.dictIdx_nil_eq]
        simp only [List.length_cons]
        omega
      · by_cases heq : w = d
        · subst heq
          rw [LZ78.dictIdx_cons_eq hne rfl]
          simp only [List.length_cons]
          omega
        · rw [LZ78.dictIdx_cons_ne hne heq]
          simp only [List.length_cons]
          have hmem' : w ∈ ds := by simpa [heq] using hmem
          have hle := ih (Or.inr hmem')
          omega

/-- Look up a dictionary index, with the empty phrase at index `0`. -/
def LZ78.dictGet {A : Type u} (dict : List (List A)) (i : ℕ) : Option (List A) :=
  ([] :: dict)[i]?

private theorem LZ78.dictGet_dictIdx {A : Type u} [DecidableEq A] (dict : List (List A))
    (w : List A) (h : w = [] ∨ w ∈ dict) :
    LZ78.dictGet dict (LZ78.dictIdx dict w) = some w := by
  unfold LZ78.dictGet
  induction dict generalizing w with
  | nil =>
    cases h with
    | inl hnil =>
      subst hnil
      simp only [LZ78.dictIdx_nil_eq, List.getElem?_cons_zero]
    | inr hmem => simp at hmem
  | cons d ds ih =>
    cases h with
    | inl hnil =>
      subst hnil
      simp only [LZ78.dictIdx_nil_eq, List.getElem?_cons_zero]
    | inr hmem =>
      by_cases hne : w = []
      · subst hne
        simp only [LZ78.dictIdx_nil_eq, List.getElem?_cons_zero]
      · by_cases heq : w = d
        · subst heq
          simp only [LZ78.dictIdx_cons_eq hne rfl, List.getElem?_cons_zero,
            List.getElem?_cons_succ]
        · have hmem' : w ∈ ds := by simpa [heq] using hmem
          rw [LZ78.dictIdx_cons_ne hne heq]
          have ih' := ih w (Or.inr hmem')
          have hk : 1 ≤ LZ78.dictIdx ds w := LZ78.dictIdx_ge_one ds w hne
          generalize LZ78.dictIdx ds w = m at ih' hk ⊢
          cases m with
          | zero => omega
          | succ k =>
            simp only [List.getElem?_cons_succ] at ih' ⊢
            exact ih'

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

/-- Take the next LZ78 phrase: extend `cur` through the input while it stays known. -/
def LZ78.nextAux {A : Type u} [DecidableEq A] (dict : List (List A)) (cur : List A) :
    List A → List A × LZ78.Token A × List A
  | [] => (cur, (LZ78.dictIdx dict cur, none), [])
  | a :: rest =>
    if cur ++ [a] ∈ dict then LZ78.nextAux dict (cur ++ [a]) rest
    else (cur ++ [a], (LZ78.dictIdx dict cur, some a), rest)

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
    ∃ cur', (cur' = [] ∨ cur' ∈ dict) ∧ t.1 = LZ78.dictIdx dict cur' ∧
      w = LZ78.applySym cur' t.2 := by
  induction x generalizing cur w t rest with
  | nil =>
    simp only [LZ78.nextAux] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨cur, hkn, rfl, rfl⟩
  | cons a r ih =>
    simp only [LZ78.nextAux] at h
    by_cases hmem : cur ++ [a] ∈ dict
    · rw [ite_eq_left hmem] at h
      exact ih _ _ _ _ h (Or.inr hmem)
    · rw [ite_eq_right hmem] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨cur, hkn, rfl, rfl⟩

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

/-- Joint phrase/token recursion over the input with fuel. -/
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
        have hle := LZ78.dictIdx_le_length dict cur' hkn'
        omega
      | succ j =>
        rw [List.getElem_cons_succ]
        have hi' : j < toks'.length := by simp only [List.length_cons] at hi ⊢; omega
        have ih' := ih _ _ _ _ hsub j hi'
        simp only [List.length_append, List.length_cons, List.length_nil] at ih'
        omega

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

/-- Rebuild phrases from tokens, rejecting dangling indices. -/
def LZ78.decodeAux {A : Type u} (dict : List (List A)) :
    List (LZ78.Token A) → Option (List (List A))
  | [] => some []
  | (i, s) :: ts =>
    match LZ78.dictGet dict i with
    | none => none
    | some p =>
      match LZ78.decodeAux (dict ++ [LZ78.applySym p s]) ts with
      | none => none
      | some ws => some (LZ78.applySym p s :: ws)

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
      have hidx' : i0 = LZ78.dictIdx dict cur' := hidx
      have hww' : w0 = LZ78.applySym cur' s0 := hww
      have hget : LZ78.dictGet dict i0 = some cur' := by
        rw [hidx']
        exact LZ78.dictGet_dictIdx dict cur' hkn'
      simp only [LZ78.decodeAux, hget]
      cases s0 with
      | none =>
        rw [LZ78.applySym_none] at hww' ⊢
        subst hww'
        rw [ih _ _ _ _ hsub]
      | some a =>
        rw [LZ78.applySym_some] at hww' ⊢
        subst hww'
        rw [ih _ _ _ _ hsub]

def LZ78.parse {A : Type u} [DecidableEq A] (x : List A) : List (List A) :=
  (LZ78.parseEncodeAux [] x (x.length + 1)).1

def LZ78.encode {A : Type u} [DecidableEq A] (x : List A) : List (LZ78.Token A) :=
  (LZ78.parseEncodeAux [] x (x.length + 1)).2

private theorem LZ78.aux_parse_encode_eq {A : Type u} [DecidableEq A] (x : List A) :
    LZ78.parseEncodeAux [] x (x.length + 1) = (LZ78.parse x, LZ78.encode x) := rfl

def LZ78.decode {A : Type u} (ts : List (LZ78.Token A)) : Option (List A) :=
  (LZ78.decodeAux [] ts).map List.flatten

theorem LZ78.decode_encode {A : Type u} [DecidableEq A] (x : List A) : LZ78.decode (LZ78.encode x) = some x := by
  have hde := LZ78.aux_decode [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
  unfold LZ78.decode
  rw [hde, Option.map_some]
  congr 1
  exact LZ78.aux_flatten [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) (Nat.lt_succ_self _)

def LZ78.encoding {A : Type u} [DecidableEq A] : Computability.Encoding (List A) (LZ78.Token A) where
  encode := LZ78.encode
  decode := LZ78.decode
  decode_encode := LZ78.decode_encode

theorem LZ78.flatten_parse {A : Type u} [DecidableEq A] (x : List A) : (LZ78.parse x).flatten = x := by
  exact LZ78.aux_flatten [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) (Nat.lt_succ_self _)

theorem LZ78.ne_nil_of_mem_parse {A : Type u} [DecidableEq A] {x w : List A} (hw : w ∈ LZ78.parse x) : w ≠ [] := by
  exact LZ78.aux_ne_nil [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) w hw

theorem LZ78.nodup_dropLast_parse {A : Type u} [DecidableEq A] (x : List A) : (LZ78.parse x).dropLast.Nodup := by
  have h := LZ78.aux_nodup_dropLast [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    (Nat.lt_succ_self _) List.nodup_nil LZ78.prefixClosed_nil
  simpa using h

theorem LZ78.prefix_mem_parse {A : Type u} [DecidableEq A] (x : List A) (i : ℕ) (hi : i < (LZ78.parse x).length) {v : List A} (hv : v <+: (LZ78.parse x)[i]) (hne : v ≠ (LZ78.parse x)[i]) : v = [] ∨ v ∈ (LZ78.parse x).take i := by
  have h := LZ78.aux_prefix_mem [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
    LZ78.prefixClosed_nil i hi v hv hne
  simpa using h

theorem LZ78.encoding_encode_length {A : Type u} [DecidableEq A] (x : List A) : ((LZ78.encoding (A := A)).encode x).length = (LZ78.parse x).length := by
  have h := LZ78.aux_length [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x)
  simpa [LZ78.encoding] using h

theorem LZ78.fst_encode_le {A : Type u} [DecidableEq A] (x : List A) (i : ℕ) (hi : i < (LZ78.encode x).length) : ((LZ78.encode x)[i]).1 ≤ i := by
  have h := LZ78.aux_fst_le [] x (x.length + 1) _ _ (LZ78.aux_parse_encode_eq x) i hi
  simpa using h

end Cslib.Algorithms.Lean
