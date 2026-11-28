/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup

/-!
# Baby-step giant-step discrete logarithm in the generic group model

A concrete discrete-logarithm algorithm over `OracleComp (Query (Label q)) (Label q)`:
given the identity label, a generator label, and a target label, `bsgs` returns the
discrete logarithm of the target, making at most `2 * bsgsM q` oracle queries. This is
the standard textbook baby-step giant-step algorithm, run against the fixed-encoding
oracle `oracleOf`.

Scope: this file exhibits one concrete `OracleComp` algorithm. It does not claim that
arbitrary `OracleComp` programs are generic programs — that is the separate deeply
embedded `GProg` result of `CSLibExt.Crypto.Framework.GenericGroup`, whose compiler,
query bound, and relabeling invariance (`eval_natural`) live there. No collision bounds
in the style of Shoup are claimed here.
-/

@[expose] public section

namespace CSLibExt.Crypto.Framework.GenericGroup

open Cslib.Crypto.Framework.GenericGroup
open Cslib.Crypto.Framework

/-- Giant-step count: `⌈√q⌉` realized as `√(q - 1) + 1`. -/
def bsgsM (q : Nat) : Nat := Nat.sqrt (q - 1) + 1

theorem bsgsM_pos (q : Nat) : 0 < bsgsM q := Nat.succ_pos _

/-- `bsgsM q` covers all of `ZMod q`: every `x.val < q` is `i * m + j` with `i, j < m`. -/
theorem bsgsM_sq {q : Nat} (h : 1 < q) : q ≤ (bsgsM q) ^ 2 := by
  unfold bsgsM
  have hlt := Nat.lt_succ_sqrt (q - 1)
  rw [pow_two]
  rw [Nat.succ_eq_add_one] at hlt
  omega

/-- Reference baby table: encodings of exponents `c, …, c + f - 1`. -/
def babySpec {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (c f : Nat) :
    List (Label q) :=
  match f with
  | 0 => []
  | f + 1 => enc (c : ZMod q) :: babySpec enc (c + 1) f

theorem babySpec_zero {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (c : Nat) :
    babySpec enc c 0 = [] := rfl

theorem babySpec_succ {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (c f : Nat) :
    babySpec enc c (f + 1) = enc (c : ZMod q) :: babySpec enc (c + 1) f := rfl

theorem babySpec_length {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (c f : Nat) :
    (babySpec enc c f).length = f := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih => simp only [babySpec_succ, List.length_cons, ih]

theorem babySpec_get {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (c f j : Nat)
    (hj : j < f) :
    (babySpec enc c f)[j]? = some (enc (((c + j : Nat)) : ZMod q)) := by
  induction f generalizing c j with
  | zero => omega
  | succ f ih =>
    cases j with
    | zero =>
      simp only [babySpec_succ]
      show some (enc (c : ZMod q)) = _
      rw [Nat.add_zero]
    | succ j =>
      have hj' : j < f := by omega
      simp only [babySpec_succ]
      show (babySpec enc (c + 1) f)[j]? = _
      rw [show c + (j + 1) = c + 1 + j from by omega]
      exact ih _ _ hj'

/-- Baby steps: accumulate the labels of exponents `0, …, m - 1` plus `enc m`,
using one multiplication query per fuel unit. -/
def babiesAux {q : Nat} [Fact (1 < q)] (f : Nat) (cur g : Label q) (acc : List (Label q)) :
    OracleComp (Query (Label q)) (Label q) (List (Label q) × Label q) :=
  match f with
  | 0 => .pure (acc.reverse, cur)
  | f + 1 => OracleComp.query (.inl (cur, g)) fun nxt => babiesAux f nxt g (cur :: acc)

theorem babiesAux_zero {q : Nat} [Fact (1 < q)] (cur g : Label q) (acc : List (Label q)) :
    babiesAux 0 cur g acc = .pure (acc.reverse, cur) := rfl

theorem babiesAux_succ {q : Nat} [Fact (1 < q)] (f : Nat) (cur g : Label q)
    (acc : List (Label q)) :
    babiesAux (f + 1) cur g acc
      = OracleComp.query (.inl (cur, g)) fun nxt => babiesAux f nxt g (cur :: acc) := rfl

theorem run_babiesAux {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (f c : Nat)
    (cur g : Label q) (acc : List (Label q))
    (hcur : cur = enc (c : ZMod q)) (hg : g = enc 1) :
    OracleComp.run (oracleOf enc) (babiesAux f cur g acc)
      = (acc.reverse ++ babySpec enc c f, enc (((c + f : Nat)) : ZMod q)) := by
  induction f generalizing cur c acc with
  | zero =>
    simp only [babiesAux_zero, babySpec_zero, List.append_nil]
    show (acc.reverse, cur) = _
    rw [hcur, Nat.add_zero]
  | succ f ih =>
    simp only [babiesAux_succ]
    have hnxt : oracleOf enc (.inl (cur, g)) = enc (((c + 1 : Nat)) : ZMod q) := by
      have e : (c : ZMod q) + 1 = (((c + 1 : Nat)) : ZMod q) := by
        simp only [Nat.cast_add, Nat.cast_one]
      simp only [oracleOf_inl, hcur, hg, Equiv.symm_apply_apply, e]
    show OracleComp.run (oracleOf enc)
      (babiesAux f (oracleOf enc (.inl (cur, g))) g (cur :: acc)) = _
    rw [hnxt, ih _ _ _ rfl, babySpec_succ, List.reverse_cons, hcur]
    congr 1
    · simp
    · have h : c + 1 + f = c + (f + 1) := by omega
      rw [h]

/-- Table lookup: first index `≥ k` where `cur` occurs, by label equality. -/
def findIdx {q : Nat} [Fact (1 < q)] (cur : Label q) : List (Label q) → Nat → Option Nat
  | [], _ => none
  | t :: ts, k => if cur = t then some k else findIdx cur ts (k + 1)

theorem findIdx_nil {q : Nat} [Fact (1 < q)] (cur : Label q) (k : Nat) :
    findIdx cur ([] : List (Label q)) k = none := rfl

theorem findIdx_cons {q : Nat} [Fact (1 < q)] (cur t : Label q) (ts : List (Label q))
    (k : Nat) :
    findIdx cur (t :: ts) k = (if cur = t then some k else findIdx cur ts (k + 1)) := rfl

theorem findIdx_some {q : Nat} [Fact (1 < q)] (cur : Label q) (tab : List (Label q))
    (k j : Nat) (h : findIdx cur tab k = some j) :
    k ≤ j ∧ j < k + tab.length ∧ tab[j - k]? = some cur := by
  induction tab generalizing k j with
  | nil =>
    simp only [findIdx_nil] at h
    cases h
  | cons t ts ih =>
    rw [findIdx_cons] at h
    by_cases hct : cur = t
    · rw [ite_eq_left hct] at h
      cases h
      refine ⟨le_rfl, by simp only [List.length_cons]; omega, ?_⟩
      rw [Nat.sub_self]
      show some t = _
      rw [← hct]
    · rw [ite_eq_right hct] at h
      obtain ⟨hle, hlt, hget⟩ := ih _ _ h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
      have hdecomp : j - k = (j - (k + 1)) + 1 := by omega
      rw [hdecomp]
      show ts[j - (k + 1)]? = some cur
      exact hget

theorem findIdx_none {q : Nat} [Fact (1 < q)] (cur : Label q) (tab : List (Label q))
    (k : Nat) (h : findIdx cur tab k = none) (j : Nat) : tab[j]? ≠ some cur := by
  induction tab generalizing k j with
  | nil =>
    intro hcon
    simp at hcon
  | cons t ts ih =>
    by_cases hct : cur = t
    · rw [findIdx_cons, ite_eq_left hct] at h
      cases h
    · rw [findIdx_cons, ite_eq_right hct] at h
      cases j with
      | zero =>
        intro hcon
        have hte : t = cur := by simpa using hcon
        exact hct hte.symm
      | succ j =>
        show ts[j]? ≠ some cur
        exact ih _ h j

/-- Giant steps: check the baby table at each `i` before stepping, returning
`i * m + j` on a match and `none` after `i = m - 1`. -/
def giantsAux {q : Nat} [Fact (1 < q)] (fuel i m : Nat) (cur : Label q)
    (tab : List (Label q)) (gfactor : Label q) :
    OracleComp (Query (Label q)) (Label q) (Option (ZMod q)) :=
  match fuel with
  | 0 => .pure none
  | fuel + 1 =>
    match findIdx cur tab 0 with
    | some j => .pure (some (((i * m + j : Nat)) : ZMod q))
    | none =>
      if i + 1 = m then .pure none
      else OracleComp.query (.inl (cur, gfactor)) fun nxt =>
        giantsAux fuel (i + 1) m nxt tab gfactor

theorem giantsAux_zero {q : Nat} [Fact (1 < q)] (i m : Nat) (cur : Label q)
    (tab : List (Label q)) (gfactor : Label q) :
    giantsAux 0 i m cur tab gfactor = .pure none := rfl

theorem giantsAux_succ {q : Nat} [Fact (1 < q)] (fuel i m : Nat) (cur : Label q)
    (tab : List (Label q)) (gfactor : Label q) :
    giantsAux (fuel + 1) i m cur tab gfactor
      = (match findIdx cur tab 0 with
        | some j => .pure (some (((i * m + j : Nat)) : ZMod q))
        | none =>
          if i + 1 = m then .pure none
          else OracleComp.query (.inl (cur, gfactor)) fun nxt =>
            giantsAux fuel (i + 1) m nxt tab gfactor) := rfl

/-- With `s + 1` checks left and the last check at `i = m - 1`, at most `s` steps remain. -/
theorem isQueryBounded_giantsAux {q : Nat} [Fact (1 < q)] (s i m : Nat) (cur : Label q)
    (tab : List (Label q)) (gfactor : Label q) (hi : i + s + 1 = m) :
    FreeM.IsQueryBounded s (giantsAux (s + 1) i m cur tab gfactor) := by
  induction s generalizing i cur with
  | zero =>
    simp only [giantsAux_succ]
    by_cases hfind : ∃ j, findIdx cur tab 0 = some j
    · obtain ⟨j, hfind⟩ := hfind
      simp only [hfind]
      show FreeM.IsQueryBounded 0 (.pure _)
      exact FreeM.isQueryBounded_pure _ _
    · have hnone : findIdx cur tab 0 = none := by
        cases h : findIdx cur tab 0
        · rfl
        · exact (hfind ⟨_, h⟩).elim
      simp only [hnone]
      show FreeM.IsQueryBounded 0 (if i + 1 = m then .pure none else _)
      by_cases hi' : i + 1 = m
      · rw [ite_eq_left hi']
        exact FreeM.isQueryBounded_pure _ _
      · rw [ite_eq_right hi']
        exact False.elim (by omega)
  | succ s ih =>
    simp only [giantsAux_succ]
    by_cases hfind : ∃ j, findIdx cur tab 0 = some j
    · obtain ⟨j, hfind⟩ := hfind
      simp only [hfind]
      show FreeM.IsQueryBounded (s + 1) (.pure _)
      exact FreeM.IsQueryBounded.mono (Nat.zero_le _) (FreeM.isQueryBounded_pure _ _)
    · have hnone : findIdx cur tab 0 = none := by
        cases h : findIdx cur tab 0
        · rfl
        · exact (hfind ⟨_, h⟩).elim
      simp only [hnone]
      show FreeM.IsQueryBounded (s + 1) (if i + 1 = m then .pure none else _)
      by_cases hi' : i + 1 = m
      · rw [ite_eq_left hi']
        exact FreeM.IsQueryBounded.mono (Nat.zero_le _) (FreeM.isQueryBounded_pure _ _)
      · rw [ite_eq_right hi']
        exact FreeM.isQueryBounded_liftBind fun b => ih _ _ (by omega)

/-- Baby steps use exactly the fuel as queries, leaving budget `t` for the continuation. -/
theorem isQueryBoundedWith_babiesAux {q : Nat} [Fact (1 < q)] (f t : Nat) (cur g : Label q)
    (acc : List (Label q))
    (G : List (Label q) × Label q → OracleComp (Query (Label q)) (Label q) (Option (ZMod q)))
    (hG : ∀ p, FreeM.IsQueryBounded t (G p)) :
    FreeM.IsQueryBoundedWith (fun p j => FreeM.IsQueryBounded j (G p)) (t + f)
      (babiesAux f cur g acc) := by
  induction f generalizing cur acc with
  | zero =>
    simp only [babiesAux_zero]
    exact hG _
  | succ f ih =>
    simp only [babiesAux_succ]
    exact fun b => ih _ _

/-- Baby-step giant-step discrete logarithm: baby table, one inversion for the giant
factor, then giant steps with check-then-step. -/
def bsgs {q : Nat} [Fact (1 < q)] (e g h : Label q) :
    OracleComp (Query (Label q)) (Label q) (Option (ZMod q)) :=
  PFunctor.FreeM.bind (babiesAux (bsgsM q) e g [])
    fun p => OracleComp.query (.inr p.2) fun gfactor =>
      giantsAux (bsgsM q) 0 (bsgsM q) h p.1 gfactor

theorem bsgs_eq {q : Nat} [Fact (1 < q)] (e g h : Label q) :
    bsgs e g h
      = PFunctor.FreeM.bind (babiesAux (bsgsM q) e g [])
        fun p => OracleComp.query (.inr p.2) fun gfactor =>
          giantsAux (bsgsM q) 0 (bsgsM q) h p.1 gfactor := rfl

/-- Every exponent splits as `x.val = (x.val / m) * m + x.val % m` with both parts
below `m`, and the giant value at `x.val / m` is the baby value at `x.val % m`. -/
theorem bsgs_decomp {q m : Nat} (x : ZMod q) (h1q : 1 < q) (hm : 0 < m)
    (hq : q ≤ m ^ 2) :
    x.val / m < m ∧ x.val % m < m ∧
      x - (x.val / m : ZMod q) * (m : ZMod q) = (((x.val % m : Nat)) : ZMod q) := by
  have hNe : NeZero q := ⟨by omega⟩
  have hval : x.val < q := ZMod.val_lt x
  have hmod : x.val % m < m := Nat.mod_lt _ hm
  have hspec : x.val / m * m + x.val % m = x.val := by
    have h := Nat.div_add_mod x.val m
    rwa [mul_comm m (x.val / m)] at h
  have hlt : x.val / m * m < m * m := by
    have hq' : q ≤ m * m := by
      rw [pow_two] at hq
      exact hq
    omega
  have hdiv : x.val / m < m := Nat.lt_of_mul_lt_mul_right hlt
  refine ⟨hdiv, hmod, ?_⟩
  have hcast : x = ((x.val : Nat) : ZMod q) := (ZMod.natCast_zmod_val x).symm
  have h3 : ((x.val : Nat) : ZMod q)
      = (((x.val / m * m + x.val % m : Nat)) : ZMod q) := by
    rw [hspec]
  conv_lhs =>
    lhs
    rw [hcast]
  rw [← Nat.cast_mul, h3, Nat.cast_add, add_sub_cancel_left]

/-- Giant steps find `x`: a match at `(i, j)` is sound by injectivity of `enc`, and
the target giant index `x.val / m` always matches, so the run returns `some x`. -/
theorem run_giantsAux {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (x : ZMod q)
    (fuel i m : Nat) (cur : Label q) (tab : List (Label q)) (gfactor : Label q)
    (hm : 0 < m)
    (hcur : cur = enc (x - (i : ZMod q) * (m : ZMod q)))
    (hgf : gfactor = enc (-(m : ZMod q)))
    (htab : ∀ j, j < m → tab[j]? = some (enc ((j : Nat) : ZMod q)))
    (hlen : tab.length = m)
    (hi : i + fuel = m) (hle : i ≤ x.val / m)
    (h1q : 1 < q) (hq : q ≤ m ^ 2) :
    OracleComp.run (oracleOf enc) (giantsAux fuel i m cur tab gfactor) = some x := by
  obtain ⟨hdiv, hmod, hdecomp⟩ := bsgs_decomp x h1q hm hq
  induction fuel generalizing i cur with
  | zero =>
    have : False := by omega
    exact this.elim
  | succ fuel ih =>
    simp only [giantsAux_succ]
    by_cases hfind : ∃ j, findIdx cur tab 0 = some j
    · obtain ⟨j, hfind⟩ := hfind
      simp only [hfind]
      obtain ⟨-, hlt, hget⟩ := findIdx_some cur tab 0 j hfind
      rw [Nat.sub_zero] at hget
      rw [hlen] at hlt
      have hjm : j < m := by omega
      have htabj := htab j hjm
      rw [hget] at htabj
      have hcurj : cur = enc ((j : Nat) : ZMod q) := by simpa using htabj
      have hinj : ((j : Nat) : ZMod q) = x - (i : ZMod q) * (m : ZMod q) :=
        enc.injective (hcurj.symm.trans hcur)
      have hx : (((i * m + j : Nat)) : ZMod q) = x := by
        have h1 : (((i * m + j : Nat)) : ZMod q)
            = (i : ZMod q) * (m : ZMod q) + (j : ZMod q) := by
          simp only [Nat.cast_add, Nat.cast_mul]
        rw [h1]
        linear_combination hinj
      show (some (((i * m + j : Nat)) : ZMod q)) = some x
      exact congrArg some hx
    · have hnone : findIdx cur tab 0 = none := by
        cases h : findIdx cur tab 0
        · rfl
        · exact (hfind ⟨_, h⟩).elim
      simp only [hnone]
      have hnotarget : i ≠ x.val / m := by
        intro heq
        rw [heq] at hcur
        rw [hdecomp] at hcur
        have htab0 := htab (x.val % m) hmod
        have hne := findIdx_none cur tab 0 hnone (x.val % m)
        rw [hcur] at hne
        exact hne htab0
      show OracleComp.run (oracleOf enc) (if i + 1 = m then .pure none else _) = some x
      by_cases hi' : i + 1 = m
      · rw [ite_eq_left hi']
        have hi0 : i = x.val / m := by omega
        exact (hnotarget hi0).elim
      · rw [ite_eq_right hi']
        have hstep : (x - (i : ZMod q) * (m : ZMod q)) + (-(m : ZMod q))
            = x - ((i + 1 : Nat) : ZMod q) * (m : ZMod q) := by
          push_cast
          ring
        have hcur' : oracleOf enc (.inl (cur, gfactor))
            = enc (x - ((i + 1 : Nat) : ZMod q) * (m : ZMod q)) := by
          simp only [oracleOf_inl, hcur, hgf, Equiv.symm_apply_apply, hstep]
        show OracleComp.run (oracleOf enc)
          (giantsAux fuel (i + 1) m (oracleOf enc (.inl (cur, gfactor))) tab gfactor)
          = some x
        exact ih _ _ hcur' (by omega) (by omega)

/-- `bsgs` returns the discrete logarithm, for every encoding and every target. -/
theorem bsgs_correct {q : Nat} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (x : ZMod q) :
    OracleComp.run (oracleOf enc) (bsgs (enc 0) (enc 1) (enc x)) = some x := by
  have h1q : 1 < q := Fact.out
  have hmsq : q ≤ (bsgsM q) ^ 2 := bsgsM_sq h1q
  have hm : 0 < bsgsM q := bsgsM_pos q
  have hcur0 : enc 0 = enc (((0 : Nat)) : ZMod q) := by simp
  have hbab := run_babiesAux enc (bsgsM q) 0 (enc 0) (enc 1) [] hcur0 rfl
  simp only [bsgs_eq]
  rw [OracleComp.run_bind, hbab]
  simp only [List.reverse_nil, List.nil_append, Nat.zero_add]
  show OracleComp.run (oracleOf enc)
      (giantsAux (bsgsM q) 0 (bsgsM q) (enc x) (babySpec enc 0 (bsgsM q))
        (oracleOf enc (.inr (enc (((bsgsM q : Nat)) : ZMod q))))) = some x
  refine run_giantsAux _ _ _ _ _ _ _ _ hm ?_ ?_ ?_ ?_ ?_ ?_ h1q hmsq
  · simp only [Nat.cast_zero, zero_mul, sub_zero]
  · show enc (-enc.symm (enc (((bsgsM q : Nat)) : ZMod q))) = _
    rw [Equiv.symm_apply_apply]
  · intro j hj
    have h := babySpec_get enc 0 (bsgsM q) j hj
    rwa [Nat.zero_add] at h
  · exact babySpec_length enc 0 (bsgsM q)
  · exact Nat.zero_add _
  · exact Nat.zero_le _

/-- `bsgs` makes at most `2 * bsgsM q` queries along every path. -/
theorem bsgs_isQueryBounded {q : Nat} [Fact (1 < q)] (e g h : Label q) :
    FreeM.IsQueryBounded (2 * bsgsM q) (bsgs e g h) := by
  have hm : 0 < bsgsM q := bsgsM_pos q
  have hms : (bsgsM q - 1) + 1 = bsgsM q := by omega
  have hG : ∀ p : List (Label q) × Label q,
      FreeM.IsQueryBounded (bsgsM q)
        ((fun p => OracleComp.query (.inr p.2) fun gfactor =>
          giantsAux (bsgsM q) 0 (bsgsM q) h p.1 gfactor) p) := by
    intro p
    show FreeM.IsQueryBounded (bsgsM q)
      (OracleComp.query (.inr p.2) fun gfactor =>
        giantsAux (bsgsM q) 0 (bsgsM q) h p.1 gfactor)
    refine FreeM.isQueryBounded_liftBind fun gfactor => ?_
    have hgi := isQueryBounded_giantsAux (bsgsM q - 1) 0 (bsgsM q) h p.1 gfactor (by omega)
    rw [hms] at hgi
    exact hgi
  have hbind : FreeM.IsQueryBounded (bsgsM q + bsgsM q)
      (PFunctor.FreeM.bind (babiesAux (bsgsM q) e g [])
        (fun p => OracleComp.query (.inr p.2) fun gfactor =>
          giantsAux (bsgsM q) 0 (bsgsM q) h p.1 gfactor)) :=
    FreeM.isQueryBounded_bind
      (isQueryBoundedWith_babiesAux (bsgsM q) (bsgsM q) e g [] _ hG)
  simp only [bsgs_eq]
  exact FreeM.IsQueryBounded.mono (by omega) hbind

/-- The query transcript of a `bsgs` run has length at most `2 * bsgsM q`. -/
theorem bsgs_length_queries_le {q : Nat} [Fact (1 < q)] (e g h : Label q)
    (O : Query (Label q) → Label q) :
    (OracleComp.queries O (bsgs e g h)).length ≤ 2 * bsgsM q :=
  OracleComp.length_queries_le O (bsgs_isQueryBounded e g h)

end CSLibExt.Crypto.Framework.GenericGroup
