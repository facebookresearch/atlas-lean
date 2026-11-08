/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathCheck
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# The NP verifier for HAMPATH: the machine

`prog` is a `TM2` component on thirteen stacks over the alphabet `Sym` (bits as `Sym.bit`) that
decides `hamCheck x w` (`CSLibExt.Computability.Complexity.Karp.HamPathCheck`) with `x` on `X`
and `w` on `W`.

* Parse: read `s`, `t`, `n` in unary off `X` onto the counters `S`, `T`, `N` (`readU`); check
  that the rest of `X` is an edge list by moving it to `E` one unary number at a time (`skipU`,
  `valE_run`) and put it back (`moveB`); check that `w` is a list of unary numbers the same way
  (`valW_run`), through `Z`.
* Walk the vertices (`loop_run`): read the next vertex `a` onto `A`; compare it with `n`
  (`cmp_run`); if no vertex was seen yet (`C` empty) compare it with `s`, otherwise scan the
  edge list for the pair `(b, a)`, `b` the previous vertex on `B` (`scan_run`: each edge's ends
  are compared with `B` and `A` while its bits move to `E`, `cmpN_run`); compare `a` with every
  later vertex (`nd_run`, through `Z`); count `a` on `C` and make it the previous vertex. With
  no vertex left, `C` must equal `n` and be nonzero, and `B` must equal `t`.
* `run`: from `start`, `prog` reaches `yes` iff `hamCheck x w` and `no` otherwise, within
  `100 (|x| + |w| + 1)⁴` steps (quadratically many, in fact). The machine's order of checks is
  `walkOk`, which `walkOk_eq` identifies with the check.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.HamVerify

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)

/-! ### The machine -/

/-- Stacks: the input `X` and the witness `W`; the counters `S`, `T`, `N` (for `s`, `t`, `n`),
`C` (vertices seen), `A` (the current vertex) and `B` (the previous one); the save stacks `E`
(for `X`) and `Z` (for `W`); the scratch stacks `R` and `Q`. -/
inductive K | X | W | S | T | N | C | A | B | E | Z | R | Q
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .S, .T, .N, .C, .A, .B, .E, .Z, .R, .Q], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The four counter comparisons: `a` with `n`, `a` with `s`, `c` with `n`, `b` with `t`. -/
inductive CI | an | as | cn | bt
  deriving DecidableEq

/-- `CI` is finite. -/
instance CI.instFintypeEnumFix : Fintype CI where
  elems := ⟨↑[CI.an, .as, .cn, .bt], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Labels: read `s`, `t`, `n`; validate the edge list and put it back; validate the witness and
put it back; the vertex loop, reading a vertex, and the head-or-edge dispatch; the counter
comparisons (`cmp`, and the two restoring loops `cr`, `crb` of each outcome); the edge scan
(comparing an edge's ends, restoring the counters, putting the edge list back); the repeat scan;
the final nonzero-count check; counting the vertex and making it the previous one; accept;
reject. -/
inductive Lab
  | rdS | rdT | rdN | vE | vEU | vEV | vEb | vW | vWU | vWb | loop | rdA | hd
  | cmp (i : CI) | cr (i : CI) (o : Ordering) | crb (i : CI) (o : Ordering)
  | scan | ceU (ok : Bool) | rsU (ok : Bool) | ceV (ok : Bool) | rsV (ok : Bool) | scB
  | nd | cbN (ok : Bool) | rsN (ok : Bool) | ndB | fin | incC | dB | mA | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdS, .rdT, .rdN, .vE, .vEU, .vEV, .vEb, .vW, .vWU, .vWb, .loop, .rdA, .hd,
    .cmp .an, .cmp .as, .cmp .cn, .cmp .bt,
    .cr .an .lt, .cr .an .eq, .cr .an .gt, .cr .as .lt, .cr .as .eq, .cr .as .gt,
    .cr .cn .lt, .cr .cn .eq, .cr .cn .gt, .cr .bt .lt, .cr .bt .eq, .cr .bt .gt,
    .crb .an .lt, .crb .an .eq, .crb .an .gt, .crb .as .lt, .crb .as .eq, .crb .as .gt,
    .crb .cn .lt, .crb .cn .eq, .crb .cn .gt, .crb .bt .lt, .crb .bt .eq, .crb .bt .gt,
    .scan, .ceU false, .ceU true, .rsU false, .rsU true, .ceV false, .ceV true,
    .rsV false, .rsV true, .scB, .nd, .cbN false, .cbN true, .rsN false, .rsN true, .ndB,
    .fin, .incC, .dB, .mA, .yes, .no], by decide⟩
  complete := by
    rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _⟩ |
      ⟨_ | _ | _ | _, _ | _ | _⟩ | ⟨_ | _ | _ | _, _ | _ | _⟩ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ |
      ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _) <;> decide

/-- Statements of the verifier. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- Read a unary number off `src` onto the counter `c`: a `true` adds a unit, the `false`
terminator moves on to `next`, an exhausted `src` rejects. -/
def readU (src c : K) (self next : Lab) : Stmt :=
  .peek src (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop src (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- Move a unary number, terminator included, from `src` to `dst`; an exhausted `src`
rejects. -/
def skipU (src dst : K) (self next : Lab) : Stmt :=
  .peek src (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop src (fun _ o => bitOf Sym.bit? o) <| .push dst (fun b => .bit b) <| .branch id
      (.goto fun _ => self) (.goto fun _ => next)

/-- Go to `e` if stack `k` is empty and to `ne` otherwise. -/
def ifE (k : K) (e ne : Lab) : Stmt :=
  .peek k (fun _ o => o.isNone) <| .branch id (.goto fun _ => e) (.goto fun _ => ne)

/-- Compare the next unary number of `src` (its bits move to `sv`) with the counter `c`, one
unit of `c` per `true`, parked on `R`; `ok` is the verdict so far, falsified when `c` runs out
early. At the terminator the verdict is `ok` if `c` is exhausted and `false` otherwise. -/
def cbS (src sv c : K) (self fin : Bool → Lab) (ok : Bool) : Stmt :=
  .pop src (fun _ o => bitOf Sym.bit? o) <| .push sv (fun b => .bit b) <| .branch id
    (.pop c (fun _ o => o.isSome) <| .branch id
      (.push .R (fun _ => .bit true) (.goto fun _ => self ok)) (.goto fun _ => self false))
    (.peek c (fun _ o => o.isNone) <| .branch id (.goto fun _ => fin ok)
      (.goto fun _ => fin false))

/-- The first counter of each comparison. -/
def ca : CI → K
  | .an => .A
  | .as => .A
  | .cn => .C
  | .bt => .B

/-- The second counter of each comparison. -/
def cb : CI → K
  | .an => .N
  | .as => .S
  | .cn => .N
  | .bt => .T

/-- Where each comparison goes: on `a < n`, `a = s`, `c = n`, `b = t` respectively to the
dispatch, the repeat scan, the nonzero-count check and `yes`; otherwise to `no`. -/
def cout : CI → Ordering → Lab
  | .an, .lt => .hd
  | .as, .eq => .nd
  | .cn, .eq => .fin
  | .bt, .eq => .yes
  | _, _ => .no

/-- The verifier: parse and validate, then walk the vertices. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .rdS => readU .X .S .rdS .rdT
  | .rdT => readU .X .T .rdT .rdN
  | .rdN => readU .X .N .rdN .vE
  | .vE => ifE .X .vEb .vEU
  | .vEU => skipU .X .E .vEU .vEV
  | .vEV => skipU .X .E .vEV .vE
  | .vEb => moveB .E .X Sym.bit? Sym.bit .vEb .vW
  | .vW => ifE .W .vWb .vWU
  | .vWU => skipU .W .Z .vWU .vW
  | .vWb => moveB .Z .W Sym.bit? Sym.bit .vWb .loop
  | .loop => ifE .W (.cmp .cn) .rdA
  | .rdA => readU .W .A .rdA (.cmp .an)
  | .hd => ifE .C (.cmp .as) .scan
  | .cmp i => cmpStep (ca i) (cb i) .R .Q (Sym.bit true) (Sym.bit true) (.cmp i) (.cr i .lt)
      (.cr i .eq) (.cr i .gt)
  | .cr i o => xfer .R [⟨ca i, Sym.bit true⟩] (.cr i o) (.crb i o)
  | .crb i o => xfer .Q [⟨cb i, Sym.bit true⟩] (.crb i o) (cout i o)
  | .scan => ifE .X .no (.ceU true)
  | .ceU ok => cbS .X .E .B .ceU .rsU ok
  | .rsU ok => xfer .R [⟨.B, Sym.bit true⟩] (.rsU ok) (.ceV ok)
  | .ceV ok => cbS .X .E .A .ceV .rsV ok
  | .rsV ok => xfer .R [⟨.A, Sym.bit true⟩] (.rsV ok) (if ok then .scB else .scan)
  | .scB => moveB .E .X Sym.bit? Sym.bit .scB .nd
  | .nd => ifE .W .ndB (.cbN true)
  | .cbN ok => cbS .W .Z .A .cbN .rsN ok
  | .rsN ok => xfer .R [⟨.A, Sym.bit true⟩] (.rsN ok) (if ok then .no else .nd)
  | .ndB => moveB .Z .W Sym.bit? Sym.bit .ndB .incC
  | .fin => ifE .C .no (.cmp .bt)
  | .incC => incr .C (Sym.bit true) .dB
  | .dB => xfer .B [] .dB .mA
  | .mA => xfer .A [⟨.B, Sym.bit true⟩] .mA .loop
  | .yes => .halt
  | .no => .halt

/-- The start label. -/
def start : Lab := .rdS

/-! ### Generic phases -/

/-- Two updates of `a` interleaved with two of `b` leave the last of each. -/
theorem update_update_update_update {a b : K} (hab : a ≠ b) (S : ∀ _ : K, List Sym)
    (p p' t t' : List Sym) :
    update (update (update (update S a p) b t) a p') b t' = update (update S a p') b t' := by
  rw [update_comm hab.symm, update_idem, update_idem]

/-- A step whose label and stacks are known. -/
theorem step1 {l l' : Lab} {v : Bool} {S S' : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some l') (h' : (TM2.stepAux (prog l) v S).stk = S') :
    ∃ v', Run prog 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, Run.single (d := ⟨some l', (TM2.stepAux (prog l) v S).var, S'⟩) (by rw [← h, ← h'])⟩

/-- `ifE` peeks at its stack. -/
theorem ifE_run {l e ne : Lab} {k : K} (hp : prog l = ifE k e ne) (v : Bool)
    (St : ∀ _ : K, List Sym) :
    ∃ v', Run prog 1 ⟨some l, v, St⟩ ⟨some (if St k = [] then e else ne), v', St⟩ :=
  step1 (by cases h : St k <;> simp [hp, ifE, TM2.stepAux, h])
    (by cases h : St k <;> simp [hp, ifE, TM2.stepAux, h])

/-- `readU` on `k` in unary: `k + 1` steps to `next`, with `k` more units on the counter and
the rest of `src` left. -/
theorem readU_run {src c : K} {self next : Lab} (hp : prog self = readU src c self next)
    (hc : c ≠ src) : ∀ (k j : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate k true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) j →
      ∃ v', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v',
        update (update St src (r.map Sym.bit)) c (cnt (Sym.bit true) (k + j))⟩ := by
  intro k
  induction k with
  | zero =>
      intro j r v St hX hC
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      have e : update (update St src (r.map Sym.bit)) c (cnt (Sym.bit true) (0 + j)) =
          update St src (r.map Sym.bit) := by
        rw [zero_add, ← hC, ← update_of_ne hc (r.map Sym.bit) St, update_eq_self]
      rw [e]
      exact step1 (by simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?])
        (by simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?])
  | succ k ih =>
      intro j r v St hX hC
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      obtain ⟨v', hrun⟩ := ih (j + 1) r true
        (update (update St src ((List.replicate k true ++ false :: r).map Sym.bit)) c
          (Sym.bit true :: St c)) (by simp [update_of_ne hc.symm]) (by simp [hC, cnt_succ])
      rw [update_update_update_update hc.symm, show k + (j + 1) = k + 1 + j by omega] at hrun
      exact ⟨v', Run.head (by simp [TM2.step, hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?,
        update_of_ne hc]) hrun⟩

/-- `readU` on an unterminated unary prefix rejects. -/
theorem readU_none {src c : K} {self next : Lab} (hp : prog self = readU src c self next)
    (hc : c ≠ src) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St src = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', h⟩ := step1 (l := self) (v := v) (S := St) (l' := .no) (S' := St)
        (by simp [hp, readU, TM2.stepAux, hX]) (by simp [hp, readU, TM2.stepAux, hX])
      exact ⟨v', St, h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St src (l.map Sym.bit)) c (Sym.bit true :: St c)) hl'
            (by simp [update_of_ne hc.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hc]

/-- A unary block, reversed, after one more unit. -/
theorem blk_succ (a : ℕ) (L : List Sym) :
    (List.replicate a true ++ [false]).reverse.map Sym.bit ++ Sym.bit true :: L =
      (List.replicate (a + 1) true ++ [false]).reverse.map Sym.bit ++ L := by
  have e : ∀ (n : ℕ) (x : Sym) (L : List Sym),
      List.replicate n x ++ x :: L = x :: (List.replicate n x ++ L) := by
    intro n x L
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  simp [e, List.replicate_succ]

/-- `skipU` on `k` in unary: `k + 1` steps to `next`, the number (with its terminator) moved to
`dst`, reversed. -/
theorem skipU_run {src dst : K} {self next : Lab} (hp : prog self = skipU src dst self next)
    (hd : dst ≠ src) : ∀ (k : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate k true ++ false :: r).map Sym.bit →
      ∃ v', Run prog (k + 1) ⟨some self, v, St⟩ ⟨some next, v',
        update (update St src (r.map Sym.bit)) dst
          ((List.replicate k true ++ [false]).reverse.map Sym.bit ++ St dst)⟩ := by
  intro k
  induction k with
  | zero =>
      intro r v St hX
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      exact step1 (by simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?])
        (by simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hd])
  | succ k ih =>
      intro r v St hX
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      obtain ⟨v', hrun⟩ := ih r true
        (update (update St src ((List.replicate k true ++ false :: r).map Sym.bit)) dst
          (Sym.bit true :: St dst)) (by simp [update_of_ne hd.symm])
      rw [update_update_update_update hd.symm, update_self, blk_succ] at hrun
      exact ⟨v', Run.head (by simp [TM2.step, hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?,
        update_of_ne hd]) hrun⟩

/-- `skipU` on an unterminated unary prefix rejects. -/
theorem skipU_none {src dst : K} {self next : Lab} (hp : prog self = skipU src dst self next)
    (hd : dst ≠ src) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St src = l.map Sym.bit →
      ∃ v' S', RunLe prog (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', h⟩ := step1 (l := self) (v := v) (S := St) (l' := .no) (S' := St)
        (by simp [hp, skipU, TM2.stepAux, hX]) (by simp [hp, skipU, TM2.stepAux, hX])
      exact ⟨v', St, h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St src (l.map Sym.bit)) dst (Sym.bit true :: St dst)) hl'
            (by simp [update_of_ne hd.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, skipU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hd]

/-- `moveB` on a stack of bits moves all of them, reversed. -/
theorem mv_run {self next : Lab} {a b : K} (hp : prog self = moveB a b Sym.bit? Sym.bit self next)
    (hab : a ≠ b) (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (ha : St a = l.map Sym.bit) :
    ∃ v', Run prog (l.length + 1) ⟨some self, v, St⟩
      ⟨some next, v', update (update St a []) b ((l.map Sym.bit).reverse ++ St b)⟩ := by
  obtain ⟨v', S', h, ha', hb', hk'⟩ := moveB_run hp hab l (l.map Sym.bit) [] v St (by simp [ha])
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  refine ⟨v', ?_⟩
  have e : S' = update (update St a []) b ((l.map Sym.bit).reverse ++ St b) := by
    funext k
    by_cases h1 : k = b
    · subst h1; simpa using hb'
    · by_cases h2 : k = a
      · subst h2; simp [ha', update_of_ne h1]
      · simp [update_of_ne h1, update_of_ne h2, hk' k h2 h1]
  exact e ▸ h

/-- A counter comparison: all stacks are restored, and the outcome picks the next label. -/
theorem cmpI_run (i : CI) (m n : ℕ) (v : Bool) (St : ∀ _ : K, List Sym)
    (ha : St (ca i) = cnt (Sym.bit true) m) (hb : St (cb i) = cnt (Sym.bit true) n)
    (hR : St .R = []) (hQ : St .Q = []) :
    RunLe prog (3 * min m n + 4) ⟨some (.cmp i), v, St⟩ ⟨some (cout i (compare m n)), false, St⟩ :=
  by cases i <;>
    exact (cmp_run (M := prog) rfl (fun _ => rfl) (fun _ => rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) m n v St ha hb hR hQ).le (by split <;> omega)

/-- The comparison of `a` with `n`. -/
theorem cout_an (m n : ℕ) : cout .an (compare m n) = if m < n then .hd else .no := by
  rcases lt_trichotomy m n with h | rfl | h
  · simp [cout, Nat.compare_eq_lt.2 h, h]
  · simp [cout]
  · simp [cout, Nat.compare_eq_gt.2 h, Nat.not_lt.2 h.le]

/-- An equality comparison. -/
theorem cout_eq (i : CI) (l : Lab) (hl : cout i .eq = l) (hne : ∀ o, o ≠ .eq → cout i o = .no)
    (m n : ℕ) : cout i (compare m n) = if m = n then l else .no := by
  by_cases h : m = n
  · subst h; simpa using hl
  · rw [ite_eq_right h, hne]
    rwa [Ne, Nat.compare_eq_eq]

/-- The next unary number of `src` against the counter `c`, then `c` restored: the verdict
`ok && (number = c)` picks `nx`, the number's bits moved to `sv`. -/
theorem cb_run {src sv c : K} {cb fin : Bool → Lab}
    (hp : ∀ ok, prog (cb ok) = cbS src sv c cb fin ok) (h1 : sv ≠ src) (h2 : c ≠ src)
    (h3 : K.R ≠ src) (h4 : c ≠ sv) (h5 : K.R ≠ sv) (h6 : K.R ≠ c) :
    ∀ (a u j : ℕ) (ok : Bool) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St src = (List.replicate a true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) u →
      St .R = cnt (Sym.bit true) j →
      ∃ v' S', Run prog (a + 1) ⟨some (cb ok), v, St⟩
        ⟨some (fin (ok && decide (a = u))), v', S'⟩ ∧ S' src = r.map Sym.bit ∧
        S' sv = (List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv ∧
        S' c = cnt (Sym.bit true) (u - a) ∧ S' .R = cnt (Sym.bit true) (min a u + j) ∧
        ∀ k, k ≠ src → k ≠ sv → k ≠ c → k ≠ .R → S' k = St k := by
  intro a
  induction a with
  | zero =>
      intro u j ok r v St hs hc hR
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hs
      obtain ⟨v', h⟩ := step1 (l := cb ok) (v := v) (S := St)
        (l' := fin (ok && decide (0 = u)))
        (S' := update (update St src (r.map Sym.bit)) sv (Sym.bit false :: St sv))
        (by cases u <;> simp [hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, update_of_ne h1,
          update_of_ne h2, update_of_ne h4])
        (by cases u <;> simp [hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, update_of_ne h1,
          update_of_ne h2, update_of_ne h4])
      refine ⟨v', _, h, by simp [update_of_ne h1.symm], by simp, ?_, ?_, fun k k1 k2 _ _ => ?_⟩
      · simp [update_of_ne h4, update_of_ne h2, hc]
      · simp [update_of_ne h5, update_of_ne h3, hR]
      · simp [update_of_ne k1, update_of_ne k2]
  | succ a ih =>
      intro u j ok r v St hs hc hR
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hs
      cases u with
      | zero =>
          set St₁ := update (update (update St src
            ((List.replicate a true ++ false :: r).map Sym.bit)) sv (Sym.bit true :: St sv)) c []
            with hSt₁
          obtain ⟨v', S', hrun, hs', hsv', hc', hR', hF'⟩ := ih 0 j false r false St₁
            (by simp [hSt₁, update_of_ne h1.symm, update_of_ne h2.symm])
            (by simp [hSt₁])
            (by simp [hSt₁, update_of_ne h6, update_of_ne h5, update_of_ne h3, hR])
          have hstep :
              TM2.step prog ⟨some (cb ok), v, St⟩ = some ⟨some (cb false), false, St₁⟩ := by
            simp [TM2.step, hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, hSt₁,
              update_of_ne h1, update_of_ne h2, update_of_ne h4]
          refine ⟨v', S', by simpa using Run.head hstep hrun, hs', ?_, by simpa using hc', ?_,
            fun k k1 k2 k3 k4 => ?_⟩
          · rw [hsv', hSt₁, update_of_ne h4.symm, update_self, blk_succ]
          · simpa using hR'
          · rw [hF' k k1 k2 k3 k4, hSt₁, update_of_ne k3, update_of_ne k2, update_of_ne k1]
      | succ u =>
          set St₁ := update (update (update (update St src
            ((List.replicate a true ++ false :: r).map Sym.bit)) sv (Sym.bit true :: St sv)) c
            (cnt (Sym.bit true) u)) .R (Sym.bit true :: St .R) with hSt₁
          obtain ⟨v', S', hrun, hs', hsv', hc', hR', hF'⟩ := ih u (j + 1) ok r true St₁
            (by simp [hSt₁, update_of_ne h1.symm, update_of_ne h2.symm, update_of_ne h3.symm])
            (by simp [hSt₁, update_of_ne h6.symm]) (by simp [hSt₁, hR, cnt_succ])
          have hstep : TM2.step prog ⟨some (cb ok), v, St⟩ = some ⟨some (cb ok), true, St₁⟩ := by
            simp [TM2.step, hp, cbS, TM2.stepAux, hs, hc, bitOf, Sym.bit?, hSt₁, cnt_succ,
              update_of_ne h1, update_of_ne h2, update_of_ne h4, update_of_ne h6,
              update_of_ne h5, update_of_ne h3]
          refine ⟨v', S', by simpa using Run.head hstep hrun, hs', ?_, by simpa using hc', ?_,
            fun k k1 k2 k3 k4 => ?_⟩
          · rw [hsv', hSt₁, update_of_ne h5.symm, update_of_ne h4.symm, update_self, blk_succ]
          · rw [hR']; congr 1; omega
          · rw [hF' k k1 k2 k3 k4, hSt₁, update_of_ne k4, update_of_ne k3, update_of_ne k2,
              update_of_ne k1]

/-- `cb_run`, then the restoring loop: the counter `c` and `R` are as before. -/
theorem cmpN_run {src sv c : K} {cb rs nx : Bool → Lab}
    (hp : ∀ ok, prog (cb ok) = cbS src sv c cb rs ok)
    (hr : ∀ ok, prog (rs ok) = xfer .R [⟨c, Sym.bit true⟩] (rs ok) (nx ok))
    (h1 : sv ≠ src) (h2 : c ≠ src) (h3 : K.R ≠ src) (h4 : c ≠ sv) (h5 : K.R ≠ sv)
    (h6 : K.R ≠ c) (a u : ℕ) (ok : Bool) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hs : St src = (List.replicate a true ++ false :: r).map Sym.bit)
    (hc : St c = cnt (Sym.bit true) u) (hR : St .R = []) :
    ∃ v', Run prog (a + 1 + (min a u + 1)) ⟨some (cb ok), v, St⟩
      ⟨some (nx (ok && decide (a = u))), v', update (update St src (r.map Sym.bit)) sv
        ((List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv)⟩ := by
  obtain ⟨v₁, S₁, h₁, hs₁, hsv₁, hc₁, hR₁, hF₁⟩ :=
    cb_run hp h1 h2 h3 h4 h5 h6 a u 0 ok r v St hs hc (by simp [hR])
  have h₂ := xfer_run (hr (ok && decide (a = u))) (single_nodupKeys _) (by simpa using h6)
    (Sym.bit true) (min a u + 0) v₁ S₁ hR₁
  have e : addU [⟨c, Sym.bit true⟩] (min a u + 0) (update S₁ .R []) =
      update (update St src (r.map Sym.bit)) sv
        ((List.replicate a true ++ [false]).reverse.map Sym.bit ++ St sv) := by
    funext k
    by_cases hk : k = c
    · subst hk
      rw [addU_single_self, update_of_ne h6.symm, hc₁, update_of_ne h4, update_of_ne h2, hc,
        cnt_add]
      congr 1; omega
    · rw [addU_single_ne _ _ _ hk]
      by_cases hkR : k = .R
      · subst hkR; rw [update_self, update_of_ne h5, update_of_ne h3, hR]
      · rw [update_of_ne hkR]
        by_cases hks : k = sv
        · subst hks; rw [update_self, hsv₁]
        · rw [update_of_ne hks]
          by_cases hks' : k = src
          · subst hks'; rw [update_self, hs₁]
          · rw [update_of_ne hks', hF₁ k hks' hks hk hkR]
  rw [e] at h₂
  exact ⟨_, (h₁.trans h₂).of_eq (by omega)⟩

/-! ### Validation -/

/-- The edge-list check: from `vE` with the rest `r` of the input on `X` and the bits `acc`
already moved (reversed) on `E`, it reaches `vEb` iff `r` parses as an edge list, within
`2 |r| + 1` steps, having moved all of `r` to `E`. -/
theorem valE_run : ∀ (r acc : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .X = r.map Sym.bit → St .E = acc.reverse.map Sym.bit →
    ∃ v' S', RunLe prog (2 * r.length + 1) ⟨some .vE, v, St⟩
      ⟨some (if (Karp.decodeEs r).isSome then .vEb else .no), v', S'⟩ ∧
      ((Karp.decodeEs r).isSome →
        S' = update (update St .X []) .E ((acc ++ r).reverse.map Sym.bit)) := by
  intro r
  induction hL : r.length using Nat.strong_induction_on generalizing r with
  | _ L ih =>
  intro acc v St hX hE
  subst hL
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .vE) rfl v St
  by_cases hr : r = []
  · subst hr
    rw [ite_eq_left (by simpa using hX)] at h₀
    refine ⟨v₀, St, by simpa [Karp.decodeEs_nil] using h₀.le le_rfl, fun _ => ?_⟩
    funext k; cases k <;> simp_all
  have hpos : 1 ≤ r.length := List.length_pos_of_ne_nil hr
  rw [ite_eq_right (by rw [hX]; simpa using hr)] at h₀
  cases h₁ : readUnaryLength r with
  | none =>
      obtain ⟨v₁, S₁, r₁⟩ := skipU_none (src := .X) (dst := .E) (self := .vEU) (next := .vEV) rfl
        (by decide) r v₀ St h₁ hX
      rw [Karp.decodeEs_of_none hr h₁]
      exact ⟨v₁, S₁, ((h₀.le le_rfl).trans r₁).mono (by omega), by simp⟩
  | some p =>
      obtain ⟨u, r₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      have hl₁ : r.length = u + 1 + r₁.length := by rw [hx₁]; simp; omega
      obtain ⟨v₁, run₁⟩ := skipU_run (src := .X) (dst := .E) (self := .vEU) (next := .vEV) rfl
        (by decide) u r₁ v₀ St (by rw [hX, hx₁])
      set St₁ := update (update St .X (r₁.map Sym.bit)) .E
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .E) with hSt₁
      cases h₂ : readUnaryLength r₁ with
      | none =>
          obtain ⟨v₂, S₂, run₂⟩ := skipU_none (src := .X) (dst := .E) (self := .vEV) (next := .vE)
            rfl (by decide) r₁ v₁ St₁ h₂ (by simp [hSt₁])
          rw [Karp.decodeEs_of_some_none h₁ h₂]
          exact ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono (by omega),
            by simp⟩
      | some q =>
          obtain ⟨u', r₂⟩ := q
          have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
          have hl₂ : r₁.length = u' + 1 + r₂.length := by rw [hx₂]; simp; omega
          obtain ⟨v₂, run₂⟩ := skipU_run (src := .X) (dst := .E) (self := .vEV) (next := .vE) rfl
            (by decide) u' r₂ v₁ St₁ (by simp [hSt₁, hx₂])
          set St₂ := update (update St₁ .X (r₂.map Sym.bit)) .E
            ((List.replicate u' true ++ [false]).reverse.map Sym.bit ++ St₁ .E) with hSt₂
          obtain ⟨v₃, S₃, run₃, hF₃⟩ := ih r₂.length (by omega) r₂ rfl
            (acc ++ (List.replicate u true ++ [false]) ++ (List.replicate u' true ++ [false]))
            v₂ St₂ (by simp [hSt₂]) (by simp [hSt₂, hSt₁, hE])
          rw [Karp.decodeEs_of_some_some h₁ h₂, Option.isSome_map]
          refine ⟨v₃, S₃, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans
            (run₂.le le_rfl)).trans run₃).mono (by omega), fun h => ?_⟩
          rw [hF₃ h, hSt₂, hSt₁, update_update_update_update (by decide),
            update_update_update_update (by decide), hx₁, hx₂]
          simp

/-- The witness check: from `vW` with the rest `w` of the witness on `W` and the bits `acc`
already moved (reversed) on `Z`, it reaches `vWb` iff `w` parses as a vertex list, within
`2 |w| + 1` steps, having moved all of `w` to `Z`. -/
theorem valW_run : ∀ (w acc : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .W = w.map Sym.bit → St .Z = acc.reverse.map Sym.bit →
    ∃ v' S', RunLe prog (2 * w.length + 1) ⟨some .vW, v, St⟩
      ⟨some (if (decodeW w).isSome then .vWb else .no), v', S'⟩ ∧
      ((decodeW w).isSome → S' = update (update St .W []) .Z ((acc ++ w).reverse.map Sym.bit)) := by
  intro w
  induction hL : w.length using Nat.strong_induction_on generalizing w with
  | _ L ih =>
  intro acc v St hW hZ
  subst hL
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .vW) rfl v St
  by_cases hw : w = []
  · subst hw
    rw [ite_eq_left (by simpa using hW)] at h₀
    refine ⟨v₀, St, by simpa [decodeW_nil] using h₀.le le_rfl, fun _ => ?_⟩
    funext k; cases k <;> simp_all
  have hpos : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  rw [ite_eq_right (by rw [hW]; simpa using hw)] at h₀
  cases h₁ : readUnaryLength w with
  | none =>
      obtain ⟨v₁, S₁, r₁⟩ := skipU_none (src := .W) (dst := .Z) (self := .vWU) (next := .vW) rfl
        (by decide) w v₀ St h₁ hW
      rw [decodeW_of_none hw h₁]
      exact ⟨v₁, S₁, ((h₀.le le_rfl).trans r₁).mono (by omega), by simp⟩
  | some p =>
      obtain ⟨u, r₁⟩ := p
      have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
      have hl₁ : w.length = u + 1 + r₁.length := by rw [hx₁]; simp; omega
      obtain ⟨v₁, run₁⟩ := skipU_run (src := .W) (dst := .Z) (self := .vWU) (next := .vW) rfl
        (by decide) u r₁ v₀ St (by rw [hW, hx₁])
      set St₁ := update (update St .W (r₁.map Sym.bit)) .Z
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .Z) with hSt₁
      obtain ⟨v₂, S₂, run₂, hF₂⟩ := ih r₁.length (by omega) r₁ rfl
        (acc ++ (List.replicate u true ++ [false])) v₁ St₁ (by simp [hSt₁]) (by simp [hSt₁, hZ])
      rw [decodeW_of_some h₁, Option.isSome_map]
      refine ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono (by omega),
        fun h => ?_⟩
      rw [hF₂ h, hSt₁, update_update_update_update (by decide), hx₁]
      simp

/-! ### The scans -/

/-- The edge scan for the pair `(b, a)` (`b` on `B`, `a` on `A`): from `scan` with the edges
`rest` on `X` and the bits of the edges `done` already passed (reversed) on `E`, it reaches `nd`
iff `(b, a)` is one of `rest`, having put the edge list back on `X`. -/
theorem scan_run (a b : ℕ) : ∀ (rest done : List (ℕ × ℕ)) (v : Bool) (St : ∀ _ : K, List Sym),
    St .X = (Karp.edgeBits rest).map Sym.bit → St .E = (Karp.edgeBits done).reverse.map Sym.bit →
    St .A = cnt (Sym.bit true) a → St .B = cnt (Sym.bit true) b → St .R = [] →
    ∃ v' S', RunLe prog (4 * (Karp.edgeBits rest).length + (Karp.edgeBits done).length + 2)
      ⟨some .scan, v, St⟩ ⟨some (if (b, a) ∈ rest then .nd else .no), v', S'⟩ ∧
      ((b, a) ∈ rest →
        S' = update (update St .X ((Karp.edgeBits (done ++ rest)).map Sym.bit)) .E [])
  | [], done, v, St, hX, _, _, _, _ => by
      obtain ⟨v', h⟩ := ifE_run (l := .scan) rfl v St
      rw [ite_eq_left (by simpa using hX)] at h
      exact ⟨v', St, by simpa using h.le (by omega), by simp⟩
  | (u, u') :: rest, done, v, St, hX, hE, hA, hB, hR => by
      have hX' : St .X = (List.replicate u true ++ false ::
          (List.replicate u' true ++ false :: Karp.edgeBits rest)).map Sym.bit := by
        rw [hX, edgeBits_cons]
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .scan) rfl v St
      rw [ite_eq_right (by rw [hX']; simp)] at h₀
      obtain ⟨v₁, run₁⟩ := cmpN_run (src := .X) (sv := .E) (c := .B) (cb := .ceU) (rs := .rsU)
        (nx := .ceV) (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) u b true _ v₀ St hX' hB hR
      set St₁ := update (update St .X
        ((List.replicate u' true ++ false :: Karp.edgeBits rest).map Sym.bit)) .E
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .E) with hSt₁
      obtain ⟨v₂, run₂⟩ := cmpN_run (src := .X) (sv := .E) (c := .A) (cb := .ceV) (rs := .rsV)
        (nx := fun ok => if ok then .scB else .scan) (fun _ => rfl) (fun _ => rfl) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) u' a (true && decide (u = b))
        (Karp.edgeBits rest) v₁ St₁ (by simp [hSt₁]) (by simp [hSt₁, hA]) (by simp [hSt₁, hR])
      set St₂ := update (update St₁ .X ((Karp.edgeBits rest).map Sym.bit)) .E
        ((List.replicate u' true ++ [false]).reverse.map Sym.bit ++ St₁ .E) with hSt₂
      have hE₂ : St₂ .E = (Karp.edgeBits (done ++ [(u, u')])).reverse.map Sym.bit := by
        simp [hSt₂, hSt₁, hE, edgeBits_append, edgeBits_cons]
      have hlen : (Karp.edgeBits ((u, u') :: rest)).length =
          u + u' + 2 + (Karp.edgeBits rest).length := by simp [edgeBits_cons]; omega
      have hlen' : (Karp.edgeBits (done ++ [(u, u')])).length =
          (Karp.edgeBits done).length + u + u' + 2 := by
        simp [edgeBits_append, edgeBits_cons]; omega
      have m₁ := Nat.min_le_left u b
      have m₂ := Nat.min_le_left u' a
      by_cases hf : u = b ∧ u' = a
      · obtain ⟨rfl, rfl⟩ := hf
        simp only [decide_true, Bool.and_self, ↓reduceIte] at run₁ run₂
        rw [ite_eq_left List.mem_cons_self]
        obtain ⟨v₃, run₃⟩ := mv_run (self := .scB) (next := .nd) (a := .E) (b := .X) rfl
          (by decide) _ v₂ St₂ hE₂
        refine ⟨v₃, _, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans (run₂.le le_rfl)).trans
          (run₃.le le_rfl)).mono ?_, fun _ => ?_⟩
        · simp only [List.length_reverse]; omega
        · funext k
          cases k <;> simp [hSt₂, hSt₁, edgeBits_append, edgeBits_cons, List.map_reverse]
      · have hf' : (true && decide (u = b) && decide (u' = a)) = false := by
          simpa [not_and] using hf
        rw [hf'] at run₂
        obtain ⟨v₃, S₃, run₃, hF₃⟩ := scan_run a b rest (done ++ [(u, u')]) v₂ St₂
          (by simp [hSt₂]) hE₂ (by simp [hSt₂, hSt₁, hA]) (by simp [hSt₂, hSt₁, hB])
          (by simp [hSt₂, hSt₁, hR])
        have hm : (b, a) ∈ (u, u') :: rest ↔ (b, a) ∈ rest := by
          simp only [List.mem_cons, Prod.mk.injEq]
          exact ⟨fun h => h.resolve_left fun h' => hf ⟨h'.1.symm, h'.2.symm⟩, Or.inr⟩
        rw [if_congr hm rfl rfl]
        refine ⟨v₃, S₃, ((((h₀.le le_rfl).trans (run₁.le le_rfl)).trans
          (run₂.le le_rfl)).trans run₃).mono ?_, fun h => ?_⟩
        · rw [hlen', hlen]; omega
        · rw [hF₃ (hm.1 h)]
          funext k
          cases k <;> simp [hSt₂, hSt₁]

/-- The repeat scan for `a` (on `A`): from `nd` with the vertices `q` on `W` and the bits of the
vertices `done` already passed (reversed) on `Z`, it reaches `incC` iff `a` is not one of `q`,
having put the vertices back on `W`. -/
theorem nd_run (a : ℕ) : ∀ (q done : List ℕ) (v : Bool) (St : ∀ _ : K, List Sym),
    St .W = (encW q).map Sym.bit → St .Z = (encW done).reverse.map Sym.bit →
    St .A = cnt (Sym.bit true) a → St .R = [] →
    ∃ v' S', RunLe prog (4 * (encW q).length + (encW done).length + 2) ⟨some .nd, v, St⟩
      ⟨some (if a ∈ q then .no else .incC), v', S'⟩ ∧
      (a ∉ q → S' = update (update St .W ((encW (done ++ q)).map Sym.bit)) .Z [])
  | [], done, v, St, hW, hZ, _, _ => by
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .nd) rfl v St
      rw [ite_eq_left (by simpa using hW)] at h₀
      obtain ⟨v₁, h₁⟩ := mv_run (self := .ndB) (next := .incC) (a := .Z) (b := .W) rfl
        (by decide) _ v₀ St hZ
      refine ⟨v₁, _, ((h₀.le le_rfl).trans (h₁.le le_rfl)).mono (by simp; omega), fun _ => ?_⟩
      funext k
      cases k <;> simp [hW, List.map_reverse]
  | u :: q, done, v, St, hW, hZ, hA, hR => by
      have hW' : St .W = (List.replicate u true ++ false :: encW q).map Sym.bit := by
        rw [hW, encW_cons]
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .nd) rfl v St
      rw [ite_eq_right (by rw [hW']; simp)] at h₀
      obtain ⟨v₁, run₁⟩ := cmpN_run (src := .W) (sv := .Z) (c := .A) (cb := .cbN) (rs := .rsN)
        (nx := fun ok => if ok then .no else .nd) (fun _ => rfl) (fun _ => rfl) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) u a true _ v₀ St hW' hA hR
      set St₁ := update (update St .W ((encW q).map Sym.bit)) .Z
        ((List.replicate u true ++ [false]).reverse.map Sym.bit ++ St .Z) with hSt₁
      have hlen : (encW (u :: q)).length = u + 1 + (encW q).length := by simp [encW_cons]; omega
      have m₁ := Nat.min_le_left u a
      by_cases hua : u = a
      · subst hua
        simp only [Bool.true_and, decide_true, ↓reduceIte] at run₁
        rw [ite_eq_left List.mem_cons_self]
        refine ⟨v₁, _, ((h₀.le le_rfl).trans (run₁.le le_rfl)).mono (by omega), ?_⟩
        simp
      · have hf : (true && decide (u = a)) = false := by simpa using hua
        rw [hf] at run₁
        obtain ⟨v₂, S₂, run₂, hF₂⟩ := nd_run a q (done ++ [u]) v₁ St₁ (by simp [hSt₁])
          (by simp [hSt₁, hZ, encW_append, encW_cons]) (by simp [hSt₁, hA]) (by simp [hSt₁, hR])
        have hm : a ∈ u :: q ↔ a ∈ q := by
          simp only [List.mem_cons]
          exact ⟨fun h => h.resolve_left fun h' => hua h'.symm, Or.inr⟩
        rw [if_congr hm rfl rfl]
        have hlen' : (encW (done ++ [u])).length = (encW done).length + u + 1 := by
          simp [encW_append, encW_cons]; omega
        refine ⟨v₂, S₂, (((h₀.le le_rfl).trans (run₁.le le_rfl)).trans run₂).mono ?_,
          fun h => ?_⟩
        · rw [hlen', hlen]; omega
        · rw [hF₂ (fun h' => h (hm.2 h'))]
          funext k
          cases k <;> simp [hSt₁]

/-! ### The vertex walk -/

/-- The stacks between vertex steps: the edge list on `X`, the vertices `q` still to walk on
`W`, the counters `s`, `t`, `n`, the count `c` on `C`, the previous vertex `b` on `B`; all other
stacks empty. -/
def lay (es : List (ℕ × ℕ)) (s t n c b : ℕ) (q : List ℕ) : K → List Sym
  | .X => (Karp.edgeBits es).map Sym.bit
  | .W => (encW q).map Sym.bit
  | .S => cnt (Sym.bit true) s
  | .T => cnt (Sym.bit true) t
  | .N => cnt (Sym.bit true) n
  | .C => cnt (Sym.bit true) c
  | .A => []
  | .B => cnt (Sym.bit true) b
  | .E => []
  | .Z => []
  | .R => []
  | .Q => []

/-- The stacks during the step on vertex `a`: `lay`, with `a` on `A`. -/
def mid (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) : K → List Sym :=
  update (lay es s t n c b q) .A (cnt (Sym.bit true) a)

/-- The head-or-edge check on vertex `a`: with no vertex seen (`c = 0`) compare `a` with `s`,
otherwise scan the edge list for `(b, a)`; on success the stacks are as before. -/
theorem hd_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (3 * a + 4 * (Karp.edgeBits es).length + 7)
      ⟨some .hd, v, mid es s t n c b a q⟩
      ⟨some (if (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true then .nd
        else .no), v', S'⟩ ∧
      ((if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true →
        S' = mid es s t n c b a q) := by
  obtain ⟨v₀, h₀⟩ := ifE_run (l := .hd) rfl v (mid es s t n c b a q)
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left (by simp [mid, lay])] at h₀
    have h₁ := cmpI_run .as a s v₀ (mid es s t n 0 b a q) (by simp [mid, ca])
      (by simp [mid, lay, cb]) (by simp [mid, lay]) (by simp [mid, lay])
    rw [cout_eq .as .nd rfl (by intro o ho; cases o <;> simp_all [cout]) a s] at h₁
    simp only [↓reduceIte, decide_eq_true_eq]
    refine ⟨false, _, ((h₀.le le_rfl).trans h₁).mono ?_, fun _ => rfl⟩
    have := Nat.min_le_left a s
    omega
  · rw [ite_eq_right (by simp [mid, lay, hc])] at h₀
    obtain ⟨v₁, S₁, h₁, hF₁⟩ := scan_run a b es [] v₀ (mid es s t n c b a q) (by simp [mid, lay])
      (by simp [mid, lay]) (by simp [mid]) (by simp [mid, lay]) (by simp [mid, lay])
    simp only [hc, ↓reduceIte, decide_eq_true_eq]
    refine ⟨v₁, S₁, ((h₀.le le_rfl).trans h₁).mono (by simp; omega), fun h => ?_⟩
    rw [hF₁ h]
    funext k
    cases k <;> simp [mid, lay]

/-- The rest of a vertex step: the repeat scan for `a`, then `a` is counted and becomes the
previous vertex. -/
theorem tail_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (4 * (encW q).length + a + b + 6) ⟨some .nd, v, mid es s t n c b a q⟩
      ⟨some (if a ∈ q then .no else .loop), v', S'⟩ ∧
      (a ∉ q → S' = lay es s t n (c + 1) a q) := by
  obtain ⟨v₁, S₁, h₁, hF₁⟩ := nd_run a q [] v (mid es s t n c b a q) (by simp [mid, lay])
    (by simp [mid, lay]) (by simp [mid]) (by simp [mid, lay])
  by_cases ha : a ∈ q
  · rw [ite_eq_left ha] at h₁ ⊢
    exact ⟨v₁, S₁, h₁.mono (by simp; omega), fun h => absurd ha h⟩
  · rw [ite_eq_right ha] at h₁ ⊢
    have e₁ : S₁ = mid es s t n c b a q := by
      rw [hF₁ ha]
      funext k
      cases k <;> simp [mid, lay]
    subst e₁
    have h₂ := incr_run (M := prog) (self := .incC) (next := .dB) (k := .C) (u := Sym.bit true)
      rfl v₁ (mid es s t n c b a q)
    set S₂ := update (mid es s t n c b a q) .C (Sym.bit true :: mid es s t n c b a q .C) with hS₂
    have h₃ := xfer_run (M := prog) (self := .dB) (next := .mA) (k := .B) (ps := []) rfl
      (by simp) (by simp) (Sym.bit true) b v₁ S₂ (by simp [hS₂, mid, lay])
    set S₃ := addU ([] : List (Σ _ : K, Sym)) b (update S₂ .B []) with hS₃
    have h₄ := xfer_run (M := prog) (self := .mA) (next := .loop) (k := .A)
      (ps := [⟨.B, Sym.bit true⟩]) rfl (single_nodupKeys _) (by simp) (Sym.bit true) a
      (Flag.tag false) S₃
      (by simp [hS₃, hS₂, addU, mid])
    refine ⟨_, _, (((h₁.trans (h₂.le le_rfl)).trans (h₃.le le_rfl)).trans
      (h₄.le le_rfl)).mono (by simp; omega), fun _ => ?_⟩
    funext k
    cases k <;> simp [hS₃, hS₂, mid, lay, addU, cnt_succ]

/-- One vertex step, from reading the vertex `a` to the next round of the loop. -/
theorem step_run (es : List (ℕ × ℕ)) (s t n c b a : ℕ) (q : List ℕ) (v : Bool) :
    ∃ v' S', RunLe prog (8 * a + b + 4 * (Karp.edgeBits es).length + 4 * (encW q).length + 20)
      ⟨some .rdA, v, lay es s t n c b (a :: q)⟩
      ⟨some (if stepOk s n es c b a q then .loop else .no), v', S'⟩ ∧
      (stepOk s n es c b a q = true → S' = lay es s t n (c + 1) a q) := by
  obtain ⟨v₁, h₁⟩ := readU_run (src := .W) (c := .A) (self := .rdA) (next := .cmp .an) rfl
    (by decide) a 0 (encW q) v (lay es s t n c b (a :: q)) (by simp [lay, encW_cons])
    (by simp [lay])
  have e₁ : update (update (lay es s t n c b (a :: q)) .W ((encW q).map Sym.bit)) .A
      (cnt (Sym.bit true) (a + 0)) = mid es s t n c b a q := by
    funext k
    cases k <;> simp [mid, lay]
  rw [e₁] at h₁
  have h₂ := cmpI_run .an a n v₁ (mid es s t n c b a q) (by simp [mid, ca])
    (by simp [mid, lay, cb]) (by simp [mid, lay]) (by simp [mid, lay])
  rw [cout_an] at h₂
  have m₁ := Nat.min_le_left a n
  by_cases han : a < n
  · rw [ite_eq_left han] at h₂
    obtain ⟨v₃, S₃, h₃, hF₃⟩ := hd_run es s t n c b a q false
    by_cases hh : (if c = 0 then decide (a = s) else decide ((b, a) ∈ es)) = true
    · rw [ite_eq_left hh, hF₃ hh] at h₃
      obtain ⟨v₄, S₄, h₄, hF₄⟩ := tail_run es s t n c b a q v₃
      have hs : stepOk s n es c b a q = !decide (a ∈ q) := by
        simp only [stepOk, han, decide_true, Bool.true_and, hh]
      refine ⟨v₄, S₄, ?_, fun h => hF₄ (by simpa [hs] using h)⟩
      have e : (if stepOk s n es c b a q = true then Lab.loop else Lab.no) =
          if a ∈ q then .no else .loop := by
        by_cases ha : a ∈ q <;> simp [hs, ha]
      rw [e]
      exact ((((h₁.le le_rfl).trans h₂).trans h₃).trans h₄).mono (by omega)
    · rw [ite_eq_right hh] at h₃
      have hs : stepOk s n es c b a q = false := by
        simp only [stepOk, Bool.eq_false_iff.2 hh, Bool.and_false, Bool.false_and]
      refine ⟨v₃, S₃, ?_, fun h => by simp [hs] at h⟩
      rw [hs]
      exact (((h₁.le le_rfl).trans h₂).trans h₃).mono (by omega)
  · rw [ite_eq_right han] at h₂
    have hs : stepOk s n es c b a q = false := by simp [stepOk, han]
    refine ⟨false, mid es s t n c b a q, ?_, fun h => by simp [hs] at h⟩
    rw [hs]
    exact ((h₁.le le_rfl).trans h₂).mono (by omega)

/-- The vertex loop: from `loop` with the vertices `q` still to walk, `c` seen and `b` the
previous one, it reaches `yes` iff `walkOk s t n es c b q`, within `(|q| + 1) (20 L + 20)`
steps for a bound `L` on `n`, `t`, the edge bits, the bits of `q` and `b`. -/
theorem loop_run (es : List (ℕ × ℕ)) (s t n L : ℕ) (hn : n ≤ L) (ht : t ≤ L)
    (he : (Karp.edgeBits es).length ≤ L) : ∀ (q : List ℕ) (c b : ℕ) (v : Bool),
    (encW q).length ≤ L → b ≤ L →
    ∃ v' S', RunLe prog ((q.length + 1) * (20 * L + 20)) ⟨some .loop, v, lay es s t n c b q⟩
      ⟨some (if walkOk s t n es c b q then .yes else .no), v', S'⟩
  | [], c, b, v, _, _ => by
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .loop) rfl v (lay es s t n c b [])
      rw [ite_eq_left (by simp [lay])] at h₀
      have h₁ := cmpI_run .cn c n v₀ (lay es s t n c b []) (by simp [lay, ca]) (by simp [lay, cb])
        (by simp [lay]) (by simp [lay])
      rw [cout_eq .cn .fin rfl (by intro o ho; cases o <;> simp_all [cout]) c n] at h₁
      have m₁ := Nat.min_le_right c n
      by_cases hcn : c = n
      · rw [ite_eq_left hcn] at h₁
        obtain ⟨v₂, h₂⟩ := ifE_run (l := .fin) rfl false (lay es s t n c b [])
        by_cases hc0 : c = 0
        · rw [ite_eq_left (by simp [lay, hc0])] at h₂
          have hw : walkOk s t n es c b [] = false := by simp [walkOk, hc0]
          rw [hw]
          exact ⟨v₂, _, (((h₀.le le_rfl).trans h₁).trans (h₂.le le_rfl)).mono
            (by simp only [List.length_nil]; omega)⟩
        · rw [ite_eq_right (by simp [lay, hc0])] at h₂
          have h₃ := cmpI_run .bt b t v₂ (lay es s t n c b []) (by simp [lay, ca])
            (by simp [lay, cb]) (by simp [lay]) (by simp [lay])
          rw [cout_eq .bt .yes rfl (by intro o ho; cases o <;> simp_all [cout]) b t] at h₃
          have m₂ := Nat.min_le_right b t
          have hw : walkOk s t n es c b [] = decide (b = t) := by subst hcn; simp [walkOk, hc0]
          rw [hw]
          simp only [decide_eq_true_eq]
          exact ⟨false, _, ((((h₀.le le_rfl).trans h₁).trans (h₂.le le_rfl)).trans h₃).mono
            (by simp only [List.length_nil]; omega)⟩
      · rw [ite_eq_right hcn] at h₁
        have hw : walkOk s t n es c b [] = false := by simp [walkOk, hcn]
        rw [hw]
        exact ⟨false, _, ((h₀.le le_rfl).trans h₁).mono (by simp only [List.length_nil]; omega)⟩
  | a :: q, c, b, v, hq, hb => by
      have hq' : a + 1 + (encW q).length ≤ L := by simp [encW_cons] at hq; omega
      obtain ⟨v₀, h₀⟩ := ifE_run (l := .loop) rfl v (lay es s t n c b (a :: q))
      rw [ite_eq_right (by simp [lay, encW_cons])] at h₀
      obtain ⟨v₁, S₁, h₁, hF₁⟩ := step_run es s t n c b a q v₀
      by_cases hst : stepOk s n es c b a q = true
      · rw [ite_eq_left hst, hF₁ hst] at h₁
        obtain ⟨v₂, S₂, h₂⟩ := loop_run es s t n L hn ht he q (c + 1) a v₁ (by omega) (by omega)
        refine ⟨v₂, S₂, ?_⟩
        rw [walkOk, hst, Bool.true_and]
        refine (((h₀.le le_rfl).trans h₁).trans h₂).mono ?_
        simp only [List.length_cons]
        nlinarith
      · have hst' : stepOk s n es c b a q = false := by simpa using hst
        rw [ite_eq_right hst] at h₁
        refine ⟨v₁, S₁, ?_⟩
        rw [walkOk, hst', Bool.false_and]
        refine ((h₀.le le_rfl).trans h₁).mono ?_
        simp only [List.length_cons]
        nlinarith

/-! ### The verifier -/

/-- **The verifier machine.** From `start` with `x` on `X`, `w` on `W` and the other stacks
empty, `prog` reaches `yes` if `hamCheck x w` and `no` otherwise, within
`100 (|x| + |w| + 1)⁴` steps (quadratically many, in fact). -/
theorem run (x w : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hX : St .X = x.map Sym.bit) (hW : St .W = w.map Sym.bit)
    (h0 : ∀ k, k ≠ .X → k ≠ .W → St k = []) :
    ∃ v' S', RunLe prog (100 * (x.length + w.length + 1) ^ 4) ⟨some start, v, St⟩
      ⟨some (if hamCheck x w then .yes else .no), v', S'⟩ := by
  set L := x.length + w.length + 1 with hL
  have hL1 : 1 ≤ L := by omega
  have hLL : L ≤ L * L := Nat.le_mul_self L
  have hL4 : L * L ≤ L ^ 4 := by
    calc L * L = L ^ 2 := (sq L).symm
      _ ≤ L ^ 4 := Nat.pow_le_pow_right hL1 (by omega)
  have hS : St .S = [] := h0 .S (by decide) (by decide)
  have hT : St .T = [] := h0 .T (by decide) (by decide)
  have hN : St .N = [] := h0 .N (by decide) (by decide)
  have hC : St .C = [] := h0 .C (by decide) (by decide)
  have hA : St .A = [] := h0 .A (by decide) (by decide)
  have hB : St .B = [] := h0 .B (by decide) (by decide)
  have hE : St .E = [] := h0 .E (by decide) (by decide)
  have hZ : St .Z = [] := h0 .Z (by decide) (by decide)
  have hR : St .R = [] := h0 .R (by decide) (by decide)
  have hQ : St .Q = [] := h0 .Q (by decide) (by decide)
  cases h₁ : readUnaryLength x with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .S) (self := .rdS) (next := .rdT) rfl
        (by decide) x v St h₁ hX
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, h₁])]
      exact ⟨v', S', r.mono (by nlinarith)⟩
  | some p =>
  obtain ⟨s, r₁⟩ := p
  have hx₁ := (readUnaryLength_eq_some_iff _ _ _).1 h₁
  obtain ⟨v₁, run₁⟩ := readU_run (src := .X) (c := .S) (self := .rdS) (next := .rdT) rfl
    (by decide) s 0 r₁ v St (by rw [hX, hx₁]) (by simp [hS])
  set St₁ := update (update St .X (r₁.map Sym.bit)) .S (cnt (Sym.bit true) (s + 0)) with hSt₁
  have hl₁ : x.length = s + 1 + r₁.length := by rw [hx₁]; simp; omega
  cases h₂ : readUnaryLength r₁ with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .T) (self := .rdT) (next := .rdN) rfl
        (by decide) r₁ v₁ St₁ h₂ (by simp [hSt₁])
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, h₁, h₂])]
      exact ⟨v', S', ((run₁.le le_rfl).trans r).mono (by nlinarith)⟩
  | some p =>
  obtain ⟨t, r₂⟩ := p
  have hx₂ := (readUnaryLength_eq_some_iff _ _ _).1 h₂
  obtain ⟨v₂, run₂⟩ := readU_run (src := .X) (c := .T) (self := .rdT) (next := .rdN) rfl
    (by decide) t 0 r₂ v₁ St₁ (by simp [hSt₁, hx₂]) (by simp [hSt₁, hT])
  set St₂ := update (update St₁ .X (r₂.map Sym.bit)) .T (cnt (Sym.bit true) (t + 0)) with hSt₂
  have hl₂ : r₁.length = t + 1 + r₂.length := by rw [hx₂]; simp; omega
  cases h₃ : readUnaryLength r₂ with
  | none =>
      obtain ⟨v', S', r⟩ := readU_none (src := .X) (c := .N) (self := .rdN) (next := .vE) rfl
        (by decide) r₂ v₂ St₂ h₃ (by simp [hSt₂])
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, Karp.decodeE, h₁, h₂, h₃])]
      exact ⟨v', S', (((run₁.le le_rfl).trans (run₂.le le_rfl)).trans r).mono (by nlinarith)⟩
  | some p =>
  obtain ⟨n, r₃⟩ := p
  have hx₃ := (readUnaryLength_eq_some_iff _ _ _).1 h₃
  obtain ⟨v₃, run₃⟩ := readU_run (src := .X) (c := .N) (self := .rdN) (next := .vE) rfl
    (by decide) n 0 r₃ v₂ St₂ (by simp [hSt₂, hx₃]) (by simp [hSt₂, hSt₁, hN])
  set St₃ := update (update St₂ .X (r₃.map Sym.bit)) .N (cnt (Sym.bit true) (n + 0)) with hSt₃
  have hl₃ : r₂.length = n + 1 + r₃.length := by rw [hx₃]; simp; omega
  obtain ⟨v₄, S₄, run₄, hF₄⟩ := valE_run r₃ [] v₃ St₃ (by simp [hSt₃])
    (by simp [hSt₃, hSt₂, hSt₁, hE])
  have run₀₃ := ((run₁.le le_rfl).trans (run₂.le le_rfl)).trans (run₃.le le_rfl)
  cases h₄ : Karp.decodeEs r₃ with
  | none =>
      simp only [h₄, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at run₄
      rw [hamCheck_of_decodeP (by simp [Path.decodeP, Karp.decodeE, h₁, h₂, h₃, h₄])]
      exact ⟨v₄, S₄, (run₀₃.trans run₄).mono (by nlinarith)⟩
  | some es =>
  have hr₃ : Karp.edgeBits es = r₃ := Karp.edgeBits_of_decodeEs h₄
  simp only [h₄, Option.isSome_some, ↓reduceIte, forall_const, List.nil_append] at run₄ hF₄
  rw [hF₄] at run₄
  obtain ⟨v₅, run₅⟩ := mv_run (self := .vEb) (next := .vW) (a := .E) (b := .X) rfl (by decide)
    r₃.reverse v₄ (update (update St₃ .X []) .E (r₃.reverse.map Sym.bit)) (by simp)
  set St₅ := update (update (update (update St₃ .X []) .E (r₃.reverse.map Sym.bit)) .E []) .X
    ((r₃.reverse.map Sym.bit).reverse ++
      update (update St₃ .X []) .E (r₃.reverse.map Sym.bit) .X) with hSt₅
  obtain ⟨v₆, S₆, run₆, hF₆⟩ := valW_run w [] v₅ St₅ (by simp [hSt₅, hSt₃, hSt₂, hSt₁, hW])
    (by simp [hSt₅, hSt₃, hSt₂, hSt₁, hZ])
  have run₀₅ := (run₀₃.trans run₄).trans (run₅.le le_rfl)
  cases h₅ : decodeW w with
  | none =>
      simp only [h₅, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at run₆
      rw [hamCheck_of_decodeW x h₅]
      exact ⟨v₆, S₆, (run₀₅.trans run₆).mono (by simp only [List.length_reverse]; nlinarith)⟩
  | some p =>
  have hw₅ : encW p = w := encW_of_decodeW h₅
  simp only [h₅, Option.isSome_some, ↓reduceIte, forall_const, List.nil_append] at run₆ hF₆
  rw [hF₆] at run₆
  obtain ⟨v₇, run₇⟩ := mv_run (self := .vWb) (next := .loop) (a := .Z) (b := .W) rfl (by decide)
    w.reverse v₆ (update (update St₅ .W []) .Z (w.reverse.map Sym.bit)) (by simp)
  have e₇ : update (update (update (update St₅ .W []) .Z (w.reverse.map Sym.bit)) .Z []) .W
      ((w.reverse.map Sym.bit).reverse ++
        update (update St₅ .W []) .Z (w.reverse.map Sym.bit) .W) = lay es s t n 0 0 p := by
    funext k
    cases k <;> simp [hSt₅, hSt₃, hSt₂, hSt₁, lay, hr₃, hw₅, List.map_reverse, hC, hA, hB, hR,
      hQ]
  rw [e₇] at run₇
  have hpw : p.length ≤ w.length := hw₅ ▸ length_le_length_encW p
  obtain ⟨v₈, S₈, run₈⟩ := loop_run es s t n L (by omega) (by omega)
    (by rw [hr₃]; omega) p 0 0 v₇ (by rw [hw₅]; omega) (by omega)
  have hx : x = Path.encodeP s t n es := by
    rw [hx₁, hx₂, hx₃, ← hr₃]; rfl
  have hc : hamCheck x w = walkOk s t n es 0 0 p := by
    rw [hx, ← hw₅, hamCheck_encode, walkOk_eq]
  rw [hc]
  refine ⟨v₈, S₈, ((run₀₅.trans run₆).trans ((run₇.le le_rfl).trans run₈)).mono ?_⟩
  have hp1 : (p.length + 1) * (20 * L + 20) ≤ L * (20 * L + 20) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_reverse]
  nlinarith

end Cslib.Complexity.Karp.HamVerify
