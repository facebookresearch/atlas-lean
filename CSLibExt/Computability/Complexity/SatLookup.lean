/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps

/-!
# The lookup component of the SAT verifier as a `TM2` machine

Component (2) of `SatVerifierSpec`: from a query name block `(q.map .bit).reverse` on top of
stack `T` and the table `tblStk es` on stack `B`, compute `liveVal es q` on the empty stack `V`,
leaving every other stack exactly as it was (`run`, within `8 · |tblStk es| + 4` steps).

The machine pushes `bit false` on `V`, then scans `B` from the top, i.e. the entries last-first,
moving each entry onto the stash `S`: it moves the marker; a dead entry's name goes straight to
`S`; for a live entry `val b` it compares the query with the name (`cmpB`, scratch stacks `A`
and `C`), on equality overwrites `V` with `bit b`, restores both blocks (`moveB_restore`) and
moves the name to `S`. The last live match overwritten is the first in list order, which is
`liveVal`. Finally it moves the entries back from `S` to `B`.

Each comparison costs at most the entry's name length plus one (the common prefix is a prefix of
the name), so the bound is linear in the table and independent of `q`.
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier.Lookup

open Turing MetaMathlibExt TM2Program Function

/-- **Stacks of the lookup machine.** The lookup machine has six stacks: the query stack $T$, the
table stack $B$, the stash $S$, the two scratch stacks $A$ and $C$ used for comparisons, and the
value stack $V$. -/
inductive K | T | B | S | A | C | V
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.T, .B, .S, .A, .C, .V], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Labels of the lookup machine.** The lookup machine has the labels $\mathsf{init}$,
$\mathsf{scan}$, $\mathsf{cmp}(b)$ and $\mathsf{put}(b)$ for each bit $b$, $\mathsf{rstT}$,
$\mathsf{rstB}$, $\mathsf{mvN}$, $\mathsf{back}$, $\mathsf{mark}$ and $\mathsf{done}$. The labels
$\mathsf{cmp}(b)$ and $\mathsf{put}(b)$ serve a live table entry with value $b$. -/
inductive Lab
  | init | scan | cmp (b : Bool) | put (b : Bool) | rstT | rstB | mvN | back | mark | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.init, .scan, .cmp false, .cmp true, .put false, .put true, .rstT, .rstB, .mvN,
    .back, .mark, .done], by decide⟩
  complete := fun l => by
    cases l with
    | cmp b => cases b <;> decide
    | put b => cases b <;> decide
    | _ => decide

/-- **Moving a symbol between stacks.** For stacks $a$ and $b$, a symbol $x$ and a map $f$ from
symbols to labels, this machine instruction pops the top of $a$ (if any), pushes $x$ onto $b$ and
goes to the label $f(x)$. -/
def mvSym (a b : K) (x : Sym) (f : Sym → Lab) : TM2.Stmt (fun _ : K => Sym) Lab Bool :=
  .pop a (fun s _ => s) <| .push b (fun _ => x) <| .goto fun _ => f x

/-- **Moving a table marker between stacks.** For stacks $a$ and $b$, a label $e$ and a map $f$
from symbols to labels, this machine instruction does the following: if the top of $a$ is a table
marker $y$ (that is, $\mathsf{dead}$ or $\mathsf{val}(c)$ for a bit $c$), it pops $y$ from $a$,
pushes it onto $b$ and goes to $f(y)$; if $a$ is empty or has another symbol on top, it goes to
$e$ and leaves the stacks unchanged.

The invariants of the lookup machine rule out another symbol on top of $a$. -/
def mvMark (a b : K) (e : Lab) (f : Sym → Lab) : TM2.Stmt (fun _ : K => Sym) Lab Bool :=
  .peek a (fun _ (o : Option Sym) => decide (o = none)) <| .branch id (.goto fun _ => e) <|
  .peek a (fun _ (o : Option Sym) => decide (o = some .dead)) <|
    .branch id (mvSym a b .dead f) <|
  .peek a (fun _ (o : Option Sym) => decide (o = some (.val true))) <|
    .branch id (mvSym a b (.val true) f) <|
  .peek a (fun _ (o : Option Sym) => decide (o = some (.val false))) <|
    .branch id (mvSym a b (.val false) f) (.goto fun _ => e)

/-- **Next label of the lookup scan.** The label at which the lookup scan continues after moving
a marker symbol $x$: the comparison label $\mathsf{cmp}(b)$ if $x$ is the value marker
$\mathsf{val}(b)$, and the name-moving label $\mathsf{mvN}$ for every other symbol. -/
def scanNext : Sym → Lab
  | .val b => .cmp b
  | _ => .mvN

/-- **The lookup program.** The lookup machine works on the stacks $T$, $B$, $S$, $A$, $C$ and
$V$ and acts at each label as follows. At $\mathsf{init}$ it pushes the bit symbol of false onto
$V$ and goes to $\mathsf{scan}$. At $\mathsf{scan}$, if the top of $B$ is a table marker it moves
that marker onto $S$ and goes to $\mathsf{cmp}(b)$ if the marker is $\mathsf{val}(b)$ and to
$\mathsf{mvN}$ if it is $\mathsf{dead}$; if $B$ is empty or has another symbol on top it goes to
$\mathsf{back}$. At $\mathsf{cmp}(b)$ it compares the bit blocks on top of $T$ and $B$: while
both tops are equal bits it pops them, pushes that bit symbol onto $A$ and onto $C$ and stays at
$\mathsf{cmp}(b)$; when both blocks end together it goes to $\mathsf{put}(b)$, and on a mismatch
(different bits, or one block ending first) it goes to $\mathsf{rstT}$ without popping. At
$\mathsf{put}(b)$ it pops $V$, pushes the bit symbol of $b$ onto $V$ and goes to
$\mathsf{rstT}$. At $\mathsf{rstT}$, $\mathsf{rstB}$, $\mathsf{mvN}$ and $\mathsf{back}$ it moves
the bit block on top of $A$ onto $T$, of $C$ onto $B$, of $B$ onto $S$ and of $S$ onto $B$
respectively, staying at the label while the top is a bit and then going to $\mathsf{rstB}$,
$\mathsf{mvN}$, $\mathsf{scan}$ and $\mathsf{mark}$ respectively. At $\mathsf{mark}$, if the top
of $S$ is a table marker it moves that marker onto $B$ and goes to $\mathsf{back}$; if $S$ is
empty or has another symbol on top it goes to $\mathsf{done}$. At $\mathsf{done}$ it halts. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .init => .push .V (fun _ => Sym.bit false) (.goto fun _ => .scan)
  | .scan => mvMark .B .S .back scanNext
  | .cmp b => cmpB .T .B .A .C Sym.bit? Sym.bit? Sym.bit Sym.bit (.cmp b) (.put b) .rstT
  | .put b => .pop .V (fun s _ => s) (.push .V (fun _ => Sym.bit b) (.goto fun _ => .rstT))
  | .rstT => moveB .A .T Sym.bit? Sym.bit .rstT .rstB
  | .rstB => moveB .C .B Sym.bit? Sym.bit .rstB .mvN
  | .mvN => moveB .B .S Sym.bit? Sym.bit .mvN .scan
  | .back => moveB .S .B Sym.bit? Sym.bit .back .mark
  | .mark => mvMark .S .B .done fun _ => .back
  | .done => .halt

/-- **Start label of the lookup machine.** The lookup program starts at its initialization label
$\mathsf{init}$. -/
def start : Lab := .init

/-- **Stack contents of the lookup machine.** For lists of symbols $t$, $b$, $s$, $a$, $c$, $v$,
the assignment of contents to the six stacks of the lookup machine that gives $T$ the list $t$,
$B$ the list $b$, $S$ the list $s$, $A$ the list $a$, $C$ the list $c$ and $V$ the list $v$. -/
def stk (t b s a c v : List Sym) : ∀ _ : K, List Sym
  | .T => t
  | .B => b
  | .S => s
  | .A => a
  | .C => c
  | .V => v

section Upd

variable (t b s a c v l : List Sym)

@[simp] theorem stk_T : stk t b s a c v .T = t := rfl
@[simp] theorem stk_B : stk t b s a c v .B = b := rfl
@[simp] theorem stk_S : stk t b s a c v .S = s := rfl
@[simp] theorem stk_A : stk t b s a c v .A = a := rfl
@[simp] theorem stk_C : stk t b s a c v .C = c := rfl
@[simp] theorem stk_V : stk t b s a c v .V = v := rfl

@[simp] theorem upd_T : update (stk t b s a c v) .T l = stk l b s a c v := by
  funext k; cases k <;> rfl
@[simp] theorem upd_B : update (stk t b s a c v) .B l = stk t l s a c v := by
  funext k; cases k <;> rfl
@[simp] theorem upd_S : update (stk t b s a c v) .S l = stk t b l a c v := by
  funext k; cases k <;> rfl
@[simp] theorem upd_A : update (stk t b s a c v) .A l = stk t b s l c v := by
  funext k; cases k <;> rfl
@[simp] theorem upd_C : update (stk t b s a c v) .C l = stk t b s a l v := by
  funext k; cases k <;> rfl
@[simp] theorem upd_V : update (stk t b s a c v) .V l = stk t b s a c l := by
  funext k; cases k <;> rfl

end Upd

theorem stk_ext {St : ∀ _ : K, List Sym} {t b s a c v : List Sym} (hT : St .T = t)
    (hB : St .B = b) (hS : St .S = s) (hA : St .A = a) (hC : St .C = c) (hV : St .V = v) :
    St = stk t b s a c v := by
  funext k; cases k <;> assumption

/-! ### Name blocks and table entries -/

/-- **A name bit reads as itself.** For every bit $b$, the name-bit symbol for $b$ reads as the
bit $b$. -/
theorem bit?_bit (b : Bool) : Sym.bit? (.bit b) = some b := rfl

theorem bit_of_bit? (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

theorem isBitBlock_map (l : List Bool) : IsBitBlock Sym.bit? (l.map Sym.bit) l := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?]

theorem isBitBlock_rev (l : List Bool) :
    IsBitBlock Sym.bit? (l.map Sym.bit).reverse l.reverse := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?]

theorem ends_markOf (m : Option Bool) (l : List Sym) : EndsBitBlock Sym.bit? (markOf m :: l) := by
  cases m <;> rfl

theorem tblStk_concat (pre : List Ent) (e : Ent) :
    tblStk (pre ++ [e]) = markOf e.2 :: ((e.1.map Sym.bit).reverse ++ tblStk pre) := by
  simp [tblStk, entToks]

theorem ends_tblStk (pre : List Ent) : EndsBitBlock Sym.bit? (tblStk pre) := by
  induction pre using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre e _ => rw [tblStk_concat]; exact ends_markOf _ _

theorem flatMap_cons_entToks (e : Ent) (post : List Ent) :
    (e :: post).flatMap entToks = e.1.map Sym.bit ++ markOf e.2 :: post.flatMap entToks := by
  simp [entToks]

theorem liveVal_dead (n : List Bool) (post : List Ent) (q : List Bool) :
    liveVal ((n, none) :: post) q = liveVal post q := by
  simp [liveVal]

theorem liveVal_val (n : List Bool) (b : Bool) (post : List Ent) (q : List Bool) :
    liveVal ((n, some b) :: post) q = if n = q then b else liveVal post q := by
  by_cases h : n = q <;> simp [liveVal, h]

/-! ### Single steps -/

/-- **Initialization step of the lookup machine.** Let $t$ and $b$ be lists of symbols and $v$ a
bit. In exactly one step, the lookup program goes from the label $\mathsf{init}$ with internal bit
$v$, stack $T$ holding $t$, stack $B$ holding $b$ and the stacks $S$, $A$, $C$, $V$ empty, to the
label $\mathsf{scan}$ with internal bit $v$, the same contents of $T$, $B$, $S$, $A$ and $C$, and
stack $V$ holding the single symbol name bit false. -/
theorem init_run (t b : List Sym) (v : Bool) :
    Run prog 1 ⟨some .init, v, stk t b [] [] [] []⟩
      ⟨some .scan, v, stk t b [] [] [] [Sym.bit false]⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem scan_nil (t s a c w : List Sym) (v : Bool) :
    Run prog 1 ⟨some .scan, v, stk t [] s a c w⟩ ⟨some .back, true, stk t [] s a c w⟩ :=
  Run.single (by simp [prog, mvMark, TM2.stepAux])

theorem scan_cons (m : Option Bool) (t r s a c w : List Sym) (v : Bool) :
    Run prog 1 ⟨some .scan, v, stk t (markOf m :: r) s a c w⟩
      ⟨some (scanNext (markOf m)), true, stk t r (markOf m :: s) a c w⟩ := by
  refine Run.single ?_
  cases m with
  | none => simp [prog, mvMark, mvSym, TM2.stepAux, markOf, scanNext]
  | some b => cases b <;> simp [prog, mvMark, mvSym, TM2.stepAux, markOf, scanNext]

theorem mark_nil (t b a c w : List Sym) (v : Bool) :
    Run prog 1 ⟨some .mark, v, stk t b [] a c w⟩ ⟨some .done, true, stk t b [] a c w⟩ :=
  Run.single (by simp [prog, mvMark, TM2.stepAux])

theorem mark_cons (m : Option Bool) (t b r a c w : List Sym) (v : Bool) :
    Run prog 1 ⟨some .mark, v, stk t b (markOf m :: r) a c w⟩
      ⟨some .back, true, stk t (markOf m :: b) r a c w⟩ := by
  refine Run.single ?_
  cases m with
  | none => simp [prog, mvMark, mvSym, TM2.stepAux, markOf]
  | some b => cases b <;> simp [prog, mvMark, mvSym, TM2.stepAux, markOf]

theorem put_run (b : Bool) (t bb s a c : List Sym) (x : Sym) (v : Bool) :
    Run prog 1 ⟨some (.put b), v, stk t bb s a c [x]⟩
      ⟨some .rstT, v, stk t bb s a c [Sym.bit b]⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

/-! ### One table entry -/

/-- **Restoring and stashing after a comparison in the lookup machine.** Let $q$, $n$, $c$ be
lists of bits such that $c$ is a prefix of both the reverse of $q$ and the reverse of $n$; let
$R$, $r$, $s$, $w$ be lists of symbols with $r$ empty or starting with a symbol other than a name
bit; and for a list of bits $x$ write $\bar x$ for the list of its bits as name bits. Suppose the
lookup program is at label $\mathsf{rstT}$, with any internal bit, and its stacks are: $T$ holds
the reverse of $\bar q$ with its first $|c|$ symbols removed, followed by $R$; $B$ holds the
reverse of $\bar n$ with its first $|c|$ symbols removed, followed by $r$; $S$ holds $s$; $A$ and
$C$ both hold the reverse of $\bar c$; and $V$ holds $w$. Then after exactly
$2(|c| + 1) + (|n| + 1)$ steps the program is at label $\mathsf{scan}$, with some internal bit,
where $T$ holds the reverse of $\bar q$ followed by $R$, $B$ holds $r$, $S$ holds $\bar n$
followed by $s$, $A$ and $C$ are empty, and $V$ holds $w$. -/
theorem tail_run (q n c : List Bool) (hcq : c <+: q.reverse) (hcn : c <+: n.reverse)
    (R r s w : List Sym) (hr : EndsBitBlock Sym.bit? r) (v : Bool) :
    ∃ v', Run prog (2 * (c.length + 1) + (n.length + 1))
      ⟨some .rstT, v, stk (((q.map Sym.bit).reverse).drop c.length ++ R)
        (((n.map Sym.bit).reverse).drop c.length ++ r) s (c.map Sym.bit).reverse
        (c.map Sym.bit).reverse w⟩
      ⟨some .scan, v', stk ((q.map Sym.bit).reverse ++ R) r (n.map Sym.bit ++ s) [] [] w⟩ := by
  obtain ⟨v₁, S₁, h₁, h₁A, h₁T, h₁k⟩ := moveB_restore (M := prog) (self' := .rstT)
    (next := .rstB) (t := .A) (a := .T) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) rfl (by decide) bit?_bit bit_of_bit? q.reverse c (q.map Sym.bit).reverse R
    [] v (stk (((q.map Sym.bit).reverse).drop c.length ++ R)
      (((n.map Sym.bit).reverse).drop c.length ++ r) s (c.map Sym.bit).reverse
      (c.map Sym.bit).reverse w) (isBitBlock_rev q) hcq (by simp) rfl rfl
  have e₁ : S₁ = stk ((q.map Sym.bit).reverse ++ R) (((n.map Sym.bit).reverse).drop c.length ++ r)
      s [] (c.map Sym.bit).reverse w :=
    stk_ext h₁T (h₁k .B (by decide) (by decide)) (h₁k .S (by decide) (by decide)) h₁A
      (h₁k .C (by decide) (by decide)) (h₁k .V (by decide) (by decide))
  subst e₁
  obtain ⟨v₂, S₂, h₂, h₂C, h₂B, h₂k⟩ := moveB_restore (M := prog) (self' := .rstB)
    (next := .mvN) (t := .C) (a := .B) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) rfl (by decide) bit?_bit bit_of_bit? n.reverse c (n.map Sym.bit).reverse r
    [] v₁ (stk ((q.map Sym.bit).reverse ++ R) (((n.map Sym.bit).reverse).drop c.length ++ r) s
      [] (c.map Sym.bit).reverse w) (isBitBlock_rev n) hcn (by simp) rfl rfl
  have e₂ : S₂ = stk ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r) s [] [] w :=
    stk_ext (h₂k .T (by decide) (by decide)) h₂B (h₂k .S (by decide) (by decide))
      (h₂k .A (by decide) (by decide)) h₂C (h₂k .V (by decide) (by decide))
  subst e₂
  obtain ⟨v₃, S₃, h₃, h₃B, h₃S, h₃k⟩ := moveB_run (M := prog) (self := .mvN) (next := .scan)
    (a := .B) (b := .S) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) n.reverse
    (n.map Sym.bit).reverse r v₂
    (stk ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r) s [] [] w) rfl
    (isBitBlock_rev n) hr
  have e₃ : S₃ = stk ((q.map Sym.bit).reverse ++ R) r (n.map Sym.bit ++ s) [] [] w :=
    stk_ext (h₃k .T (by decide) (by decide)) h₃B (by rw [h₃S]; simp)
      (h₃k .A (by decide) (by decide)) (h₃k .C (by decide) (by decide))
      (h₃k .V (by decide) (by decide))
  subst e₃
  exact ⟨v₃, (h₁.trans (h₂.trans h₃)).of_eq (by simp only [List.length_reverse]; omega)⟩

/-- **Serving a live table entry.** Write stack contents top first, and for a list of bits $u$ let
$\overrightarrow{u}$ be its bit symbols in order and $\overleftarrow{u}$ the same symbols in
reverse order. Let $q$ and $n$ be lists of bits, $b$ and $x$ bits, $s$ a list of symbols, and $R$,
$r$ lists of symbols each empty or topped by a symbol that is not a bit. From label
$\mathsf{cmp}(b)$ with any internal state, $\overleftarrow{q}R$ on $T$, $\overleftarrow{n}r$ on
$B$, $s$ on $S$, the stacks $A$ and $C$ empty and the bit symbol of $x$ alone on $V$, the lookup
program reaches, in at most $4|n| + 5$ steps, label $\mathsf{scan}$ with some internal state,
$\overleftarrow{q}R$ on $T$, $r$ on $B$, $\overrightarrow{n}s$ on $S$, the stacks $A$ and $C$
empty and on $V$ alone the bit symbol of $b$ if $n = q$ and of $x$ otherwise. -/
theorem cmp_run (q : List Bool) (R : List Sym) (hR : EndsBitBlock Sym.bit? R) (n : List Bool)
    (b x : Bool) (r s : List Sym) (hr : EndsBitBlock Sym.bit? r) (v : Bool) :
    ∃ v', RunLe prog (4 * n.length + 5)
      ⟨some (.cmp b), v, stk ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r) s
        [] [] [Sym.bit x]⟩
      ⟨some .scan, v', stk ((q.map Sym.bit).reverse ++ R) r (n.map Sym.bit ++ s) [] []
        [Sym.bit (if n = q then b else x)]⟩ := by
  obtain ⟨c, v₁, S₁, hcq, hcn, -, h₁, h₁T, h₁B, h₁A, h₁C, h₁k⟩ := cmpB_run (M := prog)
    (a := .T) (b := .B) (ta := .A) (tb := .C) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit)
    (eb := Sym.bit) (self := .cmp b) (eqL := .put b) (neL := .rstT) rfl
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ q.reverse n.reverse
    (q.map Sym.bit).reverse R (n.map Sym.bit).reverse r v
    (stk ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r) s [] [] [Sym.bit x])
    rfl rfl (isBitBlock_rev q) (isBitBlock_rev n) hR hr
  have e₁ : S₁ = stk (((q.map Sym.bit).reverse).drop c.length ++ R)
      (((n.map Sym.bit).reverse).drop c.length ++ r) s (c.map Sym.bit).reverse
      (c.map Sym.bit).reverse [Sym.bit x] :=
    stk_ext h₁T h₁B (h₁k .S (by decide) (by decide) (by decide) (by decide))
      (by rw [h₁A]; simp) (by rw [h₁C]; simp)
      (h₁k .V (by decide) (by decide) (by decide) (by decide))
  subst e₁
  have hc : c.length ≤ n.length := by simpa using hcn.length_le
  by_cases h : n = q
  · subst h
    simp only [↓reduceIte] at h₁ ⊢
    have h₂ := put_run b ((n.map Sym.bit).reverse.drop c.length ++ R)
      ((n.map Sym.bit).reverse.drop c.length ++ r) s (c.map Sym.bit).reverse
      (c.map Sym.bit).reverse (Sym.bit x) v₁
    obtain ⟨v₃, h₃⟩ := tail_run n n c hcq hcn R r s [Sym.bit b] hr v₁
    have h₄ := h₁.trans (h₂.trans h₃)
    exact ⟨v₃, h₄.le (by omega)⟩
  · have h' : ¬ q.reverse = n.reverse := fun e => h (List.reverse_inj.1 e).symm
    simp only [h, h', ↓reduceIte] at h₁ ⊢
    obtain ⟨v₃, h₃⟩ := tail_run q n c hcq hcn R r s [Sym.bit x] hr v₁
    exact ⟨v₃, (h₁.trans h₃).le (by omega)⟩

/-- **One scan step of the lookup.** Write stack contents top first; for a list of bits $u$ let
$\overleftarrow{u}$ be its bit symbols in reverse order; for a list $E$ of table entries let
$\tau(E)$ be the symbols of its entries in reading order (each entry's name bits, then its marker)
and $\mathrm{val}_E(q)$ the value of the first live entry of $E$ named $q$, or false if there is
none. Let $q$ be a list of bits, $e = (n, m)$ a table entry, $E$ a list of entries, $eE$ the list
$E$ with $e$ prepended, and $R$, $r$ lists of symbols each empty or topped by a symbol that is not
a bit. From label $\mathsf{scan}$ with any internal state, $\overleftarrow{q}R$ on $T$, the marker
of $e$ above $\overleftarrow{n}r$ on $B$, $\tau(E)$ on $S$, the stacks $A$ and $C$ empty and the
bit symbol of $\mathrm{val}_E(q)$ alone on $V$, the lookup program reaches, in at most
$4|n| + 6$ steps, label $\mathsf{scan}$ with some internal state, $\overleftarrow{q}R$ on $T$, $r$
on $B$, $\tau(eE)$ on $S$, the stacks $A$ and $C$ empty and the bit symbol of
$\mathrm{val}_{eE}(q)$ alone on $V$. -/
theorem entry_run (q : List Bool) (R : List Sym) (hR : EndsBitBlock Sym.bit? R) (e : Ent)
    (r : List Sym) (hr : EndsBitBlock Sym.bit? r) (post : List Ent) (v : Bool) :
    ∃ v', RunLe prog (4 * e.1.length + 6)
      ⟨some .scan, v, stk ((q.map Sym.bit).reverse ++ R)
        (markOf e.2 :: ((e.1.map Sym.bit).reverse ++ r)) (post.flatMap entToks) [] []
        [Sym.bit (liveVal post q)]⟩
      ⟨some .scan, v', stk ((q.map Sym.bit).reverse ++ R) r ((e :: post).flatMap entToks) [] []
        [Sym.bit (liveVal (e :: post) q)]⟩ := by
  obtain ⟨n, m⟩ := e
  dsimp only
  have h₁ := scan_cons m ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r)
    (post.flatMap entToks) [] [] [Sym.bit (liveVal post q)] v
  rw [flatMap_cons_entToks]
  dsimp only
  cases m with
  | none =>
      obtain ⟨v₂, S₂, h₂, h₂B, h₂S, h₂k⟩ := moveB_run (M := prog) (self := .mvN)
        (next := .scan) (a := .B) (b := .S) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
        n.reverse (n.map Sym.bit).reverse r true
        (stk ((q.map Sym.bit).reverse ++ R) ((n.map Sym.bit).reverse ++ r)
          (markOf none :: post.flatMap entToks) [] [] [Sym.bit (liveVal post q)])
        rfl (isBitBlock_rev n) hr
      have e₂ : S₂ = stk ((q.map Sym.bit).reverse ++ R) r
          (n.map Sym.bit ++ markOf none :: post.flatMap entToks) [] []
          [Sym.bit (liveVal post q)] :=
        stk_ext (h₂k .T (by decide) (by decide)) h₂B (by rw [h₂S]; simp)
          (h₂k .A (by decide) (by decide)) (h₂k .C (by decide) (by decide))
          (h₂k .V (by decide) (by decide))
      subst e₂
      rw [liveVal_dead]
      exact ⟨v₂, (h₁.trans h₂).le (by simp only [List.length_reverse]; omega)⟩
  | some b =>
      obtain ⟨v₂, h₂⟩ := cmp_run q R hR n b (liveVal post q) r
        (markOf (some b) :: post.flatMap entToks) hr true
      rw [liveVal_val]
      exact ⟨v₂, ((h₁.le le_rfl).trans h₂).mono (by omega)⟩

/-! ### The two loops -/

/-- **The scan loop of the lookup machine.** Let $q$ be a list of bits, let $R$ be a list of
symbols that is empty or starts with a symbol other than a name bit, and let $pre$ and $post$ be
lists of table entries; the live value of $q$ in an entry list is the value of its first entry
named $q$ that has a value, or false if there is none. Suppose the lookup program is at label
$\mathsf{scan}$, with any internal bit, and its stacks are: $T$ holds the bits of $q$ as name
bits, last bit on top, above $R$; $B$ holds the table stack of $pre$, of length $\ell$; $S$ holds
the symbols of the entries of $post$ in reading order, first entry on top; $A$ and $C$ are empty;
and $V$ holds the single name bit carrying the live value of $q$ in $post$. Then within
$6\ell + 1$ steps the program reaches label $\mathsf{back}$, with some internal bit, where $B$ is
empty, $S$ holds the symbols of the entries of $pre$ followed by $post$ in reading order, first
entry on top, $V$ holds the single name bit carrying the live value of $q$ in $pre$ followed by
$post$, and $T$, $A$ and $C$ are unchanged. -/
theorem scan_loop (q : List Bool) (R : List Sym) (hR : EndsBitBlock Sym.bit? R)
    (pre : List Ent) :
    ∀ (post : List Ent) (v : Bool), ∃ v', RunLe prog (6 * (tblStk pre).length + 1)
      ⟨some .scan, v, stk ((q.map Sym.bit).reverse ++ R) (tblStk pre) (post.flatMap entToks) []
        [] [Sym.bit (liveVal post q)]⟩
      ⟨some .back, v', stk ((q.map Sym.bit).reverse ++ R) [] ((pre ++ post).flatMap entToks) []
        [] [Sym.bit (liveVal (pre ++ post) q)]⟩ := by
  induction pre using List.reverseRecOn with
  | nil =>
      intro post v
      exact ⟨true, (scan_nil _ _ _ _ _ v).le (by simp)⟩
  | append_singleton pre e ih =>
      intro post v
      rw [tblStk_concat, List.append_assoc, List.singleton_append]
      obtain ⟨v₁, h₁⟩ := entry_run q R hR e (tblStk pre) (ends_tblStk pre) post v
      obtain ⟨v₂, h₂⟩ := ih (e :: post) v₁
      refine ⟨v₂, (h₁.trans h₂).mono ?_⟩
      simp only [List.length_cons, List.length_append, List.length_reverse, List.length_map]
      omega

/-- **The return loop of the lookup machine.** Let $t$ and $w$ be lists of symbols, let $pre$ and
$post$ be lists of table entries, and let $m$ be the total number of symbols of the entries of
$post$. Suppose the lookup program is at label $\mathsf{back}$, with any internal bit, and its
stacks are: $T$ holds $t$; $B$ holds the table stack of $pre$; $S$ holds the symbols of the
entries of $post$ in reading order, first entry on top; $A$ and $C$ are empty; and $V$ holds $w$.
Then within $2m + 2$ steps the program reaches label $\mathsf{done}$, with some internal bit,
where $B$ holds the table stack of the entry list $pre$ followed by $post$, the stacks $S$, $A$
and $C$ are empty, and $T$ and $V$ still hold $t$ and $w$. -/
theorem back_loop (T w : List Sym) (post : List Ent) :
    ∀ (pre : List Ent) (v : Bool), ∃ v', RunLe prog (2 * (post.flatMap entToks).length + 2)
      ⟨some .back, v, stk T (tblStk pre) (post.flatMap entToks) [] [] w⟩
      ⟨some .done, v', stk T (tblStk (pre ++ post)) [] [] [] w⟩ := by
  induction post with
  | nil =>
      intro pre v
      rw [List.append_nil]
      obtain ⟨v₁, S₁, h₁, h₁S, h₁B, h₁k⟩ := moveB_run (M := prog) (self := .back)
        (next := .mark) (a := .S) (b := .B) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) []
        [] [] v (stk T (tblStk pre) [] [] [] w) rfl rfl rfl
      have e₁ : S₁ = stk T (tblStk pre) [] [] [] w :=
        stk_ext (h₁k .T (by decide) (by decide)) (by rw [h₁B]; rfl) h₁S
          (h₁k .A (by decide) (by decide)) (h₁k .C (by decide) (by decide))
          (h₁k .V (by decide) (by decide))
      subst e₁
      exact ⟨true, (h₁.trans (mark_nil T (tblStk pre) [] [] w v₁)).le (by simp)⟩
  | cons e post ih =>
      intro pre v
      obtain ⟨n, m⟩ := e
      rw [flatMap_cons_entToks]
      dsimp only
      obtain ⟨v₁, S₁, h₁, h₁S, h₁B, h₁k⟩ := moveB_run (M := prog) (self := .back)
        (next := .mark) (a := .S) (b := .B) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) n
        (n.map Sym.bit) (markOf m :: post.flatMap entToks) v
        (stk T (tblStk pre) (n.map Sym.bit ++ markOf m :: post.flatMap entToks) [] [] w) rfl
        (isBitBlock_map n) (ends_markOf m _)
      have e₁ : S₁ = stk T ((n.map Sym.bit).reverse ++ tblStk pre)
          (markOf m :: post.flatMap entToks) [] [] w :=
        stk_ext (h₁k .T (by decide) (by decide)) h₁B h₁S (h₁k .A (by decide) (by decide))
          (h₁k .C (by decide) (by decide)) (h₁k .V (by decide) (by decide))
      subst e₁
      have h₂ := mark_cons m T ((n.map Sym.bit).reverse ++ tblStk pre) (post.flatMap entToks)
        [] [] w v₁
      rw [show markOf m :: ((n.map Sym.bit).reverse ++ tblStk pre) = tblStk (pre ++ [(n, m)])
        from (tblStk_concat pre (n, m)).symm] at h₂
      obtain ⟨v₃, h₃⟩ := ih (pre ++ [(n, m)]) true
      rw [List.append_assoc, List.singleton_append] at h₃
      refine ⟨v₃, ((h₁.trans h₂).le le_rfl).trans h₃ |>.mono ?_⟩
      simp only [List.length_append, List.length_map, List.length_cons]
      omega

/-! ### The lookup machine -/

/-- **Correctness of the SAT-verifier lookup machine.** Let $q$ be a list of bits, $es$ a list of
table entries and $R$ a list of symbols that is empty or starts with a symbol other than a name
bit. Suppose the stacks of the lookup machine are as follows: $T$ holds the bits of $q$ as name
bits, last bit on top, above $R$; $B$ holds the table stack of $es$, of length $\ell$; and $S$,
$A$, $C$ and $V$ are empty. Then the lookup program, started at its start label with any
internal bit, reaches the label $\mathsf{done}$ within $8\ell + 4$ steps, with some internal bit;
there $V$ holds the single name bit carrying the live value of $q$ in $es$ (the value of the
first entry of $es$ named $q$ that has a value, or false if there is none), and every other
stack is as it started. -/
theorem run (q : List Bool) (es : List Ent) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (v : Bool) (St : ∀ _ : K, List Sym) (hT : St .T = (q.map Sym.bit).reverse ++ R)
    (hB : St .B = tblStk es) (hS : St .S = []) (hA : St .A = []) (hC : St .C = [])
    (hV : St .V = []) :
    ∃ v', RunLe prog (8 * (tblStk es).length + 4) ⟨some start, v, St⟩
      ⟨some .done, v', update St .V [Sym.bit (liveVal es q)]⟩ := by
  obtain rfl := stk_ext hT hB hS hA hC hV
  rw [upd_V]
  have h₁ := init_run ((q.map Sym.bit).reverse ++ R) (tblStk es) v
  obtain ⟨v₂, h₂⟩ := scan_loop q R hR es [] v
  obtain ⟨v₃, h₃⟩ := back_loop ((q.map Sym.bit).reverse ++ R) [Sym.bit (liveVal es q)] es [] v₂
  rw [List.append_nil] at h₂
  refine ⟨v₃, ((h₁.le le_rfl).trans (h₂.trans h₃)).mono ?_⟩
  have : (es.flatMap entToks).length = (tblStk es).length := by simp [tblStk]
  omega

end Cslib.Complexity.SatVerifier.Lookup
