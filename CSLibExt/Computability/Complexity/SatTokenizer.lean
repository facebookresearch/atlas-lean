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
# The SAT verifier's tokenizer as a `TM2` machine

Component 1 of the `TM2` SAT verifier (`SatVerifierSpec`). From the formula bits `x` on stack `X`
and the witness bits `w` on stack `W`, the machine `prog` decodes `x` as `decodeCNF` does, pushes
the token stack `(toks φ).reverse` on `T` and the table stack `tblStk (ents φ w)` on `B`, and
consumes one witness bit per literal occurrence. It reaches `acc` on a valid encoding
(`run_some`) and `rej` otherwise (`run_none`), within `2 |x| + 2` steps.

The unary counts go to the counters `CC` (clauses left) and `LC` (literals left in the current
clause). A name block is read a pair at a time; the label remembers the last name bit, so a
non-canonical name (non-empty and ending in `false`, `encodeNat_decodeNat_eq_iff`) is rejected
when its block closes.
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier.Tokenizer

open Turing MetaMathlibExt TM2Program Function Cslib.CookLevin Cslib.Logic.PL Computability
open MetaMathlibExt.BitstringEncoding

/-- **Stacks of the SAT tokenizer.** The SAT tokenizer has six stacks: $X$ for the formula bits,
$W$ for the witness bits, $T$ for the token output, $B$ for the table output, and the clause
counter $\mathsf{CC}$ and the literal counter $\mathsf{LC}$. -/
inductive K | X | W | T | B | CC | LC
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.X, .W, .T, .B, .CC, .LC], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Labels of the SAT tokenizer.** The labels of the SAT tokenizer are: $\mathsf{un}(c)$ for a
bit $c$, which reads a unary count onto the clause counter $\mathsf{CC}$ if $c$ is true and onto
the literal counter $\mathsf{LC}$ otherwise; $\mathsf{cls}$, which starts a clause;
$\mathsf{lits}$, which starts a literal; $\mathsf{nm}(\ell)$, where $\ell$ is a bit or none,
which reads the bit pairs of a name block, $\ell$ being the last name bit read (none before the
first one); $\mathsf{pol}$, which reads the polarity and the next witness bit; $\mathsf{fin}$,
which checks that the formula stack $X$ is used up; and the halting labels $\mathsf{acc}$ and
$\mathsf{rej}$. -/
inductive Lab
  | un (c : Bool)
  | cls
  | lits
  | nm (last : Option Bool)
  | pol
  | fin
  | acc
  | rej
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.un false, .un true, .cls, .lits, .nm none, .nm (some false), .nm (some true),
    .pol, .fin, .acc, .rej], by decide⟩
  complete := fun l => by
    cases l with
    | un c => cases c <;> decide
    | nm o =>
        cases o with
        | none => decide
        | some b => cases b <;> decide
    | _ => decide

/-- **Testing whether the top symbol is a given bit.** For a bit $b$ and the result of peeking at
a stack (a symbol, or nothing when the stack is empty), this is true exactly when the peeked
symbol is the bit symbol carrying $b$; it is false for an empty stack and for every other
symbol. -/
def topIsBit (b : Bool) : Option Sym → Bool
  | some (.bit c) => c == b
  | _ => false

open TM2.Stmt in
/-- **Instruction for reading a unary count.** For a stack $k$ of the tokenizer and labels $s$ and
$t$, this is the tokenizer instruction that looks at the top of the formula stack $X$. If it is
the bit true, the instruction pops it, pushes the clause-end symbol $\mathsf{cl}$ onto $k$ and
goes to $s$; if it is the bit false, it pops it and goes to $t$; otherwise, when $X$ is empty or
its top is not a bit, it goes to $\mathsf{rej}$. The internal bit is set to true in the first two
cases and to false in the last.

When $k$ is not $X$ and the instruction is placed at label $s$, a run on a formula stack that
starts with $m$ bits true followed by a bit false pops these $m + 1$ bits, pushes $m$ copies
of $\mathsf{cl}$ onto $k$ and goes to $t$. -/
def unary (k : K) (self next : Lab) : TM2.Stmt (fun _ : K => Sym) Lab Bool :=
  peek .X (fun _ o => topIsBit true o) <| branch id
    (pop .X (fun s _ => s) <| push k (fun _ => .cl) <| goto fun _ => self)
    (peek .X (fun _ o => topIsBit false o) <| branch id
      (pop .X (fun s _ => s) <| goto fun _ => next)
      (goto fun _ => .rej))

open TM2.Stmt in
/-- **The tokenizer program.** The tokenizer is a multi-stack machine with stacks $X$ (formula
bits), $W$ (witness bits), $T$ (tokens), $B$ (table) and the unary counters $CC$, $LC$ (over the
unit symbol $\mathsf{cl}$), and one bit of internal state. Its instruction at each label is:

- $\mathsf{un}(\mathrm{true})$, $\mathsf{un}(\mathrm{false})$: read a unary count from $X$ onto
  $CC$ and $LC$ respectively. If the top of $X$ is the bit true, pop it, push $\mathsf{cl}$ onto
  the counter and stay; if it is the bit false, pop it and go to $\mathsf{cls}$ (from
  $\mathsf{un}(\mathrm{true})$) or $\mathsf{lits}$ (from $\mathsf{un}(\mathrm{false})$); otherwise
  go to $\mathsf{rej}$.
- $\mathsf{cls}$: pop $CC$; if it was non-empty go to $\mathsf{un}(\mathrm{false})$, else go to
  $\mathsf{fin}$.
- $\mathsf{lits}$: pop $LC$; if it was non-empty go to $\mathsf{nm}(\mathrm{none})$, else push
  $\mathsf{cl}$ onto $T$ and go to $\mathsf{cls}$.
- $\mathsf{nm}(\ell)$, where $\ell$ is an optional bit: if the top of $X$ is the bit true, pop it;
  then if the top of $X$ is a bit $s$, pop it, push the name bit $s$ onto $T$ and onto $B$ and go to
  $\mathsf{nm}(s)$, and otherwise go to $\mathsf{rej}$. If instead the top of $X$ is the bit false,
  pop it and go to $\mathsf{rej}$ if $\ell$ is the bit false and to $\mathsf{pol}$ otherwise. In
  any other case go to $\mathsf{rej}$.
- $\mathsf{pol}$: if the top of $X$ is a bit $p$, pop it and push $\mathsf{lit}(p)$ onto $T$; then
  if $W$ is non-empty, pop its top symbol, read as a bit $s$ (false if it is not a bit), and push
  $\mathsf{val}(s)$ onto $B$, and otherwise push $\mathsf{dead}$ onto $B$; go to $\mathsf{lits}$.
  If the top of $X$ is not a bit, go to $\mathsf{rej}$.
- $\mathsf{fin}$: go to $\mathsf{rej}$ if $X$ is non-empty and to $\mathsf{acc}$ if it is empty.
- $\mathsf{acc}$, $\mathsf{rej}$: halt.

Each test stores its outcome in the internal bit: whether the top of $X$ or $W$ has the stated
form, or, for the pop of $CC$ or $LC$, whether that counter was non-empty. Popping a name bit $s$
in $\mathsf{nm}(\ell)$, the polarity $p$ in $\mathsf{pol}$ or a witness symbol in $\mathsf{pol}$
stores the bit read ($s$, $p$ or the witness bit $s$); the remaining pops and all pushes leave the
internal bit unchanged. So after popping a bit of a unary count, or the closing bit false of a name
block, the internal bit is true. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .un true => unary .CC (.un true) .cls
  | .un false => unary .LC (.un false) .lits
  | .cls => pop .CC (fun _ o => o.isSome) <| branch id (goto fun _ => .un false)
      (goto fun _ => .fin)
  | .lits => pop .LC (fun _ o => o.isSome) <| branch id (goto fun _ => .nm none)
      (push .T (fun _ => .cl) <| goto fun _ => .cls)
  | .nm last => peek .X (fun _ o => topIsBit true o) <| branch id
      (pop .X (fun s _ => s) <| peek .X (fun _ o => isBit Sym.bit? o) <| branch id
        (pop .X (fun _ o => bitOf Sym.bit? o) <| push .T (fun s => .bit s) <|
          push .B (fun s => .bit s) <|
          goto fun s => .nm (some s))
        (goto fun _ => .rej))
      (peek .X (fun _ o => topIsBit false o) <| branch id
        (pop .X (fun s _ => s) <| goto fun _ => if last = some false then .rej else .pol)
        (goto fun _ => .rej))
  | .pol => peek .X (fun _ o => isBit Sym.bit? o) <| branch id
      (pop .X (fun _ o => bitOf Sym.bit? o) <| push .T (fun s => .lit s) <|
        peek .W (fun _ o => o.isSome) <| branch id
          (pop .W (fun _ o => bitOf Sym.bit? o) <| push .B (fun s => .val s) <| goto fun _ => .lits)
          (push .B (fun _ => .dead) <| goto fun _ => .lits))
      (goto fun _ => .rej)
  | .fin => peek .X (fun _ o => o.isSome) <| branch id (goto fun _ => .rej) (goto fun _ => .acc)
  | .acc => halt
  | .rej => halt

/-- **Start label of the SAT tokenizer.** The tokenizer starts at the label $\mathrm{un}(1)$,
which reads a unary count from the input stack $X$ onto the clause counter $CC$. -/
def start : Lab := .un true

/-! ### Stacks -/

/-- **Tokenizer stack contents.** For symbol lists $x, w, t, b$ and natural numbers $c, \ell$, this
assigns to the tokenizer's stacks $X$, $W$, $T$, $B$ the lists $x$, $w$, $t$, $b$, and to the
counter stacks $CC$ and $LC$ the lists of $c$ and $\ell$ copies of the clause-end symbol
$\mathrm{cl}$ (the counters in unary). -/
def st (x w t b : List Sym) (cc lc : ℕ) : K → List Sym
  | .X => x
  | .W => w
  | .T => t
  | .B => b
  | .CC => List.replicate cc .cl
  | .LC => List.replicate lc .cl

section Upd

variable (x w t b l : List Sym) (cc lc j : ℕ)

@[simp] theorem upd_X : update (st x w t b cc lc) .X l = st l w t b cc lc := by
  funext s; cases s <;> rfl
@[simp] theorem upd_W : update (st x w t b cc lc) .W l = st x l t b cc lc := by
  funext s; cases s <;> rfl
@[simp] theorem upd_T : update (st x w t b cc lc) .T l = st x w l b cc lc := by
  funext s; cases s <;> rfl
@[simp] theorem upd_B : update (st x w t b cc lc) .B l = st x w t l cc lc := by
  funext s; cases s <;> rfl
@[simp] theorem upd_CC : update (st x w t b cc lc) .CC (List.replicate j .cl) =
    st x w t b j lc := by funext s; cases s <;> rfl
@[simp] theorem upd_LC : update (st x w t b cc lc) .LC (List.replicate j .cl) =
    st x w t b cc j := by funext s; cases s <;> rfl
@[simp] theorem upd_CC' : update (st x w t b cc lc) .CC (.cl :: List.replicate j .cl) =
    st x w t b (j + 1) lc := by funext s; cases s <;> rfl
@[simp] theorem upd_LC' : update (st x w t b cc lc) .LC (.cl :: List.replicate j .cl) =
    st x w t b cc (j + 1) := by funext s; cases s <;> rfl
@[simp] theorem upd_CC0 : update (st x w t b cc lc) .CC [] = st x w t b 0 lc := by
  funext s; cases s <;> rfl
@[simp] theorem upd_LC0 : update (st x w t b cc lc) .LC [] = st x w t b cc 0 := by
  funext s; cases s <;> rfl

@[simp] theorem st_X : st x w t b cc lc .X = x := rfl
@[simp] theorem st_W : st x w t b cc lc .W = w := rfl
@[simp] theorem st_T : st x w t b cc lc .T = t := rfl
@[simp] theorem st_B : st x w t b cc lc .B = b := rfl
@[simp] theorem st_CC : st x w t b cc lc .CC = List.replicate cc .cl := rfl
@[simp] theorem st_LC : st x w t b cc lc .LC = List.replicate lc .cl := rfl

end Upd

/-- **Rejection of the SAT tokenizer within a step bound.** For a natural number $n$ and a
configuration $c$ of the tokenizer, the tokenizer rejects from $c$ within $n$ steps when there are
an internal bit $v$ and stacks $S$ such that it runs in at most $n$ steps from $c$ to the
configuration with label $\mathsf{rej}$, internal bit $v$ and stacks $S$. -/
def Rej (n : ℕ) (c : TM2.Cfg (fun _ : K => Sym) Lab Bool) : Prop :=
  ∃ v S, RunLe prog n c ⟨some .rej, v, S⟩

theorem Rej.mono {n m : ℕ} {c : TM2.Cfg (fun _ : K => Sym) Lab Bool} (h : Rej n c)
    (hnm : n ≤ m) : Rej m c :=
  let ⟨v, S, h⟩ := h; ⟨v, S, h.mono hnm⟩

theorem Rej.head {k n : ℕ} {c d : TM2.Cfg (fun _ : K => Sym) Lab Bool} (h₁ : Run prog k c d)
    (h₂ : Rej n d) : Rej (k + n) c :=
  let ⟨v, S, h⟩ := h₂; ⟨v, S, (h₁.le le_rfl).trans h⟩

theorem Rej.headLe {k n : ℕ} {c d : TM2.Cfg (fun _ : K => Sym) Lab Bool}
    (h₁ : RunLe prog k c d) (h₂ : Rej n d) : Rej (k + n) c :=
  let ⟨v, S, h⟩ := h₂; ⟨v, S, h₁.trans h⟩

/-- **One step to rejection.** Let $\ell$ be a label, $v$ a bit and $S$ an assignment of symbol
stacks to the tokenizer's stacks. If executing the tokenizer's instruction at $\ell$ from internal
bit $v$ and stacks $S$ yields a configuration with label $\mathsf{rej}$, then the tokenizer
reaches $\mathsf{rej}$ within one step from the configuration with label $\ell$, internal bit $v$
and stacks $S$. -/
theorem rej_one {l : Lab} {v : Bool} {S : K → List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some .rej) : Rej 1 ⟨some l, v, S⟩ := by
  rcases hs : TM2.stepAux (prog l) v S with ⟨l', v', S'⟩
  rw [hs] at h
  cases h
  exact ⟨v', S', (Run.single hs).le le_rfl⟩

/-! ### Unary counts -/

/-- **Reading a unary count.** Let $c$ be a bit, $n$ a natural number, $r$ a bit string, $w, t, b$
symbol lists and $m, \ell$ counter values. Started at the label $\mathrm{un}(c)$ with any value
of its Boolean variable, with $X$ holding the bits of $1^n 0 r$, with $W$, $T$, $B$ holding $w$,
$t$, $b$, and with the counters $CC$ and $LC$ holding $m$ and $\ell$ in unary, the tokenizer
takes exactly $n + 1$ steps to reach the configuration whose label is $\mathrm{cls}$ if $c = 1$
and $\mathrm{lits}$ if $c = 0$, whose Boolean variable is $1$, whose stack $X$ holds the bits of
$r$, whose stacks $W$, $T$, $B$ still hold $w$, $t$, $b$, and whose counters hold $m + n$ and
$\ell$ if $c = 1$, and $m$ and $\ell + n$ if $c = 0$. -/
theorem un_run (c : Bool) (rest : List Bool) (w t b : List Sym) : ∀ (n cc lc : ℕ) (v : Bool),
    Run prog (n + 1)
      ⟨some (.un c), v, st ((List.replicate n true ++ false :: rest).map .bit) w t b cc lc⟩
      ⟨some (if c then .cls else .lits), true,
        st (rest.map .bit) w t b (if c then cc + n else cc) (if c then lc else lc + n)⟩ := by
  intro n
  induction n with
  | zero =>
      intro cc lc v
      cases c <;> exact Run.single (by simp [prog, unary, TM2.stepAux, topIsBit])
  | succ n ih =>
      intro cc lc v
      cases c with
      | false =>
          have h := ih cc (lc + 1) true
          rw [show lc + 1 + n = lc + (n + 1) by omega] at h
          exact Run.head
            (by simp [TM2.step, prog, unary, TM2.stepAux, topIsBit, List.replicate_succ]) h
      | true =>
          have h := ih (cc + 1) lc true
          rw [show cc + 1 + n = cc + (n + 1) by omega] at h
          exact Run.head
            (by simp [TM2.step, prog, unary, TM2.stepAux, topIsBit, List.replicate_succ]) h

/-- **An unterminated unary count is rejected.** Let $r$ be a bit string on which reading a unary
length prefix fails. For every bit $c$, symbol lists $w, t, b$, counter values $m, \ell$ and
value of the Boolean variable, the tokenizer started at the label $\mathrm{un}(c)$ with $X$
holding the bits of $r$, with $W$, $T$, $B$ holding $w$, $t$, $b$, and with the counters $CC$
and $LC$ holding $m$ and $\ell$ in unary reaches the rejecting label within $|r| + 1$ steps. -/
theorem un_fail (c : Bool) (w t b : List Sym) : ∀ (r : List Bool), readUnaryLength r = none →
    ∀ (cc lc : ℕ) (v : Bool), Rej (r.length + 1) ⟨some (.un c), v, st (r.map .bit) w t b cc lc⟩
  | [], _, cc, lc, v => rej_one (by cases c <;> simp [prog, unary, TM2.stepAux, topIsBit])
  | false :: r, h, _, _, _ => by simp [readUnaryLength] at h
  | true :: r, h, cc, lc, v => by
      have hr : readUnaryLength r = none := by simpa [readUnaryLength] using h
      cases c with
      | false =>
          have ih := un_fail false w t b r hr cc (lc + 1) true
          refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
          simp [prog, unary, TM2.stepAux, topIsBit]
      | true =>
          have ih := un_fail true w t b r hr (cc + 1) lc true
          refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
          simp [prog, unary, TM2.stepAux, topIsBit]

/-! ### Names -/

/-- **Name-loop outcome.** For an optional bit $\ell$ and a bit string $u$, the name-loop outcome
is the tokenizer label defined by recursion on $u$: for empty $u$ it is $\mathsf{rej}$ if $\ell$ is
the bit false and $\mathsf{pol}$ otherwise, and for $u = c\,u'$ it is the outcome for the bit $c$
and the string $u'$. So it is $\mathsf{rej}$ exactly when the string formed by $\ell$ (if present)
followed by $u$ is non-empty and ends in false, and $\mathsf{pol}$ otherwise. -/
def nmEnd : Option Bool → List Bool → Lab
  | last, [] => if last = some false then .rej else .pol
  | _, c :: bits => nmEnd (some c) bits

theorem nmEnd_some (c : Bool) :
    ∀ bits : List Bool, nmEnd (some c) bits = if bits.getLast?.getD c then .pol else .rej
  | [] => by cases c <;> rfl
  | d :: bits => by rw [nmEnd, nmEnd_some d bits, List.getLast?_cons, Option.getD_some]

/-- **Name-loop outcome from the start of a name.** For every bit string $u$, the name-loop
outcome with no previous bit after $u$ is the label $\mathsf{pol}$ if $u$ is a canonical name,
that is, encoding the natural number that $u$ decodes to gives back $u$, and the label
$\mathsf{rej}$ otherwise. -/
theorem nmEnd_none (bits : List Bool) :
    nmEnd none bits = if encodeNat (decodeNat bits) = bits then .pol else .rej := by
  simp only [encodeNat_decodeNat_eq_iff]
  cases bits with
  | nil => simp [nmEnd]
  | cons c bits => simp [nmEnd, nmEnd_some, List.getLast?_cons]

/-- **Reading a name block.** Let $u$ and $r$ be bit strings, $\ell$ an optional bit, $v$ a bit,
$w$, $t$, $b$ symbol stacks and $c$, $l$ natural numbers. Started at label $\mathsf{nm}(\ell)$ with
internal bit $v$, the bits of the self-delimiting block of $u$ followed by $r$ on the formula stack
$X$, $w$ on the witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack $B$, clause
counter $c$ and literal counter $l$, the tokenizer runs in exactly $|u| + 1$ steps to the
configuration whose label is the name-loop outcome for $\ell$ and $u$, with internal bit true, the
bits of $r$ on $X$, $w$ on $W$, the bits of $u$ in reverse order (last bit on top) above $t$ on $T$
and above $b$ on $B$, and the same counters. -/
theorem nm_run (rest : List Bool) (w : List Sym) (cc lc : ℕ) :
    ∀ (bits : List Bool) (last : Option Bool) (t b : List Sym) (v : Bool),
    Run prog (bits.length + 1)
      ⟨some (.nm last), v, st ((delimit bits ++ rest).map .bit) w t b cc lc⟩
      ⟨some (nmEnd last bits), true, st (rest.map .bit) w ((bits.map .bit).reverse ++ t)
        ((bits.map .bit).reverse ++ b) cc lc⟩
  | [], last, t, b, v => Run.single (by simp [prog, TM2.stepAux, topIsBit, delimit, nmEnd])
  | c :: bits, last, t, b, v => by
      have h := nm_run rest w cc lc bits (some c) (.bit c :: t) (.bit c :: b) c
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, nmEnd]
      exact Run.head
        (by simp [TM2.step, prog, TM2.stepAux, topIsBit, isBit, Sym.bit?, bitOf, delimit]) h

/-- **Rejecting an unterminated name block.** Let $r$ be a bit string from whose front no
self-delimiting block can be parsed. For every optional last bit $\ell$, internal bit $v$, symbol
stacks $w$, $t$, $b$ and natural numbers $c$, $l$, the tokenizer started at label
$\mathsf{nm}(\ell)$ with internal bit $v$, the bits of $r$ on the formula stack $X$, $w$ on the
witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack $B$, clause counter $c$ and
literal counter $l$ reaches the label $\mathsf{rej}$ within $|r| + 1$ steps. -/
theorem nm_fail (w : List Sym) (cc lc : ℕ) : ∀ (r : List Bool), undelimit r = none →
    ∀ (last : Option Bool) (t b : List Sym) (v : Bool),
    Rej (r.length + 1) ⟨some (.nm last), v, st (r.map .bit) w t b cc lc⟩
  | [], _, last, t, b, v => rej_one (by simp [prog, TM2.stepAux, topIsBit])
  | false :: r, h, _, _, _, _ => by simp [undelimit] at h
  | [true], _, last, t, b, v => by
      refine Rej.mono (n := 1) (rej_one ?_) (by simp)
      simp [prog, TM2.stepAux, topIsBit, isBit, Sym.bit?]
  | true :: c :: r, h, last, t, b, v => by
      have hr : undelimit r = none := by simpa [undelimit] using h
      have ih := nm_fail w cc lc r hr (some c) (.bit c :: t) (.bit c :: b) c
      refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
      simp [prog, TM2.stepAux, topIsBit, isBit, Sym.bit?, bitOf]

/-! ### Literals -/

/-- **Reading a polarity.** Let $p$, $v$ be bits, $r$, $w$ bit strings, $t$, $b$ symbol stacks and
$c$, $l$ natural numbers. Started at label $\mathsf{pol}$ with internal bit $v$, the bit $p$
followed by the bits of $r$ on the formula stack $X$, the bits of $w$ on the witness stack $W$, $t$
on the token stack $T$, $b$ on the table stack $B$, clause counter $c$ and literal counter $l$, the
tokenizer moves in exactly one step to label $\mathsf{lits}$ with the bits of $r$ on $X$, the bits
of $w$ after its first on $W$, the polarity marker $\mathsf{lit}(p)$ pushed onto $t$, and the same
counters. If $w$ starts with the bit $w_1$, the internal bit becomes $w_1$ and the marker
$\mathsf{val}(w_1)$ is pushed onto $b$; if $w$ is empty, the internal bit becomes false and the
marker $\mathsf{dead}$ is pushed onto $b$. -/
theorem pol_run (p : Bool) (rest w : List Bool) (t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Run prog 1 ⟨some .pol, v, st ((p :: rest).map .bit) (w.map .bit) t b cc lc⟩
      ⟨some .lits, w.head?.getD false, st (rest.map .bit) (w.tail.map .bit) (.lit p :: t)
        (markOf w.head? :: b) cc lc⟩ := by
  cases w <;> exact Run.single (by simp [prog, TM2.stepAux, isBit, Sym.bit?, bitOf, markOf])

theorem pol_rej (w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Rej 1 ⟨some .pol, v, st [] w t b cc lc⟩ :=
  rej_one (by simp [prog, TM2.stepAux, isBit, Sym.bit?])

/-- **Tokenizer run on one literal.** A configuration $\langle \ell, v \mid x, w, t, b, i, j\rangle$
of the SAT tokenizer has label $\ell$, internal bit $v$, stacks $X$, $W$, $T$, $B$ holding $x$,
$w$, $t$, $b$ (top first; a bit string stands for its list of bit symbols), and $i$ and $j$ marks
on the clause and literal counters; $\mathbin{+\!\!+}$ is concatenation. Let
$n, i, j \in \mathbb{N}$, let $p$ and $v$ be bits, $r$ and $w$ bit strings and $t$ and $b$ symbol
lists. Let $q$ be the binary code of $n$ (Mathlib's canonical bits of $n$, least significant first,
empty for $0$), $E$ the encoding of the literal $(n, p)$, $o$ the first bit of $w$ (none if $w$ is
empty), $o'$ that bit with default false, and $w'$ the string $w$ with its first bit, if any,
removed. Then the tokenizer goes in exactly $|q| + 2$ steps from
$\langle \mathsf{nm}(\mathrm{none}), v \mid E \mathbin{+\!\!+} r, w, t, b, i, j\rangle$ to
$\langle \mathsf{lits}, o' \mid r, w', \mathrm{rev}(\lambda) \mathbin{+\!\!+} t,
\mathrm{rev}(\eta) \mathbin{+\!\!+} b, i, j\rangle$, where $\lambda$ is the token list of the
literal $(n, p)$ (the bits of $q$, then the polarity marker of $p$) and $\eta$ is the symbol list
of the table entry $(q, o)$ (the bits of $q$, then the value marker of $o$, which is dead if $o$
is none). -/
theorem lit_run (n : ℕ) (p : Bool) (rest w : List Bool) (t b : List Sym) (cc lc : ℕ)
    (v : Bool) :
    Run prog ((encodeNat n).length + 2)
      ⟨some (.nm none), v, st ((encodeLit (n, p) ++ rest).map .bit) (w.map .bit) t b cc lc⟩
      ⟨some .lits, w.head?.getD false, st (rest.map .bit) (w.tail.map .bit)
        ((litToks (n, p)).reverse ++ t) ((entToks (encodeNat n, w.head?)).reverse ++ b)
        cc lc⟩ := by
  have h1 := nm_run (p :: rest) (w.map .bit) cc lc (encodeNat n) none t b v
  rw [nmEnd_none, decode_encodeNat, ite_eq_left rfl] at h1
  have h2 := pol_run p rest w (((encodeNat n).map .bit).reverse ++ t)
    (((encodeNat n).map .bit).reverse ++ b) cc lc true
  have e : encodeLit (n, p) ++ rest = delimit (encodeNat n) ++ p :: rest := by
    simp [encodeLit, encodeNatPrefix]
  rw [e]
  simpa [litToks, entToks] using h1.trans h2

/-- **Tokenizer rejects an undecodable literal.** A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let $r$ be a bit
string from whose front no literal can be decoded (a literal being a self-delimited canonical
variable code followed by a polarity bit), let $w$, $t$, $b$ be symbol lists,
$i, j \in \mathbb{N}$ and $v$ a bit. Then from
$\langle \mathsf{nm}(\mathrm{none}), v \mid r, w, t, b, i, j\rangle$ the tokenizer reaches the
label $\mathsf{rej}$ within $|r| + 2$ steps. -/
theorem lit_fail (r : List Bool) (hr : decodeLit r = none) (w t b : List Sym) (cc lc : ℕ)
    (v : Bool) : Rej (r.length + 2) ⟨some (.nm none), v, st (r.map .bit) w t b cc lc⟩ := by
  cases hu : undelimit r with
  | none => exact (nm_fail w cc lc r hu none t b v).mono (by omega)
  | some pr =>
      obtain ⟨bits, r'⟩ := pr
      obtain rfl := (undelimit_eq_some_iff r bits r').1 hu
      have h1 := nm_run r' w cc lc bits none t b v
      rw [nmEnd_none] at h1
      by_cases hc : encodeNat (decodeNat bits) = bits
      · rw [ite_eq_left hc] at h1
        cases r' with
        | nil => exact (Rej.head h1 (pol_rej _ _ _ cc lc true)).mono (by simp; omega)
        | cons p r'' => simp [decodeLit, decodeNatPrefix, hc] at hr
      · rw [ite_eq_right hc] at h1
        exact ⟨_, _, h1.le (by simp; omega)⟩

/-! ### Clauses -/

/-- **Occurrence table of a nonempty list.** Let $n$ be a natural number, $L$ a list of natural
numbers and $w$ a list of bits. The occurrence table of the list $n$ followed by $L$, with $w$, is
the entry whose name is the binary code of $n$ and whose value is the first bit of $w$ (no value
if $w$ is empty), followed by the occurrence table of $L$ with $w$ minus its first bit (with the
empty list if $w$ is empty). -/
theorem entsOf_cons (n : ℕ) (ns : List ℕ) (w : List Bool) :
    entsOf (n :: ns) w = (encodeNat n, w.head?) :: entsOf ns w.tail := by
  cases w <;> rfl

theorem entsOf_append (ns ms : List ℕ) :
    ∀ w : List Bool, entsOf (ns ++ ms) w = entsOf ns w ++ entsOf ms (w.drop ns.length) := by
  induction ns with
  | nil => intro w; rfl
  | cons n ns ih => intro w; simp [entsOf_cons, ih, List.drop_tail]

theorem tblStk_cons (e : Ent) (es : List Ent) :
    tblStk (e :: es) = tblStk es ++ (entToks e).reverse := by
  simp [tblStk]

theorem tblStk_append (es fs : List Ent) : tblStk (es ++ fs) = tblStk fs ++ tblStk es := by
  simp [tblStk]

/-- **Reading the literals of a clause.** Let $C$ be a clause with literals
$(n_1, p_1), \dots, (n_k, p_k)$, let $u$ be the concatenation of their literal codes, and let $r$,
$w$ be bit strings, $t$, $b$ stacks of symbols, $c$ a natural number and $v$ a bit. Started at
label $\mathsf{lits}$ with internal bit $v$, the bits of $u$ followed by $r$ on the formula stack
$X$, the bits of $w$ on the witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack
$B$, clause counter $c$ and literal counter $k$, the tokenizer reaches within $2|u| + 1$ steps the
configuration with label $\mathsf{cls}$, internal bit false, the bits of $r$ on $X$, the bits of
$w$ with its first $k$ bits removed on $W$, the tokens of $C$ in reverse order (its final
$\mathsf{cl}$ on top) above $t$ on $T$, the table stack of the entries $e_1, \dots, e_k$ above $b$
on $B$, clause counter $c$ and literal counter $0$. Here $e_i$ pairs the binary name of $n_i$ with
the $i$-th bit of $w$, or with no value when $w$ has fewer than $i$ bits. -/
theorem lits_run (rest : List Bool) (cc : ℕ) :
    ∀ (C : CNFClause) (w : List Bool) (t b : List Sym) (v : Bool),
    RunLe prog (2 * (C.flatMap encodeLit).length + 1)
      ⟨some .lits, v, st ((C.flatMap encodeLit ++ rest).map .bit) (w.map .bit) t b cc C.length⟩
      ⟨some .cls, false, st (rest.map .bit) ((w.drop C.length).map .bit)
        ((clauseToks C).reverse ++ t) (tblStk (entsOf (C.map Prod.fst) w) ++ b) cc 0⟩
  | [], w, t, b, v =>
      (Run.single (by simp [prog, TM2.stepAux, clauseToks, tblStk, entsOf])).le (by simp)
  | (n, p) :: C, w, t, b, v => by
      have h0 : Run prog 1
          ⟨some .lits, v, st ((((n, p) :: C).flatMap encodeLit ++ rest).map .bit) (w.map .bit) t b
            cc (C.length + 1)⟩
          ⟨some (.nm none), true, st ((encodeLit (n, p) ++ (C.flatMap encodeLit ++ rest)).map .bit)
            (w.map .bit) t b cc C.length⟩ :=
        Run.single (by simp [prog, TM2.stepAux, List.replicate_succ])
      have h1 := lit_run n p (C.flatMap encodeLit ++ rest) w t b cc C.length true
      have h2 := lits_run rest cc C w.tail ((litToks (n, p)).reverse ++ t)
        ((entToks (encodeNat n, w.head?)).reverse ++ b) (w.head?.getD false)
      have e1 : (clauseToks ((n, p) :: C)).reverse ++ t =
          (clauseToks C).reverse ++ ((litToks (n, p)).reverse ++ t) := by
        simp [clauseToks]
      have e2 : tblStk (entsOf (((n, p) :: C).map Prod.fst) w) ++ b =
          tblStk (entsOf (C.map Prod.fst) w.tail) ++
            ((entToks (encodeNat n, w.head?)).reverse ++ b) := by
        simp [entsOf_cons, tblStk_cons]
      have e3 : w.drop ((n, p) :: C).length = w.tail.drop C.length := by simp [List.drop_tail]
      rw [e1, e2, e3]
      refine ((h0.le le_rfl).trans ((h1.le le_rfl).trans h2)).mono ?_
      simp
      omega

/-- **Tokenizer rejects undecodable literals.** A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let
$c, k \in \mathbb{N}$, let $r$ and $w$ be bit strings, $t$ and $b$ symbol lists and $v$ a bit, and
suppose that decoding $k$ literals from the front of $r$ fails. Then from
$\langle \mathsf{lits}, v \mid r, w, t, b, c, k\rangle$ the tokenizer reaches the label
$\mathsf{rej}$ within $2|r| + 3$ steps. -/
theorem lits_fail (cc : ℕ) : ∀ (k : ℕ) (r w : List Bool) (t b : List Sym) (v : Bool),
    decodeLits k r = none →
    Rej (2 * r.length + 3) ⟨some .lits, v, st (r.map .bit) (w.map .bit) t b cc k⟩
  | 0, r, w, t, b, v, h => by simp [decodeLits] at h
  | k + 1, r, w, t, b, v, h => by
      have h0 : Run prog 1 ⟨some .lits, v, st (r.map .bit) (w.map .bit) t b cc (k + 1)⟩
          ⟨some (.nm none), true, st (r.map .bit) (w.map .bit) t b cc k⟩ :=
        Run.single (by simp [prog, TM2.stepAux, List.replicate_succ])
      cases hl : decodeLit r with
      | none => exact (Rej.head h0 (lit_fail r hl _ t b cc k true)).mono (by omega)
      | some q =>
          obtain ⟨⟨n, p⟩, r'⟩ := q
          obtain rfl := (decodeLit_eq_some_iff r (n, p) r').1 hl
          have hr' : decodeLits k r' = none := by
            cases h' : decodeLits k r' with
            | none => rfl
            | some q => simp [decodeLits, h'] at h
          have h1 := lit_run n p r' w t b cc k true
          have ih := lits_fail cc k r' w.tail ((litToks (n, p)).reverse ++ t)
            ((entToks (encodeNat n, w.head?)).reverse ++ b) (w.head?.getD false) hr'
          exact (Rej.head h0 (Rej.head h1 ih)).mono (by simp; omega)

/-- **Tokenizer run on one clause.** A configuration $\langle \ell, v \mid x, w, t, b, i, j\rangle$
of the SAT tokenizer has label $\ell$, internal bit $v$, stacks $X$, $W$, $T$, $B$ holding $x$,
$w$, $t$, $b$ (top first; a bit string stands for its list of bit symbols), and $i$ and $j$ marks
on the clause and literal counters; $\mathbin{+\!\!+}$ is concatenation. Let $C$ be a clause,
$r$ and $w$ bit strings, $t$ and $b$ symbol lists, $c \in \mathbb{N}$ and $v$ a bit. Let $E$ be
the encoding of $C$, $N$ the list of variable indices of the literals of $C$ in order, and $w'$
the string $w$ with its first $|C|$ bits removed (all of them if $w$ is shorter). Then the
tokenizer goes in at most $2|E| + 1$ steps from
$\langle \mathsf{cls}, v \mid E \mathbin{+\!\!+} r, w, t, b, c + 1, 0\rangle$ to
$\langle \mathsf{cls}, \mathsf{false} \mid r, w', \mathrm{rev}(\tau) \mathbin{+\!\!+} t,
\beta \mathbin{+\!\!+} b, c, 0\rangle$, where $\tau$ is the token list of $C$ and $\beta$ is the
table stack of the occurrence table of $N$ against $w$. -/
theorem clause_run (C : CNFClause) (rest w : List Bool) (t b : List Sym) (cc : ℕ) (v : Bool) :
    RunLe prog (2 * (encodeClause C).length + 1)
      ⟨some .cls, v, st ((encodeClause C ++ rest).map .bit) (w.map .bit) t b (cc + 1) 0⟩
      ⟨some .cls, false, st (rest.map .bit) ((w.drop C.length).map .bit)
        ((clauseToks C).reverse ++ t) (tblStk (entsOf (C.map Prod.fst) w) ++ b) cc 0⟩ := by
  have e : encodeClause C ++ rest =
      List.replicate C.length true ++ false :: (C.flatMap encodeLit ++ rest) := by
    simp [encodeClause]
  have h0 : Run prog 1
      ⟨some .cls, v, st ((encodeClause C ++ rest).map .bit) (w.map .bit) t b (cc + 1) 0⟩
      ⟨some (.un false), true, st ((List.replicate C.length true ++ false ::
        (C.flatMap encodeLit ++ rest)).map .bit) (w.map .bit) t b cc 0⟩ := by
    rw [e]; exact Run.single (by simp [prog, TM2.stepAux, List.replicate_succ])
  have h1 := un_run false (C.flatMap encodeLit ++ rest) (w.map .bit) t b C.length cc 0 true
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at h1
  have h2 := lits_run rest cc C w t b true
  refine ((h0.le le_rfl).trans ((h1.le le_rfl).trans h2)).mono ?_
  simp [encodeClause]
  omega

/-- **Tokenizer run on all clauses.** A configuration $\langle \ell, v \mid x, w, t, b, i, j\rangle$
of the SAT tokenizer has label $\ell$, internal bit $v$, stacks $X$, $W$, $T$, $B$ holding $x$,
$w$, $t$, $b$ (top first; a bit string stands for its list of bit symbols), and $i$ and $j$ marks
on the clause and literal counters; $\mathbin{+\!\!+}$ is concatenation. Let $r$ and $w$ be bit
strings, $\varphi$ a CNF formula with $m$ clauses, $t$ and $b$ symbol lists and $v$ a bit. Let
$E$ be the concatenation of the encodings of the clauses of $\varphi$, $N$ the list of variable
indices of all literal occurrences of $\varphi$ in order, and $w'$ the string $w$ with its first
$|N|$ bits removed (all of them if $w$ is shorter). Then the tokenizer goes in at most
$2|E| + m + 1$ steps from $\langle \mathsf{cls}, v \mid E \mathbin{+\!\!+} r, w, t, b, m, 0\rangle$
to $\langle \mathsf{fin}, \mathsf{false} \mid r, w', \mathrm{rev}(\tau) \mathbin{+\!\!+} t,
\beta \mathbin{+\!\!+} b, 0, 0\rangle$, where $\tau$ is the token list of $\varphi$ and $\beta$ is
the table stack of the occurrence table of $N$ against $w$. -/
theorem clauses_run (rest : List Bool) :
    ∀ (φ : CNF) (w : List Bool) (t b : List Sym) (v : Bool),
    RunLe prog (2 * (φ.flatMap encodeClause).length + φ.length + 1)
      ⟨some .cls, v, st ((φ.flatMap encodeClause ++ rest).map .bit) (w.map .bit) t b φ.length 0⟩
      ⟨some .fin, false, st (rest.map .bit) ((w.drop (varsOf φ).length).map .bit)
        ((toks φ).reverse ++ t) (tblStk (entsOf (varsOf φ) w) ++ b) 0 0⟩
  | [], w, t, b, v =>
      (Run.single (by simp [prog, TM2.stepAux, toks, varsOf, tblStk, entsOf])).le (by simp)
  | C :: φ, w, t, b, v => by
      have h1 := clause_run C (φ.flatMap encodeClause ++ rest) w t b φ.length v
      have ih := clauses_run rest φ (w.drop C.length) ((clauseToks C).reverse ++ t)
        (tblStk (entsOf (C.map Prod.fst) w) ++ b) false
      have e1 : (C :: φ).flatMap encodeClause ++ rest =
          encodeClause C ++ (φ.flatMap encodeClause ++ rest) := by simp
      have e2 : (toks (C :: φ)).reverse ++ t =
          (toks φ).reverse ++ ((clauseToks C).reverse ++ t) := by
        simp [toks]
      have e3 : tblStk (entsOf (varsOf (C :: φ)) w) ++ b =
          tblStk (entsOf (varsOf φ) (w.drop C.length)) ++
            (tblStk (entsOf (C.map Prod.fst) w) ++ b) := by
        simp [varsOf, entsOf_append, tblStk_append]
      have e4 : w.drop (varsOf (C :: φ)).length = (w.drop C.length).drop (varsOf φ).length := by
        simp [varsOf, List.drop_drop]
      rw [e1, e2, e3, e4]
      refine (h1.trans ih).mono ?_
      simp
      omega

/-- **Tokenizer rejects undecodable clauses.** A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let
$n \in \mathbb{N}$, let $r$ and $w$ be bit strings, $t$ and $b$ symbol lists and $v$ a bit, and
suppose that decoding $n$ clauses (each a unary literal count followed by that many encoded
literals) from the front of $r$ fails. Then from
$\langle \mathsf{cls}, v \mid r, w, t, b, n, 0\rangle$ the tokenizer reaches the label
$\mathsf{rej}$ within $2|r| + n + 2$ steps. -/
theorem clauses_fail : ∀ (n : ℕ) (r w : List Bool) (t b : List Sym) (v : Bool),
    decodeClauses n r = none →
    Rej (2 * r.length + n + 2) ⟨some .cls, v, st (r.map .bit) (w.map .bit) t b n 0⟩
  | 0, r, w, t, b, v, h => by simp [decodeClauses] at h
  | n + 1, r, w, t, b, v, h => by
      cases hc : decodeClause r with
      | none =>
          have h0 : Run prog 1 ⟨some .cls, v, st (r.map .bit) (w.map .bit) t b (n + 1) 0⟩
              ⟨some (.un false), true, st (r.map .bit) (w.map .bit) t b n 0⟩ :=
            Run.single (by simp [prog, TM2.stepAux, List.replicate_succ])
          cases hu : readUnaryLength r with
          | none => exact (Rej.head h0 (un_fail false _ t b r hu n 0 true)).mono (by omega)
          | some q =>
              obtain ⟨l, r'⟩ := q
              obtain rfl := (readUnaryLength_eq_some_iff r l r').1 hu
              have hl : decodeLits l r' = none := by simpa [decodeClause] using hc
              have h1 := un_run false r' (w.map .bit) t b l n 0 true
              simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at h1
              exact (Rej.head h0 (Rej.head h1 (lits_fail n l r' w t b true hl))).mono
                (by simp; omega)
      | some q =>
          obtain ⟨C, r'⟩ := q
          obtain rfl := (decodeClause_eq_some_iff r C r').1 hc
          have hr : decodeClauses n r' = none := by
            cases h' : decodeClauses n r' with
            | none => rfl
            | some q => simp [decodeClauses, h'] at h
          have h1 := clause_run C r' w t b n v
          exact (Rej.headLe h1 (clauses_fail n r' _ _ _ false hr)).mono (by simp; omega)

/-! ### The whole input -/

/-- **The tokenizer accepts when the formula stack is empty.** Let $w$, $t$, $b$ be lists of
symbols, $i, j \in \mathbb{N}$ and $v$ a bit. In exactly one step, the SAT tokenizer goes from the
label $\mathsf{fin}$ with internal bit $v$, empty formula stack $X$, stacks $W$, $T$, $B$ holding
$w$, $t$, $b$, and $i$ and $j$ marks on the clause and literal counters, to the label
$\mathsf{acc}$ with internal bit false and all stacks unchanged. -/
theorem fin_acc (w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Run prog 1 ⟨some .fin, v, st [] w t b cc lc⟩ ⟨some .acc, false, st [] w t b cc lc⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem fin_rej (s : Sym) (x w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Rej 1 ⟨some .fin, v, st (s :: x) w t b cc lc⟩ :=
  rej_one (by simp [prog, TM2.stepAux])

theorem st_eq {S : ∀ _ : K, List Sym} (hCC : S .CC = []) (hLC : S .LC = []) :
    S = st (S .X) (S .W) (S .T) (S .B) 0 0 := by
  funext k; cases k <;> simp [hCC, hLC]

/-- **Accepting run of the SAT tokenizer.** Let $x$ and $w$ be bit strings such that $x$ decodes
to the CNF formula $\varphi$, and let $S$ be contents of the tokenizer's stacks in which $X$
holds the bits of $x$, $W$ holds the bits of $w$, and the counters $CC$ and $LC$ are empty.
Started at the start label with stacks $S$ and any value of its Boolean variable, the tokenizer
reaches the accepting label within $2|x| + 2$ steps, with final stacks $S'$ such that $X$, $CC$
and $LC$ are empty, $W$ holds the bits of $w$ without their first $m$ entries, where $m$ is the
number of literal occurrences in $\varphi$, $T$ holds the reversed token list of $\varphi$ on top
of the original contents of $T$, and $B$ holds the table stack of the occurrence table of
$\varphi$ and $w$ on top of the original contents of $B$. -/
theorem run_some {x w : List Bool} {φ : CNF} (h : decodeCNF x = some φ) (v : Bool)
    (S : ∀ _ : K, List Sym) (hX : S .X = x.map Sym.bit) (hW : S .W = w.map Sym.bit)
    (hCC : S .CC = []) (hLC : S .LC = []) :
    ∃ v' S', RunLe prog (2 * x.length + 2) ⟨some start, v, S⟩ ⟨some .acc, v', S'⟩ ∧
      S' .X = [] ∧ S' .W = (w.drop (varsOf φ).length).map Sym.bit ∧ S' .CC = [] ∧
      S' .LC = [] ∧ S' .T = (toks φ).reverse ++ S .T ∧ S' .B = tblStk (ents φ w) ++ S .B := by
  obtain rfl := (decodeCNF_eq_some_iff x φ).1 h
  refine ⟨false, st [] ((w.drop (varsOf φ).length).map .bit) ((toks φ).reverse ++ S .T)
    (tblStk (ents φ w) ++ S .B) 0 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [congrArg (TM2.Cfg.mk (some start) v) (st_eq hCC hLC), hX, hW]
  have h1 := un_run true (φ.flatMap encodeClause) (w.map .bit) (S .T) (S .B) φ.length 0 0 v
  simp only [ite_true, Nat.zero_add] at h1
  have h2 := clauses_run [] φ w (S .T) (S .B) true
  rw [List.append_nil, List.map_nil] at h2
  have h3 := fin_acc ((w.drop (varsOf φ).length).map .bit) ((toks φ).reverse ++ S .T)
    (tblStk (entsOf (varsOf φ) w) ++ S .B) 0 0 false
  refine ((h1.le le_rfl).trans (h2.trans (h3.le le_rfl))).mono ?_
  simp [encodeCNF]
  omega

/-- **Rejecting run.** Let $x$ and $w$ be bit strings such that $x$ does not decode as a CNF
formula. For every bit $v$ and stacks $S$ with the bits of $x$ on the formula stack $X$, the bits
of $w$ on the witness stack $W$, and both counter stacks $CC$ and $LC$ empty, the tokenizer
started at its start label with internal bit $v$ and stacks $S$ reaches a configuration with label
$\mathsf{rej}$ within $2|x| + 2$ steps. -/
theorem run_none {x w : List Bool} (h : decodeCNF x = none) (v : Bool) (S : ∀ _ : K, List Sym)
    (hX : S .X = x.map Sym.bit) (hW : S .W = w.map Sym.bit) (hCC : S .CC = [])
    (hLC : S .LC = []) :
    ∃ v' S', RunLe prog (2 * x.length + 2) ⟨some start, v, S⟩ ⟨some .rej, v', S'⟩ := by
  change Rej _ _
  rw [congrArg (TM2.Cfg.mk (some start) v) (st_eq hCC hLC), hX, hW]
  cases hu : readUnaryLength x with
  | none => exact (un_fail true _ _ _ x hu 0 0 v).mono (by omega)
  | some q =>
      obtain ⟨n, r⟩ := q
      obtain rfl := (readUnaryLength_eq_some_iff x n r).1 hu
      have h1 := un_run true r (w.map .bit) (S .T) (S .B) n 0 0 v
      simp only [ite_true, Nat.zero_add] at h1
      cases hc : decodeClauses n r with
      | none => exact (Rej.head h1 (clauses_fail n r w _ _ true hc)).mono (by simp; omega)
      | some q =>
          obtain ⟨φ, rest⟩ := q
          obtain ⟨rfl, rfl⟩ := (decodeClauses_eq_some_iff n r φ rest).1 hc
          cases rest with
          | nil =>
              rw [List.append_nil] at h
              exact absurd ((decodeCNF_encodeCNF φ).symm.trans h) (Option.some_ne_none φ)
          | cons s rest' =>
              have h2 := clauses_run (s :: rest') φ w (S .T) (S .B) true
              have h3 := fin_rej (.bit s) (rest'.map .bit) ((w.drop (varsOf φ).length).map .bit)
                ((toks φ).reverse ++ S .T) (tblStk (entsOf (varsOf φ) w) ++ S .B) 0 0 false
              exact (Rej.headLe ((h1.le le_rfl).trans h2) h3).mono (by simp; omega)

end Cslib.Complexity.SatVerifier.Tokenizer
