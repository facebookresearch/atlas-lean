/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSat
public import CSLibExt.Computability.Complexity.SatCheck

/-!
# SAT ≤ 3SAT, component 2: the emitter machine

A `TM2` machine that walks the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes `encodeCNF (to3 φ)` onto the output stack `O`, so that
`O` reads the encoding top-first (`run`). Symbols are pushed in reverse order of the encoding,
which is the order in which the token stack presents them: clauses last-first and, per clause,
literals last-first, each literal's name bits from the most significant one.

* Per input clause (a `cl` token) the machine prepends the encodings of the clauses of
  `chain C u`; per literal it prepends one output clause, `litCl` (the literal renamed, with a
  fresh literal `(fresh z, true)` unless it is the first literal walked, and `(fresh z', false)`
  unless it is the last one), closed by `false` and the unary literal count. An empty clause
  gives the empty output clause.
* Names: `ren n = 2 n` has code `false :: encodeNat n` for `n > 0`, so the name bits are copied
  and a low `false` is added when the name was non-empty (`encodeLit_renLit`). Fresh names have
  the palindromic code `true, z × false, true` (`encodeNat_fresh`), written from the unary
  counter `U` holding the current fresh number (`fresh_run`).
* `C` counts the output clauses; at the end the formula prefix is `C` ones and a `false`.

The literal loop follows the clause by forward induction on its literals (`lits_run`), the
clause loop by forward induction on the formula (`formula_run`): the token stack holds the
earlier literals (clauses) under the later ones, so the inductive hypothesis covers the top part
and the step handles the last literal (clause), as `to3Aux` and `walkF` do.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.Emit3

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier

/-! ### Codes of renamed and fresh names -/

theorem num_pos (n : ℕ) (h : 0 < n) : ∃ p : PosNum, (n : Num) = .pos p ∧ (p : ℕ) = n := by
  cases e : (n : Num) with
  | zero => exfalso; have := congrArg (fun m : Num => (m : ℕ)) e; simp at this; omega
  | pos p =>
      refine ⟨p, rfl, ?_⟩
      have := congrArg (fun m : Num => (m : ℕ)) e
      simpa only [Num.to_of_nat, Num.cast_pos] using this.symm

theorem encodeNat_bit1 (n : ℕ) : encodeNat (2 * n + 1) = true :: encodeNat n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  obtain ⟨p, hp, hpn⟩ := num_pos n hn
  have : ((2 * n + 1 : ℕ) : Num) = Num.pos (PosNum.bit1 p) := by
    apply Num.to_nat_inj.1
    rw [Num.to_of_nat, Num.cast_pos, PosNum.cast_bit1, hpn]; omega
  unfold encodeNat; rw [this, hp]; rfl

theorem encodeNat_bit0 (n : ℕ) (hn : 0 < n) : encodeNat (2 * n) = false :: encodeNat n := by
  obtain ⟨p, hp, hpn⟩ := num_pos n hn
  have : ((2 * n : ℕ) : Num) = Num.pos (PosNum.bit0 p) := by
    apply Num.to_nat_inj.1
    rw [Num.to_of_nat, Num.cast_pos, PosNum.cast_bit0, hpn]; omega
  unfold encodeNat; rw [this, hp]; rfl

theorem encodeNat_two_pow (z : ℕ) : encodeNat (2 ^ z) = List.replicate z false ++ [true] := by
  induction z with
  | zero => rfl
  | succ z ih =>
      rw [pow_succ, mul_comm, encodeNat_bit0 _ (Nat.two_pow_pos z), ih]; rfl

/-- **Binary representation of a fresh name.** For every natural number $z$, the binary
representation (least significant bit first) of $\mathrm{fresh}(z) = 2^{z+1} + 1$ is
$\mathrm{true}$, then $z$ copies of $\mathrm{false}$, then $\mathrm{true}$. -/
theorem encodeNat_fresh (z : ℕ) :
    encodeNat (fresh z) = true :: (List.replicate z false ++ [true]) := by
  rw [fresh, pow_succ, mul_comm, encodeNat_bit1, encodeNat_two_pow]

theorem encodeNat_eq_nil {n : ℕ} : encodeNat n = [] ↔ n = 0 :=
  ⟨fun h => by rw [← decode_encodeNat n, h]; rfl, fun h => by subst h; rfl⟩

theorem delimit_eq (bs : List Bool) :
    BitstringEncoding.delimit bs = bs.flatMap (fun b => [true, b]) ++ [false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [BitstringEncoding.delimit, ih]

/-- **Code of a fresh literal.** For every natural number $z$ and every polarity $b$, the binary
code of the literal $(\mathrm{fresh}(z), b)$, where $\mathrm{fresh}(z) = 2^{z+1} + 1$, is
$\mathrm{true}, \mathrm{true}$, then $z$ copies of the pair $\mathrm{true}, \mathrm{false}$, then
$\mathrm{true}, \mathrm{true}, \mathrm{false}, b$. -/
theorem encodeLit_fresh (z : ℕ) (b : Bool) :
    encodeLit (fresh z, b) = [true, true] ++ rep [true, false] z ++ [true, true, false, b] := by
  have h : ∀ z : ℕ, (List.replicate z false).flatMap (fun b => [true, b]) = rep [true, false] z :=
    fun z => by induction z with
      | zero => rfl
      | succ z ih => rw [List.replicate_succ, List.flatMap_cons, ih, rep_succ]
  simp [encodeLit, encodeNatPrefix, encodeNat_fresh, delimit_eq, h]

/-- **Code of a renamed literal.** For every literal $(n, p)$, the binary code of the renamed
literal $(2n, p)$ is: the pair $\mathrm{true}, \mathrm{false}$ if $n \neq 0$ and nothing if
$n = 0$, then the pair $\mathrm{true}, b$ for each bit $b$ of the binary representation of $n$
(least significant bit first, no bits for $n = 0$), then $\mathrm{false}, p$. -/
theorem encodeLit_renLit (l : ℕ × Bool) :
    encodeLit (renLit l) = (if l.1 = 0 then [] else [true, false]) ++
      (encodeNat l.1).flatMap (fun b => [true, b]) ++ [false, l.2] := by
  simp only [encodeLit, encodeNatPrefix, renLit, ren, delimit_eq]
  rcases Nat.eq_zero_or_pos l.1 with h | h
  · simp [h]
  · simp [encodeNat_bit0 _ h, Nat.pos_iff_ne_zero.1 h]

/-! ### The machine -/

/-- **Stacks of the 3SAT emitter.** The 3SAT emitter machine has six stacks: the token stack
$T$, the output stack $O$, the fresh counter $U$, two scratch counters $Z$ and $W$, and the
output clause count $C$. -/
inductive K | T | O | U | Z | W | C
  deriving DecidableEq

instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.O, K.U, K.Z, K.W, K.C], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the SAT-to-3SAT emitter.** The output stack of the emitter machine holds
Booleans; each of its other stacks (the token stack, the fresh counter, the two scratch counters
and the output clause count) holds symbols of the SAT verifier's token alphabet.

The counters are unary: they hold only the clause token. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Control labels of the SAT-to-3SAT emitter.** The emitter machine has the labels
$\mathrm{start}$, $\mathrm{clause}$, $\mathrm{fin}$ and $\mathrm{done}$, and, for Booleans
$f, p, s, x, e$, the labels $\mathrm{lit}(f)$, $\mathrm{fa}(s, x)$, $\mathrm{fb}(s, x)$,
$\mathrm{fc}(s, x)$, $\mathrm{fd}(s, x)$, $\mathrm{fe}(s, x)$, $\mathrm{body}(f, p)$,
$\mathrm{cp}(f, e)$, $\mathrm{aft}(f)$ and $\mathrm{sfx}(f)$, all distinct; equality of labels is
decidable.

At $\mathrm{lit}(f)$ the machine pops a literal marker, $f$ telling whether it is the first
literal walked in its clause. The labels $\mathrm{fa}$ to $\mathrm{fe}$ prepend the fresh literal
$(2^{z+1} + 1, s)$ for the current counter $z$, where $x$ is the polarity of the pending literal
when $s$ is true and its first-literal flag when $s$ is false. The labels $\mathrm{body}$ and
$\mathrm{cp}$ prepend the renamed literal, and $\mathrm{aft}$ and $\mathrm{sfx}$ close the output
clause. -/
inductive Lab
  | start | clause | lit (f : Bool)
  | fa (s x : Bool) | fb (s x : Bool) | fc (s x : Bool) | fd (s x : Bool) | fe (s x : Bool)
  | body (f p : Bool) | cp (f ne : Bool) | aft (f : Bool) | sfx (f : Bool) | fin | done
  deriving DecidableEq

instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.start, .clause, .fin, .done, .lit true, .lit false, .aft true, .aft false, .sfx true,
      .sfx false] ++ ([(true, true), (true, false), (false, true), (false, false)].flatMap
        fun q : Bool × Bool => [Lab.fa q.1 q.2, .fb q.1 q.2, .fc q.1 q.2, .fd q.1 q.2,
          .fe q.1 q.2, .body q.1 q.2, .cp q.1 q.2]))
    (fun x => by cases x <;> (try rename_i a b; cases a <;> cases b) <;>
      (try rename_i a; cases a) <;> decide)

/-- **Literal-marker test of the 3SAT emitter.** For an optional token $s$ (the top of a stack,
absent when the stack is empty), the test is true exactly when $s$ is present and is a literal
marker, of either polarity. -/
def isLit : Option Sym → Bool
  | some (.lit _) => true
  | _ => false

/-- **Entry label of a literal.** For Booleans $f$ and $p$, the label where the emitter continues
after popping the marker of a literal of polarity $p$ is $\mathrm{body}(\text{true}, p)$, which
copies the name directly, if $f$ holds (the literal is the first walked in its clause), and
$\mathrm{fa}(\text{true}, p)$, which first prepends the fresh literal of the current counter
with polarity true, otherwise. -/
def pre (f p : Bool) : Lab := if f then .body true p else .fa true p

/-- **Return label of the fresh-literal subroutine.** For Booleans $s$ and $x$, the label where
the emitter continues after prepending the fresh literal of polarity $s$ is
$\mathrm{body}(\text{false}, x)$ if $s$ is true, which copies the name of the pending literal of
polarity $x$, and $\mathrm{sfx}(x)$ if $s$ is false, which closes the output clause, $x$ being
the first-literal flag. -/
def ret : Bool → Bool → Lab
  | true, p => .body false p
  | false, f => .sfx f

/-- **The SAT-to-3SAT emitter machine.** The emitter is the multi-stack machine on the stacks
$T, O, U, Z, W, C$ of the emitter ($O$ holds bits, the others token symbols), with the labels of
the emitter and one internal Boolean variable. A unit is the clause symbol, and prepending bits
$b_1, \dots, b_k$ to $O$ pushes them so that $O$ reads $b_1, \dots, b_k$ from the top. The labels
act as follows.

* $\mathrm{start}$: if $T$ is empty, push $\text{false}$ on $O$ and go to $\mathrm{fin}$;
  otherwise pop $T$ and go to $\mathrm{clause}$.
* $\mathrm{clause}$: if the top of $T$ is a literal marker, go to $\mathrm{lit}(\text{true})$;
  otherwise push a unit on $C$, push $\text{false}$ on $O$ and go to $\mathrm{start}$.
* $\mathrm{lit}(f)$: pop $T$, set the variable $p$ to whether the popped symbol is the literal
  marker of polarity true, and go to $\mathrm{body}(\text{true}, p)$ if $f$ holds and to
  $\mathrm{fa}(\text{true}, p)$ otherwise.
* $\mathrm{fa}(s, x)$: prepend $\text{true}, \text{true}, \text{false}, s$ to $O$ and go to
  $\mathrm{fb}(s, x)$.
* $\mathrm{fb}(s, x)$: pop $U$ until it is empty, pushing a unit on $Z$ and on $W$ per popped
  symbol, then go to $\mathrm{fc}(s, x)$.
* $\mathrm{fc}(s, x)$: pop $W$ until it is empty, pushing a unit on $U$ per popped symbol, then
  go to $\mathrm{fd}(s, x)$.
* $\mathrm{fd}(s, x)$: pop $Z$ until it is empty, prepending $\text{true}, \text{false}$ to $O$
  per popped symbol, then go to $\mathrm{fe}(s, x)$.
* $\mathrm{fe}(\text{true}, p)$: push a unit on $U$, prepend $\text{true}, \text{true}$ to $O$
  and go to $\mathrm{body}(\text{false}, p)$. $\mathrm{fe}(\text{false}, f)$: prepend
  $\text{true}, \text{true}$ to $O$ and go to $\mathrm{sfx}(f)$.
* $\mathrm{body}(f, p)$: prepend $\text{false}, p$ to $O$ and go to $\mathrm{cp}(f, \text{false})$.
* $\mathrm{cp}(f, e)$: if the top of $T$ is a bit symbol $b$, pop it, prepend $\text{true}, b$ to
  $O$ and go to $\mathrm{cp}(f, \text{true})$; otherwise prepend $\text{true}, \text{false}$ to
  $O$ if $e$ holds, and go to $\mathrm{aft}(f)$.
* $\mathrm{aft}(f)$: if the top of $T$ is a literal marker, go to $\mathrm{fa}(\text{false}, f)$;
  otherwise push a unit on $C$, prepend $k$ copies of $\text{true}$ and then $\text{false}$ to
  $O$, where $k = 1$ if $f$ holds and $k = 2$ otherwise, and go to $\mathrm{start}$.
* $\mathrm{sfx}(f)$: push a unit on $C$, prepend $k$ copies of $\text{true}$ and then
  $\text{false}$ to $O$, where $k = 2$ if $f$ holds and $k = 3$ otherwise, and go to
  $\mathrm{lit}(\text{false})$.
* $\mathrm{fin}$: pop $C$ until it is empty, prepending $\text{true}$ to $O$ per popped symbol,
  then go to $\mathrm{done}$.
* $\mathrm{done}$: halt.

Each test of a stack top and each pop of a loop also stores its outcome in the internal
variable. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .start => .peek .T (fun _ o => o.isNone) <| .branch id
      (.push .O (fun _ => false) (.goto fun _ => .fin))
      (.pop .T (fun s _ => s) (.goto fun _ => .clause))
  | .clause => .peek .T (fun _ o => isLit o) <| .branch id (.goto fun _ => .lit true)
      (.push .C (fun _ => Sym.cl) <| .push .O (fun _ => false) <| .goto fun _ => .start)
  | .lit f => .pop .T (fun _ o => o == some (.lit true)) (.goto fun s => pre f s)
  | .fa s x => emitR .O [true, true, false, s] (.fb s x)
  | .fb s x => xfer .U [⟨.Z, Sym.cl⟩, ⟨.W, Sym.cl⟩] (.fb s x) (.fc s x)
  | .fc s x => xfer .W [⟨.U, Sym.cl⟩] (.fc s x) (.fd s x)
  | .fd s x => xferE .Z .O [true, false] (.fd s x) (.fe s x)
  | .fe true p => .push .U (fun _ => Sym.cl) (emitR .O [true, true] (.body false p))
  | .fe false f => emitR .O [true, true] (.sfx f)
  | .body f p => emitR .O [false, p] (.cp f false)
  | .cp f ne => .peek .T (fun _ o => isBit Sym.bit? o) <| .branch id
      (.peek .T (fun _ o => o == some (.bit true)) <| .pop .T (fun s _ => s) <|
        .push .O id <| .push .O (fun _ => true) <| .goto fun _ => .cp f true)
      (if ne then emitR .O [true, false] (.aft f) else .goto fun _ => .aft f)
  | .aft f => .peek .T (fun _ o => isLit o) <| .branch id (.goto fun _ => .fa false f)
      (.push .C (fun _ => Sym.cl) <|
        emitR .O (List.replicate (if f then 1 else 2) true ++ [false]) .start)
  | .sfx f => .push .C (fun _ => Sym.cl) <|
      emitR .O (List.replicate (if f then 2 else 3) true ++ [false]) (.lit false)
  | .fin => xferE .C .O [true] .fin .done
  | .done => .halt

/-- **Start label of the SAT-to-3SAT emitter.** The start label of the emitter machine is its label
$\mathrm{start}$, at which the machine begins each input clause or, once the token stack is
empty, moves on to its final phase, which writes the output clause count. -/
def start : Lab := .start

/-! ### Machine states -/

/-- **Stack contents of the SAT-to-3SAT emitter.** For a list $t$ of tokens, a list $o$ of bits
and $z, c \in \mathbb{N}$, $\mathrm{st}(t, o, z, c)$ is the stack contents of the emitter machine
in which the token stack holds $t$, the output stack holds $o$, the fresh counter holds exactly
$z$ copies of the clause token $\mathrm{cl}$, the output clause count holds exactly $c$ copies of
$\mathrm{cl}$, and the two scratch counters are empty. -/
def st (t : List Sym) (o : List Bool) (z c : ℕ) : ∀ k, List (Γ k)
  | .T => t
  | .O => o
  | .U => cnt Sym.cl z
  | .Z => []
  | .W => []
  | .C => cnt Sym.cl c

section States

variable (t : List Sym) (o : List Bool) (z c : ℕ)

@[simp] theorem st_T : st t o z c .T = t := rfl
@[simp] theorem st_O : st t o z c .O = o := rfl
@[simp] theorem st_U : st t o z c .U = List.replicate z Sym.cl := rfl
@[simp] theorem st_Z : st t o z c .Z = [] := rfl
@[simp] theorem st_W : st t o z c .W = [] := rfl
@[simp] theorem st_C : st t o z c .C = List.replicate c Sym.cl := rfl

@[simp] theorem st_upd_T (t' : List Sym) : update (st t o z c) .T t' = st t' o z c := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_O (o' : List Bool) : update (st t o z c) .O o' = st t o' z c := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_U (x : List (Γ .U)) (hx : x = Sym.cl :: List.replicate z Sym.cl) :
    update (st t o z c) .U x = st t o (z + 1) c := by
  subst hx; funext k; cases k <;> rfl

@[simp] theorem st_upd_C (x : List (Γ .C)) (hx : x = Sym.cl :: List.replicate c Sym.cl) :
    update (st t o z c) .C x = st t o z (c + 1) := by
  subst hx; funext k; cases k <;> rfl

end States

@[simp] theorem sym_beq (a b : Sym) : (a == b) = decide (a = b) := rfl

/-! ### One-step lemmas -/

section Steps

variable (v : Bool) (o : List Bool) (z c : ℕ)

theorem start_nil : Run prog 1 ⟨some .start, v, st [] o z c⟩
    ⟨some .fin, true, st [] (false :: o) z c⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem start_cl (R : List Sym) : Run prog 1 ⟨some .start, v, st (.cl :: R) o z c⟩
    ⟨some .clause, false, st R o z c⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem clause_lit (t : List Sym) (h : isLit t.head? = true) :
    Run prog 1 ⟨some .clause, v, st t o z c⟩ ⟨some (.lit true), true, st t o z c⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem clause_nil (t : List Sym) (h : isLit t.head? = false) :
    Run prog 1 ⟨some .clause, v, st t o z c⟩ ⟨some .start, false, st t (false :: o) z (c + 1)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem lit_step (f p : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.lit f), v, st (.lit p :: R) o z c⟩ ⟨some (pre f p), p, st R o z c⟩ :=
  Run.single (by cases p <;> simp [prog, TM2.stepAux])

theorem body_step (f p : Bool) (t : List Sym) :
    Run prog 1 ⟨some (.body f p), v, st t o z c⟩
      ⟨some (.cp f false), v, st t (false :: p :: o) z c⟩ :=
  Run.single (by simp [prog, TM2.stepAux, emitR, emit, stepAux_pushList])

theorem cp_bit (f ne b : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.cp f ne), v, st (.bit b :: R) o z c⟩
      ⟨some (.cp f true), b, st R (true :: b :: o) z c⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, isBit, Sym.bit?])

theorem cp_end (f ne : Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) :
    Run prog 1 ⟨some (.cp f ne), v, st R o z c⟩
      ⟨some (.aft f), false, st R ((if ne then [true, false] else []) ++ o) z c⟩ := by
  have h : isBit Sym.bit? R.head? = false := by simp [isBit, hR]
  cases ne
  · exact Run.single (by simp [prog, TM2.stepAux, h])
  · exact Run.single (by simp [prog, TM2.stepAux, h, emitR, emit, stepAux_pushList])

theorem aft_lit (f : Bool) (R : List Sym) (h : isLit R.head? = true) :
    Run prog 1 ⟨some (.aft f), v, st R o z c⟩ ⟨some (.fa false f), true, st R o z c⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem aft_end (f : Bool) (R : List Sym) (h : isLit R.head? = false) :
    Run prog 1 ⟨some (.aft f), v, st R o z c⟩ ⟨some .start, false,
      st R (List.replicate (if f then 1 else 2) true ++ false :: o) z (c + 1)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h, emitR, emit, stepAux_pushList])

theorem sfx_step (f : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.sfx f), v, st R o z c⟩ ⟨some (.lit false), v,
      st R (List.replicate (if f then 2 else 3) true ++ false :: o) z (c + 1)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, emitR, emit, stepAux_pushList])

end Steps

/-! ### Phases of a literal -/

section Phases

theorem run_cast {n n' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : Run prog n c d) (hn : n = n')
    (hd : d = d') : Run prog n' c d' := hn ▸ hd ▸ h

/-- **Fresh-literal subroutine of the 3SAT emitter.** For all booleans $s$ and $x$, every token
list $t$, output bit list $o$, natural numbers $z$ and $c$, and flag $v$, there is a flag $v'$
such that the 3SAT emitter machine, started at the fresh-literal label for $(s, x)$ with flag
$v$, token stack $t$, output stack $o$, fresh counter $z$, clause count $c$ and empty scratch
counters, reaches in exactly $3z + 5$ steps the return label for $(s, x)$ with flag $v'$, token
stack $t$, output stack the code of the literal $(\mathrm{fresh}(z), s)$ followed by $o$, where
$\mathrm{fresh}(z) = 2^{z+1} + 1$, fresh counter $z + 1$ if $s$ is true and $z$ if $s$ is false,
clause count $c$ and empty scratch counters. The return label is the renamed-literal label for a
literal of polarity $x$ that is not the first walked in its clause if $s$ is true, and the
clause-closing label for first-flag $x$ if $s$ is false.

The subroutine prepends $\mathrm{true}, \mathrm{true}, \mathrm{false}, s$, copies the fresh
counter $U$ into the scratch counter $Z$ (restoring $U$ through the scratch counter $W$),
prepends $\mathrm{true}, \mathrm{false}$ per unit of $Z$, then prepends
$\mathrm{true}, \mathrm{true}$, and for $s$ true adds one to $U$. -/
theorem fresh_run (s x : Bool) (t : List Sym) (o : List Bool) (z c : ℕ) (v : Bool) :
    ∃ v', Run prog (3 * z + 5) ⟨some (.fa s x), v, st t o z c⟩
      ⟨some (ret s x), v', st t (encodeLit (fresh z, s) ++ o) (z + if s then 1 else 0) c⟩ := by
  have r₁ := emitR_run (M := prog) (self := .fa s x) rfl v (st t o z c)
  rw [st_upd_O, st_O] at r₁
  set o₁ := [true, true, false, s] ++ o with ho₁
  have r₂ := copy_run (M := prog) (a := .U) (c := .Z) (t := .W) (ua := Sym.cl) (uc := Sym.cl)
    (ut := Sym.cl) (l₁ := .fb s x) (l₂ := .fc s x) (next := .fd s x) rfl rfl (by decide)
    (by decide) (by decide) z 0 v (st t o₁ z c) rfl rfl rfl
  have r₃ := xferE_run (M := prog) (self := .fd s x) (next := .fe s x) (k := .Z) (o := .O)
    (ys := [true, false]) rfl
    (by decide) Sym.cl (z + 0) (Flag.tag false) (update (st t o₁ z c) .Z (cnt Sym.cl (z + 0)))
    (by rw [update_self])
  have e : update (update (update (st t o₁ z c) K.Z (cnt Sym.cl (z + 0))) K.Z []) K.O
      (rep [true, false] (z + 0) ++ (update (st t o₁ z c) K.Z (cnt Sym.cl (z + 0))) K.O) =
      st t (rep [true, false] z ++ o₁) z c := by
    funext k; cases k <;> simp
  rw [e] at r₃
  have r₄ : Run prog 1 ⟨some (.fe s x), Flag.tag false, st t (rep [true, false] z ++ o₁) z c⟩
      ⟨some (ret s x), Flag.tag false,
        st t (encodeLit (fresh z, s) ++ o) (z + if s then 1 else 0) c⟩ := by
    cases s
    · exact Run.single (by
        simp [prog, ret, TM2.stepAux, emitR, emit, stepAux_pushList, encodeLit_fresh, ho₁])
    · exact Run.single (by
        simp [prog, ret, TM2.stepAux, emitR, emit, stepAux_pushList, encodeLit_fresh, ho₁])
  exact ⟨_, (((r₁.trans r₂).trans r₃).trans r₄).of_eq (by omega)⟩

/-- **Name copy loop of the 3SAT emitter.** Let $f$ and $e$ be booleans, $R$ a token list whose
first token, if there is one, is not a name bit, $z$ and $c$ natural numbers, $b_1, \dots, b_m$
bits, $v$ a flag and $o$ an output bit list. Then there is a flag $v'$ such that the 3SAT emitter
machine, started at the copy label for $(f, e)$ with flag $v$, token stack the name-bit tokens
$b_1, \dots, b_m$ followed by $R$, output stack $o$, fresh counter $z$, clause count $c$ and
empty scratch counters, reaches in exactly $m + 1$ steps the after-literal label for $f$ with
flag $v'$, token stack $R$, output stack
$P, \mathrm{true}, b_m, \mathrm{true}, b_{m-1}, \dots, \mathrm{true}, b_1$ followed by $o$, and
the same counters, where $P$ is the pair $\mathrm{true}, \mathrm{false}$ if $e$ is true or
$m > 0$, and is empty otherwise.

Each name bit $b$ read prepends $b$ and then $\mathrm{true}$; the leading pair
$\mathrm{true}, \mathrm{false}$ codes the low bit $0$ of a renamed name $2n$. -/
theorem cp_run (f : Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) (z c : ℕ) :
    ∀ (rb : List Bool) (ne v : Bool) (o : List Bool),
      ∃ v', Run prog (rb.length + 1) ⟨some (.cp f ne), v, st (rb.map Sym.bit ++ R) o z c⟩
        ⟨some (.aft f), v', st R ((if ne || !rb.isEmpty then [true, false] else []) ++
          rb.reverse.flatMap (fun b => [true, b]) ++ o) z c⟩ := by
  intro rb
  induction rb with
  | nil =>
      intro ne v o
      exact ⟨false, by simpa using cp_end v o z c f ne R hR⟩
  | cons b rb ih =>
      intro ne v o
      obtain ⟨v', r⟩ := ih true b (true :: b :: o)
      exact ⟨v', run_cast ((cp_bit v o z c f ne b _).trans r) (by simp; omega) (by simp)⟩

/-- **Copying a renamed name.** Write $\langle \ell, w, t, o, z, c\rangle$ for the configuration
of the emitter machine at label $\ell$ with internal variable $w$, token stack $t$, output stack
$o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let $l = (n, b)$ be a
literal, $f$ and $v$ Booleans, $R$ a token stack whose top, if any, is not a bit symbol, $o$ an
output stack and $z$, $c$ natural numbers. Let $B$ be the $k$ binary digits of $n$ as bit
symbols, most significant first ($k = 0$ for $n = 0$), and $e$ the encoding of the renamed
literal $(2n, b)$. Then for some $w'$ the machine goes in exactly $k + 2$ steps from
$\langle \mathrm{body}(f, b), v, B R, o, z, c\rangle$ to
$\langle \mathrm{aft}(f), w', R, e\,o, z, c\rangle$, where juxtaposition is concatenation of
stacks, top first. -/
theorem name_run (f : Bool) (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (o : List Bool) (z c : ℕ) (v : Bool) :
    ∃ v', Run prog ((encodeNat l.1).length + 2)
      ⟨some (.body f l.2), v, st (((encodeNat l.1).map Sym.bit).reverse ++ R) o z c⟩
      ⟨some (.aft f), v', st R (encodeLit (renLit l) ++ o) z c⟩ := by
  obtain ⟨v', r⟩ := cp_run f R hR z c (encodeNat l.1).reverse false v (false :: l.2 :: o)
  refine ⟨v', ?_⟩
  have h := (body_step v o z c f l.2 _).trans r
  rw [← List.map_reverse]
  refine run_cast h (by simp; omega) ?_
  rw [encodeLit_renLit]
  rcases Nat.eq_zero_or_pos l.1 with h0 | h0
  · simp [h0, show encodeNat 0 = [] from rfl]
  · have e : encodeNat l.1 ≠ [] := fun e => by simp [encodeNat_eq_nil.1 e] at h0
    simp [e, Nat.pos_iff_ne_zero.1 h0]

/-- **The 3SAT emitter reads a literal marker.** For all booleans $f$ and $p$, every token list
$t$, output bit list $o$, natural numbers $z$ and $c$, and flag $v$, there is a flag $v'$ such
that the 3SAT emitter machine, started at the literal label for $f$ with flag $v$, token stack
the literal marker of polarity $p$ followed by $t$, output stack $o$, fresh counter $z$, clause
count $c$ and empty scratch counters, reaches the renamed-literal label for $(f, p)$ with flag
$v'$ and token stack $t$ as follows. If $f$ is true (the literal is the first walked in its
clause), this takes exactly $1$ step and leaves the output stack and the fresh counter unchanged.
If $f$ is false, it takes exactly $3z + 6$ steps, the output stack becomes the code of the
literal $(\mathrm{fresh}(z), \mathrm{true})$ followed by $o$, where
$\mathrm{fresh}(z) = 2^{z+1} + 1$, and the fresh counter becomes $z + 1$. In both cases the
clause count stays $c$ and the scratch counters stay empty. -/
theorem head_run (f : Bool) (p : Bool) (t : List Sym) (o : List Bool) (z c : ℕ) (v : Bool) :
    ∃ v', Run prog (if f then 1 else 3 * z + 6) ⟨some (.lit f), v, st (.lit p :: t) o z c⟩
      ⟨some (.body f p), v', st t ((if f then [] else encodeLit (fresh z, true)) ++ o)
        (z + if f then 0 else 1) c⟩ := by
  cases f
  · obtain ⟨v', r⟩ := fresh_run true p t o z c p
    exact ⟨v', run_cast ((lit_step v o z c false p t).trans r) (by simp; omega) (by simp [ret])⟩
  · exact ⟨p, by simpa [pre] using lit_step v o z c true p t⟩

/-- **Closing an output clause in the SAT-to-3SAT emitter.** Let $f$ be a Boolean, $R$ a list of
tokens, $o$ a list of bits and $z, c \in \mathbb{N}$, and let $m = 1$ if $f$ is true and $m = 2$
otherwise. Start the emitter machine at its clause-closing label $\mathrm{aft}(f)$, with any
internal state, with stack contents $\mathrm{st}(R, o, z, c)$: token stack $R$, output stack $o$,
fresh counter $z$, output clause count $c$ and empty scratch counters.

If the top of $R$ is a literal marker, then after exactly $3z + 7$ steps the machine is at the
label $\mathrm{lit}(\mathrm{false})$ with stack contents $\mathrm{st}(R, o', z, c + 1)$, where the
list $o'$ consists of $m + 1$ copies of true, then false, then the code of the literal
$(\mathrm{fresh}(z), \mathrm{false})$, then $o$. Otherwise (in particular when $R$ is empty),
after exactly one step the machine is at the label $\mathrm{start}$ with stack contents
$\mathrm{st}(R, o', z, c + 1)$, where $o'$ consists of $m$ copies of true, then false, then $o$.
In both cases the final internal state is unspecified. -/
theorem tail_run (f : Bool) (R : List Sym) (o : List Bool) (z c : ℕ) (v : Bool) :
    ∃ v', Run prog (if isLit R.head? then 3 * z + 7 else 1) ⟨some (.aft f), v, st R o z c⟩
      ⟨some (if isLit R.head? then .lit false else .start), v',
        st R (List.replicate ((if f then 1 else 2) + if isLit R.head? then 1 else 0) true ++
          false :: ((if isLit R.head? then encodeLit (fresh z, false) else []) ++ o)) z
          (c + 1)⟩ := by
  cases h : isLit R.head?
  · exact ⟨false, by simpa using aft_end v o z c f R h⟩
  · obtain ⟨v', r⟩ := fresh_run false f R o z c true
    have r' := ((aft_lit v o z c f R h).trans r).trans
      (sfx_step v' (encodeLit (fresh z, false) ++ o) (z + 0) c f R)
    refine ⟨v', run_cast r' (by simp; omega) ?_⟩
    cases f <;> simp

end Phases

/-! ### Output clauses -/

section Spec

/-- **Output clause of one literal.** For Booleans $f$ and $g$, a counter $z$ and a literal
$l = (n, b)$, let $z' = z$ if $f$ holds and $z' = z + 1$ otherwise. The output clause of $l$ is
the clause consisting of, in this order: the literal $(2^{z'+1} + 1, \text{false})$ unless $g$
holds, then the renamed literal $(2n, b)$, then the literal $(2^{z+1} + 1, \text{true})$ unless
$f$ holds. Here $f$ tells whether $l$ is the first literal walked in its clause, $g$ whether it
is the last one, and $z'$ is the counter after $l$. -/
def litCl (f g : Bool) (z : ℕ) (l : ℕ × Bool) : CNFClause :=
  (if g then [] else [(fresh (z + if f then 0 else 1), false)]) ++
    renLit l :: (if f then [] else [(fresh z, true)])

theorem encodeClause_litCl (f g : Bool) (z : ℕ) (l : ℕ × Bool) :
    encodeClause (litCl f g z l) =
      List.replicate ((if f then 1 else 2) + if g then 0 else 1) true ++ false ::
        ((if g then [] else encodeLit (fresh (z + if f then 0 else 1), false)) ++
          encodeLit (renLit l) ++ (if f then [] else encodeLit (fresh z, true))) := by
  cases f <;> cases g <;> simp [encodeClause, litCl]

/-- **Fresh numbers used by a run of literals.** For a list $L$ of literals and a Boolean $f$,
the number of fresh numbers used up by walking $L$ is $|L| - 1$ (truncated at $0$) if $f$ holds
and $|L|$ otherwise; $f$ tells whether the last literal of $L$ is the first literal walked in
its clause. -/
def nz (Ls : List (ℕ × Bool)) (f : Bool) : ℕ := if f then Ls.length - 1 else Ls.length

theorem nz_cons (l : ℕ × Bool) (Ls : List (ℕ × Bool)) (f : Bool) :
    nz (l :: Ls) f = nz Ls f + if f && Ls.isEmpty then 0 else 1 := by
  cases f <;> cases Ls <;> simp [nz]

/-- **Output clauses of a walked list of literals.** For a list $L$ of literals of a clause,
Booleans $f$ and $g$, and $z \in \mathbb{N}$, $\mathrm{walkF}(L, f, g, z)$ is the list of output
clauses of the literals of $L$, in reading order, when $L$ is walked from its last literal with
counter $z$; $f$ tells whether the last literal of $L$ is the first walked in its clause, and $g$
whether the first literal of $L$ is the last walked. It is defined by recursion on $L$. The empty
list gives no clauses. If $L$ has first literal $l$ and remaining literals $L'$, the first clause
is the output clause of $l$ whose first-walked flag is true exactly when $f$ is true and $L'$ is
empty, whose last-walked flag is $g$, and whose counter is $z + n$, where $n$ is the number of
fresh numbers used up by walking $L'$ ($|L'| - 1$ if $f$ is true, with $0 - 1 = 0$, and $|L'|$
otherwise); it is followed by $\mathrm{walkF}(L', f, \mathrm{false}, z)$. -/
def walkF : List (ℕ × Bool) → Bool → Bool → ℕ → CNF
  | [], _, _, _ => []
  | l :: Ls, f, g, z => litCl (f && Ls.isEmpty) g (z + nz Ls f) l :: walkF Ls f false z

theorem walkF_length (Ls : List (ℕ × Bool)) (f g : Bool) (z : ℕ) :
    (walkF Ls f g z).length = Ls.length := by
  induction Ls generalizing g with
  | nil => rfl
  | cons l Ls ih => simp [walkF, ih]

theorem walkF_chainTail (l : ℕ × Bool) (ls : List (ℕ × Bool)) (z : ℕ) :
    walkF (l :: ls) true false z = chainTail (l :: ls) (z + ls.length) := by
  induction ls generalizing l with
  | nil => simp [walkF, chainTail, litCl, nz]
  | cons l' ls ih =>
      rw [walkF, ih, List.length_cons, chainTail, show z + (ls.length + 1) - 1 = z + ls.length by
        omega]
      simp [litCl, nz, Nat.add_assoc]

/-- **Walking a whole clause gives its chain.** For every non-empty clause $C$ and every
$z \in \mathbb{N}$, the output clauses of the literals of $C$, walked from its last literal with
counter $z$, with both the first-walked flag and the last-walked flag true, that is,
$\mathrm{walkF}(C, \mathrm{true}, \mathrm{true}, z)$, are the chain of clauses replacing $C$ with
fresh numbers from $z$ on. -/
theorem walkF_chain (C : CNFClause) (hC : C ≠ []) (z : ℕ) : walkF C true true z = chain C z := by
  match C, hC with
  | [l], _ => simp [walkF, chain, litCl]
  | l :: l' :: ls, _ =>
      rw [walkF, walkF_chainTail, chain]
      simp [litCl, nz]

theorem chain_length_cons (l : ℕ × Bool) (Ls : List (ℕ × Bool)) (z : ℕ) :
    (chain (l :: Ls) z).length = Ls.length + 1 := by
  rw [← walkF_chain _ (List.cons_ne_nil l Ls), walkF_length, List.length_cons]

theorem clRev_length (C : CNFClause) :
    (Check.clRev C).length = (C.flatMap Check.litRev).length + 1 := by
  simp [Check.clRev, List.length_flatMap, List.sum_reverse]

theorem clauseToks_length_ge (C : CNFClause) : C.length + 1 ≤ (clauseToks C).length := by
  have e := congrArg List.length (Check.clauseToks_reverse C)
  rw [List.length_reverse] at e
  rw [e, clRev_length]
  have := Check.litRev_flatMap_length_ge C
  omega

theorem to3Aux_le (φ : CNF) :
    (to3Aux φ).1 ≤ (toks φ).length ∧ (to3Aux φ).2.length ≤ (toks φ).length := by
  induction φ with
  | nil => simp [to3Aux]
  | cons C φ ih =>
      have h := clauseToks_length_ge C
      have hc : (chain C (to3Aux φ).1).length ≤ C.length + 1 := by
        cases C with
        | nil => simp [chain]
        | cons l Ls => rw [chain_length_cons]; simp
      simp only [to3Aux, toks, List.flatMap_cons, List.length_append, used] at ih ⊢
      omega

end Spec

/-! ### Literals, clauses, formulas -/

section Loops

theorem runLe_cast {n n' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog n c d)
    (hn : n ≤ n') (hd : d = d') : RunLe prog n' c d' := hd ▸ h.mono hn

theorem bit_none_of_isLit {R : List Sym} (h : isLit R.head? = true) :
    R.head?.bind Sym.bit? = none := by
  rcases R with _ | ⟨x, R⟩
  · simp [isLit] at h
  · cases x <;> simp_all [isLit, Sym.bit?]

theorem isLit_litRev (Ls : List (ℕ × Bool)) (l : ℕ × Bool) (R : List Sym) :
    isLit (Ls.flatMap Check.litRev ++ (Check.litRev l ++ R)).head? = true := by
  cases Ls <;> simp [Check.litRev, isLit]

/-- **One literal of the emitter.** Write $\langle \ell, w, t, o, z, c\rangle$ for the
configuration of the emitter machine at label $\ell$ with internal variable $w$, token stack $t$,
output stack $o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let
$l = (n, b)$ be a literal, $f$ and $v$ Booleans, $R$ a token stack whose top, if any, is not a
bit symbol, $o$ an output stack, and $z$, $c$, $Z_b$ natural numbers with $z + d \le Z_b$, where
$d = 0$ if $f$ holds and $d = 1$ otherwise. Let $T_l$ be the token block of $l$: the literal
marker of polarity $b$ above the binary digits of $n$, most significant first (no digits for
$n = 0$). Let $g$ be true exactly when the top of $R$ is not a literal marker (in particular
when $R$ is empty), let $\ell'$ be $\mathrm{start}$ if $g$ holds and $\mathrm{lit}(\text{false})$
otherwise, and let $e$ be the encoding of the output clause of $l$ with flags $f$, $g$ and
counter $z$. Then for some $w'$ the machine goes in at most $|T_l| + 6 Z_b + 14$ steps from
$\langle \mathrm{lit}(f), v, T_l R, o, z, c\rangle$ to
$\langle \ell', w', R, e\,o, z + d, c + 1\rangle$, where juxtaposition is concatenation of
stacks, top first. -/
theorem lit_run (Zb : ℕ) (f : Bool) (l : ℕ × Bool) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) (o : List Bool) (z c : ℕ)
    (hz : z + (if f then 0 else 1) ≤ Zb) (v : Bool) :
    ∃ v', RunLe prog ((Check.litRev l).length + 6 * Zb + 14)
      ⟨some (.lit f), v, st (Check.litRev l ++ R) o z c⟩
      ⟨some (if isLit R.head? then .lit false else .start), v',
        st R (encodeClause (litCl f (!isLit R.head?) z l) ++ o) (z + if f then 0 else 1)
          (c + 1)⟩ := by
  have hT : Check.litRev l ++ R = .lit l.2 :: (((encodeNat l.1).map Sym.bit).reverse ++ R) := by
    simp [Check.litRev]
  obtain ⟨v₁, r₁⟩ := head_run f l.2 (((encodeNat l.1).map Sym.bit).reverse ++ R) o z c v
  obtain ⟨v₂, r₂⟩ := name_run f l R hR _ (z + if f then 0 else 1) c v₁
  obtain ⟨v₃, r₃⟩ := tail_run f R _ (z + if f then 0 else 1) c v₂
  refine ⟨v₃, ?_⟩
  rw [hT]
  refine runLe_cast (((r₁.trans r₂).trans r₃).le le_rfl) ?_ ?_
  · rw [Check.litRev_length]; split_ifs at hz ⊢ <;> omega
  · rw [encodeClause_litCl]
    cases f <;> cases isLit R.head? <;> simp

/-- **The literals of a clause in the emitter.** Write $\langle \ell, w, t, o, z, c\rangle$ for
the configuration of the emitter machine at label $\ell$ with internal variable $w$, token stack
$t$, output stack $o$, fresh counter $z$, output-clause count $c$ and empty scratch stacks. Let
$Z_b$ be a natural number, $L = (l_1, \dots, l_k)$ a list of literals, $R$ a token stack whose
top is a literal marker, $f$ and $v$ Booleans, $o$ an output stack and $z$, $c$ natural numbers
with $z + m \le Z_b$, where $m$ is $k - 1$ (truncated at $0$) if $f$ holds and $k$ otherwise.
The token block of a literal $(n, b)$ is the literal marker of polarity $b$ above the binary
digits of $n$, most significant first (no digits for $n = 0$); let $T$ be the concatenation of
the token blocks of $l_k, \dots, l_1$, in this order. For $1 \le i \le k$ let $z_i = z + m_i$,
where $m_i$ is $k - i - 1$ (truncated at $0$) if $f$ holds and $k - i$ otherwise, let $f_i$ be
true exactly when $f$ holds and $i = k$, and let $e_i$ be the encoding of the output clause of
$l_i$ with flags $f_i$, false and counter $z_i$. Let $E = e_1 \cdots e_k$ (empty for $k = 0$),
and let $f'$ be true exactly when $f$ holds and $k = 0$. Then for some $w'$ the machine goes in
at most $|T| + k (6 Z_b + 14)$ steps from $\langle \mathrm{lit}(f), v, T R, o, z, c\rangle$ to
$\langle \mathrm{lit}(f'), w', R, E\,o, z + m, c + k\rangle$, where juxtaposition is
concatenation of stacks, top first. -/
theorem lits_run (Zb : ℕ) :
    ∀ (Ls : List (ℕ × Bool)) (R : List Sym), isLit R.head? = true →
      ∀ (f : Bool) (o : List Bool) (z c : ℕ) (v : Bool), z + nz Ls f ≤ Zb →
      ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length + Ls.length * (6 * Zb + 14))
        ⟨some (.lit f), v, st (Ls.reverse.flatMap Check.litRev ++ R) o z c⟩
        ⟨some (.lit (f && Ls.isEmpty)), v',
          st R ((walkF Ls f false z).flatMap encodeClause ++ o) (z + nz Ls f) (c + Ls.length)⟩ := by
  intro Ls
  induction Ls with
  | nil =>
      intro R _ f o z c v _
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [walkF, nz])⟩
  | cons l Ls ih =>
      intro R hR f o z c v hz
      have hz' : z + nz Ls f ≤ Zb := by rw [nz_cons] at hz; omega
      obtain ⟨v₁, r₁⟩ := ih (Check.litRev l ++ R) (by simp [Check.litRev, isLit]) f o z c v hz'
      obtain ⟨v₂, r₂⟩ := lit_run Zb (f && Ls.isEmpty) l R (bit_none_of_isLit hR) _
        (z + nz Ls f) (c + Ls.length) (by rw [nz_cons] at hz; omega) v₁
      refine ⟨v₂, ?_⟩
      have e : (l :: Ls).reverse.flatMap Check.litRev ++ R =
          Ls.reverse.flatMap Check.litRev ++ (Check.litRev l ++ R) := by simp
      rw [e]
      refine runLe_cast (r₁.trans r₂) ?_ ?_
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]; nlinarith
      · rw [show walkF (l :: Ls) f false z =
            litCl (f && Ls.isEmpty) false (z + nz Ls f) l :: walkF Ls f false z from rfl,
          nz_cons, hR]
        simp [Nat.add_assoc]

/-- **The 3SAT emitter processes one clause.** Let $C$ be a clause, $Z_b$, $z$ and $c$ natural
numbers with $z + \mathrm{used}(C) \le Z_b$, where $\mathrm{used}(C) = \max(|C| - 1, 0)$, let $R$
be a token list that is empty or starts with a clause token, $o$ an output bit list and $v$ a
flag. Let $\mathrm{clRev}(C)$ be the tokens of $C$ as they lie on the token stack (a clause token,
then the tokens of its literals, last literal first), and let $D_1, \dots, D_k$ be the clauses of
$\mathrm{chain}(C, z)$. Then there is a flag $v'$ such that the 3SAT emitter machine, started at
its start label with flag $v$, token stack $\mathrm{clRev}(C)$ followed by $R$, output stack $o$,
fresh counter $z$, clause count $c$ and empty scratch counters, reaches in at most
$|\mathrm{clRev}(C)| \cdot (6 Z_b + 15)$ steps its start label with flag $v'$, token stack $R$,
output stack $\mathrm{enc}(D_1) \cdots \mathrm{enc}(D_k)$ followed by $o$, fresh counter
$z + \mathrm{used}(C)$, clause count $c + k$ and empty scratch counters, where $\mathrm{enc}$ is
the binary clause encoding. -/
theorem clause_run (Zb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (o : List Bool) (z c : ℕ) (hz : z + used C ≤ Zb) (v : Bool) :
    ∃ v', RunLe prog ((Check.clRev C).length * (6 * Zb + 15))
      ⟨some .start, v, st (Check.clRev C ++ R) o z c⟩
      ⟨some .start, v', st R ((chain C z).flatMap encodeClause ++ o) (z + used C)
        (c + (chain C z).length)⟩ := by
  have hRl : isLit R.head? = false := by rcases hR with rfl | h <;> simp [isLit, *]
  have hRb : R.head?.bind Sym.bit? = none := by rcases hR with rfl | h <;> simp [Sym.bit?, *]
  have r₁ := start_cl v o z c (C.reverse.flatMap Check.litRev ++ R)
  cases C with
  | nil =>
      have r₂ := clause_nil false o z c R hRl
      refine ⟨false, runLe_cast ((r₁.trans r₂).le le_rfl) ?_ ?_⟩
      · simp [Check.clRev]
      · simp [chain, used, encodeClause]
  | cons l Ls =>
      have e : (l :: Ls).reverse.flatMap Check.litRev ++ R =
          Ls.reverse.flatMap Check.litRev ++ (Check.litRev l ++ R) := by simp
      rw [e] at r₁
      have r₂ := clause_lit false o z c _ (isLit_litRev Ls.reverse l R)
      have hz' : z + nz Ls true + (if true && Ls.isEmpty then 0 else 1) ≤ Zb := by
        rw [Nat.add_assoc, ← nz_cons l]; simpa [nz, used] using hz
      obtain ⟨v₃, r₃⟩ := lits_run Zb Ls (Check.litRev l ++ R) (by simp [Check.litRev, isLit]) true
        o z c true (by omega)
      obtain ⟨v₄, r₄⟩ := lit_run Zb (true && Ls.isEmpty) l R hRb _ (z + nz Ls true)
        (c + Ls.length) hz' v₃
      refine ⟨v₄, ?_⟩
      rw [show Check.clRev (l :: Ls) ++ R =
        Sym.cl :: (Ls.reverse.flatMap Check.litRev ++ (Check.litRev l ++ R)) by simp [Check.clRev]]
      have r := ((r₁.trans r₂).le le_rfl).trans (r₃.trans r₄)
      refine runLe_cast r ?_ ?_
      · have h1 := Check.litRev_flatMap_length_ge Ls
        have hb : 1 ≤ (Check.litRev l).length := by simp [Check.litRev]
        have h3 := Nat.mul_le_mul_right (6 * Zb + 14) h1
        rw [clRev_length, List.flatMap_cons, List.length_append]
        nlinarith
      · rw [← walkF_chain _ (List.cons_ne_nil l Ls), hRl]
        rcases Ls with _ | ⟨l', Ls⟩
        · simp [walkF, nz, used]
        · simp [walkF, walkF_length, nz, used, Nat.add_assoc]

/-- **The 3SAT emitter processes a whole formula.** Let $\varphi = C_1 \cdots C_m$ be a CNF
formula, $u = \sum_{i=1}^{m} \max(|C_i| - 1, 0)$ the number of fresh variables its 3SAT
translation uses, $Z_b \ge u$ a natural number, $R$ a token list that is empty or starts with a
clause token, $o$ an output bit list and $v$ a flag. Let $T$ be the token list
$\mathrm{clRev}(C_m) \cdots \mathrm{clRev}(C_1)$, where $\mathrm{clRev}(C)$ is the list of tokens
of $C$ as they lie on the token stack, and let $D_1, \dots, D_k$ be the clauses of the 3SAT
translation $\mathrm{to3}(\varphi)$. Then there is a flag $v'$ such that the 3SAT emitter machine,
started at its start label with flag $v$, token stack $T$ followed by $R$, output stack $o$,
fresh counter $0$, clause count $0$ and empty scratch counters, reaches in at most
$|T| \cdot (6 Z_b + 15)$ steps its start label with flag $v'$, token stack $R$, output stack
$\mathrm{enc}(D_1) \cdots \mathrm{enc}(D_k)$ followed by $o$, fresh counter $u$, clause count $k$
and empty scratch counters, where $\mathrm{enc}$ is the binary clause encoding. -/
theorem formula_run (Zb : ℕ) :
    ∀ (φ : CNF) (R : List Sym), (R = [] ∨ R.head? = some .cl) → ∀ (o : List Bool) (v : Bool),
      (to3Aux φ).1 ≤ Zb →
      ∃ v', RunLe prog ((φ.reverse.flatMap Check.clRev).length * (6 * Zb + 15))
        ⟨some .start, v, st (φ.reverse.flatMap Check.clRev ++ R) o 0 0⟩
        ⟨some .start, v', st R ((to3 φ).flatMap encodeClause ++ o) (to3Aux φ).1
          (to3 φ).length⟩ := by
  intro φ
  induction φ with
  | nil =>
      intro R _ o v _
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [to3, to3Aux])⟩
  | cons C φ ih =>
      intro R hR o v hz
      have h1 : to3 (C :: φ) = chain C (to3Aux φ).1 ++ to3 φ := rfl
      have h2 : (to3Aux (C :: φ)).1 = (to3Aux φ).1 + used C := rfl
      have hz' : (to3Aux φ).1 + used C ≤ Zb := h2 ▸ hz
      obtain ⟨v₁, r₁⟩ := ih (Check.clRev C ++ R) (Or.inr rfl) o v (by omega)
      obtain ⟨v₂, r₂⟩ := clause_run Zb C R hR _ _ _ hz' v₁
      refine ⟨v₂, ?_⟩
      have e : (C :: φ).reverse.flatMap Check.clRev ++ R =
          φ.reverse.flatMap Check.clRev ++ (Check.clRev C ++ R) := by simp
      rw [e]
      refine runLe_cast (r₁.trans r₂) ?_ ?_
      · simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.length_append]
        nlinarith
      · rw [h1, h2]
        simp [Nat.add_comm]

end Loops

/-! ### The emitter -/

/-- **Repeating a single bit.** For every bit $x$ and every $n \in \mathbb{N}$, the repeated block
$\mathrm{rep}([x], n)$ is the list consisting of $n$ copies of $x$. -/
theorem rep_single (x : Bool) (n : ℕ) : rep [x] n = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- **The SAT-to-3SAT emitter writes the encoded translation in quadratic time.** Let $\varphi$ be
a CNF formula, $o$ a list of bits and $T$ the token sequence of $\varphi$. Start the emitter
machine at its start label, with any internal state, with the token stack holding $T$ reversed
(so that the first token of $T$ is at the bottom), the output stack holding $o$, and every other
stack empty. Then after at most $8(|T| + 1)^2$ steps the machine reaches its label
$\mathrm{done}$, with some internal state and stack contents in which the output stack, read from
the top, holds the binary code of the SAT-to-3SAT translation of $\varphi$ followed by $o$. -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (8 * ((toks φ).length + 1) ^ 2) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = encodeCNF (to3 φ) ++ o := by
  have hSt : St = st ((toks φ).reverse) o 0 0 := by
    funext k
    cases k
    · exact hT
    · exact hO
    all_goals exact h0 _ (by decide) (by decide)
  obtain ⟨h1, h2⟩ := to3Aux_le φ
  obtain ⟨v₁, r₁⟩ := formula_run (toks φ).length φ [] (Or.inl rfl) o v h1
  rw [List.append_nil, ← Check.toks_reverse, List.length_reverse] at r₁
  set X := (to3 φ).flatMap encodeClause ++ o with hX
  have r₂ := start_nil v₁ X (to3Aux φ).1 (to3 φ).length
  have r₃ := xferE_run (M := prog) (self := .fin) (next := .done) (k := .C) (o := .O)
    (ys := [true]) rfl (by decide) Sym.cl (to3 φ).length true
    (st [] (false :: X) (to3Aux φ).1 (to3 φ).length) rfl
  have h3 : (to3 φ).length ≤ (toks φ).length := h2
  have hb : (toks φ).length * (6 * (toks φ).length + 15) + (1 + ((to3 φ).length + 1)) ≤
      8 * ((toks φ).length + 1) ^ 2 := by nlinarith
  rw [hSt]
  exact ⟨_, _, (r₁.trans ((r₂.trans r₃).le le_rfl)).mono hb, by simp [hX, encodeCNF, rep_single]⟩

end Cslib.Complexity.Karp.Emit3
