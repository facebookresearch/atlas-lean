/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.SatCheck

/-!
# SAT ≤ 3-COLOR, component 2: the emitter machine

A `TM2` machine that walks the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes the 3-COLOR instance `toCol φ` onto the output stack
`O`, so that `O` reads the instance top-first (`run`).

* `toCol φ` is `next` in unary, then the edges of `colSt φ` in reverse emission order, so the
  machine pushes every edge `(u, v)` in emission order as `false`, `v` ones, `false`, `u` ones
  (`out`), and at the end `false` and `next` ones.
* The token stack lists the clauses last-first and, per clause, the literals last-first: the
  order in which `colSt` walks them. The next free vertex is the unary counter `N`, the current
  OR output the counter `R`. Earlier occurrences lie on `D`, latest on top, each as a marker
  `lit p` above its name bits and its literal vertex `L'` in unary (`dTok`).
* Every edge endpoint is a counter (`N`, `R`, or `U`, which holds an earlier `L'`) plus a
  constant. A copy site (`Site`) pushes a constant block and then a counter's value in ones,
  restoring the counter through the scratch stack `W` (`site_run`); fixed lists of sites
  (`chain_run`) push the occurrence triangle, the consistency edges, the OR gadget, the clause
  end, the empty clause and the vertex count.
* A new occurrence walks `D`, comparing names with `cmpB` (restored with `moveB_restore`); on a
  match it moves the earlier `L'` to `U` and pushes the consistency edges (`consEdges`). The walk
  moves `D` to `E`, which is moved back before the occurrence goes on `D`. `N` is advanced after
  the occurrence's edges: by `2` for a clause's first literal (flag `F`), by `5` after an OR
  gadget, with `R` set to the new output.

The proof follows the CLIQUE emitter: one-step lemmas on the quiescent states `MS.stk`, the walk
over `D` by induction (`walk_run`), then literals, clauses and the formula by forward induction,
with the size invariant `Sz` bounding the counters and `D`. The step count is cubic in
`|toks φ|`; `run` states it as `500 (|toks φ| + 1)⁴`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitColor

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier

/-! ### The output, edge by edge -/

/-- **Bit encoding of an edge.** The bits of an edge $(u, v)$ in the edge-list encoding of a
graph: $u$ copies of true, then false, then $v$ copies of true, then false. -/
def eB (e : ℕ × ℕ) : List Bool :=
  List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- **Bits pushed for a list of edges.** For a list of edges $e_1, \dots, e_k$ (pairs of
natural numbers), the output is the concatenation $b(e_k) \cdots b(e_1)$, where $b(u, v)$ is
$u$ ones, a zero, $v$ ones and a zero.

This is what the output stack gains, read top-first, when the edges are pushed in the order
$e_1, \dots, e_k$. -/
def out (em : List (ℕ × ℕ)) : List Bool := em.reverse.flatMap eB

theorem out_append (xs ys : List (ℕ × ℕ)) : out (xs ++ ys) = out ys ++ out xs := by
  simp [out]

theorem toCol_eq (φ : CNF) :
    toCol φ = List.replicate (colSt φ).next true ++ false :: out (colSt φ).em := rfl

/-! ### The machine -/

/-- **Stacks of the 3-coloring emitter.** The emitter has thirteen stacks: $T$ (tokens), $O$
(output), $N$ (the next free vertex), $R$ (the current OR output), $D$ (earlier occurrences),
$E$ (the walk's other side), $A$ (the current name), $P$ (its polarity), $F$ (the first-literal
flag), $U$ (an earlier literal vertex), and the scratch stacks $X$ and $B$ for comparisons and
$W$ for copies. -/
inductive K | T | O | N | R | D | E | A | P | F | U | X | B | W
  deriving DecidableEq

/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.O, K.N, K.R, K.D, K.E, K.A, K.P, K.F, K.U, K.X, K.B, K.W], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the 3-coloring emitter.** The output stack has the booleans (bits) as
its alphabet; every other stack has the token symbols as its alphabet.

The counter stacks hold only the clause-end symbol, used as a unary unit. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Counters read by copy sites of the 3-COLOR emitter.** The type with the three elements
$n, r, u$, naming the counters of the 3-coloring emitter that a copy site can read: the next free
vertex $n$, the current OR output $r$ and an earlier literal vertex $u$. -/
inductive Src | n | r | u
  deriving DecidableEq

/-- **Stack of a counter.** The counter $n$ (the next vertex) is held on stack $N$, the counter
$r$ (the OR output) on stack $R$, and the counter $u$ (an earlier literal vertex) on stack $U$. -/
def Src.k : Src → K
  | .n => .N
  | .r => .R
  | .u => .U

/-- **Unit symbol of a counter.** For each of the three counters read by copy sites of the
3-coloring emitter, the unit symbol in the alphabet of the counter's stack is the clause-end
token symbol. -/
def Src.unit : (s : Src) → Γ s.k
  | .n => Sym.cl
  | .r => Sym.cl
  | .u => Sym.cl

/-- **Copy sites of the 3-COLOR emitter.** The type of copy sites has 29 distinct elements:
$o_1, \dots, o_4$ for the occurrence triangle; $c_1, \dots, c_4$ and $d_1, \dots, d_4$ for the
consistency edges with an earlier occurrence of equal and of opposite polarity;
$r_1, \dots, r_{11}$ for the OR gadget; $e_1, e_2$ for the clause end; $z_1, z_2, z_3$ for the
empty clause; and one site for the vertex count. Equality of sites is decidable. -/
inductive Site
  | o1 | o2 | o3 | o4 | c1 | c2 | c3 | c4 | d1 | d2 | d3 | d4
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | e1 | e2 | z1 | z2 | z3 | fin
  deriving DecidableEq

/-- **The copy sites of the 3-COLOR emitter, listed.** The list of all copy sites of the 3-COLOR
emitter, each exactly once, in the order $o_1, \dots, o_4$, $c_1, \dots, c_4$, $d_1, \dots, d_4$,
$r_1, \dots, r_{11}$, $e_1, e_2$, $z_1, z_2, z_3$ and the vertex-count site. -/
def Site.all : List Site :=
  [.o1, .o2, .o3, .o4, .c1, .c2, .c3, .c4, .d1, .d2, .d3, .d4, .r1, .r2, .r3, .r4, .r5, .r6, .r7,
    .r8, .r9, .r10, .r11, .e1, .e2, .z1, .z2, .z3, .fin]

/-- The sites, enumerated. -/
instance Site.instFintypeEnumFix : Fintype Site :=
  Fintype.ofList Site.all (fun x => by cases x <;> decide)

/-- **Counter copied by a copy site.** In the 3-coloring emitter, the sites $c_2$, $c_4$,
$d_2$ and $d_4$ copy the earlier-literal counter $U$, the sites $r_4$, $e_1$ and $e_2$ copy the
OR-output counter $R$, and every other site copies the next-vertex counter $N$. -/
def Site.src : Site → Src
  | .c2 | .c4 | .d2 | .d4 => .u
  | .r4 | .e1 | .e2 => .r
  | _ => .n

/-- **Constant block of a copy site.** The list of bits a copy site of the 3-coloring emitter
pushes onto the output stack below its counter copy, read top-first and written with $1$ for
true and $0$ for false: $o_1$: 10, $o_2$: 0, $o_3$: 0110, $o_4$: 10110; $c_1$: 10, $c_2$: 0,
$c_3$: 0, $c_4$: 10; $d_1$: 0, $d_2$: 0, $d_3$: 10, $d_4$: 10; $r_1$: 110, $r_2$: 0,
$r_3$: 1110, $r_4$: 0, $r_5$: 1110, $r_6$: 110, $r_7$: 11110, $r_8$: 110, $r_9$: 11110,
$r_{10}$: 1110, $r_{11}$: 11110110; $e_1$: 010, $e_2$: 0110; $z_1$: 00, $z_2$: 010,
$z_3$: 0110; and the vertex-count site: 0. -/
def Site.top : Site → List Bool
  | .o1 => [true, false]
  | .o2 => [false]
  | .o3 => [false, true, true, false]
  | .o4 => [true, false, true, true, false]
  | .c1 => [true, false]
  | .c2 => [false]
  | .c3 => [false]
  | .c4 => [true, false]
  | .d1 => [false]
  | .d2 => [false]
  | .d3 => [true, false]
  | .d4 => [true, false]
  | .r1 => [true, true, false]
  | .r2 => [false]
  | .r3 => [true, true, true, false]
  | .r4 => [false]
  | .r5 => [true, true, true, false]
  | .r6 => [true, true, false]
  | .r7 => [true, true, true, true, false]
  | .r8 => [true, true, false]
  | .r9 => [true, true, true, true, false]
  | .r10 => [true, true, true, false]
  | .r11 => [true, true, true, true, false, true, true, false]
  | .e1 => [false, true, false]
  | .e2 => [false, true, true, false]
  | .z1 => [false, false]
  | .z2 => [false, true, false]
  | .z3 => [false, true, true, false]
  | .fin => [false]

/-- **Control labels of the 3-coloring emitter.** `init`: palette; `cls`: next clause; `lits`:
next literal; `lp`, `nm`: pop the polarity and the name; `walk` to `dr`: walk `D` (compare,
restore, select the polarity case, move the name and the vertex to `E`, or the vertex to `U`
and push the consistency edges); `back`: move `E` back to `D`; `putN` to `putP`: put the
occurrence on `D`; `aft`, `fA` to `fC`: set `R` and advance `N`; `clr`: clear `R`; `zN`:
advance `N` after an empty clause; `pre j`, `cpA j`, `cpB j`: copy site `j`; `done`: halt. -/
inductive Lab
  | init | cls | lits | lp | nm | walk | cmp | rsA (e : Bool) | rsD (e : Bool) | sel
  | mvN (r : Option Bool) | skU | mvU (b : Bool) | dr | back | putN | putW | putA | putB | putP
  | aft | fA (b : Bool) | fB (b : Bool) | fC (b : Bool) | clr (b : Bool) | zN
  | pre (j : Site) | cpA (j : Site) | cpB (j : Site) | done
  deriving DecidableEq

/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.init, .cls, .lits, .lp, .nm, .walk, .cmp, .sel, .mvN none, .skU, .dr, .back, .putN,
        .putW, .putA, .putB, .putP, .aft, .zN, .done] ++
      ([true, false].flatMap fun b =>
        [Lab.rsA b, .rsD b, .mvN (some b), .mvU b, .fA b, .fB b, .fC b, .clr b]) ++
      (Site.all.flatMap fun j => [Lab.pre j, .cpA j, .cpB j]))
    (fun x => by
      cases x <;> (try rename_i a; cases a) <;> (try rename_i a; cases a) <;> decide)

/-- **Successor label of a copy site.** The label at which the 3-COLOR emitter continues
after a copy site. In each of the chains $o_1, \dots, o_4$; $c_1, \dots, c_4$; $d_1, \dots, d_4$;
$r_1, \dots, r_{11}$; $e_1, e_2$; $z_1, z_2, z_3$, every site but the last continues with
$\mathtt{pre}$ of the next site of its chain. The last sites continue as follows: $o_4$ with
$\mathtt{lp}$, $c_4$ and $d_4$ with $\mathtt{dr}$, $r_{11}$ with $\mathtt{clr}(\mathrm{true})$,
$e_2$ with $\mathtt{clr}(\mathrm{false})$, $z_3$ with $\mathtt{zN}$, and the site
$\mathrm{fin}$ with $\mathtt{done}$. -/
def Site.nxt : Site → Lab
  | .o1 => .pre .o2
  | .o2 => .pre .o3
  | .o3 => .pre .o4
  | .o4 => .lp
  | .c1 => .pre .c2
  | .c2 => .pre .c3
  | .c3 => .pre .c4
  | .c4 => .dr
  | .d1 => .pre .d2
  | .d2 => .pre .d3
  | .d3 => .pre .d4
  | .d4 => .dr
  | .r1 => .pre .r2
  | .r2 => .pre .r3
  | .r3 => .pre .r4
  | .r4 => .pre .r5
  | .r5 => .pre .r6
  | .r6 => .pre .r7
  | .r7 => .pre .r8
  | .r8 => .pre .r9
  | .r9 => .pre .r10
  | .r10 => .pre .r11
  | .r11 => .clr true
  | .e1 => .pre .e2
  | .e2 => .clr false
  | .z1 => .pre .z2
  | .z2 => .pre .z3
  | .z3 => .zN
  | .fin => .done

/-- **Literal-marker test.** For an optional symbol (the top of a stack, absent when the stack is
empty), the test is true exactly when the symbol is present and is a literal marker of some
polarity; it is false for every other symbol and for an empty stack. -/
def isLit : Option Sym → Bool
  | some (.lit _) => true
  | _ => false

/-- **Reading unary units.** The partial reading of token symbols as unary units used by the
3-coloring emitter: the clause-end symbol is read as the bit true, and every other symbol has
no reading, so it ends a run of units. -/
def unitOf : Sym → Option Bool
  | .cl => some true
  | _ => none

/-- **Bits of the palette triangle.** The bits pushed for the edges $(0, 1)$, $(0, 2)$,
$(1, 2)$ in this order, that is, for the triangle on the palette vertices $0$, $1$, $2$. -/
def pal : List Bool := out [(0, 1), (0, 2), (1, 2)]

/-- **The 3-COLOR emitter machine.** The TM2 program, with the stacks, stack alphabets and
labels of the emitter and a Boolean local state, that builds the 3-COLOR instance of a CNF
formula from its token stack. It first pushes the palette triangle on the output stack and
adds $3$ to the next free vertex $N$. It then reads the clauses one at a time. For each
literal occurrence it pushes the occurrence triangle, walks the earlier occurrences comparing
variable names, and for each one with the same variable pushes the consistency edges for
equal or opposite polarity; it then records the occurrence. After the first literal of a
clause it adds $N$ to the current OR output $R$ and adds $2$ to $N$; after a later literal it
pushes an OR gadget with inputs $N$ and $R$, sets $R$ to $N + 4$ and adds $5$ to $N$. At the
end of a clause it joins $R$ to the vertices $1$ and $2$ and clears $R$; an empty clause gets
the vertex $N$ joined to $0$, $1$ and $2$, and $N$ is increased by $1$. When the tokens run
out it pushes the vertex count $N$ and halts. Apart from the palette, every edge is pushed by
copy sites, each of which pushes a constant block of bits and then the value of a counter in
ones, restoring the counter through a scratch stack. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .init => pushList .O pal.reverse <| pushList .N [Sym.cl, Sym.cl, Sym.cl] <|
      .goto fun _ => .cls
  | .cls => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .pre .fin) <|
      .pop .T (fun s _ => s) <| .peek .T (fun _ o => isLit o) <| .branch id
        (.push .F (fun _ => Sym.cl) <| .goto fun _ => .lits) (.goto fun _ => .pre .z1)
  | .lits => .peek .T (fun _ o => isLit o) <| .branch id (.goto fun _ => .pre .o1)
      (.goto fun _ => .pre .e1)
  | .lp => .pop .T (fun _ o => o == some (.lit true)) <| .push .P (fun s => Sym.lit s) <|
      .goto fun _ => .nm
  | .nm => moveB .T .A Sym.bit? Sym.bit .nm .walk
  | .walk => .peek .D (fun _ o => o.isNone) <| .branch id (.goto fun _ => .back) <|
      .pop .D (fun _ o => o == some (.lit true)) <| .push .E (fun s => Sym.lit s) <|
        .goto fun _ => .cmp
  | .cmp => cmpB .A .D .X .B Sym.bit? Sym.bit? Sym.bit Sym.bit .cmp (.rsA true) (.rsA false)
  | .rsA e => moveB .X .A Sym.bit? Sym.bit (.rsA e) (.rsD e)
  | .rsD e => moveB .B .D Sym.bit? Sym.bit (.rsD e) (if e then .sel else .mvN none)
  | .sel => .peek .E (fun _ o => o == some (.lit true)) <|
      .peek .P (fun s o => s == (o == some (.lit true))) <| .goto fun s => .mvN (some s)
  | .mvN r => moveB .D .E Sym.bit? Sym.bit (.mvN r) (r.elim .skU .mvU)
  | .skU => moveB .D .E unitOf (fun _ => Sym.cl) .skU .walk
  | .mvU b => moveB .D .U unitOf (fun _ => Sym.cl) (.mvU b) (.pre (if b then .c1 else .d1))
  | .dr => xfer .U [⟨.E, Sym.cl⟩] .dr .walk
  | .back => .peek .E (fun _ o => o.isNone) <| .branch id (.goto fun _ => .putN) <|
      .peek .E (fun _ o => o == some .cl) <| .branch id
        (.pop .E (fun s _ => s) <| .push .D (fun _ => Sym.cl) <| .goto fun _ => .back) <|
      .peek .E (fun _ o => isLit o) <| .branch id
        (.pop .E (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
          .goto fun _ => .back)
        (.pop .E (fun _ o => o == some (.bit true)) <| .push .D (fun s => Sym.bit s) <|
          .goto fun _ => .back)
  | .putN => xfer .N [⟨.D, Sym.cl⟩, ⟨.W, Sym.cl⟩] .putN .putW
  | .putW => xfer .W [⟨.N, Sym.cl⟩] .putW .putA
  | .putA => moveB .A .B Sym.bit? Sym.bit .putA .putB
  | .putB => moveB .B .D Sym.bit? Sym.bit .putB .putP
  | .putP => .pop .P (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
      .goto fun _ => .aft
  | .aft => decr .F (.pre .r1) (.fA true)
  | .fA b => xfer .N [⟨.R, Sym.cl⟩, ⟨.W, Sym.cl⟩] (.fA b) (.fB b)
  | .fB b => xfer .W [⟨.N, Sym.cl⟩] (.fB b) (.fC b)
  | .fC b => pushList .R (cnt Sym.cl (if b then 0 else 4)) <|
      emit .N (cnt Sym.cl (if b then 2 else 5)) .lits
  | .clr b => xfer .R [] (.clr b) (if b then .fA false else .cls)
  | .zN => emit .N [Sym.cl] .cls
  | .pre j => emitR .O j.top (.cpA j)
  | .cpA j => xfer j.src.k [⟨.O, true⟩, ⟨.W, Sym.cl⟩] (.cpA j) (.cpB j)
  | .cpB j => xfer .W [⟨j.src.k, j.src.unit⟩] (.cpB j) j.nxt
  | .done => .halt

/-- **Start label of the 3-coloring emitter.** The emitter machine starts at its palette label,
the label whose instruction pushes the palette triangle onto the output stack. -/
def start : Lab := .init

/-! ### Quiescent states -/

/-- **Quiescent states of the 3-COLOR emitter.** A quiescent state records the contents of
the token stack $T$ and of the stacks $D$, $E$, $A$, $P$ (lists of token symbols), the content
of the output stack $O$ (a list of bits), and four natural numbers $n$, $r$, $f$, $u$: the
values of the counters $N$ (next free vertex), $R$ (current OR output), $F$ (first-literal flag)
and $U$ (an earlier literal vertex).

On the machine, $N$, $R$, $F$, $U$ hold that many clause tokens $\mathtt{cl}$ and the scratch
stacks $X$, $B$, $W$ are empty. -/
structure MS where
  /-- The token stack. -/
  t : List Sym
  /-- The output stack. -/
  o : List Bool
  /-- The next free vertex. -/
  n : ℕ
  /-- The current OR output. -/
  r : ℕ
  /-- Earlier occurrences. -/
  d : List Sym
  /-- The walk's other side. -/
  e : List Sym
  /-- The current name. -/
  a : List Sym
  /-- The current polarity. -/
  p : List Sym
  /-- The first-literal flag. -/
  f : ℕ
  /-- An earlier literal vertex. -/
  u : ℕ

/-- **Stacks of a quiescent state.** The stack contents of a quiescent state $m$ of the
3-coloring emitter: the token, output, earlier-occurrence, walk, name and polarity stacks hold
the corresponding lists of $m$; the counters $N$, $R$, $F$ and $U$ hold $n$, $r$, $f$ and $u$
copies of the clause-end symbol, where $n$, $r$, $f$, $u$ are the counter values of $m$; and
the scratch stacks $X$, $B$ and $W$ are empty. -/
def MS.stk (m : MS) : ∀ k, List (Γ k)
  | .T => m.t
  | .O => m.o
  | .N => cnt Sym.cl m.n
  | .R => cnt Sym.cl m.r
  | .D => m.d
  | .E => m.e
  | .A => m.a
  | .P => m.p
  | .F => cnt Sym.cl m.f
  | .U => cnt Sym.cl m.u
  | .X | .B | .W => []

/-- **Counter values of a quiescent state.** For a quiescent state $m$ of the 3-coloring emitter,
the value of the next-vertex counter is the next free vertex $n$ of $m$, that of the OR-output
counter is the current OR output $r$ of $m$, and that of the earlier-literal counter is the
earlier literal vertex $u$ of $m$. -/
def MS.val (m : MS) : Src → ℕ
  | .n => m.n
  | .r => m.r
  | .u => m.u

section MSLemmas

variable (m : MS)

@[simp] theorem stk_T : m.stk .T = m.t := rfl
@[simp] theorem stk_O : m.stk .O = m.o := rfl
@[simp] theorem stk_N : m.stk .N = List.replicate m.n Sym.cl := rfl
@[simp] theorem stk_R : m.stk .R = List.replicate m.r Sym.cl := rfl
@[simp] theorem stk_D : m.stk .D = m.d := rfl
@[simp] theorem stk_E : m.stk .E = m.e := rfl
@[simp] theorem stk_A : m.stk .A = m.a := rfl
@[simp] theorem stk_P : m.stk .P = m.p := rfl
@[simp] theorem stk_F : m.stk .F = List.replicate m.f Sym.cl := rfl
@[simp] theorem stk_U : m.stk .U = List.replicate m.u Sym.cl := rfl
@[simp] theorem stk_X : m.stk .X = [] := rfl
@[simp] theorem stk_B : m.stk .B = [] := rfl
@[simp] theorem stk_W : m.stk .W = [] := rfl

@[simp] theorem upd_T (x : List Sym) : update m.stk .T x = {m with t := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_O (x : List Bool) : update m.stk .O x = {m with o := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_D (x : List Sym) : update m.stk .D x = {m with d := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_E (x : List Sym) : update m.stk .E x = {m with e := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_A (x : List Sym) : update m.stk .A x = {m with a := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_P (x : List Sym) : update m.stk .P x = {m with p := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_R (j : ℕ) :
    update m.stk .R (List.replicate j Sym.cl) = {m with r := j}.stk := by
  funext k; cases k <;> rfl
theorem upd_F_nil : update m.stk .F [] = {m with f := 0}.stk := by
  funext k; cases k <;> rfl

theorem stk_src (s : Src) : m.stk s.k = cnt s.unit (m.val s) := by cases s <;> rfl

theorem val_le (s : Src) : m.val s ≤ m.n + m.r + m.u := by
  cases s <;> simp only [MS.val] <;> omega

end MSLemmas

@[simp] private theorem sym_beq (a b : Sym) : (a == b) = decide (a = b) := rfl

theorem run_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : Run prog k c d)
    (hk : k = k') (hd : d = d') : Run prog k' c d' := hk ▸ hd ▸ h

theorem runLe_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hk : k ≤ k') (hd : d = d') : RunLe prog k' c d' := hd ▸ h.mono hk

/-! ### Copy sites -/

/-- **Counters are not held on the output stack.** For each of the three counters read by copy
sites of the 3-coloring emitter, the stack of the counter is not the output stack $O$. -/
theorem Src.k_ne_O (s : Src) : s.k ≠ .O := by cases s <;> decide

theorem Src.k_ne_W (s : Src) : s.k ≠ .W := by cases s <;> decide

/-- **Copying a counter through $W$.** Let $s$ be a counter, $c$ a stack different from the stack
of $s$ and from $W$, and $x$ a symbol of $c$. Suppose the instruction at label $l_1$ pops the
stack of $s$ until it is empty, pushing $x$ onto $c$ and the unit symbol onto $W$ for each popped
symbol, then goes to $l_2$; and the instruction at $l_2$ pops $W$ until it is empty, pushing the
unit symbol of $s$ onto the stack of $s$ for each popped symbol, then goes to $\ell$. Then for
every $n$, every flag and all stacks $S$ in which the stack of $s$ holds $n$ unit symbols of $s$
and $W$ is empty, the emitter goes from label $l_1$ with stacks $S$ to label $\ell$ in exactly
$2n + 2$ steps, with some flag and the stacks $S$ except that $n$ copies of $x$ are pushed onto
$c$. -/
theorem dup_run (s : Src) {c : K} (x : Γ c) (hc : c ≠ s.k) (hcW : c ≠ .W) {l₁ l₂ next : Lab}
    (h₁ : prog l₁ = xfer s.k [⟨c, x⟩, ⟨.W, Sym.cl⟩] l₁ l₂)
    (h₂ : prog l₂ = xfer .W [⟨s.k, s.unit⟩] l₂ next) (val : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S s.k = cnt s.unit val) (hW : S .W = []) :
    ∃ v', Run prog (2 * val + 2) ⟨some l₁, v, S⟩
      ⟨some next, v', update S c (cnt x val ++ S c)⟩ := by
  have hsW := s.k_ne_W
  have r₁ := xfer_run h₁ (pair_nodupKeys x (Sym.cl : Γ .W) hcW) (by simp [hc.symm, hsW]) s.unit
    val v S hS
  set S₁ := addU [⟨c, x⟩, ⟨.W, Sym.cl⟩] val (update S s.k []) with hS₁
  have h₁W : S₁ .W = cnt (Sym.cl : Γ .W) val := by
    rw [hS₁, addU_pair_snd _ _ _ _ hcW.symm, update_of_ne hsW.symm, hW, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys s.unit) (by simp [hsW.symm]) (Sym.cl : Γ .W) val
    (Flag.tag false) S₁ h₁W
  have hfin : addU [⟨s.k, s.unit⟩] val (update S₁ .W []) = update S c (cnt x val ++ S c) := by
    funext k
    by_cases hks : k = s.k
    · subst hks
      rw [addU_single_self, update_of_ne hsW, hS₁, addU_pair_ne _ _ _ _ hc.symm hsW,
        update_self, update_of_ne hc.symm, hS, List.append_nil]
    rw [addU_single_ne _ _ _ hks]
    by_cases hkW : k = .W
    · subst hkW; rw [update_self, update_of_ne hcW.symm, hW]
    rw [update_of_ne hkW]
    by_cases hkc : k = c
    · subst hkc; rw [hS₁, addU_pair_fst, update_of_ne hc, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkW, update_of_ne hks, update_of_ne hkc]
  rw [hfin] at r₂
  exact ⟨_, (r₁.trans r₂).of_eq (by omega)⟩

/-- **Bit list of a copy site of the 3-COLOR emitter.** For a quiescent state $m$ of the 3-COLOR
emitter and a copy site $j$, the bit list of $j$ at $m$ is $v$ ones followed by the constant
block of $j$, where $v$ is the value in $m$ of the counter that $j$ copies. Read top-first, the
ones lie above the constant block. -/
def atom (m : MS) (j : Site) : List Bool := List.replicate (m.val j.src) true ++ j.top

/-- **Running a copy site of the 3-COLOR emitter.** Let $j$ be a copy site, $m$ a quiescent
state and $v$ a local state, and let $c$ be the value in $m$ of the counter that $j$ copies.
From the label that starts site $j$, with local state $v$, the machine runs in exactly
$2c + 3$ steps to the label where $j$ continues, in some local state and in the quiescent
state obtained from $m$ by pushing onto the output stack $c$ ones above the constant block of
$j$. -/
theorem site_run (j : Site) (m : MS) (v : Bool) :
    ∃ v', Run prog (2 * m.val j.src + 3) ⟨some (.pre j), v, m.stk⟩
      ⟨some j.nxt, v', {m with o := atom m j ++ m.o}.stk⟩ := by
  have r₁ := emitR_run (M := prog) (self := .pre j) (next := .cpA j) (k := .O) (ys := j.top) rfl
    v m.stk
  obtain ⟨v', r₂⟩ := dup_run j.src (true : Γ .O) (Ne.symm j.src.k_ne_O) (by decide)
    (l₁ := .cpA j) (l₂ := .cpB j) (next := j.nxt) rfl rfl (m.val j.src) v
    (update m.stk .O (j.top ++ m.stk .O))
    (by rw [update_of_ne j.src.k_ne_O]; exact stk_src m j.src) rfl
  have e : update (update m.stk .O (j.top ++ m.stk .O)) .O
      (cnt true (m.val j.src) ++ update m.stk .O (j.top ++ m.stk .O) .O) =
      {m with o := atom m j ++ m.o}.stk := by simp [atom]
  rw [e] at r₂
  exact ⟨v', (r₁.trans r₂).of_eq (by omega)⟩

/-- **Copy sites of the 3-COLOR emitter running in sequence.** Copy sites $j_1, \dots, j_k$ run in
sequence from label $\ell_0$ to label $\ell$ when $\ell_0$ is the entry label of $j_1$, the
continuation label of each $j_i$ with $i < k$ is the entry label of $j_{i+1}$, and the
continuation label of $j_k$ is $\ell$; for $k = 0$ this means $\ell_0 = \ell$. The condition is
a Boolean test. -/
def Chain : List Site → Lab → Lab → Bool
  | [], l₀, l => l₀ == l
  | j :: js, l₀, l => l₀ == .pre j && Chain js j.nxt l

/-- **Bits pushed by a sequence of copy sites of the 3-COLOR emitter.** For a quiescent state $m$
of the 3-COLOR emitter and copy sites $j_1, \dots, j_k$, the bits of the sequence at $m$ are the
bit lists at $m$ of $j_k, j_{k-1}, \dots, j_1$, concatenated in that order. Read top-first, the
bits of the last site lie on top. -/
def chainOut (m : MS) (js : List Site) : List Bool := (js.map (atom m)).reverse.flatten

@[simp] theorem chainOut_nil (m : MS) : chainOut m [] = [] := rfl

@[simp] theorem chainOut_cons (m : MS) (j : Site) (js : List Site) :
    chainOut m (j :: js) = chainOut m js ++ atom m j := by simp [chainOut]

theorem chainOut_o (m : MS) (x : List Bool) (js : List Site) :
    chainOut {m with o := x} js = chainOut m js := rfl

/-- **Running a sequence of copy sites of the 3-COLOR emitter.** Let copy sites
$j_1, \dots, j_k$ run in sequence from label $\ell_0$ to label $\ell$, and let $m$ be a quiescent
state of the 3-COLOR emitter whose counters $N$, $R$, $U$ have values $n$, $r$, $u$. Then for
every Boolean $v$ there is a Boolean $v'$ such that the emitter goes in at most
$k (2 (n + r + u) + 3)$ steps from label $\ell_0$ with internal state $v$ and the stacks of $m$
to label $\ell$ with internal state $v'$ and the stacks of $m$ with the bits of the sequence
$j_1, \dots, j_k$ at $m$ placed on top of the output stack. -/
theorem chain_run (js : List Site) : ∀ (m : MS) (l₀ l : Lab), Chain js l₀ l = true →
    ∀ v : Bool, ∃ v', RunLe prog (js.length * (2 * (m.n + m.r + m.u) + 3)) ⟨some l₀, v, m.stk⟩
      ⟨some l, v', {m with o := chainOut m js ++ m.o}.stk⟩ := by
  induction js with
  | nil =>
      intro m l₀ l h v
      simp only [Chain, beq_iff_eq] at h
      subst h
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) rfl⟩
  | cons j js ih =>
      intro m l₀ l h v
      simp only [Chain, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨v₁, r₁⟩ := site_run j m v
      obtain ⟨v₂, r₂⟩ := ih {m with o := atom m j ++ m.o} j.nxt l h v₁
      refine ⟨v₂, runLe_cast ((r₁.le le_rfl).trans r₂) ?_ ?_⟩
      · have := val_le m j.src
        simp only [List.length_cons, add_mul, one_mul]
        omega
      · simp [chainOut_o, List.append_assoc]

/-! ### One-step lemmas -/

/-- **Walk tokens.** A symbol is a walk token, one the walk moves between the stacks $D$ and $E$,
when it is a name bit, a literal marker or the clause symbol (which also serves as the unary
unit); the value symbols and the dead symbol are not walk tokens. -/
def isTok : Sym → Bool
  | .bit _ | .lit _ | .cl => true
  | _ => false

section Steps

variable (m : MS) (v : Bool)

theorem init_step : Run prog 1 ⟨some .init, v, m.stk⟩
    ⟨some .cls, v, {m with o := pal ++ m.o, n := m.n + 3}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, stepAux_pushList, TM2.stepAux]
  congr 1
  funext k; cases k <;> simp [List.replicate_succ]

theorem cls_nil (h : m.t = []) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some (.pre .fin), true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem cls_lit (R : List Sym) (h : m.t = .cl :: R) (hR : isLit R.head? = true) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some .lits, true, {m with t := R, f := m.f + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_T, h, List.head?_cons, Option.isNone_some, id,
      Bool.cond_false, List.tail_cons, upd_T, hR, Bool.cond_true]
    congr 1; funext k; cases k <;> simp [List.replicate_succ])

theorem cls_emp (R : List Sym) (h : m.t = .cl :: R) (hR : isLit R.head? = false) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some (.pre .z1), false, {m with t := R}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h, hR])

theorem lits_lit (h : isLit m.t.head? = true) :
    Run prog 1 ⟨some .lits, v, m.stk⟩ ⟨some (.pre .o1), true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem lits_end (h : isLit m.t.head? = false) :
    Run prog 1 ⟨some .lits, v, m.stk⟩ ⟨some (.pre .e1), false, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem lp_step (b : Bool) (R : List Sym) (h : m.t = .lit b :: R) :
    Run prog 1 ⟨some .lp, v, m.stk⟩ ⟨some .nm, b, {m with t := R, p := .lit b :: m.p}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem walk_nil (h : m.d = []) :
    Run prog 1 ⟨some .walk, v, m.stk⟩ ⟨some .back, true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem walk_lit (b : Bool) (R : List Sym) (h : m.d = .lit b :: R) :
    Run prog 1 ⟨some .walk, v, m.stk⟩ ⟨some .cmp, b, {m with d := R, e := .lit b :: m.e}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem sel_step (q b : Bool) (R : List Sym) (hE : m.e = .lit q :: R) (hP : m.p = [.lit b]) :
    Run prog 1 ⟨some .sel, v, m.stk⟩ ⟨some (.mvN (some (q == b))), q == b, m.stk⟩ :=
  Run.single (by cases q <;> cases b <;> simp [prog, TM2.stepAux, hE, hP])

theorem putP_step (b : Bool) (h : m.p = [.lit b]) :
    Run prog 1 ⟨some .putP, v, m.stk⟩ ⟨some .aft, b, {m with p := [], d := .lit b :: m.d}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem back_nil (h : m.e = []) :
    Run prog 1 ⟨some .back, v, m.stk⟩ ⟨some .putN, true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem back_step (s : Sym) (hs : isTok s = true) (R : List Sym) (h : m.e = s :: R) :
    ∃ v', Run prog 1 ⟨some .back, v, m.stk⟩
      ⟨some .back, v', {m with e := R, d := s :: m.d}.stk⟩ := by
  cases s with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, isLit, h])⟩
  | lit q => exact ⟨q, Run.single (by cases q <;> simp [prog, TM2.stepAux, isLit, h])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩
  | val _ => simp [isTok] at hs
  | dead => simp [isTok] at hs

theorem aft_pos (h : m.f = 1) :
    ∃ v', Run prog 1 ⟨some .aft, v, m.stk⟩ ⟨some (.fA true), v', {m with f := 0}.stk⟩ := by
  have := decr_run_pos (M := prog) (self := .aft) rfl v (S := m.stk) (x := Sym.cl) (r := [])
    (by simp [h])
  rw [upd_F_nil] at this
  exact ⟨_, this⟩

theorem aft_zero (h : m.f = 0) :
    ∃ v', Run prog 1 ⟨some .aft, v, m.stk⟩ ⟨some (.pre .r1), v', m.stk⟩ :=
  ⟨_, decr_run_zero (M := prog) (self := .aft) rfl v (by simp [h])⟩

theorem fC_step (b : Bool) : Run prog 1 ⟨some (.fC b), v, m.stk⟩ ⟨some .lits, v,
    {m with r := m.r + (if b then 0 else 4), n := m.n + (if b then 2 else 5)}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, emit, stepAux_pushList, TM2.stepAux]
  congr 1
  funext k; cases k <;> cases b <;> simp [List.replicate_succ]

theorem zN_step : Run prog 1 ⟨some .zN, v, m.stk⟩ ⟨some .cls, v, {m with n := m.n + 1}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, emit, stepAux_pushList, TM2.stepAux]
  congr 1; funext k; cases k <;> simp [List.replicate_succ]

end Steps

/-! ### Phases -/

/-- **Name of a variable.** The name of a variable $x \in \mathbb{N}$ is the list of name-bit
tokens $\mathtt{bit}(b)$, one for each bit $b$ of Mathlib's binary encoding of $x$ (least
significant bit first, empty for $x = 0$), in that order; this is how the stacks $A$ and $D$
hold it. -/
abbrev name (x : ℕ) : List Sym := (encodeNat x).map Sym.bit

/-- **Encoding of an earlier occurrence on stack $D$.** An occurrence $q = (x, p, L, M)$ of the
literal $(x, p)$ with vertices $L$ and $M$ is written, top first, as the polarity marker of $p$,
then the name bits of the variable $x$, then $L$ unit symbols (its literal vertex in unary);
the vertex $M$ is not recorded. -/
def dTok (q : ℕ × Bool × ℕ × ℕ) : List Sym := .lit q.2.1 :: (name q.1 ++ cnt Sym.cl q.2.2.1)

section Phases

variable (m : MS) (v : Bool)

private theorem isBitBlock_map (u : List Bool) : IsBitBlock Sym.bit? (u.map Sym.bit) u := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?]

private theorem isBitBlock_map_reverse (u : List Bool) :
    IsBitBlock Sym.bit? (u.map Sym.bit).reverse u.reverse := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?, List.map_reverse]

theorem isBitBlock_cnt (j : ℕ) : IsBitBlock unitOf (cnt Sym.cl j) (List.replicate j true) := by
  simp [IsBitBlock, unitOf]

theorem bit_inv (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

/-- **Moving the current name from $T$ to $A$.** Let $m$ be a quiescent state of the 3-COLOR
emitter whose stack $A$ is empty, $v$ a bit, $x \in \mathbb{N}$, and $R$ a list of token symbols
whose first element, if any, is not a name bit. If the token stack $T$ of $m$ is the name of $x$
in reverse order followed by $R$, then for some bit $v'$ the emitter machine runs in exactly
$k + 1$ steps, where $k$ is the length of the binary encoding of $x$, from label $\mathtt{nm}$
with internal bit $v$ and the stacks of $m$ to label $\mathtt{walk}$ with internal bit $v'$ and
the stacks of the quiescent state obtained from $m$ by setting $T$ to $R$ and $A$ to the name
of $x$. -/
theorem nm_run (x : ℕ) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (h : m.t = (name x).reverse ++ R) (hA : m.a = []) :
    ∃ v', Run prog ((encodeNat x).length + 1) ⟨some .nm, v, m.stk⟩
      ⟨some .walk, v', {m with t := R, a := name x}.stk⟩ := by
  obtain ⟨v', S', r, hT, hA', hk⟩ := moveB_run (M := prog) (self := .nm) (next := .walk)
    (a := .T) (b := .A) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x).reverse
    (name x).reverse R v m.stk (by simp [h]) (isBitBlock_map_reverse _) hR
  have hS : S' = {m with t := R, a := name x}.stk := by
    funext k; cases k <;> simp [hT, hA', hA, hk, List.map_reverse]
  rw [hS, List.length_reverse] at r
  exact ⟨v', r⟩

/-- **Name comparison in the 3-COLOR emitter.** Let $m$ be a quiescent state, $u$ and $w$ lists
of bits, and $R$ a list of symbols that is empty or does not start with a name bit. If stack $A$
of $m$ holds $u$ as name bits and stack $D$ holds $w$ as name bits followed by $R$, then from
label $\mathsf{cmp}$ with the stacks of $m$ and any flag, the emitter reaches, in at most
$3|w| + 3$ steps, label $\mathsf{sel}$ if $u = w$ and label $\mathsf{mvN}(\mathrm{none})$
otherwise, with the stacks of $m$ restored and some flag. -/
theorem cmp_run (u w : List Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (hA : m.a = u.map Sym.bit) (hD : m.d = w.map Sym.bit ++ R) :
    ∃ v', RunLe prog (3 * w.length + 3) ⟨some .cmp, v, m.stk⟩
      ⟨some (if u = w then .sel else .mvN none), v', m.stk⟩ := by
  have hd : Distinct4 K.A K.D K.X K.B :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1A, h1D, h1X, h1B, h1k⟩ := cmpB_run (M := prog)
    (self := .cmp) (eqL := .rsA true) (neL := .rsA false) (a := .A) (b := .D)
    (ta := .X) (tb := .B) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) rfl
    hd u w (u.map Sym.bit) [] (w.map Sym.bit) R v m.stk (by simp [hA]) hD (isBitBlock_map u)
    (isBitBlock_map w) rfl hR
  have hl : (if u = w then Lab.rsA true else Lab.rsA false) = Lab.rsA (decide (u = w)) := by
    split <;> simp_all
  rw [hl] at r₁
  obtain ⟨v₂, S₂, r₂, h2X, h2A, h2k⟩ := moveB_restore (M := prog)
    (self' := .rsA (decide (u = w))) (next := .rsD (decide (u = w))) (t := .X) (a := .A)
    (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?) rfl (by decide)
    (fun _ => rfl) bit_inv u cp (u.map Sym.bit) [] [] v₁ S₁ (isBitBlock_map u) hcu
    (by simpa using h1X) h1A rfl
  obtain ⟨v₃, S₃, r₃, h3B, h3D, h3k⟩ := moveB_restore (M := prog)
    (self' := .rsD (decide (u = w))) (next := if decide (u = w) then .sel else .mvN none)
    (t := .B) (a := .D) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?) rfl
    (by decide) (fun _ => rfl) bit_inv w cp (w.map Sym.bit) R [] v₂ S₂ (isBitBlock_map w) hcw
    (by simp [h2k, h1B]) (by simp [h2k, h1D]) rfl
  have hS : S₃ = m.stk := by
    funext k; cases k <;> simp [h3B, h3D, h3k, h2X, h2A, h2k, h1k, hA, hD]
  rw [hS] at r₃
  refine ⟨v₃, runLe_cast (((r₁.trans r₂).trans r₃).le le_rfl) ?_ (by simp)⟩
  have := hcw.length_le
  omega

/-- **Moving an earlier name from $D$ to $E$.** Let $m$ be a quiescent state of the 3-COLOR
emitter, $v$ a bit, $r$ either empty or a bit $b$, $w$ a list of bits, and $R$ a list of token
symbols whose first element, if any, is not a name bit. If the stack $D$ of $m$ is the name bits
of $w$ followed by $R$, then for some bit $v'$ the emitter machine runs in exactly $|w| + 1$
steps from label $\mathtt{mvN}(r)$ with internal bit $v$ and the stacks of $m$ to internal bit
$v'$, label $\mathtt{skU}$ if $r$ is empty and $\mathtt{mvU}(b)$ if $r = b$, and the stacks of
the quiescent state obtained from $m$ by setting $D$ to $R$ and putting the name bits of $w$, in
reverse order, on top of $E$. -/
theorem mvN_run (r : Option Bool) (w : List Bool) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) (h : m.d = w.map Sym.bit ++ R) :
    ∃ v', Run prog (w.length + 1) ⟨some (.mvN r), v, m.stk⟩
      ⟨some (r.elim .skU .mvU), v', {m with d := R, e := (w.map Sym.bit).reverse ++ m.e}.stk⟩ := by
  obtain ⟨v', S', r', hD, hE, hk⟩ := moveB_run (M := prog) (self := .mvN r)
    (next := r.elim .skU .mvU) (a := .D) (b := .E) (d := Sym.bit?) (g := Sym.bit) rfl
    (by decide) w (w.map Sym.bit) R v m.stk h (isBitBlock_map _) hR
  have hS : S' = {m with d := R, e := (w.map Sym.bit).reverse ++ m.e}.stk := by
    funext k; cases k <;> simp [hD, hE, hk]
  rw [hS] at r'
  exact ⟨v', r'⟩

/-- **Skipping an earlier literal vertex.** Let $m$ be a quiescent state of the 3-COLOR emitter
whose occurrence stack consists of $j$ units above a stack $R$ that is empty or does not have
a unit on top. From the label $\mathsf{skU}$, with any local state, the machine runs in
exactly $j + 1$ steps to the label $\mathsf{walk}$, in some local state and in the quiescent
state obtained from $m$ by replacing the occurrence stack with $R$ and pushing $j$ units onto
the other side of the walk. -/
theorem skU_run (j : ℕ) (R : List Sym) (hR : R.head?.bind unitOf = none)
    (h : m.d = cnt Sym.cl j ++ R) :
    ∃ v', Run prog (j + 1) ⟨some .skU, v, m.stk⟩
      ⟨some .walk, v', {m with d := R, e := cnt Sym.cl j ++ m.e}.stk⟩ := by
  obtain ⟨v', S', r', hD, hE, hk⟩ := moveB_run (M := prog) (self := .skU) (next := .walk)
    (a := .D) (b := .E) (d := unitOf) (g := fun _ => Sym.cl) rfl (by decide)
    (List.replicate j true) (cnt Sym.cl j) R v m.stk h (isBitBlock_cnt j) hR
  have hS : S' = {m with d := R, e := cnt Sym.cl j ++ m.e}.stk := by
    funext k; cases k <;> simp [hD, hE, hk]
  rw [hS, List.length_replicate] at r'
  exact ⟨v', r'⟩

/-- **Moving an earlier literal vertex from $D$ to $U$.** Let $m$ be a quiescent state of the
3-COLOR emitter whose counter $U$ is $0$, let $v$ and $b$ be bits, $j \in \mathbb{N}$, and $R$ a
list of token symbols whose first element, if any, is not the clause token $\mathtt{cl}$. If
the stack $D$ of $m$ is $j$ copies of $\mathtt{cl}$ followed by $R$, then for some bit $v'$ the
emitter machine runs in exactly $j + 1$ steps from label $\mathtt{mvU}(b)$ with internal bit $v$
and the stacks of $m$ to label $\mathtt{pre}(c_1)$ if $b$ is true and $\mathtt{pre}(d_1)$ if $b$
is false, internal bit $v'$, and the stacks of the quiescent state obtained from $m$ by setting
$D$ to $R$ and $U$ to $j$. -/
theorem mvU_run (b : Bool) (j : ℕ) (R : List Sym) (hR : R.head?.bind unitOf = none)
    (h : m.d = cnt Sym.cl j ++ R) (hU : m.u = 0) :
    ∃ v', Run prog (j + 1) ⟨some (.mvU b), v, m.stk⟩
      ⟨some (.pre (if b then .c1 else .d1)), v', {m with d := R, u := j}.stk⟩ := by
  obtain ⟨v', S', r', hD, hU', hk⟩ := moveB_run (M := prog) (self := .mvU b)
    (next := .pre (if b then .c1 else .d1)) (a := .D) (b := .U) (d := unitOf)
    (g := fun _ => Sym.cl) rfl (by decide) (List.replicate j true) (cnt Sym.cl j) R v m.stk h
    (isBitBlock_cnt j) hR
  have hS : S' = {m with d := R, u := j}.stk := by
    funext k; cases k <;> simp [hD, hU', hk, hU]
  rw [hS, List.length_replicate] at r'
  exact ⟨v', r'⟩

/-- **Moving $U$ onto $E$.** Let $m$ be a quiescent state and $u$ the value of its counter $U$.
From label $\mathsf{dr}$ with the stacks of $m$ and any flag, the emitter reaches label
$\mathsf{walk}$ in exactly $u + 1$ steps, with some flag and the stacks of $m$ except that $U$ is
empty (value $0$) and $u$ unit symbols are pushed onto $E$. -/
theorem dr_run : ∃ v', Run prog (m.u + 1) ⟨some .dr, v, m.stk⟩
    ⟨some .walk, v', {m with u := 0, e := cnt Sym.cl m.u ++ m.e}.stk⟩ := by
  have h := xfer_run (M := prog) (self := .dr) (next := .walk) (k := .U)
    (ps := [⟨.E, Sym.cl⟩]) rfl (single_nodupKeys _) (by simp) Sym.cl m.u v m.stk rfl
  have e : addU [⟨K.E, Sym.cl⟩] m.u (update m.stk .U []) =
      {m with u := 0, e := cnt Sym.cl m.u ++ m.e}.stk := by
    funext k
    by_cases hk : k = .E
    · subst hk; rw [addU_single_self]; rfl
    · rw [addU_single_ne _ _ _ hk]; cases k <;> first | rfl | exact absurd rfl hk
  rw [e] at h
  exact ⟨_, h⟩

/-- **The 3-COLOR emitter clears its OR-output counter.** Let $m$ be a quiescent state of the
3-COLOR emitter whose OR-output counter $R$ has value $r$, let $v$ be a Boolean and $b$ a Boolean.
Then there is a Boolean $v'$ such that the emitter runs in exactly $r + 1$ steps from label
$\mathsf{clr}(b)$ with internal state $v$ and the stacks of $m$ to the stacks of $m$ with $R$ set
to $0$ and internal state $v'$, at label $\mathsf{fA}(\mathrm{false})$ if $b$ is true and at
label $\mathsf{cls}$ otherwise. -/
theorem clr_run (b : Bool) : ∃ v', Run prog (m.r + 1) ⟨some (.clr b), v, m.stk⟩
    ⟨some (if b then .fA false else .cls), v', {m with r := 0}.stk⟩ := by
  have h := xfer_run (M := prog) (self := .clr b) (next := if b then .fA false else .cls)
    (k := .R) (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl m.r v m.stk rfl
  have e : addU [] m.r (update m.stk .R []) = {m with r := 0}.stk := by
    funext k; cases k <;> rfl
  rw [e] at h
  exact ⟨_, h⟩

/-- **Adding the vertex counter to the OR output.** For every quiescent state $m$ with counters
$n$ on stack $N$ and $r$ on stack $R$, every local state $v$ and every boolean $b$, the emitter
goes from label $\mathrm{fA}(b)$ with state $(v, m)$ to label $\mathrm{fC}(b)$, with some local
state, in exactly $2n + 2$ steps, ending in the state $m$ with the counter on $R$ replaced by
$n + r$; the counter $N$ is restored through the scratch stack $W$. -/
theorem fAB_run (b : Bool) : ∃ v', Run prog (2 * m.n + 2) ⟨some (.fA b), v, m.stk⟩
    ⟨some (.fC b), v', {m with r := m.n + m.r}.stk⟩ := by
  obtain ⟨v', h⟩ := dup_run .n (c := .R) Sym.cl (by decide) (by decide) (l₁ := .fA b)
    (l₂ := .fB b) (next := .fC b) rfl rfl m.n v m.stk rfl rfl
  have e : update m.stk .R (cnt (Sym.cl : Γ .R) m.n ++ m.stk .R) =
      {m with r := m.n + m.r}.stk := by
    rw [stk_R, ← List.replicate_add]; exact upd_R m _
  rw [e] at h
  exact ⟨v', h⟩

/-- **3-COLOR emitter: moving the walk side back.** Let $L$ be a list of token symbols each of
which is a walk token (a name bit, a literal marker or the clause symbol), let $m$ be a quiescent
state of the 3-COLOR emitter whose stack $E$ (the walk's other side) holds $L$, and let $v$ be a
Boolean. Then there is a Boolean $v'$ such that the emitter runs in exactly $|L| + 1$ steps from
label $\mathsf{back}$ with internal state $v$ and the stacks of $m$ to label $\mathsf{putN}$ with
internal state $v'$ and the stacks of the quiescent state obtained from $m$ by emptying $E$ and
replacing the occurrence stack $D$ by the reverse of $L$ followed by the old contents of $D$. -/
theorem back_run : ∀ (L : List Sym), (∀ s ∈ L, isTok s = true) → ∀ (m : MS) (v : Bool),
    m.e = L → ∃ v', Run prog (L.length + 1) ⟨some .back, v, m.stk⟩
      ⟨some .putN, v', {m with e := [], d := L.reverse ++ m.d}.stk⟩ := by
  intro L
  induction L with
  | nil =>
      intro _ m v h
      refine ⟨true, ?_⟩
      have e : ({m with e := [], d := [].reverse ++ m.d} : MS) = m := by
        obtain ⟨⟩ := m; simp only at h; subst h; rfl
      rw [e]
      exact back_nil m v h
  | cons s L ih =>
      intro hL m v h
      obtain ⟨v₁, r₁⟩ := back_step m v s (hL s (by simp)) L h
      obtain ⟨v₂, r₂⟩ := ih (fun x hx => hL x (by simp [hx])) {m with e := L, d := s :: m.d} v₁
        rfl
      exact ⟨v₂, run_cast (r₁.trans r₂) (by simp only [List.length_cons]; omega) (by simp)⟩

/-- **Recording the current occurrence.** Let $m$ be a quiescent state of the 3-COLOR emitter
with next free vertex $n$, whose name stack holds the name bits of a variable $x$ and whose
polarity stack holds only the marker for polarity $b$. From the label $\mathsf{putN}$, with
any local state, the machine runs in exactly $2n + 2|w| + 5$ steps, where $w$ is the binary
encoding of $x$, to the label $\mathsf{aft}$, in some local state and in the quiescent state
obtained from $m$ by emptying the name and polarity stacks and pushing onto the occurrence
stack the entry of the occurrence $(x, b, n, n + 1)$: the polarity marker of $b$ above the
name bits of $x$ above $n$ units. -/
theorem put_run (x : ℕ) (b : Bool) (hA : m.a = name x) (hP : m.p = [.lit b]) :
    ∃ v', Run prog (2 * m.n + 2 * (encodeNat x).length + 5) ⟨some .putN, v, m.stk⟩
      ⟨some .aft, v', {m with a := [], p := [], d := dTok (x, b, m.n, m.n + 1) ++ m.d}.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := dup_run .n (c := .D) Sym.cl (by decide) (by decide) (l₁ := .putN)
    (l₂ := .putW) (next := .putA) rfl rfl m.n v m.stk rfl rfl
  rw [show update m.stk .D (cnt (Sym.cl : Γ .D) m.n ++ m.stk .D) =
    {m with d := cnt Sym.cl m.n ++ m.d}.stk from upd_D _ _] at r₁
  obtain ⟨v₂, S₂, r₂, h2A, h2B, h2k⟩ := moveB_run (M := prog) (self := .putA) (next := .putB)
    (a := .A) (b := .B) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x) (name x)
    [] v₁ {m with d := cnt Sym.cl m.n ++ m.d}.stk (by simp [hA]) (isBitBlock_map _) rfl
  obtain ⟨v₃, S₃, r₃, h3B, h3D, h3k⟩ := moveB_run (M := prog) (self := .putB) (next := .putP)
    (a := .B) (b := .D) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x).reverse
    (name x).reverse [] v₂ S₂ (by simp [h2B]) (isBitBlock_map_reverse _) rfl
  have hS₃ : S₃ = {m with a := [], d := name x ++ cnt Sym.cl m.n ++ m.d}.stk := by
    funext k; cases k <;> simp [h3B, h3D, h3k, h2A, h2k, List.map_reverse]
  rw [hS₃] at r₃
  have r₄ := putP_step {m with a := [], d := name x ++ cnt Sym.cl m.n ++ m.d} v₃ b (by simp [hP])
  exact ⟨b, run_cast (((r₁.trans r₂).trans r₃).trans r₄) (by simp only [List.length_reverse]; omega)
    (by simp [dTok])⟩

end Phases

/-! ### The edges of the site runs -/

/-- **Copy sites of the occurrence triangle.** The list of copy sites $o_1, o_2, o_3, o_4$, in
this order.

Run in sequence, these sites push the edges $(L, M)$, $(L, 2)$, $(M, 2)$ of the occurrence
triangle, where $L = N$ and $M = N + 1$ for the next-vertex counter $N$. -/
def occSites : List Site := [.o1, .o2, .o3, .o4]

/-- **Copy sites of the consistency edges.** For a flag $b$, the list of copy sites that push the
consistency edges with an earlier occurrence whose literal vertex $L'$ is on stack $U$: the
sites $c_1, c_2, c_3, c_4$ (equal polarity) when $b$ is true, and the sites
$d_1, d_2, d_3, d_4$ (opposite polarity) when $b$ is false. -/
def consSites (b : Bool) : List Site :=
  if b then [.c1, .c2, .c3, .c4] else [.d1, .d2, .d3, .d4]

/-- **The OR-gadget copy sites.** The list of the eleven copy sites $r_1, \dots, r_{11}$ of
the 3-COLOR emitter, in this order.

Run in sequence, they push the OR gadget whose inputs are the next free vertex $N$ and the
current OR output $R$ and whose fresh vertices are $N + 2$, $N + 3$ and $N + 4$. -/
def orSites : List Site := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- **Copy sites of the clause end.** The list of copy sites $e_1, e_2$, which push the edges
joining the current OR output $R$ to the palette vertices $F = 1$ and $B = 2$. -/
def endSites : List Site := [.e1, .e2]

/-- **Copy sites of the empty clause.** The list of copy sites $z_1, z_2, z_3$, which push the
edges joining the next free vertex $N$ to the palette vertices $0$, $1$ and $2$. -/
def empSites : List Site := [.z1, .z2, .z3]

theorem out_cons (e : ℕ × ℕ) (es : List (ℕ × ℕ)) : out (e :: es) = out es ++ eB e := by
  simp [out]

@[simp] theorem out_nil : out [] = [] := rfl

theorem occ_out (m : MS) :
    chainOut m occSites = out [(m.n, m.n + 1), (m.n, 2), (m.n + 1, 2)] := by
  simp [occSites, atom, Site.src, Site.top, MS.val, out_cons, eB, List.replicate_succ']

theorem cons_out (b : Bool) (m : MS) : chainOut m (consSites b) =
    out (if b then [(m.u, m.n + 1), (m.u + 1, m.n)] else [(m.u, m.n), (m.u + 1, m.n + 1)]) := by
  cases b <;> simp [consSites, atom, Site.src, Site.top, MS.val, out_cons, eB,
    List.replicate_succ']

theorem or_out (m : MS) : chainOut m orSites = out [(m.n, m.n + 2), (m.r, m.n + 3),
    (m.n + 2, m.n + 3), (m.n + 2, m.n + 4), (m.n + 3, m.n + 4), (m.n + 4, 2)] := by
  simp [orSites, atom, Site.src, Site.top, MS.val, out_cons, eB, List.replicate_add]

theorem end_out (m : MS) : chainOut m endSites = out [(m.r, 1), (m.r, 2)] := by
  simp [endSites, atom, Site.src, Site.top, MS.val, out_cons, eB]

theorem emp_out (m : MS) : chainOut m empSites = out [(m.n, 0), (m.n, 1), (m.n, 2)] := by
  simp [empSites, atom, Site.src, Site.top, MS.val, out_cons, eB]

/-! ### The walk over earlier occurrences -/

/-- **Consistency edges of two occurrences of the same variable.** Let $x$, $L'$ and $n$ be
natural numbers and let $p$, $b$ be Booleans. The consistency edges between a new occurrence of
the literal $(x, p)$ with vertices $L = n$, $M = n + 1$ and an earlier occurrence
$(x, b, L', L' + 1)$ are $[(L', n + 1), (L' + 1, n)]$ if $b = p$, and
$[(L', n), (L' + 1, n + 1)]$ otherwise. -/
theorem consEdges_same (x : ℕ) (p b : Bool) (L' n : ℕ) :
    consEdges (x, p) n (n + 1) (x, b, L', L' + 1) =
      if b == p then [(L', n + 1), (L' + 1, n)] else [(L', n), (L' + 1, n + 1)] := by
  cases b <;> cases p <;> simp [consEdges]

theorem flatMap_dTok_head (qs : List (ℕ × Bool × ℕ × ℕ)) :
    (qs.flatMap dTok).head?.bind unitOf = none ∧ (qs.flatMap dTok).head?.bind Sym.bit? = none := by
  cases qs with
  | nil => exact ⟨rfl, rfl⟩
  | cons q qs => simp [List.flatMap_cons, dTok, unitOf, Sym.bit?]

theorem isTok_dTok (qs : List (ℕ × Bool × ℕ × ℕ)) :
    ∀ s ∈ (qs.flatMap dTok).reverse, isTok s = true := by
  intro s hs
  simp only [List.mem_reverse, List.mem_flatMap, dTok, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_replicate] at hs
  obtain ⟨q, -, hs⟩ := hs
  rcases hs with rfl | ⟨b, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- **One step of the walk over earlier occurrences.** Let $l = (x, p)$ be a new occurrence and
$q = (x', b', L', M')$ an earlier one with $M' = L' + 1$. Let $m$ be a quiescent state whose
stack $D$ holds the tokens of $q$ (the marker of polarity $b'$, the name bits of $x'$, then $L'$
unary unit symbols) above a list $S$ whose first symbol, if any, is neither a unary unit nor a
name bit; whose stack $A$ holds the name bits of $x$; whose stack $P$ holds only the marker of
polarity $p$; and whose counter $U$ is $0$. Write $n$ and $r$ for the counters $N$ and $R$ of $m$
and $k$ for the number of tokens of $q$. Then for every local state $v$, the emitter goes from
label walk with state $(v, m)$ to label walk again, with some local state, in at most
$12k + 8(n + r) + 21$ steps. It ends in the state $m$ with $D$ replaced by $S$, with $E$ holding
the tokens of $q$ in reverse order above its old contents, and with the output stack holding
the bits of the consistency edges of $l$ (with literal vertex $n$ and negation vertex $n + 1$)
with $q$ above its old contents. -/
theorem ent_run (l : ℕ × Bool) (q : ℕ × Bool × ℕ × ℕ) (hq : q.2.2.2 = q.2.2.1 + 1)
    (R : List Sym) (hR : R.head?.bind unitOf = none) (hRb : R.head?.bind Sym.bit? = none)
    (m : MS) (v : Bool) (hD : m.d = dTok q ++ R) (hA : m.a = name l.1) (hP : m.p = [.lit l.2])
    (hU : m.u = 0) :
    ∃ v', RunLe prog (12 * (dTok q).length + 8 * (m.n + m.r) + 21) ⟨some .walk, v, m.stk⟩
      ⟨some .walk, v', {m with
        d := R, e := (dTok q).reverse ++ m.e,
        o := out (consEdges l m.n (m.n + 1) q) ++ m.o}.stk⟩ := by
  obtain ⟨x', b', L', M'⟩ := q
  obtain ⟨x, p⟩ := l
  simp only at hq hA hP ⊢
  subst hq
  have hD' : m.d = .lit b' :: (name x' ++ (cnt Sym.cl L' ++ R)) := by simp [hD, dTok]
  have r₁ := walk_lit m v b' _ hD'
  have hcR : (cnt Sym.cl L' ++ R).head?.bind Sym.bit? = none := by
    cases L' <;> simp [Sym.bit?, hRb, List.replicate_succ]
  obtain ⟨v₂, r₂⟩ := cmp_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
    b' (encodeNat x) (encodeNat x') _ hcR hA rfl
  have hlen : (dTok (x', b', L', L' + 1)).length = (encodeNat x').length + L' + 1 := by
    simp [dTok]
  by_cases hx : x' = x
  · subst hx
    rw [show (if encodeNat x' = encodeNat x' then Lab.sel else .mvN none) = .sel by simp] at r₂
    have r₃ := sel_step {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e} v₂ b' p
      m.e rfl hP
    obtain ⟨v₄, r₄⟩ := mvN_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
      (b' == p) (some (b' == p)) (encodeNat x') _ hcR rfl
    obtain ⟨v₅, r₅⟩ := mvU_run {m with
      d := cnt Sym.cl L' ++ R, e := (name x').reverse ++ .lit b' :: m.e} v₄ (b' == p) L' R hR rfl
      hU
    obtain ⟨v₆, r₆⟩ := chain_run (consSites (b' == p)) {m with
      d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L'}
      (.pre (if b' == p then .c1 else .d1)) .dr (by cases b' <;> cases p <;> decide) v₅
    obtain ⟨v₇, r₇⟩ := dr_run {m with
      d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L',
      o := chainOut {m with d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L'}
        (consSites (b' == p)) ++ m.o} v₆
    refine ⟨v₇, runLe_cast ((((r₁.le le_rfl).trans r₂).trans
      (((r₃.trans r₄).trans r₅).le le_rfl)).trans r₆ |>.trans (r₇.le le_rfl)) ?_ ?_⟩
    · have h4 : (consSites (b' == p)).length = 4 := by cases b' <;> cases p <;> rfl
      simp only [h4, hlen]
      omega
    · simp [cons_out, consEdges_same, dTok, hU]
  · have hne : encodeNat x ≠ encodeNat x' := fun h => hx (encodeNat_inj.1 h).symm
    rw [show (if encodeNat x = encodeNat x' then Lab.sel else .mvN none) = .mvN none by
      simp [hne]] at r₂
    obtain ⟨v₃, r₃⟩ := mvN_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
      v₂ none (encodeNat x') _ hcR rfl
    obtain ⟨v₄, r₄⟩ := skU_run {m with
      d := cnt Sym.cl L' ++ R, e := (name x').reverse ++ .lit b' :: m.e} v₃ L' R hR rfl
    refine ⟨v₄, runLe_cast (((r₁.le le_rfl).trans r₂).trans ((r₃.trans r₄).le le_rfl)) ?_ ?_⟩
    · simp only [hlen]
      omega
    · simp [consEdges, hx, dTok]

/-- **Walking the earlier occurrences.** Let $l = (x, b)$ be a literal and let
$q_1, \dots, q_k$ be earlier occurrences, each a tuple $(y, c, L, M)$ of a variable, a polarity,
a literal vertex and a negation vertex with $M = L + 1$. Let $m$ be a quiescent state of the
3-coloring emitter whose earlier-occurrence stack $D$ holds the concatenation $\delta$ of the
stack encodings of $q_1, \dots, q_k$, whose name stack holds the name bits of $x$, whose
polarity stack holds the single marker of polarity $b$, and whose earlier-literal counter is $0$;
let $n$ and $r$ be its next-vertex and OR-output counter values. Then for every internal state,
the emitter runs in at most $12|\delta| + k(8(n + r) + 21) + 1$ steps from the walk label with
the stacks of $m$ to the back label, with some internal state, and with the stacks of the
quiescent state obtained from $m$ by emptying $D$, putting the reverse of $\delta$ on top of the
walk stack $E$, and putting on top of the output stack the output for the consistency edges of
$l$, with literal vertex $n$ and negation vertex $n + 1$, with $q_1, \dots, q_k$ in turn. -/
theorem walk_run (l : ℕ × Bool) : ∀ (qs : List (ℕ × Bool × ℕ × ℕ)),
    (∀ q ∈ qs, q.2.2.2 = q.2.2.1 + 1) → ∀ (m : MS) (v : Bool), m.d = qs.flatMap dTok →
    m.a = name l.1 → m.p = [.lit l.2] → m.u = 0 →
    ∃ v', RunLe prog (12 * (qs.flatMap dTok).length + qs.length * (8 * (m.n + m.r) + 21) + 1)
      ⟨some .walk, v, m.stk⟩ ⟨some .back, v', {m with
        d := [], e := (qs.flatMap dTok).reverse ++ m.e,
        o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ m.o}.stk⟩ := by
  intro qs
  induction qs with
  | nil =>
      intro _ m v hD _ _ _
      refine ⟨true, runLe_cast ((walk_nil m v (by simpa using hD)).le le_rfl) (by simp) ?_⟩
      obtain ⟨⟩ := m
      simp only [List.flatMap_nil] at hD
      subst hD
      rfl
  | cons q qs ih =>
      intro hq m v hD hA hP hU
      obtain ⟨v₁, r₁⟩ := ent_run l q (hq q (by simp)) (qs.flatMap dTok) (flatMap_dTok_head qs).1
        (flatMap_dTok_head qs).2 m v (by simpa using hD) hA hP hU
      obtain ⟨v₂, r₂⟩ := ih (fun q' h => hq q' (by simp [h])) {m with
        d := qs.flatMap dTok, e := (dTok q).reverse ++ m.e,
        o := out (consEdges l m.n (m.n + 1) q) ++ m.o} v₁ rfl hA hP hU
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith
      · simp [List.flatMap_cons, out_append]

/-- **Emitting one literal occurrence.** Let $\ell = (x, p)$ be a literal, $R$ a list of token
symbols whose first element, if any, is not a name bit, and $qs$ a list of earlier occurrences
$(x_i, p_i, L_i, M_i)$ with $M_i = L_i + 1$ for each. Let $m$ be a quiescent state of the
3-COLOR emitter with counter values $n$ for $N$ and $r$ for the OR output, and $v$ a bit.
Suppose the token stack of $m$ is the tokens of $\ell$ (its polarity marker above its name in
reverse order) followed by $R$, the stack $D$ is the concatenated stack encodings of the
occurrences in $qs$, the stacks $E$, $A$, $P$ are empty and the counter $U$ is $0$. Let $d$ be
the length of $D$ and $k$ the length of the binary encoding of $x$. Then for some bit $v'$ the
emitter machine runs in at most
$13 d + |qs| (8 (n + r) + 21) + 10 (n + r) + 3 k + 30$
steps from label $\mathtt{lits}$ with internal bit $v$ and the stacks of $m$ to label
$\mathtt{aft}$ with internal bit $v'$ and the stacks of the quiescent state obtained from $m$
as follows: the token stack is $R$; $D$ holds the stack encodings of $(x, p, n, n + 1)$ and then
of the occurrences in $qs$; and the output is the old output with the edges $(n, n + 1)$,
$(n, 2)$, $(n + 1, 2)$ and then the consistency edges of the new occurrence $(\ell, n, n + 1)$
with the occurrences in $qs$, in order, pushed on top. The counter $N$ is not advanced. -/
theorem occ_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (qs : List (ℕ × Bool × ℕ × ℕ)) (hq : ∀ q ∈ qs, q.2.2.2 = q.2.2.1 + 1) (m : MS) (v : Bool)
    (hT : m.t = Check.litRev l ++ R) (hD : m.d = qs.flatMap dTok) (hE : m.e = [])
    (hA : m.a = []) (hP : m.p = []) (hU : m.u = 0) :
    ∃ v', RunLe prog (13 * (qs.flatMap dTok).length + qs.length * (8 * (m.n + m.r) + 21) +
        10 * (m.n + m.r) + 3 * (encodeNat l.1).length + 30) ⟨some .lits, v, m.stk⟩
      ⟨some .aft, v', {m with
        t := R, d := ((l.1, l.2, m.n, m.n + 1) :: qs).flatMap dTok,
        o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++
          out [(m.n, m.n + 1), (m.n, 2), (m.n + 1, 2)] ++ m.o}.stk⟩ := by
  have hT' : m.t = .lit l.2 :: ((name l.1).reverse ++ R) := by simp [hT, Check.litRev]
  have r₁ := lits_lit m v (by simp [hT', isLit])
  obtain ⟨v₂, r₂⟩ := chain_run occSites m (.pre .o1) .lp (by decide) true
  have r₃ := lp_step {m with o := chainOut m occSites ++ m.o} v₂ l.2 _ hT'
  obtain ⟨v₄, r₄⟩ := nm_run {m with
    o := chainOut m occSites ++ m.o, t := (name l.1).reverse ++ R, p := .lit l.2 :: m.p} l.2 l.1
    R hR rfl hA
  obtain ⟨v₅, r₅⟩ := walk_run l qs hq {m with
    o := chainOut m occSites ++ m.o, t := R, p := .lit l.2 :: m.p, a := name l.1} v₄ hD rfl
    (by simp [hP]) hU
  obtain ⟨v₆, r₆⟩ := back_run (qs.flatMap dTok).reverse (isTok_dTok qs) {m with
      o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ (chainOut m occSites ++ m.o),
      t := R, p := .lit l.2 :: m.p, a := name l.1, d := [],
      e := (qs.flatMap dTok).reverse ++ m.e} v₅ (by simp [hE])
  obtain ⟨v₇, r₇⟩ := put_run {m with
      o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ (chainOut m occSites ++ m.o),
      t := R, p := .lit l.2 :: m.p, a := name l.1, d := (qs.flatMap dTok).reverse.reverse ++ [],
      e := []} v₆ l.1 l.2 rfl (by simp [hP])
  refine ⟨v₇, runLe_cast ((((r₁.le le_rfl).trans r₂).trans ((r₃.trans r₄).le le_rfl)).trans r₅
    |>.trans ((r₆.trans r₇).le le_rfl)) ?_ ?_⟩
  · simp only [occSites, List.length_cons, List.length_nil, List.length_reverse, hU]
    omega
  · simp [occ_out, hE, hA, hP, List.flatMap_cons, List.append_assoc]

/-! ### The size invariant -/

/-- **Size invariant of the 3-coloring emitter.** A construction state $s$ satisfies the size
invariant after $\tau$ tokens when its next free vertex $n$ is at most $5\tau + 3$, it has at
most $\tau$ earlier occurrences, the total number of tokens of its earlier occurrences as they
lie on stack $D$ is at most $\tau (n + 1)$, and every earlier occurrence $(x, b, L, M)$ has
$M = L + 1$. -/
def Inv (τ : ℕ) (s : ColSt) : Prop :=
  s.next ≤ 5 * τ + 3 ∧ s.prev.length ≤ τ ∧ (s.prev.flatMap dTok).length ≤ τ * (s.next + 1) ∧
    ∀ q ∈ s.prev, q.2.2.2 = q.2.2.1 + 1

theorem Inv.of_eq {τ : ℕ} {s s' : ColSt} (h : Inv τ s) (hn : s'.next = s.next)
    (hp : s'.prev = s.prev) : Inv τ s' := by
  unfold Inv; rw [hn, hp]; exact h

/-- **One more token preserves the 3-COLOR emitter's size invariant.** Let $s$ and $s'$ be
construction states with the same earlier occurrences, such that the next free vertex of $s'$ is
at least that of $s$ and at most that of $s$ plus $5$. If $s$ satisfies the size invariant after
$\tau$ tokens, then $s'$ satisfies the size invariant after $\tau + 1$ tokens. -/
theorem Inv.bump {τ : ℕ} {s s' : ColSt} (h : Inv τ s) (hp : s'.prev = s.prev)
    (hn : s.next ≤ s'.next) (hn' : s'.next ≤ s.next + 5) : Inv (τ + 1) s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by rw [hp]; omega, ?_, by rw [hp]; exact h4⟩
  rw [hp]
  have : τ * (s.next + 1) ≤ (τ + 1) * (s'.next + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **The size invariant survives a new literal occurrence.** Let $s$ and $s'$ be states of
the 3-COLOR construction with next free vertices $n$ and $n'$, and let $l = (x, p)$ be a
literal. Suppose that $s$ satisfies the size invariant after $\tau$ tokens, that the earlier
occurrences of $s'$ are those of $s$ preceded by the occurrence of $l$ with literal vertex $n$
and negation vertex $n + 1$, and that $n \le n' \le n + 5$. Then $s'$ satisfies the size
invariant after $\tau + t$ tokens, where $t$ is the number of tokens of $l$ on the token
stack. -/
theorem Inv.occ {τ : ℕ} {s s' : ColSt} (l : ℕ × Bool) (h : Inv τ s)
    (hp : s'.prev = (l.1, l.2, s.next, s.next + 1) :: s.prev) (hn : s.next ≤ s'.next)
    (hn' : s'.next ≤ s.next + 5) : Inv (τ + (Check.litRev l).length) s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl := Check.litRev_length l
  refine ⟨by omega, by rw [hp, List.length_cons]; omega, ?_, ?_⟩
  · rw [hp, List.flatMap_cons, List.length_append]
    have hd : (dTok (l.1, l.2, s.next, s.next + 1)).length =
        (encodeNat l.1).length + s.next + 1 := by simp [dTok]
    rw [hd, hl]
    have e1 : τ * (s.next + 1) ≤ τ * (s'.next + 1) := Nat.mul_le_mul_left _ (by omega)
    have e2 : ((encodeNat l.1).length + 1) * (s.next + 1) ≤
        ((encodeNat l.1).length + 1) * (s'.next + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · rw [hp]
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rfl
    · exact h4 q hq

theorem inv_colLits : ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt) (τ : ℕ), Inv τ s →
    Inv (τ + (ls.flatMap Check.litRev).length) (colLits ls o s) := by
  intro ls
  induction ls with
  | nil =>
      intro o s τ h
      rw [List.flatMap_nil, List.length_nil, Nat.add_zero]
      exact h.of_eq rfl rfl
  | cons l ls ih =>
      intro o s τ h
      have h' := ih (colOr (colOcc l s).2 o (colOcc l s).1).2 _ _
        (h.occ l (s' := (colOr (colOcc l s).2 o (colOcc l s).1).1) rfl
        (by simp only [colOr, colOcc]; omega) (by simp only [colOr, colOcc]; omega))
      rw [List.flatMap_cons, List.length_append, ← Nat.add_assoc]
      exact h'

private theorem clRev_length' (C : CNFClause) :
    (Check.clRev C).length = (C.reverse.flatMap Check.litRev).length + 1 := by
  simp [Check.clRev]

theorem inv_colClause (C : CNFClause) (s : ColSt) (τ : ℕ) (h : Inv τ s) :
    Inv (τ + (Check.clRev C).length) (colClause C s) := by
  rw [clRev_length']
  unfold colClause
  cases hC : C.reverse with
  | nil => exact h.bump rfl (by simp) (by simp)
  | cons l ls =>
      have h1 := (h.bump (s' := s) rfl le_rfl (by omega)).occ l (s' := (colOcc l s).1) rfl
        (by simp only [colOcc]; omega) (by simp only [colOcc]; omega)
      have h2 := inv_colLits ls (colOcc l s).2 _ _ h1
      simp only [List.flatMap_cons, List.length_append] at h2 ⊢
      convert h2 using 1
      omega

theorem inv_foldl : ∀ (Cs : CNF) (s : ColSt) (τ : ℕ), Inv τ s →
    Inv (τ + (Cs.flatMap Check.clRev).length) (Cs.foldl (fun s C => colClause C s) s) := by
  intro Cs
  induction Cs with
  | nil => intro s τ h; simpa using h
  | cons C Cs ih =>
      intro s τ h
      have := ih _ _ (inv_colClause C s τ h)
      rw [List.flatMap_cons, List.length_append, ← Nat.add_assoc]
      exact this

/-! ### Literals, clauses, the formula -/

/-- **Per-token step budget of the 3-COLOR emitter.** For a bound $L$ on the number of tokens of
a formula, the step budget per token is $400 (L + 1)^2$. -/
def budget (Lb : ℕ) : ℕ := 400 * (Lb + 1) ^ 2

/-- **The emitter state of a construction state.** For a construction state $s$, a token list $t$,
a bit list $o_0$ and natural numbers $r$ and $f$: the quiescent state whose token stack is $t$,
whose output stack is the bits of the edges emitted by $s$ (the last one on top) above $o_0$,
whose counter $N$ is the next free vertex of $s$, whose counter $R$ is $r$, whose stack $D$
holds the encodings of the earlier occurrences of $s$ (latest on top), whose stacks $E$, $A$
and $P$ are empty, whose counter $F$ is $f$, and whose counter $U$ is $0$. -/
def enc (s : ColSt) (t : List Sym) (o0 : List Bool) (r f : ℕ) : MS :=
  ⟨t, out s.em ++ o0, s.next, r, s.prev.flatMap dTok, [], [], [], f, 0⟩

theorem runLe_cast' {k k' : ℕ} {c c' d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hc : c' = c) (hk : k ≤ k') (hd : d = d') : RunLe prog k' c' d' := hc ▸ hd ▸ h.mono hk

/-- **Step budget for one literal.** Let $L_b, \tau, n, r, P, D, w$ be natural numbers with
$\tau + w + 1 \le L_b$, $n \le 5\tau + 3$, $r \le n$, $P \le \tau$ and $D \le \tau (n + 1)$. Then
$13 D + P (8 (n + r) + 21) + 40 (n + r) + 3 w + 100 \le \mathrm{budget}(L_b)$, where
$\mathrm{budget}(L_b) = 400 (L_b + 1)^2$ is the per-token step budget of the 3-COLOR emitter. -/
theorem lit_cost {Lb τ n r P D w : ℕ} (hτ : τ + w + 1 ≤ Lb) (hn : n ≤ 5 * τ + 3) (hr : r ≤ n)
    (hP : P ≤ τ) (hD : D ≤ τ * (n + 1)) :
    13 * D + P * (8 * (n + r) + 21) + 40 * (n + r) + 3 * w + 100 ≤ budget Lb := by
  unfold budget
  have h1 : P * (8 * (n + r) + 21) ≤ Lb * (16 * (5 * Lb + 3) + 21) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : τ * (n + 1) ≤ Lb * (5 * Lb + 4) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem headLit_of (R : List Sym) (hR : R = [] ∨ R.head? = some .cl) :
    isLit R.head? = false ∧ R.head?.bind Sym.bit? = none := by
  rcases hR with rfl | h <;> simp [isLit, Sym.bit?, *]

theorem flatMap_litRev_head (ls : List (ℕ × Bool)) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) :
    (ls.flatMap Check.litRev ++ R).head?.bind Sym.bit? = none := by
  cases ls with
  | nil => simpa using hR
  | cons l ls => simp [List.flatMap_cons, Check.litRev, Sym.bit?]

/-- **The emitter processes the remaining literals of a clause.** Let $L_b \in \mathbb{N}$, let
$R$ be a list of token symbols that is empty or starts with the clause token $\mathtt{cl}$, and
let $o_0$ be a list of bits. Let $ls$ be a list of literals, $o, \tau \in \mathbb{N}$, $s$ a
construction state and $v$ a bit, and write $T$ for the concatenation of the token-stack tokens
of the literals of $ls$ and $TR$ for $T$ followed by $R$. Suppose $s$ satisfies the size
invariant after $\tau$ tokens, $o$ is at most the next free vertex of $s$, and
$\tau + |T| \le L_b$. Then for some bit $v'$ the emitter machine runs in at most
$(|T| + 1) \cdot \mathrm{budget}(L_b)$ steps from label $\mathtt{lits}$ with internal bit $v$
and the stacks of the quiescent state $\mathrm{enc}(s, TR, o_0, o, 0)$ to label $\mathtt{cls}$
with internal bit $v'$ and the stacks of $\mathrm{enc}(\mathrm{colLits}(ls, o, s), R, o_0, 0, 0)$.
Here $\mathrm{enc}(s, t, o_0, r, f)$ is the quiescent state of $s$ with token stack $t$, output
above $o_0$, OR output $r$ and first-literal flag $f$; $\mathrm{colLits}(ls, o, s)$ is $s$ after
the occurrences and OR gadgets of $ls$, starting from OR output $o$, and the clause end; and
$\mathrm{budget}(L_b) = 400 (L_b + 1)^2$. -/
theorem lits_run (Lb : ℕ) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl) (o0 : List Bool) :
    ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt) (τ : ℕ) (v : Bool), Inv τ s → o ≤ s.next →
      τ + (ls.flatMap Check.litRev).length ≤ Lb →
      ∃ v', RunLe prog (((ls.flatMap Check.litRev).length + 1) * budget Lb)
        ⟨some .lits, v, (enc s (ls.flatMap Check.litRev ++ R) o0 o 0).stk⟩
        ⟨some .cls, v', (enc (colLits ls o s) R o0 0 0).stk⟩ := by
  obtain ⟨hRl, hRb⟩ := headLit_of R hR
  intro ls
  induction ls with
  | nil =>
      intro o s τ v hinv ho hb
      have r₁ := lits_end (enc s R o0 o 0) v hRl
      obtain ⟨v₂, r₂⟩ := chain_run endSites (enc s R o0 o 0) (.pre .e1) (.clr false) (by decide)
        false
      obtain ⟨v₃, r₃⟩ := clr_run {enc s R o0 o 0 with
        o := chainOut (enc s R o0 o 0) endSites ++ (enc s R o0 o 0).o} v₂ false
      refine ⟨v₃, runLe_cast (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)) ?_ ?_⟩
      · have h1 := hinv.1
        simp only [enc, endSites, List.length_cons, List.length_nil, List.flatMap_nil, budget]
        nlinarith
      · simp [enc, colLits, end_out, out_append]
  | cons l ls ih =>
      intro o s τ v hinv ho hb
      have hl := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb ⊢
      rw [List.append_assoc]
      obtain ⟨v₁, r₁⟩ := occ_run l (ls.flatMap Check.litRev ++ R) (flatMap_litRev_head ls R hRb)
        s.prev hinv.2.2.2 (enc s (Check.litRev l ++ (ls.flatMap Check.litRev ++ R)) o0 o 0) v rfl
        rfl rfl rfl rfl rfl
      let m₁ : MS := ⟨ls.flatMap Check.litRev ++ R,
        out (s.prev.flatMap (consEdges l s.next (s.next + 1))) ++
          out [(s.next, s.next + 1), (s.next, 2), (s.next + 1, 2)] ++ (out s.em ++ o0),
        s.next, o, ((l.1, l.2, s.next, s.next + 1) :: s.prev).flatMap dTok, [], [], [], 0, 0⟩
      obtain ⟨v₂, r₂⟩ := aft_zero m₁ v₁ rfl
      obtain ⟨v₃, r₃⟩ := chain_run orSites m₁ (.pre .r1) (.clr true) (by decide) v₂
      obtain ⟨v₄, r₄⟩ := clr_run {m₁ with o := chainOut m₁ orSites ++ m₁.o} v₃ true
      obtain ⟨v₅, r₅⟩ := fAB_run {m₁ with o := chainOut m₁ orSites ++ m₁.o, r := 0} v₄ false
      have r₆ := fC_step {m₁ with o := chainOut m₁ orSites ++ m₁.o, r := s.next + 0} v₅ false
      let r' := colOr (colOcc l s).2 o (colOcc l s).1
      obtain ⟨v₇, r₇⟩ := ih r'.2 r'.1 (τ + (Check.litRev l).length) v₅
        (hinv.occ l rfl (by simp only [r', colOr, colOcc]; omega)
          (by simp only [r', colOr, colOcc]; omega))
        (by simp only [r', colOr, colOcc]; omega) (by omega)
      have hmid : (⟨some .lits, v₅, {m₁ with
          o := chainOut m₁ orSites ++ m₁.o, r := s.next + 0 + (if false then 0 else 4),
          n := s.next + (if false then 2 else 5)}.stk⟩ : TM2.Cfg Γ Lab Bool) =
          ⟨some .lits, v₅, (enc r'.1 (ls.flatMap Check.litRev ++ R) o0 r'.2 0).stk⟩ := by
        simp [m₁, r', enc, colOr, colOcc, or_out, out_append, out_cons, Nat.add_assoc]
      refine ⟨v₇, runLe_cast ((((r₁.trans (r₂.le le_rfl)).trans r₃).trans
        (((r₄.trans r₅).trans r₆).le le_rfl)).trans (runLe_cast' r₇ hmid le_rfl rfl)) ?_ rfl⟩
      have hc := lit_cost (Lb := Lb) (w := (encodeNat l.1).length) (by omega) hinv.1 ho hinv.2.1
        hinv.2.2.1
      have hK : budget Lb ≤ (Check.litRev l).length * budget Lb :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [enc, m₁, orSites, List.length_cons, List.length_nil]
      nlinarith

/-- **The 3-COLOR emitter processes one clause.** Let $C$ be a CNF clause, $T_C$ its tokens as
they lie on the token stack, $s$ a construction state that satisfies the size invariant after
$\tau$ tokens, and $L$ a bound with $\tau + |T_C| \le L$. Let $Y$ be a list of symbols that is
empty or starts with the clause marker, and $o_0$ a list of bits. For a construction state $t$
and a symbol list $X$, write $q(t, X)$ for the quiescent state encoding $t$ with token stack $X$,
output stack holding the bits of the edges emitted in $t$ above $o_0$, OR output $0$ and
first-literal flag $0$. Then for every Boolean $v$ there is a Boolean $v'$ such that the emitter
goes in at most $|T_C| \cdot (400 (L + 1)^2 + 1)$ steps from label $\mathsf{cls}$ with internal
state $v$ and the stacks of $q(s, T_C Y)$ to label $\mathsf{cls}$ with internal state $v'$ and
the stacks of $q(s_C, Y)$, where $T_C Y$ is $T_C$ on top of $Y$ and $s_C$ is the construction
state after clause $C$ is processed from $s$. -/
theorem clause_run (Lb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (o0 : List Bool) (s : ColSt) (τ : ℕ) (v : Bool) (hinv : Inv τ s)
    (hb : τ + (Check.clRev C).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * (budget Lb + 1))
      ⟨some .cls, v, (enc s (Check.clRev C ++ R) o0 0 0).stk⟩
      ⟨some .cls, v', (enc (colClause C s) R o0 0 0).stk⟩ := by
  obtain ⟨hRl, hRb⟩ := headLit_of R hR
  have hcl : Check.clRev C ++ R = .cl :: (C.reverse.flatMap Check.litRev ++ R) := by
    simp [Check.clRev]
  rw [hcl, clRev_length']
  rw [clRev_length'] at hb
  unfold colClause
  cases hC : C.reverse with
  | nil =>
      rw [hC] at hb
      have r₁ := cls_emp (enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0) v R rfl hRl
      obtain ⟨v₂, r₂⟩ := chain_run empSites
        {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with t := R} (.pre .z1) .zN
        (by decide) false
      have r₃ := zN_step {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with
        t := R,
        o := chainOut {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with t := R}
          empSites ++ (out s.em ++ o0)} v₂
      refine ⟨v₂, runLe_cast (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)) ?_ ?_⟩
      · have h1 := hinv.1
        simp only [enc, empSites, List.length_cons, List.length_nil, List.flatMap_nil, budget]
        nlinarith
      · simp [enc, emp_out, out_append]
  | cons l ls =>
      rw [hC] at hb
      have hl := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb ⊢
      rw [List.append_assoc]
      have r₁ := cls_lit (enc s (.cl :: (Check.litRev l ++ (ls.flatMap Check.litRev ++ R))) o0 0 0)
        v _ rfl (by simp [Check.litRev, isLit])
      obtain ⟨v₂, r₂⟩ := occ_run l (ls.flatMap Check.litRev ++ R) (flatMap_litRev_head ls R hRb)
        s.prev hinv.2.2.2 {enc s (.cl :: (Check.litRev l ++ (ls.flatMap Check.litRev ++ R))) o0 0 0
          with t := Check.litRev l ++ (ls.flatMap Check.litRev ++ R), f := 0 + 1} true rfl rfl rfl
        rfl rfl rfl
      let m₂ : MS := ⟨ls.flatMap Check.litRev ++ R,
        out (s.prev.flatMap (consEdges l s.next (s.next + 1))) ++
          out [(s.next, s.next + 1), (s.next, 2), (s.next + 1, 2)] ++ (out s.em ++ o0),
        s.next, 0, ((l.1, l.2, s.next, s.next + 1) :: s.prev).flatMap dTok, [], [], [], 0 + 1, 0⟩
      obtain ⟨v₃, r₃⟩ := aft_pos m₂ v₂ rfl
      obtain ⟨v₄, r₄⟩ := fAB_run {m₂ with f := 0} v₃ true
      have r₅ := fC_step {m₂ with f := 0, r := s.next + 0} v₄ true
      obtain ⟨v₆, r₆⟩ := lits_run Lb R hR o0 ls (colOcc l s).2 (colOcc l s).1
        (τ + 1 + (Check.litRev l).length) v₄
        ((hinv.bump (s' := s) rfl le_rfl (by omega)).occ l rfl (by simp only [colOcc]; omega)
          (by simp only [colOcc]; omega))
        (by simp only [colOcc]; omega) (by omega)
      have hmid : (⟨some .lits, v₄, {m₂ with
          f := 0, r := s.next + 0 + (if true then 0 else 4),
          n := s.next + (if true then 2 else 5)}.stk⟩ : TM2.Cfg Γ Lab Bool) =
          ⟨some .lits, v₄, (enc (colOcc l s).1 (ls.flatMap Check.litRev ++ R) o0
            (colOcc l s).2 0).stk⟩ := by
        simp [m₂, enc, colOcc, out_append, out_cons]
      refine ⟨v₆, runLe_cast ((((r₁.le le_rfl).trans r₂).trans
        (((r₃.trans r₄).trans r₅).le le_rfl)).trans (runLe_cast' r₆ hmid le_rfl rfl)) ?_ rfl⟩
      have hc := lit_cost (Lb := Lb) (r := 0) (w := (encodeNat l.1).length) (by omega) hinv.1
        (Nat.zero_le _) hinv.2.1 hinv.2.2.1
      have hK : budget Lb ≤ (Check.litRev l).length * budget Lb :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [enc]
      nlinarith

/-- **The emitter on a list of clauses.** Let $L_b$ be a natural number, $o_0$ a list of bits,
$C_s$ a list of clauses, $s$ a construction state and $\tau$ a natural number, and let $T$ be the
concatenation over the clauses $C$ of $C_s$, in order, of the tokens of $C$ as they lie on the
token stack. If the size invariant holds for $\tau$ and $s$ and $\tau + |T| \le L_b$, then for
every local state $v$ the emitter goes from label cls with the quiescent state of $s$ with
tokens $T$, output above $o_0$, OR output $0$ and first-literal flag $0$, to label cls again,
with some local state, in at most $|T| \cdot (400 (L_b + 1)^2 + 1)$ steps. It ends in the
quiescent state of $s'$ with no tokens, output above $o_0$, OR output $0$ and first-literal
flag $0$, where $s'$ is obtained from $s$ by applying the one-clause step of the 3-coloring
construction to the clauses of $C_s$ in order. -/
theorem formula_run (Lb : ℕ) (o0 : List Bool) : ∀ (Cs : CNF) (s : ColSt) (τ : ℕ) (v : Bool),
    Inv τ s → τ + (Cs.flatMap Check.clRev).length ≤ Lb →
    ∃ v', RunLe prog ((Cs.flatMap Check.clRev).length * (budget Lb + 1))
      ⟨some .cls, v, (enc s (Cs.flatMap Check.clRev) o0 0 0).stk⟩
      ⟨some .cls, v', (enc (Cs.foldl (fun s C => colClause C s) s) [] o0 0 0).stk⟩ := by
  intro Cs
  induction Cs with
  | nil => intro s τ v _ _; exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) rfl⟩
  | cons C Cs ih =>
      intro s τ v hinv hb
      have hR : Cs.flatMap Check.clRev = [] ∨ (Cs.flatMap Check.clRev).head? = some .cl := by
        cases Cs with
        | nil => left; rfl
        | cons C' Cs' => right; simp [List.flatMap_cons, Check.clRev]
      simp only [List.flatMap_cons, List.length_append] at hb
      obtain ⟨v₁, r₁⟩ := clause_run Lb C (Cs.flatMap Check.clRev) hR o0 s τ v hinv (by omega)
      obtain ⟨v₂, r₂⟩ := ih (colClause C s) (τ + (Check.clRev C).length) v₁
        (inv_colClause C s τ hinv) (by omega)
      refine ⟨v₂, runLe_cast (r₁.trans r₂) (by simp [List.flatMap_cons, add_mul]) rfl⟩

/-! ### The emitter -/

/-- **Correctness and step bound of the 3-COLOR emitter.** Let $\varphi$ be a CNF formula
with token list $t(\varphi)$, let $o$ be a bit list and $v$ a Boolean. Started at its start
label with local state $v$, with the token stack holding $t(\varphi)$ reversed, the output
stack holding $o$ and every other stack empty, the emitter machine reaches the label
$\mathsf{done}$ within $500\,(|t(\varphi)| + 1)^4$ steps, in some local state and with some
stacks whose output stack holds the 3-COLOR instance of $\varphi$ followed by $o$ (read
top-first). -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (500 * ((toks φ).length + 1) ^ 4) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = toCol φ ++ o := by
  have hSt : St = (MS.mk (toks φ).reverse o 0 0 [] [] [] [] 0 0).stk := by
    funext k
    cases k
    · exact hT
    · exact hO
    all_goals exact h0 _ (by decide) (by decide)
  set L := (toks φ).length with hL
  let s0 : ColSt := ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩
  have hinv0 : Inv 0 s0 := by simp [Inv, s0]
  have hTr : (toks φ).reverse = φ.reverse.flatMap Check.clRev := Check.toks_reverse φ
  have hL' : (φ.reverse.flatMap Check.clRev).length = L := by rw [← hTr, List.length_reverse]
  have r₁ := init_step (MS.mk (toks φ).reverse o 0 0 [] [] [] [] 0 0) v
  obtain ⟨v₂, r₂⟩ := formula_run L o φ.reverse s0 0 v hinv0 (by omega)
  have hfin := (inv_foldl φ.reverse s0 0 hinv0).1
  have r₃ := cls_nil (enc (colSt φ) [] o 0 0) v₂ rfl
  obtain ⟨v₄, r₄⟩ := site_run .fin (enc (colSt φ) [] o 0 0) true
  refine ⟨v₄, {enc (colSt φ) [] o 0 0 with
    o := atom (enc (colSt φ) [] o 0 0) .fin ++ (enc (colSt φ) [] o 0 0).o}.stk, ?_, ?_⟩
  · rw [hSt]
    refine runLe_cast (((r₁.le le_rfl).trans (runLe_cast' r₂ ?_ le_rfl rfl)).trans
      ((r₃.trans r₄).le le_rfl)) ?_ rfl
    · simp [enc, s0, pal, hTr]
    · rw [hL'] at hfin
      change (colSt φ).next ≤ 5 * (0 + L) + 3 at hfin
      simp only [enc, MS.val, Site.src, budget, hL'] at hfin ⊢
      have h3 : (L + 1) ^ 3 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : L + 1 ≤ (L + 1) ^ 4 := by
        calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
          _ ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : L * (400 * (L + 1) ^ 2 + 1) ≤ 400 * (L + 1) ^ 3 + L := by
        have : L * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by
          calc L * (L + 1) ^ 2 ≤ (L + 1) * (L + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ = (L + 1) ^ 3 := by rw [pow_succ (L + 1) 2, Nat.mul_comm]
        nlinarith
      nlinarith
  · simp [enc, atom, MS.val, Site.src, Site.top, toCol_eq]

end Cslib.Complexity.Karp.EmitColor
