/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueVerify
public import CSLibExt.Computability.Complexity.Karp.ThreeSatEmit
public import CSLibExt.Computability.Complexity.SatLookup
public import CSLibExt.Computability.Complexity.SatCheck

/-!
# SAT ≤ CLIQUE, component 2: the emitter machine

A `TM2` machine that walks the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes Karp's CLIQUE instance `toClique φ` onto the output
stack `O`, so that `O` reads the instance top-first (`run`). The pair bits are pushed in reverse
order of the encoding: rows `i` descending and, within a row, columns `j` ascending.

* The token stack lists the clauses last-first and, per clause, its literals last-first, so the
  occurrences come as `N - 1, …, 0`. Walked occurrences are kept on the stack `D`, as a marker
  `lit p` above the name bits (`dTok`), with a `cl` marker pushed at the start of each clause.
  Then `D`, read top-down, lists the occurrences above the current one in ascending order, with
  a `cl` after the current clause's later occurrences (`items`).
* Occurrence `i` (a `lit p` token, `p` kept in the label) moves its name to `A`, walks `D`
  top-down onto `E` and pushes one bit per later occurrence `j`: `false` before the first `cl`
  (same clause), else `!(name_i = name_j && p_i != p_j)` (`adjL`), comparing the names with
  `cmpB` and restoring them with `moveB_restore`. Then `E` goes back onto `D` and occurrence
  `i`'s tokens go on top of `D`.
* `C` and `N` count clauses and occurrences; at the end the prefix of `encodeKG` is pushed.

The spec side (`bitsRec`, `rowsF`) relates the pushed bits to `cliqueBits` through
`KGVerify.pairs_succ`;
the machine side follows the 3SAT emitter: one-step lemmas, the walk over `D` by induction on its
items (`walk_run`), then literals, clauses and the formula by forward induction. Each occurrence
walks `D` once, so the step count is quadratic in `|toks φ|`; `run` states it as
`8 (|toks φ| + 1)³`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitClique

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier
open Cslib.Complexity.SatVerifier.Lookup (isBitBlock_map isBitBlock_rev)

/-! ### The pair bits, recursively -/

/-- **Karp adjacency of two literals.** For literals $l = (x, p)$ and $l' = (x', q)$, each a
variable $x, x' \in \mathbb{N}$ with a polarity $p, q \in \{\mathrm{true}, \mathrm{false}\}$, the
adjacency bit of $l$ and $l'$ is false when they are complementary, that is $x = x'$ and
$p \ne q$, and true otherwise. It is the adjacency of two occurrences in different clauses in
Karp's graph. -/
def adjL (l l' : ℕ × Bool) : Bool := !(l.1 == l'.1 && l.2 != l'.2)

/-- **Row-by-row pair bits of an occurrence list.** For a list of literal occurrences (clause
index, variable, polarity), the row-by-row pair bits are defined recursively: the empty list has
none, and for a list $o, o_1, \dots, o_k$ they are the adjacency bits of $o$ with
$o_k, \dots, o_1$, in that order, followed by the row-by-row pair bits of $o_1, \dots, o_k$.
Two occurrences are adjacent when they lie in different clauses and are not complementary. -/
def bitsRec : List (ℕ × ℕ × Bool) → List Bool
  | [] => []
  | o :: os => (os.map (occAdj o)).reverse ++ bitsRec os

theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- **Pair bits of an occurrence list, row by row.** Let $o_0, \dots, o_{m-1}$ be a list of
literal occurrences (clause index, variable, polarity). The list of adjacency bits of $o_i$ and
$o_j$ over the pairs $(i, j)$ with $i < j < m$ in encoding order (rows $i$ ascending, and $j$
descending within a row) equals the recursive pair bits of the list, which are empty for the
empty list and otherwise are the adjacency bits of $o_0$ with $o_{m-1}, o_{m-2}, \dots, o_1$, in
this order, followed by the recursive pair bits of $o_1, \dots, o_{m-1}$. Two occurrences are
adjacent when they lie in different clauses and are not complementary. -/
theorem pairBits_eq (os : List (ℕ × ℕ × Bool)) :
    (pairs os.length).map (fun p => occAdj (os.getD p.1 (0, 0, false))
      (os.getD p.2 (0, 0, false))) = bitsRec os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
      rw [List.length_cons, KGVerify.pairs_succ, List.map_reverse, List.map_append, bitsRec, ← ih]
      congr 1
      · rw [List.map_reverse, List.map_map]
        conv_rhs => rw [← map_getD_range os (0, 0, false)]
        simp [Function.comp_def]
      · simp [Function.comp_def]

theorem cliqueBits_eq (φ : CNF) : cliqueBits φ = bitsRec (occs φ) := pairBits_eq _

/-- **Row-by-row pair bits see only adjacency.** Call two literal occurrences (clause index,
variable, polarity) adjacent when they lie in different clauses and are not complementary. Let
$f$ be a map on occurrences such that $f(a)$ and $f(b)$ are adjacent exactly when $a$ and $b$
are, for all occurrences $a$ and $b$. Then for every list of occurrences $o_1, \dots, o_k$, the
row-by-row pair bits of $f(o_1), \dots, f(o_k)$ equal those of $o_1, \dots, o_k$. -/
theorem bitsRec_map (f : ℕ × ℕ × Bool → ℕ × ℕ × Bool)
    (hf : ∀ a b, occAdj (f a) (f b) = occAdj a b) (os : List (ℕ × ℕ × Bool)) :
    bitsRec (os.map f) = bitsRec os := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [bitsRec, ih, Function.comp_def, hf]

/-- **Occurrences of a formula with a first clause.** Let $C$ be a clause and $\varphi$ a CNF
formula, and write a literal occurrence as a pair $(i, \ell)$ of a clause index $i$ and a literal
$\ell$. The list of literal occurrences of the formula whose first clause is $C$ and whose
remaining clauses are those of $\varphi$ is the list of $(0, \ell)$ for the literals $\ell$ of $C$
in order, followed by the list of $(i + 1, \ell)$ for the occurrences $(i, \ell)$ of $\varphi$ in
order. -/
theorem occs_cons (C : CNFClause) (φ : CNF) :
    occs (C :: φ) = C.map (fun l => (0, l)) ++ (occs φ).map fun o => (o.1 + 1, o.2) := by
  simp [occs, List.zipIdx_succ, List.flatMap_map, List.map_flatMap, Function.comp_def]

theorem occs_snd (φ : CNF) : (occs φ).map Prod.snd = φ.flatten := by
  induction φ with
  | nil => rfl
  | cons C φ ih => rw [occs_cons]; simp [Function.comp_def, ← ih]

/-! ### The bits pushed by the walk -/

/-- **Polarity-first tokens of a literal.** For a literal $(x, p)$ with variable index
$x \in \mathbb{N}$ and polarity $p$, the token list is the polarity marker symbol for $p$
followed by one name-bit symbol for each bit of the canonical binary representation of $x$
(least significant bit first, empty for $x = 0$), in order.

This is how the CLIQUE emitter writes a walked literal occurrence on its stack $D$, top first. -/
def dTok (l : ℕ × Bool) : List Sym := .lit l.2 :: (encodeNat l.1).map .bit

/-- **Tokens of an item on the walked stack.** An item of the stack $D$ is either $\mathrm{none}$,
standing for a clause marker, or an occurrence $(x, p)$ of the variable $x$ with polarity $p$. The
tokens of $\mathrm{none}$ are the single clause-marker symbol; the tokens of $(x, p)$ are the
polarity marker of $p$ followed by the binary encoding of $x$ as name-bit symbols. -/
def itemTok : Option (ℕ × Bool) → List Sym
  | none => [.cl]
  | some l => dTok l

/-- **Bits pushed by a walk of the CLIQUE emitter.** Let $l = (x, p)$ be a literal occurrence
with name $x \in \mathbb{N}$ and polarity $p$, let $f$ be a Boolean, and let $ds$ be a list whose
items are literal occurrences or clause markers. The bit list $\mathrm{walkBits}(l, f, ds)$ is
defined by recursion on $ds$: it is empty if $ds$ is empty; if $ds$ is a clause marker followed
by $ds'$, it is $\mathrm{walkBits}(l, \mathrm{true}, ds')$; and if $ds$ is an occurrence $l'$
followed by $ds'$, it is the bit $f \wedge \mathrm{adj}(l, l')$ followed by
$\mathrm{walkBits}(l, f, ds')$. Here $\mathrm{adj}(l, l')$ is the Karp adjacency of literals: it
is false exactly when $l$ and $l'$ have the same name and opposite polarities.

The flag $f$ records whether a clause marker has been passed; while it is false, each occurrence
contributes a false bit. -/
def walkBits (l : ℕ × Bool) : Bool → List (Option (ℕ × Bool)) → List Bool
  | _, [] => []
  | _, none :: ds => walkBits l true ds
  | f, some l' :: ds => (f && adjL l l') :: walkBits l f ds

/-- **Walked items of a formula.** For a CNF formula $\varphi$ with clauses $C_1, \dots, C_m$ in
order, the items of $\varphi$ are the list made of, for each $i = 1, \dots, m$ in turn, the
literals of $C_i$ in order, each as an occurrence item, followed by one clause-marker item
$\mathrm{none}$. These are the items on the stack $D$ once the clauses of $\varphi$ are walked. -/
def items (φ : CNF) : List (Option (ℕ × Bool)) := φ.flatMap fun C => C.map some ++ [none]

/-- **Rows pushed for a clause's literals.** For a list $I$ of items and literals
$l_1, \dots, l_k$, the rows are the concatenation, for $i = 1, \dots, k$ in turn, of the reverse
of the walk bits of $l_i$ with flag false over the items $l_{i+1}, \dots, l_k$ (as occurrence
items) followed by $I$. These are the bits pushed when the literals of a clause are walked above
the items $I$. -/
def lrows (ds : List (Option (ℕ × Bool))) : List (ℕ × Bool) → List Bool
  | [] => []
  | l :: Ls => (walkBits l false (Ls.map some ++ ds)).reverse ++ lrows ds Ls

/-- **Row bits of a formula for the CLIQUE emitter.** A literal is a pair $(x, s)$ of a variable
$x \in \mathbb{N}$ and a polarity $s$, and an item is a literal or a clause marker. For a literal
$\ell = (x, s)$, a Boolean $f$ and a list of items, the walk bits are defined by recursion on the
list: there are none for the empty list; for a list starting with a clause marker they are the
walk bits of the rest with $f$ replaced by true; for a list starting with a literal $(x', s')$
they are the bit "$f$ and not ($x = x'$ and $s \ne s'$)" followed by the walk bits of the rest
with the same $f$. For a list $\delta$ of items, the rows of a list of literals are none for the
empty list, and for a list $\ell_1, \dots, \ell_k$ with $k \ge 1$ they are the reverse of the walk
bits of $\ell_1$ with $f$ false over the list $\ell_2, \dots, \ell_k$ followed by $\delta$, then
the rows of $\ell_2, \dots, \ell_k$. The items of a CNF formula $\psi$ are, for each clause of
$\psi$ in order, its literals followed by a clause marker. The row bits of a CNF formula are
defined by recursion on its clauses: the empty formula has none, and for the formula with first
clause $C$ and remaining clauses $\varphi$ they are the rows of the literals of $C$ for $\delta$
the clause marker followed by the items of $\varphi$, followed by the row bits of $\varphi$. -/
def rowsF : CNF → List Bool
  | [] => []
  | C :: φ => lrows (none :: items φ) C ++ rowsF φ

theorem walkBits_true_some (l : ℕ × Bool) (Ls : List (ℕ × Bool))
    (ds : List (Option (ℕ × Bool))) :
    walkBits l true (Ls.map some ++ ds) = Ls.map (adjL l) ++ walkBits l true ds := by
  induction Ls with
  | nil => rfl
  | cons l' Ls ih => simp [walkBits, ih]

theorem walkBits_false_some (l : ℕ × Bool) (Ls : List (ℕ × Bool))
    (ds : List (Option (ℕ × Bool))) :
    walkBits l false (Ls.map some ++ none :: ds) =
      List.replicate Ls.length false ++ walkBits l true ds := by
  induction Ls with
  | nil => rfl
  | cons l' Ls ih => simp [walkBits, ih, List.replicate_succ]

theorem walkBits_items (l : ℕ × Bool) (φ : CNF) :
    walkBits l true (items φ) = φ.flatten.map (adjL l) := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
      simp only [items, List.flatMap_cons, List.append_assoc, List.singleton_append] at ih ⊢
      rw [walkBits_true_some, walkBits, ih]
      simp

/-- **Pair bits of a leading clause.** Let $C$ be a clause and $\varphi$ a CNF formula. Let
$O_\varphi$ be the list of literal occurrences of $\varphi$ (clause index, variable, polarity),
with every clause index increased by $1$. Then the row-by-row pair bits of the list made of the
literals of $C$, each with clause index $0$, followed by $O_\varphi$, are the rows pushed for the
literals of $C$ walked above a clause marker and the items of $\varphi$, followed by the
row-by-row pair bits of $O_\varphi$. -/
theorem bitsRec_clause (C : CNFClause) (φ : CNF) :
    bitsRec (C.map (fun l => (0, l)) ++ (occs φ).map fun o => (o.1 + 1, o.2)) =
      lrows (none :: items φ) C ++ bitsRec ((occs φ).map fun o => (o.1 + 1, o.2)) := by
  induction C with
  | nil => rfl
  | cons l Ls ih =>
      rw [List.map_cons, List.cons_append, bitsRec, ih, lrows, walkBits_false_some,
        walkBits_items, ← occs_snd, ← List.append_assoc]
      congr 2
      simp [occAdj, adjL, Function.comp_def]

/-- **The CLIQUE emitter's row bits are Karp's pair bits.** For every CNF formula $\varphi$, the
row bits of $\varphi$ equal the pair bits of Karp's CLIQUE graph of $\varphi$: with
$o_0, \dots, o_{m-1}$ the literal occurrences of $\varphi$, these are, for the pairs $(i, j)$ with
$i < j < m$ in encoding order (rows $i$ ascending, and $j$ descending within a row), the bits
telling whether $o_i$ and $o_j$ lie in different clauses and are not complementary. -/
theorem rowsF_eq (φ : CNF) : rowsF φ = cliqueBits φ := by
  rw [cliqueBits_eq]
  induction φ with
  | nil => rfl
  | cons C φ ih =>
      rw [rowsF, occs_cons, bitsRec_clause, ih, bitsRec_map]
      intro a b
      simp [occAdj]

/-! ### The machine -/

/-- **Stacks of the SAT-to-CLIQUE emitter.** The emitter has nine stacks: $T$ (tokens), $O$
(output), $A$ (the current name), $B$ (scratch), $D$ (walked occurrences), $E$ (the walk's other
side), $X$ (scratch), $C$ (the clause count) and $N$ (the occurrence count). -/
inductive K | T | O | A | B | D | E | X | C | N
  deriving DecidableEq

/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.O, K.A, K.B, K.D, K.E, K.X, K.C, K.N], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the CLIQUE emitter.** In the CLIQUE emitter, the output stack $O$ has
the Booleans as its alphabet, and every other stack has the token symbols as its alphabet.

The counter stacks $C$ and $N$ hold copies of the clause marker. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Labels of the SAT-to-CLIQUE emitter.** For bits $p, q, f, b$ the labels are
$\mathsf{start}$, $\mathsf{lits}$, $\mathsf{nm}(p)$, $\mathsf{walk}(p, f)$, $\mathsf{cmp}(p, q)$,
$\mathsf{res}(p, b)$, $\mathsf{rsA}(p)$, $\mathsf{rsD}(p)$, $\mathsf{mvN}(p, f)$,
$\mathsf{back}(p)$, $\mathsf{put}(p)$, $\mathsf{put2}(p)$, $\mathsf{put3}(p)$, $\mathsf{fin}$,
$\mathsf{finN}$, $\mathsf{fin2}$, $\mathsf{finC}$ and $\mathsf{done}$. Here $p$ is the polarity
of the current occurrence. $\mathsf{start}$ begins a clause and $\mathsf{lits}$ pops a literal
marker; $\mathsf{nm}$ moves its name to $A$; $\mathsf{walk}(p, f)$ walks $D$, where $f$ tells
whether a clause marker was passed; $\mathsf{cmp}(p, q)$, $\mathsf{res}$, $\mathsf{rsA}$ and
$\mathsf{rsD}$ compare with an occurrence of polarity $q$, push the bit $b$ and restore;
$\mathsf{mvN}$ moves that occurrence's name to $E$; $\mathsf{back}$ moves $E$ back to $D$;
$\mathsf{put}$, $\mathsf{put2}$ and $\mathsf{put3}$ put the current occurrence on $D$;
$\mathsf{fin}$ to $\mathsf{finC}$ push the instance prefix, and $\mathsf{done}$ halts. -/
inductive Lab
  | start | lits | nm (p : Bool) | walk (p f : Bool) | cmp (p q : Bool) | res (p b : Bool)
  | rsA (p : Bool) | rsD (p : Bool) | mvN (p f : Bool) | back (p : Bool) | put (p : Bool)
  | put2 (p : Bool) | put3 (p : Bool) | fin | finN | fin2 | finC | done
  deriving DecidableEq

/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.start, .lits, .fin, .finN, .fin2, .finC, .done] ++
      ([true, false].flatMap fun p =>
        [Lab.nm p, .rsA p, .rsD p, .back p, .put p, .put2 p, .put3 p]) ++
      ([(true, true), (true, false), (false, true), (false, false)].flatMap
        fun q : Bool × Bool => [Lab.walk q.1 q.2, .cmp q.1 q.2, .res q.1 q.2, .mvN q.1 q.2]))
    (fun x => by cases x <;> (try rename_i a b; cases a <;> cases b) <;>
      (try rename_i a; cases a) <;> decide)

/-- **The CLIQUE emitter machine.** The CLIQUE emitter is the multi-stack machine with stacks
$T, O, A, B, D, E, X, C, N$, a Boolean flag and the labels named below. The stack $O$ holds
Booleans and the others hold symbols, among them the bit symbols $\mathrm{bit}(b)$, the literal
symbols $\mathrm{lit}(p)$ and the clause marker $\mathrm{cl}$. Each test sets the flag to its
outcome, a pop that reads a polarity or a bit sets the flag to it, and other pops leave the flag
unchanged. To move the bits of $Y$ to $Z$ and then go to $\lambda$ means: while the top of $Y$ is
a bit symbol, pop it and push it onto $Z$; once $Y$ is empty or its top is another symbol, go to
$\lambda$ (the flag serves as scratch). The instruction at each label is as follows.

At $\mathrm{start}$: test whether $T$ is empty; if so go to $\mathrm{fin}$, else pop $T$, push
$\mathrm{cl}$ onto $D$ and onto $C$, and go to $\mathrm{lits}$. At $\mathrm{lits}$: test whether
the top of $T$ is a literal symbol; if so pop it, reading the polarity $q$ (true exactly for
$\mathrm{lit}(\mathrm{true})$), push $\mathrm{cl}$ onto $N$ and go to $\mathrm{nm}(q)$; else go
to $\mathrm{start}$. At $\mathrm{nm}(p)$: move the bits of $T$ to $A$, then go to
$\mathrm{walk}(p, \mathrm{false})$. At $\mathrm{walk}(p, f)$: test whether $D$ is empty; if so
go to $\mathrm{back}(p)$; else test whether the top of $D$ is $\mathrm{cl}$; if so pop it, push
$\mathrm{cl}$ onto $E$ and go to $\mathrm{walk}(p, \mathrm{true})$; else pop $D$, reading $q$
(true exactly for $\mathrm{lit}(\mathrm{true})$), push $\mathrm{lit}(q)$ onto $E$, and if $f$ go
to $\mathrm{cmp}(p, q)$, else push false onto $O$ and go to $\mathrm{mvN}(p, \mathrm{false})$.
At $\mathrm{cmp}(p, q)$: compare the bits of $A$ and $D$, that is, while both tops are bit
symbols of the same bit, pop both and push that bit symbol onto $X$ and onto $B$; when both bit
blocks end together go to $\mathrm{res}(p, b)$ with $b$ true exactly when $p = q$, and on a
mismatch (different bits, or one block ending first) go to $\mathrm{res}(p, \mathrm{true})$
without popping (the flag serves as scratch). At $\mathrm{res}(p, b)$: push $b$ onto $O$ and go
to $\mathrm{rsA}(p)$. At $\mathrm{rsA}(p)$: move the bits of $X$ to $A$, then go to
$\mathrm{rsD}(p)$. At $\mathrm{rsD}(p)$: move the bits of $B$ to $D$, then go to
$\mathrm{mvN}(p, \mathrm{true})$. At $\mathrm{mvN}(p, f)$: move the bits of $D$ to $E$, then go
to $\mathrm{walk}(p, f)$. At $\mathrm{back}(p)$: test whether $E$ is empty; if so go to
$\mathrm{put}(p)$; else test whether its top is $\mathrm{cl}$; if so pop it and push
$\mathrm{cl}$ onto $D$; else test whether its top is a literal symbol; if so pop it, reading $q$
(true exactly for $\mathrm{lit}(\mathrm{true})$), and push $\mathrm{lit}(q)$ onto $D$; else pop
it, reading $b$ (true exactly for $\mathrm{bit}(\mathrm{true})$), and push $\mathrm{bit}(b)$ onto
$D$; in these three cases stay at $\mathrm{back}(p)$. At $\mathrm{put}(p)$: move the bits of $A$
to $B$, then go to $\mathrm{put2}(p)$. At $\mathrm{put2}(p)$: move the bits of $B$ to $D$, then
go to $\mathrm{put3}(p)$. At $\mathrm{put3}(p)$: push $\mathrm{lit}(p)$ onto $D$ and go to
$\mathrm{lits}$. At $\mathrm{fin}$: push false onto $O$ and go to $\mathrm{finN}$. At
$\mathrm{finN}$: pop $N$, testing whether a symbol was popped; if so push true onto $O$ and stay,
else go to $\mathrm{fin2}$. At $\mathrm{fin2}$: push false onto $O$ and go to $\mathrm{finC}$. At
$\mathrm{finC}$: pop $C$, testing whether a symbol was popped; if so push true onto $O$ and stay,
else go to $\mathrm{done}$. At $\mathrm{done}$: halt. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .start => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .fin) <|
      .pop .T (fun s _ => s) <| .push .D (fun _ => Sym.cl) <| .push .C (fun _ => Sym.cl) <|
        .goto fun _ => .lits
  | .lits => .peek .T (fun _ o => Emit3.isLit o) <| .branch id
      (.pop .T (fun _ o => o == some (.lit true)) <| .push .N (fun _ => Sym.cl) <|
        .goto fun s => .nm s)
      (.goto fun _ => .start)
  | .nm p => moveB .T .A Sym.bit? Sym.bit (.nm p) (.walk p false)
  | .walk p f => .peek .D (fun _ o => o.isNone) <| .branch id (.goto fun _ => .back p) <|
      .peek .D (fun _ o => o == some .cl) <| .branch id
        (.pop .D (fun s _ => s) <| .push .E (fun _ => Sym.cl) <| .goto fun _ => .walk p true)
        (.pop .D (fun _ o => o == some (.lit true)) <| .push .E (fun s => Sym.lit s) <|
          if f then .goto fun s => .cmp p s
          else .push .O (fun _ => false) <| .goto fun _ => .mvN p false)
  | .cmp p q => cmpB .A .D .X .B Sym.bit? Sym.bit? Sym.bit Sym.bit (.cmp p q) (.res p (p == q))
      (.res p true)
  | .res p b => .push .O (fun _ => b) <| .goto fun _ => .rsA p
  | .rsA p => moveB .X .A Sym.bit? Sym.bit (.rsA p) (.rsD p)
  | .rsD p => moveB .B .D Sym.bit? Sym.bit (.rsD p) (.mvN p true)
  | .mvN p f => moveB .D .E Sym.bit? Sym.bit (.mvN p f) (.walk p f)
  | .back p => .peek .E (fun _ o => o.isNone) <| .branch id (.goto fun _ => .put p) <|
      .peek .E (fun _ o => o == some .cl) <| .branch id
        (.pop .E (fun s _ => s) <| .push .D (fun _ => Sym.cl) <| .goto fun _ => .back p) <|
      .peek .E (fun _ o => Emit3.isLit o) <| .branch id
        (.pop .E (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
          .goto fun _ => .back p)
        (.pop .E (fun _ o => o == some (.bit true)) <| .push .D (fun s => Sym.bit s) <|
          .goto fun _ => .back p)
  | .put p => moveB .A .B Sym.bit? Sym.bit (.put p) (.put2 p)
  | .put2 p => moveB .B .D Sym.bit? Sym.bit (.put2 p) (.put3 p)
  | .put3 p => .push .D (fun _ => Sym.lit p) <| .goto fun _ => .lits
  | .fin => .push .O (fun _ => false) <| .goto fun _ => .finN
  | .finN => xferE .N .O [true] .finN .fin2
  | .fin2 => .push .O (fun _ => false) <| .goto fun _ => .finC
  | .finC => xferE .C .O [true] .finC .done
  | .done => .halt

/-- **Start label of the CLIQUE emitter.** The start label of the CLIQUE emitter machine is its
label $\mathsf{start}$. -/
def start : Lab := .start

/-! ### Machine states -/

/-- **Configuration stacks of the CLIQUE emitter.** For a token stack $t$, an output stack $o$
of bits, stacks $a$, $d$, $e$ of token symbols and natural numbers $c$ and $n$, this assigns to
each stack of the CLIQUE emitter its contents: the token stack $T$ holds $t$, the output stack
$O$ holds $o$, the name stack $A$ holds $a$, the walked-occurrence stack $D$ holds $d$, the
walk's other stack $E$ holds $e$, the clause counter $C$ holds $c$ copies of the clause marker,
the occurrence counter $N$ holds $n$ copies of the clause marker, and the scratch stacks $B$ and
$X$ are empty. -/
def st (t : List Sym) (o : List Bool) (a d e : List Sym) (c n : ℕ) : ∀ k, List (Γ k)
  | .T => t
  | .O => o
  | .A => a
  | .B => []
  | .D => d
  | .E => e
  | .X => []
  | .C => cnt Sym.cl c
  | .N => cnt Sym.cl n

section States

variable (t : List Sym) (o : List Bool) (a d e : List Sym) (c n : ℕ)

@[simp] theorem st_T : st t o a d e c n .T = t := rfl
@[simp] theorem st_O : st t o a d e c n .O = o := rfl
@[simp] theorem st_A : st t o a d e c n .A = a := rfl
@[simp] theorem st_B : st t o a d e c n .B = [] := rfl
@[simp] theorem st_D : st t o a d e c n .D = d := rfl
@[simp] theorem st_E : st t o a d e c n .E = e := rfl
@[simp] theorem st_X : st t o a d e c n .X = [] := rfl
@[simp] theorem st_C : st t o a d e c n .C = List.replicate c Sym.cl := rfl
@[simp] theorem st_N : st t o a d e c n .N = List.replicate n Sym.cl := rfl

@[simp] theorem st_upd_T (t' : List Sym) :
    update (st t o a d e c n) .T t' = st t' o a d e c n := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_O (o' : List Bool) :
    update (st t o a d e c n) .O o' = st t o' a d e c n := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_A (a' : List Sym) :
    update (st t o a d e c n) .A a' = st t o a' d e c n := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_D (d' : List Sym) :
    update (st t o a d e c n) .D d' = st t o a d' e c n := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_E (e' : List Sym) :
    update (st t o a d e c n) .E e' = st t o a d e' c n := by
  funext k; cases k <;> rfl

@[simp] theorem st_upd_C (x : List (Γ .C)) (hx : x = Sym.cl :: List.replicate c Sym.cl) :
    update (st t o a d e c n) .C x = st t o a d e (c + 1) n := by
  subst hx; funext k; cases k <;> rfl

@[simp] theorem st_upd_N (x : List (Γ .N)) (hx : x = Sym.cl :: List.replicate n Sym.cl) :
    update (st t o a d e c n) .N x = st t o a d e c (n + 1) := by
  subst hx; funext k; cases k <;> rfl

end States

/-- **CLIQUE emitter: recognizing a standard state.** Let $S$ assign contents to the stacks of
the CLIQUE emitter and let $c, n \in \mathbb{N}$. If the scratch stacks $B$ and $X$ are empty and
the counters $C$ and $N$ hold exactly $c$ and $n$ clause markers, then $S$ is the standard state
whose stacks $T$, $O$, $A$, $D$, $E$ hold what they hold in $S$, whose stacks $B$ and $X$ are
empty and whose counters $C$ and $N$ hold $c$ and $n$ clause markers. -/
theorem st_eq {S : ∀ k, List (Γ k)} {c n : ℕ} (hB : S .B = []) (hX : S .X = [])
    (hC : S .C = cnt Sym.cl c) (hN : S .N = cnt Sym.cl n) :
    S = st (S .T) (S .O) (S .A) (S .D) (S .E) c n := by
  funext k; cases k <;> first | rfl | assumption

/-! ### One-step lemmas -/

/-- **Tokens moved by the walk.** A symbol is a token of the walk between the stacks $D$ and $E$
when it is a name bit, a literal marker or a clause marker; the value symbols and the dead
symbol are not. -/
def isTok : Sym → Bool
  | .bit _ | .lit _ | .cl => true
  | _ => false

section Steps

variable (v : Bool) (t : List Sym) (o : List Bool) (a d e : List Sym) (c n : ℕ)

theorem start_nil : Run prog 1 ⟨some .start, v, st [] o a d e c n⟩
    ⟨some .fin, true, st [] o a d e c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem start_cl (R : List Sym) : Run prog 1 ⟨some .start, v, st (.cl :: R) o a d e c n⟩
    ⟨some .lits, false, st R o a (.cl :: d) e (c + 1) n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem lits_lit (p : Bool) (R : List Sym) :
    Run prog 1 ⟨some .lits, v, st (.lit p :: R) o a d e c n⟩
      ⟨some (.nm p), p, st R o a d e c (n + 1)⟩ :=
  Run.single (by cases p <;> simp [prog, TM2.stepAux, Emit3.isLit])

theorem lits_end (h : Emit3.isLit t.head? = false) :
    Run prog 1 ⟨some .lits, v, st t o a d e c n⟩ ⟨some .start, false, st t o a d e c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem walk_nil (p f : Bool) : Run prog 1 ⟨some (.walk p f), v, st t o a [] e c n⟩
    ⟨some (.back p), true, st t o a [] e c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem walk_cl (p f : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.walk p f), v, st t o a (.cl :: R) e c n⟩
      ⟨some (.walk p true), true, st t o a R (.cl :: e) c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem walk_lit_false (p q : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.walk p false), v, st t o a (.lit q :: R) e c n⟩
      ⟨some (.mvN p false), q, st t (false :: o) a R (.lit q :: e) c n⟩ :=
  Run.single (by cases q <;> simp [prog, TM2.stepAux])

theorem walk_lit_true (p q : Bool) (R : List Sym) :
    Run prog 1 ⟨some (.walk p true), v, st t o a (.lit q :: R) e c n⟩
      ⟨some (.cmp p q), q, st t o a R (.lit q :: e) c n⟩ :=
  Run.single (by cases q <;> simp [prog, TM2.stepAux])

theorem back_nil (p : Bool) : Run prog 1 ⟨some (.back p), v, st t o a d [] c n⟩
    ⟨some (.put p), true, st t o a d [] c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem back_step (p : Bool) (s : Sym) (hs : isTok s = true) (R : List Sym) :
    ∃ v', Run prog 1 ⟨some (.back p), v, st t o a d (s :: R) c n⟩
      ⟨some (.back p), v', st t o a (s :: d) R c n⟩ := by
  cases s with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, Emit3.isLit])⟩
  | lit q => exact ⟨q, Run.single (by cases q <;> simp [prog, TM2.stepAux, Emit3.isLit])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux])⟩
  | val _ => simp [isTok] at hs
  | dead => simp [isTok] at hs

theorem put3_step (p : Bool) : Run prog 1 ⟨some (.put3 p), v, st t o a d e c n⟩
    ⟨some .lits, v, st t o a (.lit p :: d) e c n⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

end Steps

/-! ### Phases of an occurrence -/

section Phases

theorem bit_inv (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

/-- **Name bits of a variable in the CLIQUE emitter.** For $x \in \mathbb{N}$, the name of $x$ is
the list of symbols obtained from the binary encoding of $x$ (least significant bit first, empty
for $x = 0$) by writing each bit $b$ as the bit symbol $\mathrm{bit}(b)$. This is the form in which
the stacks $A$ and $D$ of the CLIQUE emitter hold variable names. -/
abbrev name (x : ℕ) : List Sym := (encodeNat x).map Sym.bit

variable (v : Bool) (t : List Sym) (o : List Bool) (a d e : List Sym) (c n : ℕ)

/-- **CLIQUE emitter: reading a variable name.** Stacks are listed top first. Let $p$ be a Boolean,
$x \in \mathbb{N}$ with name $w$ (its binary encoding written as bit symbols) of length $\ell$, and
$R$ a list of symbols that is empty or whose top symbol is not a bit symbol. Let $v$ be a flag,
$o$ a list of Booleans, $d$ and $e$ lists of symbols, and $c, n \in \mathbb{N}$. Started at label
$\mathrm{nm}(p)$ with flag $v$, the token stack $T$ holding $w$ reversed on top of $R$, empty
stacks $A$, $B$, $X$, stacks $O$, $D$, $E$ holding $o$, $d$, $e$, and $c$ and $n$ clause markers
on the counters $C$ and $N$, the CLIQUE emitter reaches, in exactly $\ell + 1$ steps and with
some flag, the label $\mathrm{walk}(p, \mathrm{false})$ with $T$ holding $R$, $A$ holding $w$,
and all other stacks as before. -/
theorem nm_run (p : Bool) (x : ℕ) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) :
    ∃ v', Run prog ((encodeNat x).length + 1)
      ⟨some (.nm p), v, st ((name x).reverse ++ R) o [] d e c n⟩
      ⟨some (.walk p false), v', st R o (name x) d e c n⟩ := by
  obtain ⟨v', S', h, hT, hA, hk⟩ := moveB_run (M := prog) (self := .nm p)
    (next := .walk p false) (a := .T) (b := .A) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    (encodeNat x).reverse (name x).reverse R v (st ((name x).reverse ++ R) o [] d e c n) rfl
    (isBitBlock_rev _) hR
  have hS : S' = st R o (name x) d e c n := by
    funext k; cases k <;> simp [hT, hA, hk, List.map_reverse]
  exact ⟨v', by simpa [hS] using h⟩

/-- **Moving a walked name from $D$ to $E$.** Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $p, f$ be bits, $w$ a list of bits with $\bar w$ the
corresponding list of name-bit symbols, $R$ a list of symbols that is empty or does not start
with a name-bit symbol, and $t, o, a, e, c, n, v$ arbitrary. Then for some bit $v'$ the machine
goes in exactly $|w| + 1$ steps from
$\langle \mathsf{mvN}(p, f), v \mid t, o, a, \bar w R, e, c, n\rangle$ to
$\langle \mathsf{walk}(p, f), v' \mid t, o, a, R, \bar w^{\mathrm{rev}} e, c, n\rangle$, where
$\bar w^{\mathrm{rev}}$ is the reverse of $\bar w$. -/
theorem mvN_run (p f : Bool) (w : List Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) :
    ∃ v', Run prog (w.length + 1) ⟨some (.mvN p f), v, st t o a (w.map Sym.bit ++ R) e c n⟩
      ⟨some (.walk p f), v', st t o a R ((w.map Sym.bit).reverse ++ e) c n⟩ := by
  obtain ⟨v', S', h, hD, hE, hk⟩ := moveB_run (M := prog) (self := .mvN p f)
    (next := .walk p f) (a := .D) (b := .E) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    w (w.map Sym.bit) R v (st t o a (w.map Sym.bit ++ R) e c n) rfl (isBitBlock_map _) hR
  have hS : S' = st t o a R ((w.map Sym.bit).reverse ++ e) c n := by
    funext k; cases k <;> simp [hD, hE, hk]
  exact ⟨v', by simpa [hS] using h⟩

/-- **Clique emitter: comparing two names.** Let $p$, $q$ and $v$ be Booleans, $u$ and $w$ lists
of bits, $t$, $e$ and $R$ stack-symbol lists with $R$ empty or not starting with a name bit, $o$
a list of bits and $c, n \in \mathbb{N}$. Let $b$ be $(p = q)$ if $u = w$ and true otherwise.
For some flag $v'$, the emitter machine goes in at most $3|w| + 4$ steps from label
$\mathrm{cmp}(p, q)$ with flag $v$ and the state with token stack $t$, output $o$, name stack
$u$, walked stack $w$ followed by $R$, walk side $e$, clause count $c$, occurrence count $n$ and
empty scratch stacks to label $\mathrm{mvN}(p, \mathrm{true})$ with flag $v'$ and the same state
except that the output is $b$ followed by $o$. Here $u$ and $w$ lie on the stacks as name-bit
symbols. -/
theorem cmp_run (p q : Bool) (u w : List Bool) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) :
    ∃ v', RunLe prog (3 * w.length + 4)
      ⟨some (.cmp p q), v, st t o (u.map Sym.bit) (w.map Sym.bit ++ R) e c n⟩
      ⟨some (.mvN p true), v', st t ((if u = w then p == q else true) :: o) (u.map Sym.bit)
        (w.map Sym.bit ++ R) e c n⟩ := by
  have hd : Distinct4 K.A K.D K.X K.B :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1A, h1D, h1X, h1B, h1k⟩ := cmpB_run (M := prog)
    (self := .cmp p q) (eqL := .res p (p == q)) (neL := .res p true) (a := .A) (b := .D)
    (ta := .X) (tb := .B) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) rfl
    hd u w (u.map Sym.bit) [] (w.map Sym.bit) R v
    (st t o (u.map Sym.bit) (w.map Sym.bit ++ R) e c n) (by simp) rfl (isBitBlock_map u)
    (isBitBlock_map w) rfl hR
  set b := if u = w then p == q else true with hb
  have hl : (if u = w then Lab.res p (p == q) else Lab.res p true) = Lab.res p b := by
    rw [hb]; split <;> rfl
  rw [hl] at r₁
  have r₂ : Run prog 1 ⟨some (.res p b), v₁, S₁⟩
      ⟨some (.rsA p), v₁, update S₁ .O (b :: S₁ .O)⟩ :=
    Run.single (by simp [prog, TM2.stepAux])
  set S₂ := update S₁ .O (b :: S₁ .O) with hS₂
  obtain ⟨v₃, S₃, r₃, h3X, h3A, h3k⟩ := moveB_restore (M := prog) (self' := .rsA p)
    (next := .rsD p) (t := .X) (a := .A) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) rfl (by decide) (fun _ => rfl) bit_inv u cp (u.map Sym.bit) [] [] v₁ S₂
    (isBitBlock_map u) hcu (by simp [hS₂, h1X]) (by simp [hS₂, h1A]) rfl
  obtain ⟨v₄, S₄, r₄, h4B, h4D, h4k⟩ := moveB_restore (M := prog) (self' := .rsD p)
    (next := .mvN p true) (t := .B) (a := .D) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) rfl (by decide) (fun _ => rfl) bit_inv w cp (w.map Sym.bit) R [] v₃ S₃
    (isBitBlock_map w) hcw (by simp [h3k, hS₂, h1B]) (by simp [h3k, hS₂, h1D]) rfl
  have hS : S₄ = st t (b :: o) (u.map Sym.bit) (w.map Sym.bit ++ R) e c n := by
    funext k; cases k <;> simp [h4B, h4D, h4k, h3X, h3A, h3k, hS₂, h1k]
  rw [← hS]
  refine ⟨v₄, ((r₁.trans r₂).trans (r₃.trans r₄)).le ?_⟩
  have := hcw.length_le
  omega

/-- **CLIQUE emitter: putting the current occurrence on the walked stack.** Stacks are listed top
first. Let $p$ be a Boolean, $u$ a list of Booleans and $\bar u$ the list of bit symbols
$\mathrm{bit}(b)$ for $b$ in $u$, let $v$ be a flag, $t$, $d$, $e$ lists of symbols, $o$ a list of
Booleans and $c, n \in \mathbb{N}$. Started at label $\mathrm{put}(p)$ with flag $v$, stacks $T$,
$O$, $A$, $D$, $E$ holding $t$, $o$, $\bar u$, $d$, $e$, empty scratch stacks $B$ and $X$, and $c$
and $n$ clause markers on the counters $C$ and $N$, the CLIQUE emitter reaches, in exactly
$2|u| + 3$ steps and with some flag, the label $\mathrm{lits}$ with $A$ empty, $D$ holding the
literal marker $\mathrm{lit}(p)$ on top of $\bar u$ on top of $d$, and all other stacks as before.

The name goes from $A$ to $D$ through $B$, so it is reversed twice. -/
theorem put_run (p : Bool) (u : List Bool) :
    ∃ v', Run prog (2 * u.length + 3) ⟨some (.put p), v, st t o (u.map Sym.bit) d e c n⟩
      ⟨some .lits, v', st t o [] (.lit p :: (u.map Sym.bit ++ d)) e c n⟩ := by
  obtain ⟨v₁, S₁, r₁, h1A, h1B, h1k⟩ := moveB_run (M := prog) (self := .put p)
    (next := .put2 p) (a := .A) (b := .B) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) u
    (u.map Sym.bit) [] v (st t o (u.map Sym.bit) d e c n) (by simp) (isBitBlock_map u) rfl
  obtain ⟨v₂, S₂, r₂, h2B, h2D, h2k⟩ := moveB_run (M := prog) (self := .put2 p)
    (next := .put3 p) (a := .B) (b := .D) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    u.reverse (u.map Sym.bit).reverse [] v₁ S₁ (by simp [h1B]) (isBitBlock_rev u) rfl
  have hS : S₂ = st t o [] (u.map Sym.bit ++ d) e c n := by
    funext k; cases k <;> simp [h2B, h2D, h2k, h1A, h1k, List.map_reverse]
  have r₃ := put3_step v₂ t o [] (u.map Sym.bit ++ d) e c n p
  rw [← hS] at r₃
  exact ⟨v₂, ((r₁.trans r₂).trans r₃).of_eq (by simp; omega)⟩

/-- **Clique emitter: moving the walk side back.** Let $p$ and $v$ be Booleans, $t$, $a$ and $d$
stack-symbol lists, $o$ a list of bits, $c, n \in \mathbb{N}$, and let $L$ be a list of stack
symbols each of which is a name bit, a polarity marker or a clause marker. From label
$\mathrm{back}(p)$ with flag $v$ and the state with token stack $t$, output $o$, name stack $a$,
walked stack $d$, walk side $L$, clause count $c$, occurrence count $n$ and empty scratch stacks,
the emitter machine reaches in exactly $|L| + 1$ steps, for some flag $v'$, label
$\mathrm{put}(p)$ with flag $v'$ and the same state except that the walked stack is the reverse
of $L$ followed by $d$ and the walk side is empty. -/
theorem back_run (p : Bool) :
    ∀ (L : List Sym), (∀ s ∈ L, isTok s = true) → ∀ (d : List Sym) (v : Bool),
      ∃ v', Run prog (L.length + 1) ⟨some (.back p), v, st t o a d L c n⟩
        ⟨some (.put p), v', st t o a (L.reverse ++ d) [] c n⟩ := by
  intro L
  induction L with
  | nil => intro _ d v; exact ⟨true, by simpa using back_nil v t o a d c n p⟩
  | cons s L ih =>
      intro hL d v
      obtain ⟨v₁, r₁⟩ := back_step v t o a d c n p s (hL s (by simp)) L
      obtain ⟨v₂, r₂⟩ := ih (fun x hx => hL x (by simp [hx])) (s :: d) v₁
      exact ⟨v₂, by simpa [Nat.add_comm] using r₁.trans r₂⟩

/-- **Clique emitter: the instance prefix.** Let $v$ be a Boolean, $d$ and $e$ stack-symbol lists,
$o$ a list of bits and $c, n \in \mathbb{N}$. From label fin with flag $v$ and the state with
empty token stack, output $o$, empty name stack, walked stack $d$, walk side $e$, clause count
$c$, occurrence count $n$ and empty scratch stacks, the emitter machine reaches in exactly
$n + c + 4$ steps label done with some flag and some state whose output, read top-down, is $c$
ones, false, $n$ ones, false, then $o$. -/
theorem fin_run :
    ∃ v' S', Run prog (n + c + 4) ⟨some .fin, v, st [] o [] d e c n⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = List.replicate c true ++ false :: (List.replicate n true ++ false :: o) := by
  have r₁ : Run prog 1 ⟨some .fin, v, st [] o [] d e c n⟩
      ⟨some .finN, v, st [] (false :: o) [] d e c n⟩ :=
    Run.single (by simp [prog, TM2.stepAux])
  have r₂ := xferE_run (M := prog) (self := .finN) (next := .fin2) (k := .N) (o := .O)
    (ys := [true]) rfl (by decide) Sym.cl n v (st [] (false :: o) [] d e c n) rfl
  set S₂ := update (update (st [] (false :: o) [] d e c n) K.N []) K.O
    (rep [true] n ++ (st [] (false :: o) [] d e c n) K.O) with hS₂
  have r₃ : Run prog 1 ⟨some .fin2, Flag.tag false, S₂⟩
      ⟨some .finC, Flag.tag false, update S₂ .O (false :: S₂ .O)⟩ :=
    Run.single (by simp [prog, TM2.stepAux])
  have r₄ := xferE_run (M := prog) (self := .finC) (next := .done) (k := .C) (o := .O)
    (ys := [true]) rfl (by decide) Sym.cl c (Flag.tag false) (update S₂ .O (false :: S₂ .O))
    (by simp [hS₂])
  refine ⟨_, _, (((r₁.trans r₂).trans r₃).trans r₄).of_eq (by omega), ?_⟩
  simp [hS₂, Emit3.rep_single]

end Phases

/-! ### Lengths and shapes -/

/-- **Reversing a list preserves the length of a flat map.** Let $\alpha$ and $\beta$ be types,
$l$ a list of elements of $\alpha$ and $f$ a function from $\alpha$ to lists of elements of
$\beta$. Concatenating the lists $f(a)$ for $a$ running through the reverse of $l$ gives a list
of the same length as concatenating them for $a$ running through $l$. -/
theorem flatMap_reverse_length {α β : Type} (l : List α) (f : α → List β) :
    (l.reverse.flatMap f).length = (l.flatMap f).length := by
  simp [List.length_flatMap, List.map_reverse, List.sum_reverse]

theorem dTok_length (l : ℕ × Bool) : (dTok l).length = (Check.litRev l).length := by
  simp [dTok, Check.litRev]

theorem some_itemTok_length (Ls : List (ℕ × Bool)) (ds : List (Option (ℕ × Bool))) :
    ((Ls.map some ++ ds).flatMap itemTok).length =
      (Ls.flatMap Check.litRev).length + (ds.flatMap itemTok).length := by
  induction Ls with
  | nil => simp
  | cons l Ls ih =>
      simp only [List.map_cons, List.cons_append, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih, show itemTok (some l) = dTok l from rfl, dTok_length]
      omega

theorem items_length (φ : CNF) :
    ((items φ).flatMap itemTok).length = (φ.flatMap Check.clRev).length := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
      have e : items (C :: φ) = C.map some ++ none :: items φ := by simp [items]
      rw [e, some_itemTok_length, List.flatMap_cons, List.length_append]
      simp only [List.flatMap_cons, List.length_append, Emit3.clRev_length, ih]
      simp [itemTok]
      omega

theorem length_add_le (φ : CNF) : φ.length + φ.flatten.length ≤ (φ.flatMap Check.clRev).length := by
  induction φ with
  | nil => simp
  | cons C φ ih =>
      have := Check.litRev_flatMap_length_ge C
      simp only [List.length_cons, List.flatten_cons, List.flatMap_cons, List.length_append,
        Emit3.clRev_length]
      omega

theorem itemTok_head (i : Option (ℕ × Bool)) (rest : List Sym) :
    (itemTok i ++ rest).head?.bind Sym.bit? = none := by
  cases i <;> simp [itemTok, dTok, Sym.bit?]

theorem flatMap_itemTok_head (ds : List (Option (ℕ × Bool))) :
    (ds.flatMap itemTok).head?.bind Sym.bit? = none := by
  cases ds with
  | nil => rfl
  | cons i ds => rw [List.flatMap_cons]; exact itemTok_head i _

theorem isTok_flatMap_itemTok (ds : List (Option (ℕ × Bool))) :
    ∀ s ∈ ds.flatMap itemTok, isTok s = true := by
  intro s hs
  simp only [List.mem_flatMap] at hs
  obtain ⟨i, -, hi⟩ := hs
  cases i with
  | none => simp only [itemTok, List.mem_singleton] at hi; subst hi; rfl
  | some l =>
      simp only [itemTok, dTok, List.mem_cons, List.mem_map] at hi
      rcases hi with rfl | ⟨b, -, rfl⟩ <;> rfl

theorem adjL_eq (l l' : ℕ × Bool) :
    (if encodeNat l.1 = encodeNat l'.1 then l.2 == l'.2 else true) = adjL l l' := by
  obtain ⟨x, p⟩ := l
  obtain ⟨x', q⟩ := l'
  by_cases h : x = x'
  · cases p <;> cases q <;> simp [adjL, h]
  · simp [adjL, h, encodeNat_inj]

theorem runLe_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hk : k ≤ k') (hd : d = d') : RunLe prog k' c d' := hd ▸ h.mono hk

/-! ### The walk, occurrences, clauses, the formula -/

section Loops

/-- **Walk over the occurrence stack in the CLIQUE emitter.** Let $l = (x, p)$ be a literal
occurrence, $ds$ a list of items (literal occurrences or clause markers), $f$ and $v$ Booleans,
$t$ a token stack, $o$ an output stack of bits, $e$ a stack of token symbols and
$c, n \in \mathbb{N}$. Let $D$ be the concatenation of the tokens of the items of $ds$: a clause
marker for a clause marker, and the polarity marker of $l'$ above the name bits of $l'$ (the
binary encoding of its name as bit symbols) for an occurrence $l'$. Start the CLIQUE emitter at
label $\mathsf{walk}(p, f)$ with internal variable $v$, on the configuration stacks with token
stack $t$, output $o$, name stack the name bits of $x$, walked-occurrence stack $D$, other walk
stack $e$ and counts $c$ and $n$. Then for some Boolean $v'$ the machine reaches, in at most
$6\,|D| + 1$ steps, label $\mathsf{back}(p)$ with internal variable $v'$ on the configuration
stacks with token stack $t$, output stack the reverse of $\mathrm{walkBits}(l, f, ds)$ followed
by $o$, name stack the name bits of $x$, empty walked-occurrence stack, other walk stack the
reverse of $D$ followed by $e$, and counts $c$ and $n$. -/
theorem walk_run (l : ℕ × Bool) (t : List Sym) (c n : ℕ) :
    ∀ (ds : List (Option (ℕ × Bool))) (f : Bool) (o : List Bool) (e : List Sym) (v : Bool),
      ∃ v', RunLe prog (6 * (ds.flatMap itemTok).length + 1)
        ⟨some (.walk l.2 f), v, st t o (name l.1) (ds.flatMap itemTok) e c n⟩
        ⟨some (.back l.2), v', st t ((walkBits l f ds).reverse ++ o) (name l.1) []
          ((ds.flatMap itemTok).reverse ++ e) c n⟩ := by
  intro ds
  induction ds with
  | nil =>
      intro f o e v
      exact ⟨true, runLe_cast ((walk_nil v t o _ e c n l.2 f).le le_rfl) (by simp)
        (by simp [walkBits])⟩
  | cons i ds ih =>
      intro f o e v
      set R := ds.flatMap itemTok with hR
      have hRb : R.head?.bind Sym.bit? = none := flatMap_itemTok_head ds
      cases i with
      | none =>
          have e1 : (none :: ds).flatMap itemTok = .cl :: R := rfl
          rw [e1]
          have r₁ := walk_cl v t o (name l.1) e c n l.2 f R
          obtain ⟨v₂, r₂⟩ := ih true o (.cl :: e) true
          refine ⟨v₂, runLe_cast ((r₁.le le_rfl).trans r₂) (by simp; omega) ?_⟩
          simp [walkBits]
      | some l' =>
          have e1 : (some l' :: ds).flatMap itemTok = .lit l'.2 :: (name l'.1 ++ R) := by
            simp [hR, itemTok, dTok]
          rw [e1]
          cases f with
          | false =>
              have r₁ := walk_lit_false v t o (name l.1) e c n l.2 l'.2 (name l'.1 ++ R)
              obtain ⟨v₂, r₂⟩ := mvN_run (v := l'.2) (t := t) (o := false :: o) (a := name l.1)
                (e := .lit l'.2 :: e) (c := c) (n := n) l.2 false (encodeNat l'.1) R hRb
              obtain ⟨v₃, r₃⟩ := ih false (false :: o) ((name l'.1).reverse ++ .lit l'.2 :: e) v₂
              refine ⟨v₃, runLe_cast (((r₁.trans r₂).le le_rfl).trans r₃) (by simp; omega) ?_⟩
              simp [walkBits]
          | true =>
              have r₁ := walk_lit_true v t o (name l.1) e c n l.2 l'.2 (name l'.1 ++ R)
              obtain ⟨v₂, r₂⟩ := cmp_run (v := l'.2) (t := t) (o := o) (e := .lit l'.2 :: e)
                (c := c) (n := n) l.2 l'.2 (encodeNat l.1) (encodeNat l'.1) R hRb
              rw [adjL_eq] at r₂
              obtain ⟨v₃, r₃⟩ := mvN_run (v := v₂) (t := t) (o := adjL l l' :: o)
                (a := name l.1) (e := .lit l'.2 :: e) (c := c) (n := n) l.2 true (encodeNat l'.1)
                R hRb
              obtain ⟨v₄, r₄⟩ := ih true (adjL l l' :: o)
                ((name l'.1).reverse ++ .lit l'.2 :: e) v₃
              refine ⟨v₄, runLe_cast (((r₁.le le_rfl).trans r₂).trans ((r₃.le le_rfl).trans r₄))
                (by simp; omega) ?_⟩
              simp [walkBits]

/-- **Emitter run over one literal occurrence.** Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $l = (x, p)$ be a literal, $R$ a list of symbols that
is empty or does not start with a name-bit symbol, $I$ a list of items, $o$ a list of bits,
$c, n \in \mathbb{N}$ and $v$ a bit. Let $\delta$ be the concatenation of the tokens of the items
of $I$, $\lambda$ the token list of $l$ as it lies on the token stack, $\rho$ the reverse of the
walk bits of $l$ with flag false over $I$, and $\delta'$ the concatenation of the tokens of the
item $l$ followed by those of $I$. Then for some bit $v'$ the machine goes in at most
$7|\delta| + 3|\mathrm{enc}(x)| + 7$ steps, where $\mathrm{enc}(x)$ is the binary encoding of $x$,
from $\langle \mathsf{lits}, v \mid \lambda R, o, [], \delta, [], c, n\rangle$ to
$\langle \mathsf{lits}, v' \mid R, \rho\, o, [], \delta', [], c, n + 1\rangle$. -/
theorem lit_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (ds : List (Option (ℕ × Bool))) (o : List Bool) (c n : ℕ) (v : Bool) :
    ∃ v', RunLe prog (7 * (ds.flatMap itemTok).length + 3 * (encodeNat l.1).length + 7)
      ⟨some .lits, v, st (Check.litRev l ++ R) o [] (ds.flatMap itemTok) [] c n⟩
      ⟨some .lits, v', st R ((walkBits l false ds).reverse ++ o) []
        ((some l :: ds).flatMap itemTok) [] c (n + 1)⟩ := by
  have hT : Check.litRev l ++ R = .lit l.2 :: ((name l.1).reverse ++ R) := by
    simp [Check.litRev]
  rw [hT]
  set D := ds.flatMap itemTok with hD
  have r₁ := lits_lit (v := v) (o := o) (a := []) (d := D) (e := []) (c := c) (n := n) l.2
    ((name l.1).reverse ++ R)
  obtain ⟨v₂, r₂⟩ := nm_run (v := l.2) (o := o) (d := D) (e := []) (c := c) (n := n + 1) l.2 l.1
    R hR
  obtain ⟨v₃, r₃⟩ := walk_run l R c (n + 1) ds false o [] v₂
  set O' := (walkBits l false ds).reverse ++ o with hO'
  obtain ⟨v₄, r₄⟩ := back_run (t := R) (o := O') (a := name l.1) (c := c) (n := n + 1) l.2
    (D.reverse ++ []) (fun s hs => isTok_flatMap_itemTok ds s (by
      rw [List.append_nil, List.mem_reverse] at hs; exact hs)) [] v₃
  obtain ⟨v₅, r₅⟩ := put_run (v := v₄) (t := R) (o := O') (d := D) (e := []) (c := c)
    (n := n + 1) l.2 (encodeNat l.1)
  have r₄' : Run prog (D.length + 1) ⟨some (.back l.2), v₃, st R O' (name l.1) [] (D.reverse ++ [])
      c (n + 1)⟩ ⟨some (.put l.2), v₄, st R O' (name l.1) D [] c (n + 1)⟩ := by
    simpa using r₄
  refine ⟨v₅, runLe_cast ((((r₁.trans r₂).le le_rfl).trans r₃).trans
    ((r₄'.trans r₅).le le_rfl)) (by simp only [hD]; omega) ?_⟩
  simp [hD, itemTok, dTok]

/-- **Emitter run over a clause's literals.** Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $L, c \in \mathbb{N}$, let $I$ be a list of items
and $\delta$ the concatenation of their tokens, let $l_1, \dots, l_k$ be literals, $R$ a list of
symbols that is empty or does not start with a name-bit symbol, $o$ a list of bits,
$n \in \mathbb{N}$ and $v$ a bit. Let $\lambda_i$ be the token list of $l_i$ as it lies on the
token stack and $\Lambda = |\lambda_1| + \dots + |\lambda_k|$. If $\Lambda + |\delta| \le L$, then
for some bit $v'$ the machine goes in at most $\Lambda (7L + 7)$ steps from
$\langle \mathsf{lits}, v \mid \lambda_k \cdots \lambda_1 R, o, [], \delta, [], c, n\rangle$ to
$\langle \mathsf{lits}, v' \mid R, \rho\, o, [], \delta', [], c, n + k\rangle$, where $\rho$ is the
rows pushed for the literals $l_1, \dots, l_k$ above the items $I$ and $\delta'$ is the
concatenation of the tokens of the items $l_1, \dots, l_k$ followed by those of $I$. -/
theorem lits_run (Lb : ℕ) (ds : List (Option (ℕ × Bool))) (c : ℕ) :
    ∀ (Ls : List (ℕ × Bool)) (R : List Sym), R.head?.bind Sym.bit? = none →
      ∀ (o : List Bool) (n : ℕ) (v : Bool),
      (Ls.flatMap Check.litRev).length + (ds.flatMap itemTok).length ≤ Lb →
      ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length * (7 * Lb + 7))
        ⟨some .lits, v, st (Ls.reverse.flatMap Check.litRev ++ R) o [] (ds.flatMap itemTok) []
          c n⟩
        ⟨some .lits, v', st R (lrows ds Ls ++ o) [] ((Ls.map some ++ ds).flatMap itemTok) []
          c (n + Ls.length)⟩ := by
  intro Ls
  induction Ls with
  | nil =>
      intro R _ o n v _
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [lrows])⟩
  | cons l Ls ih =>
      intro R hR o n v hb
      have hl : (Check.litRev l).length = (encodeNat l.1).length + 1 := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb
      obtain ⟨v₁, r₁⟩ := ih (Check.litRev l ++ R) (by simp [Check.litRev, Sym.bit?]) o n v
        (by omega)
      obtain ⟨v₂, r₂⟩ := lit_run l R hR (Ls.map some ++ ds) (lrows ds Ls ++ o) c (n + Ls.length)
        v₁
      have e : (l :: Ls).reverse.flatMap Check.litRev ++ R =
          Ls.reverse.flatMap Check.litRev ++ (Check.litRev l ++ R) := by simp
      rw [e]
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · rw [some_itemTok_length, List.flatMap_cons, List.length_append, hl]
        have h7 : 7 * ((Ls.flatMap Check.litRev).length + (ds.flatMap itemTok).length) ≤ 7 * Lb :=
          by omega
        nlinarith
      · simp [lrows, Nat.add_assoc]

/-- **Clique emitter: one clause.** Let $C$ be a clause, $\varphi$ a CNF formula, $R$ a token list
that is empty or starts with a clause marker, $o$ a list of bits, $c, n, B \in \mathbb{N}$ and $v$
a Boolean. Write $T_C$ for the tokens of $C$ as they lie on the token stack (a clause marker,
then the literals last-first) and $D_\psi$ for the tokens of the items of a formula $\psi$. If
$|T_C| + |D_\varphi| \le B$, then for some flag $v'$ the emitter machine goes in at most
$|T_C| \cdot (7B + 7)$ steps from label start with flag $v$ and the state with token stack $T_C$
followed by $R$, output $o$, walked stack $D_\varphi$, clause count $c$, occurrence count $n$ and
all other stacks empty, to label start with flag $v'$ and the state with token stack $R$, output
the rows pushed for the literals of $C$ walked above a clause marker and the items of $\varphi$,
followed by $o$, walked stack $D_{C \varphi}$ for the formula $C\varphi$ with first clause $C$,
clause count $c + 1$, occurrence count $n + |C|$ and all other stacks empty. -/
theorem clause_run (Lb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (φ : CNF) (o : List Bool) (c n : ℕ) (v : Bool)
    (hb : (Check.clRev C).length + ((items φ).flatMap itemTok).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * (7 * Lb + 7))
      ⟨some .start, v, st (Check.clRev C ++ R) o [] ((items φ).flatMap itemTok) [] c n⟩
      ⟨some .start, v', st R (lrows (none :: items φ) C ++ o) []
        ((items (C :: φ)).flatMap itemTok) [] (c + 1) (n + C.length)⟩ := by
  have hRl : Emit3.isLit R.head? = false := by rcases hR with rfl | h <;> simp [Emit3.isLit, *]
  have hRb : R.head?.bind Sym.bit? = none := by rcases hR with rfl | h <;> simp [Sym.bit?, *]
  have r₁ := start_cl v o [] ((items φ).flatMap itemTok) [] c n
    (C.reverse.flatMap Check.litRev ++ R)
  rw [Emit3.clRev_length] at hb
  obtain ⟨v₂, r₂⟩ := lits_run Lb (none :: items φ) (c + 1) C R hRb o n false (by
    simp only [List.flatMap_cons, List.length_append, show (itemTok none).length = 1 from rfl]
    omega)
  have r₃ := lits_end v₂ R (lrows (none :: items φ) C ++ o) []
    ((C.map some ++ none :: items φ).flatMap itemTok) [] (c + 1) (n + C.length) hRl
  have e : Check.clRev C ++ R = .cl :: (C.reverse.flatMap Check.litRev ++ R) := by
    simp [Check.clRev]
  rw [e]
  refine ⟨false, runLe_cast (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)) ?_ ?_⟩
  · rw [Emit3.clRev_length]; nlinarith
  · simp [items]

/-- **Emitter run over a formula's clauses.** Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $L \in \mathbb{N}$, let $\varphi$ be a CNF formula
with clauses $C_1, \dots, C_m$ in order, let $R$ be a list of symbols that is empty or starts
with the clause marker, $o$ a list of bits and $v$ a bit. Let $\kappa_i$ be the token list of
$C_i$ as it lies on the token stack and $\tau = \kappa_m \cdots \kappa_1$. If $|\tau| \le L$,
then for some bit $v'$ the machine goes in at most $|\tau| (7L + 7)$ steps from
$\langle \mathsf{start}, v \mid \tau R, o, [], [], [], 0, 0\rangle$ to
$\langle \mathsf{start}, v' \mid R, \rho\, o, [], \delta, [], m, s\rangle$, where $\rho$ is the
row bits of $\varphi$, $\delta$ is the concatenation of the tokens of the items of $\varphi$ and
$s = |C_1| + \dots + |C_m|$ is the total number of literals of $\varphi$. -/
theorem formula_run (Lb : ℕ) :
    ∀ (φ : CNF) (R : List Sym), (R = [] ∨ R.head? = some .cl) → ∀ (o : List Bool) (v : Bool),
      (φ.reverse.flatMap Check.clRev).length ≤ Lb →
      ∃ v', RunLe prog ((φ.reverse.flatMap Check.clRev).length * (7 * Lb + 7))
        ⟨some .start, v, st (φ.reverse.flatMap Check.clRev ++ R) o [] [] [] 0 0⟩
        ⟨some .start, v', st R (rowsF φ ++ o) [] ((items φ).flatMap itemTok) [] φ.length
          φ.flatten.length⟩ := by
  intro φ
  induction φ with
  | nil =>
      intro R _ o v _
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [rowsF, items])⟩
  | cons C φ ih =>
      intro R hR o v hb
      have hl : ((C :: φ).reverse.flatMap Check.clRev).length =
          (φ.reverse.flatMap Check.clRev).length + (Check.clRev C).length := by simp
      obtain ⟨v₁, r₁⟩ := ih (Check.clRev C ++ R) (Or.inr rfl) o v (by omega)
      obtain ⟨v₂, r₂⟩ := clause_run Lb C R hR φ (rowsF φ ++ o) φ.length φ.flatten.length v₁ (by
        rw [items_length, ← flatMap_reverse_length]; omega)
      have e : (C :: φ).reverse.flatMap Check.clRev ++ R =
          φ.reverse.flatMap Check.clRev ++ (Check.clRev C ++ R) := by simp
      rw [e]
      refine ⟨v₂, runLe_cast (r₁.trans r₂) (by rw [hl]; nlinarith) ?_⟩
      simp [rowsF, Nat.add_comm]

end Loops

/-! ### The emitter -/

/-- **The CLIQUE emitter computes Karp's instance in cubic time.** Let $\varphi$ be a CNF formula
with token list $\tau$ (in reading order), $o$ a list of Booleans, $v$ a flag, and $S$ stack
contents in which the token stack $T$ holds $\tau$ reversed (stacks are listed top first), the
output stack $O$ holds $o$ and every other stack is empty. Started at its start label with flag
$v$ and stacks $S$, the CLIQUE emitter reaches the label $\mathrm{done}$ in at most
$8(|\tau| + 1)^3$ steps, with some flag and stacks $S'$ such that $O$ holds, in $S'$, Karp's
CLIQUE instance of $\varphi$ followed by $o$. -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (8 * ((toks φ).length + 1) ^ 3) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = toClique φ ++ o := by
  have hSt : St = st ((toks φ).reverse) o [] [] [] 0 0 := by
    funext k
    cases k
    · exact hT
    · exact hO
    all_goals exact h0 _ (by decide) (by decide)
  set L := (toks φ).length with hL
  have hL' : (φ.reverse.flatMap Check.clRev).length = L := by
    rw [hL, ← Check.toks_reverse, List.length_reverse]
  obtain ⟨v₁, r₁⟩ := formula_run L φ [] (Or.inl rfl) o v hL'.le
  rw [hL', List.append_nil, ← Check.toks_reverse] at r₁
  have r₂ := start_nil v₁ (rowsF φ ++ o) [] ((items φ).flatMap itemTok) [] φ.length
    φ.flatten.length
  obtain ⟨v₃, S₃, r₃, hS₃⟩ := fin_run true (rowsF φ ++ o) ((items φ).flatMap itemTok) []
    φ.length φ.flatten.length
  have hlen := length_add_le φ
  rw [← flatMap_reverse_length, hL'] at hlen
  refine ⟨v₃, S₃, ?_, ?_⟩
  · rw [hSt]
    refine (r₁.trans ((r₂.trans r₃).le le_rfl)).mono ?_
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 2)]
  · have hn : (occs φ).length = φ.flatten.length := by
      rw [← occs_snd, List.length_map]
    rw [hS₃, toClique, encodeKG, hn, ← rowsF_eq]
    simp

end Cslib.Complexity.Karp.EmitClique
