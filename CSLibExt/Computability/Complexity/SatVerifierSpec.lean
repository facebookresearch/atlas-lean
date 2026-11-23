/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.SatTimeM

/-!
# The SAT verifier as `TM2` components: stack formats and specs

`Cslib.CookLevin.satVerifier` decodes the formula `x` (rejecting on failure) and checks every
clause against the witness `w`, read as values of the literal occurrences in order, first
occurrence winning. Its `TM2` machine has three components; this module fixes the stack formats
they share and the pure function each computes, and composes them (`satVerifier_ret_eq`).

* Symbols `Sym`: name bits, polarity markers `lit p`, clause ends `cl`, table markers `val b` and
  `dead`. Names are canonical `encodeNat` strings, so equal names are equal indices.
* Token stack `(toks φ).reverse` (head = top): per literal its name bits then `lit p`, per
  clause a final `cl`, pushed in reading order (names lie reversed under their marker).
* Table stack `tblStk (ents φ w)`: per occurrence its name bits then `val w[i]` (`dead` once `w`
  has run out), pushed alongside the token stack (first occurrence at the bottom).

Components: (1) tokenizer, `tokenize` (the canonical-name check is
`encodeNat_decodeNat_eq_iff`); (2) lookup: from a reversed name block `(q.map .bit).reverse` and
`tblStk es`, compute `liveVal es q` (the last live match scanning from the top) and restore
both stacks; (3) clause check: walk the token stack, looking literals up, giving `checkSpec`.
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier

open Cslib.CookLevin Cslib.Logic.PL Computability

/-- **Stack alphabet of the SAT verifier.** The symbols of the token and table stacks are a name
bit $b$ for each boolean $b$, a polarity marker for each polarity $p$, a clause end marker, a
value marker for each boolean $b$, and a dead marker. Equality of symbols is decidable. -/
inductive Sym
  | bit (b : Bool) | lit (p : Bool) | cl | val (b : Bool) | dead
  deriving DecidableEq

/-- **Reading a symbol as a name bit.** A symbol of the token and table stacks that is the name
bit $b$ reads as the bit $b$; every other symbol reads as no bit, and so ends a name block. -/
def Sym.bit? : Sym → Option Bool
  | .bit b => some b
  | _ => none

/-- **Tokens of a literal.** For a literal $(n, p)$ with variable index $n$ and polarity $p$,
the token list is one bit symbol for each bit of the canonical binary representation of $n$
(least significant bit first, empty for $n = 0$), in order, followed by the polarity marker
symbol for $p$. -/
def litToks (l : ℕ × Bool) : List Sym := (encodeNat l.1).map .bit ++ [.lit l.2]

/-- **Tokens of a clause.** The tokens of a CNF clause are the tokens of its literals, in order,
followed by the clause-end symbol. -/
def clauseToks (C : CNFClause) : List Sym := C.flatMap litToks ++ [.cl]

/-- **Token sequence of a CNF formula.** For a CNF formula $\varphi$ with clauses
$C_1, \dots, C_k$ (in order), the token sequence of $\varphi$ is the concatenation of the token
sequences of $C_1, \dots, C_k$. The token sequence of a clause is the concatenation of the token
sequences of its literals, in order, followed by a clause-end symbol; the token sequence of a
literal with variable index $n \in \mathbb{N}$ and polarity $p$ is the bits of the binary
encoding of $n$ (Mathlib's `encodeNat`), each as a name-bit symbol, followed by a polarity
marker for $p$.

The verifier's token stack holds this sequence in reverse order. -/
def toks (φ : CNF) : List Sym := φ.flatMap clauseToks

/-- **Table entries.** A table entry is a pair of a name, which is a list of bits, and an optional
bit, its value; the value is absent for occurrences past the end of the witness. -/
abbrev Ent := List Bool × Option Bool

/-- **Closing marker of a table entry.** The marker closing a table entry whose value is the
boolean $b$ is the value symbol for $b$; for an entry with no value it is the dead symbol. -/
def markOf : Option Bool → Sym
  | some b => .val b
  | none => .dead

/-- **Symbols of a table entry.** The symbols of a table entry with name $q$ and value $v$ are the
bits of $q$ as name-bit symbols, in order, followed by one closing marker: the value marker of $b$
if $v$ is a bit $b$, and the dead marker if $v$ is absent. -/
def entToks (e : Ent) : List Sym := e.1.map .bit ++ [markOf e.2]

/-- **Table stack of an entry list.** Write each table entry as one bit symbol per bit of its
name followed by its closing marker (the value symbol for its value, or the dead symbol if it
has no value), and concatenate these in the order of the list. The table stack is the reverse
of this sequence, with the head as the top of the stack, so the first entry lies at the bottom.
-/
def tblStk (es : List Ent) : List Sym := (es.flatMap entToks).reverse

/-- **Occurrence table of a list of variables.** Given natural numbers $n_0, \dots, n_{k-1}$ and a
list $w$ of bits, the occurrence table is the list of $k$ table entries whose $i$-th entry has as
name the binary code of $n_i$ (Mathlib's encoding of natural numbers as bit lists) and as value
the bit $w_i$ if $i$ is less than the length of $w$, and no value otherwise. -/
def entsOf : List ℕ → List Bool → List Ent
  | [], _ => []
  | n :: ns, [] => (encodeNat n, none) :: entsOf ns []
  | n :: ns, b :: bs => (encodeNat n, some b) :: entsOf ns bs

/-- **Occurrence table of a formula and a witness.** Let $\varphi$ be a CNF formula, $w$ a list
of booleans, and $n_0, \dots, n_{k-1}$ the variable indices of the literals of $\varphi$ in
reading order, with repetitions. The occurrence table is the list of $k$ entries whose $i$-th
entry pairs the binary name of $n_i$ (its canonical binary representation, least significant
bit first, empty for $0$) with the value $w_i$ if $i$ is less than the length of $w$, and with
no value otherwise. -/
def ents (φ : CNF) (w : List Bool) : List Ent := entsOf (varsOf φ) w

/-- **Live value of a name in a table.** Given a list of table entries, each pairing a name (a
bit string) with either a boolean value or no value, and a bit string $q$, the live value of
$q$ is the value of the first entry whose name is $q$ and which carries a value, or false if
there is no such entry. -/
def liveVal (es : List Ent) (q : List Bool) : Bool :=
  (es.findSome? fun e => if e.1 = q then e.2 else none).getD false

/-- **Clause check against an occurrence table.** For a CNF formula $\varphi$ and a list $es$ of
table entries, the clause check is true exactly when every clause of $\varphi$ contains a literal
$(x, p)$ whose live value equals its polarity $p$. Here the live value of $x$ is the value of the
first entry of $es$ that is named by the binary code of $x$ and has a value, and false if there
is no such entry. -/
def checkSpec (φ : CNF) (es : List Ent) : Bool :=
  φ.all fun C => C.any fun l => liveVal es (encodeNat l.1) == l.2

/-- **Tokenizer of the SAT verifier.** Given bit strings $x$ and $w$, the tokenizer rejects
(returns no result) if $x$ does not decode to a CNF formula. If $x$ decodes to a formula
$\varphi$, it returns the pair consisting of the token stack, the reverse of the tokens of
$\varphi$ in reading order, and the table stack of the occurrence table of $\varphi$ and $w$. -/
def tokenize (x w : List Bool) : Option (List Sym × List Sym) :=
  (decodeCNF x).map fun φ => ((toks φ).reverse, tblStk (ents φ w))

/-- **The binary code of natural numbers is injective.** For natural numbers $m$ and $n$, the
binary codes of $m$ and $n$ (Mathlib's encoding of natural numbers as bit lists) are equal if and
only if $m = n$. -/
theorem encodeNat_inj {m n : ℕ} : encodeNat m = encodeNat n ↔ m = n :=
  ⟨fun h => by rw [← decode_encodeNat m, h, decode_encodeNat], congrArg _⟩

theorem encodePosNum_decodePosNum_eq_iff (l : List Bool) :
    encodePosNum (decodePosNum l) = l ↔ l.getLast? = some true := by
  induction l with
  | nil => simp [decodePosNum, encodePosNum]
  | cons b l ih =>
      cases l with
      | nil => cases b <;> simp [decodePosNum, encodePosNum]
      | cons c l =>
          cases b <;> simpa [decodePosNum, encodePosNum, List.getLast?_cons_cons] using ih

/-- **Canonical binary names.** For every list $l$ of bits, encoding the natural number that $l$
decodes to (Mathlib's binary code of natural numbers, least significant bit first) gives back $l$
if and only if $l$ is empty or its last bit is true. -/
theorem encodeNat_decodeNat_eq_iff (l : List Bool) :
    encodeNat (decodeNat l) = l ↔ l = [] ∨ l.getLast? = some true := by
  have h : encodeNat (decodeNat l) = encodeNum (decodeNum l) := by
    simp only [encodeNat, decodeNat, Num.of_to_nat]
  rw [h]
  by_cases hl : l = []
  · subst hl; simp [decodeNum, encodeNum]
  · simp only [decodeNum, hl, ite_false, false_or]
    rw [PosNum.cast_to_num]
    exact encodePosNum_decodePosNum_eq_iff l

theorem liveVal_entsOf_nil (ns : List ℕ) (q : List Bool) : liveVal (entsOf ns []) q = false := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simpa [liveVal, entsOf, List.findSome?_cons] using ih

/-- **Table lookup agrees with the verifier's variable lookup.** Let $n = (n_0, \dots, n_{k-1})$
be a list of natural numbers, $w$ a list of booleans and $x$ a natural number. Write $[m]$ for
the binary name of a natural number $m$: its canonical binary representation, least significant
bit first, empty for $m = 0$. Form the table whose $i$-th entry, for $i < k$, pairs $[n_i]$
with $w_i$ if $i$ is less than the length of $w$, and with no value otherwise. Then the live
value of $[x]$ in this table (the value of the first entry named $[x]$ that carries a value, or
false if there is none) equals the return value of the verifier's lookup of $x$ in the lists
$n$ and $w$: the value $w_i$ for the first $i$ below both $k$ and the length of $w$ with
$n_i = x$, or false if there is none. -/
theorem liveVal_entsOf (ns : List ℕ) (w : List Bool) (x : ℕ) :
    liveVal (entsOf ns w) (encodeNat x) = (lookupVar ns w x).ret := by
  induction ns generalizing w with
  | nil => simp [entsOf, liveVal, lookupVar]
  | cons n ns ih =>
      cases w with
      | nil =>
          rw [liveVal_entsOf_nil]
          simp [lookupVar]
      | cons b bs =>
          by_cases h : x = n
          · subst h; simp [entsOf, liveVal, lookupVar]
          · have h' : ¬ encodeNat n = encodeNat x := fun e => h (encodeNat_inj.1 e).symm
            simpa [entsOf, liveVal, lookupVar, h, h'] using ih bs

/-- **The clause check on the occurrence table is the formula check.** For every CNF formula
$\varphi$ and every list $w$ of bits, the clause check of $\varphi$ against the occurrence table
of $\varphi$ and $w$ equals the value returned (ignoring the time count) by the formula check of
$\varphi$ against $w$ that uses the variable occurrences of $\varphi$, in order, as its variable
list. -/
theorem checkSpec_ents (φ : CNF) (w : List Bool) :
    checkSpec φ (ents φ w) = (checkCNF (varsOf φ) w φ).ret := by
  rw [Bool.eq_iff_iff, checkCNF_ret, CNF.satisfies_def]
  simp [checkSpec, ents, liveVal_entsOf]

/-- **The SAT verifier's answer through the occurrence table.** For all lists $x$ and $w$ of bits,
the value returned by the SAT verifier on $(x, w)$, ignoring the time count, is false if the
complete length-prefixed CNF decoder fails on $x$, and is the clause check of $\varphi$ against
the occurrence table of $\varphi$ and $w$ if $x$ decodes to the CNF formula $\varphi$. -/
theorem satVerifier_ret_eq (x w : List Bool) :
    (satVerifier (x, w)).ret = ((decodeCNF x).map fun φ => checkSpec φ (ents φ w)).getD false := by
  cases h : decodeCNF x with
  | none => simp [satVerifier_none h]
  | some φ => simp [satVerifier_some h, checkSpec_ents]

/-- `Sym` is finite. -/
instance Sym.instFintype : Fintype Sym where
  elems := ⟨↑[Sym.bit false, .bit true, .lit false, .lit true, .cl, .val false, .val true, .dead],
    by decide⟩
  complete := fun x => by rcases x with b | b | _ | b | _ <;> (try cases b) <;> decide

/-- **A clause has at most as many tokens as code bits.** For every CNF clause $C$, the number
of tokens of $C$ is at most the length of the binary code of $C$. -/
theorem clauseToks_length_le (C : CNFClause) :
    (clauseToks C).length ≤ (encodeClause C).length := by
  simp only [clauseToks, encodeClause, List.length_append, List.length_flatMap, List.length_cons,
    List.length_replicate, List.length_nil, litToks, encodeLit, encodeNatPrefix,
    MetaMathlibExt.BitstringEncoding.length_delimit, List.length_map]
  induction C with
  | nil => simp
  | cons l C ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

/-- **Token count is bounded by the encoding length.** For every CNF formula $\varphi$, the
number of tokens of $\varphi$ is at most the length of the binary encoding of $\varphi$. -/
theorem toks_length_le (φ : CNF) : (toks φ).length ≤ (encodeCNF φ).length := by
  simp only [toks, encodeCNF, List.length_append, List.length_cons, List.length_replicate,
    List.length_flatMap]
  induction φ with
  | nil => simp
  | cons C φ ih =>
      have := clauseToks_length_le C
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

end Cslib.Complexity.SatVerifier
