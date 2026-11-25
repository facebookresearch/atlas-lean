/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CooperEmitSpec
public import CSLibExt.Computability.Complexity.Karp.TokThen
public import CSLibExt.Computability.Complexity.SatLookup

@[expose] public section

/-!
# Cooper's network, written by a TM2 machine from the SAT token stack

A `TM2` machine that walks the token stack `(toks φ).reverse` and pushes the code of Cooper's
network `encodeRatNet (cooperNet φ)` onto the output stack `O`, so that `O` reads it top first
(`run`), within `500 (|toks φ| + 1)⁴` steps. The machine follows the block emission of
`Cslib.Complexity.Karp.EmitCooper` (`eInit`, `eOpen`, `eLit`, `eClose`, `eClause`, `eFormula`)
block for block; `emitCooper` packages it as an emitter, and `isPolyTime_reduceBN` states that
Cooper's reduction map is polynomial-time.

* Counters are unary stacks of clause tokens: `N` the node counter, `A` the AND-chain output,
  `H` the chain output of the open clause, `V` the root of the current literal.
* The dictionary of roots lies on `D`, latest entry on top, each entry a marker above its name
  bits (least significant bit first) above its root in unary (`dEnt`). A literal's name is moved
  from `T` to `M`; the walk over `D` compares it with each entry's name, takes the root of the
  first match onto `V` and moves every entry to `E`, which is moved back afterwards.
* A gate node's code is pushed from the bottom up: a constant block, the second parent's counter
  in ones, the first parent's counter in ones above a `false`, then the parent count `unary 2`
  (copy sites, `site_run`).
* A spec state is a quiescent machine state through `enc`; the bounds a literal's step count
  needs at every literal boundary come from the finished formula `eClose Q = eFormula (Ls :: ψ)`
  (`preClose_eq`).
-/

namespace Cslib.Complexity.Karp.EmitCooper


open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.LegacyPL
  Computability Cslib.Complexity.SatVerifier Cslib.Complexity.Cooper


/-! ### Glue to the emission -/

/-- **Adding a clause in front.** The block emission of `C :: φ` adds the clause `C` to the block
emission of `φ`: the block emission adds the clauses from the last one. -/
theorem eFormula_cons (C : CNFClause) (φ : CNF) :
    eFormula (C :: φ) = eClause C (eFormula φ) := by
  simp only [eFormula, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]


/-- **The code of Cooper's network from the block emission**: the node count in unary, then the
codes of the nodes, newest first. -/
theorem encodeRatNet_cooperNet_eq (φ : CNF) :
    encodeRatNet (cooperNet φ) = unary (eFormula φ).n ++ (eFormula φ).out := by
  rw [eFormula_eq]
  rfl


/-- **Between clauses the chain output is `0`.** -/
theorem eFormula_o (ψ : CNF) : (eFormula ψ).o = 0 := by
  rw [eFormula_eq]
  rfl


/-- **Opening a clause** advances the node counter. -/
theorem eOpen_n (s : ESt) : (eOpen s).n = s.n + 1 := by
  rfl


/-- **Opening a clause** makes its constant-false node the chain output. -/
theorem eOpen_o (s : ESt) : (eOpen s).o = s.n := by
  rfl


/-- **Opening a clause** keeps the AND-chain output. -/
theorem eOpen_acc (s : ESt) : (eOpen s).acc = s.acc := by
  rfl


/-- **Opening a clause** keeps the dictionary. -/
theorem eOpen_dict (s : ESt) : (eOpen s).dict = s.dict := by
  rfl


/-- **Closing a clause** advances the node counter. -/
theorem eClose_n (s : ESt) : (eClose s).n = s.n + 1 := by
  rfl


/-- **Closing a clause** makes its AND node the AND-chain output. -/
theorem eClose_acc (s : ESt) : (eClose s).acc = s.n := by
  rfl


/-- **Closing a clause** resets the chain output to `0`. -/
theorem eClose_o (s : ESt) : (eClose s).o = 0 := by
  rfl


/-- **Closing a clause** keeps the dictionary. -/
theorem eClose_dict (s : ESt) : (eClose s).dict = s.dict := by
  rfl


/-- **A literal's nodes.** Adding a literal writes one node, its OR node, when its name is in the
dictionary, and two, a root node and the OR node, when it is not. -/
theorem eLit_n (p : Bool) (nm : List Bool) (s : ESt) :
    (eLit p nm s).n = s.n + (if (s.dict.lookup nm).isSome then 1 else 2) := by
  cases h : s.dict.lookup nm
  · simp [eLit, eRoot, ESt.push, h]
  · simp [eLit, eRoot, ESt.push, h]


/-- **A literal's chain output** is its OR node, the last node written. -/
theorem eLit_o (p : Bool) (nm : List Bool) (s : ESt) : (eLit p nm s).o + 1 = (eLit p nm s).n := by
  cases h : s.dict.lookup nm
  · simp [eLit, eRoot, ESt.push, h]
  · simp [eLit, eRoot, ESt.push, h]


/-- **A literal's dictionary.** A new name is recorded under the root written for it. -/
theorem eLit_dict (p : Bool) (nm : List Bool) (s : ESt) :
    (eLit p nm s).dict = if (s.dict.lookup nm).isSome then s.dict else (nm, s.n) :: s.dict := by
  cases h : s.dict.lookup nm
  · simp [eLit, eRoot, ESt.push, h]
  · simp [eLit, eRoot, ESt.push, h]


/-- **A literal** keeps the AND-chain output. -/
theorem eLit_acc (p : Bool) (nm : List Bool) (s : ESt) : (eLit p nm s).acc = s.acc := by
  cases h : s.dict.lookup nm
  · simp [eLit, eRoot, ESt.push, h]
  · simp [eLit, eRoot, ESt.push, h]


/-- **A literal whose name is recorded under the root `r`**: its OR node joins the chain output
and `r`. -/
theorem eLit_some (p : Bool) (nm : List Bool) (s : ESt) (r : ℕ) (h : s.dict.lookup nm = some r) :
    eLit p nm s = ⟨encodeRatNode (orNode s.o r p) ++ s.out, s.n + 1, s.acc, s.n, s.dict⟩ := by
  simp [eLit, eRoot, ESt.push, h]


/-- **A literal with a new name**: a root node `s.n` is written and recorded under the name, then
the OR node joining the chain output and that root. -/
theorem eLit_none (p : Bool) (nm : List Bool) (s : ESt) (h : s.dict.lookup nm = none) :
    eLit p nm s = ⟨encodeRatNode (orNode s.o s.n p) ++ (encodeRatNode rootNode ++ s.out), s.n + 2,
      s.acc, s.n + 1, (nm, s.n) :: s.dict⟩ := by
  simp [eLit, eRoot, ESt.push, h]


/-- **Literals keep the AND-chain output.** -/
theorem foldl_eLit_acc (ls : List (ℕ × Bool)) (s : ESt) :
    (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).acc = s.acc := by
  induction ls generalizing s with
  | nil => simp
  | cons hd tl ih => simp only [List.foldl_cons, ih, eLit_acc]


/-- **Literals do not lower the node counter.** -/
theorem foldl_eLit_n_ge (ls : List (ℕ × Bool)) (s : ESt) :
    s.n ≤ (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).n := by
  induction ls generalizing s with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      have h1 : s.n ≤ (eLit hd.2 (encodeNat hd.1) s).n := by
        rw [eLit_n]
        exact Nat.le_add_right _ _
      exact le_trans h1 (ih _)


/-- **After literals the chain output is the last node**, if it was before them. -/
theorem foldl_eLit_o (ls : List (ℕ × Bool)) (s : ESt) (hs : s.o + 1 = s.n) :
    (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).o + 1 =
      (ls.foldl (fun s l => eLit l.2 (encodeNat l.1) s) s).n := by
  induction ls generalizing s with
  | nil => simp only [List.foldl_nil]; exact hs
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      apply ih
      exact eLit_o hd.2 (encodeNat hd.1) s


/-- **Layout of an OR node's code**: the parents are the chain output `o` and the root `v`. -/
theorem encodeRatNode_orNode (o v : ℕ) (p : Bool) : encodeRatNode (orNode o v p) =
    unary 2 ++ unary o ++ unary v ++ unary 4 ++ gateRows (fun a c => a || c == p) := by
  exact encodeRatNode_gateNode _ _ _


/-- **Layout of an AND node's code**: the parents are the AND-chain output `i` and the clause's
chain output `j`. -/
theorem encodeRatNode_andNode (i j : ℕ) : encodeRatNode (andNode i j) =
    unary 2 ++ unary i ++ unary j ++ unary 4 ++ gateRows (fun a c => a && c) := by
  exact encodeRatNode_gateNode _ _ _


/-- **The code of a root node**, nine bits. -/
theorem encodeRatNode_rootNode :
    encodeRatNode rootNode = [false, true, false, false, true, false, true, true, false] := by
  rfl


/-- **The code of the constant-true node**, eight bits. -/
theorem encodeRatNode_constNode_true :
    encodeRatNode (constNode true) = [false, true, false, false, true, false, true, false] := by
  rfl


/-- **The code of the constant-false node**, seven bits. -/
theorem encodeRatNode_constNode_false :
    encodeRatNode (constNode false) = [false, true, false, false, false, true, false] := by
  rfl


/-- **The rows of an AND node** take 33 bits. -/
theorem gateRows_and_length : (gateRows (fun a c => a && c)).length = 33 := by
  decide


/-- **The rows of an OR node** take 35 bits, for either polarity. -/
theorem gateRows_or_length (p : Bool) : (gateRows (fun a c => a || c == p)).length = 35 := by
  cases p <;> decide


/-- **A clause before its close is a finished formula.** Inside the clause `Ls` over the suffix
`ψ`, after the literals of `Ls`, closing the clause gives the block emission of `Ls :: ψ`; so
every literal boundary inside a clause is the open state of a tail of the clause, and the bounds
on finished formulas apply to it. -/
theorem preClose_eq (Ls : CNFClause) (ψ : CNF) :
    eClose (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))) =
      eFormula (Ls :: ψ) := by
  rw [eFormula_cons]
  rfl


/-- **Node counter before a close**, from the node bound of the finished formula. -/
theorem preClose_n_le (Ls : CNFClause) (ψ : CNF) :
    (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n + 1 ≤
      2 * (toks (Ls :: ψ)).length + 1 := by
  have h := eFormula_n_le (Ls :: ψ)
  rw [← preClose_eq Ls ψ, eClose_n] at h
  exact h


/-- **Dictionary size before a close**, from the dictionary bound of the finished formula. -/
theorem preClose_dict_le (Ls : CNFClause) (ψ : CNF) :
    (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).dict.length ≤
      (toks (Ls :: ψ)).length := by
  have h := (eFormula_dict_le (Ls :: ψ)).1
  rw [← preClose_eq Ls ψ, eClose_dict] at h
  exact h


/-- **Name lengths before a close**, from the dictionary bound of the finished formula. -/
theorem preClose_name_le (Ls : CNFClause) (ψ : CNF) :
    ∀ e ∈ (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).dict,
      e.1.length ≤ (toks (Ls :: ψ)).length := by
  intro e he
  have h := (eFormula_dict_le (Ls :: ψ)).2
  have he' : e ∈ (eFormula (Ls :: ψ)).dict := by
    rw [← preClose_eq Ls ψ, eClose_dict]
    exact he
  exact h e he'


/-- **Roots before a close** lie below the AND node the close writes. -/
theorem preClose_root_lt (Ls : CNFClause) (ψ : CNF) :
    ∀ e ∈ (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).dict,
      e.2 <
        (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n + 1 := by
  intro e he
  have hInv := eFormula_inv (Ls :: ψ)
  have h3 := hInv.2.2
  have he' : e ∈ (eFormula (Ls :: ψ)).dict := by
    rw [← preClose_eq Ls ψ, eClose_dict]
    exact he
  have hlt := h3 e he'
  have hn : (eFormula (Ls :: ψ)).n =
      (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n + 1 := by
    rw [← preClose_eq Ls ψ, eClose_n]
  rw [hn] at hlt
  exact hlt


/-- **The AND-chain output before a close** lies below the node counter. -/
theorem preClose_acc_lt (Ls : CNFClause) (ψ : CNF) :
    (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).acc <
      (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n := by
  have hAcc : (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).acc =
      (eFormula ψ).acc := by
    rw [foldl_eLit_acc, eOpen_acc]
  have hNge : (eOpen (eFormula ψ)).n ≤
      (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n :=
    foldl_eLit_n_ge _ _
  have hOpenN : (eFormula ψ).n ≤ (eOpen (eFormula ψ)).n := by
    rw [eOpen_n]
    exact Nat.le_succ _
  have hInv := (eFormula_inv ψ).1
  have hLe : (eFormula ψ).n ≤
      (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n :=
    le_trans hOpenN hNge
  rw [hAcc]
  exact lt_of_lt_of_le hInv hLe


/-- **The chain output before a close** is the last node written. -/
theorem preClose_o_lt (Ls : CNFClause) (ψ : CNF) :
    (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).o + 1 =
      (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))).n := by
  have hs : (eOpen (eFormula ψ)).o + 1 = (eOpen (eFormula ψ)).n := by
    rw [eOpen_o, eOpen_n]
  exact foldl_eLit_o _ _ hs


/-- **A tail of the first clause has fewer tokens.** -/
theorem toks_tail_le (l : ℕ × Bool) (Ls : CNFClause) (ψ : CNF) :
    (toks (Ls :: ψ)).length ≤ (toks ((l :: Ls) :: ψ)).length := by
  simp [toks, clauseToks, litToks]
  omega


/-! ### The machine -/

/-- **Stacks of the Cooper emitter.** Thirteen stacks: $T$ (tokens), $O$ (output), the counters
$N$ (the node counter), $A$ (the AND-chain output), $H$ (the chain output of the open clause) and
$V$ (the root of the current literal), $D$ (the dictionary of roots), $E$ (the walk's other
side), $M$ (the current name), $P$ (its polarity), the comparison scratch stacks $X$ and $Y$, and
the copy scratch stack $W$. -/
inductive K | T | O | N | A | H | V | D | E | M | P | X | Y | W
  deriving DecidableEq


/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.O, K.N, K.A, K.H, K.V, K.D, K.E, K.M, K.P, K.X, K.Y, K.W], by decide⟩
  complete := fun x => by cases x <;> decide

@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym


/-- **Counters read by copy sites**: the node counter, the AND-chain output, the chain output and
the root of the current literal. -/
inductive Src | n | a | h | v


/-- **Stack of a counter.** -/
def Src.k : Src → K
  | .n => .N
  | .a => .A
  | .h => .H
  | .v => .V


/-- **Unit symbol of a counter**: the clause token. -/
def Src.unit : (s : Src) → Γ s.k
  | .n => Sym.cl
  | .a => Sym.cl
  | .h => Sym.cl
  | .v => Sym.cl


/-- **Copy sites of the Cooper emitter.** Each pushes a constant block and then a counter in ones:
`orV p` and `orH` push the parents of an OR node of polarity `p` (its root, then the chain
output), `andH` and `andA` those of an AND node (the clause's chain output, then the AND-chain
output), and `fin` the node count. -/
inductive Site | orV (p : Bool) | orH | andH | andA | fin
  deriving DecidableEq


/-- **The copy sites, listed.** -/
def Site.all : List Site := [.orV true, .orV false, .orH, .andH, .andA, .fin]


/-- **Counter copied by a copy site.** -/
def Site.src : Site → Src
  | .orV _ => .v
  | .orH => .h
  | .andH => .h
  | .andA => .a
  | .fin => .n


/-- **Constant block of a copy site**, read top first: below the root of an OR node of polarity
`p`, a `false`, the row count `4` in unary and the rows of the gate `a || c == p`; below the
second parent of an AND node, the same with the rows of `a && c`; below the first parent of a
gate and below the node count, a `false`. -/
def Site.top : Site → List Bool
  | .orV p => false :: (unary 4 ++ gateRows (fun a c => a || c == p))
  | .orH => [false]
  | .andH => false :: (unary 4 ++ gateRows (fun a c => a && c))
  | .andA => [false]
  | .fin => [false]


/-- **Control labels of the Cooper emitter.** `init`: node `0`; `cls`: next clause or the end;
`opn` to `opnN`: open a clause; `lits`: next literal or the close; `lp`, `nm`: pop the polarity
and the name; `walk f` to `cpVW`: walk the dictionary, `f` recording a match (compare, restore,
move the name and the root to `E`, or the root of the first match to `V`); `back f`: move `E`
back to `D`; `root` to `putK`: write a root node and record the name; `dropM`, `dropY`: discard
the name of a recorded variable; `orC`, `orT`: the OR node; `clrH` to `clrV`: the counters after
a literal; `andT`: the AND node; `clrA` to `incNA`: the counters after a clause; `pre j`, `cpA j`,
`cpB j`: copy site `j`; `done`: halt. -/
inductive Lab
  | init | cls | opn | opnH | opnW | opnN | lits | lp | nm
  | walk (found : Bool) | cmp | rsM (e : Bool) | rsD (e : Bool) | mvN (e : Bool) | skN
  | skU (found : Bool) | getV | cpV | cpVW | back (found : Bool)
  | root | putN | putW | putM | putX | putK | dropM | dropY
  | orC | orT | clrH | setH | setHW | incN | clrV
  | andT | clrA | setA | setAW | clrHA | incNA
  | pre (j : Site) | cpA (j : Site) | cpB (j : Site) | done
  deriving DecidableEq


/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.init, .cls, .opn, .opnH, .opnW, .opnN, .lits, .lp, .nm, .cmp, .skN, .getV, .cpV,
        .cpVW, .root, .putN, .putW, .putM, .putX, .putK, .dropM, .dropY, .orC, .orT, .clrH,
        .setH, .setHW, .incN, .clrV, .andT, .clrA, .setA, .setAW, .clrHA, .incNA, .done] ++
      ([true, false].flatMap fun b => [Lab.walk b, .rsM b, .rsD b, .mvN b, .skU b, .back b]) ++
      (Site.all.flatMap fun j => [Lab.pre j, .cpA j, .cpB j]))
    (fun x => by
      cases x <;> (try rename_i a; cases a) <;> (try rename_i a; cases a) <;> decide)


/-- **Successor label of a copy site.** -/
def Site.nxt : Site → Lab
  | .orV _ => .pre .orH
  | .orH => .orT
  | .andH => .pre .andA
  | .andA => .andT
  | .fin => .done


/-- **Literal-marker test** for the top of a stack. -/
def isLit : Option Sym → Bool
  | some (.lit _) => true
  | _ => false


/-- **Reading unary units.** The clause token reads as a unit; every other symbol ends a run of
units. -/
def unitOf : Sym → Option Bool
  | .cl => some true
  | _ => none


/-- **The Cooper emitter machine.** It writes node `0` (constant true) and then reads the clauses
one at a time. A clause writes a constant-false node, its chain output. A literal moves its name
to `M` and walks the dictionary on `D` for it: at the first entry with that name the entry's root
is copied to `V`; when no entry has the name, a root node is written and the name is recorded
under it. The literal then writes its OR node, joining the chain output `H` to the root `V`, and
the OR node becomes the chain output. At the end of a clause its AND node joins the AND chain `A`
to the clause's chain output and becomes the AND-chain output. When the tokens run out the node
count is pushed and the machine halts. Every node's code is pushed onto `O` from the bottom up,
so that `O` reads it top first, and the counters are restored through the scratch stack `W`. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .init => pushList .O (encodeRatNode (constNode true)).reverse <|
      .push .N (fun _ => Sym.cl) <| .goto fun _ => .cls
  | .cls => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .pre .fin) <|
      .pop .T (fun s _ => s) <| .goto fun _ => .opn
  | .opn => emitR .O (encodeRatNode (constNode false)) .opnH
  | .opnH => xfer .N [⟨.H, Sym.cl⟩, ⟨.W, Sym.cl⟩] .opnH .opnW
  | .opnW => xfer .W [⟨.N, Sym.cl⟩] .opnW .opnN
  | .opnN => emit .N [Sym.cl] .lits
  | .lits => .peek .T (fun _ o => isLit o) <| .branch id (.goto fun _ => .lp)
      (.goto fun _ => .pre .andH)
  | .lp => .pop .T (fun _ o => o == some (.lit true)) <| .push .P (fun s => Sym.lit s) <|
      .goto fun _ => .nm
  | .nm => moveB .T .M Sym.bit? Sym.bit .nm (.walk false)
  | .walk f => .peek .D (fun _ o => o.isNone) <| .branch id (.goto fun _ => .back f) <|
      .pop .D (fun s _ => s) <| .push .E (fun _ => Sym.lit true) <|
        .goto fun _ => if f then .skN else .cmp
  | .cmp => cmpB .M .D .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit .cmp (.rsM true) (.rsM false)
  | .rsM e => moveB .X .M Sym.bit? Sym.bit (.rsM e) (.rsD e)
  | .rsD e => moveB .Y .D Sym.bit? Sym.bit (.rsD e) (.mvN e)
  | .mvN e => moveB .D .E Sym.bit? Sym.bit (.mvN e) (if e then .getV else .skU false)
  | .skN => moveB .D .E Sym.bit? Sym.bit .skN (.skU true)
  | .skU f => moveB .D .E unitOf (fun _ => Sym.cl) (.skU f) (.walk f)
  | .getV => moveB .D .V unitOf (fun _ => Sym.cl) .getV .cpV
  | .cpV => xfer .V [⟨.E, Sym.cl⟩, ⟨.W, Sym.cl⟩] .cpV .cpVW
  | .cpVW => xfer .W [⟨.V, Sym.cl⟩] .cpVW (.walk true)
  | .back f => .peek .E (fun _ o => o.isNone) <|
      .branch id (.goto fun _ => if f then .dropM else .root) <|
      .peek .E (fun _ o => o == some .cl) <| .branch id
        (.pop .E (fun s _ => s) <| .push .D (fun _ => Sym.cl) <| .goto fun _ => .back f) <|
      .peek .E (fun _ o => isLit o) <| .branch id
        (.pop .E (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
          .goto fun _ => .back f)
        (.pop .E (fun _ o => o == some (.bit true)) <| .push .D (fun s => Sym.bit s) <|
          .goto fun _ => .back f)
  | .root => emitR .O (encodeRatNode rootNode) .putN
  | .putN => xfer .N [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] .putN .putW
  | .putW => xfer .W [⟨.N, Sym.cl⟩] .putW .putM
  | .putM => moveB .M .X Sym.bit? Sym.bit .putM .putX
  | .putX => moveB .X .D Sym.bit? Sym.bit .putX .putK
  | .putK => .push .D (fun _ => Sym.lit true) <| .push .N (fun _ => Sym.cl) <|
      .goto fun _ => .orC
  | .dropM => moveB .M .Y Sym.bit? (fun _ => Sym.cl) .dropM .dropY
  | .dropY => xfer .Y [] .dropY .orC
  | .orC => .pop .P (fun _ o => o == some (.lit true)) <| .goto fun s => .pre (.orV s)
  | .orT => emitR .O (unary 2) .clrH
  | .clrH => xfer .H [] .clrH .setH
  | .setH => xfer .N [⟨.H, Sym.cl⟩, ⟨.W, Sym.cl⟩] .setH .setHW
  | .setHW => xfer .W [⟨.N, Sym.cl⟩] .setHW .incN
  | .incN => emit .N [Sym.cl] .clrV
  | .clrV => xfer .V [] .clrV .lits
  | .andT => emitR .O (unary 2) .clrA
  | .clrA => xfer .A [] .clrA .setA
  | .setA => xfer .N [⟨.A, Sym.cl⟩, ⟨.W, Sym.cl⟩] .setA .setAW
  | .setAW => xfer .W [⟨.N, Sym.cl⟩] .setAW .clrHA
  | .clrHA => xfer .H [] .clrHA .incNA
  | .incNA => emit .N [Sym.cl] .cls
  | .pre j => emitR .O j.top (.cpA j)
  | .cpA j => xfer j.src.k [⟨.O, true⟩, ⟨.W, Sym.cl⟩] (.cpA j) (.cpB j)
  | .cpB j => xfer .W [⟨j.src.k, j.src.unit⟩] (.cpB j) j.nxt
  | .done => .halt


/-- **Start label of the Cooper emitter**: the label that writes node `0`. -/
def start : Lab := .init


/-! ### Quiescent states -/

/-- **A dictionary entry on `D`**: a marker, the name bits (least significant bit first) and the
root in unary, top first. -/
def dEnt (e : List Bool × ℕ) : List Sym := .lit true :: (e.1.map Sym.bit ++ cnt Sym.cl e.2)


/-- **Quiescent states of the Cooper emitter.** The contents of the token stack, the output
stack, the dictionary, the walk's other side, the name and the polarity stacks, and the values of
the four counters. On the machine the counters hold that many clause tokens and the scratch
stacks `X`, `Y`, `W` are empty. -/
structure MS where
  t : List Sym
  o : List Bool
  n : ℕ
  a : ℕ
  h : ℕ
  v : ℕ
  d : List Sym
  e : List Sym
  m : List Sym
  p : List Sym


/-- **Stacks of a quiescent state**: the counters as that many clause tokens, the scratch stacks
empty. -/
def MS.stk (s : MS) : ∀ k, List (Γ k)
  | .T => s.t
  | .O => s.o
  | .N => cnt Sym.cl s.n
  | .A => cnt Sym.cl s.a
  | .H => cnt Sym.cl s.h
  | .V => cnt Sym.cl s.v
  | .D => s.d
  | .E => s.e
  | .M => s.m
  | .P => s.p
  | .X | .Y | .W => []


/-- **Counter values of a quiescent state.** -/
def MS.val (s : MS) : Src → ℕ
  | .n => s.n
  | .a => s.a
  | .h => s.h
  | .v => s.v


section MSLemmas


variable (s : MS)

@[simp] theorem stk_T : s.stk .T = s.t := rfl

@[simp] theorem stk_O : s.stk .O = s.o := rfl

@[simp] theorem stk_N : s.stk .N = List.replicate s.n Sym.cl := rfl

@[simp] theorem stk_A : s.stk .A = List.replicate s.a Sym.cl := rfl

@[simp] theorem stk_H : s.stk .H = List.replicate s.h Sym.cl := rfl

@[simp] theorem stk_V : s.stk .V = List.replicate s.v Sym.cl := rfl

@[simp] theorem stk_D : s.stk .D = s.d := rfl

@[simp] theorem stk_E : s.stk .E = s.e := rfl

@[simp] theorem stk_M : s.stk .M = s.m := rfl

@[simp] theorem stk_P : s.stk .P = s.p := rfl

@[simp] theorem stk_X : s.stk .X = [] := rfl

@[simp] theorem stk_Y : s.stk .Y = [] := rfl

@[simp] theorem stk_W : s.stk .W = [] := rfl

@[simp] theorem upd_T (x : List Sym) : update s.stk .T x = {s with t := x}.stk := by
  funext k; cases k <;> rfl

@[simp] theorem upd_O (x : List Bool) : update s.stk .O x = {s with o := x}.stk := by
  funext k; cases k <;> rfl

@[simp] theorem upd_D (x : List Sym) : update s.stk .D x = {s with d := x}.stk := by
  funext k; cases k <;> rfl

@[simp] theorem upd_E (x : List Sym) : update s.stk .E x = {s with e := x}.stk := by
  funext k; cases k <;> rfl

@[simp] theorem upd_M (x : List Sym) : update s.stk .M x = {s with m := x}.stk := by
  funext k; cases k <;> rfl

@[simp] theorem upd_P (x : List Sym) : update s.stk .P x = {s with p := x}.stk := by
  funext k; cases k <;> rfl

theorem upd_N (j : ℕ) : update s.stk .N (List.replicate j Sym.cl) = {s with n := j}.stk := by
  funext k; cases k <;> rfl

theorem upd_A (j : ℕ) : update s.stk .A (List.replicate j Sym.cl) = {s with a := j}.stk := by
  funext k; cases k <;> rfl

theorem upd_H (j : ℕ) : update s.stk .H (List.replicate j Sym.cl) = {s with h := j}.stk := by
  funext k; cases k <;> rfl

theorem upd_V (j : ℕ) : update s.stk .V (List.replicate j Sym.cl) = {s with v := j}.stk := by
  funext k; cases k <;> rfl


theorem stk_src (j : Src) : s.stk j.k = cnt j.unit (s.val j) := by cases j <;> rfl


end MSLemmas


/-- **Counters are not the output stack.** -/
theorem Src.k_ne_O (j : Src) : j.k ≠ .O := by cases j <;> decide


/-- **Counters are not the copy scratch stack.** -/
theorem Src.k_ne_W (j : Src) : j.k ≠ .W := by cases j <;> decide


/-- **Spec state as a quiescent state**: the token stack `t`, the output written so far above
`o0`, the counters of `s`, the root counter `0`, the dictionary on `D`, and empty walk, name and
polarity stacks. -/
def enc (s : ESt) (t : List Sym) (o0 : List Bool) : MS :=
  ⟨t, s.out ++ o0, s.n, s.acc, s.o, 0, s.dict.flatMap dEnt, [], [], []⟩


/-- **Bounds at a literal boundary**, for a bound `Lb` on the token count: the node counter is at
most `2 Lb + 1`, the AND-chain and chain outputs lie below it, the dictionary has at most `Lb`
entries, each with a name of at most `Lb` bits and a root at most the node counter. -/
def Bnd (Lb : ℕ) (s : ESt) : Prop :=
  s.n ≤ 2 * Lb + 1 ∧ s.acc < s.n ∧ s.o < s.n ∧ s.dict.length ≤ Lb ∧
    ∀ e ∈ s.dict, e.1.length ≤ Lb ∧ e.2 ≤ s.n


/-- **Steps of the dictionary walk** for the name `u`: per entry at most the comparison (with its
restores), the move of the entry and the copy of its root, plus one final step. -/
def walkCost (u : List Bool) (d : List (List Bool × ℕ)) : ℕ :=
  (d.map fun e => 3 * u.length + e.1.length + 3 * e.2 + 8).sum + 1


/-- **Steps of one literal**, for a bound `Lb` on the token count: `100 (Lb + 1)²`. -/
def litCost (Lb : ℕ) : ℕ := 100 * (Lb + 1) ^ 2


/-- **Per-token step budget**, for a bound `Lb` on the token count: `200 (Lb + 1)²`, at least the
cost of a literal and of a clause's open and close. -/
def budget (Lb : ℕ) : ℕ := 200 * (Lb + 1) ^ 2


/-- **Bounds at every literal boundary.** The open state of a tail `Ls` of a clause over the
suffix `ψ` satisfies the literal-boundary bounds for every bound at least `|toks (Ls :: ψ)|`. -/
theorem bnd_preClose (Lb : ℕ) (Ls : CNFClause) (ψ : CNF) (h : (toks (Ls :: ψ)).length ≤ Lb) :
    Bnd Lb (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hN := preClose_n_le Ls ψ
    omega
  · exact preClose_acc_lt Ls ψ
  · have ho := preClose_o_lt Ls ψ
    omega
  · exact le_trans (preClose_dict_le Ls ψ) h
  · intro e he
    constructor
    · exact le_trans (preClose_name_le Ls ψ e he) h
    · have hr := preClose_root_lt Ls ψ e he
      omega


/-! ### Copy sites -/

/-- **Copying a counter through `W`.** Let `j` be a counter and `c` a stack other than the
counter's stack and `W`. If label `l₁` moves the counter onto `c` (as copies of `x`) and onto
`W`, and label `l₂` moves `W` back onto the counter, then from `l₁`, with the counter holding
`val` units and `W` empty, the machine reaches `next` in exactly `2 val + 2` steps with `val`
copies of `x` pushed onto `c` and nothing else changed. -/
theorem dup_run (j : Src) {c : K} (x : Γ c) (hc : c ≠ j.k) (hcW : c ≠ .W) {l₁ l₂ next : Lab}
    (h₁ : prog l₁ = xfer j.k [⟨c, x⟩, ⟨.W, Sym.cl⟩] l₁ l₂)
    (h₂ : prog l₂ = xfer .W [⟨j.k, j.unit⟩] l₂ next) (val : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S j.k = cnt j.unit val) (hW : S .W = []) :
    ∃ v', Run prog (2 * val + 2) ⟨some l₁, v, S⟩
      ⟨some next, v', update S c (cnt x val ++ S c)⟩ := by
  have hsW := j.k_ne_W
  have r₁ := xfer_run h₁ (pair_nodupKeys x (Sym.cl : Γ .W) hcW) (by simp [hc.symm, hsW]) j.unit
    val v S hS
  set S₁ := addU [⟨c, x⟩, ⟨.W, Sym.cl⟩] val (update S j.k []) with hS₁
  have h₁W : S₁ .W = cnt (Sym.cl : Γ .W) val := by
    rw [hS₁, addU_pair_snd _ _ _ _ hcW.symm, update_of_ne hsW.symm, hW, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys j.unit) (by simp [hsW.symm]) (Sym.cl : Γ .W) val
    (Flag.tag false) S₁ h₁W
  have hfin : addU [⟨j.k, j.unit⟩] val (update S₁ .W []) = update S c (cnt x val ++ S c) := by
    funext k
    by_cases hks : k = j.k
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


/-- **Bits of a copy site**: its counter in ones above its constant block. -/
def atom (s : MS) (j : Site) : List Bool := cnt true (s.val j.src) ++ j.top


/-- **Running a copy site.** From `pre j` the machine reaches the successor of `j` in exactly
`2 c + 3` steps, `c` the counter `j` copies, with the bits of `j` pushed onto `O`. -/
theorem site_run (j : Site) (s : MS) (v : Bool) :
    ∃ v', Run prog (2 * s.val j.src + 3) ⟨some (.pre j), v, s.stk⟩
      ⟨some j.nxt, v', {s with o := atom s j ++ s.o}.stk⟩ := by
  have r₁ := emitR_run (M := prog) (self := .pre j) (next := .cpA j) (k := .O) (ys := j.top) rfl
    v s.stk
  obtain ⟨v', r₂⟩ := dup_run j.src (true : Γ .O) (Ne.symm j.src.k_ne_O) (by decide)
    (l₁ := .cpA j) (l₂ := .cpB j) (next := j.nxt) rfl rfl (s.val j.src) v
    (update s.stk .O (j.top ++ s.stk .O))
    (by rw [update_of_ne j.src.k_ne_O]; exact stk_src s j.src) rfl
  have e : update (update s.stk .O (j.top ++ s.stk .O)) .O
      (cnt true (s.val j.src) ++ update s.stk .O (j.top ++ s.stk .O) .O) =
      {s with o := atom s j ++ s.o}.stk := by simp [atom]
  rw [e] at r₂
  exact ⟨v', (r₁.trans r₂).of_eq (by omega)⟩


/-- **Writing an OR node.** From `orC`, with the polarity `p` alone on `P`, the machine reaches
`clrH` in exactly `2 v + 2 h + 8` steps, `v` the root and `h` the chain output, with `P` emptied
and the code of the OR node joining the chain output to the root pushed onto `O`. -/
theorem orNode_run (p : Bool) (s : MS) (v : Bool) (hP : s.p = [.lit p]) :
    ∃ v', Run prog (2 * s.v + 2 * s.h + 8) ⟨some .orC, v, s.stk⟩
      ⟨some .clrH, v', {s with p := [], o := encodeRatNode (orNode s.h s.v p) ++ s.o}.stk⟩ := by
  have r0 : Run prog 1 ⟨some .orC, v, s.stk⟩ ⟨some (.pre (.orV p)), p, {s with p := []}.stk⟩ := by
    cases p
    · apply Run.single
      simp [prog, TM2.stepAux, hP]
    · apply Run.single
      simp [prog, TM2.stepAux, hP]
  obtain ⟨v1, r1⟩ := site_run (.orV p) {s with p := []} p
  obtain ⟨v2, r2⟩ := site_run .orH {s with p := [], o := atom {s with p := []} (.orV p) ++ s.o} v1
  have r3 := emitR_run (M := prog) (self := .orT) (next := .clrH) (k := .O) (ys := unary 2) rfl v2
    {s with p := [], o := atom {s with p := [], o := atom {s with p := []} (.orV p) ++ s.o} .orH ++
      (atom {s with p := []} (.orV p) ++ s.o)}.stk
  have r01 := r0.trans r1
  have r012 := r01.trans r2
  have r0123 := r012.trans r3
  have he : update {s with p := [], o := atom {s with p := [], o := atom {s with p := []} (.orV p) ++ s.o} .orH ++
      (atom {s with p := []} (.orV p) ++ s.o)}.stk .O
      (unary 2 ++ {s with p := [], o := atom {s with p := [], o := atom {s with p := []} (.orV p) ++ s.o} .orH ++
      (atom {s with p := []} (.orV p) ++ s.o)}.stk .O) =
      {s with p := [], o := encodeRatNode (orNode s.h s.v p) ++ s.o}.stk := by
    simp [atom, Site.top, Site.src, MS.val, encodeRatNode_orNode, unary, cnt]
  rw [he] at r0123
  have hv : ({s with p := []}.val (Site.orV p).src) = s.v := rfl
  have hh : ({s with p := [], o := atom {s with p := []} (.orV p) ++ s.o}.val Site.orH.src) = s.h := rfl
  exact ⟨_, r0123.of_eq (by omega)⟩


/-- **Writing an AND node.** From `pre andH` the machine reaches `clrA` in exactly
`2 h + 2 a + 7` steps, `h` the chain output and `a` the AND-chain output, with the code of the
AND node joining the AND-chain output to the chain output pushed onto `O`. -/
theorem andNode_run (s : MS) (v : Bool) :
    ∃ v', Run prog (2 * s.h + 2 * s.a + 7) ⟨some (.pre .andH), v, s.stk⟩
      ⟨some .clrA, v', {s with o := encodeRatNode (andNode s.a s.h) ++ s.o}.stk⟩ := by
  obtain ⟨v1, r1⟩ := site_run .andH s v
  obtain ⟨v2, r2⟩ := site_run .andA {s with o := atom s .andH ++ s.o} v1
  have r3 := emitR_run (M := prog) (self := .andT) (next := .clrA) (k := .O) (ys := unary 2) rfl v2
    {s with o := atom {s with o := atom s .andH ++ s.o} .andA ++ (atom s .andH ++ s.o)}.stk
  have r12 := r1.trans r2
  have r123 := r12.trans r3
  have he : update {s with o := atom {s with o := atom s .andH ++ s.o} .andA ++ (atom s .andH ++ s.o)}.stk .O
      (unary 2 ++ {s with o := atom {s with o := atom s .andH ++ s.o} .andA ++ (atom s .andH ++ s.o)}.stk .O) =
      {s with o := encodeRatNode (andNode s.a s.h) ++ s.o}.stk := by
    simp [atom, Site.top, Site.src, MS.val, encodeRatNode_andNode, unary, cnt]
  rw [he] at r123
  have hh : (s.val Site.andH.src) = s.h := rfl
  have ha : ({s with o := atom s .andH ++ s.o}.val Site.andA.src) = s.a := rfl
  exact ⟨_, r123.of_eq (by omega)⟩

theorem orReset_run_aux1 (s : MS) :
    addU ([] : List (Σ k, Γ k)) s.h (update s.stk .H []) = {s with h := 0}.stk := by
  have h0 : addU ([] : List (Σ k, Γ k)) s.h (update s.stk .H []) = update s.stk .H [] := by
    funext k; simp [addU]
  rw [h0]
  simpa using upd_H s 0

theorem orReset_run_aux2 (s : MS) :
    Function.update ({s with h := 0}.stk) K.H (cnt Sym.cl (s.n + 0)) =
      {s with h := s.n}.stk := by
  simpa using upd_H {s with h := 0} s.n

theorem orReset_run_aux3 (s : MS) :
    Function.update ({s with h := s.n}.stk) K.N
        ([Sym.cl].reverse ++ ({s with h := s.n}.stk) K.N) =
      {s with h := s.n, n := s.n + 1}.stk := by
  have hN : ({s with h := s.n}.stk) K.N = cnt Sym.cl s.n := by simp
  rw [hN]
  have hrev : ([Sym.cl].reverse ++ cnt Sym.cl s.n) = cnt Sym.cl (s.n + 1) := by
    simp [cnt, List.replicate_succ]
  rw [hrev]
  have := upd_N {s with h := s.n} (s.n + 1)
  simpa using this

theorem orReset_run_aux4 (s : MS) :
    addU ([] : List (Σ k, Γ k)) s.v
        (Function.update ({s with h := s.n, n := s.n + 1}.stk) K.V []) =
      {s with h := s.n, n := s.n + 1, v := 0}.stk := by
  have h0 : addU ([] : List (Σ k, Γ k)) s.v
      (Function.update ({s with h := s.n, n := s.n + 1}.stk) K.V []) =
      Function.update ({s with h := s.n, n := s.n + 1}.stk) K.V [] := by
    funext k; simp [addU]
  rw [h0]
  simpa using upd_V {s with h := s.n, n := s.n + 1} 0


/-- **Counters after a literal.** From `clrH` the machine reaches `lits` in exactly
`h + 2 n + v + 5` steps: the chain output becomes the node counter's value, the node counter
advances, and the root counter is cleared. -/
theorem orReset_run (s : MS) (v : Bool) :
    ∃ v', Run prog (s.h + 2 * s.n + s.v + 5) ⟨some .clrH, v, s.stk⟩
      ⟨some .lits, v', {s with h := s.n, n := s.n + 1, v := 0}.stk⟩ := by
  have r1 := xfer_run (M := prog) (self := .clrH) (next := .setH) (k := .H)
    (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl s.h v s.stk rfl
  rw [orReset_run_aux1 s] at r1
  have r2 := copy_run (M := prog) (a := .N) (c := .H) (t := .W)
    (ua := Sym.cl) (uc := Sym.cl) (ut := Sym.cl)
    (l₁ := .setH) (l₂ := .setHW) (next := .incN)
    rfl rfl (by decide) (by decide) (by decide)
    s.n 0 (Flag.tag false) {s with h := 0}.stk (by simp) (by simp) rfl
  rw [orReset_run_aux2 s] at r2
  have r3 := emit_run (M := prog) (self := .incN) (next := .clrV) (k := .N)
    (xs := [Sym.cl]) rfl (Flag.tag false) {s with h := s.n}.stk
  rw [orReset_run_aux3 s] at r3
  have r4 := xfer_run (M := prog) (self := .clrV) (next := .lits) (k := .V)
    (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl s.v (Flag.tag false)
    {s with h := s.n, n := s.n + 1}.stk (by simp)
  rw [orReset_run_aux4 s] at r4
  exact ⟨_, (((r1.trans r2).trans r3).trans r4).of_eq (by omega)⟩

theorem andReset_run_aux1 (s : MS) :
    addU ([] : List (Σ k, Γ k)) s.a (update s.stk .A []) = {s with a := 0}.stk := by
  have h0 : addU ([] : List (Σ k, Γ k)) s.a (update s.stk .A []) = update s.stk .A [] := by
    funext k; simp [addU]
  rw [h0]
  simpa using upd_A s 0

theorem andReset_run_aux2 (s : MS) :
    Function.update ({s with a := 0}.stk) K.A (cnt Sym.cl (s.n + 0)) =
      {s with a := s.n}.stk := by
  simpa using upd_A {s with a := 0} s.n

theorem andReset_run_aux3 (s : MS) :
    addU ([] : List (Σ k, Γ k)) s.h
        (Function.update ({s with a := s.n}.stk) K.H []) =
      {s with a := s.n, h := 0}.stk := by
  have h0 : addU ([] : List (Σ k, Γ k)) s.h
      (Function.update ({s with a := s.n}.stk) K.H []) =
      Function.update ({s with a := s.n}.stk) K.H [] := by
    funext k; simp [addU]
  rw [h0]
  simpa using upd_H {s with a := s.n} 0

theorem andReset_run_aux4 (s : MS) :
    Function.update ({s with a := s.n, h := 0}.stk) K.N
        ([Sym.cl].reverse ++ ({s with a := s.n, h := 0}.stk) K.N) =
      {s with a := s.n, h := 0, n := s.n + 1}.stk := by
  have hN : ({s with a := s.n, h := 0}.stk) K.N = cnt Sym.cl s.n := by simp
  rw [hN]
  have hrev : ([Sym.cl].reverse ++ cnt Sym.cl s.n) = cnt Sym.cl (s.n + 1) := by
    simp [cnt, List.replicate_succ]
  rw [hrev]
  have := upd_N {s with a := s.n, h := 0} (s.n + 1)
  simpa using this


/-- **Counters after a clause.** From `clrA` the machine reaches `cls` in exactly
`a + 2 n + h + 5` steps: the AND-chain output becomes the node counter's value, the chain output
is cleared, and the node counter advances. -/
theorem andReset_run (s : MS) (v : Bool) :
    ∃ v', Run prog (s.a + 2 * s.n + s.h + 5) ⟨some .clrA, v, s.stk⟩
      ⟨some .cls, v', {s with a := s.n, h := 0, n := s.n + 1}.stk⟩ := by
  have r1 := xfer_run (M := prog) (self := .clrA) (next := .setA) (k := .A)
    (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl s.a v s.stk rfl
  rw [andReset_run_aux1 s] at r1
  have r2 := copy_run (M := prog) (a := .N) (c := .A) (t := .W)
    (ua := Sym.cl) (uc := Sym.cl) (ut := Sym.cl)
    (l₁ := .setA) (l₂ := .setAW) (next := .clrHA)
    rfl rfl (by decide) (by decide) (by decide)
    s.n 0 (Flag.tag false) {s with a := 0}.stk (by simp) (by simp) rfl
  rw [andReset_run_aux2 s] at r2
  have r3 := xfer_run (M := prog) (self := .clrHA) (next := .incNA) (k := .H)
    (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl s.h (Flag.tag false)
    {s with a := s.n}.stk (by simp)
  rw [andReset_run_aux3 s] at r3
  have r4 := emit_run (M := prog) (self := .incNA) (next := .cls) (k := .N)
    (xs := [Sym.cl]) rfl (Flag.tag false) {s with a := s.n, h := 0}.stk
  rw [andReset_run_aux4 s] at r4
  exact ⟨_, (((r1.trans r2).trans r3).trans r4).of_eq (by omega)⟩


/-! ### The dictionary walk, entry by entry -/

/-- **Comparing the name with an entry's name.** With the name `u` on `M` and an entry's name `w`
on `D` above a rest that does not start with a name bit, the machine goes from `cmp` to
`mvN (u = w)` within `3 |u| + 3` steps and leaves every stack as it was. -/
theorem cmp_run (s : MS) (v : Bool) (u w : List Bool) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) (hM : s.m = u.map Sym.bit)
    (hD : s.d = w.map Sym.bit ++ R) :
    ∃ v', RunLe prog (3 * u.length + 3) ⟨some .cmp, v, s.stk⟩
      ⟨some (.mvN (decide (u = w))), v', s.stk⟩ := by
  have hd : Distinct4 K.M K.D K.X K.Y :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1M, h1D, h1X, h1Y, h1k⟩ :=
    cmpB_run (M := prog) (self := .cmp) (eqL := .rsM true) (neL := .rsM false)
      (a := .M) (b := .D) (ta := .X) (tb := .Y)
      (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) rfl hd
      u w (u.map Sym.bit) [] (w.map Sym.bit) R v s.stk (by simp [hM]) hD
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map u)
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map w) rfl hR
  have hl : (if u = w then Lab.rsM true else Lab.rsM false) =
      Lab.rsM (decide (u = w)) := by
    split <;> simp_all
  rw [hl] at r₁
  obtain ⟨v₂, S₂, r₂, h2X, h2M, h2k⟩ :=
    moveB_restore (M := prog) (self' := .rsM (decide (u = w)))
      (next := .rsD (decide (u = w))) (t := .X) (a := .M)
      (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?)
      rfl (by decide) (fun _ => rfl)
      Cslib.Complexity.SatVerifier.Lookup.bit_of_bit?
      u cp (u.map Sym.bit) [] [] v₁ S₁
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map u) hcu
      (by simpa using h1X) h1M rfl
  obtain ⟨v₃, S₃, r₃, h3Y, h3D, h3k⟩ :=
    moveB_restore (M := prog) (self' := .rsD (decide (u = w)))
      (next := .mvN (decide (u = w))) (t := .Y) (a := .D)
      (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?)
      rfl (by decide) (fun _ => rfl)
      Cslib.Complexity.SatVerifier.Lookup.bit_of_bit?
      w cp (w.map Sym.bit) R [] v₂ S₂
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map w) hcw
      (by simp [h2k, h1Y]) (by simp [h2k, h1D]) rfl
  have hS : S₃ = s.stk := by
    funext k; cases k <;> simp [h3Y, h3D, h3k, h2X, h2M, h2k, h1k, hM, hD]
  rw [hS] at r₃
  refine ⟨v₃, (((r₁.trans r₂).trans r₃).le ?_)⟩
  have := hcu.length_le
  omega

theorem ent_found_aux1 (n : ℕ) : IsBitBlock unitOf (cnt Sym.cl n) (cnt true n) := by
  simp [IsBitBlock, cnt, unitOf]

theorem ent_found_aux2 (d : List (List Bool × ℕ)) :
    (d.flatMap dEnt).head?.bind Sym.bit? = none := by
  cases d with
  | nil => rfl
  | cons e d' => simp [dEnt, Sym.bit?]

theorem ent_found_aux3 (n : ℕ) (d : List (List Bool × ℕ)) :
    EndsBitBlock Sym.bit? (cnt Sym.cl n ++ d.flatMap dEnt) := by
  cases n with
  | zero => simpa [cnt, EndsBitBlock] using ent_found_aux2 d
  | succ n => simp [EndsBitBlock, cnt, List.replicate_succ, Sym.bit?]

theorem ent_found_aux4 (d : List (List Bool × ℕ)) :
    EndsBitBlock unitOf (d.flatMap dEnt) := by
  cases d with
  | nil => rfl
  | cons e d' => simp [EndsBitBlock, dEnt, unitOf]


/-- **The first entry with the name.** While searching, an entry whose name is the name `u` moves
to `E` and its root is copied onto the empty root counter; the walk goes on with a match
recorded. -/
theorem ent_hit (u : List Bool) (e : List Bool × ℕ) (hu : u = e.1) (d : List (List Bool × ℕ))
    (s : MS) (v : Bool) (hD : s.d = dEnt e ++ d.flatMap dEnt) (hM : s.m = u.map Sym.bit)
    (hV : s.v = 0) :
    ∃ v', RunLe prog (3 * u.length + e.1.length + 3 * e.2 + 8) ⟨some (.walk false), v, s.stk⟩
      ⟨some (.walk true), v',
        {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e, v := e.2}.stk⟩ := by
  have hDcons : s.d = .lit true :: ((e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt) := by
    simp [hD, dEnt]
  have r1 : Run prog 1 ⟨some (.walk false), v, s.stk⟩
      ⟨some .cmp, false, {s with
        d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt,
        e := .lit true :: s.e}.stk⟩ := by
    apply Run.single
    simp [prog, TM2.stepAux, hDcons]
  have hdec : decide (u = e.1) = true := by simp [hu]
  obtain ⟨v₂, r₂⟩ := cmp_run {s with
      d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt,
      e := .lit true :: s.e} false u e.1 (cnt Sym.cl e.2 ++ d.flatMap dEnt)
    (ent_found_aux3 e.2 d) hM (by simp [List.append_assoc])
  rw [hdec] at r₂
  obtain ⟨v₃, S₃, r₃, h3D, h3E, h3k⟩ :=
    moveB_run (M := prog) (self := .mvN true) (next := .getV) (a := .D) (b := .E)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      e.1 (e.1.map Sym.bit) (cnt Sym.cl e.2 ++ d.flatMap dEnt) v₂
      {s with d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt, e := .lit true :: s.e}.stk
      (by simp [List.append_assoc])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map e.1)
      (ent_found_aux3 e.2 d)
  obtain ⟨v₄, S₄, r₄, h4D, h4V, h4k⟩ :=
    moveB_run (M := prog) (self := .getV) (next := .cpV) (a := .D) (b := .V)
      (d := unitOf) (g := fun _ => Sym.cl) rfl (by decide)
      (cnt true e.2) (cnt Sym.cl e.2) (d.flatMap dEnt) v₃ S₃
      h3D (ent_found_aux1 e.2) (ent_found_aux4 d)
  have hlen : (cnt true e.2).length = e.2 := cnt_length true e.2
  rw [hlen] at r₄
  have hS3V : S₃ .V = cnt Sym.cl s.v := h3k .V (by decide) (by decide)
  have hS3V' : S₃ .V = [] := by simp [hS3V, hV]
  have hmap : (((cnt true e.2).map fun _ => Sym.cl).reverse) = cnt Sym.cl e.2 := by
    simp [cnt]
  have h4V' : S₄ .V = cnt Sym.cl e.2 := by rw [h4V, hS3V', List.append_nil, hmap]
  have h4W : S₄ .W = [] := by
    simp [h4k .W (by decide) (by decide), h3k .W (by decide) (by decide)]
  obtain ⟨v₅, r₅⟩ := dup_run (j := .v) (c := .E) (x := Sym.cl)
    (by decide) (by decide) (l₁ := .cpV) (l₂ := .cpVW) (next := .walk true)
    rfl rfl e.2 v₄ S₄ h4V' h4W
  have h3E' : S₃ .E = (e.1.map Sym.bit).reverse ++ .lit true :: s.e := h3E
  have hE : cnt Sym.cl e.2 ++ S₃ .E = (dEnt e).reverse ++ s.e := by
    rw [h3E']
    simp [dEnt, cnt, List.reverse_replicate, List.append_assoc]
  have hS : update S₄ .E (cnt Sym.cl e.2 ++ S₄ .E) =
      {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e, v := e.2}.stk := by
    funext k
    cases k <;> simp [hE, h4D, h4V', h4k, h3k]
  rw [hS] at r₅
  exact ⟨v₅, (((((r1.le le_rfl).trans r₂).trans (r₃.le le_rfl)).trans (r₄.le le_rfl)).trans
    (r₅.le le_rfl)).mono (by omega)⟩


/-- **An entry with another name.** While searching, an entry whose name is not `u` moves to `E`
and the search goes on. -/
theorem ent_miss (u : List Bool) (e : List Bool × ℕ) (hu : u ≠ e.1) (d : List (List Bool × ℕ))
    (s : MS) (v : Bool) (hD : s.d = dEnt e ++ d.flatMap dEnt) (hM : s.m = u.map Sym.bit) :
    ∃ v', RunLe prog (3 * u.length + e.1.length + e.2 + 6) ⟨some (.walk false), v, s.stk⟩
      ⟨some (.walk false), v', {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e}.stk⟩ := by
  have hDcons : s.d = .lit true :: ((e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt) := by
    simp [hD, dEnt]
  have r1 : Run prog 1 ⟨some (.walk false), v, s.stk⟩
      ⟨some .cmp, false, {s with
        d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt,
        e := .lit true :: s.e}.stk⟩ := by
    apply Run.single
    simp [prog, TM2.stepAux, hDcons]
  have hdec : decide (u = e.1) = false := by simp [hu]
  obtain ⟨v₂, r₂⟩ := cmp_run {s with
      d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt,
      e := .lit true :: s.e} false u e.1 (cnt Sym.cl e.2 ++ d.flatMap dEnt)
    (ent_found_aux3 e.2 d) hM (by simp [List.append_assoc])
  rw [hdec] at r₂
  obtain ⟨v₃, S₃, r₃, h3D, h3E, h3k⟩ :=
    moveB_run (M := prog) (self := .mvN false) (next := .skU false) (a := .D) (b := .E)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      e.1 (e.1.map Sym.bit) (cnt Sym.cl e.2 ++ d.flatMap dEnt) v₂
      {s with d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt, e := .lit true :: s.e}.stk
      (by simp [List.append_assoc])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map e.1)
      (ent_found_aux3 e.2 d)
  obtain ⟨v₄, S₄, r₄, h4D, h4E, h4k⟩ :=
    moveB_run (M := prog) (self := .skU false) (next := .walk false) (a := .D) (b := .E)
      (d := unitOf) (g := fun _ => Sym.cl) rfl (by decide)
      (cnt true e.2) (cnt Sym.cl e.2) (d.flatMap dEnt) v₃ S₃
      h3D (ent_found_aux1 e.2) (ent_found_aux4 d)
  have hlen : (cnt true e.2).length = e.2 := cnt_length true e.2
  rw [hlen] at r₄
  have h3E' : S₃ .E = (e.1.map Sym.bit).reverse ++ .lit true :: s.e := h3E
  have hE : S₄ .E = (dEnt e).reverse ++ s.e := by
    rw [h4E, h3E']
    have hX : (((cnt true e.2).map fun _ => Sym.cl).reverse) = cnt Sym.cl e.2 := by
      simp [cnt]
    rw [hX]
    simp [dEnt, cnt, List.reverse_replicate, List.append_assoc]
  have hS : S₄ = {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e}.stk := by
    funext k
    cases k <;> simp [h4D, hE, h4k, h3k]
  rw [hS] at r₄
  exact ⟨v₄, ((((r1.le le_rfl).trans r₂).trans (r₃.le le_rfl)).trans (r₄.le le_rfl)).mono (by omega)⟩


/-- **An entry after the match.** Once a match is recorded, an entry moves to `E` without a
comparison, in exactly `|w| + r + 3` steps for its name `w` and root `r`. -/
theorem ent_found (e : List Bool × ℕ) (d : List (List Bool × ℕ)) (s : MS) (v : Bool)
    (hD : s.d = dEnt e ++ d.flatMap dEnt) :
    ∃ v', Run prog (e.1.length + e.2 + 3) ⟨some (.walk true), v, s.stk⟩
      ⟨some (.walk true), v', {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e}.stk⟩ := by
  have hDcons : s.d = .lit true :: ((e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt) := by
    simp [hD, dEnt]
  have r1 : Run prog 1 ⟨some (.walk true), v, s.stk⟩
      ⟨some .skN, false, {s with
        d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt,
        e := .lit true :: s.e}.stk⟩ := by
    apply Run.single
    simp [prog, TM2.stepAux, hDcons]
  obtain ⟨v2, S2, r2, h2D, h2E, h2k⟩ :=
    moveB_run (M := prog) (self := .skN) (next := .skU true) (a := .D) (b := .E)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      e.1 (e.1.map Sym.bit) (cnt Sym.cl e.2 ++ d.flatMap dEnt) false
      {s with d := (e.1.map Sym.bit ++ cnt Sym.cl e.2) ++ d.flatMap dEnt, e := .lit true :: s.e}.stk
      (by simp [List.append_assoc])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map e.1)
      (ent_found_aux3 e.2 d)
  obtain ⟨v3, S3, r3, h3D, h3E, h3k⟩ :=
    moveB_run (M := prog) (self := .skU true) (next := .walk true) (a := .D) (b := .E)
      (d := unitOf) (g := fun _ => Sym.cl) rfl (by decide)
      (cnt true e.2) (cnt Sym.cl e.2) (d.flatMap dEnt) v2 S2
      h2D (ent_found_aux1 e.2) (ent_found_aux4 d)
  have hlen : (cnt true e.2).length = e.2 := cnt_length true e.2
  have hE : S3 .E = (dEnt e).reverse ++ s.e := by
    have h2E' : S2 .E = (e.1.map Sym.bit).reverse ++ .lit true :: s.e := h2E
    rw [h3E, h2E']
    have hX : (((cnt true e.2).map fun _ => Sym.cl).reverse) = cnt Sym.cl e.2 := by
      simp [cnt]
    rw [hX]
    simp [dEnt, cnt, List.reverse_replicate, List.append_assoc]
  have hS : S3 = {s with d := d.flatMap dEnt, e := (dEnt e).reverse ++ s.e}.stk := by
    funext k
    cases k <;> simp [h3D, hE, h3k, h2k]
  rw [hS] at r3
  exact ⟨v3, ((r1.trans r2).trans r3).of_eq (by omega)⟩


/-- **The rest of the walk after the match**: every remaining entry moves to `E`, and the walk
ends at `back true`. -/
theorem walkF_run : ∀ (d : List (List Bool × ℕ)) (s : MS) (v : Bool), s.d = d.flatMap dEnt →
    ∃ v', RunLe prog ((d.map fun e => e.1.length + e.2 + 3).sum + 1) ⟨some (.walk true), v, s.stk⟩
      ⟨some (.back true), v', {s with d := [], e := (d.flatMap dEnt).reverse ++ s.e}.stk⟩ := by
  intro d
  induction d with
  | nil =>
    intro s v hD
    have hD' : s.d = [] := by simpa using hD
    have r : Run prog 1 ⟨some (.walk true), v, s.stk⟩ ⟨some (.back true), true, s.stk⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, hD']
    have hS : ({s with d := [], e := (([] : List (List Bool × ℕ)).flatMap dEnt).reverse ++ s.e}.stk) =
        s.stk := by
      funext k
      cases k <;> simp [hD', List.flatMap]
    rw [hS]
    exact ⟨true, r.le (by simp)⟩
  | cons e d' ih =>
    intro s v hD
    have hDcons : s.d = dEnt e ++ d'.flatMap dEnt := by simpa using hD
    obtain ⟨v1, r1⟩ := ent_found e d' s v hDcons
    set s1 := {s with d := d'.flatMap dEnt, e := (dEnt e).reverse ++ s.e} with hs1
    obtain ⟨v2, r2⟩ := ih s1 v1 rfl
    have hflat : ((e :: d').flatMap dEnt) = dEnt e ++ d'.flatMap dEnt := rfl
    have hS : ({s1 with d := [], e := (d'.flatMap dEnt).reverse ++ s1.e}).stk = {s with d := [], e := ((e :: d').flatMap dEnt).reverse ++ s.e}.stk := by
      funext k
      cases k <;> simp [hs1, hflat, List.reverse_append, List.append_assoc]
    rw [hS] at r2
    have hB : (e.1.length + e.2 + 3) + ((d'.map fun e => e.1.length + e.2 + 3).sum + 1) =
        (((e :: d').map fun e => e.1.length + e.2 + 3).sum + 1) := by
      simp only [List.map_cons, List.sum_cons]
      omega
    have h := (r1.le le_rfl).trans r2
    rw [hB] at h
    exact ⟨v2, h⟩


/-! ### Blocks -/

/-- **Node `0`.** From the start label, with every counter `0` and the dictionary, walk, name and
polarity stacks empty, one step writes the constant-true node and reaches `cls` in the initial
emitter state. -/
theorem init_run (t : List Sym) (o0 : List Bool) (v : Bool) :
    ∃ v', Run prog 1 ⟨some .init, v, (MS.mk t o0 0 0 0 0 [] [] [] []).stk⟩
      ⟨some .cls, v', (enc eInit t o0).stk⟩ := by
  refine ⟨v, Run.single ?_⟩
  simp [prog, stepAux_pushList, TM2.stepAux, enc, eInit]
  funext k
  cases k <;> rfl

private theorem open_run_aux1 (s : ESt) (R : List Sym) (o0 : List Bool) (v : Bool) :
    Run prog 1 ⟨some .cls, v, (enc s (.cl :: R) o0).stk⟩
      ⟨some .opn, false, ({enc s (.cl :: R) o0 with t := R}).stk⟩ := by
  apply Run.single
  simp [prog, TM2.stepAux, enc]

private theorem open_run_aux2 (s : MS) (ys : List Bool) :
    update s.stk .O (ys ++ s.stk .O) = {s with o := ys ++ s.o}.stk := by
  simp

private theorem open_run_aux3 (s : MS) (n : ℕ) :
    update s.stk .H (cnt Sym.cl (n + 0)) = {s with h := n}.stk := by
  simpa using upd_H s n

private theorem open_run_aux4 (s : MS) :
    update s.stk .N ([Sym.cl].reverse ++ s.stk .N) = {s with n := s.n + 1}.stk := by
  have hN : s.stk K.N = cnt Sym.cl s.n := rfl
  rw [hN]
  have hrev : ([Sym.cl].reverse ++ cnt Sym.cl s.n) = cnt Sym.cl (s.n + 1) := by
    simp [cnt, List.replicate_succ]
  rw [hrev]
  simpa using upd_N s (s.n + 1)


/-- **Opening a clause.** From `cls`, with the clause marker on top of `T` and chain output `0`,
the machine writes the clause's constant-false node and reaches `lits` in the opened state,
within `2 n + 12` steps. -/
theorem open_run (s : ESt) (hs : s.o = 0) (R : List Sym) (o0 : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * s.n + 12) ⟨some .cls, v, (enc s (.cl :: R) o0).stk⟩
      ⟨some .lits, v', (enc (eOpen s) R o0).stk⟩ := by
  have r0 := open_run_aux1 s R o0 v
  have r1 := emitR_run (M := prog) (self := .opn) (next := .opnH) (k := .O)
    (ys := encodeRatNode (constNode false)) rfl false ({enc s (.cl :: R) o0 with t := R}).stk
  rw [open_run_aux2] at r1
  have r2 := copy_run (M := prog) (a := .N) (c := .H) (t := .W)
    (ua := Sym.cl) (uc := Sym.cl) (ut := Sym.cl)
    (l₁ := .opnH) (l₂ := .opnW) (next := .opnN)
    rfl rfl (by decide) (by decide) (by decide)
    s.n 0 false ({{enc s (.cl :: R) o0 with t := R} with
      o := encodeRatNode (constNode false) ++ ({enc s (.cl :: R) o0 with t := R}).o}).stk
    (by simp [enc, cnt]) (by simp [enc, hs]) rfl
  rw [open_run_aux3] at r2
  have r3 := emit_run (M := prog) (self := .opnN) (next := .lits) (k := .N)
    (xs := [Sym.cl]) rfl (Flag.tag false)
    ({{{enc s (.cl :: R) o0 with t := R} with
      o := encodeRatNode (constNode false) ++ ({enc s (.cl :: R) o0 with t := R}).o} with
      h := s.n}).stk
  rw [open_run_aux4] at r3
  have hfin : ({{{{enc s (.cl :: R) o0 with t := R} with
      o := encodeRatNode (constNode false) ++ ({enc s (.cl :: R) o0 with t := R}).o} with
      h := s.n} with
      n := ({{{enc s (.cl :: R) o0 with t := R} with
        o := encodeRatNode (constNode false) ++ ({enc s (.cl :: R) o0 with t := R}).o} with
        h := s.n}).n + 1}).stk = (enc (eOpen s) R o0).stk := by
    funext k
    cases k <;> simp [enc, eOpen, ESt.push, List.append_assoc]
  rw [hfin] at r3
  refine ⟨_, ((((r0.le le_rfl).trans (r1.le le_rfl)).trans (r2.le le_rfl)).trans
    (r3.le le_rfl)).mono ?_⟩
  omega


/-- **The dictionary walk.** With the dictionary `d` on `D`, the name `u` on `M` and the root
counter `0`, the machine walks from `walk false` to `back f`, `f` telling whether `u` is in the
dictionary, within `walkCost u d` steps: `D` is moved to `E` and the root counter holds the root
of the first entry with the name `u` (`List.lookup`), or `0` when there is none. -/
theorem walk_run (u : List Bool) : ∀ (d : List (List Bool × ℕ)) (m : MS) (v : Bool),
    m.d = d.flatMap dEnt → m.m = u.map Sym.bit → m.v = 0 →
    ∃ v', RunLe prog (walkCost u d) ⟨some (.walk false), v, m.stk⟩
      ⟨some (.back (d.lookup u).isSome), v', {m with
        d := [], e := (d.flatMap dEnt).reverse ++ m.e, v := (d.lookup u).getD 0}.stk⟩ := by
  intro d
  induction d with
  | nil =>
    intro m v hD hM hV
    have hD' : m.d = [] := by simpa using hD
    have r : Run prog 1 ⟨some (.walk false), v, m.stk⟩ ⟨some (.back false), true, m.stk⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, hD']
    have hL : (([] : List (List Bool × ℕ)).lookup u).isSome = false := by simp
    have hS : ({m with d := [], e := (([] : List (List Bool × ℕ)).flatMap dEnt).reverse ++ m.e, v := (([] : List (List Bool × ℕ)).lookup u).getD 0}.stk) = m.stk := by
      funext k
      cases k <;> simp [hD', hV, List.flatMap]
    rw [hL, hS]
    exact ⟨true, r.le (by simp [walkCost])⟩
  | cons e d ih =>
    intro m v hD hM hV
    by_cases hu : u = e.1
    · have hDcons : m.d = dEnt e ++ d.flatMap dEnt := by simpa using hD
      obtain ⟨v₁, r₁⟩ := ent_hit u e hu d m v hDcons hM hV
      set m₁ := {m with d := d.flatMap dEnt, e := (dEnt e).reverse ++ m.e, v := e.2} with hm₁
      obtain ⟨v₂, r₂⟩ := walkF_run d m₁ v₁ rfl
      have hlook : (e :: d).lookup u = some e.2 := by
        obtain ⟨e1, e2⟩ := e
        simp [hu]
      have hL : ((e :: d).lookup u).isSome = true := by simp [hlook]
      have hV' : ((e :: d).lookup u).getD 0 = e.2 := by simp [hlook]
      have hflat : ((e :: d).flatMap dEnt) = dEnt e ++ d.flatMap dEnt := rfl
      have hS : ({m₁ with d := [], e := (d.flatMap dEnt).reverse ++ m₁.e}).stk = {m with d := [], e := ((e :: d).flatMap dEnt).reverse ++ m.e, v := ((e :: d).lookup u).getD 0}.stk := by
        funext k
        cases k <;> simp [hm₁, hflat, hV', List.reverse_append, List.append_assoc]
      have hle : ∀ d : List (List Bool × ℕ), (d.map fun e => e.1.length + e.2 + 3).sum ≤
          (d.map fun e => 3 * u.length + e.1.length + 3 * e.2 + 8).sum := by
        intro d
        induction d with
        | nil => simp
        | cons e d ih => simp only [List.map_cons, List.sum_cons]; omega
      have hB : (3 * u.length + e.1.length + 3 * e.2 + 8) +
          ((d.map fun e => e.1.length + e.2 + 3).sum + 1) ≤ walkCost u (e :: d) := by
        simp only [walkCost, List.map_cons, List.sum_cons]
        have hled := hle d
        omega
      rw [hL]
      rw [hS] at r₂
      exact ⟨v₂, (r₁.trans r₂).mono hB⟩
    · have hDcons : m.d = dEnt e ++ d.flatMap dEnt := by simpa using hD
      obtain ⟨v₁, r₁⟩ := ent_miss u e hu d m v hDcons hM
      set m₁ := {m with d := d.flatMap dEnt, e := (dEnt e).reverse ++ m.e} with hm₁
      obtain ⟨v₂, r₂⟩ := ih m₁ v₁ rfl (by simp [hm₁, hM]) (by simp [hm₁, hV])
      have hlook : (e :: d).lookup u = d.lookup u := by
        obtain ⟨e1, e2⟩ := e
        have hbeq : (u == e1) = false := by simp [hu]
        simp [List.lookup_cons, hbeq]
      have hflat : ((e :: d).flatMap dEnt) = dEnt e ++ d.flatMap dEnt := rfl
      have hS : ({m₁ with d := [], e := (d.flatMap dEnt).reverse ++ m₁.e, v := (d.lookup u).getD 0}.stk) = {m with d := [], e := ((e :: d).flatMap dEnt).reverse ++ m.e, v := (d.lookup u).getD 0}.stk := by
        funext k
        cases k <;> simp [hm₁, hflat, List.reverse_append, List.append_assoc]
      have hB : (3 * u.length + e.1.length + e.2 + 6) + walkCost u d ≤ walkCost u (e :: d) := by
        simp only [walkCost, List.map_cons, List.sum_cons]
        omega
      rw [hlook]
      rw [hS] at r₂
      exact ⟨v₂, (r₁.trans r₂).mono hB⟩


/-- **Walk tokens**: name bits, markers and clause tokens, the symbols the walk moves. -/
def isTok : Sym → Bool
  | .bit _ | .lit _ | .cl => true
  | _ => false


/-- **A walked dictionary holds walk tokens.** -/
theorem isTok_flatMap_dEnt (d : List (List Bool × ℕ)) :
    ∀ x ∈ (d.flatMap dEnt).reverse, isTok x = true := by
  intro x hx
  simp only [List.mem_reverse, List.mem_flatMap, dEnt, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_replicate] at hx
  obtain ⟨e, -, hx⟩ := hx
  rcases hx with rfl | ⟨b, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem back_run_aux1 (f : Bool) (s : MS) (v : Bool) (h : s.e = []) :
    ∃ v', Run prog 1 ⟨some (.back f), v, s.stk⟩
      ⟨some (if f then .dropM else .root), v', s.stk⟩ := by
  refine ⟨true, ?_⟩
  apply Run.single
  simp [prog, TM2.stepAux, h]

theorem back_run_aux2 (f : Bool) (s : Sym) (L : List Sym) (hs : isTok s = true) (m : MS)
    (v : Bool) (h : m.e = s :: L) :
    ∃ v', Run prog 1 ⟨some (.back f), v, m.stk⟩
      ⟨some (.back f), v', {m with e := L, d := s :: m.d}.stk⟩ := by
  cases s with
  | bit b =>
    cases b
    · have hbeq : (Sym.bit false == Sym.bit true) = false := by decide
      refine ⟨false, ?_⟩
      apply Run.single
      simp [prog, TM2.stepAux, h, isLit, hbeq]
    · refine ⟨true, ?_⟩
      apply Run.single
      simp [prog, TM2.stepAux, h, isLit]
  | lit b =>
    cases b
    · have hbeq : (Sym.lit false == Sym.lit true) = false := by decide
      refine ⟨false, ?_⟩
      apply Run.single
      simp [prog, TM2.stepAux, h, isLit, hbeq]
    · refine ⟨true, ?_⟩
      apply Run.single
      simp [prog, TM2.stepAux, h, isLit]
  | cl =>
    refine ⟨true, ?_⟩
    apply Run.single
    simp [prog, TM2.stepAux, h]
  | val b => simp [isTok] at hs
  | dead => simp [isTok] at hs


/-- **Moving the walk side back.** From `back f`, with `E` holding walk tokens `L`, the machine
moves `E` back onto `D` in exactly `|L| + 1` steps and goes on to `dropM` if the name was found
and to `root` if not. -/
theorem back_run (f : Bool) : ∀ (L : List Sym), (∀ x ∈ L, isTok x = true) → ∀ (s : MS) (v : Bool),
    s.e = L → ∃ v', Run prog (L.length + 1) ⟨some (.back f), v, s.stk⟩
      ⟨some (if f then .dropM else .root), v', {s with e := [], d := L.reverse ++ s.d}.stk⟩ := by
  intro L
  induction L with
  | nil =>
    intro _ m v h
    have e : ({m with e := [], d := ([] : List Sym).reverse ++ m.d} : MS) = m := by
      obtain ⟨⟩ := m; simp only at h; subst h; rfl
    rw [e]
    exact back_run_aux1 f m v h
  | cons s L ih =>
    intro hL m v h
    obtain ⟨v₁, r₁⟩ := back_run_aux2 f s L (hL s (by simp)) m v h
    set m' := {m with e := L, d := s :: m.d} with hm'
    obtain ⟨v₂, r₂⟩ := ih (fun x hx => hL x (by simp [hx])) m' v₁ rfl
    have hEq : ({m' with e := [], d := L.reverse ++ m'.d} : MS) =
        {m with e := [], d := (s :: L).reverse ++ m.d} := by simp [hm']
    rw [hEq] at r₂
    exact ⟨v₂, (r₁.trans r₂).of_eq (by simp only [List.length_cons]; omega)⟩

theorem lpnm_run_aux1 (x : ℕ) (b : Bool) (R : List Sym) (s : MS) (v : Bool)
    (hT : s.t = Check.litRev (x, b) ++ R) :
    ∃ v', Run prog 1 ⟨some .lits, v, s.stk⟩ ⟨some .lp, v', s.stk⟩ := by
  refine ⟨true, ?_⟩
  apply Run.single
  simp [prog, TM2.stepAux, hT, Check.litRev, isLit]

theorem lpnm_run_aux2 (b : Bool) (T : List Sym) (s : MS) (v : Bool)
    (hT : s.t = .lit b :: T) :
    ∃ v', Run prog 1 ⟨some .lp, v, s.stk⟩
      ⟨some .nm, v', {s with t := T, p := .lit b :: s.p}.stk⟩ := by
  cases b
  · have hbeq : (Sym.lit false == Sym.lit true) = false := by decide
    refine ⟨false, ?_⟩
    apply Run.single
    simp [prog, TM2.stepAux, hT, hbeq]
  · refine ⟨true, ?_⟩
    apply Run.single
    simp [prog, TM2.stepAux, hT]


/-! ### Literals -/

/-- **Reading a literal's tokens.** From `lits`, with a literal's tokens on top of `T` above a
rest that does not start with a name bit and `M` empty, the machine reaches `walk false` in
exactly `|w| + 3` steps, `w` the literal's name: the polarity marker goes to `P` and the name to
`M`, least significant bit on top. -/
theorem lpnm_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) (s : MS)
    (v : Bool) (hT : s.t = Check.litRev l ++ R) (hM : s.m = []) :
    ∃ v', Run prog ((encodeNat l.1).length + 3) ⟨some .lits, v, s.stk⟩
      ⟨some (.walk false), v',
        {s with t := R, p := .lit l.2 :: s.p, m := (encodeNat l.1).map Sym.bit}.stk⟩ := by
  obtain ⟨x, b⟩ := l
  obtain ⟨v₁, r₁⟩ := lpnm_run_aux1 x b R s v hT
  have hT2 : s.t = .lit b :: (((encodeNat x).map Sym.bit).reverse ++ R) := hT
  obtain ⟨v₂, r₂⟩ := lpnm_run_aux2 b (((encodeNat x).map Sym.bit).reverse ++ R) s v₁ hT2
  obtain ⟨v₃, S₃, r₃, h3T, h3M, h3k⟩ :=
    moveB_run (M := prog) (self := .nm) (next := .walk false) (a := .T) (b := .M)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      (encodeNat x).reverse (((encodeNat x).map Sym.bit).reverse) R v₂
      {s with t := ((encodeNat x).map Sym.bit).reverse ++ R, p := .lit b :: s.p}.stk
      rfl (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_rev (encodeNat x)) hR
  have hS : S₃ = {s with t := R, p := .lit b :: s.p, m := (encodeNat x).map Sym.bit}.stk := by
    funext k; cases k <;> simp [h3T, h3M, h3k, hM]
  have hlen : (encodeNat (x, b).1).length = (encodeNat x).length := rfl
  rw [hS, List.length_reverse] at r₃
  exact ⟨v₃, ((r₁.trans r₂).trans r₃).of_eq (by omega)⟩

theorem put_run_aux1 (T : ∀ k, List (Γ k)) (n : ℕ) :
    addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] n T .D = cnt Sym.cl n ++ T .D := by
  rfl

theorem put_run_aux2 (T : ∀ k, List (Γ k)) (n : ℕ) :
    addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] n T .V = cnt Sym.cl n ++ T .V := by
  rfl

theorem put_run_aux3 (T : ∀ k, List (Γ k)) (n : ℕ) :
    addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] n T .W = cnt Sym.cl n ++ T .W := by
  rfl

theorem put_run_aux4 (T : ∀ k, List (Γ k)) (n : ℕ) (k : K)
    (h1 : k ≠ .D) (h2 : k ≠ .V) (h3 : k ≠ .W) :
    addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] n T k = T k := by
  apply addU_of_not_mem
  have hk : ([⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] : List (Σ k, Γ k)).keys =
      [.D, .V, .W] := rfl
  simp [hk, h1, h2, h3]

theorem put_run_aux5 (S : ∀ k, List (Γ k)) (v : Bool) :
    ∃ v', Run prog 1 ⟨some .putK, v, S⟩
      ⟨some .orC, v',
        update (update S .D (Sym.lit true :: S .D)) .N (Sym.cl :: S .N)⟩ := by
  refine ⟨v, ?_⟩
  apply Run.single
  simp [prog, TM2.stepAux]


/-- **A new root.** From `root`, with the name `u` on `M` and the root counter `0`, the machine
reaches `orC` in exactly `2 n + 2 |u| + 6` steps: a root node is written as node `n`, the entry
`(u, n)` goes on top of `D`, the root counter becomes `n` and the node counter advances. -/
theorem put_run (u : List Bool) (s : MS) (v : Bool) (hM : s.m = u.map Sym.bit) (hV : s.v = 0) :
    ∃ v', Run prog (2 * s.n + 2 * u.length + 6) ⟨some .root, v, s.stk⟩
      ⟨some .orC, v', {s with
        o := encodeRatNode rootNode ++ s.o, n := s.n + 1, v := s.n, m := [],
        d := dEnt (u, s.n) ++ s.d}.stk⟩ := by
  have r₁ := emitR_run (M := prog) (self := .root) (next := .putN) (k := .O)
    (ys := encodeRatNode rootNode) rfl v s.stk
  have r₂ := xfer_run (M := prog) (self := .putN) (next := .putW) (k := .N)
    (ps := [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩]) rfl
    (by show List.Nodup ([.D, .V, .W] : List K); decide) (by decide)
    Sym.cl s.n v (update s.stk .O (encodeRatNode rootNode ++ s.stk .O)) (by simp [cnt])
  have r₃ := xfer_run (M := prog) (self := .putW) (next := .putM) (k := .W)
    (ps := [⟨.N, Sym.cl⟩]) rfl (single_nodupKeys _) (by decide)
    Sym.cl s.n (Flag.tag false)
    (addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] s.n
      (update (update s.stk .O (encodeRatNode rootNode ++ s.stk .O)) .N []))
    (by simp [put_run_aux3])
  set s2 := {s with o := encodeRatNode rootNode ++ s.o, d := cnt Sym.cl s.n ++ s.d, v := s.n} with hs2
  have hS₃ : addU [⟨.N, Sym.cl⟩] s.n
      (update (addU [⟨.D, Sym.cl⟩, ⟨.V, Sym.cl⟩, ⟨.W, Sym.cl⟩] s.n
        (update (update s.stk .O (encodeRatNode rootNode ++ s.stk .O)) .N [])) .W []) =
      s2.stk := by
    funext k; cases k <;>
      simp [hs2, put_run_aux1, put_run_aux2, put_run_aux4,
        addU_single_self, addU_single_ne, hV, cnt]
  rw [hS₃] at r₃
  obtain ⟨v₄, S₄, r₄, h4M, h4X, h4k⟩ :=
    moveB_run (M := prog) (self := .putM) (next := .putX) (a := .M) (b := .X)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      u (u.map Sym.bit) [] (Flag.tag false) s2.stk (by simp [hs2, hM])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map u) rfl
  obtain ⟨v₅, S₅, r₅, h5X, h5D, h5k⟩ :=
    moveB_run (M := prog) (self := .putX) (next := .putK) (a := .X) (b := .D)
      (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      u.reverse ((u.map Sym.bit).reverse) [] v₄ S₄ (by simp [h4X])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_rev u) rfl
  obtain ⟨v₆, r₆⟩ := put_run_aux5 S₅ v₅
  have hS₆ : update (update S₅ .D (Sym.lit true :: S₅ .D)) .N (Sym.cl :: S₅ .N) =
      {s with o := encodeRatNode rootNode ++ s.o, n := s.n + 1, v := s.n, m := [], d := dEnt (u, s.n) ++ s.d}.stk := by
    funext k; cases k <;>
      simp [hs2, h4M, h4k, h5X, h5D, h5k, dEnt, cnt, List.replicate_succ]
  rw [hS₆] at r₆
  rw [List.length_reverse] at r₅
  exact ⟨_, (((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).of_eq (by omega)⟩


/-- **A recorded name is discarded.** From `dropM`, with the name `u` on `M`, the machine reaches
`orC` in exactly `2 |u| + 2` steps with `M` emptied. -/
theorem drop_run (u : List Bool) (s : MS) (v : Bool) (hM : s.m = u.map Sym.bit) :
    ∃ v', Run prog (2 * u.length + 2) ⟨some .dropM, v, s.stk⟩
      ⟨some .orC, v', {s with m := []}.stk⟩ := by
  obtain ⟨v₁, S₁, r₁, h1M, h1Y, h1k⟩ :=
    moveB_run (M := prog) (self := .dropM) (next := .dropY) (a := .M) (b := .Y)
      (d := Sym.bit?) (g := fun _ => Sym.cl) rfl (by decide)
      u (u.map Sym.bit) [] v s.stk (by simp [hM])
      (Cslib.Complexity.SatVerifier.Lookup.isBitBlock_map u) rfl
  have hY : S₁ .Y = cnt Sym.cl u.length := by simp [h1Y, cnt, List.reverse_replicate]
  have r₂ := xfer_run (M := prog) (self := .dropY) (next := .orC) (k := .Y) (ps := [])
    rfl List.nodupKeys_nil (by simp) Sym.cl u.length v₁ S₁ hY
  have hS : addU [] u.length (update S₁ .Y []) = {s with m := []}.stk := by
    funext k; cases k <;> simp [addU, h1M, h1k]
  rw [hS] at r₂
  exact ⟨_, (r₁.trans r₂).of_eq (by omega)⟩

private theorem lit_run_sum_le (α : Type _) (l : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ l, f x ≤ C) : (l.map f).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have h1 : f hd ≤ C := h _ (by simp)
    have h2 : ∀ x ∈ tl, f x ≤ C := fun x hx => h x (by simp [List.mem_cons, hx])
    have ih' := ih h2
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem lit_run_mem_of_lookup (d : List (List Bool × ℕ)) (u : List Bool) (r : ℕ)
    (h : d.lookup u = some r) : (u, r) ∈ d := by
  induction d with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨e1, e2⟩ := hd
    cases heq : (u == e1)
    · simp only [List.lookup_cons, heq] at h
      exact List.mem_cons.mpr (Or.inr (ih h))
    · simp only [List.lookup_cons, heq] at h
      have hue : u = e1 := beq_iff_eq.mp heq
      have hr : e2 = r := by simpa using h
      simp [hue, hr]

private theorem lit_run_lookup_le (Lb : ℕ) (s : ESt) (u : List Bool) (r : ℕ)
    (hb : Bnd Lb s) (h : s.dict.lookup u = some r) : r ≤ s.n := by
  obtain ⟨-, -, -, -, hmem⟩ := hb
  have hm := lit_run_mem_of_lookup s.dict u r h
  exact (hmem (u, r) hm).2

private theorem lit_run_walk_le (Lb : ℕ) (u : List Bool) (s : ESt)
    (hu : u.length ≤ Lb) (hb : Bnd Lb s) :
    walkCost u s.dict ≤ Lb * (10 * Lb + 11) + 1 := by
  obtain ⟨hn, -, -, hlen, hmem⟩ := hb
  have hterm : ∀ e ∈ s.dict, 3 * u.length + e.1.length + 3 * e.2 + 8 ≤ 10 * Lb + 11 := by
    intro e he
    obtain ⟨he1, he2⟩ := hmem e he
    omega
  have hsum := lit_run_sum_le _ s.dict
    (fun e => 3 * u.length + e.1.length + 3 * e.2 + 8) (10 * Lb + 11) hterm
  have hmul : s.dict.length * (10 * Lb + 11) ≤ Lb * (10 * Lb + 11) := by gcongr
  simp only [walkCost]
  omega

private theorem lit_run_back_le (Lb : ℕ) (s : ESt) (hb : Bnd Lb s) :
    ((s.dict.flatMap dEnt).reverse).length + 1 ≤ Lb * (3 * Lb + 2) + 1 := by
  obtain ⟨hn, -, -, hlen, hmem⟩ := hb
  have hlen_flat : (s.dict.flatMap dEnt).length =
      (s.dict.map fun e => (dEnt e).length).sum := by
    rw [List.length_flatMap]
  have hterm : ∀ e ∈ s.dict, (dEnt e).length ≤ 3 * Lb + 2 := by
    intro e he
    obtain ⟨he1, he2⟩ := hmem e he
    simp only [dEnt, List.length_cons, List.length_append, List.length_map, cnt_length]
    omega
  have hsum := lit_run_sum_le _ s.dict (fun e => (dEnt e).length) (3 * Lb + 2) hterm
  have hmul : s.dict.length * (3 * Lb + 2) ≤ Lb * (3 * Lb + 2) := by gcongr
  rw [List.length_reverse, hlen_flat]
  omega

private theorem lit_run_aux_found (_Lb : ℕ) (l : ℕ × Bool) (R : List Sym) (s : ESt)
    (o0 : List Bool) (v : Bool) (r : ℕ) (h : s.dict.lookup (encodeNat l.1) = some r)
    (m : MS) (hmt : m.t = R) (hmo : m.o = s.out ++ o0) (hmn : m.n = s.n)
    (hma : m.a = s.acc) (hmh : m.h = s.o) (hmv : m.v = r)
    (hmd : m.d = s.dict.flatMap dEnt) (hme : m.e = [])
    (hmm : m.m = (encodeNat l.1).map Sym.bit) (hmp : m.p = [.lit l.2]) :
    ∃ v', RunLe prog ((2 * (encodeNat l.1).length + 2) + (2 * r + 2 * s.o + 8) +
      (s.o + 2 * s.n + r + 5)) ⟨some .dropM, v, m.stk⟩
      ⟨some .lits, v', (enc (eLit l.2 (encodeNat l.1) s) R o0).stk⟩ := by
  obtain ⟨v₁, r₁⟩ := drop_run (encodeNat l.1) m v hmm
  set m4 := { m with m := [] } with hm4
  have hp4 : m4.p = [.lit l.2] := by simp [hm4, hmp]
  obtain ⟨v₂, r₂⟩ := orNode_run l.2 m4 v₁ hp4
  set m5 := { m4 with p := [], o := encodeRatNode (orNode m4.h m4.v l.2) ++ m4.o } with hm5
  obtain ⟨v₃, r₃⟩ := orReset_run m5 v₂
  set m6 := { m5 with h := m5.n, n := m5.n + 1, v := 0 } with hm6
  have hfin : m6.stk = (enc (eLit l.2 (encodeNat l.1) s) R o0).stk := by
    rw [eLit_some l.2 _ _ _ h]
    funext k; cases k <;> simp [hm6, hm5, hm4, hmt, hmo, hmn, hma, hmh, hmv, hmd,
      hme, hmp, enc, List.append_assoc]
  rw [hfin] at r₃
  have hle : (2 * (encodeNat l.1).length + 2) + (2 * m4.v + 2 * m4.h + 8) +
      (m5.h + 2 * m5.n + m5.v + 5) ≤ (2 * (encodeNat l.1).length + 2) +
      (2 * r + 2 * s.o + 8) + (s.o + 2 * s.n + r + 5) := by
    have hv4 : m4.v = r := by simp [hm4, hmv]
    have hh4 : m4.h = s.o := by simp [hm4, hmh]
    have hh5 : m5.h = s.o := by simp [hm5, hm4, hmh]
    have hn5 : m5.n = s.n := by simp [hm5, hm4, hmn]
    have hv5 : m5.v = r := by simp [hm5, hm4, hmv]
    omega
  exact ⟨v₃, (((r₁.le le_rfl).trans (r₂.le le_rfl)).trans (r₃.le le_rfl)).mono hle⟩

private theorem lit_run_aux_new (_Lb : ℕ) (l : ℕ × Bool) (R : List Sym) (s : ESt)
    (o0 : List Bool) (v : Bool) (h : s.dict.lookup (encodeNat l.1) = none)
    (m : MS) (hmt : m.t = R) (hmo : m.o = s.out ++ o0) (hmn : m.n = s.n)
    (hma : m.a = s.acc) (hmh : m.h = s.o) (hmv : m.v = 0)
    (hmd : m.d = s.dict.flatMap dEnt) (hme : m.e = [])
    (hmm : m.m = (encodeNat l.1).map Sym.bit) (hmp : m.p = [.lit l.2]) :
    ∃ v', RunLe prog ((2 * s.n + 2 * (encodeNat l.1).length + 6) + (2 * s.n + 2 * s.o + 8) +
      (s.o + 2 * (s.n + 1) + s.n + 5)) ⟨some .root, v, m.stk⟩
      ⟨some .lits, v', (enc (eLit l.2 (encodeNat l.1) s) R o0).stk⟩ := by
  obtain ⟨v₁, r₁⟩ := put_run (encodeNat l.1) m v hmm hmv
  set m4 := { m with o := encodeRatNode rootNode ++ m.o, n := m.n + 1, v := m.n, m := [], d := dEnt (encodeNat l.1, m.n) ++ m.d } with hm4
  have hp4 : m4.p = [.lit l.2] := by simp [hm4, hmp]
  obtain ⟨v₂, r₂⟩ := orNode_run l.2 m4 v₁ hp4
  set m5 := { m4 with p := [], o := encodeRatNode (orNode m4.h m4.v l.2) ++ m4.o } with hm5
  obtain ⟨v₃, r₃⟩ := orReset_run m5 v₂
  set m6 := { m5 with h := m5.n, n := m5.n + 1, v := 0 } with hm6
  have hn2 : s.n + 1 + 1 = s.n + 2 := by omega
  have hfin : m6.stk = (enc (eLit l.2 (encodeNat l.1) s) R o0).stk := by
    rw [eLit_none l.2 _ _ h]
    funext k; cases k <;> simp [hm6, hm5, hm4, hmt, hmo, hmn, hma, hmh, hmd,
      hme, hmp, enc, List.append_assoc, List.flatMap_cons, hn2]
  rw [hfin] at r₃
  have hle : (2 * m.n + 2 * (encodeNat l.1).length + 6) + (2 * m4.v + 2 * m4.h + 8) +
      (m5.h + 2 * m5.n + m5.v + 5) ≤ (2 * s.n + 2 * (encodeNat l.1).length + 6) +
      (2 * s.n + 2 * s.o + 8) + (s.o + 2 * (s.n + 1) + s.n + 5) := by
    have hv4 : m4.v = s.n := by simp [hm4, hmn]
    have hh4 : m4.h = s.o := by simp [hm4, hmh]
    have hh5 : m5.h = s.o := by simp [hm5, hm4, hmh]
    have hn5 : m5.n = s.n + 1 := by simp [hm5, hm4, hmn]
    have hv5 : m5.v = s.n := by simp [hm5, hm4, hmn]
    omega
  exact ⟨v₃, (((r₁.le le_rfl).trans (r₂.le le_rfl)).trans (r₃.le le_rfl)).mono hle⟩


/-- **One literal.** From `lits`, with a literal's tokens on top of `T` above a rest that does
not start with a name bit, in a state within the literal-boundary bounds for `Lb` and with a name
of at most `Lb` bits, the machine adds the literal (`eLit`) and returns to `lits` within
`litCost Lb` steps. -/
theorem lit_run (Lb : ℕ) (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (s : ESt) (hb : Bnd Lb s) (hx : (encodeNat l.1).length ≤ Lb) (o0 : List Bool) (v : Bool) :
    ∃ v', RunLe prog (litCost Lb) ⟨some .lits, v, (enc s (Check.litRev l ++ R) o0).stk⟩
      ⟨some .lits, v', (enc (eLit l.2 (encodeNat l.1) s) R o0).stk⟩ := by
  set s0 := enc s (Check.litRev l ++ R) o0 with hs0
  have hT0 : s0.t = Check.litRev l ++ R := by simp [hs0, enc]
  have hM0 : s0.m = [] := by simp [hs0, enc]
  obtain ⟨v₁, r₁⟩ := lpnm_run l R hR s0 v hT0 hM0
  set m1 := {s0 with t := R, p := .lit l.2 :: s0.p, m := (encodeNat l.1).map Sym.bit} with hm1
  have hm1d : m1.d = s.dict.flatMap dEnt := by simp [hm1, hs0, enc]
  have hm1m : m1.m = (encodeNat l.1).map Sym.bit := by simp [hm1]
  have hm1v : m1.v = 0 := by simp [hm1, hs0, enc]
  have hm1e : m1.e = [] := by simp [hm1, hs0, enc]
  obtain ⟨v₂, r₂⟩ := walk_run (encodeNat l.1) s.dict m1 v₁ hm1d hm1m hm1v
  set m2 := {m1 with d := [], e := (s.dict.flatMap dEnt).reverse ++ m1.e, v := (s.dict.lookup (encodeNat l.1)).getD 0} with hm2
  have hm2d : m2.d = [] := by simp [hm2]
  have hm2e : m2.e = (s.dict.flatMap dEnt).reverse := by simp [hm2, hm1e]
  have hTok : ∀ x ∈ m2.e, isTok x = true := by
    rw [hm2e]
    exact isTok_flatMap_dEnt s.dict
  obtain ⟨v₃, r₃⟩ := back_run ((s.dict.lookup (encodeNat l.1)).isSome) m2.e hTok m2 v₂ rfl
  set m3 := {m2 with e := [], d := m2.e.reverse ++ m2.d} with hm3
  have hm3t : m3.t = R := by simp [hm3, hm2, hm1]
  have hm3o : m3.o = s.out ++ o0 := by simp [hm3, hm2, hm1, hs0, enc]
  have hm3n : m3.n = s.n := by simp [hm3, hm2, hm1, hs0, enc]
  have hm3a : m3.a = s.acc := by simp [hm3, hm2, hm1, hs0, enc]
  have hm3h : m3.h = s.o := by simp [hm3, hm2, hm1, hs0, enc]
  have hm3e : m3.e = [] := by simp [hm3]
  have hm3m : m3.m = (encodeNat l.1).map Sym.bit := by simp [hm3, hm2, hm1]
  have hm3p : m3.p = [.lit l.2] := by simp [hm3, hm2, hm1, hs0, enc]
  have hm3d : m3.d = s.dict.flatMap dEnt := by simp [hm3, hm2e, hm2d]
  have hLen : m2.e.length = ((s.dict.flatMap dEnt).reverse).length := by rw [hm2e]
  have hw := lit_run_walk_le Lb (encodeNat l.1) s hx hb
  have hbk := lit_run_back_le Lb s hb
  obtain ⟨hn, ha, ho, hlen, hmem⟩ := hb
  cases h : s.dict.lookup (encodeNat l.1) with
  | some r =>
    simp [h] at r₂ r₃
    have hm3v : m3.v = r := by simp [hm3, hm2, h]
    have hr := lit_run_lookup_le Lb s (encodeNat l.1) r ⟨hn, ha, ho, hlen, hmem⟩ h
    obtain ⟨v₄, r₄⟩ := lit_run_aux_found Lb l R s o0 v₃ r h m3 hm3t hm3o hm3n hm3a hm3h hm3v hm3d hm3e hm3m hm3p
    refine ⟨v₄, ((((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)).trans r₄).mono ?_⟩
    simp only [litCost]
    nlinarith [hw, hbk, hr, hx, hn, ho, hLen]
  | none =>
    simp [h] at r₂ r₃
    have hm3v : m3.v = 0 := by simp [hm3, hm2, h]
    obtain ⟨v₄, r₄⟩ := lit_run_aux_new Lb l R s o0 v₃ h m3 hm3t hm3o hm3n hm3a hm3h hm3v hm3d hm3e hm3m hm3p
    refine ⟨v₄, ((((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)).trans r₄).mono ?_⟩
    simp only [litCost]
    nlinarith [hw, hbk, hx, hn, ho, hLen]

private theorem lits_run_aux1 (Lb : ℕ) (ψ : CNF) (o0 : List Bool) :
    ∀ (Ls : CNFClause) (R : List Sym), R.head?.bind Sym.bit? = none → ∀ (v : Bool),
    (toks (Ls :: ψ)).length ≤ Lb →
    ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length * litCost Lb)
      ⟨some .lits, v, (enc (eOpen (eFormula ψ)) (Ls.reverse.flatMap Check.litRev ++ R) o0).stk⟩
      ⟨some .lits, v', (enc (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s)
        (eOpen (eFormula ψ))) R o0).stk⟩ := by
  intro Ls
  induction Ls with
  | nil =>
    intro R hR v h
    exact ⟨v, RunLe.refl _ _⟩
  | cons l Ls ih =>
    intro R hR v h
    have hLs : (toks (Ls :: ψ)).length ≤ Lb := le_trans (toks_tail_le l Ls ψ) h
    have hRmid : (Check.litRev l ++ R).head?.bind Sym.bit? = none := by
      simp [Check.litRev, Sym.bit?]
    obtain ⟨v₁, r₁⟩ := ih (Check.litRev l ++ R) hRmid v hLs
    have hbQ : Bnd Lb
        (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))) :=
      bnd_preClose Lb Ls ψ hLs
    have hx : (encodeNat l.1).length ≤ Lb := by
      have hle : (encodeNat l.1).length + 1 ≤ (toks ((l :: Ls) :: ψ)).length := by
        simp only [toks, clauseToks, litToks, List.flatMap_cons, List.length_append,
          List.length_cons, List.length_map, List.length_nil]
        omega
      omega
    obtain ⟨v₂, r₂⟩ := lit_run Lb l R hR _ hbQ hx o0 v₁
    have htape : (l :: Ls).reverse.flatMap Check.litRev ++ R =
        Ls.reverse.flatMap Check.litRev ++ (Check.litRev l ++ R) := by
      rw [List.reverse_cons, List.flatMap_append]
      simp [List.append_assoc]
    have hfold : (l :: Ls).reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s)
        (eOpen (eFormula ψ)) =
        eLit l.2 (encodeNat l.1)
          (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))) := by
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : ((l :: Ls).flatMap Check.litRev).length =
        (Ls.flatMap Check.litRev).length + (Check.litRev l).length := by
      simp [List.flatMap_cons, List.length_append, Nat.add_comm]
    have hlen1 : 1 ≤ (Check.litRev l).length := by
      simp [Check.litRev]
    have hcost : litCost Lb ≤ (Check.litRev l).length * litCost Lb := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen1
      rw [hk, Nat.add_mul, Nat.one_mul]
      exact Nat.le_add_right _ _
    rw [htape, hfold]
    refine ⟨v₂, (r₁.trans r₂).mono ?_⟩
    rw [hlen, Nat.add_mul]
    exact Nat.add_le_add_left hcost _


/-- **The literals of a clause.** In a clause `Ls` over the suffix `ψ`, from the opened state with
the literals' tokens on top of `T`, the machine adds the literals from the last one and returns
to `lits`, within `litCost Lb` steps per token, for every `Lb` at least `|toks (Ls :: ψ)|`. -/
theorem lits_run (Lb : ℕ) (ψ : CNF) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (o0 : List Bool) : ∀ (Ls : CNFClause) (v : Bool), (toks (Ls :: ψ)).length ≤ Lb →
    ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length * litCost Lb)
      ⟨some .lits, v, (enc (eOpen (eFormula ψ)) (Ls.reverse.flatMap Check.litRev ++ R) o0).stk⟩
      ⟨some .lits, v', (enc (Ls.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s)
        (eOpen (eFormula ψ))) R o0).stk⟩ := by
  intro Ls v h
  exact lits_run_aux1 Lb ψ o0 Ls R hR v h

theorem close_run_aux1 (s : ESt) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (o0 : List Bool) (v : Bool) :
    Run prog 1 ⟨some .lits, v, (enc s R o0).stk⟩
      ⟨some (.pre .andH), false, (enc s R o0).stk⟩ := by
  have hlit : isLit R.head? = false := by
    rcases hR with rfl | hR
    · rfl
    · rw [hR]; rfl
  apply Run.single
  simp [prog, TM2.stepAux, enc, hlit]


/-- **Closing a clause.** From `lits`, with `T` empty or a clause marker on top, the machine
writes the clause's AND node and reaches `cls` in the closed state, within
`4 (n + acc + o) + 100` steps. -/
theorem close_run (s : ESt) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl) (o0 : List Bool)
    (v : Bool) : ∃ v', RunLe prog (4 * (s.n + s.acc + s.o) + 100)
      ⟨some .lits, v, (enc s R o0).stk⟩ ⟨some .cls, v', (enc (eClose s) R o0).stk⟩ := by
  have r0 := close_run_aux1 s R hR o0 v
  obtain ⟨v1, r1⟩ := andNode_run (enc s R o0) false
  have hh : (enc s R o0).h = s.o := rfl
  have ha : (enc s R o0).a = s.acc := rfl
  have ho : (enc s R o0).o = s.out ++ o0 := rfl
  rw [hh, ha, ho] at r1
  set m := {enc s R o0 with o := encodeRatNode (andNode s.acc s.o) ++ (s.out ++ o0)} with hm
  obtain ⟨v2, r2⟩ := andReset_run m v1
  have hma : m.a = s.acc := by simp [hm, enc]
  have hmn : m.n = s.n := by simp [hm, enc]
  have hmh : m.h = s.o := by simp [hm, enc]
  rw [hma, hmn, hmh] at r2
  have hfin : ({m with a := s.n, h := 0, n := s.n + 1}).stk = (enc (eClose s) R o0).stk := by
    funext k
    cases k <;> simp [hm, enc, eClose, ESt.push, List.append_assoc]
  rw [hfin] at r2
  refine ⟨v2, (((r0.le le_rfl).trans (r1.le le_rfl)).trans (r2.le le_rfl)).mono ?_⟩
  omega


/-- **One clause.** From `cls`, with a clause's tokens on top of `T` above a rest that is empty
or starts with a clause marker, the machine adds the clause to the block emission of the suffix
and returns to `cls`, within `budget Lb` steps per token, for every `Lb` at least the token count
of the formula. -/
theorem clause_run (Lb : ℕ) (C : CNFClause) (ψ : CNF) (R : List Sym)
    (hR : R = [] ∨ R.head? = some .cl) (o0 : List Bool) (v : Bool)
    (hb : (toks (C :: ψ)).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * budget Lb)
      ⟨some .cls, v, (enc (eFormula ψ) (Check.clRev C ++ R) o0).stk⟩
      ⟨some .cls, v', (enc (eFormula (C :: ψ)) R o0).stk⟩ := by
  have hR' : R.head?.bind Sym.bit? = none := by
    rcases hR with rfl | hR
    · rfl
    · rw [hR]; rfl
  have hψ : (toks ψ).length ≤ Lb := by
    have hle : (toks ψ).length ≤ (toks (C :: ψ)).length := by
      simp only [toks, List.flatMap_cons, List.length_append]
      omega
    omega
  have hnψ : (eFormula ψ).n ≤ 2 * Lb + 1 := by
    have h := eFormula_n_le ψ
    omega
  have hflat : (C.reverse.flatMap Check.litRev).length = (C.flatMap Check.litRev).length := by
    rw [List.length_flatMap, List.length_flatMap, List.map_reverse, List.sum_reverse]
  have hlen1 : (Check.clRev C).length = (C.flatMap Check.litRev).length + 1 := by
    rw [show Check.clRev C = .cl :: C.reverse.flatMap Check.litRev from rfl,
      List.length_cons, hflat]
  have hcl : Check.clRev C ++ R = .cl :: (C.reverse.flatMap Check.litRev ++ R) := rfl
  rw [hcl]
  obtain ⟨v₁, r₁⟩ := open_run (eFormula ψ) (eFormula_o ψ)
    (C.reverse.flatMap Check.litRev ++ R) o0 v
  obtain ⟨v₂, r₂⟩ := lits_run Lb ψ R hR' o0 C v₁ hb
  obtain ⟨v₃, r₃⟩ := close_run
    (C.reverse.foldl (fun s l => eLit l.2 (encodeNat l.1) s) (eOpen (eFormula ψ))) R hR o0 v₂
  rw [preClose_eq C ψ] at r₃
  refine ⟨v₃, ((r₁.trans r₂).trans r₃).mono ?_⟩
  have h1 := preClose_n_le C ψ
  have h2 := preClose_acc_lt C ψ
  have h3 := preClose_o_lt C ψ
  rw [hlen1]
  simp only [budget, litCost]
  nlinarith [mul_nonneg (Nat.zero_le (C.flatMap Check.litRev).length)
    (Nat.zero_le ((Lb + 1) ^ 2)),
    mul_nonneg (Nat.zero_le Lb) (Nat.zero_le Lb), h1, h2, h3, hb, hnψ]


/-- **All clauses.** From `cls` in the initial emitter state, with a formula's clause tokens on
top of `T`, the machine reaches `cls` in the state of the block emission of the formula, within
`budget Lb` steps per token. -/
theorem formula_run (Lb : ℕ) (o0 : List Bool) : ∀ (φ : CNF) (R : List Sym),
    (R = [] ∨ R.head? = some .cl) → ∀ v, (toks φ).length ≤ Lb →
    ∃ v', RunLe prog ((φ.reverse.flatMap Check.clRev).length * budget Lb)
      ⟨some .cls, v, (enc eInit (φ.reverse.flatMap Check.clRev ++ R) o0).stk⟩
      ⟨some .cls, v', (enc (eFormula φ) R o0).stk⟩ := by
  intro φ
  induction φ with
  | nil =>
    intro R hR v h
    exact ⟨v, RunLe.refl _ _⟩
  | cons C φ ih =>
    intro R hR v h
    have hφ : (toks φ).length ≤ Lb := by
      have hle : (toks φ).length ≤ (toks (C :: φ)).length := by
        simp only [toks, List.flatMap_cons, List.length_append]
        omega
      omega
    have hR' : Check.clRev C ++ R = [] ∨ (Check.clRev C ++ R).head? = some .cl :=
      Or.inr rfl
    obtain ⟨v₁, r₁⟩ := ih (Check.clRev C ++ R) hR' v hφ
    obtain ⟨v₂, r₂⟩ := clause_run Lb C φ R hR o0 v₁ h
    have htape : ((C :: φ).reverse.flatMap Check.clRev ++ R) =
        (φ.reverse.flatMap Check.clRev ++ (Check.clRev C ++ R)) := by
      rw [List.reverse_cons, List.flatMap_append]
      simp [List.append_assoc]
    rw [htape]
    refine ⟨v₂, (r₁.trans r₂).mono ?_⟩
    have hlen : ((C :: φ).reverse.flatMap Check.clRev).length =
        (φ.reverse.flatMap Check.clRev).length + (Check.clRev C).length := by
      rw [List.reverse_cons, List.flatMap_append, List.length_append]
      simp
    rw [hlen, Nat.add_mul]

theorem fin_run_aux1 (s : ESt) (o0 : List Bool) (v : Bool) :
    Run prog 1 ⟨some .cls, v, (enc s [] o0).stk⟩
      ⟨some (.pre .fin), true, (enc s [] o0).stk⟩ := by
  apply Run.single
  simp [prog, TM2.stepAux, enc]


/-- **The end.** From `cls` with `T` empty, the machine pushes the node count in unary and halts
at `done`, in exactly `2 n + 4` steps. -/
theorem fin_run (s : ESt) (o0 : List Bool) (v : Bool) :
    ∃ v' S', Run prog (2 * s.n + 4) ⟨some .cls, v, (enc s [] o0).stk⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = unary s.n ++ s.out ++ o0 := by
  have r0 := fin_run_aux1 s o0 v
  obtain ⟨v1, r1⟩ := site_run .fin (enc s [] o0) true
  have hval : (enc s [] o0).val (Site.src .fin) = s.n := rfl
  rw [hval] at r1
  have hnxt : Site.nxt .fin = .done := rfl
  rw [hnxt] at r1
  have hO : ({enc s [] o0 with o := atom (enc s [] o0) .fin ++ (enc s [] o0).o}.stk) .O
      = unary s.n ++ s.out ++ o0 := by
    simp [atom, Site.top, Site.src, MS.val, enc, unary, cnt, List.append_assoc]
  refine ⟨v1, {enc s [] o0 with o := atom (enc s [] o0) .fin ++ (enc s [] o0).o}.stk,
    (r0.trans r1).of_eq (by omega), hO⟩


/-! ### The emitter -/

/-- **Correctness and step bound of the Cooper emitter.** Started at its start label with the
token stack holding the tokens of a CNF formula `φ` in reverse, the output stack holding `o` and
every other stack empty, the machine reaches `done` within `500 (|toks φ| + 1)⁴` steps with the
code of Cooper's network of `φ` above `o` on the output stack. -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (500 * ((toks φ).length + 1) ^ 4) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = encodeRatNet (cooperNet φ) ++ o := by
  have hSt : St = (MS.mk (toks φ).reverse o 0 0 0 0 [] [] [] []).stk := by
    funext k
    cases k <;> simp <;> first
      | exact hT
      | exact hO
      | exact h0 _ (by decide) (by decide)
  rw [hSt]
  obtain ⟨v₁, r₁⟩ := init_run (toks φ).reverse o v
  have htoks : (toks φ).reverse = φ.reverse.flatMap Check.clRev ++ [] := by
    rw [Check.toks_reverse, List.append_nil]
  obtain ⟨v₂, r₂⟩ := formula_run (toks φ).length o φ [] (Or.inl rfl) v₁ le_rfl
  rw [← htoks] at r₂
  obtain ⟨v₃, S', r₃, hO'⟩ := fin_run (eFormula φ) o v₂
  refine ⟨v₃, S', (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)).mono ?_, ?_⟩
  · have hL : (φ.reverse.flatMap Check.clRev).length = (toks φ).length := by
      rw [← Check.toks_reverse, List.length_reverse]
    have hn := eFormula_n_le φ
    rw [hL]
    simp only [budget]
    nlinarith [mul_nonneg (Nat.zero_le (toks φ).length) (Nat.zero_le (toks φ).length),
      mul_nonneg (Nat.zero_le ((toks φ).length * (toks φ).length))
        (Nat.zero_le (toks φ).length),
      mul_nonneg (Nat.zero_le ((toks φ).length * (toks φ).length))
        (Nat.zero_le ((toks φ).length * (toks φ).length)),
      mul_nonneg (Nat.zero_le (((toks φ).length + 1) ^ 2))
        (Nat.zero_le ((toks φ).length * (toks φ).length + (toks φ).length + 1)), hn]
  · rw [hO', encodeRatNet_cooperNet_eq, List.append_assoc]


end Cslib.Complexity.Karp.EmitCooper


namespace Cslib.Complexity.Karp


open Cslib.CookLevin Cslib.Logic.LegacyPL MetaMathlibExt.ComplexityTheory Cslib.Complexity.Cooper


/-- The alphabets of the Cooper emitter are finite. -/
instance EmitCooper.instFintypeΓ (k : EmitCooper.K) : Fintype (EmitCooper.Γ k) := by
  cases k <;> infer_instance


/-- **The Cooper emitter.** The emitter whose stacks, alphabets, labels, program and start label
are those of the Cooper emitter machine, which exits at the machine's label `done`, reads the
tokens of a CNF formula from stack `T` and writes its output bits on stack `O` (both symbol maps
the identity), and has step bound `B(n) = 500 (n + 1)⁴` for `n` tokens. Its output for a CNF
formula `φ` is the code of Cooper's network of `φ`, and for undecodable input the code of the
fixed no-instance `noBN`. -/
abbrev emitCooper : Emitter where
  K := EmitCooper.K
  Γ := EmitCooper.Γ
  L := EmitCooper.Lab
  prog := EmitCooper.prog
  start := EmitCooper.start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .T
  cO := .O
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g φ := encodeRatNet (cooperNet φ)
  noOut := encodeRatNet noBN
  B n := 500 * (n + 1) ^ 4
  B_mono a b h := by dsimp only; gcongr
  run φ v St hT hO h0 := by
    obtain ⟨v', S', r, h⟩ := EmitCooper.run φ [] v St (by simpa using hT) hO h0
    exact ⟨v', S', r, by simpa using h⟩


/-- **The Cooper emitter computes Cooper's reduction map**: tokenizing a bit string and running
the Cooper emitter on its token stack gives `reduceBN`, undecodable input included. -/
theorem out_emitCooper (x : List Bool) : TokThen.out emitCooper x = reduceBN x := by
  unfold TokThen.out reduceBN
  cases decodeCNF x <;> rfl


/-- **Cooper's reduction is polynomial-time.** The map on bit strings that sends the code of a
CNF formula `φ` to the code of Cooper's network of `φ`, and every other bit string to the code of
the fixed no-instance `noBN`, is computable in polynomial time. -/
theorem isPolyTime_reduceBN : IsPolyTime reduceBN := by
  have h : reduceBN = TokThen.out emitCooper := (funext out_emitCooper).symm
  rw [h]
  refine TokThen.isPolyTime_out emitCooper
    [EmitCooper.K.T, EmitCooper.K.O, EmitCooper.K.N, EmitCooper.K.A, EmitCooper.K.H,
      EmitCooper.K.V, EmitCooper.K.D, EmitCooper.K.E, EmitCooper.K.M, EmitCooper.K.P,
      EmitCooper.K.X, EmitCooper.K.Y, EmitCooper.K.W] ?_ ?_
    (500 * (Polynomial.X + 1) ^ 4 + 2 * Polynomial.X + 3) ?_
  · decide
  · intro k
    cases k <;> decide
  · intro n
    simp
    omega


end Cslib.Complexity.Karp
