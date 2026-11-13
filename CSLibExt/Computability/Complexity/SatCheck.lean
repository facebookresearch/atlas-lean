/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps
public import Mathlib.Tactic.Linarith

/-!
# SAT verifier, component 3: the clause check

A `TM2` driver that walks the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and decides `checkSpec φ es` against the table stack `tblStk es`.
Per clause (a `cl` token, then its literals) it clears a flag on stack `F`; per literal (a
`lit p` token, then the reversed name bits) it saves `p` on stack `P`, runs a lookup
sub-program, sets the flag if the looked-up value is `p`, and drops the name. At the end of a
clause an unset flag rejects; an exhausted token stack accepts.

The lookup is a parameter: the driver runs on labels `DLab ⊕ LL` with an arbitrary
sub-program `lk` on `LL`, started at `l0` and returning to `DLab.ret`, and `run` assumes only
`LookupSpec` (the lookup leaves `liveVal es q` alone on `V` and changes nothing else).
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier.Check

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability

/-- **Stacks of the clause check.** The eight stacks of the clause-check machine: $T$ (tokens),
$B$ (table), $S$ (the lookup's stash), $A$ and $C$ (the lookup's scratch stacks), $V$ (looked-up
value), $P$ (polarity) and $F$ (clause flag). -/
inductive K | T | B | S | A | C | V | P | F
  deriving DecidableEq

instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.B, K.S, K.A, K.C, K.V, K.P, K.F], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Driver labels of the clause check.** The seven labels of the clause-check driver: start
(begin the next clause), lits (read the next literal), ret (return from the lookup), drop
(discard a literal's name bits), endc (end of a clause), yes (accept) and no (reject). -/
inductive DLab | start | lits | ret | drop | endc | yes | no
  deriving DecidableEq

instance DLab.instFintypeEnumFix : Fintype DLab where
  elems := ⟨↑[DLab.start, .lits, .ret, .drop, .endc, .yes, .no], by decide⟩
  complete := fun x => by cases x <;> decide

variable {LL : Type}

/-- **Clause-check statements.** For a label set $L$, the statements of a multi-stack Turing
machine with the eight driver stacks, each over the symbols of the token and table stacks, with
labels in $D \sqcup L$, where $D$ is the set of driver labels, and with a Boolean internal
state. -/
abbrev Stmt (LL : Type) := TM2.Stmt (fun _ : K => Sym) (DLab ⊕ LL) Bool

/-- **Configurations of the clause-check machine.** For a type $LL$ of lookup labels, a
configuration of the multi-stack Turing machine of the clause check: a current label (absent once
the machine halts) that is either a driver label or a label in $LL$, a Boolean internal state,
and the contents of the eight stacks $T$, $B$, $S$, $A$, $C$, $V$, $P$, $F$ of the clause check,
each a list of symbols of the token and table stacks (name bits, literal and clause markers, and
table markers). -/
abbrev Cfg (LL : Type) := TM2.Cfg (fun _ : K => Sym) (DLab ⊕ LL) Bool

/-- **Calling the lookup.** For the lookup's start label $l_0$ and a polarity $p$, the statement
that pops the top of the token stack $T$, pushes the bit $p$ onto the polarity stack $P$, and
then goes to label $l_0$. -/
def callS (l0 : LL) (p : Bool) : Stmt LL :=
  .pop .T (fun s _ => s) (.push .P (fun _ => .bit p) (.goto fun _ => .inr l0))

/-- **The clause-check driver.** Given the lookup's start label $l_0$, the statement at each
driver label. At start: if the token stack $T$ is empty, go to yes; if its top is a clause
marker, pop it, push the bit false onto the flag stack $F$ and go to lits; otherwise go to no.
At lits: if the top of $T$ is a literal marker of polarity $p$, pop it, push the bit $p$ onto
the polarity stack $P$ and go to $l_0$; otherwise go to endc. At ret: if the top of the value
stack $V$ is the bit true exactly when the top of $P$ is the bit true, pop $F$ and push the bit
true onto it; in either case then pop $V$, pop $P$ and go to drop. At drop: if the top of $T$
is a bit, pop it and go to drop; otherwise go to lits. At endc: if the top of $F$ is the bit
true, pop it and go to start; otherwise go to no. At yes and at no: halt. -/
def drv (l0 : LL) : DLab → Stmt LL
  | .start => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .inl .yes) <|
      .peek .T (fun _ o => o == some .cl) <| .branch id
        (.pop .T (fun s _ => s) (.push .F (fun _ => .bit false) (.goto fun _ => .inl .lits)))
        (.goto fun _ => .inl .no)
  | .lits => .peek .T (fun _ o => o == some (.lit true)) <| .branch id (callS l0 true) <|
      .peek .T (fun _ o => o == some (.lit false)) <| .branch id (callS l0 false)
        (.goto fun _ => .inl .endc)
  | .ret => .peek .V (fun _ o => o == some (.bit true)) <|
      .peek .P (fun s o => s == (o == some (.bit true))) <| .branch id
        (.pop .F (fun s _ => s) <| .push .F (fun _ => .bit true) <|
          .pop .V (fun s _ => s) <| .pop .P (fun s _ => s) <| .goto fun _ => .inl .drop)
        (.pop .V (fun s _ => s) <| .pop .P (fun s _ => s) <| .goto fun _ => .inl .drop)
  | .drop => .peek .T (fun _ o => isBit Sym.bit? o) <| .branch id
      (.pop .T (fun s _ => s) (.goto fun _ => .inl .drop)) (.goto fun _ => .inl .lits)
  | .endc => .peek .F (fun _ o => o == some (.bit true)) <| .branch id
      (.pop .F (fun s _ => s) (.goto fun _ => .inl .start)) (.goto fun _ => .inl .no)
  | .yes => .halt
  | .no => .halt

/-- **The clause-check driver with a lookup sub-program.** Given a lookup sub-program $lk$ on a
label set $L$ and an entry label $l_0 \in L$, this is the program on the labels $D \sqcup L$, where
$D$ is the set of driver labels: at a driver label $d$ it runs the driver's statement for $d$
(the driver calls the lookup by jumping to $l_0$), and at a label $l \in L$ it runs $lk(l)$. -/
def prog (lk : LL → Stmt LL) (l0 : LL) : DLab ⊕ LL → Stmt LL
  | .inl d => drv l0 d
  | .inr l => lk l

/-- **The lookup contract.** A lookup sub-program $lk$ with start label $l_0$ meets the contract
with constants $a$ and $b$ when the following holds. For every name $q$ (a list of bits), every
table $es$, with table stack $B_{es}$, and every list of symbols $R$ whose first symbol, if any,
is not a bit, start the clause-check machine with lookup $lk$ at label $l_0$, with any internal
state and with stack contents that have the bits of $q$ in reverse order followed by $R$ on the
token stack $T$, $B_{es}$ on $B$, and $S$, $A$, $C$, $V$ empty. Then it reaches label ret in at
most $a \cdot |B_{es}| + b$ steps, with some internal state, with $V$ holding exactly the bit
that is the live value of $q$ in $es$, and with every other stack unchanged. -/
def LookupSpec (lk : LL → Stmt LL) (l0 : LL) (a b : ℕ) : Prop :=
  ∀ (q : List Bool) (es : List Ent) (R : List Sym), R.head?.bind Sym.bit? = none →
    ∀ (v : Bool) (St : ∀ _ : K, List Sym), St .T = (q.map Sym.bit).reverse ++ R →
      St .B = tblStk es → St .S = [] → St .A = [] → St .C = [] → St .V = [] →
      ∃ v', RunLe (prog lk l0) (a * (tblStk es).length + b) ⟨some (.inr l0), v, St⟩
        ⟨some (.inl .ret), v', update St .V [Sym.bit (liveVal es q)]⟩

/-! ### The token stack, clause by clause -/

/-- **A literal's tokens on the token stack.** For a literal $(n, p)$ with variable index $n$ and
polarity $p$, the list of symbols consisting of the literal marker of polarity $p$ followed by
the bits of the binary encoding of $n$ (least significant bit first, empty for $n = 0$) in
reverse order. -/
def litRev (l : ℕ × Bool) : List Sym := .lit l.2 :: ((encodeNat l.1).map Sym.bit).reverse

/-- **A clause's tokens on the token stack.** For a clause with literals $l_1, \dots, l_k$, the
list of symbols consisting of the clause marker followed by the stack tokens of $l_k$, then of
$l_{k-1}$, down to $l_1$, where the stack tokens of a literal $(n, p)$ are the literal marker of
polarity $p$ followed by the bits of the binary encoding of $n$ (least significant bit first,
empty for $n = 0$) in reverse order. -/
def clRev (C : CNFClause) : List Sym := .cl :: C.reverse.flatMap litRev

theorem clauseToks_reverse (C : CNFClause) : (clauseToks C).reverse = clRev C := by
  simp only [clauseToks, clRev, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.reverse_flatMap]
  congr 1
  apply List.flatMap_congr
  intro l _
  simp [litToks, litRev]

theorem toks_reverse (φ : CNF) : (toks φ).reverse = φ.reverse.flatMap clRev := by
  simp only [toks, List.reverse_flatMap]
  exact List.flatMap_congr fun C _ => clauseToks_reverse C

theorem litRev_length (l : ℕ × Bool) : (litRev l).length = (encodeNat l.1).length + 1 := by
  simp [litRev]

/-! ### One-step lemmas -/

section Steps

variable (lk : LL → Stmt LL) (l0 : LL)

theorem start_nil (v : Bool) (St : ∀ _ : K, List Sym) (h : St .T = []) :
    Run (prog lk l0) 1 ⟨some (.inl .start), v, St⟩ ⟨some (.inl .yes), true, St⟩ :=
  Run.single (by simp [prog, drv, TM2.stepAux, h])

theorem start_cl (v : Bool) (St : ∀ _ : K, List Sym) (R : List Sym) (h : St .T = .cl :: R) :
    Run (prog lk l0) 1 ⟨some (.inl .start), v, St⟩
      ⟨some (.inl .lits), true, update (update St .T R) .F (.bit false :: St .F)⟩ :=
  Run.single (by simp [prog, drv, TM2.stepAux, h])

theorem lits_lit (v : Bool) (St : ∀ _ : K, List Sym) (p : Bool) (R : List Sym)
    (h : St .T = .lit p :: R) :
    ∃ v', Run (prog lk l0) 1 ⟨some (.inl .lits), v, St⟩
      ⟨some (.inr l0), v', update (update St .T R) .P (.bit p :: St .P)⟩ := by
  cases p
  · exact ⟨_, Run.single (by simp [prog, drv, callS, TM2.stepAux, h]; rfl)⟩
  · exact ⟨_, Run.single (by simp [prog, drv, callS, TM2.stepAux, h]; rfl)⟩

theorem lits_end (v : Bool) (St : ∀ _ : K, List Sym) (h : St .T = [] ∨ (St .T).head? = some .cl) :
    ∃ v', Run (prog lk l0) 1 ⟨some (.inl .lits), v, St⟩ ⟨some (.inl .endc), v', St⟩ := by
  rcases h with h | h
  · exact ⟨_, Run.single (by simp [prog, drv, TM2.stepAux, h]; rfl)⟩
  · exact ⟨_, Run.single (by simp [prog, drv, TM2.stepAux, h]; rfl)⟩

theorem ret_run (v : Bool) (St : ∀ _ : K, List Sym) (val p s : Bool) (hV : St .V = [.bit val])
    (hP : St .P = [.bit p]) (hF : St .F = [.bit s]) :
    ∃ v', Run (prog lk l0) 1 ⟨some (.inl .ret), v, St⟩ ⟨some (.inl .drop), v',
      update (update (update St .F [.bit (s || val == p)]) .V []) .P []⟩ := by
  refine ⟨val == p, Run.single ?_⟩
  cases val <;> cases p <;> cases s <;>
    simp [prog, drv, TM2.stepAux, hV, hP, hF, update_idem, update_comm (show K.F ≠ K.V by decide),
      update_comm (show K.F ≠ K.P by decide)] <;> rfl

theorem drop_run (bs : List Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none) :
    ∀ (v : Bool) (St : ∀ _ : K, List Sym), St .T = bs.map Sym.bit ++ R →
      ∃ v', Run (prog lk l0) (bs.length + 1) ⟨some (.inl .drop), v, St⟩
        ⟨some (.inl .lits), v', update St .T R⟩ := by
  induction bs with
  | nil =>
      intro v St h
      refine ⟨false, Run.single ?_⟩
      have h' : (St .T).head?.bind Sym.bit? = none := by simpa [h] using hR
      have : isBit Sym.bit? (St .T).head? = false := by simp [isBit, h']
      simp only [List.map_nil, List.nil_append] at h
      simp only [prog, drv, TM2.stepAux, this, id, cond_false]
      rw [← h, update_eq_self]
  | cons b bs ih =>
      intro v St h
      obtain ⟨v', hr⟩ := ih true (update St .T (bs.map Sym.bit ++ R)) (by simp)
      refine ⟨v', Run.head ?_ (by simpa using hr)⟩
      simp [TM2.step, prog, drv, TM2.stepAux, h, isBit, Sym.bit?]

theorem endc_true (v : Bool) (St : ∀ _ : K, List Sym) (h : St .F = [.bit true]) :
    ∃ v', Run (prog lk l0) 1 ⟨some (.inl .endc), v, St⟩
      ⟨some (.inl .start), v', update St .F []⟩ :=
  ⟨_, Run.single (by simp [prog, drv, TM2.stepAux, h]; rfl)⟩

theorem endc_false (v : Bool) (St : ∀ _ : K, List Sym) (h : St .F = [.bit false]) :
    ∃ v', Run (prog lk l0) 1 ⟨some (.inl .endc), v, St⟩ ⟨some (.inl .no), v', St⟩ :=
  ⟨_, Run.single (by simp [prog, drv, TM2.stepAux, h]; rfl)⟩

end Steps

/-! ### The literal loop and the clause loop -/

section Loops

variable {lk : LL → Stmt LL} {l0 : LL} {a b : ℕ}

theorem litRev_head_bit (l : ℕ × Bool) (rest : List Sym) :
    (litRev l ++ rest).head?.bind Sym.bit? = none := by
  simp [litRev, Sym.bit?]

/-- **Literal loop of the clause check.** Suppose the lookup sub-program $lk$ with start label
$l_0$ meets the lookup contract with constants $a$ and $b$. Let $es$ be a table with table stack
$B_{es}$, let $R$ be a list of symbols that is empty or starts with a clause marker, and let $s$
be a bit. The stack tokens of a literal $(n, p)$ are the literal marker of polarity $p$
followed by the bits of the binary encoding of $n$ (least significant bit first, empty for
$n = 0$) in reverse order. Let $l_1, \dots, l_k$ be literals whose stack tokens have total
length $N$. Start the clause-check machine with lookup $lk$ at label lits, with any internal
state and with the stack tokens of $l_1$, then of $l_2$, up to $l_k$, followed by $R$ on the
token stack $T$, $B_{es}$ on $B$, the single bit $s$ on the flag stack $F$, and $S$, $A$, $C$,
$V$, $P$ empty. Then it reaches label endc in at most
$k \cdot (a \cdot |B_{es}| + b + 2) + N + 1$ steps, with some internal state, with $T$ holding
$R$, with $F$ holding the single bit that is true exactly when $s$ is true or some literal
$l_i = (n, p)$ has live value of the binary encoding of $n$ in $es$ equal to $p$, and with
every other stack unchanged. -/
theorem lits_run (hlk : LookupSpec lk l0 a b) (es : List Ent) (R : List Sym)
    (hR : R = [] ∨ R.head? = some .cl) :
    ∀ (Ls : List (ℕ × Bool)) (s v : Bool) (St : ∀ _ : K, List Sym),
      St .T = Ls.flatMap litRev ++ R → St .B = tblStk es → St .S = [] → St .A = [] →
      St .C = [] → St .V = [] → St .P = [] → St .F = [.bit s] →
      ∃ v', RunLe (prog lk l0)
        (Ls.length * (a * (tblStk es).length + b + 2) + (Ls.flatMap litRev).length + 1)
        ⟨some (.inl .lits), v, St⟩ ⟨some (.inl .endc), v', update (update St .T R) .F
          [.bit (s || Ls.any fun l => liveVal es (encodeNat l.1) == l.2)]⟩ := by
  have hRb : R.head?.bind Sym.bit? = none := by
    rcases hR with h | h <;> simp [h, Sym.bit?]
  intro Ls
  induction Ls with
  | nil =>
      intro s v St hT _ _ _ _ _ _ hF
      simp only [List.flatMap_nil, List.nil_append] at hT
      obtain ⟨v', hr⟩ := lits_end lk l0 v St (by rw [hT]; exact hR)
      refine ⟨v', ?_⟩
      have : update (update St .T R) .F [.bit (s || false)] = St := by
        rw [Bool.or_false, ← hF, ← hT, update_eq_self, update_eq_self]
      rw [List.any_nil, this]
      exact hr.le (by simp)
  | cons l Ls ih =>
      intro s v St hT hB hS hA hC hV hP hF
      set rest := Ls.flatMap litRev ++ R with hrest
      have hrestb : rest.head?.bind Sym.bit? = none := by
        cases Ls with
        | nil => simpa [hrest] using hRb
        | cons l' Ls' =>
            rw [hrest, List.flatMap_cons, List.append_assoc]; exact litRev_head_bit _ _
      have hT' : St .T = .lit l.2 :: (((encodeNat l.1).map Sym.bit).reverse ++ rest) := by
        rw [hT]; simp [litRev, hrest]
      obtain ⟨v₁, r₁⟩ := lits_lit lk l0 v St l.2 _ hT'
      set St₁ := update (update St .T (((encodeNat l.1).map Sym.bit).reverse ++ rest)) .P
        (.bit l.2 :: St .P) with hSt₁
      obtain ⟨v₂, r₂⟩ := hlk (encodeNat l.1) es rest hrestb v₁ St₁ (by simp [hSt₁])
        (by simp [hSt₁, hB]) (by simp [hSt₁, hS]) (by simp [hSt₁, hA]) (by simp [hSt₁, hC])
        (by simp [hSt₁, hV])
      set val := liveVal es (encodeNat l.1) with hval
      set St₂ := update St₁ .V [Sym.bit val] with hSt₂
      obtain ⟨v₃, r₃⟩ := ret_run lk l0 v₂ St₂ val l.2 s (by simp [hSt₂])
        (by simp [hSt₂, hSt₁, hP]) (by simp [hSt₂, hSt₁, hF])
      set St₃ := update (update (update St₂ .F [.bit (s || val == l.2)]) .V []) .P [] with hSt₃
      obtain ⟨v₄, r₄⟩ := drop_run lk l0 (encodeNat l.1).reverse rest hrestb v₃ St₃
        (by simp [hSt₃, hSt₂, hSt₁, List.map_reverse])
      set St₄ := update St₃ .T rest with hSt₄
      obtain ⟨v₅, r₅⟩ := ih (s || val == l.2) v₄ St₄ (by simp [hSt₄])
        (by simp [hSt₄, hSt₃, hSt₂, hSt₁, hB]) (by simp [hSt₄, hSt₃, hSt₂, hSt₁, hS])
        (by simp [hSt₄, hSt₃, hSt₂, hSt₁, hA]) (by simp [hSt₄, hSt₃, hSt₂, hSt₁, hC])
        (by simp [hSt₄, hSt₃]) (by simp [hSt₄, hSt₃]) (by simp [hSt₄, hSt₃, hSt₂, hSt₁])
      refine ⟨v₅, ?_⟩
      have h := ((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl) |>.trans (r₄.le le_rfl) |>.trans r₅
      have hfin : update (update St₄ .T R) .F [.bit ((s || val == l.2) ||
            Ls.any fun l => liveVal es (encodeNat l.1) == l.2)] = update (update St .T R) .F
            [.bit (s || (l :: Ls).any fun l => liveVal es (encodeNat l.1) == l.2)] := by
        funext k
        cases k <;> simp [hSt₄, hSt₃, hSt₂, hSt₁, hT, hP, hV, hrest, Bool.or_assoc, ← hval]
      rw [hfin] at h
      refine h.mono ?_
      simp only [List.length_cons, List.flatMap_cons, List.length_append, litRev_length,
        List.length_reverse, List.length_map]
      nlinarith

theorem clRev_head (C : CNFClause) (rest : List Sym) : (clRev C ++ rest).head? = some .cl := rfl

theorem litRev_flatMap_length_ge (Ls : List (ℕ × Bool)) :
    Ls.length ≤ (Ls.flatMap litRev).length := by
  induction Ls with
  | nil => simp
  | cons l Ls ih => simp [List.flatMap_cons, litRev_length]; omega

/-- **Clause loop of the clause check.** Suppose the lookup sub-program $lk$ with start label
$l_0$ meets the lookup contract with constants $a$ and $b$. Let $es$ be a table with table stack
$B_{es}$, and let $\varphi$ be a CNF formula with clauses $D_1, \dots, D_m$. The stack tokens
of a clause are its clause marker followed by the stack tokens of its literals, last literal
first, where the stack tokens of a literal $(n, p)$ are the literal marker of polarity $p$
followed by the bits of the binary encoding of $n$ (least significant bit first, empty for
$n = 0$) in reverse order. Let $N$ be the total length of the stack tokens of
$D_1, \dots, D_m$. Start the clause-check machine with lookup $lk$ at label start, with any
internal state and with the stack tokens of $D_1$, then of $D_2$, up to $D_m$ on the token
stack $T$, $B_{es}$ on $B$, and $S$, $A$, $C$, $V$, $P$, $F$ empty. Then within
$N \cdot (a \cdot |B_{es}| + b + 5) + 1$ steps it reaches, with some internal state and some
stack contents, label yes if every clause $D_j$ has a literal $(n, p)$ such that the live value
of the binary encoding of $n$ in $es$ is $p$, and label no otherwise. -/
theorem clauses_run (hlk : LookupSpec lk l0 a b) (es : List Ent) :
    ∀ (Cs : CNF) (v : Bool) (St : ∀ _ : K, List Sym),
      St .T = Cs.flatMap clRev → St .B = tblStk es → St .S = [] → St .A = [] →
      St .C = [] → St .V = [] → St .P = [] → St .F = [] →
      ∃ v' S', RunLe (prog lk l0)
        ((Cs.flatMap clRev).length * (a * (tblStk es).length + b + 5) + 1)
        ⟨some (.inl .start), v, St⟩ ⟨some (.inl (if Cs.all (fun C => C.any fun l =>
          liveVal es (encodeNat l.1) == l.2) then .yes else .no)), v', S'⟩ := by
  intro Cs
  induction Cs with
  | nil =>
      intro v St hT _ _ _ _ _ _ _
      exact ⟨true, St, (start_nil lk l0 v St (by simpa using hT)).le (by simp)⟩
  | cons C Cs ih =>
      intro v St hT hB hS hA hC hV hP hF
      set rest := Cs.flatMap clRev with hrest
      have hR : rest = [] ∨ rest.head? = some .cl := by
        cases Cs with
        | nil => left; rfl
        | cons C' Cs' => right; rw [hrest, List.flatMap_cons]; exact clRev_head C' _
      have hT' : St .T = .cl :: (C.reverse.flatMap litRev ++ rest) := by
        rw [hT]; simp [clRev, hrest]
      have r₁ := start_cl lk l0 v St _ hT'
      set St₁ := update (update St .T (C.reverse.flatMap litRev ++ rest)) .F
        (.bit false :: St .F) with hSt₁
      obtain ⟨v₂, r₂⟩ := lits_run hlk es rest hR C.reverse false true St₁ (by simp [hSt₁])
        (by simp [hSt₁, hB]) (by simp [hSt₁, hS]) (by simp [hSt₁, hA]) (by simp [hSt₁, hC])
        (by simp [hSt₁, hV]) (by simp [hSt₁, hP]) (by simp [hSt₁, hF])
      set c := C.any fun l => liveVal es (encodeNat l.1) == l.2 with hc
      have hcr : (false || C.reverse.any fun l => liveVal es (encodeNat l.1) == l.2) = c := by
        simp [hc, List.any_reverse]
      rw [hcr] at r₂
      set St₂ := update (update St₁ .T rest) .F [.bit c] with hSt₂
      have hcost : (C.reverse.length * (a * (tblStk es).length + b + 2) +
          (C.reverse.flatMap litRev).length + 1) + 2 ≤
          (clRev C).length * (a * (tblStk es).length + b + 5) := by
        have h1 := litRev_flatMap_length_ge C.reverse
        simp only [clRev, List.length_cons]
        generalize a * (tblStk es).length + b = X
        generalize C.reverse.length = m at h1 ⊢
        generalize (C.reverse.flatMap litRev).length = L at h1 ⊢
        have := Nat.mul_le_mul_right (X + 2) h1
        nlinarith
      cases hcv : c with
      | true =>
          obtain ⟨v₃, r₃⟩ := endc_true lk l0 v₂ St₂ (by simp [hSt₂, hcv])
          obtain ⟨v', S', r₄⟩ := ih v₃ (update St₂ .F []) (by simp [hSt₂])
            (by simp [hSt₂, hSt₁, hB]) (by simp [hSt₂, hSt₁, hS]) (by simp [hSt₂, hSt₁, hA])
            (by simp [hSt₂, hSt₁, hC]) (by simp [hSt₂, hSt₁, hV]) (by simp [hSt₂, hSt₁, hP])
            (by simp)
          refine ⟨v', S', ?_⟩
          have h := (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)).trans r₄
          rw [List.all_cons, ← hc, hcv, Bool.true_and]
          refine h.mono ?_
          simp only [List.flatMap_cons, List.length_append, add_mul]
          linarith
      | false =>
          obtain ⟨v₃, r₃⟩ := endc_false lk l0 v₂ St₂ (by simp [hSt₂, hcv])
          refine ⟨v₃, St₂, ?_⟩
          have h := ((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)
          rw [List.all_cons, ← hc, hcv, Bool.false_and]
          refine h.mono ?_
          simp only [List.flatMap_cons, List.length_append, add_mul]
          have : 0 ≤ (List.flatMap clRev Cs).length * (a * (tblStk es).length + b + 5) :=
            Nat.zero_le _
          linarith

end Loops

/-- **The clause check.** Suppose the lookup sub-program $lk$ with entry label $l_0$ satisfies
the lookup contract with constants $a, b \in \mathbb{N}$. Let $\varphi$ be a CNF formula, $es$ a
list of table entries, $t$ the token list of $\varphi$ and $m$ the length of the table stack of
$es$. Start the driver with lookup $lk$ at its start label, with any internal state, with $t$
reversed on the token stack, the table stack of $es$ on the table stack, and the other six stacks
empty. Then within at most $|t| \cdot (a m + b + 5) + 1$ steps it reaches the label yes, with
some internal state and some stack contents, if every clause of $\varphi$ has a literal whose
polarity equals the value of its variable, and it reaches the label no otherwise. Here the value
of a variable $n$ is the value of the first entry of $es$ that is named by the binary encoding of
$n$ and has a value, or false if there is no such entry. -/
theorem run {lk : LL → Stmt LL} {l0 : LL} {a b : ℕ} (hlk : LookupSpec lk l0 a b) (φ : CNF)
    (es : List Ent) (v : Bool) (St : ∀ _ : K, List Sym) (hT : St .T = (toks φ).reverse)
    (hB : St .B = tblStk es) (hS : St .S = []) (hA : St .A = []) (hC : St .C = [])
    (hV : St .V = []) (hP : St .P = []) (hF : St .F = []) :
    ∃ v' S', RunLe (prog lk l0) ((toks φ).length * (a * (tblStk es).length + b + 5) + 1)
      ⟨some (.inl .start), v, St⟩
      ⟨some (.inl (if checkSpec φ es then .yes else .no)), v', S'⟩ := by
  rw [toks_reverse] at hT
  obtain ⟨v', S', h⟩ := clauses_run hlk es φ.reverse v St hT hB hS hA hC hV hP hF
  refine ⟨v', S', ?_⟩
  have hl : (toks φ).length = (φ.reverse.flatMap clRev).length := by
    rw [← toks_reverse, List.length_reverse]
  rw [hl]
  have hr : ∀ {α : Type} (l : List α) (f : α → Bool), l.reverse.all f = l.all f := by
    intro α l f; rw [Bool.eq_iff_iff]; simp [List.all_eq_true]
  rw [checkSpec, ← hr]
  exact h

end Cslib.Complexity.SatVerifier.Check
