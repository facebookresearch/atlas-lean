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

/-- Stacks: formula bits `X`, witness bits `W`, token output `T`, table output `B`, and the clause
and literal counters `CC`, `LC`. -/
inductive K | X | W | T | B | CC | LC
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.X, .W, .T, .B, .CC, .LC], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Labels. `un c` reads a unary count onto `CC` (`c = true`) or `LC`; `cls` starts a clause and
`lits` a literal; `nm last` reads name pairs, `last` being the last name bit read (`none`: no bit
yet); `pol` reads the polarity and the next witness bit; `fin` checks that `X` is used up. -/
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

/-- Whether a peeked symbol is the bit `b`. -/
def topIsBit (b : Bool) : Option Sym → Bool
  | some (.bit c) => c == b
  | _ => false

open TM2.Stmt in
/-- At label `self`, read a unary count from `X` onto the counter `k`, then go to `next`; reject
at the end of `X`. -/
def unary (k : K) (self next : Lab) : TM2.Stmt (fun _ : K => Sym) Lab Bool :=
  peek .X (fun _ o => topIsBit true o) <| branch id
    (pop .X (fun s _ => s) <| push k (fun _ => .cl) <| goto fun _ => self)
    (peek .X (fun _ o => topIsBit false o) <| branch id
      (pop .X (fun s _ => s) <| goto fun _ => next)
      (goto fun _ => .rej))

open TM2.Stmt in
/-- The program. -/
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

/-- The start label. -/
def start : Lab := .un true

/-! ### Stacks -/

/-- The stacks, with the counters `CC`, `LC` in unary over `cl`. -/
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

/-- The machine reaches `rej` from `c` within `n` steps. -/
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

/-- One step that lands on `rej`. -/
theorem rej_one {l : Lab} {v : Bool} {S : K → List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some .rej) : Rej 1 ⟨some l, v, S⟩ := by
  rcases hs : TM2.stepAux (prog l) v S with ⟨l', v', S'⟩
  rw [hs] at h
  cases h
  exact ⟨v', S', (Run.single hs).le le_rfl⟩

/-! ### Unary counts -/

/-- Reading `n` ones and a zero: `n + 1` steps, adding `n` to the chosen counter. -/
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

/-- A unary count that never ends: rejected within `|r| + 1` steps. -/
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

/-- Where the name loop ends after the payload `bits`, from last bit `last`: `rej` exactly when
the whole name is non-empty and ends in `false`. -/
def nmEnd : Option Bool → List Bool → Lab
  | last, [] => if last = some false then .rej else .pol
  | _, c :: bits => nmEnd (some c) bits

theorem nmEnd_some (c : Bool) :
    ∀ bits : List Bool, nmEnd (some c) bits = if bits.getLast?.getD c then .pol else .rej
  | [] => by cases c <;> rfl
  | d :: bits => by rw [nmEnd, nmEnd_some d bits, List.getLast?_cons, Option.getD_some]

/-- From the start of a name, the loop ends at `pol` exactly for a canonical name. -/
theorem nmEnd_none (bits : List Bool) :
    nmEnd none bits = if encodeNat (decodeNat bits) = bits then .pol else .rej := by
  simp only [encodeNat_decodeNat_eq_iff]
  cases bits with
  | nil => simp [nmEnd]
  | cons c bits => simp [nmEnd, nmEnd_some, List.getLast?_cons]

/-- Reading the block `delimit bits`: `|bits| + 1` steps, pushing the name on `T` and `B`. -/
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

/-- A block that does not close: rejected within `|r| + 1` steps. -/
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

/-- The polarity and the witness bit: one step. -/
theorem pol_run (p : Bool) (rest w : List Bool) (t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Run prog 1 ⟨some .pol, v, st ((p :: rest).map .bit) (w.map .bit) t b cc lc⟩
      ⟨some .lits, w.head?.getD false, st (rest.map .bit) (w.tail.map .bit) (.lit p :: t)
        (markOf w.head? :: b) cc lc⟩ := by
  cases w <;> exact Run.single (by simp [prog, TM2.stepAux, isBit, Sym.bit?, bitOf, markOf])

theorem pol_rej (w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Rej 1 ⟨some .pol, v, st [] w t b cc lc⟩ :=
  rej_one (by simp [prog, TM2.stepAux, isBit, Sym.bit?])

/-- One literal, from the start of its name block to `lits`: `|encodeNat n| + 2` steps. -/
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

/-- A literal that does not decode: rejected within `|r| + 2` steps. -/
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

/-- The literals of a clause, from `lits` with the literal count on `LC`, ending at `cls` with the
clause's tokens and table entries pushed. -/
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

/-- Literals that do not decode: rejected within `2 |r| + 3` steps. -/
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

/-- One clause, from `cls` back to `cls`. -/
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

/-- All clauses, from `cls` with the clause count on `CC` to `fin`. -/
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

/-- Clauses that do not decode: rejected within `2 |r| + n + 2` steps. -/
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

theorem fin_acc (w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Run prog 1 ⟨some .fin, v, st [] w t b cc lc⟩ ⟨some .acc, false, st [] w t b cc lc⟩ :=
  Run.single (by simp [prog, TM2.stepAux])

theorem fin_rej (s : Sym) (x w t b : List Sym) (cc lc : ℕ) (v : Bool) :
    Rej 1 ⟨some .fin, v, st (s :: x) w t b cc lc⟩ :=
  rej_one (by simp [prog, TM2.stepAux])

theorem st_eq {S : ∀ _ : K, List Sym} (hCC : S .CC = []) (hLC : S .LC = []) :
    S = st (S .X) (S .W) (S .T) (S .B) 0 0 := by
  funext k; cases k <;> simp [hCC, hLC]

/-- **Accepting run.** On a valid encoding `x` of `φ`, the machine reaches `acc` within
`2 |x| + 2` steps, having consumed `X` and one witness bit per literal occurrence, and pushed
`(toks φ).reverse` on `T` and `tblStk (ents φ w)` on `B`. -/
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

/-- **Rejecting run.** On an input that does not decode, the machine reaches `rej` within
`2 |x| + 2` steps. -/
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
