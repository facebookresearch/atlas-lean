/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Situation

/-!
# Cook-Levin: generator machine for the accept family

For every label/state code `u < n1`, the dense unit clause `X[T, u]` with polarity `u = ac`, then
for every symbol code `x < g` the dense unit clause `C[T, k1, 0, x]` with polarity `x = ea`: at
time `T` the machine is halted and the output stack's top cell holds the accept symbol.
`Situation.Enc.accFamily` is the instance for a concrete encoding. Every clause is dense over
`V = (T+1)·W`.

The machine computes `H·g`, `W`, `T·W`, `V = (T+1)·W` and the cell base on runtime counters; the
`u` and `x` loops are label chains. `acc_gen_time` gives its run and step bound.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Accept

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc encodeClause_denseClause denseClause)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out emitS emitOut incS drainS
  xferES copyS mulS mulS_run gapS bud_st)

/-! ## [FAM] The family (pure specification) -/

section Spec

variable (L : Layout) (n1 ac k1 ea : ℕ)

/-- Code-block clause `u`: `X[T,u]`, positive iff `u = ac`. -/
def codeLits (T H u : ℕ) : List (ℕ × Bool) := [(L.xIdx H T u, decide (u = ac))]

/-- Top-cell clause `x` of stack `k1`: `C[T,k1,0,x]`, positive iff `x = ea`. -/
def cellLits (T H x : ℕ) : List (ℕ × Bool) := [(L.cIdx H T k1 0 x, decide (x = ea))]

/-- **The accept family** (layout level). -/
def accFam (T H : ℕ) : CNF :=
  (List.range n1).map (fun u => denseClause (L.numVars T H) (codeLits L ac T H u)) ++
    (List.range L.g).map (fun x => denseClause (L.numVars T H) (cellLits L k1 ea T H x))

end Spec

/-! ## [FAM] The generator machine -/

/-- Unit-counter stacks of the generator. -/
inductive CK
  | Tn | Hs | Gc | HG | Wc | Kc | K1 | Vc | TW | CB | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Kc, CK.K1, CK.Vc, CK.TW, CK.CB, CK.P, CK.Q,
      CK.tmp, CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Clause kinds: code clause `u`, cell clause `x`. -/
inductive AK (n1 g : ℕ)
  | code (u : Fin n1)
  | cell (x : Fin g)
  deriving DecidableEq, Fintype

namespace AK

variable {n1 g : ℕ}

/-- Base counter of the single literal. -/
def bc : AK n1 g → CK
  | code _ => .TW
  | cell _ => .CB

/-- Offset of the single literal from its base. -/
def off : AK n1 g → ℕ
  | code u => u
  | cell x => x

/-- Polarity of the single literal. -/
def sg (ac ea : ℕ) : AK n1 g → Bool
  | code u => decide (u.val = ac)
  | cell x => decide (x.val = ea)

theorem bc_ne (c : AK n1 g) : c.bc ≠ .Q ∧ c.bc ≠ .tmp ∧ c.bc ≠ .P := by
  cases c <;> simp [bc]

end AK

/-- Precomputation stages. -/
inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | tw (s : MS) | inc | v (s : MS)
  | cb1 | cb2 | cbA | k1 | cbM (s : MS)
  deriving DecidableEq, Fintype

/-- Stages of the routine emitting the literal. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- Labels, finite (`Fin` fields only). -/
inductive GL (n1 g : ℕ)
  | pre (s : PS)
  | e00 (c : AK n1 g) | cv1 (c : AK n1 g) | cv2 (c : AK n1 g) | lit (c : AK n1 g) (s : LS)
  | fin (c : AK n1 g)
  | done
  deriving DecidableEq, Fintype

namespace GL

variable {n1 g : ℕ}

/-- Code clause `u` (`done` past the end). -/
def codeFrom (u : ℕ) : GL n1 g := if h : u < n1 then .e00 (.code ⟨u, h⟩) else .done

/-- The code chain, last clause first. -/
def codeStart : GL n1 g := if n1 = 0 then .done else codeFrom (n1 - 1)

/-- Cell clause `x` (the code chain past the end). -/
def cellFrom (x : ℕ) : GL n1 g := if h : x < g then .e00 (.cell ⟨x, h⟩) else codeStart

/-- First clause emitted: the last cell clause. -/
def start : GL n1 g := if g = 0 then codeStart else cellFrom (g - 1)

/-- Where to go after clause `c` (clauses are emitted last first). -/
def nextC : AK n1 g → GL n1 g
  | .code u => if u.val = 0 then .done else codeFrom (u.val - 1)
  | .cell x => if x.val = 0 then codeStart else cellFrom (x.val - 1)

theorem codeFrom_of_lt {u : ℕ} (h : u < n1) : (codeFrom u : GL n1 g) = .e00 (.code ⟨u, h⟩) :=
  dite_eq_left h

theorem cellFrom_of_lt {x : ℕ} (h : x < g) : (cellFrom x : GL n1 g) = .e00 (.cell ⟨x, h⟩) :=
  dite_eq_left h

end GL

section Machine

variable (L : Layout) (n1 ac k1 ea : ℕ)

/-- The literal routine of clause `c`: `Q := base + off`, the gap down from `P`, the slot, drain
`Q`. -/
def litP (c : AK n1 L.g) : LS → TM2.Stmt (SΓ CK) (GL n1 L.g) Bool
  | .cp1 => xfer (.c c.bc) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c .cp1) (.lit c .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c c.bc, ()⟩] (.lit c .cp2) (.lit c .eo)
  | .eo => emitR (.c .Q) (List.replicate c.off ()) (.lit c .dec)
  | .dec => decr (.c .P) (.lit c .bad) (.lit c .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c .cmp)
      (.lit c (.r .lt)) (.lit c (.r .eq)) (.lit c (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c (.r o)) (.lit c (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c (.rB o))
      (if o = .eq then .lit c .slot else .lit c .emL)
  | .emL => emitR .out [false, true] (.lit c .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg ac ea))) (.lit c .dq)
  | .dq => xfer (.c .Q) [] (.lit c .dq) (.fin c)

/-- The generator. Input: `T` on `Tn`, `H` on `Hs`, everything else empty. -/
def prog : GL n1 L.g → TM2.Stmt (SΓ CK) (GL n1 L.g) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Kc) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Kc .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre (.tw .head)) s
  | .pre (.tw s) => mulS .Tn .md .Wc .TW .tmp (fun s => .pre (.tw s)) (.pre .inc) s
  | .pre .inc => incr (.c .Tn) () (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .cb1) s
  | .pre .cb1 => xfer (.c .TW) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.pre .cb1) (.pre .cb2)
  | .pre .cb2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.pre .cb2) (.pre .cbA)
  | .pre .cbA => emitR (.c .CB) (List.replicate L.A ()) (.pre .k1)
  | .pre .k1 => emitR (.c .K1) (List.replicate k1 ()) (.pre (.cbM .head))
  | .pre (.cbM s) => mulS .K1 .md .HG .CB .tmp (fun s => .pre (.cbM s)) GL.start s
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (.lit c .cp1)
  | .lit c s => litP L n1 ac ea c s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GL.nextC c)
  | .done => .halt

/-- **The generator as a genuine `FinTM2`** (finiteness check only). -/
def accTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := GL n1 L.g
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L n1 ac k1 ea

end Machine

/-! ## [FAM] Correctness: one clause -/

section Clause

variable {L : Layout} {n1 ac k1 ea : ℕ}

/-- Scratch counters that are empty whenever a clause starts. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

/-- The literal: from `P = q + gap + 1`, compute `Q := q = base + off`, prepend the gap and the
slot, leave `P = q` and the scratch counters empty. -/
theorem lit_run (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F c.bc + c.off) (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (gap * (3 * q + 6) + 2 * F c.bc + 4 * q + 9)
      ⟨some (.lit c .cp1), v, st F o⟩
      ⟨some (.fin c), false,
        st (update F .P q) (encodeSlot (some (c.sg ac ea)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  refine Bud.start ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .lit c .cp1) (l₂ := .lit c .cp2)
    (next := .lit c .eo) rfl rfl b1 b2 (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .lit c .eo) (next := .lit c .dec) rfl _ _
    _).bud ?_
  refine (gapS (M := prog L n1 ac k1 ea) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true])
    (dec := .lit c .dec) (cmpL := .lit c .cmp) (emitL := .lit c .emL)
    (ifZero := .lit c .bad) (next := .lit c .slot) (r := fun o => .lit c (.r o))
    (rB := fun o => .lit c (.rB o))
    (out := fun o => if o = .eq then .lit c .slot else .lit c .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .lit c .slot) (next := .lit c .dq) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L n1 ac k1 ea) (self := .lit c .dq) (next := .fin c) (x := .Q) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- Cost of one clause. -/
def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 10 * V + 13

theorem encodeClause_unit {V p : ℕ} {b : Bool} (h : p < V) :
    encodeClause (denseClause V [(p, b)]) =
      rep [false, true] p ++ encodeSlot (some b) ++ rep [false, true] (V - p - 1) ++
        [false, false] := by
  rw [encodeClause_denseClause (show Inc 0 [(p, b)] V from ⟨Nat.zero_le _, h⟩)]
  simp only [gapEnc, Nat.sub_zero, List.append_assoc]
  rw [show V - (p + 1) = V - p - 1 by omega]

/-- One whole clause: from `e00 c` to `nextC c`, all counters restored. -/
theorem clause_run {V : ℕ} (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V)
    (hP : F .P = 0) (hlt : F c.bc + c.off < V) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (clauseB V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GL.nextC c), false,
        st F (encodeClause (denseClause V [(F c.bc + c.off, c.sg ac ea)]) ++ o)⟩ := by
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  set p := F c.bc + c.off with hpdef
  refine Bud.start ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := .lit c .cp1)
    rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  have r := lit_run (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) c (update F .P (F .Vc + F .P))
    ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
    p (V - p - 1) (by simp [hpdef, b3]) (by simp [hV, hP]; omega) ([false, false] ++ o) false
  refine r.bud ?_
  refine (xferES (M := prog L n1 ac k1 ea) (self := .fin c) (next := GL.nextC c) (x := .P) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp only [update_self, ne_eq, b3, not_false_eq_true, update_of_ne, hV, hP]
    have h1 : (V - p - 1) * (3 * p + 6) ≤ V * (3 * V + 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold clauseB
    omega
  · rw [encodeClause_unit hlt]
    simp only [update_self, update_idem, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hP]

end Clause

/-! ## [FAM] Correctness: the two label chains and the whole generator -/

section Top

variable {L : Layout} {n1 ac k1 ea : ℕ}

/-- The code chain from clause `u` down to `0`. -/
theorem codes_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) :
    ∀ u, u < n1 → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((u + 1) * clauseB V) ⟨some (GL.codeFrom u), v, st F o⟩
        ⟨some .done, false, st F ((List.range (u + 1)).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  intro u
  induction u with
  | zero =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨0,
          hu⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GL.codeFrom_of_lt hu]
      simpa [GL.nextC, AK.bc, AK.off, AK.sg] using r
  | succ u ih =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨u + 1,
          hu⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel] at r
      rw [GL.codeFrom_of_lt hu]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .TW + (u + 1),
          decide (u + 1 = ac))]) ++ o)
        false
      rw [List.range_succ (n := u + 1), List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (u + 1)]; omega

theorem codeStart_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (n1 * clauseB V) ⟨some GL.codeStart, false, st F o⟩
      ⟨some .done, false, st F ((List.range n1).flatMap
        (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  by_cases h : n1 = 0
  · subst h
    simp only [GL.codeStart, ite_true, List.range_zero, List.flatMap_nil, List.nil_append]
    exact ⟨0, Nat.zero_le _, Run.zero _⟩
  · rw [GL.codeStart, ite_eq_right h]
    have := codes_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt (n1 - 1) (by omega)
      o false
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- The cell chain from clause `x` down to `0`, then the whole code chain. -/
theorem cells_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (hlc : F .CB + L.g ≤ V) :
    ∀ x, x < L.g → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((x + 1) * clauseB V + n1 * clauseB V)
        ⟨some (GL.cellFrom x), v, st F o⟩
        ⟨some .done, false, st F ((List.range n1).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++
          (List.range (x + 1)).flatMap
          (fun x => encodeClause (denseClause V [(F .CB + x, decide (x = ea))])) ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨0,
          hx⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GL.cellFrom_of_lt hx]
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, ite_true] at r
      refine Bud.start (r.bud ?_)
      have := codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt
        (encodeClause (denseClause V [(F .CB + 0, decide (0 = ea))]) ++ o)
      simp only [zero_add, List.range_one, List.flatMap_singleton, List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      omega
  | succ x ih =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨x + 1,
          hx⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GL.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel] at r
      rw [GL.cellFrom_of_lt hx]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .CB + (x + 1),
          decide (x + 1 = ea))]) ++ o)
        false
      rw [List.range_succ (n := x + 1), List.flatMap_append, List.flatMap_singleton]
      simp only [List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (x + 1)]; omega

/-- Initial counters: `T` on `Tn`, `H` on `Hs`. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- Counters after the precomputation. -/
def preF (L : Layout) (k1 T H : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Kc => L.KK
  | .K1 => k1
  | .Vc => L.numVars T H
  | .TW => T * L.rowW H
  | .CB => L.cIdx H T k1 0 0
  | _ => 0

/-- Cost of the precomputation. -/
def preB (L : Layout) (k1 T H : ℕ) : ℕ :=
  3 + (H * (2 * L.g + 3) + H + 2) + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) +
    (T * (2 * L.rowW H + 3) + T + 2) + 1 + ((T + 1) * (2 * L.rowW H + 3) + (T + 1) + 2) +
    (2 * (T * L.rowW H) + 2) + 2 + (k1 * (2 * (H * L.g) + 3) + k1 + 2)

/-- The explicit time bound (its polynomial form is `accBound_le`). -/
def accBound (L : Layout) (n1 k1 T H : ℕ) : ℕ :=
  preB L k1 T H + (L.g + n1) * clauseB (L.numVars T H)

theorem encodeCNF_accFam (T H : ℕ) :
    encodeCNF (accFam L n1 ac k1 ea T H) =
      (List.range n1).flatMap (fun u => encodeClause (denseClause (L.numVars T H)
        [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) := by
  simp only [encodeCNF, accFam, List.flatMap_append, List.flatMap_map, codeLits, cellLits]
  rfl

/-- The precomputation: from the input counters to `preF`, at the first clause label. -/
theorem pre_run (T H : ℕ) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (preB L k1 T H)
      ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some GL.start, false, st (preF L k1 T H) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ek) (next := .pre (.w .head)) (x := .Kc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.w s)) (next := .pre (.tw .head))
    (a := .Kc) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.tw s)) (next := .pre .inc)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (incS (M := prog L n1 ac k1 ea) (self := .pre .inc) (next := .pre (.v .head)) (x := .Tn)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.v s)) (next := .pre .cb1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .pre .cb1) (l₂ := .pre .cb2) (next := .pre .cbA)
    rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .cbA) (next := .pre .k1) (x := .CB) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .k1) (next := .pre (.cbM .head)) (x := .K1)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.cbM s)) (next := GL.start)
    (a := .K1) (ad := .md) (b := .HG) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L k1 T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars, Layout.cIdx] <;>
      first | ring1 | (left; ring1)) (Bud.fin ?_ rfl)
  simp [initF, preB, Layout.rowW]
  ring_nf
  omega

/-- **Correctness of the generator, with its explicit time bound.** Started on `T`, `H` (unary)
with empty scratch counters, it reaches `done` within `accBound` steps with exactly the family's
encoding prepended to the output. Hypotheses: the code block fits in `A` (`n1 ≤ A`), `k1` is a
stack (`k1 < KK`), and `H > 0` (there is a top cell). -/
theorem acc_run (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accBound L n1 k1 T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o := by
  refine ⟨false, st (preF L k1 T H) ((List.range n1).flatMap (fun u => encodeClause
    (denseClause (L.numVars T H) [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) ++ o), ?_, by
    rw [encodeCNF_accFam]; rfl⟩
  refine Bud.start ((pre_run (ac := ac) (ea := ea) T H o).bud ?_)
  have hR : Rest (preF L k1 T H) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hW : L.A ≤ L.rowW H := Nat.le_add_right _ _
  have hlt : preF L k1 T H .TW + n1 ≤ L.numVars T H := by
    simp only [preF, Layout.numVars]; rw [Nat.succ_mul]; omega
  have hlc : preF L k1 T H .CB + L.g ≤ L.numVars T H := by
    have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := T) (k := k1) (j := 0) le_rfl hk1 hH
    simp only [preF]
    rw [← Cslib.Complexity.CookLevin.OneHot.base_eq]; simpa using this
  by_cases hg : L.g = 0
  · have hst : (GL.start : GL n1 L.g) = GL.codeStart := by simp [GL.start, hg]
    rw [hst, show List.range L.g = [] by simp [hg], List.flatMap_nil, List.append_nil]
    refine (codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt o).bud
      (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF, hg, zero_add]; omega
  · have hst : (GL.start : GL n1 L.g) = GL.cellFrom (L.g - 1) := by simp [GL.start, hg]
    rw [hst]
    have r := cells_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt hlc (L.g - 1)
      (by omega) o false
    rw [Nat.sub_add_cancel (by omega)] at r
    simp only [List.append_assoc] at r ⊢
    refine r.bud (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF]; rw [Nat.add_mul]; omega

end Top

/-! ## [BOUND] The time bound is polynomial: `accBound ≤ accC · (T + H + 1)^4` -/

section Poly

theorem accBound_mono {L L' : Layout} {n1 n1' k1 k1' T T' H H' : ℕ} (hA : L.A ≤ L'.A)
    (hK : L.KK ≤ L'.KK) (hg : L.g ≤ L'.g) (hn : n1 ≤ n1') (hk : k1 ≤ k1') (hT : T ≤ T')
    (hH : H ≤ H') : accBound L n1 k1 T H ≤ accBound L' n1' k1' T' H' := by
  unfold accBound preB clauseB Layout.numVars Layout.rowW
  gcongr

/-- With all constants `k ≥ 1` and `T = H = y ≥ 1`, every monomial is at most `k⁵ y⁴`; the
coefficients sum to `accBound (uni 1) 1 1 1 1`. -/
theorem accBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    accBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k k y y ≤ 314 * k ^ 5 * y ^ 4 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 4 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 4 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold accBound preB clauseB Layout.numVars Layout.rowW Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 0 3 (by norm_num) (by norm_num),
    m 0 4 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 1 4 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 0 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num),
    m 4 0 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 0 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num)]

/-- The constant 314 is exact: the sum of the coefficients. -/
example : accBound (Cslib.Complexity.CookLevin.Family.Layout.uni 1) 1 1 1 1 = 314 := rfl

/-- The constant of the time bound: depends on `A, KK, g, n1, k1` only. -/
def accC (L : Layout) (n1 k1 : ℕ) : ℕ := 314 * (L.A + L.KK + L.g + n1 + k1 + 1) ^ 5

theorem accBound_le (L : Layout) (n1 k1 T H : ℕ) :
    accBound L n1 k1 T H ≤ accC L n1 k1 * (T + H + 1) ^ 4 := by
  have := accBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + n1 + k1 + 1))
    (n1 := n1) (k1 := k1)
    (n1' := L.A + L.KK + L.g + n1 + k1 + 1) (k1' := L.A + L.KK + L.g + n1 + k1 + 1)
    (T := T) (T' := T + H + 1) (H := H) (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := accBound_uni (L.A + L.KK + L.g + n1 + k1 + 1) (T + H + 1) (by omega) (by omega)
  unfold accC
  exact this.trans h2

/-- **The time-bound target.** -/
theorem acc_time {L : Layout} {n1 ac k1 ea : ℕ} (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ)
    (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accC L n1 k1 * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o :=
  let ⟨v, S, h, h'⟩ := acc_run hn1 hk1 T H hH o; ⟨v, S, h.mono (accBound_le L n1 k1 T H), h'⟩

end Poly

/-! ## [FAM] Link to the semantic family `Situation.Enc.accFamily` -/

section Link

variable {M : FinTM2} (E : Cslib.Complexity.CookLevin.Situation.Enc M)

/-- `Sit`'s accept family *is* this family with `n1 = A0`, `ac = acode`, `k1 = kc k₁`,
`ea = enc k₁ acc`. -/
theorem accFamily_eq (acc : M.Γ M.k₁) (T H : ℕ) :
    E.accFamily acc T H = accFam E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc) T H := rfl

/-- **The accept generator for a real machine**: polynomial time, output `encodeCNF` of
`E.accFamily acc T H`; only `H > 0` is assumed (it holds at `capH`). -/
theorem acc_gen_time (acc : M.Γ M.k₁) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
        (accC E.layout E.A0 (E.kc M.k₁) * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (E.accFamily acc T H) ++ o :=
  acc_time (Nat.le_add_right _ _) (E.kc_lt _) T H hH o

end Link

end Cslib.Complexity.CookLevin.Accept
