/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.CounterView
public import CSLibExt.Computability.Complexity.CookLevin.Family

/-!
# Cook-Levin: the cell one-hot family

Built on the shared counter view `CounterView`. For every `t ≤ T`, `k < KK`, `j < H`, with cell base `B = cIdx H t k j 0`: the
at-least-one clause `⋁_{x<g} C[B+x]`, then the at-most-one clauses `¬C[B+x] ∨ ¬C[B+y]` for
`x < y < g`, each dense over all `V = (T+1)·W` variables. The loops over `t`, `k` and `j` run at
run time (nested `forHead` loops on counters). The module also provides the dense-literal routine
and cell-layout lemmas (`base_le`, `kb_le`, ...) that `Shift` and `Accept` reuse. The final formula
does not use the one-hot family itself (the soundness argument does not need it).
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.OneHot

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc Inc.le encodeClause_denseClause gapEnc_shift inc_of_mono
  denseClause)
open Cslib.Complexity.CookLevin.CounterView

/-! ## [FAM] The family (pure specification) -/

section Spec

/-- At-least-one clause of the cell with base `B`. -/
def aloLits (g B : ℕ) : List (ℕ × Bool) := (List.range g).map fun x => (B + x, true)

/-- At-most-one clause for the pair `x < y` of the cell with base `B`. -/
def amoLits (B x y : ℕ) : List (ℕ × Bool) := [(B + x, false), (B + y, false)]

/-- Pairwise at-most-one clauses of rows `y' < y` (row `y'` = the pairs `x < y'`). -/
def rowsCNF (V B y : ℕ) : CNF :=
  (List.range y).flatMap fun y' => (List.range y').map fun x => denseClause V (amoLits B x y')

/-- All one-hot clauses of one cell. -/
def cellCNF (g V B : ℕ) : CNF := denseClause V (aloLits g B) :: rowsCNF V B g

/-- **The family**: cells ordered by time, stack, depth. -/
def ohFamily (L : Layout) (T H : ℕ) : CNF :=
  (List.range (T + 1)).flatMap fun t => (List.range L.KK).flatMap fun k =>
    (List.range H).flatMap fun j => cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0)

end Spec

/-! ## [FAM] The generator machine -/

/-- Unit-counter stacks of the generator. -/
inductive CK
  | Tn | Ti | Kc | Kd | Hs | Hi | Gc | HG | Wc | Vc | TW | KB | CB | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Kc, CK.Kd, CK.Hs, CK.Hi, CK.Gc, CK.HG, CK.Wc, CK.Vc, CK.TW, CK.KB,
      CK.CB, CK.P, CK.Q, CK.tmp, CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Clause kinds of one cell. -/
inductive CL (g : ℕ)
  | alo
  | amo (x y : Fin g)
  deriving DecidableEq, Fintype

namespace CL

variable {g : ℕ}

/-- Number of literals. -/
def nl : CL g → ℕ
  | alo => g
  | amo _ _ => 2

/-- Offset of literal `l` from the cell base. -/
def off : CL g → ℕ → ℕ
  | alo, l => l
  | amo x y, l => if l = 0 then x else y

/-- Sign of every literal. -/
def sg : CL g → Bool
  | alo => true
  | amo _ _ => false

/-- The pair of an `amo` clause is ordered. -/
def WF : CL g → Prop
  | alo => True
  | amo x y => x.val < y.val

end CL

/-- Precomputation stages. -/
inductive PS
  | inc | eg | hg (s : MS) | ew | ek | w (s : MS) | v (s : MS)
  deriving DecidableEq, Fintype

/-- Stages of the routine emitting one literal. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- Labels, finite from the start (`CL g`, `Fin g` fields). -/
inductive GL (g : ℕ)
  | pre (s : PS)
  | tHead | tRest | tw (s : MS) | tEnd
  | kHead | kRest | kbE | kbC1 | kbC2 | kbM (s : MS) | kEnd
  | jHead | jRest | jbC1 | jbC2 | jbM (s : MS) | jd
  | e00 (c : CL g) | cv1 (c : CL g) | cv2 (c : CL g) | lit (c : CL g) (l : Fin g) (s : LS)
  | fin (c : CL g)
  | done
  deriving DecidableEq, Fintype

namespace GL

variable {g : ℕ}

/-- Literal routine `l` of clause `c` (`done` if out of range; never used then). -/
def litL (c : CL g) (l : ℕ) : GL g := if h : l < g then .lit c ⟨l, h⟩ .cp1 else .done

/-- Where to go before literal `l` (i.e. after literal `l` when counting down): the previous
literal, or the leading gap. -/
def after (c : CL g) (l : ℕ) : GL g := if l = 0 then .fin c else litL c (l - 1)

/-- Clause `amo x y` (`done` if the pair is invalid; never used then). -/
def pr (x y : ℕ) : GL g :=
  if h : x < y ∧ y < g then .e00 (.amo ⟨x, by omega⟩ ⟨y, h.2⟩) else .done

/-- Start of the clauses of rows `< y`, then the at-least-one clause. -/
def yDone (y : ℕ) : GL g := if y ≤ 1 then .e00 .alo else pr (y - 2) (y - 1)

/-- Where to go after clause `c`. -/
def nextC : CL g → GL g
  | .alo => .jd
  | .amo x y => if x.val = 0 then yDone y.val else pr (x.val - 1) y.val

theorem litL_of_lt {c : CL g} {l : ℕ} (h : l < g) : (litL c l : GL g) = .lit c ⟨l, h⟩ .cp1 :=
  dite_eq_left h

theorem pr_of_lt {x y : ℕ} (h1 : x < y) (h2 : y < g) :
    (pr x y : GL g) = .e00 (.amo ⟨x, by omega⟩ ⟨y, h2⟩) := dite_eq_left ⟨h1, h2⟩

end GL

section Machine

variable (L : Layout)

/-- The routine for literal `l` of clause `c`: `Q := CB + off`, the gap down from `P`, the slot,
drain `Q`. -/
def litP (c : CL L.g) (l : Fin L.g) : LS → TM2.Stmt (SΓ CK) (GL L.g) Bool
  | .cp1 => xfer (.c .CB) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c l .cp1) (.lit c l .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c .CB, ()⟩] (.lit c l .cp2) (.lit c l .eo)
  | .eo => emitR (.c .Q) (List.replicate (c.off l) ()) (.lit c l .dec)
  | .dec => decr (.c .P) (.lit c l .bad) (.lit c l .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c l .cmp)
      (.lit c l (.r .lt)) (.lit c l (.r .eq)) (.lit c l (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c l (.r o)) (.lit c l (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c l (.rB o))
      (if o = .eq then .lit c l .slot else .lit c l .emL)
  | .emL => emitR .out [false, true] (.lit c l .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some c.sg)) (.lit c l .dq)
  | .dq => xfer (.c .Q) [] (.lit c l .dq) (GL.after c l)

/-- The generator. Input: `T` on `Tn`, `H` on `Hs`, everything else empty. -/
def prog : GL L.g → TM2.Stmt (SΓ CK) (GL L.g) Bool
  | .pre .inc => incr (.c .Tn) () (.pre .eg)
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Kc) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Kc .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre (.v .head)) s
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) .tHead s
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw .kHead s
  | .kHead => forHead (.c .Kc) (.c .Kd) () .kbE .kRest
  | .kRest => xfer (.c .Kd) [⟨.c .Kc, ()⟩] .kRest .tEnd
  | .tEnd => xfer (.c .TW) [] .tEnd .tHead
  | .kbE => emitR (.c .KB) (List.replicate L.A ()) .kbC1
  | .kbC1 => xfer (.c .TW) [⟨.c .KB, ()⟩, ⟨.c .tmp, ()⟩] .kbC1 .kbC2
  | .kbC2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] .kbC2 (.kbM .head)
  | .kbM s => mulS .Kc .md .HG .KB .tmp .kbM .jHead s
  | .kEnd => xfer (.c .KB) [] .kEnd .kHead
  | .jHead => forHead (.c .Hs) (.c .Hi) () .jbC1 .jRest
  | .jRest => xfer (.c .Hi) [⟨.c .Hs, ()⟩] .jRest .kEnd
  | .jbC1 => xfer (.c .KB) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] .jbC1 .jbC2
  | .jbC2 => xfer (.c .tmp) [⟨.c .KB, ()⟩] .jbC2 (.jbM .head)
  | .jbM s => mulS .Hs .md .Gc .CB .tmp .jbM (GL.yDone L.g) s
  | .jd => xfer (.c .CB) [] .jd .jHead
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (GL.after c c.nl)
  | .lit c l s => litP L c l s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GL.nextC c)
  | .done => .halt

/-- **The generator as a genuine `FinTM2`** (finiteness check only). -/
def ohTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := GL L.g
  main := .pre .inc
  σ := Bool
  initialState := false
  m := prog L

end Machine

/-! ## [FAM] Clause kinds: literal positions -/

section Lits

variable {g : ℕ}

/-- Literals of clause kind `c` in the cell with base `B`. -/
def clits (B : ℕ) (c : CL g) : List (ℕ × Bool) := (List.range c.nl).map fun l => (B + c.off l, c.sg)

theorem clits_alo (B : ℕ) : clits B (.alo : CL g) = aloLits g B := rfl

theorem clits_amo (B : ℕ) (x y : Fin g) : clits B (.amo x y) = amoLits B x y := by
  simp [clits, CL.nl, CL.off, CL.sg, amoLits, List.range_succ]

theorem nl_le {c : CL g} (hc : c.WF) : c.nl ≤ g := by
  cases c with
  | alo => exact le_rfl
  | amo x y => simp only [CL.nl]; have := y.2; simp only [CL.WF] at hc; omega

theorem off_mono {c : CL g} (hc : c.WF) {l : ℕ} (hl : l + 1 < c.nl) : c.off l < c.off (l + 1) := by
  cases c with
  | alo => simp [CL.off]
  | amo x y =>
      simp only [CL.nl] at hl
      obtain rfl : l = 0 := by omega
      simpa [CL.off, CL.WF] using hc

theorem off_lt {c : CL g} {l : ℕ} (hl : l < c.nl) : c.off l < g := by
  cases c with
  | alo => exact hl
  | amo x y => simp only [CL.off]; split_ifs; exact x.2; exact y.2

theorem clits_drop (B : ℕ) (c : CL g) (l : ℕ) :
    (clits B c).drop l = (List.range' l (c.nl - l)).map fun l => (B + c.off l, c.sg) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- The boundary before literal `l`: its position, or `V` past the last literal. -/
def bnd (V B : ℕ) (c : CL g) (l : ℕ) : ℕ := if l < c.nl then B + c.off l else V

theorem inc_drop {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) (l : ℕ) (hl : l ≤ c.nl) :
    Inc (bnd V B c l) ((clits B c).drop l) V := by
  rw [clits_drop]
  refine inc_of_mono _ c.nl V (fun j hj => ?_) (fun j hj => ?_) (c.nl - l) l _ (by omega)
    (fun hn => ?_) (fun _ => ?_)
  · simpa using off_mono hc hj
  · have := off_lt (c := c) (l := j) (by omega); simp only; omega
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show l < c.nl by omega)]; exact le_rfl

theorem bnd_le {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) {l : ℕ} (hl : l ≤ c.nl) :
    bnd V B c l ≤ V := (inc_drop hc hBV l hl).le

theorem bnd_lt {V B : ℕ} {c : CL g} (hc : c.WF) (hBV : B + g ≤ V) {l : ℕ} (hl : l < c.nl) :
    B + c.off l < bnd V B c (l + 1) := by
  unfold bnd
  split_ifs with h
  · exact Nat.add_lt_add_left (off_mono hc h) B
  · have := off_lt hl; omega

end Lits

/-! ## [FAM] Correctness: one literal, one clause -/

section Clause

variable {L : Layout}

/-- Scratch counters that are empty whenever a clause starts. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

/-- One literal: from `P = q + gap + 1`, compute `Q := q = CB + off`, prepend the gap and the
slot, leave `P = q` and the scratch counters empty. -/
theorem lit_run (c : CL L.g) (l : Fin L.g) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F .CB + c.off l) (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L) (gap * (3 * q + 6) + 2 * F .CB + 4 * q + 9)
      ⟨some (.lit c l .cp1), v, st F o⟩
      ⟨some (GL.after c l), false,
        st (update F .P q) (encodeSlot (some c.sg) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  refine Bud.start ?_
  refine (copyS (M := prog L) (l₁ := .lit c l .cp1) (l₂ := .lit c l .cp2) (next := .lit c l .eo)
    rfl rfl (by decide) (by decide) (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L) (self := .lit c l .eo) (next := .lit c l .dec) rfl _ _ _).bud ?_
  refine (gapS (M := prog L) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2) (ys := [false, true])
    (dec := .lit c l .dec) (cmpL := .lit c l .cmp) (emitL := .lit c l .emL)
    (ifZero := .lit c l .bad) (next := .lit c l .slot) (r := fun o => .lit c l (.r o))
    (rB := fun o => .lit c l (.rB o))
    (out := fun o => if o = .eq then .lit c l .slot else .lit c l .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L) (self := .lit c l .slot) (next := .lit c l .dq) rfl _ _ _).bud ?_
  refine (drainS (M := prog L) (self := .lit c l .dq) (next := GL.after c l) (x := .Q) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- Per-literal cost apart from the gap loop. -/
def litE (V : ℕ) : ℕ := 6 * V + 9

/-- Cost of one clause. -/
def clauseB (g V : ℕ) : ℕ := V * (3 * V + 6) + g * litE V + 3 * V + 4

/-- All literals of clause `c`, from the one before `l` down to the first. -/
theorem lits_run {V B : ℕ} {c : CL L.g} (hc : c.WF) (hBV : B + L.g ≤ V) (F : CK → ℕ)
    (hF : Rest F) (hCB : F .CB = B) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L) (bnd V B c l * (3 * V + 6) + l * litE V)
        ⟨some (GL.after c l), v,
          st (update F .P (bnd V B c l)) (gapEnc (bnd V B c l) ((clits B c).drop l) V ++
            [false, false] ++ o)⟩
        ⟨some (.fin c), v',
          st (update F .P (bnd V B c 0)) (gapEnc (bnd V B c 0) (clits B c) V ++
            [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hlg : l < L.g := lt_of_lt_of_le hlm (nl_le hc)
      set p := B + c.off l with hp
      set b := bnd V B c (l + 1) with hb
      have hpb : p < b := bnd_lt hc hBV hlm
      have r := lit_run c ⟨l, hlg⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by simp [hp, hCB]) (by simp; omega)
        (gapEnc b ((clits B c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel, GL.litL_of_lt hlg]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd V B c l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits B c).drop l = (p, c.sg) :: (clits B c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hc hBV (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hc hBV hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hCB]
      rw [Nat.add_one_mul l]
      unfold litE
      omega

/-- One whole clause: from `e00 c` to `nextC c`, all counters restored. -/
theorem clause_run {V B : ℕ} {c : CL L.g} (hc : c.WF) (hBV : B + L.g ≤ V) (F : CK → ℕ)
    (hF : Rest F) (hCB : F .CB = B) (hV : F .Vc = V) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L) (clauseB L.g V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GL.nextC c), false, st F (encodeClause (denseClause V (clits B c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := GL.after c c.nl) rfl rfl
    (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run hc hBV F hF hCB o c.nl le_rfl false
  have hbm : bnd V B c c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L) (self := .fin c) (next := GL.nextC c) (x := .P) rfl _ _ _).bud ?_
  have e1 : update (update F .P (bnd V B c 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hc hBV 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits B c)) =
      rep [false, true] (bnd V B c 0) ++ gapEnc (bnd V B c 0) (clits B c) V ++ [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hc hBV (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) (nl_le hc)
  unfold clauseB
  omega

end Clause

/-! ## [FAM] Correctness: the clauses of one cell (a 2-D label chain) -/

section Cell

variable {L : Layout}

theorem alo_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L) (clauseB L.g V) ⟨some (.e00 .alo), v, st F o⟩
      ⟨some .jd, false, st F (encodeClause (denseClause V (aloLits L.g B)) ++ o)⟩ :=
  clause_run (c := .alo) True.intro hBV F hF hCB hV hP o v

/-- Row `y` of the at-most-one clauses, pairs `x, x-1, …, 0`. -/
theorem row_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) {y : ℕ} (hy : y < L.g) :
    ∀ x, x < y → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L) ((x + 1) * clauseB L.g V) ⟨some (GL.pr x y), v, st F o⟩
        ⟨some (GL.yDone y), false, st F ((List.range (x + 1)).flatMap
          (fun x' => encodeClause (denseClause V (amoLits B x' y))) ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro hx o v
      have r := clause_run (c := .amo ⟨0, by omega⟩ ⟨y, hy⟩) hx hBV F hF hCB hV hP o v
      rw [GL.pr_of_lt hx hy]
      simpa [GL.nextC, clits_amo] using r
  | succ x ih =>
      intro hx o v
      have r := clause_run (c := .amo ⟨x + 1, by omega⟩ ⟨y, hy⟩) hx hBV F hF hCB hV hP o v
      simp only [GL.nextC, clits_amo, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at r
      rw [GL.pr_of_lt hx hy]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V (amoLits B (x + 1) y)) ++ o) false
      rw [List.range_succ (n := x + 1), List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (x + 1)]; omega

theorem encodeCNF_rows_succ (g V B y : ℕ) :
    encodeCNF (denseClause V (aloLits g B) :: rowsCNF V B (y + 1)) =
      encodeCNF (denseClause V (aloLits g B) :: rowsCNF V B y) ++
        (List.range y).flatMap (fun x => encodeClause (denseClause V (amoLits B x y))) := by
  simp [encodeCNF, rowsCNF, List.range_succ, List.flatMap_append, List.append_assoc,
    List.flatMap_map]

/-- All rows `< y`, then the at-least-one clause. -/
theorem rows_run {V B : ℕ} (hBV : B + L.g ≤ V) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = B)
    (hV : F .Vc = V) (hP : F .P = 0) :
    ∀ y, y ≤ L.g → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L) ((1 + y * y) * clauseB L.g V) ⟨some (GL.yDone y), v, st F o⟩
        ⟨some .jd, false,
          st F (encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B y) ++ o)⟩ := by
  intro y
  induction y with
  | zero =>
      intro _ o v
      have r := alo_run hBV F hF hCB hV hP o v
      simp only [GL.yDone, zero_le, ite_true]
      have e : encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B 0) ++ o =
          encodeClause (denseClause V (aloLits L.g B)) ++ o := by simp [encodeCNF, rowsCNF]
      rw [e]; exact r.mono (by simp)
  | succ y ih =>
      intro hy o v
      by_cases hy0 : y = 0
      · subst hy0
        have r := alo_run hBV F hF hCB hV hP o v
        simp only [GL.yDone, le_refl, ite_true]
        have e : encodeCNF (denseClause V (aloLits L.g B) :: rowsCNF V B (0 + 1)) ++ o =
            encodeClause (denseClause V (aloLits L.g B)) ++ o := by simp [encodeCNF, rowsCNF]
        rw [e]; exact r.mono (by simp; omega)
      · rw [GL.yDone, ite_eq_right (by omega), show y + 1 - 2 = y - 1 by omega, Nat.add_sub_cancel]
        have r := row_run hBV F hF hCB hV hP (y := y) (by omega) (y - 1) (by omega) o v
        rw [show y - 1 + 1 = y by omega] at r
        refine Bud.start (r.bud ?_)
        have := ih (by omega) ((List.range y).flatMap
          (fun x => encodeClause (denseClause V (amoLits B x y))) ++ o) false
        rw [encodeCNF_rows_succ, List.append_assoc]
        refine this.bud (Bud.fin ?_ rfl)
        nlinarith [Nat.zero_le (clauseB L.g V), Nat.zero_le (y * clauseB L.g V)]

/-- Cost of one cell (one iteration of the `j` loop). -/
def cellB (g H V : ℕ) : ℕ :=
  2 * V + 2 + (H * (2 * g + 3) + H + 2) + (1 + g * g) * clauseB g V + V + 1

/-- One cell (the body of the `j` loop): `CB := KB + j·g`, all its clauses, drain `CB`. -/
theorem cell_run {V H j B : ℕ} (hj : j < H) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hHs : F .Hs = j)
    (hB : j * L.g + F .KB = B) (hBV : B + L.g ≤ V) (o : List Bool) (v : Bool) :
    RunLe (prog L) (cellB L.g H V) ⟨some .jbC1, v, st F o⟩
      ⟨some .jHead, false, st F (encodeCNF (cellCNF L.g V B) ++ o)⟩ := by
  refine Bud.start ?_
  refine (copyS (M := prog L) (l₁ := .jbC1) (l₂ := .jbC2) (next := .jbM .head) rfl rfl
    (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L) (mk := .jbM) (next := GL.yDone L.g) (a := .Hs) (ad := .md)
    (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .CB B) (by funext x; cases x <;> simp [hHs, hG, hCB, ← hB]) ?_
  have hF' : Rest (update F .CB B) :=
    hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) B
  refine (rows_run hBV _ hF' (by simp) (by simp [hV]) (by simp [hP]) L.g le_rfl o _).bud ?_
  refine (drainS (M := prog L) (self := .jd) (next := .jHead) (x := .CB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) hj.le
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hHs, hG, hCB]
    unfold cellB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB]

end Cell

/-! ## [FAM] Correctness: the three nested runtime loops and the whole generator -/

section Top

variable {L : Layout}

theorem kb_le {T H t k : ℕ} (ht : t ≤ T) (hk : k < L.KK) :
    k * (H * L.g) + (t * L.rowW H + L.A) ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_le {T H t k j : ℕ} (ht : t ≤ T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) + L.g ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h1 : j * L.g + L.g ≤ H * L.g := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_eq (H t k j : ℕ) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) = L.cIdx H t k j 0 := by
  unfold Layout.cIdx; ring

/-- Encoded clauses of the cells `(t, k, ·)`. -/
def blkK (L : Layout) (T H t k : ℕ) : List Bool :=
  (List.range H).flatMap fun j => encodeCNF (cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0))

/-- Encoded clauses of time step `t`. -/
def blkT (L : Layout) (T H t : ℕ) : List Bool := (List.range L.KK).flatMap (blkK L T H t)

/-- Cost of one iteration of the `k` loop. -/
def kBodyB (g KK H V : ℕ) : ℕ :=
  1 + (2 * V + 2) + (KK * (2 * (H * g) + 3) + KK + 2) + (H * (cellB g H V + 1) + H + 2) + V + 1

/-- One iteration of the `k` loop: `KB := t·W + A + k·(H·g)`, the `j` loop, drain `KB`. -/
theorem kbody_run {T H t k : ℕ} (ht : t ≤ T) (hk : k < L.KK) (F : CK → ℕ) (hF : Rest F)
    (hCB : F .CB = 0) (hP : F .P = 0) (hKB : F .KB = 0) (hV : F .Vc = L.numVars T H)
    (hG : F .Gc = L.g) (hHG : F .HG = H * L.g) (hHs : F .Hs = H) (hHi : F .Hi = 0)
    (hTW : F .TW = t * L.rowW H) (hKc : F .Kc = k) (o : List Bool) (v : Bool) :
    RunLe (prog L) (kBodyB L.g L.KK H (L.numVars T H)) ⟨some .kbE, v, st F o⟩
      ⟨some .kHead, false, st F (blkK L T H t k ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L) (self := .kbE) (next := .kbC1) (x := .KB) rfl _ _ _).bud ?_
  refine (copyS (M := prog L) (l₁ := .kbC1) (l₂ := .kbC2) (next := .kbM .head) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) v o).bud ?_
  refine (mulS_run (M := prog L) (mk := .kbM) (next := .jHead) (a := .Kc) (ad := .md)
    (b := .HG) (c := .KB) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  set KBv := k * (H * L.g) + (t * L.rowW H + L.A) with hKBv
  refine bud_st (F' := update F .KB KBv) (by
    funext x; cases x <;> simp [hKc, hHG, hTW, hKB, hKBv]) ?_
  have hloop := stLoop (M := prog L) (c := .Hs) (cd := .Hi) (head := .jHead) (body := .jbC1)
    (rest := .jRest) (next := .kEnd) rfl rfl (by decide) H (cellB L.g H (L.numVars T H))
    (fun j => encodeCNF (cellCNF L.g (L.numVars T H) (L.cIdx H t k j 0)))
    (update F .KB KBv) (by simp [hHs]) (by simp [hHi])
    (fun j hj o' => ⟨false, cell_run hj _
      ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
      (by simp [hCB]) (by simp [hP]) (by simp [hV]) (by simp [hG]) (by simp)
      (by simp [hKBv, base_eq]) (by rw [← base_eq]; exact base_le ht hk hj) o' true⟩)
    false o
  refine hloop.bud ?_
  refine (drainS (M := prog L) (self := .kEnd) (next := .kHead) (x := .KB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := kb_le (H := H) ht hk
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.mul_le_mul_right (2 * (H * L.g) + 3) hk.le
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKc, hHG, hTW,
      hKB]
    unfold kBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hKB]

/-- Cost of one iteration of the time loop. -/
def tBodyB (L : Layout) (T H : ℕ) : ℕ :=
  T * (2 * L.rowW H + 3) + T + 2 + (L.KK * (kBodyB L.g L.KK H (L.numVars T H) + 1) + L.KK + 2) +
    L.numVars T H + 1

/-- One iteration of the time loop: `TW := t·W`, the `k` loop, drain `TW`. -/
theorem tbody_run {T H t : ℕ} (ht : t ≤ T) (F : CK → ℕ) (hF : Rest F)
    (hCB : F .CB = 0) (hP : F .P = 0) (hKB : F .KB = 0) (hTW : F .TW = 0)
    (hV : F .Vc = L.numVars T H) (hG : F .Gc = L.g) (hHG : F .HG = H * L.g) (hHs : F .Hs = H)
    (hHi : F .Hi = 0) (hWc : F .Wc = L.rowW H) (hKc : F .Kc = L.KK) (hKd : F .Kd = 0)
    (hTn : F .Tn = t) (o : List Bool) (v : Bool) :
    RunLe (prog L) (tBodyB L T H) ⟨some (.tw .head), v, st F o⟩
      ⟨some .tHead, false, st F (blkT L T H t ++ o)⟩ := by
  refine Bud.start ?_
  refine (mulS_run (M := prog L) (mk := .tw) (next := .kHead) (a := .Tn) (ad := .md)
    (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .TW (t * L.rowW H)) (by
    funext x; cases x <;> simp [hTn, hWc, hTW]) ?_
  have hloop := stLoop (M := prog L) (c := .Kc) (cd := .Kd) (head := .kHead) (body := .kbE)
    (rest := .kRest) (next := .tEnd) rfl rfl (by decide) L.KK (kBodyB L.g L.KK H (L.numVars T H))
    (blkK L T H t) (update F .TW (t * L.rowW H)) (by simp [hKc]) (by simp [hKd])
    (fun k hk o' => ⟨false, kbody_run ht hk _
      ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
      (by simp [hCB]) (by simp [hP]) (by simp [hKB]) (by simp [hV]) (by simp [hG])
      (by simp [hHG]) (by simp [hHs]) (by simp [hHi]) (by simp) (by simp) o' true⟩)
    false o
  refine hloop.bud ?_
  refine (drainS (M := prog L) (self := .tEnd) (next := .tHead) (x := .TW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    simp only [update_self, hTn, hWc]
    unfold tBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hTW]

/-- Initial counters: `T` on `Tn`, `H` on `Hs`. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- Counters after the precomputation. -/
def preF (L : Layout) (T H : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Kc => L.KK
  | .Vc => L.numVars T H
  | _ => 0

/-- Cost of the precomputation. -/
def preB (L : Layout) (T H : ℕ) : ℕ :=
  4 + (H * (2 * L.g + 3) + H + 2) + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) +
    ((T + 1) * (2 * L.rowW H + 3) + (T + 1) + 2)

/-- The explicit time bound (its polynomial form is `ohBound_le`). -/
def ohBound (L : Layout) (T H : ℕ) : ℕ := preB L T H + ((T + 1) * (tBodyB L T H + 1) + (T + 1) + 2)

theorem encodeCNF_ohFamily (T H : ℕ) :
    encodeCNF (ohFamily L T H) = (List.range (T + 1)).flatMap (blkT L T H) := by
  simp [encodeCNF, ohFamily, List.flatMap_assoc]; rfl

/-- **Correctness of the generator, with its explicit time bound.** Started on `T`, `H` (unary)
with empty scratch counters, it reaches `done` within `ohBound` steps with exactly the family's
encoding prepended to the output. -/
theorem oh_run (T H : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L) (ohBound L T H)
        ⟨some (.pre .inc), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (ohFamily L T H) ++ o := by
  refine ⟨false, st (preF L T H) (encodeCNF (ohFamily L T H) ++ o), ?_, rfl⟩
  refine Bud.start ?_
  refine (incS (M := prog L) (self := .pre .inc) (next := .pre .eg) (x := .Tn) rfl _ _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc) rfl _ _
    _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.hg s)) (next := .pre .ew) (a := .Hs)
    (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [initF])
    (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _ _).bud ?_
  refine (emitS (M := prog L) (self := .pre .ek) (next := .pre (.w .head)) (x := .Kc) rfl _ _
    _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.w s)) (next := .pre (.v .head))
    (a := .Kc) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (mulS_run (M := prog L) (mk := fun s => .pre (.v s)) (next := .tHead)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars] <;> ring) ?_
  have hloop := stLoop (M := prog L) (c := .Tn) (cd := .Ti) (head := .tHead) (body := .tw .head)
    (rest := .tRest) (next := .done) rfl rfl (by decide) (T + 1) (tBodyB L T H)
    (blkT L T H) (preF L T H) rfl rfl
    (fun t ht o' => ⟨false, tbody_run (by omega) _
      ⟨by simp [preF], by simp [preF], by simp [preF], by simp [preF], by simp [preF]⟩
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp) o' true⟩)
    false o
  rw [← encodeCNF_ohFamily] at hloop
  refine hloop.bud (Bud.fin ?_ rfl)
  simp [initF, preB, ohBound, Layout.rowW]
  ring_nf
  omega

end Top

/-! ## [BOUND] The time bound is polynomial: `ohBound ≤ ohC · (T + H + 1)^6` -/

section Poly

theorem ohBound_mono {L L' : Layout} {T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hT : T ≤ T') (hH : H ≤ H') : ohBound L T H ≤ ohBound L' T' H' := by
  unfold ohBound preB tBodyB kBodyB cellB clauseB litE Layout.numVars Layout.rowW
  gcongr

/-- With all constants `k ≥ 1` and `T = H = y ≥ 1`, every monomial is at most `k⁷ y⁶` and the
coefficients sum to 668 (the value at `k = y = 1`). -/
theorem ohBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    ohBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) y y ≤ 668 * k ^ 7 * y ^ 6 := by
  have m : ∀ a b, a ≤ 7 → b ≤ 6 → k ^ a * y ^ b ≤ k ^ 7 * y ^ 6 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold ohBound preB tBodyB kBodyB cellB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 4 5 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num),
    m 5 5 (by norm_num) (by norm_num),
    m 5 6 (by norm_num) (by norm_num),
    m 6 2 (by norm_num) (by norm_num),
    m 6 3 (by norm_num) (by norm_num),
    m 6 4 (by norm_num) (by norm_num),
    m 6 5 (by norm_num) (by norm_num),
    m 7 3 (by norm_num) (by norm_num),
    m 7 4 (by norm_num) (by norm_num),
    m 7 5 (by norm_num) (by norm_num),
    m 7 6 (by norm_num) (by norm_num)]

/-- The constant of the time bound: depends on `A, KK, g` only. -/
def ohC (L : Layout) : ℕ := 668 * (L.A + L.KK + L.g + 1) ^ 7

theorem ohBound_le (L : Layout) (T H : ℕ) : ohBound L T H ≤ ohC L * (T + H + 1) ^ 6 := by
  have := ohBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + 1))
    (T := T) (T' := T + H + 1) (H := H) (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega)
  have h2 := ohBound_uni (L.A + L.KK + L.g + 1) (T + H + 1) (by omega) (by omega)
  unfold ohC
  exact this.trans h2

open Polynomial in
/-- The bound as a `Polynomial ℕ` in `T + H`. -/
noncomputable def ohPoly (L : Layout) : Polynomial ℕ := C (ohC L) * (X + 1) ^ 6

theorem ohPoly_eval (L : Layout) (T H : ℕ) : (ohPoly L).eval (T + H) = ohC L * (T + H + 1) ^ 6 := by
  simp [ohPoly]

/-- **The time bound**: the generator emits the family within a polynomial number of steps. -/
theorem oh_time {L : Layout} (T H : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L) (ohC L * (T + H + 1) ^ 6)
        ⟨some (.pre .inc), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (ohFamily L T H) ++ o :=
  let ⟨v, S, h, h'⟩ := oh_run T H o; ⟨v, S, h.mono (ohBound_le L T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.OneHot
