/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3Shift.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3Shift.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); module docstring rewritten for this repository (the source's notes and status
lines dropped), missing docstrings added, long lines wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.OneHot

/-!
# Cook-Levin: generator machine for the cell-shift family

The stack contents of the verifier are a table of cells `C[t, k, j, x]` (time `t`, stack `k`, depth
`j`, symbol code `x`). With a situation variable `S[t, i]` for situation `i` at time `t`, and for
`t < T`, `i < N`, `k < KK`, `p = pl i k` (symbols pushed and still on top), `c = cn i k` (original
symbols consumed), `m = max p c`, the family is:
* in-range shifts, `u < H − m`, `x < g`: `¬C[t,k,u+c,x] ∨ ¬S[t,i] ∨ C[t+1,k,u+p,x]`;
* overflow fill (`c > p`), `r < c − p`: `¬S[t,i] ∨ C[t+1,k,H−c+p+r,0]` (code `0` is the empty
  cell);
* pushed fill, `j < p`: `¬S[t,i] ∨ C[t+1,k,j,pu i k j]` (`pu i k j` codes the pushed symbol at
  depth `j`).

Each clause is dense over all `V = (T+1)·W` variables. `shFamily` is the family, `prog` the
counter machine emitting it, and `sh_time` its run with a polynomial step bound. `T` and
`H` are runtime inputs in unary; the `t`, `u`, `r` loops run at run time, while `i`, `k`, `x` and
the pushed-fill `j` are label chains.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Shift

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc Inc.le encodeClause_denseClause gapEnc_shift inc_of_mono denseClause cIdx_lt_next_row)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out update_st_c emitS emitOut incS
  drainS xferES copyS mulS mulS_run gapS bud_st stLoop)

/-! ## [LIB] Decrement in the counter view -/

theorem decS {C Λ : Type} [DecidableEq C] {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {self ifZero ifPos : Λ}
    {x : C} (hp : M self = decr (.c x) ifZero ifPos) (F : C → ℕ) (n : ℕ) (hF : F x = n + 1)
    (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x n) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := n) (by simp [hF])
  rw [update_st_c] at this
  exact this

/-! ## [FAM] The family (pure specification) -/

section Spec

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ)

/-- In-range shift clause `(t, i, k, u, x)`: `¬C[t,k,u+c,x] ∨ ¬S[t,i] ∨ C[t+1,k,u+p,x]`, with
`S[t,i]` at `xIdx H (t+1) (sa i)` (sorted: row `t` cell < row `t+1` situation block < row `t+1`
cell). -/
def shLits (H t i k u x : ℕ) : List (ℕ × Bool) :=
  [(L.cIdx H t k (u + cn i k) x, false), (L.xIdx H (t + 1) (sa i), false),
    (L.cIdx H (t + 1) k (u + pl i k) x, true)]

/-- Overflow clause `(t, i, k, r)`: `¬S[t,i] ∨ C[t+1,k,H−c+p+r,⊥]`. -/
def ovLits (H t i k r : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0, true)]

/-- Pushed-fill clause `(t, i, k, j)`, `j < p`: `¬S[t,i] ∨ C[t+1,k,j,pu i k j]`. -/
def pfLits (H t i k j : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k j (pu i k j), true)]

/-- The block of situation `i`, stack `k` at time `t`: in-range shifts, overflow fills, pushed
fills. -/
def shBlk (T H t i k : ℕ) : CNF :=
  ((List.range (H - max (pl i k) (cn i k))).flatMap fun u =>
      (List.range L.g).map fun x => denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x)) ++
    ((List.range (cn i k - pl i k)).map fun r =>
      denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++
    (List.range (pl i k)).map fun j => denseClause (L.numVars T H) (pfLits L sa pu H t i k j)

/-- **The family**: blocks ordered by time, situation, stack. -/
def shFamily (N T H : ℕ) : CNF :=
  (List.range T).flatMap fun t => (List.range N).flatMap fun i =>
    (List.range L.KK).flatMap fun k => shBlk L sa pl cn pu T H t i k

/-- Well-formedness: codes in range, shifts within the window, window within the height. -/
structure WF (N H : ℕ) : Prop where
  g_pos : 0 < L.g
  d_le : L.d ≤ H
  sa_lt : ∀ i < N, sa i < L.A
  pl_le : ∀ i < N, ∀ k < L.KK, pl i k ≤ L.d
  cn_le : ∀ i < N, ∀ k < L.KK, cn i k ≤ L.d
  pu_lt : ∀ i < N, ∀ k < L.KK, ∀ j < pl i k, pu i k j < L.g

/-- **Coverage of target depths** (C2/C5 need it): every depth `j < H` of a stack in row `t+1` is
a pushed-fill target (`j < p`), an in-range target (`j = u + p`, `u < H − m`) or an overflow target
(`j = H − c + p + r`, `r < c − p`). -/
theorem depth_cover {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) (j : ℕ) (hj : j < H) :
    j < p ∨ (∃ u < H - max p c, j = u + p) ∨ (∃ r < c - p, j = H - c + p + r) := by
  by_cases h1 : j < p
  · exact Or.inl h1
  by_cases h2 : j < H - max p c + p
  · exact Or.inr (Or.inl ⟨j - p, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨j - (H - c + p), by omega, by omega⟩)

/-- The three regions are disjoint and in range: in-range targets lie in `[p, H − c + p)`, overflow
targets in `[H − m + p, H)` (and `H − m + p = H − c + p` when `r` exists). -/
theorem depth_disjoint {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) :
    (∀ u < H - max p c, p ≤ u + p ∧ u + p < H - c + p ∧ u + p < H) ∧
    (∀ r < c - p, H - max p c + p = H - c + p ∧ H - c + p + r < H) := by
  constructor <;> intro _ _ <;> omega

end Spec

/-! ## [FAM] The generator machine -/

/-- Unit-counter stacks of the generator. -/
inductive CK
  | Tn | Ti | Hs | Gc | HG | Wc | Vc | TW | TW1 | KB | U | Ui | R | Ri | CB | CW | P | Q | tmp | md | Ka
  | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Vc, CK.TW, CK.TW1, CK.KB, CK.U, CK.Ui,
      CK.R, CK.Ri, CK.CB, CK.CW, CK.P, CK.Q, CK.tmp, CK.md, CK.Ka, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Base counter of a literal position (`s`: `TW1 = (t+1)·W`, for the situation variable). -/
inductive BS | s | cb | cw
  deriving DecidableEq
instance BS.instFintypeEnumFix : Fintype BS where
  elems := ⟨↑[BS.s, BS.cb, BS.cw], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The counter holding each base. -/
def BS.k : BS → CK
  | .s => .TW1
  | .cb => .CB
  | .cw => .CW

/-- Clause kinds of an `(i, k)` block. -/
inductive CL (g d : ℕ)
  | sh (x : Fin g)
  | ov
  | pf (j : Fin d)
  deriving DecidableEq, Fintype

namespace CL

variable {g d : ℕ}

/-- Number of literals. -/
def nl : CL g d → ℕ
  | sh _ => 3
  | ov => 2
  | pf _ => 2

/-- Base counter of literal `l`. -/
def bs : CL g d → ℕ → BS
  | sh _, l => if l = 0 then .cb else if l = 1 then .s else .cw
  | ov, l => if l = 0 then .s else .cw
  | pf _, l => if l = 0 then .s else .cw

/-- Constant offset of literal `l` (situation offset `s`, push count `p`, consumed count `c`,
pushed codes `q`). -/
def cs (s p c : ℕ) (q : ℕ → ℕ) : CL g d → ℕ → ℕ
  | sh x, l => if l = 0 then c * g + x else if l = 1 then s else p * g + x
  | ov, l => if l = 0 then s else p * g
  | pf j, l => if l = 0 then s else j.val * g + q j.val

/-- Sign of literal `l`: only the last one is positive. -/
def sg (cl : CL g d) (l : ℕ) : Bool := decide (l + 1 = cl.nl)

theorem nl_le (cl : CL g d) : cl.nl ≤ 3 := by cases cl <;> simp [nl]

end CL

/-- Precomputation stages. -/
inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | dk | v (s : MS) | vw1 | vw2
  deriving DecidableEq, Fintype

/-- Stages of the routine emitting one literal. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- Setup/loop stages of an `(i, k)` block. -/
inductive ST
  | kbE | kbC1 | kbC2 | kbK | kbM (s : MS) | kbD | uC1 | uC2
  | oE | oHead | oRest | oC1 | oC2 | oR1 | oR2 | oM (s : MS) | oD
  | sHead | sRest | dU | dR | dKB
  | fC1 | fC2 | fW1 | fW2 | fD1
  deriving DecidableEq, Fintype

/-- Loop-body stages of an `(i, k)` block. The flag `b` is `true` in the in-range loop, `false` in
the overflow loop. -/
inductive BD (g d : ℕ)
  | bC1 (b : Bool) | bC2 (b : Bool) | sM (s : MS)
  | w1 (b : Bool) | w2 (b : Bool) | w3 (b : Bool) | w4 (b : Bool)
  | e00 (c : CL g d) | cv1 (c : CL g d) | cv2 (c : CL g d) | lit (c : CL g d) (l : Fin 3) (s : LS)
  | fin (c : CL g d)
  | dCB (b : Bool) | dCW (b : Bool)
  deriving DecidableEq, Fintype

/-- Labels, finite: situations `Fin N`, stacks `Fin KK`, symbols `Fin g`, decrements `Fin (d+1)`,
pushed depths `Fin d`. -/
inductive GL (N KK g d : ℕ)
  | pre (s : PS)
  | tHead | tRest | tw (s : MS) | t1a | t1b | t1c | t1d | tEnd | tEnd2
  | s (i : Fin N) (k : Fin KK) (x : ST)
  | sb (i : Fin N) (k : Fin KK) (r : Fin (d + 1))
  | b (i : Fin N) (k : Fin KK) (x : BD g d)
  | bad | done
  deriving DecidableEq, Fintype

namespace GL

variable {N KK g d : ℕ}

/-- Literal routine `l` of clause `c` (`done` if out of range; never used then). -/
def litL (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GL N KK g d :=
  if h : l < 3 then .b i k (.lit c ⟨l, h⟩ .cp1) else .done

/-- Where to go before literal `l` (counting down): the previous literal, or the leading gap. -/
def after (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GL N KK g d :=
  if l = 0 then .b i k (.fin c) else litL i k c (l - 1)

/-- In-range clauses `x < n` of the current cell pair, then the drains. -/
def xFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .b i k (.dCB true) else if h : n - 1 < g then .b i k (.e00 (.sh ⟨n - 1, h⟩))
  else .done

/-- Pushed-fill clauses `j < n`, then the fill drains. -/
def pfFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .s i k .fD1 else if h : n - 1 < d then .b i k (.e00 (.pf ⟨n - 1, h⟩)) else .done

/-- Where to go after clause `c`. -/
def nextC (i : Fin N) (k : Fin KK) : CL g d → GL N KK g d
  | .sh x => xFrom i k x.val
  | .ov => .b i k (.dCB false)
  | .pf j => pfFrom i k j.val

/-- `n` decrements of `U` still to do, then the pushed-fill setup. -/
def sbL (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .s i k .fC1 else if h : n - 1 < d + 1 then .sb i k ⟨n - 1, h⟩ else .done

/-- Blocks of situations `< n`, then the end of the time step. -/
def iFrom (n : ℕ) : GL N KK g d :=
  if n = 0 then .tEnd
  else if h : n - 1 < N ∧ 0 < KK then .s ⟨n - 1, h.1⟩ ⟨KK - 1, by omega⟩ .kbE
  else if KK = 0 then .tEnd else .done

/-- Blocks of stacks `< n` of situation `i`, then situations `< i`. -/
def ik (i n : ℕ) : GL N KK g d :=
  if n = 0 then iFrom i else if h : i < N ∧ n - 1 < KK then .s ⟨i, h.1⟩ ⟨n - 1, h.2⟩ .kbE
  else .done

theorem litL_of_lt {i : Fin N} {k : Fin KK} {c : CL g d} {l : ℕ} (h : l < 3) :
    (litL i k c l : GL N KK g d) = .b i k (.lit c ⟨l, h⟩ .cp1) := dite_eq_left h

theorem xFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < g) :
    (xFrom i k (n + 1) : GL N KK g d) = .b i k (.e00 (.sh ⟨n, h⟩)) := by
  simp [xFrom, h]

theorem pfFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d) :
    (pfFrom i k (n + 1) : GL N KK g d) = .b i k (.e00 (.pf ⟨n, h⟩)) := by
  simp [pfFrom, h]

theorem sbL_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d + 1) :
    (sbL i k (n + 1) : GL N KK g d) = .sb i k ⟨n, h⟩ := by
  simp [sbL, h]

theorem ik_succ {i n : ℕ} (hi : i < N) (hn : n < KK) :
    (ik i (n + 1) : GL N KK g d) = .s ⟨i, hi⟩ ⟨n, hn⟩ .kbE := by
  simp [ik, hi, hn]

theorem iFrom_succ {n : ℕ} (hn : n < N) (hK : 0 < KK) :
    (iFrom (n + 1) : GL N KK g d) = ik n KK := by
  have h1 : KK - 1 < KK := by omega
  simp [iFrom, ik, hn, hK, h1, hK.ne']

theorem iFrom_KK0 (hK : KK = 0) (n : ℕ) : (iFrom n : GL N KK g d) = .tEnd := by
  unfold iFrom; split_ifs <;> first | rfl | omega

end GL

section Machine

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

/-- Labels of the generator. -/
abbrev Lab := GL N L.KK L.g L.d

/-- Constant offset of literal `l` of clause `c` in block `(i, k)`. -/
def csv (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : ℕ) : ℕ :=
  c.cs (sa i) (pl i k) (cn i k) (pu i k) l

/-- The routine for literal `l` of clause `c`: `Q := base + const`, the gap down from `P`, the
slot, drain `Q`. -/
def litP (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) :
    LS → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .cp1 => xfer (.c (c.bs l).k) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.lit c l .cp1))
      (.b i k (.lit c l .cp2))
  | .cp2 => xfer (.c .tmp) [⟨.c (c.bs l).k, ()⟩] (.b i k (.lit c l .cp2)) (.b i k (.lit c l .eo))
  | .eo => emitR (.c .Q) (List.replicate (csv L sa pl cn pu N i k c l) ()) (.b i k (.lit c l .dec))
  | .dec => decr (.c .P) (.b i k (.lit c l .bad)) (.b i k (.lit c l .cmp))
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.b i k (.lit c l .cmp))
      (.b i k (.lit c l (.r .lt))) (.b i k (.lit c l (.r .eq))) (.b i k (.lit c l (.r .gt)))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.b i k (.lit c l (.r o))) (.b i k (.lit c l (.rB o)))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.b i k (.lit c l (.rB o)))
      (if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
  | .emL => emitR .out [false, true] (.b i k (.lit c l .dec))
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg l))) (.b i k (.lit c l .dq))
  | .dq => xfer (.c .Q) [] (.b i k (.lit c l .dq)) (GL.after i k c l)

/-- Stages of block `(i, k)`: `KB := TW + A + k·HG`, `U := H − m`, the pushed-fill chain
(`CW := KB + W`), `R := c − p`, the overflow loop, the in-range loop, drains. -/
def stP (i : Fin N) (k : Fin L.KK) : ST → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .kbE => emitR (.c .KB) (List.replicate L.A ()) (.s i k .kbC1)
  | .kbC1 => xfer (.c .TW) [⟨.c .KB, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .kbC1) (.s i k .kbC2)
  | .kbC2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.s i k .kbC2) (.s i k .kbK)
  | .kbK => emitR (.c .Ka) (List.replicate k.val ()) (.s i k (.kbM .head))
  | .kbM s => mulS .Ka .md .HG .KB .tmp (fun s => .s i k (.kbM s)) (.s i k .kbD) s
  | .kbD => xfer (.c .Ka) [] (.s i k .kbD) (.s i k .uC1)
  | .uC1 => xfer (.c .Hs) [⟨.c .U, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .uC1) (.s i k .uC2)
  | .uC2 => xfer (.c .tmp) [⟨.c .Hs, ()⟩] (.s i k .uC2) (GL.sbL i k (max (pl i k) (cn i k)))
  | .oE => emitR (.c .R) (List.replicate (cn i k - pl i k) ()) (.s i k .oHead)
  -- overflow loop over `r < c − p`: `CB := (U + r)·g`, then the shared body adds `KB`
  | .oHead => forHead (.c .R) (.c .Ri) () (.s i k .oC1) (.s i k .oRest)
  | .oRest => xfer (.c .Ri) [⟨.c .R, ()⟩] (.s i k .oRest) (.s i k .sHead)
  | .oC1 => xfer (.c .U) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oC1) (.s i k .oC2)
  | .oC2 => xfer (.c .tmp) [⟨.c .U, ()⟩] (.s i k .oC2) (.s i k .oR1)
  | .oR1 => xfer (.c .R) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oR1) (.s i k .oR2)
  | .oR2 => xfer (.c .tmp) [⟨.c .R, ()⟩] (.s i k .oR2) (.s i k (.oM .head))
  | .oM s => mulS .Ka .md .Gc .CB .tmp (fun s => .s i k (.oM s)) (.s i k .oD) s
  | .oD => xfer (.c .Ka) [] (.s i k .oD) (.b i k (.bC1 false))
  -- in-range loop over `u < H − m`
  | .sHead => forHead (.c .U) (.c .Ui) () (.b i k (.bC1 true)) (.s i k .sRest)
  | .sRest => xfer (.c .Ui) [⟨.c .U, ()⟩] (.s i k .sRest) (.s i k .dU)
  | .dU => xfer (.c .U) [] (.s i k .dU) (.s i k .dR)
  | .dR => xfer (.c .R) [] (.s i k .dR) (.s i k .dKB)
  | .dKB => xfer (.c .KB) [] (.s i k .dKB) (GL.ik i.val k.val)
  -- pushed fill: `CW := KB + W`, the chain `j < p`, drain
  | .fC1 => xfer (.c .KB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fC1) (.s i k .fC2)
  | .fC2 => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.s i k .fC2) (.s i k .fW1)
  | .fW1 => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fW1) (.s i k .fW2)
  | .fW2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.s i k .fW2) (GL.pfFrom i k (pl i k))
  | .fD1 => xfer (.c .CW) [] (.s i k .fD1) (.s i k .oE)

/-- Loop-body stages: `CB += KB`, (in-range) `CB += u·g`, `CW := CB + W`, the clauses, drains. -/
def bdP (i : Fin N) (k : Fin L.KK) : BD L.g L.d → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .bC1 b => xfer (.c .KB) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.bC1 b)) (.b i k (.bC2 b))
  | .bC2 b => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.b i k (.bC2 b))
      (if b then .b i k (.sM .head) else .b i k (.w1 b))
  | .sM s => mulS .U .md .Gc .CB .tmp (fun s => .b i k (.sM s)) (.b i k (.w1 true)) s
  | .w1 b => xfer (.c .CB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w1 b)) (.b i k (.w2 b))
  | .w2 b => xfer (.c .tmp) [⟨.c .CB, ()⟩] (.b i k (.w2 b)) (.b i k (.w3 b))
  | .w3 b => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w3 b)) (.b i k (.w4 b))
  | .w4 b => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.b i k (.w4 b))
      (if b then GL.xFrom i k L.g else .b i k (.e00 .ov))
  | .e00 c => emitR .out [false, false] (.b i k (.cv1 c))
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.cv1 c)) (.b i k (.cv2 c))
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.b i k (.cv2 c)) (GL.after i k c c.nl)
  | .lit c l s => litP L sa pl cn pu N i k c l s
  | .fin c => xferE (.c .P) .out [false, true] (.b i k (.fin c)) (GL.nextC i k c)
  | .dCB b => xfer (.c .CB) [] (.b i k (.dCB b)) (.b i k (.dCW b))
  | .dCW b => xfer (.c .CW) [] (.b i k (.dCW b)) (if b then .s i k .sHead else .s i k .oHead)

/-- The generator. Input: `T` on `Tn`, `H` on `Hs`, everything else empty. -/
def prog : Lab L N → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Ka) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Ka .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre .dk) s
  | .pre .dk => xfer (.c .Ka) [] (.pre .dk) (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .vw1) s
  | .pre .vw1 => xfer (.c .Wc) [⟨.c .Vc, ()⟩, ⟨.c .tmp, ()⟩] (.pre .vw1) (.pre .vw2)
  | .pre .vw2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.pre .vw2) .tHead
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw .t1a s
  | .t1a => xfer (.c .TW) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1a .t1b
  | .t1b => xfer (.c .tmp) [⟨.c .TW, ()⟩] .t1b .t1c
  | .t1c => xfer (.c .Wc) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1c .t1d
  | .t1d => xfer (.c .tmp) [⟨.c .Wc, ()⟩] .t1d (GL.iFrom N)
  | .tEnd => xfer (.c .TW) [] .tEnd .tEnd2
  | .tEnd2 => xfer (.c .TW1) [] .tEnd2 .tHead
  | .s i k x => stP L pl cn N i k x
  | .sb i k r => decr (.c .U) .bad (GL.sbL i k r.val)
  | .b i k x => bdP L sa pl cn pu N i k x
  | .bad => .halt
  | .done => .halt

/-- **The generator as a genuine `FinTM2`** (finiteness check only). -/
def shTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := Lab L N
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L sa pl cn pu N

end Machine

/-! ## [FAM] Clause kinds: literal positions -/

section Lits

variable {g d : ℕ}

theorem BS.k_ne (b : BS) : b.k ≠ .Q ∧ b.k ≠ .tmp ∧ b.k ≠ .P ∧ b.k ≠ .c1 ∧ b.k ≠ .c2 ∧ b.k ≠ .md :=
  by cases b <;> decide

/-- Literals of a clause of kind `cl` at positions `pos`. -/
def clits (pos : ℕ → ℕ) (cl : CL g d) : List (ℕ × Bool) :=
  (List.range cl.nl).map fun l => (pos l, cl.sg l)

/-- Strictly increasing positions, the last one `< V`. -/
structure Mono (pos : ℕ → ℕ) (n V : ℕ) : Prop where
  mono : ∀ l, l + 1 < n → pos l < pos (l + 1)
  last : ∀ l, l + 1 = n → pos l < V

theorem clits_drop (pos : ℕ → ℕ) (cl : CL g d) (l : ℕ) :
    (clits pos cl).drop l = (List.range' l (cl.nl - l)).map fun l => (pos l, cl.sg l) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- The boundary before literal `l`: its position, or `V` past the last literal. -/
def bnd (V : ℕ) (pos : ℕ → ℕ) (n l : ℕ) : ℕ := if l < n then pos l else V

theorem inc_drop {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) (l : ℕ)
    (hl : l ≤ cl.nl) : Inc (bnd V pos cl.nl l) ((clits pos cl).drop l) V := by
  rw [clits_drop]
  refine inc_of_mono _ cl.nl V (fun j hj => h.mono j hj) (fun j hj => h.last j hj) (cl.nl - l) l _
    (by omega) (fun hn => ?_) (fun _ => ?_)
  · simp only [bnd]; split_ifs with h'
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show l < cl.nl by omega)]; exact le_rfl

theorem bnd_le {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) {l : ℕ} (hl : l ≤ cl.nl) :
    bnd V pos cl.nl l ≤ V := (inc_drop h l hl).le

theorem bnd_lt {V : ℕ} {pos : ℕ → ℕ} {n l : ℕ} (h : Mono pos n V) (hl : l < n) :
    pos l < bnd V pos n (l + 1) := by
  unfold bnd
  split_ifs with h'
  · exact h.mono l h'
  · exact h.last l (by omega)

end Lits

/-! ## [FAM] Correctness: one literal, one clause -/

section Clause

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

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

/-- One literal: from `P = q + gap + 1`, compute `Q := q = base + const`, prepend the gap and the
slot, leave `P = q` and the scratch counters empty. -/
theorem lit_run (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) (F : CK → ℕ) (hF : Rest F)
    (q gap : ℕ) (hq : q = F (c.bs l).k + csv L sa pl cn pu N i k c l) (hp : F .P = q + gap + 1)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (gap * (3 * q + 6) + 2 * F (c.bs l).k + 4 * q + 9)
      ⟨some (.b i k (.lit c l .cp1)), v, st F o⟩
      ⟨some (GL.after i k c l), false,
        st (update F .P q) (encodeSlot (some (c.sg l)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨n1, n2, n3, -, -, -⟩ := BS.k_ne (c.bs l)
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.lit c l .cp1))
    (l₂ := .b i k (.lit c l .cp2)) (next := .b i k (.lit c l .eo)) rfl rfl n1 n2 (by decide) F
    htmp v o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .eo))
    (next := .b i k (.lit c l .dec)) rfl _ _ _).bud ?_
  refine (gapS (M := prog L sa pl cn pu N) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true]) (dec := .b i k (.lit c l .dec)) (cmpL := .b i k (.lit c l .cmp))
    (emitL := .b i k (.lit c l .emL)) (ifZero := .b i k (.lit c l .bad))
    (next := .b i k (.lit c l .slot)) (r := fun o => .b i k (.lit c l (.r o)))
    (rB := fun o => .b i k (.lit c l (.rB o)))
    (out := fun o => if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .slot))
    (next := .b i k (.lit c l .dq)) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .dq)) (next := GL.after i k c l)
    (x := .Q) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- Per-literal cost apart from the gap loop. -/
def litE (V : ℕ) : ℕ := 6 * V + 9

/-- Cost of one clause (at most 3 literals). -/
def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 3 * litE V + 3 * V + 4

/-- All literals of clause `c`, from the one before `l` down to the first. -/
theorem lits_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (bnd V pos c.nl l * (3 * V + 6) + l * litE V)
        ⟨some (GL.after i k c l), v,
          st (update F .P (bnd V pos c.nl l)) (gapEnc (bnd V pos c.nl l) ((clits pos c).drop l) V ++
            [false, false] ++ o)⟩
        ⟨some (.b i k (.fin c)), v',
          st (update F .P (bnd V pos c.nl 0)) (gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
            [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hl3 : l < 3 := lt_of_lt_of_le hlm c.nl_le
      set p := pos l with hp
      set b := bnd V pos c.nl (l + 1) with hb
      have hpb : p < b := bnd_lt hM hlm
      obtain ⟨-, -, nP, -, -, -⟩ := BS.k_ne (c.bs l)
      have r := lit_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k c ⟨l, hl3⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by simp [hp, hpos, update_of_ne nP]) (by simp; omega)
        (gapEnc b ((clits pos c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel, GL.litL_of_lt hl3]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd V pos c.nl l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits pos c).drop l = (p, c.sg l) :: (clits pos c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hM (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hM hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have h3 := hbase l
      simp only [update_of_ne nP]
      rw [Nat.add_one_mul l]
      unfold litE
      omega

/-- One whole clause: from `e00 c` to `nextC c`, all counters restored. -/
theorem clause_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (hV : F .Vc = V) (hP : F .P = 0)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (clauseB V) ⟨some (.b i k (.e00 c)), v, st F o⟩
      ⟨some (GL.nextC i k c), false, st F (encodeClause (denseClause V (clits pos c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.e00 c)) (next := .b i k (.cv1 c)) rfl
    _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.cv1 c)) (l₂ := .b i k (.cv2 c))
    (next := GL.after i k c c.nl) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run i k pos F hF hpos hbase hM o c.nl le_rfl false
  have hbm : bnd V pos c.nl c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L sa pl cn pu N) (self := .b i k (.fin c)) (next := GL.nextC i k c)
    (x := .P) rfl _ _ _).bud ?_
  have e1 : update (update F .P (bnd V pos c.nl 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hM 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits pos c)) =
      rep [false, true] (bnd V pos c.nl 0) ++ gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
        [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hM (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) c.nl_le
  unfold clauseB
  omega

end Clause

/-! ## [FAM] The shift and overflow clauses; the `x` chain; the decrement chain -/

section Cells

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- `KB` of block `k` at time `t`: `t·W + A + k·(H·g)`. -/
def kbv (L : Layout) (H t k : ℕ) : ℕ := k * (H * L.g) + (t * L.rowW H + L.A)

/-- Positions of the in-range shift clause `(u, x)`. -/
def shPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k u x l : ℕ) : ℕ :=
  if l = 0 then L.cIdx H t k (u + cn i k) x else if l = 1 then L.xIdx H (t + 1) (sa i)
  else L.cIdx H (t + 1) k (u + pl i k) x

/-- Positions of the overflow clause `r`. -/
def ovPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k r l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0

theorem rowW_le {T H t : ℕ} (ht : t < T) : (t + 1) * L.rowW H + L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)

theorem cw_le {T H t k j : ℕ} (ht : t < T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := t + 1) (k := k) (j := j) ht hk hj
  unfold kbv; rw [Nat.succ_mul] at this; omega

theorem kbw_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) :
    kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have h1 := rowW_le (L := L) (H := H) ht
  have h2 := Nat.mul_le_mul_right (H * L.g) hk.le
  have h3 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h4 : L.rowW H = L.A + L.KK * (H * L.g) := rfl
  unfold kbv; omega

theorem shPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u x : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (hx : x < L.g) :
    Mono (shPos L sa pl cn H t i k u x) 3 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have h1 := cIdx_lt_next_row (L := L) (t := t) k.2 (show u + cn i k < H by omega) hx
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show u + pl i k < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : shPos L sa pl cn H t i k u x 0 = L.cIdx H t k (u + cn i k) x := rfl
  have e1 : shPos L sa pl cn H t i k u x 1 = (t + 1) * L.rowW H + sa i := rfl
  have e2 : shPos L sa pl cn H t i k u x 2 = L.cIdx H (t + 1) k (u + pl i k) x := rfl
  have e2' : L.cIdx H (t + 1) k (u + pl i k) x =
      (t + 1) * L.rowW H + L.A + (k * H + (u + pl i k)) * L.g + x := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
    · rw [e1, show 1 + 1 = 2 from rfl, e2]; omega
  · obtain rfl : l = 2 := by omega
    rw [e2]; omega

theorem ovPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) :
    Mono (ovPos L sa pl cn H t i k r) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2
    (show H - cn i k + pl i k + r < H by omega) hwf.g_pos
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h5 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : ovPos L sa pl cn H t i k r 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : ovPos L sa pl cn H t i k r 1 = L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 := rfl
  have e1' : L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 =
      (t + 1) * L.rowW H + L.A + (k * H + (H - cn i k + pl i k + r)) * L.g + 0 := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_sh (H t : ℕ) (i : Fin N) (k : Fin L.KK) (u x : ℕ) (hx : x < L.g) :
    clits (shPos L sa pl cn H t i k u x) (.sh ⟨x,
        hx⟩ : CL L.g L.d) = shLits L sa pl cn H t i k u x := by
  simp [clits, CL.nl, CL.sg, shPos, shLits, List.range_succ]

theorem clits_ov (H t : ℕ) (i : Fin N) (k : Fin L.KK) (r : ℕ) :
    clits (ovPos L sa pl cn H t i k r) (.ov : CL L.g L.d) = ovLits L sa pl cn H t i k r := by
  simp [clits, CL.nl, CL.sg, ovPos, ovLits, List.range_succ]

/-- Positions of the pushed-fill clause `j`. -/
def pfPos (L : Layout) (sa : ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (H t i k j l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k j (pu i k j)

theorem pfPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {j : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hj : j < pl i k) :
    Mono (pfPos L sa pu H t i k j) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hp := hwf.pl_le i i.2 k k.2
  have hd := hwf.d_le
  have hx := hwf.pu_lt i i.2 k k.2 j hj
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show j < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : pfPos L sa pu H t i k j 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : pfPos L sa pu H t i k j 1 = L.cIdx H (t + 1) k j (pu i k j) := rfl
  have e1' : L.cIdx H (t + 1) k j (pu i k j) =
      (t + 1) * L.rowW H + L.A + (k * H + j) * L.g + pu i k j := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_pf (H t : ℕ) (i : Fin N) (k : Fin L.KK) (j : ℕ) (hj : j < L.d) :
    clits (pfPos L sa pu H t i k j) (.pf ⟨j, hj⟩ : CL L.g L.d) = pfLits L sa pu H t i k j := by
  simp [clits, CL.nl, CL.sg, pfPos, pfLits, List.range_succ]

/-- Counters of a loop body: the block's constants are in place. -/
structure Body (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Rest F where
  P : F .P = 0
  Vc : F .Vc = L.numVars T H
  Gc : F .Gc = L.g
  Wc : F .Wc = L.rowW H
  TW : F .TW = t * L.rowW H
  TW1 : F .TW1 = (t + 1) * L.rowW H

/-- The in-range clauses `x < n` of cell pair `u`. -/
theorem xs_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hCB : F .CB = u * L.g + kbv L H t k)
    (hCW : F .CW = u * L.g + kbv L H t k + L.rowW H) :
    ∀ n, n ≤ L.g → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H)) ⟨some (GL.xFrom i k n), v, st F o⟩
        ⟨some (.b i k (.dCB true)), v', st F ((List.range n).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.xFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hng : n < L.g := by omega
      have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .sh ⟨n, hng⟩) (shPos L sa pl cn H t i k u n) F hF.toRest
        (fun l => by
          simp only [shPos, CL.bs, csv, CL.cs]
          split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW, kbv, Layout.xIdx, Layout.cIdx] <;> ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW] <;> omega)
        (shPos_mono ht hwf hu hng) hF.Vc hF.P o v
      rw [show GL.nextC i k (CL.sh ⟨n, hng⟩) = GL.xFrom i k n from rfl, clits_sh] at r
      rw [GL.xFrom_succ hng]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- The pushed-fill clauses `j < n` of block `(i, k)` (a label chain), then the fill drains. -/
theorem pf_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (F : CK → ℕ) (hF : Body L T H t F)
    (hCW : F .CW = kbv L H t k + L.rowW H) :
    ∀ n, n ≤ pl i k → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H))
        ⟨some (GL.pfFrom i k n), v, st F o⟩
        ⟨some (.s i k .fD1), v', st F ((List.range n).flatMap (fun j =>
          encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.pfFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hnd : n < L.d := by have := hwf.pl_le i i.2 k k.2; omega
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .pf ⟨n, hnd⟩) (pfPos L sa pu H t i k n) F hF.toRest
        (fun l => by
          simp only [pfPos, CL.bs, csv, CL.cs]
          split_ifs
          · simp only [BS.k, hF.TW1, Layout.xIdx]
          · simp only [BS.k, hCW, kbv, Layout.cIdx]; ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          have := kbw_le (L := L) (H := H) ht k.2
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCW] <;> omega)
        (pfPos_mono ht hwf (by omega)) hF.Vc hF.P o v
      rw [show GL.nextC i k (CL.pf ⟨n, hnd⟩ : CL L.g L.d) = GL.pfFrom i k n from rfl,
        clits_pf] at r
      rw [GL.pfFrom_succ hnd]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- The decrement chain: `n` decrements of `U`, then the pushed-fill setup. -/
theorem sb_run (i : Fin N) (k : Fin L.KK) :
    ∀ n, n ≤ L.d + 1 → ∀ (F : CK → ℕ) (h : ℕ), F .U = h + n → ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run (prog L sa pl cn pu N) n ⟨some (GL.sbL i k n), v, st F o⟩
        ⟨some (.s i k .fC1), v', st (update F .U h) o⟩ := by
  intro n
  induction n with
  | zero =>
      intro _ F h hF v o
      refine ⟨v, ?_⟩
      rw [show update F .U h = F by rw [update_eq_self_iff]; omega]
      exact Run.zero _
  | succ n ih =>
      intro hn F h hF v o
      have r := decS (M := prog L sa pl cn pu N) (self := .sb i k ⟨n, by omega⟩)
        (ifZero := .bad) (ifPos := GL.sbL i k n) (x := .U) rfl F (h + n) (by omega) v o
      obtain ⟨v', r'⟩ := ih (by omega) (update F .U (h + n)) h (by simp) true o
      rw [update_idem] at r'
      refine ⟨v', ?_⟩
      rw [GL.sbL_succ (by omega), show n + 1 = 1 + n by omega]
      exact r.trans r'

end Cells

/-! ## [FAM] Correctness: the two runtime loop bodies -/

section Bodies

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

theorem Body.upd {T H t : ℕ} {F : CK → ℕ} (h : Body L T H t F) {x : CK}
    (hx : x ≠ .Q ∧ x ≠ .tmp ∧ x ≠ .md ∧ x ≠ .c1 ∧ x ≠ .c2 ∧ x ≠ .P ∧ x ≠ .Vc ∧ x ≠ .Gc ∧
      x ≠ .Wc ∧ x ≠ .TW ∧ x ≠ .TW1) (n : ℕ) : Body L T H t (update F x n) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hx
  exact ⟨h.toRest.upd a1 a2 a3 a4 a5 n, by rw [update_of_ne a6.symm, h.P],
    by rw [update_of_ne a7.symm, h.Vc], by rw [update_of_ne a8.symm, h.Gc],
    by rw [update_of_ne a9.symm, h.Wc], by rw [update_of_ne a10.symm, h.TW],
    by rw [update_of_ne a11.symm, h.TW1]⟩

theorem kbv_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) : kbv L H t k ≤ L.numVars T H :=
  Cslib.Complexity.CookLevin.OneHot.kb_le (by omega) hk

theorem rowW_le' {T H : ℕ} : L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- Cost of one iteration of the in-range loop. -/
def sBodyB (g H V : ℕ) : ℕ :=
  (2 * V + 2) + (H * (2 * g + 3) + H + 2) + (2 * V + 2) + (2 * V + 2) + g * clauseB V + (V + 1) +
    (V + 1)

/-- Cost of one iteration of the overflow loop. -/
def oBodyB (g H d V : ℕ) : ℕ :=
  (2 * H + 2) + (2 * d + 2) + (H * (2 * g + 3) + H + 2) + (H + 1) + (2 * V + 2) + (2 * V + 2) +
    (2 * V + 2) + clauseB V + (V + 1) + (V + 1)

/-- In-range loop body for `u`: `CB := KB + u·g`, `CW := CB + W`, the clauses `x < g`, drains. -/
theorem sbody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = u) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (sBodyB L.g H (L.numVars T H)) ⟨some (.b i k (.bC1 true)), v,
        st F o⟩
      ⟨some (.s i k .sHead), false, st F ((List.range L.g).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := u * L.g + kbv L H t k with hcb
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 true)) (l₂ := .b i k (.bC2 true))
    (next := .b i k (.sM .head)) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .b i k (.sM s))
    (next := .b i k (.w1 true)) (a := .U) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 true)) (l₂ := .b i k (.w2 true))
    (next := .b i k (.w3 true)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 true)) (l₂ := .b i k (.w4 true))
    (next := GL.xFrom i k L.g) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hF.Gc, hF.Wc, hCB, hCW, hcb]; omega) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  obtain ⟨v1,
      rx⟩ := xs_run (sa := sa) (pu := pu) ht hwf hu _ hF' (by simp [hcb]) (by simp [hcb]) L.g le_rfl o
    false
  refine rx.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB true))
    (next := .b i k (.dCW true)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW true)) (next := .s i k .sHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show u ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hF.Gc,
      hF.Wc, hCB, hCW, Nat.add_zero]
    unfold sBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

/-- Overflow loop body for `r`: `CB := KB + (U + r)·g`, `CW := CB + W`, one clause, drains. -/
theorem obody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = H - max (pl i k) (cn i k))
    (hR : F .R = r) (hKa : F .Ka = 0) (hCB : F .CB = 0) (hCW : F .CW = 0) (o : List Bool)
    (v : Bool) :
    RunLe (prog L sa pl cn pu N) (oBodyB L.g H L.d (L.numVars T H)) ⟨some (.s i k .oC1), v, st F o⟩
      ⟨some (.s i k .oHead), false,
        st F (encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++ o)⟩ := by
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hm : max (pl i k) (cn i k) = cn i k := max_eq_right (by omega)
  have hV := cw_le (L := L) (T := T) ht k.2 (show H - cn i k + r < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := (H - cn i k + r) * L.g + kbv L H t k with hcb
  rw [hm] at hU
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oC1) (l₂ := .s i k .oC2)
    (next := .s i k .oR1) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oR1) (l₂ := .s i k .oR2)
    (next := .s i k (.oM .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.oM s))
    (next := .s i k .oD) (a := .Ka) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .oD) (next := .b i k (.bC1 false))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 false)) (l₂ := .b i k (.bC2 false))
    (next := .b i k (.w1 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 false)) (l₂ := .b i k (.w2 false))
    (next := .b i k (.w3 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 false)) (l₂ := .b i k (.w4 false))
    (next := .b i k (.e00 .ov)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hR, hKa, hF.Gc, hF.Wc, hCB, hCW, hcb] <;> ring) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  have rc := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k (c := .ov)
    (ovPos L sa pl cn H t i k r) _ hF'.toRest
    (fun l => by
      simp only [ovPos, CL.bs, csv, CL.cs]
      split_ifs
      · simp [BS.k, hF.TW1, Layout.xIdx]
      · simp only [BS.k, update_self, hcb, kbv, Layout.cIdx]
        have : H - cn i k + pl i k + r = H - cn i k + r + pl i k := by omega
        rw [this]; ring)
    (fun l => by
      have := rowW_le (L := L) (H := H) ht
      simp only [CL.bs]; split_ifs <;> simp [BS.k, hF.TW1] <;> omega)
    (ovPos_mono ht hwf hr) (by simp [hF.Vc]) (by simp [hF.P]) o false
  rw [clits_ov] at rc
  refine rc.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB false))
    (next := .b i k (.dCW false)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW false)) (next := .s i k .oHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show r + (H - cn i k) ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    have h3 : (r + (H - cn i k)) * L.g = (H - cn i k + r) * L.g := by ring
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hR,
      hKa, hF.Gc, hF.Wc, hCB, hCW, Nat.add_zero]
    unfold oBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

end Bodies

/-! ## [FAM] Correctness: one `(i, k)` block, the label chains, the time loop, the generator -/

section Top

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- Counters at the start of an `(i, k)` block. -/
structure Blk (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Body L T H t F where
  KB : F .KB = 0
  U : F .U = 0
  Ui : F .Ui = 0
  R : F .R = 0
  Ri : F .Ri = 0
  Ka : F .Ka = 0
  CB : F .CB = 0
  CW : F .CW = 0
  HG : F .HG = H * L.g
  Hs : F .Hs = H

/-- Cost of one `(i, k)` block. -/
def ikB (g KK H d V : ℕ) : ℕ :=
  1 + (2 * V + 2) + 1 + (KK * (2 * V + 3) + KK + 2) + (KK + 1) + (2 * H + 2) + d + 1 +
    ((2 * V + 2) + (2 * V + 2) + d * clauseB V + (V + 1)) +
    (d * (oBodyB g H d V + 1) + d + 2) + (H * (sBodyB g H V + 1) + H + 2) + (H + 1) + (d + 1) +
    (V + 1)

theorem encodeCNF_shBlk (T H t i k : ℕ) :
    encodeCNF (shBlk L sa pl cn pu T H t i k) =
      (List.range (H - max (pl i k) (cn i k))).flatMap (fun u => (List.range L.g).flatMap
        fun x => encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++
      (List.range (cn i k - pl i k)).flatMap
        (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      (List.range (pl i k)).flatMap
        (fun j => encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) := by
  simp [encodeCNF, shBlk, List.flatMap_append, List.flatMap_assoc, List.flatMap_map]

theorem hg_le {T H : ℕ} (hK : 0 < L.KK) : H * L.g ≤ L.numVars T H := by
  have h1 : H * L.g ≤ L.KK * (H * L.g) := Nat.le_mul_of_pos_left _ hK
  have h2 := rowW_le' (L := L) (T := T) (H := H)
  unfold Layout.rowW at h2; omega

/-- **One `(i, k)` block**: setup, overflow loop, in-range loop, drains. -/
theorem ik_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (k : Fin L.KK)
    (F : CK → ℕ) (hF : Blk L T H t F) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (ikB L.g L.KK H L.d (L.numVars T H)) ⟨some (.s i k .kbE), v,
        st F o⟩
      ⟨some (GL.ik i.val k.val), false, st F (encodeCNF (shBlk L sa pl cn pu T H t i k) ++ o)⟩ := by
  have hp := hwf.pl_le i i.2 k k.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hmd : max (pl i k) (cn i k) ≤ L.d := max_le hp hc
  have hmp : pl i k ≤ max (pl i k) (cn i k) := le_max_left _ _
  have hmc : cn i k ≤ max (pl i k) (cn i k) := le_max_right _ _
  set m := max (pl i k) (cn i k) with hm
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbE) (next := .s i k .kbC1) (x := .KB)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .kbC1) (l₂ := .s i k .kbC2)
    (next := .s i k .kbK) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) v
    o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbK) (next := .s i k (.kbM .head))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.kbM s))
    (next := .s i k .kbD) (a := .Ka) (ad := .md) (b := .HG) (c := .KB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .kbD) (next := .s i k .uC1) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .uC1) (l₂ := .s i k .uC2)
    (next := GL.sbL i k m) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .KB (kbv L H t k)) .U (H - m + m)) (by
    funext x; cases x <;> simp [hF.KB, hF.U, hF.Ka, hF.TW, hF.HG, hF.Hs, kbv]; omega) ?_
  obtain ⟨v1, rsb⟩ := sb_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k m (by omega)
    (update (update F .KB (kbv L H t k)) .U (H - m + m)) (H - m) (by simp) false o
  refine rsb.bud ?_
  -- pushed fill
  set F1 := update (update F .KB (kbv L H t k)) .U (H - m) with hF1
  refine bud_st (F' := F1) (by funext x; cases x <;> simp [hF1]) ?_
  have hB1 : Body L T H t F1 := (hF.toBody.upd (by decide) _).upd (by decide) _
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fC1) (l₂ := .s i k .fC2)
    (next := .s i k .fW1) rfl rfl (by decide) (by decide) (by decide) F1 hB1.tmp v1 o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fW1) (l₂ := .s i k .fW2)
    (next := GL.pfFrom i k (pl i k)) rfl rfl (by decide) (by decide) (by decide) _
    (by simp [hB1.tmp]) _ _).bud ?_
  set Ff := update F1 .CW (kbv L H t k + L.rowW H) with hFf
  refine bud_st (F' := Ff) (by
    funext x; cases x <;> simp [hFf, hF1, hF.CW, hF.Wc]; omega) ?_
  have hBf : Body L T H t Ff := hB1.upd (by decide) _
  obtain ⟨v2, rpf⟩ := pf_run (sa := sa) (cn := cn) (i := i) (k := k) ht hwf Ff hBf
    (by simp [hFf]) (pl i k) le_rfl o false
  refine rpf.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .fD1) (next := .s i k .oE)
    (x := .CW) rfl _ _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .oE) (next := .s i k .oHead) (x := .R)
    rfl _ _ _).bud ?_
  set F2 := update (update (update F .KB (kbv L H t k)) .U (H - m)) .R (cn i k - pl i k) with hF2
  refine bud_st (F' := F2) (by
    funext x; cases x <;> simp [hF2, hFf, hF1, hF.R, hF.CW]) ?_
  have hB2 : Body L T H t F2 :=
    ((hF.toBody.upd (by decide) _).upd (by decide) _).upd (by decide) _
  have l1 := stLoop (M := prog L sa pl cn pu N) (c := .R) (cd := .Ri) (head := .s i k .oHead)
    (body := .s i k .oC1) (rest := .s i k .oRest) (next := .s i k .sHead) rfl rfl (by decide)
    (cn i k - pl i k) (oBodyB L.g H L.d (L.numVars T H))
    (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ri])
    (fun r hr o' => ⟨false, obody_run ht hwf hr _ ((hB2.upd (by decide) _).upd (by decide) _)
      (by simp [hF2]) (by simp [hF2, hm]) (by simp) (by simp [hF2, hF.Ka]) (by simp [hF2, hF.CB])
      (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (pl i k)).flatMap (fun j =>
      encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)
  refine l1.bud ?_
  have l2 := stLoop (M := prog L sa pl cn pu N) (c := .U) (cd := .Ui) (head := .s i k .sHead)
    (body := .b i k (.bC1 true)) (rest := .s i k .sRest) (next := .s i k .dU) rfl rfl (by decide)
    (H - m) (sBodyB L.g H (L.numVars T H))
    (fun u => (List.range L.g).flatMap fun x =>
      encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ui])
    (fun u hu o' => ⟨false, sbody_run ht hwf (by omega) _
      ((hB2.upd (by decide) _).upd (by decide) _) (by simp [hF2]) (by simp)
      (by simp [hF2, hF.CB]) (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (cn i k - pl i k)).flatMap
      (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      ((List.range (pl i k)).flatMap (fun j =>
        encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o))
  refine l2.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dU) (next := .s i k .dR) (x := .U) rfl _
    _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dR) (next := .s i k .dKB) (x := .R) rfl
    _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dKB) (next := GL.ik i.val k.val)
    (x := .KB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := kbv_le (L := L) (H := H) ht k.2
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have hHG := hg_le (L := L) (T := T) (H := H) (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2)
    have h3 : k.val * (2 * (H * L.g) + 3) ≤ L.KK * (2 * L.numVars T H + 3) :=
      Nat.mul_le_mul k.2.le (by omega)
    have h4 := Nat.mul_le_mul_right (oBodyB L.g H L.d (L.numVars T H) + 1)
      (show cn i k - pl i k ≤ L.d by omega)
    have h5 := Nat.mul_le_mul_right (sBodyB L.g H (L.numVars T H) + 1) (show H - m ≤ H by omega)
    have h6 := Nat.mul_le_mul_right (clauseB (L.numVars T H)) hp
    have h7 := kbw_le (L := L) (H := H) ht k.2
    have h8 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF2, hFf, hF1,
      hF.KB, hF.Ka, hF.TW, hF.HG, hF.Hs, hF.Wc, hF.CW, Nat.add_zero]
    unfold ikB
    omega
  · simp only [encodeCNF_shBlk, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hF2, hF.KB, hF.U, hF.R]

/-- The blocks of situation `i` at time `t`. -/
def blkI (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (T H t i : ℕ) : List Bool :=
  (List.range L.KK).flatMap fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)

/-- The blocks of time step `t`. -/
def blkT (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N T H t : ℕ) : List Bool :=
  (List.range N).flatMap (blkI L sa pl cn pu T H t)

/-- The stack chain of situation `i`: blocks `k < n`, then on to situations `< i`. -/
theorem ks_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ L.KK → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * ikB L.g L.KK H L.d (L.numVars T H))
        ⟨some (GL.ik i.val n), v, st F o⟩
        ⟨some (GL.iFrom i.val), v', st F ((List.range n).flatMap
          (fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.ik] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have r := ik_run ht hwf i ⟨n, by omega⟩ F hF o v
      obtain ⟨v', r'⟩ := ih (by omega) (encodeCNF (shBlk L sa pl cn pu T H t i n) ++ o) false
      refine ⟨v', ?_⟩
      rw [GL.ik_succ i.2 (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- The situation chain: situations `i < n`, then the end of the time step. -/
theorem is_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ N → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)))
        ⟨some (GL.iFrom n), v, st F o⟩
        ⟨some .tEnd, v', st F ((List.range n).flatMap (blkI L sa pl cn pu T H t) ++ o)⟩ := by
  by_cases hK : L.KK = 0
  · intro n _ o v
    refine ⟨v, ?_⟩
    rw [GL.iFrom_KK0 hK]
    have : (List.range n).flatMap (blkI L sa pl cn pu T H t) = [] := by simp [blkI, hK]
    rw [this, List.nil_append]
    exact RunLe.refl _ _
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.iFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      obtain ⟨v1, r⟩ := ks_run ht hwf ⟨n, by omega⟩ F hF L.KK le_rfl o v
      obtain ⟨v', r'⟩ := ih (by omega) (blkI L sa pl cn pu T H t n ++ o) v1
      refine ⟨v', ?_⟩
      rw [GL.iFrom_succ (by omega) (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- Cost of one iteration of the time loop. -/
def tBodyB (L : Layout) (N T H : ℕ) : ℕ :=
  (T * (2 * L.numVars T H + 3) + T + 2) + (2 * L.numVars T H + 2) + (2 * L.numVars T H + 2) +
    N * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)) + (L.numVars T H + 1) + (L.numVars T H + 1)

/-- One iteration of the time loop: `TW := t·W`, `TW1 := TW + W`, the situation chain, drains. -/
theorem tbody_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Rest F) (hP : F .P = 0) (hV : F .Vc = L.numVars T H) (hG : F .Gc = L.g)
    (hW : F .Wc = L.rowW H) (hTW : F .TW = 0) (hTW1 : F .TW1 = 0) (hTn : F .Tn = t)
    (hKB : F .KB = 0) (hU : F .U = 0)
    (hUi : F .Ui = 0) (hR : F .R = 0) (hRi : F .Ri = 0) (hKa : F .Ka = 0) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (hHG : F .HG = H * L.g) (hHs : F .Hs = H) (o : List Bool) (v : Bool) :
    ∃ v' : Bool, RunLe (prog L sa pl cn pu N) (tBodyB L N T H) ⟨some (.tw .head), v, st F o⟩
      ⟨some .tHead, v', st F (blkT L sa pl cn pu N T H t ++ o)⟩ := by
  set F1 := update (update F .TW (t * L.rowW H)) .TW1 ((t + 1) * L.rowW H) with hF1
  have hB : Blk L T H t F1 :=
    ⟨⟨(hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _).upd (by decide)
      (by decide) (by decide) (by decide) (by decide) _, by simp [hF1, hP], by simp [hF1, hV],
      by simp [hF1, hG], by simp [hF1, hW], by simp [hF1], by simp [hF1]⟩, by simp [hF1, hKB],
      by simp [hF1, hU], by simp [hF1, hUi], by simp [hF1, hR], by simp [hF1, hRi],
      by simp [hF1, hKa], by simp [hF1, hCB], by simp [hF1, hCW], by simp [hF1, hHG],
      by simp [hF1, hHs]⟩
  obtain ⟨v1, ri⟩ := is_run ht hwf _ hB N le_rfl o false
  refine ⟨false, Bud.start ?_⟩
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := .tw) (next := .t1a) (a := .Tn) (ad := .md)
    (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1a) (l₂ := .t1b) (next := .t1c) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1c) (l₂ := .t1d) (next := GL.iFrom N) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := F1) (by
    funext x; cases x <;> simp [hF1, hTn, hW, hTW, hTW1]; ring) ?_
  refine ri.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd) (next := .tEnd2) (x := .TW) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd2) (next := .tHead) (x := .TW1) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht.le
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.mul_le_mul_left T (show 2 * L.rowW H + 3 ≤ 2 * L.numVars T H + 3 by
      have := rowW_le' (L := L) (T := T) (H := H); omega)
    have h4 := rowW_le (L := L) (H := H) ht
    have h5 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF1, hTn, hW,
      hTW, hTW1, Nat.add_zero, Nat.zero_add]
    unfold tBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hF1, hTW, hTW1]

/-- Initial counters: `T` on `Tn`, `H` on `Hs`. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- Counters after the precomputation. -/
def preF (L : Layout) (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Vc => L.numVars T H
  | _ => 0

/-- Cost of the precomputation. -/
def preB (L : Layout) (T H : ℕ) : ℕ :=
  1 + (H * (2 * L.g + 3) + H + 2) + 1 + 1 + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) + (L.KK + 1) +
    (T * (2 * L.rowW H + 3) + T + 2) + (2 * L.rowW H + 2)

/-- The explicit time bound (its polynomial form is `shBound_le`). -/
def shBound (L : Layout) (N T H : ℕ) : ℕ := preB L T H + (T * (tBodyB L N T H + 1) + T + 2)

theorem encodeCNF_shFamily (T H : ℕ) :
    encodeCNF (shFamily L sa pl cn pu N T H) = (List.range T).flatMap (blkT L sa pl cn pu N T H) := by
  simp [encodeCNF, shFamily, List.flatMap_assoc]
  rfl

/-- **Correctness of the generator, with its explicit time bound.** Started on `T`, `H` (unary)
with empty scratch counters, it reaches `done` within `shBound` steps with exactly the family's
encoding prepended to the output. -/
theorem sh_run (T H : ℕ) (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shBound L N T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o := by
  refine ⟨false, st (preF L T H) (encodeCNF (shFamily L sa pl cn pu N T H) ++ o), ?_, rfl⟩
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ek) (next := .pre (.w .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.w s)) (next := .pre .dk)
    (a := .Ka) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .pre .dk) (next := .pre (.v .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.v s)) (next := .pre .vw1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .pre .vw1) (l₂ := .pre .vw2) (next := .tHead) rfl
    rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars] <;> ring) ?_
  have hloop := stLoop (M := prog L sa pl cn pu N) (c := .Tn) (cd := .Ti) (head := .tHead)
    (body := .tw .head) (rest := .tRest) (next := .done) rfl rfl (by decide) T (tBodyB L N T H)
    (blkT L sa pl cn pu N T H) (preF L T H) rfl rfl
    (fun t ht o' => tbody_run ht hwf _
      ⟨by simp [preF], by simp [preF], by simp [preF], by simp [preF], by simp [preF]⟩
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) o' true)
    false o
  rw [← encodeCNF_shFamily] at hloop
  refine hloop.bud (Bud.fin ?_ rfl)
  simp [initF, preB, shBound, Layout.rowW]
  ring_nf
  omega

end Top

/-! ## [BOUND] The time bound is polynomial: `shBound ≤ shC · (T + H + 1)^6` -/

section Poly

theorem shBound_mono {L L' : Layout} {N N' T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hd : L.d ≤ L'.d) (hN : N ≤ N') (hT : T ≤ T') (hH : H ≤ H') :
    shBound L N T H ≤ shBound L' N' T' H' := by
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
  gcongr

/-- With all constants `k ≥ 1` and `T = H = y ≥ 1`, every monomial is at most `k⁷ y⁶` and the
coefficients sum to 828 (the value at `k = y = 1`). Plain `linarith` (monomials as atoms) suffices;
no products of hypotheses are needed. -/
theorem shBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    shBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k y y ≤ 828 * k ^ 7 * y ^ 6 := by
  have m : ∀ a b, a ≤ 7 → b ≤ 6 → k ^ a * y ^ b ≤ k ^ 7 * y ^ 6 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  linarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num),
    m 6 2 (by norm_num) (by norm_num),
    m 6 3 (by norm_num) (by norm_num),
    m 6 4 (by norm_num) (by norm_num),
    m 6 5 (by norm_num) (by norm_num),
    m 7 3 (by norm_num) (by norm_num),
    m 7 4 (by norm_num) (by norm_num),
    m 7 5 (by norm_num) (by norm_num),
    m 7 6 (by norm_num) (by norm_num)]

/-- The constant of the time bound: depends on `A, KK, g, d, N` only. -/
def shC (L : Layout) (N : ℕ) : ℕ := 828 * (L.A + L.KK + L.g + L.d + N + 1) ^ 7

theorem shBound_le (L : Layout) (N T H : ℕ) : shBound L N T H ≤ shC L N * (T + H + 1) ^ 6 := by
  have := shBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + L.d + N + 1))
    (N := N) (N' := L.A + L.KK + L.g + L.d + N + 1) (T := T) (T' := T + H + 1) (H := H)
    (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by omega) (by omega) (by omega)
  have h2 := shBound_uni (L.A + L.KK + L.g + L.d + N + 1) (T + H + 1) (by omega) (by omega)
  unfold shC
  exact this.trans h2

open Polynomial in
/-- The bound as a `Polynomial ℕ` in `T + H`. -/
noncomputable def shPoly (L : Layout) (N : ℕ) : Polynomial ℕ := C (shC L N) * (X + 1) ^ 6

theorem shPoly_eval (L : Layout) (N T H : ℕ) :
    (shPoly L N).eval (T + H) = shC L N * (T + H + 1) ^ 6 := by
  simp [shPoly]

/-- **The time bound**: the generator emits the family within a polynomial number of steps. -/
theorem sh_time {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}
    (T H : ℕ)
    (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shC L N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o :=
  let ⟨v, S, h, h'⟩ := sh_run T H hwf o; ⟨v, S, h.mono (shBound_le L N T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.Shift
