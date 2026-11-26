/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.EmitEdge

/-! # Polynomial finite control for one row of the reverse CLIQUE pair order -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.CliqueRow

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier (Sym)

/- Row number, column number, remaining count and adjacency-bit input. -/
inductive K | bits | i | j | left | temp | edge (k : EmitEdge.K)
  deriving DecidableEq

instance : Fintype K where
  elems := {K.bits, .i, .j, .left, .temp} ∪ Finset.univ.image K.edge
  complete k := by cases k <;> simp

/- Row counters and the existing edge emitter workspace. -/
@[reducible] def Γ : K → Type
  | .bits => Bool
  | .edge k => EmitEdge.Γ k
  | _ => Sym

/- Test the count, read a bit, call the emitter if it is true, and increment the column. -/
inductive Lab | head | bit | copyI | restoreI | copyJ | restoreJ
  | emit (l : EmitEdge.Lab) | next | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.head, .bit, .copyI, .restoreI, .copyJ, .restoreJ, .next, .done} ∪
    Finset.univ.image Lab.emit
  complete l := by cases l <;> simp

/- The per-edge emitter occupies a disjoint workspace. -/
def emb : SEmb EmitEdge.Γ Γ where
  e := K.edge
  inj _ _ h := K.edge.inj h
  ι _ := Equiv.refl _

/- The emitter resumes at the next-column increment. -/
def redirect : EmitEdge.Lab → Lab
  | .done => .next
  | l => .emit l

/- The row walker never examines a number of positions larger than the physical count `left`. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .head => decr .left .done .bit
  | .bit => .pop .bits (fun _ o => o.getD false) <| .branch id
      (.goto fun _ => .copyI) (.goto fun _ => .next)
  | .copyI => xfer .i [⟨.edge (.local .A), EmitSS.U⟩, ⟨.temp, EmitSS.U⟩] .copyI .restoreI
  | .restoreI => xfer .temp [⟨.i, EmitSS.U⟩] .restoreI .copyJ
  | .copyJ => xfer .j [⟨.edge .second, EmitSS.U⟩, ⟨.temp, EmitSS.U⟩] .copyJ .restoreJ
  | .restoreJ => xfer .temp [⟨.j, EmitSS.U⟩] .restoreJ (.emit (.code false (.emit .hv)))
  | .emit l => mapS emb redirect (EmitEdge.prog l)
  | .next => incr .j EmitSS.U .head
  | .done => .halt

private theorem embeds : Embeds emb redirect EmitEdge.prog prog := by
  intro l
  cases l with
  | code | frame | write => exact Or.inl rfl
  | done => exact Or.inr rfl

/- Usable stack layout between row iterations. -/
def st (bits : List Bool) (i j left : ℕ) (out : List Bool) : (k : K) → List (Γ k)
  | .bits => bits
  | .i => cnt EmitSS.U i
  | .j => cnt EmitSS.U j
  | .left => cnt EmitSS.U left
  | .edge k => match k with | .output => out | _ => []
  | .temp => []

/- Processing the supplied bits from left to right, prepend true edges to the output.
The columns increase; the produced frames therefore occur in reverse column order. -/
def row (i : ℕ) : ℕ → List Bool → List Bool → List Bool
  | _, [], out => out
  | j, b :: bs, out =>
    row i (j + 1) bs (if b then delimit (bitEncode (i, j)) ++ out else out)

private theorem run_bit (i j left : ℕ) (b : Bool) (r out : List Bool) (v : Bool) :
    Run prog 1 ⟨some .bit, v, st (b :: r) i j left out⟩
      ⟨some (if b then .copyI else .next), b, st r i j left out⟩ := by
  have h : update (st (b :: r) i j left out) K.bits r = st r i j left out := by
    funext k
    cases k <;> simp [st]
  apply Run.single
  cases b <;> simp [prog, TM2.stepAux, st, h]

private theorem run_inc (i j left : ℕ) (r out : List Bool) (v : Bool) :
    Run prog 1 ⟨some .next, v, st r i j left out⟩
      ⟨some .head, v, st r i (j + 1) left out⟩ := by
  have h : update (st r i j left out) K.j (EmitSS.U :: cnt EmitSS.U j) =
      st r i (j + 1) left out := by
    funext k
    cases k <;> simp [st, cnt_succ]
  exact h ▸ incr_run (M := prog) (self := .next) rfl v (st r i j left out)

private def inEdge (i j : ℕ) (out : List Bool) : (k : EmitEdge.K) → List (EmitEdge.Γ k)
  | .local .A => cnt EmitSS.U i
  | .second => cnt EmitSS.U j
  | .output => out
  | _ => []

private theorem row_true (i j left : ℕ) (r out : List Bool) (v : Bool) :
    ∃ w, RunLe prog (716 * (i + j) + 620) ⟨some .copyI, v, st r i j left out⟩
      ⟨some .next, w, st r i j left (delimit (bitEncode (i, j)) ++ out)⟩ := by
  let S := st r i j left out
  let S₂ := update S (K.edge (.local .A)) (cnt EmitSS.U i)
  let S₃ := update S₂ (K.edge .second) (cnt EmitSS.U j)
  have r₁ : Run prog (2 * i + 2) ⟨some .copyI, v, S⟩ ⟨some .copyJ, false, S₂⟩ := by
    exact copy_run (M := prog) (l₁ := .copyI) (l₂ := .restoreI)
      (next := .copyJ) rfl rfl (by decide) (by decide) (by decide) i 0 v S rfl rfl rfl
  have r₂ : Run prog (2 * j + 2) ⟨some .copyJ, false, S₂⟩
      ⟨some (.emit (.code false (.emit .hv))), false, S₃⟩ := by
    exact copy_run (M := prog) (l₁ := .copyJ) (l₂ := .restoreJ)
      (next := .emit (.code false (.emit .hv))) rfl rfl (by decide) (by decide) (by decide)
      j 0 false S₂ rfl rfl rfl
  obtain ⟨w, T, hr, ho, ha, hs, hh, ht, hx, hO, hb, hf⟩ :=
    EmitEdge.run i j out false (inEdge i j out) rfl rfl rfl rfl rfl rfl rfl rfl
  have hA : Agree emb (inEdge i j out) S₃ := by
    intro k
    change S₃ (.edge k) = List.map id (inEdge i j out k)
    rw [List.map_id]
    cases k with
    | second | buffer | output => rfl
    | «local» k => cases k <;> rfl
  obtain ⟨R, r₃, hR, hFrame⟩ := runLe_embed redirect embeds hr hA
  have hfinal : R = st r i j left (delimit (bitEncode (i, j)) ++ out) := by
    funext k
    cases k with
    | bits | i | j | left | temp => exact hFrame _ (by intro l; decide +revert)
    | edge k =>
      have he := hR k
      change R (.edge k) = List.map id (T k) at he
      rw [List.map_id] at he
      rw [he]
      cases k with
      | second => exact hs
      | output => exact ho
      | buffer => exact hb
      | «local» k =>
        cases k <;> first | exact ha | exact hh | exact ht | exact hx | exact hO |
          exact hf _ (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨w, hfinal ▸ ((r₁.trans r₂).le le_rfl |>.trans r₃ |>.mono (by omega))⟩

private theorem head_step (i j left : ℕ) (r out : List Bool) (v : Bool) :
    Run prog 1 ⟨some .head, v, st r i j (left + 1) out⟩
      ⟨some .bit, true, st r i j left out⟩ := by
  have he : update (st r i j (left + 1) out) K.left (cnt EmitSS.U left) = st r i j left out := by
    funext k
    cases k <;> simp [st]
  exact he ▸ decr_run_cnt (M := prog) (self := .head) rfl v (S := st r i j (left + 1) out) rfl

/- Run exactly one contiguous row using the supplied prefix of adjacency bits.
The count is physical, and the cost accounts for encoding each selected pair. -/
theorem run (i j : ℕ) (bs rest out : List Bool) (v : Bool) :
    ∃ w, RunLe prog (bs.length * (716 * (i + j + bs.length) + 623) + 1)
      ⟨some .head, v, st (bs ++ rest) i j bs.length out⟩
      ⟨some .done, w, st rest i (j + bs.length) 0 (row i j bs out)⟩ := by
  induction bs generalizing j out v with
  | nil =>
    refine ⟨Flag.tag false, ?_⟩
    simpa only [List.length_nil, List.nil_append, Nat.zero_mul, Nat.zero_add, Nat.add_zero, row]
      using (decr_run_zero (M := prog) (self := .head) rfl v (S := st rest i j 0 out) rfl).le le_rfl
  | cons b bs ih =>
    have hr₁ := (head_step i j bs.length (b :: (bs ++ rest)) out v).trans
      (run_bit i j bs.length b (bs ++ rest) out true)
    let out' := if b then delimit (bitEncode (i, j)) ++ out else out
    obtain ⟨w, hr₂⟩ : ∃ w, RunLe prog (716 * (i + j) + 620)
        ⟨some (if b then .copyI else .next), b, st (bs ++ rest) i j bs.length out⟩
        ⟨some .next, w, st (bs ++ rest) i j bs.length out'⟩ := by
      cases b with
      | false => exact ⟨false, RunLe.refl _ _⟩
      | true => exact row_true _ _ _ _ _ _
    have hr₃ := run_inc i j bs.length (bs ++ rest) out' w
    obtain ⟨w', last⟩ := ih (j + 1) out' w
    have he : j + 1 + bs.length = j + (b :: bs).length := by simp; omega
    rw [he] at last
    refine ⟨w', (((hr₁.le le_rfl).trans hr₂).trans (hr₃.le le_rfl) |>.trans last).mono ?_⟩
    rw [List.length_cons, Nat.succ_mul (bs.length)]
    have hfactor : 716 * (i + (j + 1) + bs.length) + 623 =
        716 * (i + j + (bs.length + 1)) + 623 := by omega
    rw [hfactor]
    omega

end Cslib.Complexity.DensestKSubgraph.Internal.CliqueRow
