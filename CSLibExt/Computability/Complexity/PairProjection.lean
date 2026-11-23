/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs -- shake: keep (canonical export aliases)
public import CSLibExt.Computability.Complexity.Host

/-!
# Polynomial-time first projection of bitstring pairs

The canonical pair encoding is not a concatenation of raw bitstrings. We reuse its
converter to the tagged `x # w` encoding, move `x` twice to preserve its order, erase the
remaining input, and re-encode the output with the canonical bit-list encoder.
No machine or encoding definition is changed. The run specification concerns valid encoded
pairs; it does not prescribe behavior on malformed strings.
-/

@[expose] public section

namespace Cslib.Complexity.PairProjection

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program DenseSAT

/-- Input, output, and the temporary stack used to restore the first component's order. -/
inductive Stk | inp | out | stash
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, .out, .stash], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Two transfer phases, input cleanup, and the final halt. -/
inductive Lab | read | emit | clean | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.read, .emit, .clean, .done], by decide⟩
  complete := fun l => by cases l <;> decide

/-- Tagged input symbols and Boolean output/work symbols. -/
@[reducible] def Γ : Stk → Type
  | .inp => Verifier.G
  | _ => Bool

/-- Two existing bit-transfer loops followed by charged input cleanup. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .read => moveB .inp .stash Host.dX id .read .emit
  | .emit => moveB .stash .out some id .emit .clean
  | .clean => cleanS [.inp] .clean .done
  | .done => .halt

/-- The first projection on the tagged pair encoding, with explicit input cleanup. -/
def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := Lab
  main := .read
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := prog

private def stk (i : List Verifier.G) (o a : List Bool) : ∀ k, List (Γ k)
  | .inp => i
  | .out => o
  | .stash => a

private theorem move_run (x w : List Bool) :
    ∃ v, Run prog (2 * x.length + 2)
      ⟨some .read, false, stk (Verifier.pairEncode (x, w)) [] []⟩
      ⟨some .clean, v, stk (.inr none :: w.map (fun b => .inr (some b))) x []⟩ := by
  obtain ⟨v, S, hr, hi, hs, ho, _⟩ := Host.move2_run (M := prog)
    (a := .inp) (t := .stash) (b := .out) (d := Host.dX)
    (gt := id) (dt := some) (g := id) (l₁ := .read) (l₂ := .emit) (l₃ := .clean)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl)
    x (x.map Sum.inl) (.inr none :: w.map (fun b => .inr (some b))) false
    (stk (Verifier.pairEncode (x, w)) [] []) rfl
    (by simp [IsBitBlock, Host.dX, Function.comp_def]) rfl rfl
  have hS : S = stk (.inr none :: w.map (fun b => .inr (some b))) x [] := by
    funext k
    cases k with
    | inp => exact hi
    | out => simpa [stk] using ho
    | stash => exact hs
  exact ⟨v, hS ▸ hr⟩

private theorem clean_input_run (w x : List Bool) (v : Bool) :
    RunLe prog (w.length + 2)
      ⟨some .clean, v, stk (.inr none :: w.map (fun b => .inr (some b))) x []⟩
      ⟨some .done, false, stk [] x []⟩ := by
  have h := clean_run (M := prog) (ks := [Stk.inp]) (self := .clean) (next := .done)
    rfl (by simp) (w.length + 1) v
    (stk (.inr none :: w.map (fun b => .inr (some b))) x []) (by
      intro k hk
      simp only [List.mem_singleton] at hk
      subst k
      simp [stk])
  have he : (fun k => if k ∈ [Stk.inp] then [] else
      stk (.inr none :: w.map (fun b => .inr (some b))) x [] k) = stk [] x [] := by
    funext k
    cases k <;> simp [stk]
  rw [he] at h
  simpa [Flag.tag, Nat.add_assoc] using h

/-- On a tagged pair, the projection preserves the first component's order and halts with
all other stacks empty, in at most `2 |x| + |w| + 5` steps. -/
theorem run (x w : List Bool) :
    RunLe tm.m (2 * x.length + w.length + 5)
      (initList tm (Verifier.pairEncode (x, w))) (haltList tm x) := by
  have hi : initList tm (Verifier.pairEncode (x, w)) =
      ⟨some .read, false, stk (Verifier.pairEncode (x, w)) [] []⟩ := by
    simp only [initList]
    congr 1
    funext k
    cases k <;> rfl
  have ho : haltList tm x = ⟨none, false, stk [] x []⟩ := by
    simp only [haltList]
    congr 1
    funext k
    cases k <;> rfl
  rw [hi, ho]
  obtain ⟨v, hr⟩ := move_run x w
  have hf : Run prog 1 ⟨some .done, false, stk [] x []⟩
      ⟨none, false, stk [] x []⟩ := Run.single rfl
  exact ((hr.le le_rfl).trans ((clean_input_run w x v).trans (hf.le le_rfl))).mono (by omega)

/-- A polynomial-time machine computing first projection from the tagged pair encoding to
raw bits. Its bound is `2 n + 3`, including cleanup and halting. -/
noncomputable def computable :
    TM2ComputableInPolyTime Verifier.pairEncode (fun x : List Bool => x) Prod.fst where
  tm := tm
  inputAlphabet := Equiv.refl Verifier.G
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun := fun ⟨x, w⟩ => by
    have hr := run x w
    unfold RunLe at hr
    let n := Classical.choose hr
    have hn : n ≤ 2 * x.length + w.length + 5 := (Classical.choose_spec hr).1
    refine ⟨⟨n, ?_⟩, ?_⟩
    · change Run tm.m n (initList tm ((Verifier.pairEncode (x, w)).map id))
        (haltList tm (x.map id))
      erw [List.map_id, List.map_id]
      exact (Classical.choose_spec hr).2
    · change n ≤ (Polynomial.C 2 * Polynomial.X + Polynomial.C 3).eval
        (Verifier.pairEncode (x, w)).length
      simp only [Verifier.pairEncode, List.length_append, List.length_map, List.length_cons,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega

end Cslib.Complexity.PairProjection

namespace Cslib.Complexity

/-- First projection of bitstring pairs is polynomial-time for the actual canonical encodings,
not just for raw bitstrings. -/
theorem isPolyTime_fst : IsPolyTime (Prod.fst : List Bool × List Bool → List Bool) := by
  obtain ⟨h⟩ := MetaMathlibExt.tm2ComputableInPolyTime_comp (f := id) (g := Prod.fst)
    DenseSAT.Converter.computable PairProjection.computable
  exact MetaMathlibExt.tm2ComputableInPolyTime_comp (f := Prod.fst) (g := id)
    h DenseSAT.EncodeBits.computable

end Cslib.Complexity
