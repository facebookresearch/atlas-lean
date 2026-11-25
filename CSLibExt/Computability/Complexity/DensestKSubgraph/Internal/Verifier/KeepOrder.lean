/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.BinaryOrder
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import MathlibExt.Computability.TuringMachine.StackEmbedding
import MathlibExt.Computability.BinaryNatEncoding

/-! # Non-destructive comparison of binary natural numbers -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.KeepOrder

open Turing MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity.PolynomialEncoding Computability MetaMathlibExt.TM2Recursive

/- Two original words, two copies, and shared temporary storage. -/
inductive K | word (s : BinaryOrder.K) | work (s : BinaryOrder.K) | temp
  deriving DecidableEq

instance : Fintype K where
  elems := {K.temp} ∪ Finset.univ.image K.word ∪ Finset.univ.image K.work
  complete k := by cases k <;> simp

/- Copy each word and then compare and discard the copies. -/
inductive Lab | copy (s : BinaryOrder.K) | restore (s : BinaryOrder.K)
  | cmp (l : BinaryOrder.Lab) | done (o : Ordering)
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.done .lt, .done .eq, .done .gt} ∪ Finset.univ.image Lab.copy ∪
    Finset.univ.image Lab.restore ∪ Finset.univ.image Lab.cmp
  complete l := by cases l with | done o => cases o <;> simp | _ => simp

/- Comparison sees only the two input copies. -/
def emb : SEmb (fun _ : BinaryOrder.K => Bool) (fun _ : K => Bool) where
  e := K.work
  inj _ _ h := K.work.inj h
  ι _ := Equiv.refl _

/- Route the comparison verdict to the component exit. -/
def redirect : BinaryOrder.Lab → Lab
  | .done o => .done o
  | l => .cmp l

/- Bounded tape operations implementing the non-destructive comparison. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .copy s => moveB (.word s) .temp some id (.copy s) (.restore s)
  | .restore s => splitB .temp (.word s) (.work s) some id id (.restore s)
      (match s with | .a => .copy .b | .b => .cmp (.scan .eq))
  | .cmp l => mapS emb redirect (BinaryOrder.prog l)
  | .done _ => .halt

private theorem embeds : Embeds emb redirect BinaryOrder.prog prog := by
  intro l
  cases l with
  | scan => exact Or.inl rfl
  | done => exact Or.inr rfl

/- Raw work layout, with the scratch copy stack initially empty. -/
def st (a b ca cb : List Bool) : K → List Bool
  | .word .a => a
  | .word .b => b
  | .work .a => ca
  | .work .b => cb
  | .temp => []

private theorem copy_step (s : BinaryOrder.K) (S : K → List Bool) (v : Bool) (p : List Bool)
    (hs : S (.word s) = p) (ht : S .temp = []) (hw : S (.work s) = []) :
    Run prog (2 * p.length + 2) ⟨some (.copy s), v, S⟩
      ⟨some (match s with | .a => .copy .b | .b => .cmp (.scan .eq)), false,
        Function.update S (.work s) p⟩ := by
  obtain ⟨T, hr, ha, hb, hc, hf⟩ := copyB_run (M := prog) (first := .copy s)
    (second := .restore s) rfl rfl (by simp) (by simp) (by simp)
    (ga := id) (fun _ => rfl) (fun _ => rfl) p [] v S (by simpa using hs) rfl (by rw [ht]; rfl)
  have he : T = Function.update S (.work s) p := by
    funext k
    by_cases h₁ : k = .work s
    · subst k; simpa [hw] using hc
    rw [Function.update_of_ne h₁]
    by_cases h₂ : k = .word s
    · subst k; exact ha
    by_cases h₃ : k = .temp
    · subst k; exact hb
    exact hf _ h₂ h₁ h₃
  rw [he] at hr
  cases s <;> exact hr

/- Compare normalized canonical words without altering them. The bound is in bits, not values. -/
theorem run (a b : ℕ) (v : Bool) :
    ∃ w, RunLe prog (3 * (a.size + b.size) + 5)
      ⟨some (.copy .a), v, st (encodeNat a) (encodeNat b) [] []⟩
      ⟨some (.done (compare a b)), w, st (encodeNat a) (encodeNat b) [] []⟩ := by
  let A := encodeNat a
  let B := encodeNat b
  have r₁ := copy_step .a (st A B [] []) v A rfl rfl rfl
  have r₂ := copy_step .b (Function.update (st A B [] []) (.work .a) A) false B rfl rfl rfl
  obtain ⟨w, r₃⟩ := BinaryOrder.run_encodeNat a b false
  obtain ⟨T, hr, ha, hf⟩ := runLe_embed redirect embeds r₃
    (S' := Function.update (Function.update (st A B [] []) (.work .a) A) (.work .b) B)
    (by intro k; cases k <;> exact (List.map_id _).symm)
  have he : T = st A B [] [] := by
    funext k
    cases k with
    | work w => cases w <;> exact ha _
    | word w => exact hf _ (by intro l; cases l <;> simp [emb])
    | temp => exact hf _ (by intro l; cases l <;> decide)
  rw [he] at hr
  refine ⟨w, (((r₁.trans r₂).le le_rfl).trans hr).mono ?_⟩
  dsimp only [A, B]
  rw [MetaMathlibExt.BinaryNatEncoding.length_encodeNat,
    MetaMathlibExt.BinaryNatEncoding.length_encodeNat]
  omega

end Cslib.Complexity.DensestKSubgraph.Internal.KeepOrder
