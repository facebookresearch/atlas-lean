/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
public import MathlibExt.Computability.TuringMachine.StackEmbedding

/-! # A reusable finite-stack constructor for the canonical product bit framing -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.JoinKey

open Turing MetaMathlibExt BitstringEncoding TM2Program
open Cslib.Complexity.PolynomialEncoding

/- Two component words, reverse scratch, and a forward output. -/
inductive K | a | b | rev | out
  deriving DecidableEq

instance : Fintype K := Fintype.ofList [.a, .b, .rev, .out] (by intro s; cases s <;> decide)

/- Frame the first word, append the second, and restore forward bit order. -/
inductive Lab | frame | tail | back | done
  deriving DecidableEq

instance : Fintype Lab := Fintype.ofList [.frame, .tail, .back, .done]
  (by intro l; cases l <;> decide)

/- Product serialization without decoding any Nat or computing its magnitude. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .frame => emitFrame .a .rev some id .frame .tail
  | .tail => moveB .b .rev some id .tail .back
  | .back => moveB .rev .out some id .back .done
  | .done => .halt

/- Concrete bit-stack layout. -/
def st (a b r o : List Bool) : K → List Bool
  | .a => a
  | .b => b
  | .rev => r
  | .out => o

/- The constructor consumes only the two words, restores scratch and writes the product code. -/
theorem run (a b o : List Bool) (v : Bool) :
    ∃ w, RunLe prog (3 * a.length + 2 * b.length + 4)
      ⟨some .frame, v, st a b [] o⟩ ⟨some .done, w, st [] [] [] (delimit a ++ b ++ o)⟩ := by
  obtain ⟨S, h₁, ha, hr, hf⟩ := emitFrame_run (M := prog) (self := .frame) rfl (by decide)
    id (fun _ => rfl) a [] v (st a b [] o) rfl (by simp [st])
  have he : S = st [] b (delimit a).reverse o := by
    funext j
    cases j with
    | a => exact ha
    | b | out => exact hf _ (by decide) (by decide)
    | rev => simpa [st] using hr
  rw [he] at h₁
  obtain ⟨w₁, T, h₂, hb, hrev, hf'⟩ := moveB_run (M := prog) (self := .tail)
    rfl (by decide) b b [] false (st [] b (delimit a).reverse o) (by simp [st]) rfl rfl
  have he' : T = st [] [] (delimit a ++ b).reverse o := by
    funext j
    cases j with
    | a | out => exact hf' _ (by decide) (by decide)
    | b => exact hb
    | rev => simpa [st, List.reverse_append] using hrev
  rw [he'] at h₂
  let p := (delimit a ++ b).reverse
  obtain ⟨w, U, h₃, hu, ho, hf''⟩ := moveB_run (M := prog) (self := .back)
    rfl (by decide) p p [] w₁ (st [] [] p o) (by simp [st]) rfl rfl
  have he'' : U = st [] [] [] (delimit a ++ b ++ o) := by
    funext j
    cases j with
    | a | b => exact hf'' _ (by decide) (by decide)
    | rev => exact hu
    | out => simpa [st, p] using ho
  rw [he''] at h₃
  refine ⟨w, ((h₁.trans h₂).trans h₃).le ?_⟩
  simp only [p, List.length_reverse, List.length_append, length_delimit]
  omega

end Cslib.Complexity.DensestKSubgraph.Internal.JoinKey
