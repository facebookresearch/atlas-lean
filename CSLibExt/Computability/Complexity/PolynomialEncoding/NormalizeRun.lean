/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine

/-!
# Repeated-call contract for the existing Nat normalizer

This composition lemma strengthens the existing machine's postcondition:
its scratch stacks are empty and any previous output is preserved as a
suffix. It does not introduce another normalization implementation.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open Turing MetaMathlibExt.TM2Program
open FramedCNF FramedCNF.NormalizeMachine

/-- **Number normalizer restores its work stacks and prepends its answer.**
The canonical normalizer restores both work stacks and prepends
its answer to an arbitrary output suffix, within a linear bit bound. -/
theorem normalizeNat_run_frame (x out : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * x.length + 3)
      ⟨some (.read none), v, st x [] out⟩
      ⟨some .done, v', st [] [] (normalizeNat x ++ out)⟩ := by
  have r₁ := read_run x [] out v
  simp only [List.getLast?_nil, List.reverse_nil, List.nil_append] at r₁
  obtain ⟨v', S, r₂, hb, ho, hk⟩ := moveB_run
    (M := prog) (a := K.buffer) (b := K.output)
    (d := some) (g := id) (self := Lab.copy) (next := Lab.done)
    rfl (by decide) (normalizeNat x).reverse
    (normalizeNat x).reverse [] false
    (st [] (normalizeNat x).reverse out) (by simp [st]) rfl rfl
  have he : S = st [] [] (normalizeNat x ++ out) := by
    funext k
    cases k with
    | input => exact hk K.input (by decide) (by decide)
    | buffer => exact hb
    | output => simpa [st] using ho
  rw [he] at r₂
  refine ⟨v', ⟨_, ?_, r₁.trans r₂⟩⟩
  have h := length_normalizeNat_le x
  simp only [List.length_reverse]
  omega

end Cslib.Complexity.PolynomialEncoding
