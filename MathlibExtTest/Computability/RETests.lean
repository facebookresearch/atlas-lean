/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.RE

@[expose] public section

/-!
# Tests for closure properties of computable and r.e. predicates
-/

set_option autoImplicit false

open MetaMathlibExt

namespace MathlibExtTest.Computability.RE

theorem computablePred_even : ComputablePred fun n : ℕ ↦ Even n := by
  refine ComputablePred.computable_iff.mpr ⟨fun n ↦ n % 2 == 0, ?_, ?_⟩
  · exact (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).to_comp
  · funext n
    simp [Nat.even_iff]

example : ComputablePred fun n : ℕ ↦ Even n ∧ ¬Even n :=
  computablePred_even.and computablePred_even.not

example : REPred fun n : ℕ ↦ Even n ∨ ¬Even n :=
  computablePred_even.to_re.or computablePred_even.not.to_re

/-- A bounded existential over the candidate list `range (n + 1)`. -/
example : REPred fun n : ℕ ↦ ∃ m ∈ List.range (n + 1), Even m :=
  REPred.exists_mem (R := fun (_ : ℕ) (m : ℕ) ↦ Even m)
    (computablePred_even.to_re.comp Computable.snd) (Primrec.list_range.comp Primrec.succ)

example : Computable fun l : List ℕ ↦ l.any fun n ↦ n == 0 :=
  computable_list_any (l := id) (g := fun _ n ↦ n == 0) Computable.id
    (Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp

/-- An unbounded existential: the perfect squares, as a projection of a decidable relation. -/
example : REPred fun n : ℕ ↦ ∃ m, m * m = n := by
  classical
  refine REPred.exists (R := fun (n m : ℕ) ↦ m * m = n) (ComputablePred.to_re ?_)
  exact ComputablePred.computable_iff.mpr ⟨fun p ↦ decide (p.2 * p.2 = p.1),
    (Primrec.eq.decide.comp (Primrec.nat_mul.comp Primrec.snd Primrec.snd) Primrec.fst).to_comp,
    by funext p; simp⟩

end MathlibExtTest.Computability.RE
