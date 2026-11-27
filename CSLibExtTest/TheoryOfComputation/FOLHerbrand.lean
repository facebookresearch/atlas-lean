/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.TheoryOfComputation.FOLHerbrand

/-!
# Tests for Herbrand's theorem

Derive a satisfied ground instance and a nonempty list of valid instances for
self-equality in a language with a constant.
-/

open FirstOrder FirstOrder.Language Cslib.Logic.FOL
open Cslib.Logic.FOLHerbrandWanted

namespace CSLibExtTest.TheoryOfComputation.FOLHerbrand

example {L : FirstOrder.Language} {φ : L.BoundedFormula Empty 1}
    (hqf : IsQuantifierFree φ) (hground : Nonempty (L.Term Empty))
    (hvalid : ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ φ.ex)
    (M : Type) [L.Structure M] [Nonempty M] :
    ∃ t : L.Term Empty, M ⊨ instantiate t φ := by
  obtain ⟨ts, hts⟩ := fol_herbrand hqf hground hvalid
  have hd : ((ts.map (fun t => instantiate t φ)).foldr (· ⊔ ·) ⊥).Realize
      (default : Empty → M) default := by
    simpa only [List.foldr_map, Sentence.Realize, Formula.Realize] using hts M
  obtain ⟨θ, hθ, hv⟩ := (BoundedFormula.realize_foldr_sup _ _ _).mp hd
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hθ
  exact ⟨t, hv⟩

private abbrev constantLanguage : Language := constantsOn Unit

private def selfEquality : constantLanguage.BoundedFormula Empty 1 :=
  .equal (.var (Sum.inr 0)) (.var (Sum.inr 0))

example : ∃ ts : List (constantLanguage.Term Empty), ts ≠ [] ∧
    ∀ (M : Type) [constantLanguage.Structure M] [Nonempty M],
      M ⊨ ts.foldr (fun t acc => instantiate t selfEquality ⊔ acc) ⊥ := by
  have hqf : IsQuantifierFree selfEquality := trivial
  have hground : Nonempty (constantLanguage.Term Empty) :=
    ⟨Constants.term (L := constantLanguage) Unit.unit⟩
  have hvalid : ∀ (M : Type) [constantLanguage.Structure M] [Nonempty M],
      M ⊨ selfEquality.ex := by
    intro M _ hM
    rw [Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex]
    exact ⟨hM.some, rfl⟩
  obtain ⟨ts, hts⟩ := fol_herbrand hqf hground hvalid
  refine ⟨ts, ?_, hts⟩
  intro heq
  let := constantsOn.structure (fun _ : Unit => Unit.unit)
  have h := hts Unit
  rw [heq, List.foldr_nil] at h
  exact Sentence.not_realize_bot Unit h

end CSLibExtTest.TheoryOfComputation.FOLHerbrand
