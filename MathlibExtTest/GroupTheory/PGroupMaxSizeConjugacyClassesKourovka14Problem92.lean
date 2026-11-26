/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92

namespace MathlibExtTest.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92

open MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92Wanted

example : ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G),
    IsPGroup p G ∧ numMaxSizeConjClasses G = p - 1 :=
  oddPGroupWithPredMaxSizeConjClasses_holds

example : numMaxSizeConjClasses PUnit = 1 := by
  unfold numMaxSizeConjClasses
  let c := ConjClasses.mk (1 : PUnit)
  have hc (d : ConjClasses PUnit) : d = c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective d
    rw [Subsingleton.elim g 1]
  let : Unique {d : ConjClasses PUnit // ∀ e : ConjClasses PUnit,
      Nat.card e.carrier ≤ Nat.card d.carrier} :=
    { default := ⟨c, fun e ↦ by rw [hc e]⟩
      uniq := fun d ↦ Subtype.ext (hc d.1) }
  exact Nat.card_unique

end MathlibExtTest.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92
