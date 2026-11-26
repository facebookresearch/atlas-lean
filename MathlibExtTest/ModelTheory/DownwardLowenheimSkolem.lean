/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ModelTheory.DownwardLowenheimSkolem

open FirstOrder FirstOrder.Language
open Cslib.Logic.DownwardLSWanted

-- The language may have no symbols, and the starting model may already be countably infinite.
example : ∃ N : Type, ∃ _ : Language.empty.Structure N,
    Countable N ∧ Infinite N ∧ N ⊨ (∅ : Language.empty.Theory) := by
  let : Language.empty.Structure ℕ := Language.emptyStructure
  exact downward_lowenheim_skolem ⟨ℕ, inferInstance, inferInstance, inferInstance⟩

-- Named constants in a higher universe remain distinct when passing from the power set of ℕ.
example : ∃ N : Type, ∃ _ : (Language.empty[[ULift.{1} ℕ]]).Structure N,
    Countable N ∧ Infinite N ∧ N ⊨ Language.empty.distinctConstantsTheory
      (Set.univ : Set (ULift.{1} ℕ)) := by
  let : Countable (Language.empty[[ULift.{1} ℕ]]).Symbols := by
    apply Cardinal.mk_le_aleph0_iff.mp
    change (Language.empty[[ULift.{1} ℕ]]).card ≤ Cardinal.aleph0
    simp
  let : Language.empty.Structure (Set ℕ) := Language.emptyStructure
  let : (constantsOn (ULift.{1} ℕ)).Structure (Set ℕ) :=
    constantsOn.structure fun n => {n.down}
  apply downward_lowenheim_skolem
  refine ⟨Set ℕ, inferInstance, inferInstance, ?_⟩
  apply (Language.empty.model_distinctConstantsTheory _).mpr
  intro a _ b _ hab
  apply ULift.ext
  change ({a.down} : Set ℕ) = {b.down} at hab
  simpa using hab
