/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Inequalities.OSSS

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech
namespace Walls

open StatMech.OSSS StatMech.OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]











theorem oc_reveal_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) :
    0 ≤ reveal ν T e :=
  reveal_nonneg hν T e







theorem oc_reveal_le_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) :
    reveal ν T e ≤ 1 := by
  
  unfold reveal
  calc expect ν (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0)
      ≤ expect ν (fun _ => (1 : ℝ)) := by
        apply expect_mono hν
        intro ω
        split <;> norm_num
    _ = 1 := expect_one hν


theorem oc_reveal_mem_Icc {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) :
    reveal ν T e ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨oc_reveal_nonneg hν T e, oc_reveal_le_one hν T e⟩











theorem oc_revealmu_le_one {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (T : DecisionTree E)
    (e : E) :
    0 ≤ reveal ν T e ∧ reveal ν T e ≤ 1 :=
  ⟨oc_reveal_nonneg hν T e, oc_reveal_le_one hν T e⟩

end Walls
end StatMech
