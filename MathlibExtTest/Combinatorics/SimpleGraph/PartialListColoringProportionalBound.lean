/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PartialListColoringProportionalBound

namespace MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted

-- The other endpoint can have an empty list when only one endpoint is colored.
example : IsPartialListColoring (⊤ : SimpleGraph Bool)
    (fun v => if v then ∅ else {()}) {false} := by
  refine ⟨fun _ => (), ?_, ?_⟩
  · rintro ⟨v, hv⟩
    obtain rfl : v = false := Finset.mem_singleton.mp hv
    simp
  · rintro ⟨v, hv⟩ ⟨w, hw⟩
    obtain rfl : v = false := Finset.mem_singleton.mp hv
    obtain rfl : w = false := Finset.mem_singleton.mp hw
    simp

-- Both endpoints cannot be colored if they have the same single available color.
example : ¬ IsPartialListColoring (⊤ : SimpleGraph Bool) (fun _ => {()}) Finset.univ := by
  rintro ⟨color, _, hproper⟩
  exact hproper ⟨false, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩ (by decide)
    (Subsingleton.elim _ _)

end MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted
