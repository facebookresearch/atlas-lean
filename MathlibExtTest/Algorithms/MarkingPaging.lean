/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MarkingPaging

@[expose] public section

/-- A hit marks the requested page. -/
example (evict : Finset ℕ → Finset ℕ → ℕ) (s : Finset ℕ × Finset ℕ)
    (p : ℕ) (hp : p ∈ s.1) :
    (markStep 3 evict s p).2 = insert p s.2 :=
  markStep_hit evict s p hp

end
