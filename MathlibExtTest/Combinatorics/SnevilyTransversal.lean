/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SnevilyTransversal
import Mathlib.Data.ZMod.Basic

open MathlibExt.Combinatorics.SnevilyTransversalWanted

namespace SnevilyTransversalTest

private abbrev Plane := ZMod 3 × ZMod 3

private def rows : Finset Plane := {(0, 0), (1, 0), (0, 1)}
private def cols : Finset Plane := {(1, 0), (0, 0), (1, 1)}

-- Two different three-element subsets of a noncyclic group of order nine.
example : ∃ e : rows ≃ cols, Function.Injective (fun i : rows => (i : Plane) + (e i : Plane)) := by
  obtain ⟨f, hf, hs⟩ := conjecture_holds Plane ⟨4, by decide⟩ rows cols (by decide)
  exact ⟨Equiv.ofBijective f hf, fun _ _ h => hs _ _ h⟩

-- An empty indexing set still yields a bijection.
example : ∃ f : (∅ : Finset (ZMod 3)) → (∅ : Finset (ZMod 3)), Function.Bijective f := by
  obtain ⟨f, hf, -⟩ := conjecture_holds (ZMod 3) ⟨1, by decide⟩ ∅ ∅ rfl
  exact ⟨f, hf⟩

-- On the entire group of order two, both permutations give a repeated sum.
example : ¬ ∃ p : Equiv.Perm (ZMod 2), Function.Injective (fun i => i + p i) := by
  rintro ⟨p, hp⟩
  have h : ∀ x y : ZMod 2, x ≠ y → 0 + x = 1 + y := by decide
  exact zero_ne_one (hp (h _ _ (p.injective.ne zero_ne_one)))

end SnevilyTransversalTest
