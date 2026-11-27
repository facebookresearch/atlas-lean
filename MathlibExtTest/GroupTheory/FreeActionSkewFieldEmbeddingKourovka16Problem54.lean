/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Defs
import MathlibExt.GroupTheory.FreeActionSkewFieldEmbeddingKourovka16Problem54

namespace MathlibExt.GroupTheory.FreeActionSkewFieldEmbeddingKourovka16Problem54Wanted

-- The refutation provides a group that acts freely on a nontrivial abelian group but has no
-- injective homomorphism into the unit group of any division ring.
example : ∃ (G : Type) (_ : Group G),
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Nontrivial V) (_ : DistribMulAction G V),
      ∀ g : G, g ≠ 1 → ∀ v : V, v ≠ 0 → g • v ≠ v) ∧
    ∀ (D : Type) (_ : DivisionRing D) (f : G →* Dˣ), ¬ Function.Injective f := by
  by_contra h
  apply freeActionEmbedsInSkewField_refuted
  intro G inst hfree
  by_contra hne
  exact h ⟨G, inst, hfree, fun D _ f hf ↦ hne ⟨D, inferInstance, f, hf⟩⟩

-- The converse holds: a group embedded in the unit group of a division ring `D` acts freely on
-- `D` by left multiplication. So the hypothesis of `freeActionEmbedsInSkewField` is necessary
-- for its conclusion, and the refutation shows that it is not sufficient.
example (G : Type) [Group G] (D : Type) [DivisionRing D] (f : G →* Dˣ)
    (hf : Function.Injective f) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Nontrivial V) (_ : DistribMulAction G V),
      ∀ g : G, g ≠ 1 → ∀ v : V, v ≠ 0 → g • v ≠ v := by
  let _ : DistribMulAction G D := DistribMulAction.compHom D f
  refine ⟨D, inferInstance, inferInstance, inferInstance, fun g hg v hv h ↦ hg (hf ?_)⟩
  change ((f g : Dˣ) : D) * v = v at h
  rw [map_one]
  exact Units.ext (mul_right_cancel₀ hv (h.trans (one_mul v).symm))

-- The refuted statement with `freeActionEmbedsInSkewField` unfolded.
example : ¬ ∀ (G : Type) [Group G],
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Nontrivial V) (_ : DistribMulAction G V),
      ∀ g : G, g ≠ 1 → ∀ v : V, v ≠ 0 → g • v ≠ v) →
    ∃ (D : Type) (_ : DivisionRing D) (f : G →* Dˣ), Function.Injective f :=
  freeActionEmbedsInSkewField_refuted

end MathlibExt.GroupTheory.FreeActionSkewFieldEmbeddingKourovka16Problem54Wanted
