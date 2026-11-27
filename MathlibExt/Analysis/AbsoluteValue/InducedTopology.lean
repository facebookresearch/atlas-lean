/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Topology induced by an absolute value

This module ports ATLAS `NumberTheoryI` N176 / Corollary 8.6.
Given an absolute value `v` on a field `K`, the carrier map
`WithAbs.toAbs v : K → WithAbs v` pulls the norm topology on `WithAbs v`
back to `K`. The main theorem characterizes equality of these carrier
topologies, not equality of absolute values: two absolute values induce
the same topology on `K` if and only if they are equivalent.
-/

@[expose] public section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- Topology on the carrier field induced by the norm topology on `WithAbs v`. -/
@[reducible]
public noncomputable def inducedTopology (v : AbsoluteValue K ℝ) : TopologicalSpace K :=
  letI : NormedRing (WithAbs v) := WithAbs.normedRing v
  TopologicalSpace.induced (WithAbs.toAbs v) inferInstance

/-- **Absolute values inducing the same topology are equivalent.** Let $K$ be a field and
$v$, $w$ real-valued absolute values on $K$. The topologies induced on $K$ by $v$ and by $w$
are equal if and only if $v$ and $w$ are equivalent.

This is about equality of the induced topologies on $K$, not about equality
of the absolute values themselves: inequivalent absolute values may still agree
on many elements while inducing different topologies. -/
public theorem inducedTopology_eq_iff_isEquiv (v w : AbsoluteValue K ℝ) :
    v.inducedTopology = w.inducedTopology ↔ v.IsEquiv w := by
  have hcomp : (WithAbs.toAbs w : K → WithAbs w) =
      (WithAbs.congr v w (.refl K)) ∘ (WithAbs.toAbs v) := rfl
  simp only [AbsoluteValue.inducedTopology]
  rw [hcomp, ← induced_compose]
  have he_symm : ⇑(WithAbs.equiv v).toEquiv.symm = WithAbs.toAbs v := rfl
  rw [← he_symm]
  set e := (WithAbs.equiv v).toEquiv
  have cancel : ∀ t : TopologicalSpace (WithAbs v),
      TopologicalSpace.coinduced (⇑e.symm)
        (TopologicalSpace.induced (⇑e.symm) t) = t := by
    intro t
    rw [Equiv.induced_symm, coinduced_compose]
    have : (⇑e.symm) ∘ (⇑e) = id := funext (fun x => e.symm_apply_apply x)
    rw [this, coinduced_id]
  constructor
  · intro h
    have heq : (inferInstance : TopologicalSpace (WithAbs v)) =
        TopologicalSpace.induced (⇑(WithAbs.congr v w (.refl K)))
          inferInstance := by
      have h1 := cancel (inferInstance : TopologicalSpace (WithAbs v))
      have h2 := cancel (TopologicalSpace.induced
        (⇑(WithAbs.congr v w (.refl K)))
        (inferInstance : TopologicalSpace (WithAbs w)))
      rw [h] at h1
      rw [← h1, h2]
    rw [AbsoluteValue.isEquiv_iff_isHomeomorph,
      isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨⟨⟨heq⟩, (RingEquiv.bijective _).1⟩, (RingEquiv.bijective _).2⟩
  · intro h
    rw [AbsoluteValue.isEquiv_iff_isHomeomorph] at h
    exact congrArg _ h.isInducing.eq_induced

end AbsoluteValue
