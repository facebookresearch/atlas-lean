/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Generic linear forms over infinite fields

Over an infinite field, a vector space is not a finite union of proper
submodules, so a linear form can be chosen to avoid vanishing on any prescribed
finite set of nonzero vectors. Both results below are `Finset`-form corollaries
of the Mathlib API in `Mathlib.Algebra.Module.Submodule.Union`
(`Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` and its consequences);
in particular no finite-dimensionality hypothesis is needed.

Downstream (elimination coordinate changes) these supply a linear form that is
nonzero on finitely many prescribed nonzero vectors. The statements stay
general over infinite fields: `IsAlgClosed K → Infinite K` is available as an
instance (`Mathlib.FieldTheory.IsAlgClosed.Basic`), but it is never assumed.

## Main results

* `not_covered_by_proper_submodules`: no finite family of proper submodules
  covers the space.
* `exists_linearForm_ne_zero_on_finset`: one linear form avoids vanishing on a
  prescribed finite set of nonzero vectors.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/- General setting for both results: a module over an infinite field.
No finite-dimensionality hypothesis is needed anywhere below. -/
variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

/-! ## Main results -/

/-- A vector space over an infinite field is not covered by finitely many
proper submodules: for `S : Finset (Submodule K V)` with every member proper,
the union of the members is not the whole space.

Finset form of `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`, via
`Submodule.exists_forall_notMem_of_forall_ne_top` applied to the subtype
`↥S`, so the properness hypothesis is only needed on members of `S`. -/
theorem not_covered_by_proper_submodules
    (S : Finset (Submodule K V)) (hS : ∀ s ∈ S, s ≠ ⊤) :
    ⋃ s ∈ S, (s : Set V) ≠ Set.univ := by
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun i : S => (i.val : Submodule K V)) (fun i => hS i.val i.property)
  intro hcon
  have hxmem : x ∈ ⋃ s ∈ S, (s : Set V) := by
    rw [hcon]
    exact Set.mem_univ x
  simp only [Set.mem_iUnion, exists_prop] at hxmem
  obtain ⟨s, hs, hxs⟩ := hxmem
  exact hx ⟨s, hs⟩ hxs

/-- Given finitely many nonzero vectors over an infinite field, there is a
linear form vanishing on none of them.

Finset form of `Module.exists_dual_forall_apply_ne_zero` (applied to the
inclusion `↥S → V`). In particular no finite-dimensionality hypothesis is
needed. -/
theorem exists_linearForm_ne_zero_on_finset
    (S : Finset V) (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ l : V →ₗ[K] K, ∀ v ∈ S, l v ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.exists_dual_forall_apply_ne_zero (K := K)
    (fun i : S => (i.val : V)) (fun i => hS i.val i.property)
  exact ⟨l, fun v hv => hl ⟨v, hv⟩⟩

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
