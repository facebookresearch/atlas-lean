/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricBoxCompression

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricBoxCompression`

* `rit_familyEvent_eventFamily`: `eventFamily` inverts `familyEvent`, on `Set.univ` over `Fin 2`.
* `rit_exists_common_iterDownComp_isLowerSet` for two families on `Fin 2`.
* `rit_collapseDomination_false`: the disjoint-pair weight does not dominate `P(A □ B)`.
* `rit_reimer_wprob_symm_of_boxMono` instantiated on `Fin 0`, the only coordinate set where its
  hypothesis `rit_BoxDownCompMono` is known to hold (`rit_boxDownCompMono_fin0`; Stage B: false
  for `Fin 2`).
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSymmetricBoxCompression

example : familyEvent (eventFamily (Set.univ : Set (ConfigSpace (Fin 2)))) = Set.univ :=
  rit_familyEvent_eventFamily _

example : ∃ cs : List (Fin 2),
    IsLowerSet ((iterDownComp cs ({{0, 1}} : Finset (Finset (Fin 2)))) : Set (Finset (Fin 2))) ∧
    IsLowerSet ((iterDownComp cs ({{1}} : Finset (Finset (Fin 2)))) : Set (Finset (Fin 2))) :=
  rit_exists_common_iterDownComp_isLowerSet _ _

example : ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (w : β → Bool → ℝ),
    (∀ x b, 0 ≤ w x b) ∧ (∀ x, w x false + w x true = 1) ∧ (∀ x, w x false = w x true) ∧
    ∃ 𝒜 ℬ : Finset (Finset β),
      wdpairs w 𝒜 ℬ < wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) :=
  rit_collapseDomination_false

example (w : Fin 0 → Bool → ℝ) (A B : Set (ConfigSpace (Fin 0))) :
    wprob w (disjointOccurrence A B) ≤ wprob w A * wprob w B :=
  rit_reimer_wprob_symm_of_boxMono rit_boxDownCompMono_fin0 w (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) A B

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSymmetricBoxCompression
