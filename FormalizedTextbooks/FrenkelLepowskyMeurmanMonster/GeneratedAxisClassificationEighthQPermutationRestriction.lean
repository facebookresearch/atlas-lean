/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSignExtension
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthPermutationFlag

/-! Genuine coordinate-flag permutations restrict to the actual twelve dodecad coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The displayed twelve original dodecad addresses are distinct. -/
theorem generatedEighth_dodecad_coordinates_injective :
    Function.Injective generatedEighthDodecadCoordinates := by decide +kernel

private theorem range_certificate : ∀ i : Fin 24,
    golayBooleanCast (Nat.testBit 0xc5066f i.val) ≠ 0 ↔
      ∃ j : Fin 12, generatedEighthDodecadCoordinates j = i := by decide +kernel

/-- The displayed twelve addresses cover exactly the actual dodecad support. -/
theorem generatedEighth_dodecad_coordinate_range (i : Fin 24) :
    generatedEighthDodecadWord.val i ≠ 0 ↔
      ∃ j : Fin 12, generatedEighthDodecadCoordinates j = i := by
  rw [generatedEighth_dodecad_coordinate]
  exact range_certificate i

/-- Every actual flag permutation restricts to a genuine permutation of its twelve addresses. -/
theorem generatedEighth_dodecad_permutation_restrict (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedEighthPermutationFlagStabilizer) :
    ∃ q : Equiv.Perm (Fin 12), ∀ i,
      generatedEighthDodecadCoordinates (q i) = p.val (generatedEighthDodecadCoordinates i) := by
  have hw := ((generatedEighthPermutationFlagStabilizer_mem p).mp hp).2
  have hex : ∀ i : Fin 12, ∃ j : Fin 12,
      generatedEighthDodecadCoordinates j = p.val (generatedEighthDodecadCoordinates i) := by
    intro i
    apply (generatedEighth_dodecad_coordinate_range _).mp
    have hi := (generatedEighth_dodecad_coordinate_range (generatedEighthDodecadCoordinates i)).mpr
      ⟨i, rfl⟩
    have he := congrFun hw (p.val (generatedEighthDodecadCoordinates i))
    change generatedEighthDodecadWord.val (p.val.symm
      (p.val (generatedEighthDodecadCoordinates i))) = _ at he
    rw [Equiv.symm_apply_apply] at he
    exact he ▸ hi
  choose q hq using hex
  have hqi : Function.Injective q := by
    intro i j hij
    apply generatedEighth_dodecad_coordinates_injective
    apply p.val.injective
    exact (hq i).symm.trans ((congrArg generatedEighthDodecadCoordinates hij).trans (hq j))
  exact ⟨Equiv.ofBijective q ⟨hqi, Finite.surjective_of_injective hqi⟩, hq⟩

/-- Comparing a sign pattern with a permutation of itself always gives even total parity. -/
theorem generatedEighth_dodecad_sign_difference_even (s : Fin 12 → ZMod 2)
    (q : Equiv.Perm (Fin 12)) : ∑ i, (s i + s (q.symm i)) = 0 := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp q.symm s, ZModModule.add_self]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
