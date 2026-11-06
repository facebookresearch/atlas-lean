/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact Conway equivariance and squares for the original nonabelian source quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalBinaryQuotient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentationAction

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source automorphisms induce the exact actual Conway action
on the binary quotient. -/
theorem co1UniversalIntoBinary_action (g : Co1) (x : Co1UniversalPresentation) :
    co1UniversalIntoBinary (co1UniversalRepresentation g x) =
      Multiplicative.ofAdd (co1BinaryAction g (co1UniversalIntoBinary x).toAdd) := by
  let a : Multiplicative (Fin 24 → ZMod 2) →* Multiplicative (Fin 24 → ZMod 2) :=
    (co1BinaryAction g).toLinearMap.toAddMonoidHom.toMultiplicative
  have h : co1UniversalIntoBinary.comp (co1UniversalActionEnd g) =
      a.comp co1UniversalIntoBinary := by
    apply PresentedGroup.ext
    intro p
    change co1UniversalIntoBinary (co1UniversalActionEnd g (PresentedGroup.of p)) =
      a (co1UniversalIntoBinary (PresentedGroup.of p))
    rw [co1UniversalActionEnd_point, co1UniversalIntoBinary_point (g • p),
      co1UniversalIntoBinary_point p]
    rfl
  exact DFunLike.congr_fun h x

/-- Every original source square belongs to the exact source commutator subgroup. -/
theorem co1Universal_square_mem_commutator (x : Co1UniversalPresentation) :
    x ^ 2 ∈ commutator Co1UniversalPresentation := by
  rw [← co1UniversalIntoBinary_ker]
  change co1UniversalIntoBinary (x ^ 2) = 1
  rw [pow_two, map_mul]
  change (co1UniversalIntoBinary x).toAdd + (co1UniversalIntoBinary x).toAdd = 0
  exact ZModModule.add_self _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
