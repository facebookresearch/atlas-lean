/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact source Conway action transports to the existing extraspecial group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoQEquiv

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source action conjugated through the constructed extraspecial isomorphism. -/
def co1UniversalQAction
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) : Co1 →* MulAut Q :=
  (MulAut.congr (co1UniversalQEquiv hfinite hcard hne).symm).toMonoidHom.comp
    co1UniversalRepresentation

/-- The constructed action is exactly conjugate to the existing full source action. -/
theorem co1UniversalQAction_conjugates
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (g : Co1) (x : Q) :
    co1UniversalQEquiv hfinite hcard hne (co1UniversalQAction hfinite hcard hne g x) =
      co1UniversalRepresentation g (co1UniversalQEquiv hfinite hcard hne x) := by
  change co1UniversalQEquiv hfinite hcard hne
    ((co1UniversalQEquiv hfinite hcard hne).symm
      (co1UniversalRepresentation g (co1UniversalQEquiv hfinite hcard hne x))) = _
  exact (co1UniversalQEquiv hfinite hcard hne).apply_symm_apply _

/-- The transported action on the extraspecial quotient is the actual full Conway binary action. -/
theorem co1UniversalQAction_binary
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (g : Co1) :
    qBinaryAction (co1UniversalQAction hfinite hcard hne g) = co1BinaryAction g := by
  apply LinearEquiv.ext
  intro v
  let x : Q := ⟨Multiplicative.ofAdd v, 1⟩
  change qBinaryAction (co1UniversalQAction hfinite hcard hne g) (qQuotHom x).toAdd =
    co1BinaryAction g (qQuotHom x).toAdd
  calc
    _ = (qQuotHom (co1UniversalQAction hfinite hcard hne g x)).toAdd :=
      qBinaryAction_apply _ _
    _ = (co1UniversalIntoBinary (co1UniversalQEquiv hfinite hcard hne
        (co1UniversalQAction hfinite hcard hne g x))).toAdd :=
      congrArg Multiplicative.toAdd
        (co1UniversalQEquiv_binary hfinite hcard hne _).symm
    _ = (co1UniversalIntoBinary (co1UniversalRepresentation g
        (co1UniversalQEquiv hfinite hcard hne x))).toAdd := by
      rw [co1UniversalQAction_conjugates]
    _ = co1BinaryAction g
        (co1UniversalIntoBinary (co1UniversalQEquiv hfinite hcard hne x)).toAdd :=
      congrArg Multiplicative.toAdd (co1UniversalIntoBinary_action g _)
    _ = co1BinaryAction g (qQuotHom x).toAdd := by rw [co1UniversalQEquiv_binary]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
