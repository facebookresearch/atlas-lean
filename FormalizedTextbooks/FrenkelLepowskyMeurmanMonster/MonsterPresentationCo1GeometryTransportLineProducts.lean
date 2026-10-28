/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intermediate checked products retain the literal actual two-core conjugation transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportColumns

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Three complete finite product certificates compose the same literal actual line transport,
without evaluating an unshared four-matrix expression during certificate checking. -/
theorem monsterCo1GeometryTransport_matrix_line_products (g h : Co1) (k : Fin 15)
    (A Ai B E F C : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hg : ∀ v, co1BinaryAction g v = A *ᵥ v)
    (hgi : ∀ v, co1BinaryAction g⁻¹ v = Ai *ᵥ v)
    (hh : ∀ v, co1BinaryAction h v = B *ᵥ v)
    (hE : A * monsterCo1GeometryTransportOperatorMatrix k = E)
    (hF : E * Ai = F) (hC : F * B = C) :
    ∀ v, co1BinaryAction (g * monsterCo1GeometryTransportOperator k * g⁻¹ * h) v =
      C *ᵥ v := by
  apply monsterCo1GeometryTransport_matrix_line g h k A Ai B C hg hgi hh
  rw [hE, hF, hC]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
