/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.MassTransport
import Code.FrontierA.FiniteTargetTransport

open MeasureTheory Set

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ} {E : Type*}






theorem finiteTarget_massTransport_origin_null
    [MulAction (Multiplicative (Site d)) E]
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (C : ConfigSpace E → Set (Site d))
    (N : ConfigSpace E → Finset (Site d))
    (hmeas : ∀ x y, Measurable (fun omega =>
      finiteTargetTransport (C omega) (N omega) x y))
    (hdiag : IsDiagonallyInvariantTransport (fun x y omega =>
      finiteTargetTransport (C omega) (N omega) x y)) :
    mu {omega | (C omega).Infinite ∧ (N omega).Nonempty ∧
      (0 : Site d) ∈ N omega} = 0 := by
  apply lattice_mass_transport_forbidden_event_null mu hinv
    (fun x y omega => finiteTargetTransport (C omega) (N omega) x y)
    hmeas hdiag
  · intro omega
    exact finiteTargetTransport_outgoing_le_one (C omega) (N omega) 0
  · intro omega homega
    exact finiteTargetTransport_incoming_eq_top
      (C omega) (N omega) homega.1 homega.2.1 homega.2.2

end StatMech.FrontierA
