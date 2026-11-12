/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterTwoGhostPinned









namespace StatMech.Ising

noncomputable section




def lpTwoGhostPlusSectorVariance
    (a b c d e : Real) : Real :=
  (d + e) / (1 + c) - ((a + b) / (1 + c)) ^ 2


def lpTwoGhostMinusSectorVariance
    (a b c d e : Real) : Real :=
  (d - e) / (1 - c) - ((a - b) / (1 - c)) ^ 2




theorem lpTwoGhost_sectorVariance_sub_clear
    (a b c d e : Real) (hplus : Ne (1 + c) 0) (hminus : Ne (1 - c) 0) :
    (1 - c ^ 2) ^ 2 *
        (lpTwoGhostPlusSectorVariance a b c d e -
          lpTwoGhostMinusSectorVariance a b c d e) =
      2 * ((1 - c ^ 2) *
          ((e - d * c) - 2 * a * (b - a * c)) +
        2 * c * (b - a * c) ^ 2) := by
  unfold lpTwoGhostPlusSectorVariance lpTwoGhostMinusSectorVariance
  field_simp [hplus, hminus]
  ring






theorem lpTwoGhost_centeredCovariance_clear_current
    (A B C D E Z : Real) (hZ : Ne Z 0) :
    (1 - (C / Z) ^ 2) *
          (((E / Z) - (D / Z) * (C / Z)) -
            2 * (A / Z) * ((B / Z) - (A / Z) * (C / Z))) +
        2 * (C / Z) * ((B / Z) - (A / Z) * (C / Z)) ^ 2 =
      ((Z ^ 2 - C ^ 2) *
          (((E * Z - D * C) * Z) -
            2 * A * (B * Z - A * C)) +
        2 * C * (B * Z - A * C) ^ 2) / Z ^ 5 := by
  field_simp [hZ]

end

end StatMech.Ising
