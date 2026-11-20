/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamEq22AssociationClosure
import Code.FrontierA.GrahamWeightedBridgeGap





open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]





theorem grahamExpectation_correctedBound_of_cutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hassoc : GrahamCutPositiveAssociation G beta J m) :
    expectationJ G beta J {i, j, k, l} -
        expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
        expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
        expectationJ G beta J {i, l} * expectationJ G beta J {j, k} <=
      -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
        expectationJ G beta J {k, m} * expectationJ G beta J {l, m}) +
      -2 * ((expectationJ G beta J {i, k} -
          expectationJ G beta J {i, m} * expectationJ G beta J {m, k}) *
        (expectationJ G beta J {k, j} -
          expectationJ G beta J {k, m} * expectationJ G beta J {m, j}) *
        expectationJ G beta J {k, l}) +
      -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
        (expectationJ G beta J {k, i} -
          expectationJ G beta J {k, m} * expectationJ G beta J {m, i}) *
        (expectationJ G beta J {i, l} -
          expectationJ G beta J {i, m} * expectationJ G beta J {m, l})) := by
  let Z := currentSum G beta J ∅
  let N :=
    2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
      2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
        currentSum G beta J {k, l} * Z -
      2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m
  let R :=
    -2 * Z * currentSum G beta J {k, l} *
      (sourcePairDisconnSum G beta J {i, k} ∅ i m *
        sourcePairDisconnSum G beta J {k, j} ∅ k m / Z ^ 2) -
      2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m *
        (sourcePairDisconnSum G beta J {k, i} ∅ k m *
          sourcePairDisconnSum G beta J {i, l} ∅ i m / Z ^ 2)
  have hnorm := grahamExpectation_preEq22 G beta J
    hij hik hil hjk hjl hkl him hjm hkm hlm
  have hcur := grahamEq22_correction_upper_bound_of_cutPositiveAssociation
    G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm hassoc
  dsimp only at hnorm hcur
  change N <= R at hcur
  have hZ : 0 < Z := StatMech.Ising.acr_currentSum_empty_pos G beta J
  have hdiv : N / Z ^ 4 <= R / Z ^ 4 :=
    (div_le_div_iff_of_pos_right (pow_pos hZ 4)).2 hcur
  have hbik := expectationBridgeGap_eq_sourcePairDisconn
    G beta J hik him hkm
  have hbkj := expectationBridgeGap_eq_sourcePairDisconn
    G beta J hjk.symm hkm hjm
  have hbki := expectationBridgeGap_eq_sourcePairDisconn
    G beta J hik.symm hkm him
  have hbil := expectationBridgeGap_eq_sourcePairDisconn
    G beta J hil him hlm
  have haux := auxiliaryConnectionMass_div_eq G beta J hij him hjm
  have haux_mul :
      StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m =
        (expectationJ G beta J {i, m} * expectationJ G beta J {j, m}) *
          Z ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hZ.ne')).mp
    simpa [Z] using haux
  have hklrep := current_representation
    (G := G) beta J ({k, l} : Finset V)
  change
    expectationJ G beta J {i, j, k, l} -
        expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
        expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
        expectationJ G beta J {i, l} * expectationJ G beta J {j, k} +
        2 * expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
          expectationJ G beta J {k, m} * expectationJ G beta J {l, m} =
      N / Z ^ 4 at hnorm
  calc
    expectationJ G beta J {i, j, k, l} -
          expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
          expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
          expectationJ G beta J {i, l} * expectationJ G beta J {j, k}
        = N / Z ^ 4 -
            2 * expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
              expectationJ G beta J {k, m} * expectationJ G beta J {l, m} := by
          linarith
    _ <= R / Z ^ 4 -
          2 * expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
            expectationJ G beta J {k, m} * expectationJ G beta J {l, m} := by
          linarith
    _ = -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
          expectationJ G beta J {k, m} * expectationJ G beta J {l, m}) +
        -2 * ((expectationJ G beta J {i, k} -
            expectationJ G beta J {i, m} * expectationJ G beta J {m, k}) *
          (expectationJ G beta J {k, j} -
            expectationJ G beta J {k, m} * expectationJ G beta J {m, j}) *
          expectationJ G beta J {k, l}) +
        -2 * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
          (expectationJ G beta J {k, i} -
            expectationJ G beta J {k, m} * expectationJ G beta J {m, i}) *
          (expectationJ G beta J {i, l} -
            expectationJ G beta J {i, m} * expectationJ G beta J {m, l})) := by
      rw [hbik, hbkj, hbki, hbil, hklrep]
      dsimp [R]
      rw [haux_mul]
      dsimp [Z]
      field_simp [hZ.ne']
      ring_nf
      field_simp [hZ.ne']

end StatMech.FrontierA
