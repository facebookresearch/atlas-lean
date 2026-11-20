/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardTwist









open scoped BigOperators

namespace StatMech.FrontierA



theorem surfaceQuadraticParity_add_spin {g : Nat}
    (lambda mu : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    surfaceQuadraticParity (lambda + mu) h =
      surfaceQuadraticParity lambda h + surfaceSpinLinearParity mu h := by
  unfold surfaceQuadraticParity surfaceSpinLinearParity
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel



theorem surfaceQuadraticEvenPolynomial_shift_twist {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda mu : SurfaceSpinStructure g)
    (weight : Sym2 V → Complex) :
    surfaceQuadraticEvenPolynomial G edgeClass lambda
        (surfaceTwistedEdgeWeight edgeClass mu weight) =
      surfaceQuadraticEvenPolynomial G edgeClass (lambda + mu) weight := by
  unfold surfaceQuadraticEvenPolynomial
  apply Finset.sum_congr rfl
  intro F hF
  rw [prod_surfaceTwistedEdgeWeight,
    surfaceQuadraticParity_add_spin, surfaceParitySign_add]
  unfold surfaceHomologyCharacter
  push_cast
  ring



theorem surface_twisted_kacWard_det_square_of_shifted_base {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hbase : ∀ w : Sym2 V → Complex,
      (1 - kwGraphTransition G w phase).det =
        surfaceQuadraticEvenPolynomial G edgeClass lambda w ^ 2)
    (mu : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass mu weight).det =
      surfaceQuadraticEvenPolynomial G edgeClass (lambda + mu) weight ^ 2 := by
  unfold surfaceTwistedKacWardMatrix
  rw [hbase, surfaceQuadraticEvenPolynomial_shift_twist]

end StatMech.FrontierA
