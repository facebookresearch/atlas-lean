/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeRationalCurveRealizations

/-!
# Native curve realization requests in the original source scope

Both sides and matrix maps are the original computed native objects.
No general regularity or Kashiwara theorem is assumed beyond this exact
rational punctured-line analytic connection scope.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeRationalCurveRealizationWanted

open _root_.CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.RegularSingularConnections
open MathlibExt.AlgebraicGeometry.NativeRationalCurveRealizations

variable (S : Finset ℂ)
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) (ModuleCat.{0} ℂ)]
  {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions)

/-- For any analytic connection de Rham data (requested as
`RegularSingularRiemannHilbertWanted.analytic_connection_deRham_data`; all such data are canonically
isomorphic), the ordinary curve de Rham complex is the horizontal one. -/
def_wanted actual_curve_de_rham_horizontal_iso (hA : PolesWithin S A)
    (D : AnalyticConnectionDeRhamData S r A hA) :
  ordinaryCurveDR S A hA D ≅ horizontalDR S A hA

def_wanted actual_curve_horizontal_matrix_maps (δ : RationalDerivative)
    {s : ℕ} (B : Matrix (Fin s) (Fin s) RationalFunctions)
    (G : Matrix (Fin s) (Fin r) RationalFunctions)
    (hA : PolesWithin S A) (hB : PolesWithin S B) (hG : PolesWithin S G)
    (hHorizontal : HorizontalMatrix δ A B G) : CurveGaugeSource S A hA B hB G hG

end WantedExt.AlgebraicGeometry.NativeRationalCurveRealizationWanted
