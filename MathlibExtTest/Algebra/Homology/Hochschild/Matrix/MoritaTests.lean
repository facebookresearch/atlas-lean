/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Morita

/-!
# Corner-choice independence on Hochschild homology

Different matrix corners give the same inverse to finite trace on homology.
The client uses cancellation by the trace isomorphism, for independent
coefficient worlds and arbitrary common lift height.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ModuleCat.Algebra.Hochschild.Matrix

universe t u v w z

namespace MathlibExtTest.HochschildMatrixMorita

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- Any two corners induce the same homology map because both invert the finite trace. -/
theorem corner_choice_homology (b b' : ι) (n : ℕ) :
    HomologicalComplex.homologyMap (Morita.cornerChainMapAt.{t} k A M ι b) n =
      HomologicalComplex.homologyMap (Morita.cornerChainMapAt.{t} k A M ι b') n := by
  let f := HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M ι) n
  let _ : IsIso f := (Morita.finiteHomologyIsoAt.{t} k A M ι b n).isIso_hom
  apply (cancel_mono f).mp
  exact (Morita.finiteHomologyIsoAt.{t} k A M ι b n).inv_hom_id.trans
    (Morita.finiteHomologyIsoAt.{t} k A M ι b' n).inv_hom_id.symm

/-- The coefficient carrier and common lift can both lie above a noncommutative algebra. -/
example (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (traceChainMapAt.{3} ℤ (Matrix (Fin 2) (Fin 2) ℤ)
        (ULift.{2} (Matrix (Fin 2) (Fin 2) ℤ)) (Fin 3)) n) :=
  (Morita.finiteHomologyIsoAt.{3} ℤ (Matrix (Fin 2) (Fin 2) ℤ)
    (ULift.{2} (Matrix (Fin 2) (Fin 2) ℤ)) (Fin 3) 0 n).isIso_hom

end MathlibExtTest.HochschildMatrixMorita
