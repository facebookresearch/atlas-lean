/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Kraus
import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.ChoiTheorem
import Mathlib.Tactic.NormNum

/-!
# Finite matrix Kraus and Choi API examples

The bundled constructors are exercised on actual complex matrices, including
empty input/output indices and an empty Kraus family. No positivity witness is
supplied to build these maps: complete positivity comes from the constructors.
-/

noncomputable section
open Matrix CompletelyPositiveMap
open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra Kronecker ComplexOrder
namespace CompletelyPositiveKrausSmoke

-- The identity Kraus operator computes the identity map on a two-dimensional
-- matrix algebra; this checks both matrix order and conjugate-transpose order.
example (X : Matrix (Fin 2) (Fin 2) ℂ) :
    singleKraus (1 : Matrix (Fin 2) (Fin 2) ℂ) X = X := by
  simp only [singleKraus_apply, Matrix.conjTranspose_one, one_mul, mul_one]

-- A zero rectangular operator still produces a genuine bundled CP map.
example (X : Matrix (Fin 2) (Fin 2) ℂ) :
    singleKraus (0 : Matrix (Fin 1) (Fin 2) ℂ) X = 0 := by
  simp only [singleKraus_apply, Matrix.zero_mul]

-- The input matrix algebra may have size zero.
example (X : Matrix (Fin 0) (Fin 0) ℂ) :
    singleKraus (0 : Matrix (Fin 2) (Fin 0) ℂ) X = 0 := by
  simp only [singleKraus_apply, Matrix.zero_mul]

-- The output matrix algebra may independently have size zero.
example (X : Matrix (Fin 2) (Fin 2) ℂ) :
    singleKraus (0 : Matrix (Fin 0) (Fin 2) ℂ) X = 0 := by
  simp only [singleKraus_apply, Matrix.zero_mul]

-- An empty family gives the zero CP map, with no nonempty family assumption.
example (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kraus (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ) X = 0 :=
  kraus_fin_zero_apply _ X

-- A non-isometric scalar Kraus operator has its actual squared amplitude.
example :
    singleKraus (2 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 4 := by
  have htwo : (2 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = (2 : ℂ) := rfl
  norm_num [singleKraus_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, htwo]

-- The Choi equivalence reconstructs the same computed CP map from its own
-- positive semidefinite Choi matrix, rather than a caller-provided matrix model.
example (K : Matrix (Fin 2) (Fin 2) ℂ) :
    (choiEquivPosSemidef (m := Fin 2) (n := Fin 2)).symm
        ((choiEquivPosSemidef (m := Fin 2) (n := Fin 2)) (singleKraus K)) = singleKraus K :=
  Equiv.symm_apply_apply _ _

-- The finite-dimensional Kraus existence API retains an empty input domain.
example : ∃ (k : ℕ) (K : Fin k → Matrix (Fin 2) (Fin 0) ℂ),
    singleKraus (0 : Matrix (Fin 2) (Fin 0) ℂ) = kraus K :=
  exists_kraus (singleKraus (0 : Matrix (Fin 2) (Fin 0) ℂ))

end CompletelyPositiveKrausSmoke
