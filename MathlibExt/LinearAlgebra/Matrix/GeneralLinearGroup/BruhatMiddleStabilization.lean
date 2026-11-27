/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialSLStabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMonomialUniqueness
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryStabilizationCompatibility
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialMatrixStabilizationCompatibility

/-!
# Stabilization of the Bruhat middle factor

Shows that the monomial middle factor in a special-linear Bruhat decomposition
commutes with successor stabilization. The proof stabilizes both upper factors
and uses uniqueness of the monomial factor.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {F : Type*} [Field F] {n : ℕ}

@[simp] theorem bruhatMiddle_stabilization
    (g : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (Matrix.SpecialLinearGroup.stabilization F g) =
      monomialSLSuccHom (R := F) (bruhatMiddle g) := by
  have hFact := bruhat_factorizationSL (F := F) (ι := Fin n) g
  have hStab : Matrix.SpecialLinearGroup.stabilization F g =
      UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatLeft g)) *
        monomialSLHom F (Fin (n + 1)) (monomialSLSuccHom (R := F) (bruhatMiddle g)) *
        UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatRight g)) := by
    calc Matrix.SpecialLinearGroup.stabilization F g
        = Matrix.SpecialLinearGroup.stabilization F
            (UpperElementary.toSLHom (bruhatLeft g) *
              monomialSLHom F (Fin n) (bruhatMiddle g) *
              UpperElementary.toSLHom (bruhatRight g)) := by
          rw [← hFact]
      _ = Matrix.SpecialLinearGroup.stabilization F
            (UpperElementary.toSLHom (bruhatLeft g) *
              monomialSLHom F (Fin n) (bruhatMiddle g)) *
          Matrix.SpecialLinearGroup.stabilization F
            (UpperElementary.toSLHom (bruhatRight g)) := by
          rw [MonoidHom.map_mul]
      _ = (Matrix.SpecialLinearGroup.stabilization F (UpperElementary.toSLHom (bruhatLeft g)) *
            Matrix.SpecialLinearGroup.stabilization F (monomialSLHom F (Fin n) (bruhatMiddle g))) *
          Matrix.SpecialLinearGroup.stabilization F (UpperElementary.toSLHom (bruhatRight g)) := by
          rw [MonoidHom.map_mul]
      _ = (UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatLeft g)) *
            monomialSLHom F (Fin (n + 1)) (monomialSLSuccHom (R := F) (bruhatMiddle g))) *
          UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatRight g)) := by
          rw [← UpperElementary.toSLHom_stabilization (R := F) (n := n) (u := bruhatLeft g),
            ← monomialSLHom_monomialSLSuccHom (R := F) (n := n) (m := bruhatMiddle g),
            ← UpperElementary.toSLHom_stabilization (R := F) (n := n) (u := bruhatRight g)]
      _ = UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatLeft g)) *
          monomialSLHom F (Fin (n + 1)) (monomialSLSuccHom (R := F) (bruhatMiddle g)) *
          UpperElementary.toSLHom (UpperElementary.stabilization F n (bruhatRight g)) := by
          rw [mul_assoc]
  exact bruhatMiddle_factorization_elim
    (Matrix.SpecialLinearGroup.stabilization F g)
    (UpperElementary.stabilization F n (bruhatLeft g))
    (monomialSLSuccHom (R := F) (bruhatMiddle g))
    (UpperElementary.stabilization F n (bruhatRight g))
    hStab

end Matrix.GeneralLinearGroup
