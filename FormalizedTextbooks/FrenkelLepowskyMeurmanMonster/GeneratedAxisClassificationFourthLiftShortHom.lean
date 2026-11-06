/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-! Genuine extraspecial homomorphisms from finite binary matrix and central-phase certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The entire central correction, including its linear diagonal terms. -/
def generatedFourthLiftQMatrixPhase (N : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (v : Fin 24 → ZMod 2) : ZMod 2 := Matrix.toBilin' N v v

/-- Polarization of the literal central-bit matrix. -/
theorem generatedFourth_lift_q_matrix_phase_add (N : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (u v : Fin 24 → ZMod 2) :
    generatedFourthLiftQMatrixPhase N (u + v) =
      generatedFourthLiftQMatrixPhase N u + generatedFourthLiftQMatrixPhase N v +
        Matrix.toBilin' N u v + Matrix.toBilin' N v u := by
  unfold generatedFourthLiftQMatrixPhase
  simp only [map_add, LinearMap.add_apply]
  abel

/-- Equality of bilinear forms propagates from coordinate pairs to every vector pair. -/
theorem generatedFourth_lift_bilinear_basis_ext {n : ℕ}
    (B C : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2))
    (hc : ∀ i j, B (Pi.single i 1) (Pi.single j 1) =
      C (Pi.single i 1) (Pi.single j 1)) (u v : Fin n → ZMod 2) : B u v = C u v := by
  have h : B = C := by
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin n))
    simpa only [Pi.basisFun_apply] using hc
  rw [h]

/-- Basis-level cocycle certificates imply the actual identity on every binary vector pair. -/
theorem generatedFourth_lift_q_matrix_cocycle
    (M N : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hc : ∀ i j, qBeta (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) =
      qBeta (Pi.single i 1) (Pi.single j 1) + N i j + N j i)
    (u v : Fin 24 → ZMod 2) :
    qBeta (M *ᵥ u) (M *ᵥ v) = qBeta u v + Matrix.toBilin' N u v + Matrix.toBilin' N v u := by
  have hq (a b : Fin 24 → ZMod 2) : qBilin a b = qBeta a b := rfl
  have hh : ∀ i j,
      (LinearMap.BilinForm.comp qBilin M.toLin' M.toLin')
        (Pi.single i 1) (Pi.single j 1) =
      (qBilin + Matrix.toBilin' N + LinearMap.flip (Matrix.toBilin' N))
        (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
      LinearMap.add_apply, LinearMap.flip_apply, hq, Matrix.toBilin'_single]
    exact hc i j
  have h := generatedFourth_lift_bilinear_basis_ext _ _ hh u v
  simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
    LinearMap.add_apply, LinearMap.flip_apply, hq] using h

/-- A finite matrix and its certified central phase define a genuine homomorphism of actual Q. -/
def generatedFourthLiftQMatrixHom (M N : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hc : ∀ i j, qBeta (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) =
      qBeta (Pi.single i 1) (Pi.single j 1) + N i j + N j i) : Q →* Q where
  toFun q := ⟨ofAdd (M *ᵥ toAdd q.base), ofAdd (toAdd q.coeff +
    generatedFourthLiftQMatrixPhase N (toAdd q.base))⟩
  map_one' := by
    apply NormalizedCocycleExtension.Extension.ext
    · change ofAdd (M *ᵥ 0) = 1
      simp only [Matrix.mulVec_zero, ofAdd_zero]
    · change ofAdd (0 + generatedFourthLiftQMatrixPhase N 0) = 1
      simp [generatedFourthLiftQMatrixPhase]
  map_mul' q r := by
    apply NormalizedCocycleExtension.Extension.ext
    · change ofAdd (M *ᵥ (toAdd q.base + toAdd r.base)) =
        ofAdd (M *ᵥ toAdd q.base + M *ᵥ toAdd r.base)
      rw [Matrix.mulVec_add]
    · apply toAdd.injective
      change toAdd q.coeff + toAdd r.coeff + qBeta (toAdd q.base) (toAdd r.base) +
          generatedFourthLiftQMatrixPhase N (toAdd q.base + toAdd r.base) =
        (toAdd q.coeff + generatedFourthLiftQMatrixPhase N (toAdd q.base)) +
          (toAdd r.coeff + generatedFourthLiftQMatrixPhase N (toAdd r.base)) +
            qBeta (M *ᵥ toAdd q.base) (M *ᵥ toAdd r.base)
      rw [generatedFourth_lift_q_matrix_phase_add, generatedFourth_lift_q_matrix_cocycle M N hc]
      abel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
