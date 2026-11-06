/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Explicit duality and full Conway invariance of the actual hyperbolic polar form. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine polar pairing, bundled as a bilinear form. -/
def co1BinaryPolar : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) :=
  qBilin + qBilin.flip

/-- The explicit dual coordinates invert the full polar pairing. -/
theorem co1BinaryPolar_dual_left (v : Fin 24 → ZMod 2) :
    qDualVector (co1BinaryPolar v) = v := by
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective i
  cases j with
  | inl j =>
    rw [finSumFinEquiv_apply_left]
    simp only [qDualVector, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    change qBeta v (Pi.single (Fin.natAdd 12 j) 1) +
      qBeta (Pi.single (Fin.natAdd 12 j) 1) v = v (Fin.castAdd 12 j)
    rw [qBeta_single_second, qBeta_left_single_second, add_zero]
  | inr j =>
    rw [finSumFinEquiv_apply_right]
    simp only [qDualVector, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    change qBeta v (Pi.single (Fin.castAdd 12 j) 1) +
      qBeta (Pi.single (Fin.castAdd 12 j) 1) v = v (Fin.natAdd 12 j)
    rw [qBeta_right_single_first, qBeta_single_first, zero_add]

/-- Every functional is the polar pairing with its explicit dual vector. -/
theorem co1BinaryPolar_dual_right
    (f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    co1BinaryPolar (qDualVector f) = f := qPolarLinear_dual f

/-- The actual polar form identifies the genuine 24-dimensional binary space with its dual. -/
def co1BinaryPolarEquiv : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2]
    ((Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  LinearEquiv.ofBijective co1BinaryPolar
    ⟨fun u v h => by
      simpa only [co1BinaryPolar_dual_left] using congrArg qDualVector h,
      fun f => ⟨qDualVector f, co1BinaryPolar_dual_right f⟩⟩

/-- The actual polar pairing is exactly the cross term of the actual quadratic form. -/
theorem co1BinaryPolar_quadratic (u v : Fin 24 → ZMod 2) :
    co1BinaryPolar u v = squareQuad (u + v) - squareQuad u - squareQuad v := by
  change qBeta u v + qBeta v u = qBeta (u + v) (u + v) - qBeta u u - qBeta v v
  rw [qBeta_add_left, qBeta_add_right, qBeta_add_right]
  abel

/-- Every actual Conway element preserves the genuine polar pairing. -/
theorem co1BinaryPolar_invariant (g : Co1) (u v : Fin 24 → ZMod 2) :
    co1BinaryPolar (co1BinaryAction g u) (co1BinaryAction g v) = co1BinaryPolar u v := by
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective signsSubgroup g
  change co1BinaryPolar (leechBinaryAction e u) (leechBinaryAction e v) = _
  rw [co1BinaryPolar_quadratic, ← map_add, leechBinaryAction_squareQuad,
    leechBinaryAction_squareQuad, leechBinaryAction_squareQuad, co1BinaryPolar_quadratic]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
