/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.Pi

/-!
# Reconstruction and composite scalar extension for three different rings

The client reconstructs a K₀ class from its three components, extends
scalars through two independent families of ring maps, and recovers the
same reconstructed class after the factorwise extensions.
-/

public section

noncomputable section

universe u

namespace MathlibExtTest.KTheory.Ring.K0.PiTests

open AlgebraicKTheory AlgebraicKTheory.RingK0

/-- Finite-family reconstruction commutes with two actual scalar extensions,
with different rings allowed at all three coordinates. -/
theorem reconstructed_compositeScalarExtension
    {R S T : Fin 3 → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, CommRing (T i)] (φ : ∀ i, R i →+* S i) (ψ : ∀ i, S i →+* T i)
    (a : ∀ i, RingK0 (R i)) :
    mapRingHom (RingHom.pi (fun i => ((ψ i).comp (φ i)).comp (Pi.evalRingHom R i)))
        ((piEquiv R).symm a) =
      (piEquiv T).symm (fun i => mapRingHom (ψ i) (mapRingHom (φ i) (a i))) := by
  apply (piEquiv T).injective
  rw [(piEquiv T).apply_symm_apply]
  have h := DFunLike.congr_fun
    (piEquiv_naturality R T (fun i => (ψ i).comp (φ i))) ((piEquiv R).symm a)
  change piEquiv T
      (mapRingHom (RingHom.pi (fun i => ((ψ i).comp (φ i)).comp (Pi.evalRingHom R i)))
        ((piEquiv R).symm a)) =
    (fun i => mapRingHom ((ψ i).comp (φ i)) (piEquiv R ((piEquiv R).symm a) i)) at h
  rw [(piEquiv R).apply_symm_apply] at h
  exact h.trans (funext (fun i => DFunLike.congr_fun (mapRingHom_comp (φ i) (ψ i)) (a i)))

end MathlibExtTest.KTheory.Ring.K0.PiTests

end
