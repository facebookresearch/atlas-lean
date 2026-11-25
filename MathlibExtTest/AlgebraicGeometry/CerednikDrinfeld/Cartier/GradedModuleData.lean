/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedModuleData

@[expose] public noncomputable section

namespace GradedCartierModuleDataTest

open CerednikDrinfeld

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders: `V ∘ F` is multiplication by `V 1`. -/
theorem exactSource {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData.{0, 0} p B j) (x : D.M) :
    D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x :=
  D.verschiebung_frobenius x

/-- The data is universe-polymorphic in both the base ring and the module. -/
example {B : Type 1} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData.{1, 2} p B j)
    (x : D.M) : D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x :=
  D.verschiebung_frobenius x

/-- A homogeneous `V`-basis forces `V` to be injective. -/
example {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData.{0, 0} p B j)
    {γ : Fin 2 → D.M} (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung :=
  h.verschiebung_injective

end GradedCartierModuleDataTest
