/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.LMapFibre

@[expose] public noncomputable section

namespace CartierLMapFibreTest

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders: a critical index in terms of `Π` and `V`. -/
theorem exactSource {B : Type u} [CommRing B] [CharP B p] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (n : ℕ) :
    CritChart.IsCritical X j n ↔
      ∀ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
        X.piOp f = CartierModule.verschiebung g :=
  X.critChart_isCritical_iff j n

/-- Consumer with the original binders: an `L`-map lifts Frobenius through `λ`. -/
theorem exactSourceIsLMap {B : Type u} [CommRing B] [CharP B p] {X : FormalODModule p B}
    {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod} (h : X.IsLMap j L) :
    X.lambdaN.comp L = CartierModule.frobenius :=
  h.lambdaN_comp

/-- `Π` commutes with Verschiebung. -/
example {B : Type u} [CommRing B] [CharP B p] (X : FormalODModule p B) :
    X.piOp.comp CartierModule.verschiebung = CartierModule.verschiebung.comp X.piOp :=
  X.piOp_comp_verschiebung

/-- The fibre map of an `L`-map lands in the Lie algebra `M ⧸ V M`. -/
example {B : Type u} [CommRing B] [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B}
    {L : CartierModule p X.F →+ X.NMod} (h : X.IsLMap j L) :
    h.eta →+ CartierModule p X.F ⧸ (CartierModule.verschiebung (p := p) (Φ := X.F)).range :=
  h.u

end CartierLMapFibreTest
