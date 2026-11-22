/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointPrismBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkedMinimumMaximumPointIso

/-!
# Original minimally parameter-marked native endpoint prisms

The original positive-dimensional prism only uses its marked boundary
verticals. Its target row need not mark every scalar edge. In degree
zero the original minimally and maximally marked point are the same
terminal carrier through their original identity isomorphism. This
retains the entire original minimally parameter-marked target prism,
all native base equations and the original marked verticals under an
actual coherent-model fibration.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original endpoint point name retains the canonical whole point marking isomorphism. -/
abbrev nativeEndpointMinimalPointIso : min (Δ[0] : SSet.{u}) ≅ max (Δ[0] : SSet.{u}) :=
  minimumMaximumPointIso

/-- The inverse point isomorphism retains the identity on the entire original point. -/
theorem nativeEndpointMinimalPointIso_inv_hom :
    nativeEndpointMinimalPointIso.{u}.inv.hom = 𝟙 (Δ[0] : SSet.{u}) :=
  minimumMaximumPointIso_inv_hom

/-- The original whole degree-zero minimally marked prism can be read with maximal point marking through the same
original identity map. -/
theorem nativeEndpointMinimalPointTensor_inv_hom :
    (prodMap nativeEndpointMinimalPointIso.{u}.inv (𝟙 (max (Δ[1] : SSet.{u})))).hom =
      𝟙 ((Δ[0] : SSet.{u}) ⊗ Δ[1]) := by
  ext n a
  apply Prod.ext
  · exact congrArg (fun f => f.app n a.1) nativeEndpointMinimalPointIso_inv_hom
  · rfl

/-- Every original minimally parameter-marked scalar-boundary endpoint prism retains its whole native lift and all
original marked verticals, with no diagram or base fibrancy premise. -/
theorem nativeUnstraightening_endpointPrism_boundary_minimal (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (n : ℕ)
    (H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (c : (Δ[n] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : prod (min (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G)
    (hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 1 ≫ H = (boundary.{u} n).ι ≫ c)
    (hKsrc : prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K.hom = c ≫ ((nativeUnstraightening B).map q).left.hom)
    (hHK : H ≫ ((nativeUnstraightening B).map q).left.hom = ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ K.hom)
    (hHvert : nativePrismOneVerticalsMarked B F H) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ L : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ L = H ∧
        prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ L = c ∧
        L ≫ ((nativeUnstraightening B).map q).left.hom = K.hom ∧ nativePrismOneVerticalsMarked B F L := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  by_cases hn : n = 0
  · subst n
    let Kmax : prod (max (Δ[0] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G :=
      prodMap nativeEndpointMinimalPointIso.inv (𝟙 (max (Δ[1] : SSet.{u}))) ≫ K
    have hwhole : Kmax.hom = K.hom :=
      (congrArg (fun f => f ≫ K.hom) nativeEndpointMinimalPointTensor_inv_hom).trans (Category.id_comp K.hom)
    have htarget : prismSectionAt (Δ[0] : SSet.{u}) 1 ≫ Kmax.hom =
        c ≫ ((nativeUnstraightening B).map q).left.hom :=
      (congrArg (fun f => prismSectionAt (Δ[0] : SSet.{u}) 1 ≫ f) hwhole).trans hKsrc
    obtain ⟨L, hLr, hLt, hLp, hLv⟩ := nativeUnstraightening_endpointPrism_boundary_zero B q H c Kmax htarget hq
    exact ⟨L, hLr, hLt, hLp.trans hwhole, hLv⟩
  · exact nativeUnstraightening_endpointPrism_boundary_positive B q (Nat.one_le_iff_ne_zero.mpr hn)
      H c K.hom hHsrc hKsrc hHK hHvert hq

end SSet.Marked
