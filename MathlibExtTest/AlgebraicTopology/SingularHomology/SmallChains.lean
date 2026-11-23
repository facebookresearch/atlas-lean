/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSetQuasiIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.SmallChainsTests

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Refinement maps are reflexive. -/
theorem refinement_id {X : TopCat.{w}} {I : Type*} (R : C) (U : I → Set X) :
    smallChainMapOfLE R U U le_rfl = 𝟙 _ :=
  smallChainMapOfLE_refl R U

/-- Refinement maps compose strictly. -/
theorem refinement_comp {X : TopCat.{w}} {I J K : Type*}
    (R : C) (U : I → Set X) (V : J → Set X) (W : K → Set X)
    {hUV : subordinateCover U ≤ subordinateCover V}
    {hVW : subordinateCover V ≤ subordinateCover W} :
    smallChainMapOfLE R U V hUV ≫ smallChainMapOfLE R V W hVW =
      smallChainMapOfLE R U W (hUV.trans hVW) :=
  smallChainMapOfLE_comp R U V W

/-- Coefficient-natural refinement is compatible with inclusion into singular chains. -/
theorem refinement_comp_inclusion {X : TopCat.{w}} {I J : Type*}
    (U : I → Set X) (V : J → Set X)
    (h : subordinateCover U ≤ subordinateCover V) :
    smallChainMapOfLENatTrans C U V h ≫ smallChainInclusionNatTrans C V =
      smallChainInclusionNatTrans C U :=
  smallChainMapOfLENatTrans_comp_inclusion C U V h

/-- The public iterated-subdivision homotopy has identity as its first endpoint. -/
theorem subdivision_homotopy_witness
    {X : TopCat.{w}} {I : Type*} (R : C) (U : I → Set X) (k : ℕ) :
  ∃ H : Homotopy (𝟙 (smallChainComplex (C := C) R U))
        (smallSubdivisionIterateHomULift R U k),
      ∀ i j, H.hom i j = smallSubdivisionIterateHomotopyLiftULift R U k i j :=
  ⟨smallSubdivisionIterateHomotopyULift R U k,
    fun i j ↦ smallSubdivisionIterateHomotopyULift_hom R U k i j⟩

/-- The public homotopy exposes its componentwise witness. -/
theorem subdivision_homotopy_component
    {X : TopCat.{w}} {I : Type*} (R : C) (U : I → Set X) (k i j : ℕ) :
    (smallSubdivisionIterateHomotopyULift R U k).hom i j =
      smallSubdivisionIterateHomotopyLiftULift R U k i j :=
  smallSubdivisionIterateHomotopyULift_hom R U k i j

/-- Consequently, iterated subdivision induces the identity on small-chain homology. -/
theorem subdivision_homology_endpoint_identity
    {X : TopCat.{w}} {I : Type*} (R : C) (U : I → Set X) (k n : ℕ)
    [(smallChainComplex (C := C) R U).HasHomology n] :
    HomologicalComplex.homologyMap (smallSubdivisionIterateHomULift R U k) n =
      𝟙 ((smallChainComplex (C := C) R U).homology n) :=
  smallSubdivisionIterateHomULift_homologyMap_eq_id R U k n

section QuasiIso

variable {D : Type u} [Category.{v} D] [Abelian D] [HasCoproducts.{w} D]

/-- The two-set inclusion is a coefficient-natural quasi-isomorphism at generic scale. -/
theorem two_set_inclusion_quasiIso
    (G : D) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G) {X : TopCat.{w}} (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    (HomologicalComplex.quasiIso D (ComplexShape.down ℕ)).functorCategory D
      (smallChainInclusionNatTrans D (smallCoverBoth A B)) :=
  smallChainInclusionNatTrans_twoSet_quasiIsoULift G hG A B hcover

end QuasiIso

end AlgebraicTopology.SmallChainsTests
