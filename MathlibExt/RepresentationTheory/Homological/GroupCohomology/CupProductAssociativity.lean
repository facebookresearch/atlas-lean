/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Counit
public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairingAssociativity
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneousBasic
public import MathlibExt.CategoryTheory.Monoidal.ComonObjIso
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality

/-!
# Coassociativity of the group-resolution cup diagonal

The universal cover of the group classifying space has its pointwise
cartesian comonoid structure.  Oplax linearization and the
Alexander--Whitney oplax structure transport it to the standard resolution;
the bar/standard isomorphism transports it once more to the bar resolution.

Consequently both `standardComplexDiagonal` and `barComplexDiagonal` are
coassociative with the canonical chain-complex associator.  These identities
are the chain-level input for arbitrary-degree associativity of the cup on
group cohomology.

## Main declarations

* `groupCohomology.standardComplexDiagonal_assoc`
* `groupCohomology.barComplexDiagonal_assoc`
* `groupCohomology.cup_assoc`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable (G : Type u) [Group G]

/-- The pointwise terminal map from the universal cover to the simplicial
monoidal unit. -/
def universalCoverCounit :
    classifyingSpaceUniversalCover G ⟶
      𝟙_ (SimplicialObject (Action (Type u) G)) where
  app _ :=
    { hom := ↾(fun _ => PUnit.unit)
      comm := fun _ => rfl }
  naturality := by
    intro X Y f
    ext x
    rfl

/-- The pointwise cartesian comonoid structure on the universal cover. -/
@[instance_reducible]
noncomputable def universalCoverComonObj :
    ComonObj (classifyingSpaceUniversalCover G) where
  counit := universalCoverCounit G
  comul := universalCoverDiagonal G
  counit_comul := by
    ext n x
    rfl
  comul_counit := by
    ext n x
    rfl
  comul_assoc := by
    ext n x
    rfl

variable (k : Type u) [CommRing k]

noncomputable local instance universalCoverComonObjInstance :
    ComonObj (classifyingSpaceUniversalCover G) :=
  universalCoverComonObj G

noncomputable local instance linearizedUniversalCoverComonObjInstance :
    ComonObj
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) :=
  Functor.obj.instComonObj _ (linearizationOnSimplicialObjects G k)

noncomputable local instance standardComplexComonObjInstance :
    ComonObj (Rep.standardComplex k G) :=
  Functor.obj.instComonObj _
    (AlgebraicTopology.alternatingFaceMapComplex (Rep k G))

noncomputable local instance barComplexComonObjInstance :
    ComonObj (Rep.barComplex k G) :=
  ComonObj.ofIso (Rep.barComplex.isoStandardComplex k G).symm

/-- The Alexander--Whitney diagonal on the standard group resolution is
coassociative. -/
theorem standardComplexDiagonal_assoc :
    standardComplexDiagonal G k ≫
        (Rep.standardComplex k G ◁ standardComplexDiagonal G k) =
      standardComplexDiagonal G k ≫
        (standardComplexDiagonal G k ▷ Rep.standardComplex k G) ≫
        (α_ (Rep.standardComplex k G)
          (Rep.standardComplex k G) (Rep.standardComplex k G)).hom :=
  ComonObj.comul_assoc (Rep.standardComplex k G)

/-- The transported Alexander--Whitney diagonal on the bar resolution is
coassociative. -/
theorem barComplexDiagonal_assoc :
    barComplexDiagonal G k ≫
        (Rep.barComplex k G ◁ barComplexDiagonal G k) =
      barComplexDiagonal G k ≫
        (barComplexDiagonal G k ▷ Rep.barComplex k G) ≫
        (α_ (Rep.barComplex k G)
          (Rep.barComplex k G) (Rep.barComplex k G)).hom :=
  ComonObj.comul_assoc (Rep.barComplex k G)

/-- The arbitrary-degree bar-cochain cup pairing is associative through the
coefficient associator and the canonical degree transport. -/
theorem barCochainCupPairing_assoc
    (A B D : Rep k G) (p q r : ℕ) :
    ((barCochainCupPairing G k A B).pair p q ⊗ₘ
        𝟙 (((Rep.barComplex k G).linearYonedaObj k D).X r)) ≫
      (barCochainCupPairing G k (A ⊗ B) D).pair (p + q) r ≫
      (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
        (𝟙 (Rep.barComplex k G)) (α_ A B D).hom).f ((p + q) + r) ≫
      (((Rep.barComplex k G).linearYonedaObj k (A ⊗ (B ⊗ D))).XIsoOfEq
        (Nat.add_assoc p q r)).hom =
    (α_ (((Rep.barComplex k G).linearYonedaObj k A).X p)
      (((Rep.barComplex k G).linearYonedaObj k B).X q)
      (((Rep.barComplex k G).linearYonedaObj k D).X r)).hom ≫
      (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).X p) ⊗ₘ
        (barCochainCupPairing G k B D).pair q r) ≫
      (barCochainCupPairing G k A (B ⊗ D)).pair p (q + r) := by
  apply HomologicalComplex.linearYonedaCochainPair_associativity_of_diagrams
  · rw [show HomologicalComplex.tensorHom (barComplexDiagonal G k)
        (𝟙 (Rep.barComplex k G)) =
          barComplexDiagonal G k ▷ Rep.barComplex k G by rfl]
    rw [show HomologicalComplex.tensorHom (𝟙 (Rep.barComplex k G))
        (barComplexDiagonal G k) =
          Rep.barComplex k G ◁ barComplexDiagonal G k by rfl]
    exact (barComplexDiagonal_assoc G k).symm
  · simp

/-- Associativity of the arbitrary-degree cup pairing on bar-cochain
homology. -/
theorem barCochainCupPairing_pairHomology_assoc
    (A B D : Rep k G) (p q r : ℕ) :
    ((barCochainCupPairing G k A B).pairHomology p q ⊗ₘ
        𝟙 (((Rep.barComplex k G).linearYonedaObj k D).homology r)) ≫
      (barCochainCupPairing G k (A ⊗ B) D).pairHomology (p + q) r ≫
      HomologicalComplex.cochainHomologyMapOfEq k
        (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
          (𝟙 (Rep.barComplex k G)) (α_ A B D).hom)
        (Nat.add_assoc p q r) =
    (α_ (((Rep.barComplex k G).linearYonedaObj k A).homology p)
      (((Rep.barComplex k G).linearYonedaObj k B).homology q)
      (((Rep.barComplex k G).linearYonedaObj k D).homology r)).hom ≫
      (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).homology p) ⊗ₘ
        (barCochainCupPairing G k B D).pairHomology q r) ≫
      (barCochainCupPairing G k A (B ⊗ D)).pairHomology p (q + r) := by
  let comparison :
      (Rep.barComplex k G).linearYonedaObj k ((A ⊗ B) ⊗ D) ⟶
        (Rep.barComplex k G).linearYonedaObj k (A ⊗ (B ⊗ D)) :=
    HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
      (𝟙 (Rep.barComplex k G)) (α_ A B D).hom
  apply HomologicalComplex.CochainGradedPairing.pairHomology_associativity_of_pair
    k (barCochainCupPairing G k A B)
    (barCochainCupPairing G k (A ⊗ B) D)
    (barCochainCupPairing G k B D)
    (barCochainCupPairing G k A (B ⊗ D))
    p q r
    (HomologicalComplex.cochainMapXOfEq k comparison (Nat.add_assoc p q r))
    (HomologicalComplex.cochainCyclesMapOfEq k comparison (Nat.add_assoc p q r))
    (HomologicalComplex.cochainHomologyMapOfEq k comparison (Nat.add_assoc p q r))
  · exact HomologicalComplex.cochainCyclesMapOfEq_i k comparison
      (Nat.add_assoc p q r)
  · exact HomologicalComplex.cochainHomologyπ_comp_cochainHomologyMapOfEq
      k comparison (Nat.add_assoc p q r)
  · dsimp [comparison, HomologicalComplex.cochainMapXOfEq]
    convert barCochainCupPairing_assoc G k A B D p q r using 1

section

set_option backward.isDefEq.respectTransparency false

/-- The comparison from inhomogeneous cohomology to bar-cochain homology. -/
noncomputable def inhomogeneousBarHomologyIso
    (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅
      ((Rep.barComplex k G).linearYonedaObj k A).homology n :=
  HomologicalComplex.homologyMapIso (inhomogeneousCochainsIso A) n

/-- The arbitrary-degree cup is the bar-cochain cup transported through the
inhomogeneous/bar comparison on homology. -/
theorem cup_eq_barCochainCupPairing_transport
    (A B : Rep k G) (p q : ℕ) :
    cup G k A B p q =
      ((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
        (inhomogeneousBarHomologyIso G k B q).hom) ≫
        (barCochainCupPairing G k A B).pairHomology p q ≫
        (inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).inv := by
  unfold cup inhomogeneousBarHomologyIso inhomogeneousCupPairing
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_whisker]
  rfl

/-- Naturality of the inverse inhomogeneous/bar comparison on homology,
including transport across an equality of cohomological degrees. -/
theorem inhomogeneousBarHomologyIso_inv_naturality
    {A B : Rep k G} (f : A ⟶ B) {n n' : ℕ} (h : n = n') :
    (inhomogeneousBarHomologyIso G k A n).inv ≫
        map (MonoidHom.id G) f n ≫
        (HomologicalComplex.cochainHomologyIsoOfEq k
          (inhomogeneousCochains B) h).hom =
      HomologicalComplex.cochainHomologyMapOfEq k
        (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
          (𝟙 (Rep.barComplex k G)) f) h ≫
        (inhomogeneousBarHomologyIso G k B n').inv := by
  subst n'
  dsimp only [HomologicalComplex.cochainHomologyIsoOfEq,
    HomologicalComplex.cochainHomologyMapOfEq]
  erw [Category.comp_id]
  have hh := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (inhomogeneousCochainsIso_inv_naturality f)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hh
  simpa [inhomogeneousBarHomologyIso, map,
    HomologicalComplex.linearYonedaCochainComparison] using hh

/-- Associativity of the arbitrary-degree cup on group cohomology, through
the coefficient associator and the canonical equality
`(p + q) + r = p + (q + r)` of output degrees. -/
theorem cup_assoc (A B D : Rep k G) (p q r : ℕ) :
    ((cup G k A B p q ⊗ₘ 𝟙 (groupCohomology D r)) ≫
        cup G k (A ⊗ B) D (p + q) r ≫
        map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r) ≫
        (HomologicalComplex.cochainHomologyIsoOfEq k
          (inhomogeneousCochains (A ⊗ (B ⊗ D)))
          (Nat.add_assoc p q r)).hom) =
      (α_ (groupCohomology A p) (groupCohomology B q)
        (groupCohomology D r)).hom ≫
        (𝟙 (groupCohomology A p) ⊗ₘ cup G k B D q r) ≫
        cup G k A (B ⊗ D) p (q + r) := by
  rw [cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport]
  have hOut := inhomogeneousBarHomologyIso_inv_naturality G k
    (α_ A B D).hom (Nat.add_assoc p q r)
  simp only [Category.assoc]
  rw [hOut]
  have hLeft :
      ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ≫
          (barCochainCupPairing G k A B).pairHomology p q ≫
          (inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).inv) ⊗ₘ
        𝟙 (groupCohomology D r)) ≫
        ((inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) =
      ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) ≫
        ((barCochainCupPairing G k A B).pairHomology p q ⊗ₘ
          𝟙 (((Rep.barComplex k G).linearYonedaObj k D).homology r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp [Category.assoc]
  rw [← Category.assoc, hLeft]
  have hRight :
      (α_ (groupCohomology A p) (groupCohomology B q)
          (groupCohomology D r)).hom ≫
        (𝟙 (groupCohomology A p) ⊗ₘ
          (((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
              (inhomogeneousBarHomologyIso G k D r).hom) ≫
            (barCochainCupPairing G k B D).pairHomology q r ≫
            (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).inv)) ≫
        ((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).hom) =
      (((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) ≫
        (α_ (((Rep.barComplex k G).linearYonedaObj k A).homology p)
          (((Rep.barComplex k G).linearYonedaObj k B).homology q)
          (((Rep.barComplex k G).linearYonedaObj k D).homology r)).hom ≫
        (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).homology p) ⊗ₘ
          (barCochainCupPairing G k B D).pairHomology q r) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.assoc]
    have hBD :
        ((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
            (inhomogeneousBarHomologyIso G k D r).hom) ≫
          (barCochainCupPairing G k B D).pairHomology q r ≫
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).inv ≫
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).hom =
        ((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
            (inhomogeneousBarHomologyIso G k D r).hom) ≫
          (barCochainCupPairing G k B D).pairHomology q r := by
      simp
    rw [hBD]
    rw [← MonoidalCategory.tensorHom_comp_whiskerLeft]
    rw [← MonoidalCategory.associator_naturality_assoc]
    rw [MonoidalCategory.id_tensorHom]
  have hRightFull := congrArg (fun f =>
    f ≫ (barCochainCupPairing G k A (B ⊗ D)).pairHomology p (q + r) ≫
      (inhomogeneousBarHomologyIso G k (A ⊗ (B ⊗ D))
        (p + (q + r))).inv) hRight
  simp only [Category.assoc] at hRightFull
  rw [hRightFull]
  have hBar := barCochainCupPairing_pairHomology_assoc G k A B D p q r
  have hBarTransported := congrArg (fun f =>
    ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
        (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
        (inhomogeneousBarHomologyIso G k D r).hom) ≫ f ≫
      (inhomogeneousBarHomologyIso G k (A ⊗ (B ⊗ D))
        (p + (q + r))).inv)) hBar
  simp only [Category.assoc] at hBarTransported
  convert hBarTransported using 1

/-- Elementwise associativity of arbitrary-degree cups on pure triple
tensors. -/
theorem cup_assoc_tmul
    (A B D : Rep k G) (p q r : ℕ)
    (x : groupCohomology A p) (y : groupCohomology B q)
    (z : groupCohomology D r) :
    (HomologicalComplex.cochainHomologyIsoOfEq k
        (inhomogeneousCochains (A ⊗ (B ⊗ D)))
        (Nat.add_assoc p q r)).hom.hom
      ((map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r)).hom
        ((cup G k (A ⊗ B) D (p + q) r).hom
          ((cup G k A B p q).hom (x ⊗ₜ[k] y) ⊗ₜ[k] z))) =
    (cup G k A (B ⊗ D) p (q + r)).hom
      (x ⊗ₜ[k] (cup G k B D q r).hom (y ⊗ₜ[k] z)) := by
  have h := congrArg (fun f => f.hom ((x ⊗ₜ[k] y) ⊗ₜ[k] z))
    (cup_assoc G k A B D p q r)
  change (HomologicalComplex.cochainHomologyIsoOfEq k
      (inhomogeneousCochains (A ⊗ (B ⊗ D)))
      (Nat.add_assoc p q r)).hom.hom
    ((map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r)).hom
      ((cup G k (A ⊗ B) D (p + q) r).hom
        ((cup G k A B p q).hom (x ⊗ₜ[k] y) ⊗ₜ[k] z))) =
      (cup G k A (B ⊗ D) p (q + r)).hom
        (x ⊗ₜ[k] (cup G k B D q r).hom (y ⊗ₜ[k] z)) at h
  exact h

end

end groupCohomology
