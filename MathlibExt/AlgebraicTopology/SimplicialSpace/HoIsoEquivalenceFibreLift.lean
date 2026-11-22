/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original intrinsic Ho isomorphisms admit actual equivalence-fibre representatives,
-- the same-Iso roundtrip, and full weak mapping-fibre transport.
import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceFibreHomTransport

/-!
# Equivalence-fibre representatives of homotopy-category isomorphisms

Every homotopy-category isomorphism in a Reedy-fibrant Segal space has a chosen vertex in its
ordered equivalence fibre with the prescribed Hom class, and reconstructing the isomorphism
returns the original one. These representatives produce a weak span of actual mapping-fibre maps
realizing two-sided Hom transport, with exact forward, inverse and component equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SimplicialSpace.HoIsoEquivalenceFibreLift
open SegalHomotopy

/-- Choose a genuine original MF vertex representing the given original intrinsic Iso Hom. -/
def mappingPointOfIso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    (mappingFibre W x y) _⦋0⦌ :=
  Classical.choose (SSet.π₀.mk_surjective (X := mappingFibre W x y) e.hom)

/-- The chosen vertex retains the SAME original Hom class. -/
theorem mappingPointOfIso_class (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    SSet.π₀.mk (mappingPointOfIso W hW x y e) = e.hom :=
  Classical.choose_spec (SSet.π₀.mk_surjective (X := mappingFibre W x y) e.hom)

/-- Intrinsic invertibility places that SAME MF point in the actual selected EF preimage. -/
def equivalencePointOfIso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    (equivalenceFibre W hW x y) _⦋0⦌ := by
  let a := mappingPointOfIso W hW x y e
  let U := SSet.componentUnion (mappingFibre W x y)
    ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
  have hi : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) := by
    dsimp only [a]
    rw [mappingPointOfIso_class]
    infer_instance
  have ha : a ∈ U.obj (op ⦋0⦌) :=
    ((equivalenceFibrePreimageIso_laws W hW x y).2.2.2.2 a).mpr hi
  let b : (U : SSet.{u}) _⦋0⦌ := ⟨a, ha⟩
  exact (equivalenceFibrePreimageIso W hW x y).inv.app (op ⦋0⦌) b

/-- The actual EF-to-MF projection retains the original prescribed pair and exact Iso Hom. -/
theorem equivalencePointOfIso_class (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    SegalEquivalenceHomTransport.pointHom W hW x y (equivalencePointOfIso W hW x y e) = e.hom := by
  let a := mappingPointOfIso W hW x y e
  let U := SSet.componentUnion (mappingFibre W x y)
    ((SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW)
  have hi : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) := by
    dsimp only [a]
    rw [mappingPointOfIso_class]
    infer_instance
  have ha : a ∈ U.obj (op ⦋0⦌) :=
    ((equivalenceFibrePreimageIso_laws W hW x y).2.2.2.2 a).mpr hi
  let b : (U : SSet.{u}) _⦋0⦌ := ⟨a, ha⟩
  let s := equivalenceFibrePreimageIso W hW x y
  have h : s.inv ≫ equivalenceFibreToMappingFibre W hW x y = U.ι := by
    calc
      s.inv ≫ equivalenceFibreToMappingFibre W hW x y = s.inv ≫ (s.hom ≫ U.ι) :=
        congrArg (fun k => s.inv ≫ k) (equivalenceFibrePreimageIso_laws W hW x y).1.symm
      _ = U.ι := by rw [← Category.assoc, s.inv_hom_id, Category.id_comp]
  have he := congrArg (fun k => k.app (op ⦋0⦌) b) h
  change (equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌)
    (s.inv.app (op ⦋0⦌) b) = a at he
  change SSet.π₀.mk ((equivalenceFibreToMappingFibre W hW x y).app (op ⦋0⦌)
    (s.inv.app (op ⦋0⦌) b)) = e.hom
  rw [he]
  exact mappingPointOfIso_class W hW x y e


/-- Reconstructing the intrinsic Iso from its actual EF representative returns the SAME original
Iso. -/
theorem pointIso_roundtrip (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    SegalEquivalenceHomTransport.pointIso W hW x y
      (equivalencePointOfIso W hW x y e) = e := by
  apply Iso.ext
  change SegalEquivalenceHomTransport.pointHom W hW x y
    (equivalencePointOfIso W hW x y e) = e.hom
  exact equivalencePointOfIso_class W hW x y e

/-- Both literal moving-endpoint MF transport arrows are FULL weak for original Ho Isos. -/
theorem originalIsoMappingTransport_weakSpan (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (⟨x⟩ : Object W hW) ≅ (⟨x'⟩ : Object W hW))
    (b : (⟨y⟩ : Object W hW) ≅ (⟨y'⟩ : Object W hW)) :
    SSet.realizationWeakEquivalences
      (SegalEquivalenceHomTransport.postcomposePoint W hW y y'
        (equivalencePointOfIso W hW y y' b) x) ∧
    SSet.realizationWeakEquivalences
      (SegalEquivalenceHomTransport.precomposePoint W hW x x'
        (equivalencePointOfIso W hW x x' a) y') :=
  SegalEquivalenceHomTransport.originalMappingTransport_weakSpan W hW x x' y y'
    (equivalencePointOfIso W hW x x' a) (equivalencePointOfIso W hW y y' b)

/-- The SAME full MF span induces the original two-sided Ho Hom transport, in its exact order. -/
theorem originalIsoHomTransport_characteristics (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (⟨x⟩ : Object W hW) ≅ (⟨x'⟩ : Object W hW))
    (b : (⟨y⟩ : Object W hW) ≅ (⟨y'⟩ : Object W hW))
    (f : SSet.π₀ (mappingFibre W x y)) (g : SSet.π₀ (mappingFibre W x' y')) :
    SegalEquivalenceHomTransport.originalHomTransport W hW x x' y y'
      (equivalencePointOfIso W hW x x' a) (equivalencePointOfIso W hW y y' b) f =
        a.inv ≫ f ≫ b.hom ∧
    (SegalEquivalenceHomTransport.originalHomTransport W hW x x' y y'
      (equivalencePointOfIso W hW x x' a) (equivalencePointOfIso W hW y y' b)).symm g =
        a.hom ≫ g ≫ b.inv := by
  have h := SegalEquivalenceHomTransport.originalHomTransport_characteristics W hW x x' y y'
    (equivalencePointOfIso W hW x x' a) (equivalencePointOfIso W hW y y' b) f g
  simpa only [pointIso_roundtrip] using h

/-- Every original MF component retains the exact full weak-span comparison equation. -/
theorem originalIsoHomTransport_spanEquation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x x' y y' : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (⟨x⟩ : Object W hW) ≅ (⟨x'⟩ : Object W hW))
    (b : (⟨y⟩ : Object W hW) ≅ (⟨y'⟩ : Object W hW))
    (f : SSet.π₀ (mappingFibre W x y)) :
    SSet.mapπ₀ (SegalEquivalenceHomTransport.precomposePoint W hW x x'
      (equivalencePointOfIso W hW x x' a) y') (a.inv ≫ f ≫ b.hom) =
    SSet.mapπ₀ (SegalEquivalenceHomTransport.postcomposePoint W hW y y'
      (equivalencePointOfIso W hW y y' b) x) f := by
  rw [SegalEquivalenceHomTransport.precomposePoint_component,
    SegalEquivalenceHomTransport.postcomposePoint_component,
    equivalencePointOfIso_class, equivalencePointOfIso_class]
  simp only [Iso.hom_inv_id_assoc]

end SimplicialSpace.HoIsoEquivalenceFibreLift
