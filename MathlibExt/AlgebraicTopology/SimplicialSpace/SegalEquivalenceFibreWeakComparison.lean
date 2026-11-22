/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalCorePathObject
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionWeakRestriction
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Original equivalence-fibre weak comparison
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.SegalHomotopy

/-- Intrinsic full mapping-space weakness reflects the exact original equivalence selector. -/
theorem equivalenceFibreSelector_preimage_of_mappingFibreWeak
    {W V : SimplicialSpace.{u}} (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SSet.mapπ₀ (mappingFibre.map f (x := x) (y := y) rfl rfl)) ⁻¹'
        ((SSet.mapπ₀ (mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y))) ⁻¹'
          equivalenceComponents V hV) =
      (SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW := by
  let : (map f hW hV).Full := map_full_of_mappingFibreWeak f hW hV hm
  let : (map f hW hV).Faithful := map_faithful_of_mappingFibreWeak f hW hV hm
  let : (map f hW hV).ReflectsIsomorphisms :=
    (Functor.FullyFaithful.ofFullyFaithful (map f hW hV)).reflectsIsomorphisms
  let m := mappingFibre.map f (x := x) (y := y) rfl rfl
  apply Set.ext
  intro c
  induction c using SSet.π₀.rec with
  | mk a =>
    have hw := (equivalenceFibrePreimageIso_laws W hW x y).2.2.2.2 a
    have hv := (equivalenceFibrePreimageIso_laws V hV
      (mappingVertexMap f x) (mappingVertexMap f y)).2.2.2.2 (m.app (op ⦋0⦌) a)
    have hIso :
        IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) ↔
        IsIso (C := Object V hV) (X := ⟨mappingVertexMap f x⟩)
          (Y := ⟨mappingVertexMap f y⟩) (SSet.π₀.mk (m.app (op ⦋0⦌) a)) := by
      simpa only [map, SSet.mapπ₀_mk] using
        (isIso_iff_of_reflects_iso
          (show (⟨x⟩ : Object W hW) ⟶ ⟨y⟩ from SSet.π₀.mk a) (map f hW hV)).symm
    simp only [SSet.mem_componentUnion_zero] at hw hv
    simpa only [Set.mem_preimage, SSet.mapπ₀_mk] using (hv.trans hIso.symm).trans hw.symm

/-- The SAME core-fibre map is the actual component-preimage map under four original legs. -/
def equivalenceFibreMapPreimageArrowIso
    {W V : SimplicialSpace.{u}} (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    Arrow.mk (equivalenceFibreMap f hW hV (x := x) (y := y) rfl rfl) ≅
      Arrow.mk (SSet.componentUnionPreimageMap
        (mappingFibre.map f (x := x) (y := y) rfl rfl)
        ((SSet.mapπ₀ (mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y))) ⁻¹'
          equivalenceComponents V hV)) := by
  let m := mappingFibre.map f (x := x) (y := y) rfl rfl
  let cm := equivalenceFibreMap f hW hV (x := x) (y := y) rfl rfl
  let TW := (SSet.mapπ₀ (mappingFibre.fst W x y)) ⁻¹' equivalenceComponents W hW
  let TV := (SSet.mapπ₀ (mappingFibre.fst V (mappingVertexMap f x)
    (mappingVertexMap f y))) ⁻¹' equivalenceComponents V hV
  let UW := SSet.componentUnion (mappingFibre W x y) TW
  let UV := SSet.componentUnion
    (mappingFibre V (mappingVertexMap f x) (mappingVertexMap f y)) TV
  let U' := SSet.componentUnion (mappingFibre W x y) ((SSet.mapπ₀ m) ⁻¹' TV)
  let eW := equivalenceFibrePreimageIso W hW x y
  let eV := equivalenceFibrePreimageIso V hV (mappingVertexMap f x) (mappingVertexMap f y)
  let d : (UW : SSet.{u}) ≅ (U' : SSet.{u}) := SSet.Subcomplex.eqToIso
    (congrArg (SSet.componentUnion (mappingFibre W x y))
      (equivalenceFibreSelector_preimage_of_mappingFibreWeak f hW hV hm x y).symm)
  let s := eW ≪≫ d
  let r := SSet.componentUnionPreimageMap m TV
  have hOriginal := (equivalenceFibreMap_laws f hW hV
    (x := x) (y := y) rfl rfl).2.2.2.2.2.1
  change (eW.inv ≫ cm ≫ eV.hom) ≫ UV.ι = UW.ι ≫ m at hOriginal
  have hd : d.inv ≫ UW.ι = U'.ι := by
    simp only [d, SSet.Subcomplex.eqToIso, SSet.Subcomplex.homOfLE_ι]
  have hNormalize : s.inv ≫ cm ≫ eV.hom = r := by
    apply (cancel_mono UV.ι).mp
    calc
      (s.inv ≫ cm ≫ eV.hom) ≫ UV.ι = d.inv ≫ ((eW.inv ≫ cm ≫ eV.hom) ≫ UV.ι) := by
        simp only [s, Iso.trans_inv, Category.assoc]
      _ = d.inv ≫ (UW.ι ≫ m) := congrArg (fun q => d.inv ≫ q) hOriginal
      _ = (d.inv ≫ UW.ι) ≫ m := (Category.assoc _ _ _).symm
      _ = U'.ι ≫ m := congrArg (fun q => q ≫ m) hd
      _ = r ≫ UV.ι := (SSet.componentUnionPreimageMap_ι m TV).symm
  exact Arrow.isoMk s eV ((Iso.inv_comp_eq s).mp hNormalize).symm

/-- Forward and inverse Arrow source/target fields are the four original comparisons. -/
theorem equivalenceFibreMap_preimageArrowIso_laws
    {W V : SimplicialSpace.{u}} (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    let d := SSet.Subcomplex.eqToIso
      (congrArg (SSet.componentUnion (mappingFibre W x y))
        (equivalenceFibreSelector_preimage_of_mappingFibreWeak f hW hV hm x y).symm)
    let eW := equivalenceFibrePreimageIso W hW x y
    let eV := equivalenceFibrePreimageIso V hV (mappingVertexMap f x) (mappingVertexMap f y)
    let e := equivalenceFibreMapPreimageArrowIso f hW hV hm x y
    e.hom.left = eW.hom ≫ d.hom ∧ e.inv.left = d.inv ≫ eW.inv ∧
      e.hom.right = eV.hom ∧ e.inv.right = eV.inv := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Full original mapping-fibre weakness gives full weakness of the SAME equivalence-fibre map. -/
theorem equivalenceFibreMap_weak_of_mappingFibreWeak
    {W V : SimplicialSpace.{u}} (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (equivalenceFibreMap f hW hV (x := x) (y := y) rfl rfl) := by
  let e := equivalenceFibreMapPreimageArrowIso f hW hV hm x y
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).2
    (SSet.componentUnionPreimageMap_weak _ _ (hm x y))

end SimplicialSpace.SegalHomotopy
