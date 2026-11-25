/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWordFiltration
public import Mathlib.Data.Fintype.Sort
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Ordered quotient and ideal tensor coordinates

The true and false colour fibres are enumerated by native increasing
finite-order isomorphisms. Native tensor reindexing and dependent tensor
separation preserve each entry and the relative order in both fibres. All
modules are the canonical typed entry modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

namespace SplitWordTensorGrouping

variable {N : ℕ}

/-- Actual original quotient positions, with their inherited finite order. -/
def quotientPositions (colour : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i => colour i = true)

/-- Actual original ideal positions, with the same inherited finite order. -/
def idealPositions (colour : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i => colour i = false)

@[simp]
theorem mem_quotientPositions (colour : Fin N → Bool) (i : Fin N) :
    i ∈ quotientPositions colour ↔ colour i = true := by
  simp only [quotientPositions, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_idealPositions (colour : Fin N → Bool) (i : Fin N) :
    i ∈ idealPositions colour ↔ colour i = false := by
  simp only [idealPositions, Finset.mem_filter, Finset.mem_univ, true_and]

theorem quotientPositions_card (colour : Fin N → Bool) :
    (quotientPositions colour).card = quotientEntryCount colour := rfl

theorem idealPositions_card (colour : Fin N → Bool) :
    (idealPositions colour).card = splitWordIdealPositionCount colour := by
  unfold splitWordIdealPositionCount
  apply congrArg Finset.card
  apply Finset.ext
  intro i
  simp only [idealPositions, Finset.mem_filter]

/-- The native increasing enumeration of the original quotient positions. -/
def quotientPositionOrder (colour : Fin N → Bool) :
    Fin (quotientEntryCount colour) ≃o quotientPositions colour :=
  (quotientPositions colour).orderIsoOfFin (quotientPositions_card colour)

/-- The native increasing enumeration of the original ideal positions. -/
def idealPositionOrder (colour : Fin N → Bool) :
    Fin (splitWordIdealPositionCount colour) ≃o idealPositions colour :=
  (idealPositions colour).orderIsoOfFin (idealPositions_card colour)

private theorem quotientPositions_compl (colour : Fin N → Bool) :
    (quotientPositions colour)ᶜ = idealPositions colour := by
  ext i
  simp only [Finset.mem_compl, mem_quotientPositions, mem_idealPositions]
  cases colour i <;> decide

/-- Canonical ordered subset/complement coordinates for the original quotient and ideal fibres. -/
abbrev positionOrderEquiv (colour : Fin N → Bool) :
    Fin (quotientEntryCount colour) ⊕ Fin (splitWordIdealPositionCount colour) ≃ Fin N :=
  finSumEquivOfFinset (quotientPositions_card colour) (by
    have hcompl : (quotientPositions colour)ᶜ = idealPositions colour := by
      ext i
      simp only [Finset.mem_compl, mem_quotientPositions, mem_idealPositions]
      cases colour i <;> decide
    exact (congrArg Finset.card hcompl).trans (idealPositions_card colour))

theorem positionOrderEquiv_inl (colour : Fin N → Bool)
    (i : Fin (quotientEntryCount colour)) :
    positionOrderEquiv colour (Sum.inl i) = (quotientPositionOrder colour i).val :=
  finSumEquivOfFinset_inl _ _ i

theorem positionOrderEquiv_inr (colour : Fin N → Bool)
    (i : Fin (splitWordIdealPositionCount colour)) :
    positionOrderEquiv colour (Sum.inr i) = (idealPositionOrder colour i).val := by
  let hcomp : (quotientPositions colour)ᶜ.card = splitWordIdealPositionCount colour :=
    (congrArg Finset.card (quotientPositions_compl colour)).trans (idealPositions_card colour)
  have horder : (fun j => (idealPositionOrder colour j).val) =
      (quotientPositions colour)ᶜ.orderEmbOfFin hcomp := by
    apply Finset.orderEmbOfFin_unique hcomp
    · intro j
      rw [quotientPositions_compl]
      exact (idealPositionOrder colour j).property
    · exact (idealPositionOrder colour).strictMono
  exact (finSumEquivOfFinset_inr (quotientPositions_card colour) hcomp i).trans
    (congrFun horder i).symm

theorem positionOrderEquiv_true (colour : Fin N → Bool)
    (i : Fin (quotientEntryCount colour)) :
    colour (positionOrderEquiv colour (Sum.inl i)) = true := by
  rw [positionOrderEquiv_inl]
  exact (mem_quotientPositions colour _).mp (quotientPositionOrder colour i).property

theorem positionOrderEquiv_false (colour : Fin N → Bool)
    (i : Fin (splitWordIdealPositionCount colour)) :
    colour (positionOrderEquiv colour (Sum.inr i)) = false := by
  rw [positionOrderEquiv_inr]
  exact (mem_idealPositions colour _).mp (idealPositionOrder colour i).property

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The grouped fibre retains the original canonical quotient or ideal entry module. -/
def groupedEntry (colour : Fin N → Bool)
    (i : Fin (quotientEntryCount colour) ⊕ Fin (splitWordIdealPositionCount colour)) :
    ModuleCat.{v} k :=
  splitWordEntry k A I (Sum.elim (fun _ => true) (fun _ => false) i)

/-- Actual colour equations identify each original entry with the same grouped entry. -/
def entryOrderEquiv (colour : Fin N → Bool)
    (i : Fin (quotientEntryCount colour) ⊕ Fin (splitWordIdealPositionCount colour)) :
    splitWordPosition k A I colour (positionOrderEquiv colour i) ≃ₗ[k]
      groupedEntry k A I colour i := by
  cases i with
  | inl i =>
      change splitWordEntry k A I (colour (positionOrderEquiv colour (Sum.inl i))) ≃ₗ[k]
        splitWordEntry k A I true
      rw [positionOrderEquiv_true colour i]
  | inr i =>
      change splitWordEntry k A I (colour (positionOrderEquiv colour (Sum.inr i))) ≃ₗ[k]
        splitWordEntry k A I false
      rw [positionOrderEquiv_false colour i]

/-- Native reindexing and dependent tensor separation group the original entries. -/
def wordEquiv (colour : Fin N → Bool) :
    splitWordTensor k A I colour ≃ₗ[k]
      TensorPower k (quotientEntryCount colour) I.Quotient ⊗[k]
        TensorPower k (splitWordIdealPositionCount colour) I.Algebra :=
  (PiTensorProduct.reindex k (fun i : Fin N => splitWordPosition k A I colour i)
      (positionOrderEquiv colour).symm).trans
    ((PiTensorProduct.congr (entryOrderEquiv k A I colour)).trans
      (PiTensorProduct.tmulEquivDep k (fun i => groupedEntry k A I colour i)).symm)

/-- The original quotient entries read in the native increasing source order. -/
def quotientEntries (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i)
    (i : Fin (quotientEntryCount colour)) : I.Quotient :=
  entryOrderEquiv k A I colour (Sum.inl i)
    (a (positionOrderEquiv colour (Sum.inl i)))

/-- The original ideal entries read in the native increasing source order. -/
def idealEntries (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i)
    (i : Fin (splitWordIdealPositionCount colour)) : I.Algebra :=
  entryOrderEquiv k A I colour (Sum.inr i)
    (a (positionOrderEquiv colour (Sum.inr i)))

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every original typed entry survives the native grouping equivalence. -/
theorem wordEquiv_tprod (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i) :
    wordEquiv k A I colour (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (quotientEntries k A I colour a) ⊗ₜ[k]
        PiTensorProduct.tprod k (idealEntries k A I colour a) := by
  change (PiTensorProduct.tmulEquivDep k (fun i => groupedEntry k A I colour i)).symm
      (PiTensorProduct.congr (entryOrderEquiv k A I colour)
        (PiTensorProduct.reindex k (fun i : Fin N => splitWordPosition k A I colour i)
          (positionOrderEquiv colour).symm (PiTensorProduct.tprod k a))) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply]
  rfl

end SplitWordTensorGrouping

end ModuleCat.Algebra.Hochschild.NonUnital
