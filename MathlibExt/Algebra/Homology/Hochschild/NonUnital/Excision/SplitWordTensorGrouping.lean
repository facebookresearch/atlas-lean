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
# Ordered quotient and ideal tensor groups

For a Boolean word c, enumerate its true and false positions increasingly. The two
enumerations give a bijection from Fin(#true) ⊕ Fin(#false) to the word positions. At a true
position the entry module is A/I; at a false position it is I.

Reindexing the dependent tensor product and separating the two finite groups gives W_c ≃ₗ[k]
(A/I)^⊗#true ⊗[k] I^⊗#false. On a pure word this reads the quotient entries and ideal entries
in their respective increasing source orders. The grouping is ordinary tensor reindexing and
includes empty groups.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

namespace SplitWordTensorGrouping

variable {N : ℕ}

/-- For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true positions and I_c the set of
false positions, with the order inherited from Fin N. quotientPositions c is {i : Fin N | c i
= true}, as a finite subset with inherited order. -/
def quotientPositions (colour : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i => colour i = true)

/-- For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true positions and I_c the set of
false positions, with the order inherited from Fin N. idealPositions c is {i : Fin N | c i =
false}. It is the complement of the quotient-position set. -/
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

/-- For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true positions and I_c the set of
false positions, with the order inherited from Fin N. quotientPositionOrder c : Fin
(quotientEntryCount c) ≃o Q_c is the order isomorphism listing the true positions
increasingly. -/
def quotientPositionOrder (colour : Fin N → Bool) :
    Fin (quotientEntryCount colour) ≃o quotientPositions colour :=
  (quotientPositions colour).orderIsoOfFin (quotientPositions_card colour)

/-- For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true positions and I_c the set of
false positions, with the order inherited from Fin N. idealPositionOrder c : Fin
(splitWordIdealPositionCount c) ≃o I_c lists the false positions increasingly. -/
def idealPositionOrder (colour : Fin N → Bool) :
    Fin (splitWordIdealPositionCount colour) ≃o idealPositions colour :=
  (idealPositions colour).orderIsoOfFin (idealPositions_card colour)

private theorem quotientPositions_compl (colour : Fin N → Bool) :
    (quotientPositions colour)ᶜ = idealPositions colour := by
  ext i
  simp only [Finset.mem_compl, mem_quotientPositions, mem_idealPositions]
  cases colour i <;> decide

/-- For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true positions and I_c the set of
false positions, with the order inherited from Fin N. positionOrderEquiv c : Fin(#true) ⊕
Fin(#false) ≃ Fin N maps the left group to the true positions in increasing order and the
right group to the false positions in increasing order. -/
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

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). In the sum index Fin(#true) ⊕ Fin(#false), groupedEntry takes the
module A/I on the left group and I on the right group. -/
def groupedEntry (colour : Fin N → Bool)
    (i : Fin (quotientEntryCount colour) ⊕ Fin (splitWordIdealPositionCount colour)) :
    ModuleCat.{v} k :=
  splitWordEntry k A I (Sum.elim (fun _ => true) (fun _ => false) i)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true
positions and I_c the set of false positions, with the order inherited from Fin N. For a
grouped position i, entryOrderEquiv identifies the module E_(c(positionOrderEquiv i)) with
groupedEntry i. The true and false colour equations make this the identity linear equivalence
on the selected module. -/
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

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). wordEquiv c : W_c ≃ₗ[k] TensorPower k (#true) (A/I) ⊗[k]
TensorPower k (#false) I first reindexes by positionOrderEquiv, identifies the entry modules
and separates the two tensor groups. -/
def wordEquiv (colour : Fin N → Bool) :
    splitWordTensor k A I colour ≃ₗ[k]
      TensorPower k (quotientEntryCount colour) I.Quotient ⊗[k]
        TensorPower k (splitWordIdealPositionCount colour) I.Algebra :=
  (PiTensorProduct.reindex k (fun i : Fin N => splitWordPosition k A I colour i)
      (positionOrderEquiv colour).symm).trans
    ((PiTensorProduct.congr (entryOrderEquiv k A I colour)).trans
      (PiTensorProduct.tmulEquivDep k (fun i => groupedEntry k A I colour i)).symm)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true
positions and I_c the set of false positions, with the order inherited from Fin N. For typed
entries a_i : E_(c i), quotientEntries c a takes the entries at quotientPositionOrder c,
identified with A/I through entryOrderEquiv. -/
def quotientEntries (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i)
    (i : Fin (quotientEntryCount colour)) : I.Quotient :=
  entryOrderEquiv k A I colour (Sum.inl i)
    (a (positionOrderEquiv colour (Sum.inl i)))

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true
positions and I_c the set of false positions, with the order inherited from Fin N. For typed
entries a_i : E_(c i), idealEntries c a takes the entries at idealPositionOrder c, identified
with I through entryOrderEquiv. -/
def idealEntries (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i)
    (i : Fin (splitWordIdealPositionCount colour)) : I.Algebra :=
  entryOrderEquiv k A I colour (Sum.inr i)
    (a (positionOrderEquiv colour (Sum.inr i)))

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For a_i : E_(c i), wordEquiv c (tprod a) = tprod(quotientEntries c
a) ⊗ₜ[k] tprod(idealEntries c a). Each group retains the increasing order of its source
positions. -/
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
