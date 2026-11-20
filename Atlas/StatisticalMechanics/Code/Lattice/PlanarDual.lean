/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice

open SimpleGraph

namespace StatMech

namespace Lattice







def dualLattice : SimpleGraph (Site 2) := hypercubicLattice 2

@[simp]
theorem dualLattice_adj (x y : Site 2) :
    dualLattice.Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl




def rot90Fun (x : Site 2) : Site 2 := ![- x 1, x 0]


def rot90Inv (x : Site 2) : Site 2 := ![x 1, - x 0]

@[simp] theorem rot90Fun_apply (a b : ℤ) : rot90Fun ![a, b] = ![-b, a] := by
  funext i; fin_cases i <;> simp [rot90Fun]

@[simp] theorem rot90Inv_apply (a b : ℤ) : rot90Inv ![a, b] = ![b, -a] := by
  funext i; fin_cases i <;> simp [rot90Inv]


def rot90Equiv : Site 2 ≃ Site 2 where
  toFun := rot90Fun
  invFun := rot90Inv
  left_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]
  right_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]

@[simp] theorem rot90Equiv_apply (x : Site 2) : rot90Equiv x = rot90Fun x := rfl
@[simp] theorem rot90Equiv_symm_apply (x : Site 2) : rot90Equiv.symm x = rot90Inv x := rfl




theorem rot90_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (rot90Fun x) (rot90Fun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rot90Fun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg, Nat.add_comm]



def rot90Iso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨rot90Equiv, fun {x y} => rot90_adj x y⟩

@[simp] theorem rot90Iso_apply (x : Site 2) : rot90Iso x = rot90Fun x := rfl






def selfDual : hypercubicLattice 2 ≃g dualLattice := SimpleGraph.Iso.refl

@[simp] theorem selfDual_apply (x : Site 2) : selfDual x = x := rfl




def selfDualCross : hypercubicLattice 2 ≃g dualLattice := rot90Iso

@[simp] theorem selfDualCross_apply (x : Site 2) : selfDualCross x = rot90Fun x := rfl









def crossingEdgeEquiv : (hypercubicLattice 2).edgeSet ≃ dualLattice.edgeSet :=
  rot90Iso.mapEdgeSet



theorem crossingEdgeEquiv_coe (e : (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv e : Sym2 (Site 2)) = Sym2.map (⇑rot90Iso) e := by
  rw [crossingEdgeEquiv, SimpleGraph.Iso.mapEdgeSet]
  exact Hom.mapEdgeSet_coe rot90Iso.toHom e



theorem crossingEdgeEquiv_horizontal (a b : ℤ)
    (he : s(![a, b], ![a + 1, b]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-b, a + 1]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]



theorem crossingEdgeEquiv_vertical (a b : ℤ)
    (he : s(![a, b], ![a, b + 1]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-(b + 1), a]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]









def sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by intro x; rw [Sym2.map_map]; simp
  right_inv := by intro x; rw [Sym2.map_map]; simp

@[simp] theorem sym2Congr_mk {α β : Type*} (e : α ≃ β) (a b : α) :
    sym2Congr e s(a, b) = s(e a, e b) := by simp [sym2Congr, Sym2.map_mk]



def crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr rot90Equiv

@[simp] theorem crossEdge_mk (x y : Site 2) :
    crossEdge s(x, y) = s(rot90Fun x, rot90Fun y) := by simp [crossEdge]



def dualConfig (ω : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => !(ω (crossEdge.symm e))



theorem isOpen_iff_dual_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    ω e = true ↔ dualConfig ω (crossEdge e) = false := by
  unfold dualConfig
  rw [Equiv.symm_apply_apply]
  cases ω e <;> simp



theorem dual_isOpen_iff_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig ω e = true ↔ ω (crossEdge.symm e) = false := by
  unfold dualConfig
  cases ω (crossEdge.symm e) <;> simp




theorem dualConfig_dualConfig (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) := by
  unfold dualConfig
  rw [Bool.not_not]

end Lattice

end StatMech
