/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamGraphAdapter

open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

def grahamLooplessEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter (fun e => ¬ e.IsDiag)

def grahamDiagonalEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter Sym2.IsDiag

theorem grahamLooplessEdges_noDiag (E : Finset (Sym2 V)) :
    ∀ e ∈ grahamLooplessEdges E, ¬ e.IsDiag := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem bond_eq_one_of_isDiag (s : ConfigSpace V) (e : Sym2 V)
    (he : e.IsDiag) : bond s e = 1 := by
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : x = y := Sym2.mk_isDiag_iff.mp he
      subst y
      rw [bond_mk, spin_sq]



theorem wJ_eq_diagFactor_mul_loopless
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (s : ConfigSpace V) :
    wJ E J (fun _ => 0) s =
      Real.exp (∑ e ∈ grahamDiagonalEdges E, J e) *
        wJ (grahamLooplessEdges E) J (fun _ => 0) s := by
  have hpart : E = grahamLooplessEdges E ∪ grahamDiagonalEdges E := by
    ext e
    simp only [grahamLooplessEdges, grahamDiagonalEdges,
      Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (grahamLooplessEdges E) (grahamDiagonalEdges E) := by
    rw [Finset.disjoint_left]
    intro e he0 hed
    exact (Finset.mem_filter.mp he0).2 (Finset.mem_filter.mp hed).2
  have hdiagSum :
      (∑ e ∈ grahamDiagonalEdges E, J e * bond s e) =
        ∑ e ∈ grahamDiagonalEdges E, J e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [bond_eq_one_of_isDiag s e (Finset.mem_filter.mp he).2, mul_one]
  have hsum : (∑ e ∈ E, J e * bond s e) =
      (∑ e ∈ grahamLooplessEdges E, J e * bond s e) +
        ∑ e ∈ grahamDiagonalEdges E, J e * bond s e := by
    conv_lhs => rw [hpart]
    exact Finset.sum_union hdisj
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [hsum, hdiagSum, Real.exp_add, mul_comm]


theorem expJ_eq_looplessEdges
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (f : ConfigSpace V -> Real) :
    expJ E J (fun _ => 0) f =
      expJ (grahamLooplessEdges E) J (fun _ => 0) f := by
  unfold expJ ZJ
  simp_rw [wJ_eq_diagFactor_mul_loopless E J]
  rw [show (∑ s : ConfigSpace V,
      f s * (Real.exp (∑ e ∈ grahamDiagonalEdges E, J e) *
        wJ (grahamLooplessEdges E) J (fun _ => 0) s)) =
      Real.exp (∑ e ∈ grahamDiagonalEdges E, J e) *
        ∑ s : ConfigSpace V,
          f s * wJ (grahamLooplessEdges E) J (fun _ => 0) s by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos _))



theorem grahamLooplessGraph_expectationJ_eq_expJ
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (A : Finset V) :
    expectationJ (grahamGraph (grahamLooplessEdges E)) 1 J A =
      expJ E J (fun _ => 0) (spinProd A) := by
  rw [grahamGraph_expectationJ_eq_expJ
    (grahamLooplessEdges E) J (grahamLooplessEdges_noDiag E)]
  exact (expJ_eq_looplessEdges E J (spinProd A)).symm

end StatMech.FrontierA
