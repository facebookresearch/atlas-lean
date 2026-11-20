/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamCorrections
import Code.Sharpness.CurrentRep

open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamGraph (E : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := s(x, y) ∈ E ∧ x ≠ y
  symm := by
    intro x y h
    exact ⟨by simpa [Sym2.eq_swap] using h.1, h.2.symm⟩
  loopless := ⟨by
    intro x h
    exact h.2 rfl⟩

instance grahamGraph_decidableAdj (E : Finset (Sym2 V)) :
    DecidableRel (grahamGraph E).Adj := by
  intro x y
  unfold grahamGraph
  infer_instance



theorem grahamGraph_edgeFinset
    (E : Finset (Sym2 V)) (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
    (grahamGraph E).edgeFinset = E := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset]
      constructor
      · intro h
        exact h.1
      · intro hE
        exact ⟨hE, by
          intro hxy
          have hEq : x = y := Sym2.mk_isDiag_iff.mp hxy
          subst y
          exact hdiag s(x, x) hE (Sym2.mk_isDiag_iff.mpr rfl)⟩



theorem grahamGraph_boltzmannJ_eq_wJ
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (s : ConfigSpace V) :
    boltzmannJ (grahamGraph E) 1 J s = wJ E J (fun _ => 0) s := by
  unfold boltzmannJ wJ
  rw [grahamGraph_edgeFinset E hdiag]
  simp



theorem grahamGraph_expectationJ_eq_expJ
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (A : Finset V) :
    expectationJ (grahamGraph E) 1 J A =
      expJ E J (fun _ => 0) (spinProd A) := by
  unfold expectationJ expJ partitionJ ZJ
  simp_rw [grahamGraph_boltzmannJ_eq_wJ E J hdiag]


theorem grahamGraph_expectationJ_pair
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (x y : V) :
    expectationJ (grahamGraph E) 1 J (grahamPairSupport x y) =
      grahamTwoPoint E J x y := by
  rw [grahamGraph_expectationJ_eq_expJ E J hdiag]
  rfl

end StatMech.FrontierA
