/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Realization weakness on internal-Hom components

Full native component equality of the original classified maps preserves
realization weakness. EqvGen paths use actual inverse internal-Hom edges;
reverse and transitive steps use logical equivalences. Arbitrary endpoints
and every value universe remain, with no Kan, QC or nonempty hypothesis.

This scalar project bridge supports Rezk Proposition 9.1(4); it uses the
native component quotient and the existing all-endpoint homotopy invariance.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
open scoped Simplicial
namespace SSet

/-- Full internal-Hom component equality preserves the original weak predicate. -/
theorem realizationWeakEquivalences_iff_of_ihom_component_eq
    {A B : SSet.{u}} {a b : A ⟶ B}
    (h : π₀.mk (ihomVertexEquiv A B a) =
      π₀.mk (ihomVertexEquiv A B b)) :
    realizationWeakEquivalences a ↔ realizationWeakEquivalences b := by
  let V := ihomVertexEquiv A B
  have hInvariant (x y : ((ihom A).obj B) _⦋0⦌)
      (hxy : Relation.EqvGen (π₀Rel (X := (ihom A).obj B)) x y) :
      realizationWeakEquivalences (V.symm x) ↔
        realizationWeakEquivalences (V.symm y) := by
    induction hxy with
    | rel x y hxy =>
      obtain ⟨e⟩ := hxy
      have e' : ((ihom A).obj B).Edge (V (V.symm x)) (V (V.symm y)) := by
        simpa only [Equiv.apply_symm_apply] using e
      exact realizationWeakEquivalences_iff_of_homotopy (Homotopy.ofIhomEdge e')
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  have hChain : Relation.EqvGen (π₀Rel (X := (ihom A).obj B)) (V a) (V b) :=
    (π₀.mk_eq_mk_iff (V a) (V b)).1 h
  simpa only [Equiv.symm_apply_apply] using hInvariant (V a) (V b) hChain

end SSet
