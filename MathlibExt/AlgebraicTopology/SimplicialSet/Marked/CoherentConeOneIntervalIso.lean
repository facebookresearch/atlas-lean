/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOneEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso
import MathlibExt.CategoryTheory.NerveHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne

/-!
# Whole original one-simplex cone coefficient as the minimal interval

The cone subsets at original vertex zero are its singleton and full
two-vertex subset, with their original inclusion order. Their exact
maximum identifies this coefficient with the original interval. The
marking is precisely the original constant-maximum marking, hence the
minimal interval marking; the noninvertible cross edge stays unmarked.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original zero-cone inclusion order is its exact two-vertex interval, with singleton and full-subset
  endpoints retained. -/
def coneZeroOrderIso : ConeSubset (zeroOne.{u}) ≃o Vertex.{u} 1 := by
  refine Equiv.toOrderIso
    { toFun := ConeSubset.maximum
      invFun := fun i => if i.down = 0 then coefficientSource else coefficientTarget
      left_inv := ?_
      right_inv := ?_ } (fun _ _ h => ConeSubset.maximum_mono h) ?_
  · intro a
    rcases a.zero_cases with rfl | rfl <;> simp [ConeSubset.maximum, coefficientSource,
      coefficientTarget, zeroOne]
  · rintro ⟨i⟩
    fin_cases i <;> simp [ConeSubset.maximum, coefficientSource, coefficientTarget, zeroOne]
  · rintro ⟨i⟩ ⟨j⟩ hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · change coefficientSource ≤ coefficientTarget
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    · exact le_rfl

/-- The whole original cone-zero nerve has its actual interval simplicial carrier through the exact maximum functor. -/
def coneZeroNerveIso : nerve (ConeSubset (zeroOne.{u})) ≅ (Δ[1] : SSet.{u}) where
  hom := nerveMap (maximumFunctor zeroOne) ≫ (SSet.stdSimplex.isoNerve 1).inv
  inv := (SSet.stdSimplex.isoNerve 1).hom ≫ nerveMap coneZeroOrderIso.symm.monotone.functor
  hom_inv_id := by
    have hc : maximumFunctor zeroOne ⋙ coneZeroOrderIso.symm.monotone.functor =
        𝟭 (ConeSubset (zeroOne.{u})) := by
      apply CategoryTheory.Functor.ext (fun a => coneZeroOrderIso.left_inv a)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (nerveMap_comp (maximumFunctor zeroOne) coneZeroOrderIso.symm.monotone.functor).trans
      ((congrArg nerveMap hc).trans nerveMap_id)
  inv_hom_id := by
    have hc : coneZeroOrderIso.symm.monotone.functor ⋙ maximumFunctor zeroOne =
        𝟭 (Vertex.{u} 1) := by
      apply CategoryTheory.Functor.ext (fun a => coneZeroOrderIso.right_inv a)
    have hn : nerveMap coneZeroOrderIso.symm.monotone.functor ≫ nerveMap (maximumFunctor zeroOne) =
        𝟙 (nerve (Vertex.{u} 1)) :=
      (nerveMap_comp coneZeroOrderIso.symm.monotone.functor (maximumFunctor zeroOne)).trans
        ((congrArg nerveMap hc).trans nerveMap_id)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (SSet.stdSimplex.isoNerve 1).hom ≫ f)
        (Category.assoc _ _ _).symm).trans
          ((congrArg (fun f => (SSet.stdSimplex.isoNerve 1).hom ≫ (f ≫ (SSet.stdSimplex.isoNerve 1).inv)) hn).trans
            ((congrArg (fun f => (SSet.stdSimplex.isoNerve 1).hom ≫ f) (Category.id_comp _)).trans
              (SSet.stdSimplex.isoNerve 1).hom_inv_id)))

/-- The original one-simplex cone coefficient keeps precisely the unchanged minimal interval marking under
  its full maximum map. -/
def coneZeroIntervalIso : coneWeight (zeroOne.{u}) ≅ min (Δ[1] : SSet.{u}) :=
  isoMk coneZeroNerveIso (by
    intro e
    change (e.obj 0).maximum = (e.obj 1).maximum ↔ _
    constructor
    · intro he
      refine ⟨(Δ[1] : SSet.{u}).δ 0 (coneZeroNerveIso.hom.app (op ⦋1⦌) e), ?_⟩
      apply SSet.stdSimplex.ext
      intro j
      fin_cases j
      · exact congrArg ULift.down he.symm
      · rfl
    · rintro ⟨v, hv⟩
      apply ULift.ext
      have h0 := congrArg (fun e' : (Δ[1] : SSet.{u}) _⦋1⦌ => e' 0) hv
      have h1 := congrArg (fun e' : (Δ[1] : SSet.{u}) _⦋1⦌ => e' 1) hv
      exact h0.symm.trans h1)

end SSet.Marked.CoherentWeight
