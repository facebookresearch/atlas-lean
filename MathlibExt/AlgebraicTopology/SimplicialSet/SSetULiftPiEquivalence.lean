/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPointedRelation
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

/-!
# The same original Kan homotopy groups under coefficient universe lift

Both full original pointed-simplex directions preserve and reflect the
actual original relation simplex. The existing canonical quotient of
that genuine relation gives the full homotopy-group equivalence in
every degree and its exact original source-map naturality.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.KanComplex

variable (X : SSet.{u}) [KanComplex X]

/-- The same full original homotopy class equality is preserved and reflected
by the actual coefficient lift. -/
theorem ulift_mk_eq_mk_iff (n : ℕ) (x : X _⦋0⦌) (p q : X.PtSimplex n x) :
    π.mk (SSet.uliftPointedSimplexEquiv.{u,v} X n x p) =
      π.mk (SSet.uliftPointedSimplexEquiv.{u,v} X n x q) ↔ π.mk p = π.mk q := by
  let _ : KanComplex (SSet.uliftFunctor.{v,u}.obj X) := SSet.kanComplex_ulift.{u,v} X
  exact π.mk_eq_mk_iff.trans
    ((SSet.uliftPointedRelStruct_nonempty_iff p q 0).trans π.mk_eq_mk_iff.symm)

/-- Both full original quotient directions identify the same entire based Kan
homotopy groups across coefficient universes. -/
def uliftPiEquiv (n : ℕ) (x : X _⦋0⦌) :
    π n X x ≃ π n (SSet.uliftFunctor.{v,u}.obj X) (ULift.up x) := by
  let P := X.PtSimplex n x
  let Q := (SSet.uliftFunctor.{v,u}.obj X).PtSimplex n (ULift.up x)
  let e := SSet.uliftPointedSimplexEquiv.{u,v} X n x
  let f : π n X x → π n (SSet.uliftFunctor.{v,u}.obj X) (ULift.up x) :=
    Quot.lift (fun p : P => π.mk (e p)) (by
      intro p q hpq
      apply (ulift_mk_eq_mk_iff X n x p q).mpr
      exact Quot.sound hpq)
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      induction p using π.rec with
      | mk p =>
        induction q using π.rec with
        | mk q => exact (ulift_mk_eq_mk_iff X n x p q).mp hpq
    · intro q
      obtain ⟨p, rfl⟩ := π.mk_surjective q
      exact ⟨π.mk (e.symm p), congrArg π.mk (e.apply_symm_apply p)⟩
  exact Equiv.ofBijective f hf

end SSet.KanComplex
