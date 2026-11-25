/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

@[expose] public section

/-!
# The same original standard simplices under universe lift

Both full inverse maps retain every original ordinal operator inside
its literal ULift wrapper. The full natural comparison uses the same
standard-simplex functor at the enlarged coefficient universe.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Both whole original scalar inverse maps identify the lifted original standard simplex and
the same simplex in the enlarged universe. -/
def uliftStandardSimplexIso (n : SimplexCategory) :
    uliftFunctor.{v,u}.obj (stdSimplex.{u}.obj n) ≅ stdSimplex.{max u v}.obj n :=
  NatIso.ofComponents (fun q =>
    ({ toFun := fun x => ULift.up x.down.down
       invFun := fun x => ULift.up (ULift.up x.down)
       left_inv := fun x => by cases x; rfl
       right_inv := fun x => by cases x; rfl } :
      ULift.{v} (ULift.{u} (q.unop ⟶ n)) ≃ ULift.{max u v} (q.unop ⟶ n)).toIso)
    (by intro q r θ; apply ConcreteCategory.hom_ext; intro x; rfl)

/-- The full original standard-simplex universe comparison retains every original operator as a
natural isomorphism. -/
def uliftStandardSimplexNatIso : stdSimplex.{u} ⋙ uliftFunctor.{v,u} ≅ stdSimplex.{max u v} :=
  NatIso.ofComponents uliftStandardSimplexIso (by
    intro n m θ
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

end SSet
