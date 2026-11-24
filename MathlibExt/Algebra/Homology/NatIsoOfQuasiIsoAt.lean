/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u t

namespace HomologicalComplex

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
variable {ι : Type t} {c : ComplexShape ι}

/-- Degreewise homology natural isomorphism induced by a pointwise `QuasiIsoAt`.

For `K L : J ⥤ HomologicalComplex C c` and `f : K ⟶ L` such that each
`f.app j` is a `QuasiIsoAt` in degree `i`, postcomposition with
`homologyFunctor C c i` yields a natural isomorphism
`K ⋙ homologyFunctor C c i ≅ L ⋙ homologyFunctor C c i`.

The proof right-whiskers `f` with the homology functor, installs
`IsIso` at each object from `hf`, and promotes via `NatIso.isIso_of_isIso_app`. -/
noncomputable def homologyNatIsoOfQuasiIsoAt
    {K L : J ⥤ HomologicalComplex C c} (f : K ⟶ L) (i : ι)
    (hf : ∀ j, QuasiIsoAt (f.app j) i) :
    K ⋙ homologyFunctor C c i ≅ L ⋙ homologyFunctor C c i :=
  let β : K ⋙ homologyFunctor C c i ⟶ L ⋙ homologyFunctor C c i :=
    Functor.whiskerRight f (homologyFunctor C c i)
  letI : ∀ j, IsIso (β.app j) := fun j => by
    change IsIso (homologyMap (f.app j) i)
    have : QuasiIsoAt (f.app j) i := hf j
    infer_instance
  letI : IsIso β := NatIso.isIso_of_isIso_app β
  asIso β

@[simp]
theorem homologyNatIsoOfQuasiIsoAt_hom_app
    {K L : J ⥤ HomologicalComplex C c} (f : K ⟶ L) (i : ι)
    (hf : ∀ j, QuasiIsoAt (f.app j) i) (j : J) :
    (homologyNatIsoOfQuasiIsoAt f i hf).hom.app j =
      HomologicalComplex.homologyMap (f.app j) i :=
  rfl

end HomologicalComplex
