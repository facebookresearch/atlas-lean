/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.QuasiIsoNaturality

/-!
# Tests for `isoOfQuasiIsoAt` naturality

Generic compile-time checks that the naturality square and its inverse form
apply to an arbitrary commuting square of homological complexes with
quasi-isomorphic horizontal arrows, plus identity-square special cases.
No concrete complex is constructed and no production argument is re-proved.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MathlibExtTest.Algebra.Homology.QuasiIsoNaturalityTests

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type*} {c : ComplexShape ι}
variable {K L K' L' : HomologicalComplex C c}

/-- The naturality square applies to a generic commuting square. -/
example (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    [QuasiIsoAt f i] [QuasiIsoAt f' i]
    (h : u ≫ f' = f ≫ v) :
    HomologicalComplex.homologyMap u i ≫
        (isoOfQuasiIsoAt f' i).hom =
      (isoOfQuasiIsoAt f i).hom ≫
        HomologicalComplex.homologyMap v i :=
  HomologicalComplex.isoOfQuasiIsoAt_naturality f f' u v i h

/-- The inverse naturality square applies to a generic commuting square. -/
example (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    [QuasiIsoAt f i] [QuasiIsoAt f' i]
    (h : u ≫ f' = f ≫ v) :
    (isoOfQuasiIsoAt f i).inv ≫
        HomologicalComplex.homologyMap u i =
      HomologicalComplex.homologyMap v i ≫
        (isoOfQuasiIsoAt f' i).inv :=
  HomologicalComplex.isoOfQuasiIsoAt_inv_naturality f f' u v i h

/-- Identity square: vertical identities commute with any quasi-isomorphism. -/
example (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    HomologicalComplex.homologyMap (𝟙 K) i ≫
        (isoOfQuasiIsoAt f i).hom =
      (isoOfQuasiIsoAt f i).hom ≫
        HomologicalComplex.homologyMap (𝟙 L) i := by
  have h : (𝟙 K) ≫ f = f ≫ (𝟙 L) := by simp
  exact HomologicalComplex.isoOfQuasiIsoAt_naturality f f (𝟙 K) (𝟙 L) i h

/-- The naturality square has a fixed orientation: the forward proof does not
inhabit the transposed equality type. -/
example (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    [QuasiIsoAt f i] [QuasiIsoAt f' i]
    (h : u ≫ f' = f ≫ v) : True := by
  have hforward := HomologicalComplex.isoOfQuasiIsoAt_naturality f f' u v i h
  fail_if_success
    let _reversed : (isoOfQuasiIsoAt f i).hom ≫
          HomologicalComplex.homologyMap u i =
        HomologicalComplex.homologyMap v i ≫
          (isoOfQuasiIsoAt f' i).hom :=
      hforward
  trivial

end MathlibExtTest.Algebra.Homology.QuasiIsoNaturalityTests

end
