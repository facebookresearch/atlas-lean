/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.NativeProduct

/-!
# Canonical native products with independently chosen factors

The clients consume the actual two-factor tensor maps and original
subgroups, and retain the established self-product interface.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped TopCat.modelCategory

universe u

example (A B : CGWH.{u, u}) (a : A) (b : B) :
    CGWH.prodComparisonToTop A B (CGWH.tensorMk a b) = (a, b) :=
  CGWH.NativeProduct.comparison_point_eq A B a b

example {A B M N : CGWH.{u, u}} (f : A ⟶ M) (g : B ⟶ N)
    (a : A) (b : B) (m : M) (n : N) (hfa : f a = m) (hgb : g b = n) :
    CGWH.cgwhToTop.map (f ⊗ₘ g) (CGWH.tensorMk a b) = CGWH.tensorMk m n :=
  CGWH.NativeProduct.map_point_eq f g a b m n hfa hgb

example {A B M N : CGWH.{u, u}} (f : A ⟶ M) (g : B ⟶ N) :
    CGWH.cgwhToTop.map (f ⊗ₘ g) ≫ CGWH.prodComparisonToTop M N =
      CGWH.prodComparisonToTop A B ≫
        TopCat.ofHom ((CGWH.cgwhToTop.map f).hom.prodMap (CGWH.cgwhToTop.map g).hom) :=
  CGWH.NativeProduct.map_comparison f g

example (A B M N : CGWH.{u, u})
    [PathConnectedSpace B] [PathConnectedSpace M] [PathConnectedSpace N]
    (f : A ⟶ M) (g : B ⟶ N) (a : A) (b : B) (m : M) (n : N)
    (hfa : f a = m) (hgb : g b = n)
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop)]
    [Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B.toTop)]
    [Cofibration (TopCat.const m : TopCat.of PUnit.{u + 1} ⟶ M.toTop)]
    [Cofibration (TopCat.const n : TopCat.of PUnit.{u + 1} ⟶ N.toTop)]
    (P : Subgroup (FundamentalGroup A a)) (Q : Subgroup (FundamentalGroup B b))
    [P.Normal] [Q.Normal] [Group.IsPerfect P] [Group.IsPerfect Q]
    (hf : @TopCat.IsPlusConstructionAt A.toTop M.toTop
      (CGWH.cgwhToTop.map f) a m hfa P ‹P.Normal› ‹Group.IsPerfect P›)
    (hg : @TopCat.IsPlusConstructionAt B.toTop N.toTop
      (CGWH.cgwhToTop.map g) b n hgb Q ‹Q.Normal› ‹Group.IsPerfect Q›) :
    let PQ := CGWH.NativeProduct.plusSubgroup A B a b P Q
    ∃ hN : PQ.Normal, ∃ hP : Group.IsPerfect PQ,
      letI := hN
      letI := hP
      @TopCat.IsPlusConstructionAt (A ⊗ B : CGWH.{u, u}).toTop
        (M ⊗ N : CGWH.{u, u}).toTop (CGWH.cgwhToTop.map (f ⊗ₘ g))
        (CGWH.tensorMk a b) (CGWH.tensorMk m n)
        (CGWH.NativeProduct.map_point_eq f g a b m n hfa hgb) PQ hN hP :=
  CGWH.NativeProduct.isPlus A B M N f g a b m n hfa hgb P Q hf hg

example (A : CGWH.{u, u}) (a : A) :
    CGWH.prodComparisonToTop A A (CGWH.tensorMk a a) = (a, a) :=
  CGWH.nativeProductComparison_point_eq A a

example {A M : CGWH.{u, u}} (f : A ⟶ M) (a : A) (m : M) (hfa : f a = m) :
    CGWH.cgwhToTop.map (f ⊗ₘ f) (CGWH.tensorMk a a) = CGWH.tensorMk m m :=
  CGWH.nativeProductMap_point_eq f a m hfa

end
