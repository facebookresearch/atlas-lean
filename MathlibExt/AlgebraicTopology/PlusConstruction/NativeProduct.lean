/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Product
public import MathlibExt.AlgebraicTopology.PlusConstruction.HomotopyEquivSquare
public import MathlibExt.Topology.Category.CGWH.ProductHomotopy

/-!
# Actual native products of plus maps

Both canonical native-to-ordinary comparison maps are genuine homotopy
equivalences derived from actual factor point cofibrancy and the existing
CW product models. Their ORIGINAL strict square transfers the already
proved ordinary product-plus map to the ORIGINAL native tensor map. The
kernel is the original product subgroup pulled through the literal
comparison, and its normality/perfectness are derived.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace CGWH.NativeProduct

/-- The literal comparison for two different native factors preserves their pair point. -/
public theorem comparison_point_eq (A B : CGWH.{u, u}) (a : A) (b : B) :
    prodComparisonToTop A B (tensorMk a b) = (a, b) :=
  (tensorEquivProd_eq_prodComparisonToTop A B (tensorMk a b)).symm.trans
    (tensorEquivProd_tensorMk a b)

/-- The mixed native tensor retains the original point laws of both given maps. -/
public theorem map_point_eq {A B M N : CGWH.{u, u}}
    (f : A ⟶ M) (g : B ⟶ N) (a : A) (b : B) (m : M) (n : N)
    (hfa : f a = m) (hgb : g b = n) :
    CGWH.cgwhToTop.map (f ⊗ₘ g) (tensorMk a b) = tensorMk m n := by
  change (f ⊗ₘ g) (tensorMk a b) = tensorMk m n
  apply (tensorEquivProd M N).injective
  rw [tensorEquivProd_map, tensorEquivProd_tensorMk, hfa, hgb,
    tensorEquivProd_tensorMk]

/-- The product subgroup is pulled through the literal mixed native comparison. -/
public abbrev plusSubgroup (A B : CGWH.{u, u}) (a : A) (b : B)
    (P : Subgroup (FundamentalGroup A a)) (Q : Subgroup (FundamentalGroup B b)) :
    Subgroup (FundamentalGroup (A ⊗ B : CGWH.{u, u}) (tensorMk a b)) :=
  (TopCat.productPlusSubgroup (X := A.toTop) (Y := B.toTop) a b P Q).comap
    (FundamentalGroup.mapOfEq (prodComparisonToTop A B).hom
      (comparison_point_eq A B a b))

/-- Both independently given native maps form the original strict comparison square. -/
public theorem map_comparison {A B M N : CGWH.{u, u}}
    (f : A ⟶ M) (g : B ⟶ N) :
    CGWH.cgwhToTop.map (f ⊗ₘ g) ≫ prodComparisonToTop M N =
      prodComparisonToTop A B ≫
        TopCat.ofHom ((CGWH.cgwhToTop.map f).hom.prodMap
          (CGWH.cgwhToTop.map g).hom) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change prodComparisonToTop M N ((f ⊗ₘ g) z) =
    TopCat.ofHom ((CGWH.cgwhToTop.map f).hom.prodMap
      (CGWH.cgwhToTop.map g).hom) (prodComparisonToTop A B z)
  have hM : (show (cgwhToTop.obj M) × (cgwhToTop.obj N) from
      tensorEquivProd M N ((f ⊗ₘ g) z)) = prodComparisonToTop M N ((f ⊗ₘ g) z) :=
    tensorEquivProd_eq_prodComparisonToTop M N _
  have hTensor : (show (cgwhToTop.obj M) × (cgwhToTop.obj N) from
      tensorEquivProd M N ((f ⊗ₘ g) z)) =
      (cgwhToTop.map f (tensorEquivProd A B z).1,
        cgwhToTop.map g (tensorEquivProd A B z).2) :=
    tensorEquivProd_map f g z
  have hA : (show (cgwhToTop.obj A) × (cgwhToTop.obj B) from
      tensorEquivProd A B z) = prodComparisonToTop A B z :=
    tensorEquivProd_eq_prodComparisonToTop A B z
  have hPair : (cgwhToTop.map f (tensorEquivProd A B z).1,
      cgwhToTop.map g (tensorEquivProd A B z).2) =
      (cgwhToTop.map f (prodComparisonToTop A B z).1,
        cgwhToTop.map g (prodComparisonToTop A B z).2) :=
    congrArg (fun p : (cgwhToTop.obj A) × (cgwhToTop.obj B) =>
      (cgwhToTop.map f p.1, cgwhToTop.map g p.2)) hA
  have hG : (show (cgwhToTop.obj M) × (cgwhToTop.obj N) from
      TopCat.ofHom ((CGWH.cgwhToTop.map f).hom.prodMap
        (CGWH.cgwhToTop.map g).hom) (prodComparisonToTop A B z)) =
      (cgwhToTop.map f (prodComparisonToTop A B z).1,
        cgwhToTop.map g (prodComparisonToTop A B z).2) :=
    TopCat.ofHom_apply _ _
  exact hM.symm.trans (hTensor.trans (hPair.trans hG.symm))

/-- The literal tensor of two possibly different plus maps is plus on its original
product subgroup. The comparison equivalences, acyclicity, kernel, normality and
perfectness are derived from the actual factors and their structural point cofibrations. -/
public theorem isPlus
    (A B M N : CGWH.{u, u})
    [PathConnectedSpace B]
    [PathConnectedSpace M] [PathConnectedSpace N]
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
    let PQ := plusSubgroup A B a b P Q
    ∃ hN : PQ.Normal, ∃ hP : Group.IsPerfect PQ,
      letI := hN
      letI := hP
      @TopCat.IsPlusConstructionAt (A ⊗ B : CGWH.{u, u}).toTop
        (M ⊗ N : CGWH.{u, u}).toTop (CGWH.cgwhToTop.map (f ⊗ₘ g))
        (tensorMk a b) (tensorMk m n)
        (map_point_eq f g a b m n hfa hgb) PQ hN hP := by
  let fTop : A.toTop ⟶ M.toTop := CGWH.cgwhToTop.map f
  let gTop : B.toTop ⟶ N.toTop := CGWH.cgwhToTop.map g
  let F : (A ⊗ B : CGWH.{u, u}).toTop ⟶ (M ⊗ N : CGWH.{u, u}).toTop :=
    CGWH.cgwhToTop.map (f ⊗ₘ g)
  let G : TopCat.of (A × B) ⟶ TopCat.of (M × N) :=
    TopCat.ofHom (fTop.hom.prodMap gTop.hom)
  let S : (A ⊗ B : CGWH.{u, u}).toTop ⟶ TopCat.of (A × B) := prodComparisonToTop A B
  let T : (M ⊗ N : CGWH.{u, u}).toTop ⟶ TopCat.of (M × N) := prodComparisonToTop M N
  let PP := TopCat.productPlusSubgroup (X := A.toTop) (Y := B.toTop) a b P Q
  let : PP.Normal := TopCat.productPlusSubgroup_normal (X := A.toTop) (Y := B.toTop) a b P Q
  let : Group.IsPerfect PP :=
    TopCat.productPlusSubgroup_isPerfect (X := A.toTop) (Y := B.toTop) a b P Q
  let hGPoint : G (a, b) = (m, n) :=
    (TopCat.ofHom_apply (fTop.hom.prodMap gTop.hom) (a, b)).trans
      (FundamentalGroup.productMap_point_eq (x := a) (y := b) (a := m) (b := n)
        fTop.hom gTop.hom hfa hgb)
  have hG : @TopCat.IsPlusConstructionAt (TopCat.of (A × B)) (TopCat.of (M × N))
      G (a, b) (m, n) hGPoint PP ‹PP.Normal› ‹Group.IsPerfect PP› :=
    TopCat.IsPlusConstructionAt.prodContinuousMap
      (X := A.toTop) (Y := B.toTop) (A := M.toTop) (B := N.toTop)
      (f := fTop) (g := gTop) (P := P) (Q := Q) hf hg
  obtain ⟨eS, heS, _, _, _⟩ := prodComparisonToTop_homotopyEquiv_of_cofibrant_points A B a b
  obtain ⟨eT, heT, _, _, _⟩ := prodComparisonToTop_homotopyEquiv_of_cofibrant_points M N m n
  let : PathConnectedSpace (M ⊗ N : CGWH.{u, u}) := prodComparisonToTop_pathConnected M N m n
  have hs : TopCat.ofHom eS.toFun = S :=
    (congrArg TopCat.ofHom heS).trans (TopCat.ofHom_hom S)
  have ht : TopCat.ofHom eT.toFun = T :=
    (congrArg TopCat.ofHom heT).trans (TopCat.ofHom_hom T)
  have hcomm : F ≫ TopCat.ofHom eT.toFun = TopCat.ofHom eS.toFun ≫ G :=
    (congrArg (fun k => F ≫ k) ht).trans
      ((map_comparison f g).trans (congrArg (fun k => k ≫ G) hs.symm))
  let hx : eS.toFun (tensorMk a b) = (a, b) :=
    (congrArg (fun k : C((A ⊗ B : CGWH.{u, u}), A × B) => k (tensorMk a b)) heS).trans
      (comparison_point_eq A B a b)
  let hy : eT.toFun (tensorMk m n) = (m, n) :=
    (congrArg (fun k : C((M ⊗ N : CGWH.{u, u}), M × N) => k (tensorMk m n)) heT).trans
      (comparison_point_eq M N m n)
  have hPayload := TopCat.IsPlusConstructionAt.of_homotopyEquiv_square
    (X := (A ⊗ B : CGWH.{u, u}).toTop) (Y := (M ⊗ N : CGWH.{u, u}).toTop)
    (X' := TopCat.of (A × B)) (Y' := TopCat.of (M × N)) (f := F) (g := G)
    eS eT hcomm (tensorMk a b) (tensorMk m n) (a, b) (m, n)
    (map_point_eq f g a b m n hfa hgb) hx hy hGPoint PP hG
  have hQ : PP.comap (FundamentalGroup.mapOfEq eS.toFun hx) =
      plusSubgroup A B a b P Q :=
    congrArg (fun k => PP.comap k)
      (FundamentalGroup.mapOfEq_congr heS hx (comparison_point_eq A B a b))
  exact Eq.mp (congrArg
    (fun PQ : Subgroup (FundamentalGroup (A ⊗ B : CGWH.{u, u}) (tensorMk a b)) =>
      ∃ hN : PQ.Normal, ∃ hP : Group.IsPerfect PQ,
        letI := hN
        letI := hP
        @TopCat.IsPlusConstructionAt (A ⊗ B : CGWH.{u, u}).toTop
          (M ⊗ N : CGWH.{u, u}).toTop F (tensorMk a b) (tensorMk m n)
          (map_point_eq f g a b m n hfa hgb) PQ hN hP) hQ) hPayload

end CGWH.NativeProduct

namespace CGWH

/-- Compatibility specialization of the canonical comparison to a self-product. -/
public theorem nativeProductComparison_point_eq (A : CGWH.{u, u}) (a : A) :
    prodComparisonToTop A A (tensorMk a a) = (a, a) :=
  NativeProduct.comparison_point_eq A A a a

/-- Compatibility specialization of the original pair-point map law. -/
public theorem nativeProductMap_point_eq {A M : CGWH.{u, u}}
    (f : A ⟶ M) (a : A) (m : M) (hfa : f a = m) :
    (CGWH.cgwhToTop.map (f ⊗ₘ f)) (tensorMk a a) = tensorMk m m :=
  NativeProduct.map_point_eq f f a a m m hfa hfa

/-- The established self-product subgroup is the canonical subgroup with equal factors. -/
public abbrev nativeProductPlusSubgroup (A : CGWH.{u, u}) (a : A)
    (P : Subgroup (FundamentalGroup A a)) :
    Subgroup (FundamentalGroup (A ⊗ A : CGWH.{u, u}) (tensorMk a a)) :=
  NativeProduct.plusSubgroup A A a a P P

/-- Compatibility specialization of the original strict comparison square. -/
private theorem nativeProductMap_comparison {A M : CGWH.{u, u}} (f : A ⟶ M) :
    CGWH.cgwhToTop.map (f ⊗ₘ f) ≫ prodComparisonToTop M M =
      prodComparisonToTop A A ≫
        TopCat.ofHom ((CGWH.cgwhToTop.map f).hom.prodMap (CGWH.cgwhToTop.map f).hom) :=
  NativeProduct.map_comparison f f

/-- The established self-product plus theorem delegates to the canonical two-factor theorem. -/
public theorem nativeProduct_isPlus
    (A M : CGWH.{u, u}) [PathConnectedSpace A] [PathConnectedSpace M]
    (f : A ⟶ M) (a : A) (m : M) (hfa : f a = m)
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop)]
    [Cofibration (TopCat.const m : TopCat.of PUnit.{u + 1} ⟶ M.toTop)]
    (P : Subgroup (FundamentalGroup A a)) [P.Normal] [Group.IsPerfect P]
    (hf : @TopCat.IsPlusConstructionAt A.toTop M.toTop
      (CGWH.cgwhToTop.map f) a m hfa P ‹P.Normal› ‹Group.IsPerfect P›) :
    let Q := nativeProductPlusSubgroup A a P
    ∃ hN : Q.Normal, ∃ hP : Group.IsPerfect Q,
      letI := hN
      letI := hP
      @TopCat.IsPlusConstructionAt (A ⊗ A : CGWH.{u, u}).toTop
        (M ⊗ M : CGWH.{u, u}).toTop (CGWH.cgwhToTop.map (f ⊗ₘ f))
        (tensorMk a a) (tensorMk m m) (nativeProductMap_point_eq f a m hfa) Q hN hP :=
  NativeProduct.isPlus A A M M f f a a m m hfa hfa P P hf hf

end CGWH

end
