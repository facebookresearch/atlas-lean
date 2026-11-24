/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
public import Mathlib.Algebra.Group.Subgroup.Basic
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality

/-!
# The actual product map on based fundamental groups

The equivalence is the pair of the original projection maps. Its inverse
uses the existing product functor on fundamental groupoids. The naturality
law retains the given maps and both basepoint equalities, so its kernel is
the inverse image of the product of the two original kernels.
-/

noncomputable section

open CategoryTheory

universe u v w z

namespace FundamentalGroup

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

private def productPiOne (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y where
  toFun p := ((map ContinuousMap.fst (x, y)) p,
    (map ContinuousMap.snd (x, y)) p)
  invFun q := .of
    ((FundamentalGroupoidFunctor.prodToProdTop (TopCat.of X) (TopCat.of Y)).map
      (X := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
      (Y := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
      (q.1.asHom, q.2.asHom))
  left_inv p := by
    apply End.ext
    change Path.Homotopic.prod (Path.Homotopic.projLeft p.asHom)
      (Path.Homotopic.projRight p.asHom) = p.asHom
    exact Path.Homotopic.prod_projLeft_projRight p.asHom
  right_inv q := by
    apply Prod.ext
    · apply End.ext
      change Path.Homotopic.projLeft (Path.Homotopic.prod q.1.asHom q.2.asHom) = q.1.asHom
      exact Path.Homotopic.projLeft_prod q.1.asHom q.2.asHom
    · apply End.ext
      change Path.Homotopic.projRight (Path.Homotopic.prod q.1.asHom q.2.asHom) = q.2.asHom
      exact Path.Homotopic.projRight_prod q.1.asHom q.2.asHom
  map_mul' p q := Prod.ext
    ((map ContinuousMap.fst (x, y)).map_mul p q)
    ((map ContinuousMap.snd (x, y)).map_mul p q)

private theorem productPiOne_apply (x : X) (y : Y)
    (p : FundamentalGroup (X × Y) (x, y)) :
    productPiOne x y p =
      ((map ContinuousMap.fst (x, y)) p, (map ContinuousMap.snd (x, y)) p) := rfl

private theorem productPiOne_symm_apply (x : X) (y : Y)
    (p : FundamentalGroup X x × FundamentalGroup Y y) :
    (productPiOne x y).symm p = .of
      ((FundamentalGroupoidFunctor.prodToProdTop (TopCat.of X) (TopCat.of Y)).map
        (X := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
        (Y := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
        (p.1.asHom, p.2.asHom)) := rfl

/-- Fundamental groups of a product, with the actual projection maps. -/
public def productMulEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y :=
  productPiOne x y

/-- The forward map consists of the two original projections. -/
public theorem productMulEquiv_apply (x : X) (y : Y)
    (p : FundamentalGroup (X × Y) (x, y)) :
    productMulEquiv x y p =
      ((map ContinuousMap.fst (x, y)) p, (map ContinuousMap.snd (x, y)) p) := by
  unfold productMulEquiv
  exact productPiOne_apply x y p

/-- The inverse is the existing product of the two original path classes. -/
public theorem productMulEquiv_symm_apply (x : X) (y : Y)
    (p : FundamentalGroup X x × FundamentalGroup Y y) :
    (productMulEquiv x y).symm p = .of
      ((FundamentalGroupoidFunctor.prodToProdTop (TopCat.of X) (TopCat.of Y)).map
        (X := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
        (Y := (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y))
        (p.1.asHom, p.2.asHom)) := by
  unfold productMulEquiv
  exact productPiOne_symm_apply x y p

section Naturality

variable {A : Type w} {B : Type z}
  [TopologicalSpace A] [TopologicalSpace B]

/-- The literal product of the two original maps retains their specified point equalities. -/
public theorem productMap_point_eq
    (f : C(X, A)) (g : C(Y, B)) {x : X} {y : Y} {a : A} {b : B}
    (hfa : f x = a) (hgb : g y = b) :
    (f.prodMap g) (x, y) = (a, b) := by
  change (f x, g y) = (a, b)
  exact Prod.ext hfa hgb

/-- Product naturality for the actual based maps, retaining both specified
basepoint equalities. -/
public theorem productMulEquiv_mapOfEq_apply
    (f : C(X, A)) (g : C(Y, B)) {x : X} {y : Y} {a : A} {b : B}
    (hfa : f x = a) (hgb : g y = b)
    (p : FundamentalGroup (X × Y) (x, y)) :
    productMulEquiv a b (mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
      (productMap_point_eq f g hfa hgb) p) =
      (mapOfEq f hfa ((productMulEquiv x y p).1),
        mapOfEq g hgb ((productMulEquiv x y p).2)) := by
  have hfstComp := mapOfEq_comp (x := (x, y)) (y := (a, b)) (z := a)
    (f.prodMap g) (ContinuousMap.fst : C(A × B, A))
    (productMap_point_eq f g hfa hgb) rfl
    (show ((ContinuousMap.fst : C(A × B, A)).comp (f.prodMap g)) (x, y) = a
      from hfa)
  have hfstSource := mapOfEq_comp (x := (x, y)) (y := x) (z := a)
    (ContinuousMap.fst : C(X × Y, X)) f rfl hfa
    (show (f.comp (ContinuousMap.fst : C(X × Y, X))) (x, y) = a from hfa)
  have hsndComp := mapOfEq_comp (x := (x, y)) (y := (a, b)) (z := b)
    (f.prodMap g) (ContinuousMap.snd : C(A × B, B))
    (productMap_point_eq f g hfa hgb) rfl
    (show ((ContinuousMap.snd : C(A × B, B)).comp (f.prodMap g)) (x, y) = b
      from hgb)
  have hsndSource := mapOfEq_comp (x := (x, y)) (y := y) (z := b)
    (ContinuousMap.snd : C(X × Y, Y)) g rfl hgb
    (show (g.comp (ContinuousMap.snd : C(X × Y, Y))) (x, y) = b from hgb)
  change mapOfEq (x := (x, y)) (y := a)
    (f.comp (ContinuousMap.fst : C(X × Y, X)))
    (show (f.comp (ContinuousMap.fst : C(X × Y, X))) (x, y) = a from hfa) = _
      at hfstComp
  change mapOfEq (x := (x, y)) (y := b)
    (g.comp (ContinuousMap.snd : C(X × Y, Y)))
    (show (g.comp (ContinuousMap.snd : C(X × Y, Y))) (x, y) = b from hgb) = _
      at hsndComp
  have hfstSquare := hfstComp.symm.trans hfstSource
  have hsndSquare := hsndComp.symm.trans hsndSource
  have hfstTarget :
      mapOfEq (x := (a, b)) (y := a) (ContinuousMap.fst : C(A × B, A)) rfl =
        map (ContinuousMap.fst : C(A × B, A)) (a, b) :=
    mapOfEq_rfl (ContinuousMap.fst : C(A × B, A)) (a, b)
  have hsndTarget :
      mapOfEq (x := (a, b)) (y := b) (ContinuousMap.snd : C(A × B, B)) rfl =
        map (ContinuousMap.snd : C(A × B, B)) (a, b) :=
    mapOfEq_rfl (ContinuousMap.snd : C(A × B, B)) (a, b)
  have hfstInput :
      mapOfEq (x := (x, y)) (y := x) (ContinuousMap.fst : C(X × Y, X)) rfl =
        map (ContinuousMap.fst : C(X × Y, X)) (x, y) :=
    mapOfEq_rfl (ContinuousMap.fst : C(X × Y, X)) (x, y)
  have hsndInput :
      mapOfEq (x := (x, y)) (y := y) (ContinuousMap.snd : C(X × Y, Y)) rfl =
        map (ContinuousMap.snd : C(X × Y, Y)) (x, y) :=
    mapOfEq_rfl (ContinuousMap.snd : C(X × Y, Y)) (x, y)
  let Fp := mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
    (productMap_point_eq f g hfa hgb)
  have hfstActual :=
    (congrArg (fun k : FundamentalGroup (A × B) (a, b) →* FundamentalGroup A a =>
      k.comp Fp) hfstTarget.symm).trans
        (hfstSquare.trans (congrArg
          (fun k : FundamentalGroup (X × Y) (x, y) →* FundamentalGroup X x =>
            (mapOfEq f hfa).comp k) hfstInput))
  have hsndActual :=
    (congrArg (fun k : FundamentalGroup (A × B) (a, b) →* FundamentalGroup B b =>
      k.comp Fp) hsndTarget.symm).trans
        (hsndSquare.trans (congrArg
          (fun k : FundamentalGroup (X × Y) (x, y) →* FundamentalGroup Y y =>
            (mapOfEq g hgb).comp k) hsndInput))
  rw [productMulEquiv_apply, productMulEquiv_apply]
  apply Prod.ext
  · exact congrArg (fun k : FundamentalGroup (X × Y) (x, y) →*
        FundamentalGroup A a => k p) hfstActual
  · exact congrArg (fun k : FundamentalGroup (X × Y) (x, y) →*
        FundamentalGroup B b => k p) hsndActual

/-- The whole homomorphism square for a product of actual based maps. -/
public theorem productMulEquiv_mapOfEq
    (f : C(X, A)) (g : C(Y, B)) {x : X} {y : Y} {a : A} {b : B}
    (hfa : f x = a) (hgb : g y = b) :
    (productMulEquiv a b).toMonoidHom.comp
        (mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
      (productMap_point_eq f g hfa hgb)) =
      ((mapOfEq f hfa).prodMap (mapOfEq g hgb)).comp
        (productMulEquiv x y).toMonoidHom := by
  apply MonoidHom.ext
  intro p
  exact productMulEquiv_mapOfEq_apply f g hfa hgb p

/-- The kernel of the original product map, in the original product
fundamental group. No quotient map or expected kernel is substituted. -/
public theorem ker_mapOfEq_prodMap
    (f : C(X, A)) (g : C(Y, B)) {x : X} {y : Y} {a : A} {b : B}
    (hfa : f x = a) (hgb : g y = b) :
    MonoidHom.ker (mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
      (productMap_point_eq f g hfa hgb)) =
      ((MonoidHom.ker (mapOfEq f hfa)).prod
        (MonoidHom.ker (mapOfEq g hgb))).comap
          (productMulEquiv x y).toMonoidHom := by
  ext p
  change mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
      (productMap_point_eq f g hfa hgb) p = 1 ↔
    mapOfEq f hfa ((productMulEquiv x y p).1) = 1 ∧
      mapOfEq g hgb ((productMulEquiv x y p).2) = 1
  rw [← (productMulEquiv a b).injective.eq_iff,
    productMulEquiv_mapOfEq_apply f g hfa hgb, map_one]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro h
    exact Prod.ext h.1 h.2

/-- Surjectivity of the original product homomorphism follows from the
surjectivity of the two original based homomorphisms. -/
public theorem mapOfEq_prodMap_surjective
    (f : C(X, A)) (g : C(Y, B)) {x : X} {y : Y} {a : A} {b : B}
    (hfa : f x = a) (hgb : g y = b)
    (hf : Function.Surjective (mapOfEq f hfa))
    (hg : Function.Surjective (mapOfEq g hgb)) :
    Function.Surjective (mapOfEq (x := (x, y)) (y := (a, b)) (f.prodMap g)
      (productMap_point_eq f g hfa hgb)) := by
  intro p
  obtain ⟨pX, hpX⟩ := hf ((productMulEquiv a b p).1)
  obtain ⟨pY, hpY⟩ := hg ((productMulEquiv a b p).2)
  refine ⟨(productMulEquiv x y).symm (pX, pY), ?_⟩
  apply (productMulEquiv a b).injective
  rw [productMulEquiv_mapOfEq_apply f g hfa hgb, MulEquiv.apply_symm_apply, hpX, hpY]

end Naturality

end FundamentalGroup

end
