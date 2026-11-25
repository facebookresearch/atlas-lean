/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/HopfAlgebra/FiniteDual/CartierDuality/Basic.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import MathlibExt.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import MathlibExt.Algebra.HopfAlgebra.FiniteDual.Functoriality
public import MathlibExt.CategoryTheory.InvolutiveDual

/-!
# Cartier duality for finite locally free Hopf algebras

A commutative finite locally free group scheme over an affine base is represented by a finite
projective Hopf algebra whose multiplication and comultiplication are both commutative. The linear
dual preserves this bicommutative condition, reverses morphisms, and is involutive by evaluation.

This file packages those facts as a contravariant equivalence on finite locally free
bicommutative Hopf algebras. The equivalence is built from double-dual evaluation by
`CategoryTheory.Functor.dualityEquivalence`, so its inverse is again finite dualization and its
unit and counit are inverse double-dual evaluation; nothing about it is abstract. It is the
algebraic core of Cartier duality over a general affine base; its transport through `Spec` is
provided by
`AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree`.

## Main declarations

* `MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat`: finite locally free commutative,
  cocommutative Hopf algebras over a commutative ring.
* `MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor`: contravariant finite
  dualization.
* `MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.evalIso`: the objectwise double-dual
  evaluation
  isomorphism, natural in morphisms by `evalIso_hom_naturality` and bundled as `evalNatIso`.
* `MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.dualMap_evalIso_inv`: the triangle identity
  exhibiting finite dualization as involutive.
* `MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality`: the resulting
  anti-equivalence, with `cartierDuality_functor` and `cartierDuality_inverse` computing its two
  directions. Its unit and counit are computed by the generic
  `CategoryTheory.Functor.dualityEquivalence_unitIso_hom_app` and its three companions; the
  specializations to `evalIso` hold by `rfl`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 11.c, with Aside 11.17 for a base ring.
-/

public section

open CategoryTheory

namespace MathlibExt

universe u

/-- The object property selecting finite locally free bicommutative Hopf algebras.

The ambient `CommHopfAlgCat` supplies commutativity of multiplication; the final conjunct is
cocommutativity of comultiplication. Finite locally free modules are expressed as finite
projective modules. -/
def finiteLocallyFreeBicommutativeHopfAlgProperty (k : Type u) [CommRing k] :
    ObjectProperty (_root_.CommHopfAlgCat.{u} k) :=
  fun H => Module.Finite k H ∧ Module.Projective k H ∧ Coalgebra.IsCocomm k H

/-- Membership in `finiteLocallyFreeBicommutativeHopfAlgProperty` is finite projectivity together
with cocommutativity. -/
@[simp]
theorem finiteLocallyFreeBicommutativeHopfAlgProperty_iff (k : Type u) [CommRing k]
    (H : _root_.CommHopfAlgCat.{u} k) :
    finiteLocallyFreeBicommutativeHopfAlgProperty k H ↔
      Module.Finite k H ∧ Module.Projective k H ∧ Coalgebra.IsCocomm k H :=
  Iff.rfl

/-- The category of finite locally free bicommutative Hopf algebras over a commutative ring. -/
abbrev FiniteLocallyFreeBicommutativeHopfAlgCat (k : Type u) [CommRing k] : Type _ :=
  (finiteLocallyFreeBicommutativeHopfAlgProperty (k := k)).FullSubcategory

namespace FiniteLocallyFreeBicommutativeHopfAlgCat

variable {k : Type u} [CommRing k]

instance : CoeSort (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) (Type u) :=
  ⟨fun H => H.obj⟩

instance commRing (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) : CommRing H :=
  inferInstanceAs (CommRing H.obj)

instance hopfAlgebra (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    HopfAlgebra k H :=
  inferInstanceAs (HopfAlgebra k H.obj)

instance finite (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) : Module.Finite k H :=
  H.property.1

instance projective (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    Module.Projective k H :=
  H.property.2.1

instance isCocomm (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    Coalgebra.IsCocomm k H :=
  H.property.2.2

variable (k) in
/-- Bundle a finite locally free bicommutative Hopf algebra as an object of
`FiniteLocallyFreeBicommutativeHopfAlgCat`. -/
abbrev of (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    [Module.Projective k H] [Coalgebra.IsCocomm k H] :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  ⟨_root_.CommHopfAlgCat.of k H,
    (finiteLocallyFreeBicommutativeHopfAlgProperty_iff k _).2
      ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The bialgebra morphism underlying a morphism of finite locally free bicommutative Hopf
algebras. -/
abbrev toBialgHom {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    H →ₐc[k] K :=
  f.hom.hom

/-- Bundle a bialgebra morphism between finite locally free bicommutative Hopf algebras. -/
abbrev ofHom {H K : Type u} [CommRing H] [CommRing K] [HopfAlgebra k H]
    [HopfAlgebra k K] [Module.Finite k H] [Module.Finite k K]
    [Module.Projective k H] [Module.Projective k K]
    [Coalgebra.IsCocomm k H] [Coalgebra.IsCocomm k K] (f : H →ₐc[k] K) :
    of k H ⟶ of k K :=
  ObjectProperty.homMk (_root_.CommHopfAlgCat.ofHom f)

/-- Morphisms of finite locally free bicommutative Hopf algebras are determined by their underlying
bialgebra morphisms. -/
@[ext]
theorem hom_ext {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} {f g : H ⟶ K}
    (h : toBialgHom f = toBialgHom g) : f = g :=
  ObjectProperty.hom_ext (P := finiteLocallyFreeBicommutativeHopfAlgProperty k)
    (_root_.CommHopfAlgCat.hom_ext h)

@[simp]
theorem toBialgHom_id {H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id k H :=
  rfl

@[simp]
theorem toBialgHom_comp {H K L : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k}
    (f : H ⟶ K) (g : K ⟶ L) :
    toBialgHom (f ≫ g) = (toBialgHom g).comp (toBialgHom f) :=
  rfl

/-- The finite dual of a finite locally free bicommutative Hopf algebra. -/
noncomputable abbrev dual (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  of k (ConvolutionDual k H)

/-- A morphism of finite locally free bicommutative Hopf algebras induces a morphism of finite
duals in the opposite direction. -/
noncomputable abbrev dualMap {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    dual K ⟶ dual H :=
  ofHom (ConvolutionDual.map k (toBialgHom f))

/-- The bialgebra morphism underlying `dualMap` is the transposed morphism. -/
@[simp]
theorem toBialgHom_dualMap {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    toBialgHom (dualMap f) = ConvolutionDual.map k (toBialgHom f) :=
  rfl

/-- Finite dualization as a contravariant endofunctor on finite locally free bicommutative Hopf
algebras.

The body is exposed so that `dualFunctor.rightOp ⋙ dualFunctor` reduces to double dualization,
without which `evalNatIso` does not typecheck. -/
@[expose]
noncomputable def dualFunctor :
    (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)ᵒᵖ ⥤
      FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k where
  obj H := dual H.unop
  map f := dualMap f.unop
  map_id H := by
    apply hom_ext
    simp only [unop_id, toBialgHom_dualMap, toBialgHom_id, ConvolutionDual.map_id]
  map_comp f g := by
    apply hom_ext
    simp only [unop_comp, toBialgHom_dualMap, toBialgHom_comp,
      ConvolutionDual.map_comp]

/-- The object part of `dualFunctor` is the finite convolution dual. -/
@[simp]
theorem dualFunctor_obj (H : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)ᵒᵖ) :
    (dualFunctor (k := k)).obj H = dual H.unop :=
  (rfl)

/-- The morphism part of `dualFunctor` is precomposition on the finite dual. -/
@[simp]
theorem dualFunctor_map {H K : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)ᵒᵖ}
    (f : H ⟶ K) :
    (dualFunctor (k := k)).map f = dualMap f.unop :=
  (rfl)

/-- The finite-dual functor acts on underlying bialgebra morphisms by precomposition. -/
@[simp↓]
theorem toBialgHom_dualFunctor_map
    {H K : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)ᵒᵖ} (f : H ⟶ K) :
    toBialgHom ((dualFunctor (k := k)).map f) =
      ConvolutionDual.map k (toBialgHom f.unop) :=
  rfl

/-- Evaluation identifies a finite locally free bicommutative Hopf algebra with its double finite
dual. -/
noncomputable def evalIso (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    H ≅ dual (dual H) :=
  ObjectProperty.isoMk (finiteLocallyFreeBicommutativeHopfAlgProperty k)
    (_root_.CommHopfAlgCat.isoMk (ConvolutionDual.evalBialgEquiv k H))

/-- The forward map of `evalIso` evaluates finite-dual functionals. -/
@[simp]
theorem evalIso_hom_apply_apply (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)
    (x : H) (phi : ConvolutionDual k H) :
    ((evalIso H).hom x).ofConv phi = phi.ofConv x :=
  ConvolutionDual.evalBialgEquiv_apply_apply k H x phi

/-- The inverse map of `evalIso` is characterized by evaluation. -/
@[simp]
theorem evalIso_inv_apply_apply (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)
    (Phi : ConvolutionDual k (ConvolutionDual k H)) (phi : ConvolutionDual k H) :
    phi.ofConv ((evalIso H).inv Phi) = Phi.ofConv phi :=
  ConvolutionDual.evalBialgEquiv_symm_apply_apply k H Phi phi

/-- Double-dual evaluation is natural in finite locally free bicommutative Hopf algebras. -/
@[simp, reassoc]
theorem evalIso_hom_naturality
    {H K : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k} (f : H ⟶ K) :
    f ≫ (evalIso K).hom = (evalIso H).hom ≫ dualMap (dualMap f) := by
  apply hom_ext
  exact ConvolutionDual.evalBialgEquiv_naturality k H (toBialgHom f)

/-- Double-dual evaluation as a natural isomorphism from the identity functor to double finite
dualization. -/
noncomputable def evalNatIso :
    𝟭 (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) ≅
      (dualFunctor (k := k)).rightOp ⋙ dualFunctor :=
  NatIso.ofComponents evalIso fun f => evalIso_hom_naturality f

/-- The components of `evalNatIso` are the objectwise evaluation isomorphisms. -/
@[simp]
theorem evalNatIso_hom_app (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    (evalNatIso (k := k)).hom.app H = (evalIso H).hom :=
  (rfl)

/-- The inverse components of `evalNatIso` are the objectwise inverse evaluation
isomorphisms. -/
@[simp]
theorem evalNatIso_inv_app (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    (evalNatIso (k := k)).inv.app H = (evalIso H).inv :=
  (rfl)

/-- Dualizing the inverse evaluation isomorphism of `H` is the evaluation isomorphism of the
finite dual of `H`. This is the triangle identity that makes finite dualization involutive. -/
@[simp]
theorem dualMap_evalIso_inv (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    dualMap (evalIso H).inv = (evalIso (dual H)).hom := by
  apply hom_ext
  apply BialgHom.ext
  intro phi
  apply WithConv.ofConv_injective
  ext Phi
  rw [toBialgHom_dualMap, ConvolutionDual.map_apply_apply]
  exact (evalIso_inv_apply_apply H Phi phi).trans
    (evalIso_hom_apply_apply (dual H) phi Phi).symm

/-- Dualizing the evaluation isomorphism of `H` is the inverse evaluation isomorphism of the
finite dual of `H`. -/
@[simp]
theorem dualMap_evalIso_hom (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    dualMap (evalIso H).hom = (evalIso (dual H)).inv := by
  refine Iso.inv_ext' ?_
  rw [← dualMap_evalIso_inv]
  apply hom_ext
  simp only [toBialgHom_comp, toBialgHom_dualMap, toBialgHom_id, ← ConvolutionDual.map_comp]
  rw [← toBialgHom_comp, Iso.hom_inv_id, toBialgHom_id, ConvolutionDual.map_id]

/-- Double-dual evaluation at the finite dual of `H` undoes the dualized double-dual evaluation
of `H`. This is `isInvolutiveDual_dualFunctor` written with `dualMap` and `evalIso` in place of
`dualFunctor` and `evalNatIso`; it is private because the public content is
`dualMap_evalIso_inv`. -/
private theorem dualMap_evalIso_inv_comp (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k) :
    dualMap (evalIso H).inv ≫ (evalIso (dual H)).inv = 𝟙 (dual H) := by
  rw [dualMap_evalIso_inv, Iso.hom_inv_id]

/-- Finite dualization is involutive in the sense required to build an anti-equivalence out of
it.

`IsInvolutiveDual` spells the triangle identity with `dualFunctor` and `evalNatIso`; those are
the functor and natural isomorphism assembled from `dualMap` and `evalIso`, so the two forms of
the identity are the same statement and `dualMap_evalIso_inv_comp` applies directly. -/
theorem isInvolutiveDual_dualFunctor :
    (dualFunctor (k := k)).IsInvolutiveDual evalNatIso :=
  fun H => dualMap_evalIso_inv_comp H

/-- **Finite locally free Cartier duality.** Finite dualization is an anti-equivalence of the
category of finite locally free bicommutative Hopf algebras over a commutative ring. Its inverse
is finite dualization again, and its unit and counit are inverse double-dual evaluation.

The body is exposed so that `cartierDuality_functor` and `cartierDuality_inverse`, and their
counterparts for the transported group-scheme duality, hold definitionally. -/
@[expose]
noncomputable def cartierDuality :
    (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k)ᵒᵖ ≌
      FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  (dualFunctor (k := k)).dualityEquivalence evalNatIso isInvolutiveDual_dualFunctor

/-- The forward functor of `cartierDuality` is finite dualization. -/
@[simp]
theorem cartierDuality_functor : (cartierDuality (k := k)).functor = dualFunctor :=
  (rfl)

/-- The inverse functor of `cartierDuality` is finite dualization again. -/
@[simp]
theorem cartierDuality_inverse :
    (cartierDuality (k := k)).inverse = (dualFunctor (k := k)).rightOp :=
  (rfl)

instance dualFunctorIsEquivalence : (dualFunctor (k := k)).IsEquivalence :=
  (cartierDuality (k := k)).isEquivalence_functor

end FiniteLocallyFreeBicommutativeHopfAlgCat

end MathlibExt
