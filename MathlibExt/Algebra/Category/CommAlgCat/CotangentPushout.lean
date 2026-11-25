/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.Algebra.Category.CommAlgCat.Cotangent
public import MathlibExt.Algebra.Category.CommAlgCat.ExtendScalars
public import MathlibExt.RingTheory.Kaehler.CoefficientPushout
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Canonical pushout of the actual cotangent linearization

For the original ground extension k → K, take the actual tensor pushout
K ⊗[k] P at every algebra P.  The native tensor maps define its functor and
the native Over.post construction retains each original augmentation.

The actual cotangent pushout isomorphism is the existing coefficient
ring-square map: b ⊗ (a ⊗ dp) maps to (b·a) ⊗ d(1 ⊗ p).  Native tensor
pushout instances earn the isomorphism.  Flatness and a desired comparison
are not inputs.  The categorical height includes both independent ground
universes and the original algebra height, as in the existing AQ models;
the lower coefficient-pushout API retains six raw independent universes.

This model-level source does not identify a tensor of an arbitrary resolution
with the canonical André–Quillen resolution.  Native checks are unexecuted.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original algebra-action specialization of the single generic native tensor functor. -/
abbrev algebraFunctor :
    CommAlgCat.{max u v w} k ⥤ CommAlgCat.{max u v w} K :=
  CommAlgCat.extendScalarsOfAlgebra.{u, w, v} k K

/-- The original tensor ground action on the generic functor's actual object. -/
abbrev tensorGroundAlgebra (P : CommAlgCat.{max u v w} k) :
    Algebra k ((algebraFunctor.{u, v, w} k K).obj P) := by
  change Algebra k (K ⊗[k] P)
  infer_instance

/-- The actual right tensor inclusion gives the original P-action. -/
abbrev tensorRightAlgebra (P : CommAlgCat.{max u v w} k) :
    Algebra P ((algebraFunctor.{u, v, w} k K).obj P) := by
  change Algebra P (K ⊗[k] P)
  infer_instance

attribute [local instance] tensorGroundAlgebra tensorRightAlgebra

/-- The original k-to-K tensor action forms its native scalar tower. -/
abbrev tensorGroundTower (P : CommAlgCat.{max u v w} k) :
    IsScalarTower k K ((algebraFunctor.{u, v, w} k K).obj P) := by
  change IsScalarTower k K (K ⊗[k] P)
  infer_instance

/-- The original right inclusion forms its native k-to-P scalar tower. -/
abbrev tensorRightTower (P : CommAlgCat.{max u v w} k) :
    IsScalarTower k P ((algebraFunctor.{u, v, w} k K).obj P) := by
  change IsScalarTower k P (K ⊗[k] P)
  infer_instance

attribute [local instance] tensorGroundTower tensorRightTower

@[simp]
theorem algebraFunctor_map_tmul {P Q : CommAlgCat.{max u v w} k}
    (f : P ⟶ Q) (x : K) (p : P) :
    ((algebraFunctor.{u, v, w} k K).map f).hom (x ⊗ₜ[k] p) = x ⊗ₜ[k] f.hom p :=
  Algebra.TensorProduct.map_tmul (AlgHom.id K K) f.hom x p

/-- The actual right structural map into the tensor pushout. -/
def algebraUnit (P : CommAlgCat.{max u v w} k) :
    P →ₐ[k] (algebraFunctor.{u, v, w} k K).obj P :=
  Algebra.TensorProduct.includeRight

@[simp]
theorem algebraUnit_apply (P : CommAlgCat.{max u v w} k) (p : P) :
    algebraUnit.{u, v, w} k K P p = (1 : K) ⊗ₜ[k] p := rfl

/-- The actual right inclusion is natural in every original algebra map. -/
theorem algebraUnit_naturality {P Q : CommAlgCat.{max u v w} k} (f : P ⟶ Q) :
    (((algebraFunctor.{u, v, w} k K).map f).hom.restrictScalars k).comp
        (algebraUnit.{u, v, w} k K P) =
      (algebraUnit.{u, v, w} k K Q).comp f.hom :=
  Algebra.TensorProduct.map_restrictScalars_comp_includeRight (AlgHom.id K K) f.hom

variable (A : CommAlgCat.{max u v w} k)

/-- The new augmentation target.{u, v, w} is the literal tensor pushout of the original A. -/
abbrev target : CommAlgCat.{max u v w} K := (algebraFunctor.{u, v, w} k K).obj A

/-- Native Over.post retains each augmentation and every original triangle. -/
abbrev overFunctor : Over A ⥤ Over (target.{u, v, w} k K A) :=
  Over.post (algebraFunctor.{u, v, w} k K)

/-- The original tensor ground action retained by native Over.post. -/
abbrev overGroundAlgebra (P : Over A) :
    Algebra k ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra k ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorGroundAlgebra.{u, v, w} k K P.left

/-- The original P-action retained by native Over.post. -/
abbrev overRightAlgebra (P : Over A) :
    Algebra P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra P.left ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorRightAlgebra.{u, v, w} k K P.left

attribute [local instance] overGroundAlgebra overRightAlgebra

/-- Native Over.post keeps the actual k-to-K tensor tower. -/
abbrev overGroundTower (P : Over A) :
    IsScalarTower k K ((overFunctor.{u, v, w} k K A).obj P).left := by
  change IsScalarTower k K ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorGroundTower.{u, v, w} k K P.left

/-- Native Over.post keeps the actual k-to-P tensor tower. -/
abbrev overRightTower (P : Over A) :
    IsScalarTower k P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change IsScalarTower k P.left ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorRightTower.{u, v, w} k K P.left

attribute [local instance] overGroundTower overRightTower

/-- The actual tensor object is the native pushout of the original k-algebra P. -/
abbrev overIsPushout (P : Over A) :
    Algebra.IsPushout k K P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra.IsPushout k K P.left (K ⊗[k] P.left)
  infer_instance

attribute [local instance] overIsPushout

/-- Actual extension of coefficients along the original right inclusion A → K⊗A. -/
abbrev moduleFunctor :
    ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} (target.{u, v, w} k K A) :=
  ModuleCat.extendScalars (algebraMap A (target.{u, v, w} k K A))

/-- The two P-actions on the original pushout target.{u, v, w} agree by its actual augmentation. -/
theorem algebraUnit_augmentation (P : Over A) (p : P.left) :
    ((overFunctor.{u, v, w} k K A).obj P).hom.hom (algebraUnit.{u, v, w} k K P.left p) =
      algebraUnit.{u, v, w} k K A (P.hom.hom p) :=
  algebraFunctor_map_tmul.{u, v, w} k K P.hom 1 p

/-- The original augmentation and structural map determine this point algebra. -/
abbrev pointAlgebra (P : Over A) : Algebra P.left (target.{u, v, w} k K A) :=
  ((algebraMap A (target.{u, v, w} k K A)).comp P.hom.hom.toRingHom).toAlgebra

/-- The original point action forms its actual scalar tower. -/
abbrev pointTower (P : Over A) :
    letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
    letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
    IsScalarTower P.left A (target.{u, v, w} k K A) := by
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The actual pushout right inclusion forms its point scalar tower. -/
abbrev pointPushoutTower (P : Over A) :
    letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
    letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
      CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
    IsScalarTower P.left ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) := by
  letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
  letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
    CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
  apply IsScalarTower.of_algebraMap_eq'
  ext p
  exact (algebraUnit_augmentation.{u, v, w} k K A P p).symm

/-- The actual cotangent pushout isomorphism, earned from native tensor pushouts. -/
def cotangentIso (P : Over A) :
    (moduleFunctor.{u, v, w} k K A).obj (CommAlgCat.cotangent.{u, max v w} k A P) ≅
      CommAlgCat.cotangent.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P) := by
  let B := target.{u, v, w} k K A
  let Q := (overFunctor.{u, v, w} k K A).obj P
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : IsScalarTower k P.left A := CommAlgCat.cotangentScalarTower.{u, max v w} k A P
  letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra.{w, max u v} K B Q
  letI : Algebra P.left B := pointAlgebra.{u, v, w} k K A P
  letI : IsScalarTower P.left A B := pointTower.{u, v, w} k K A P
  letI : IsScalarTower P.left Q.left B := pointPushoutTower.{u, v, w} k K A P
  exact LinearEquiv.toModuleIso
    (KaehlerDifferential.coefficientPushoutEquiv k K P.left Q.left A B)

/-- The actual forward equation retains both coefficient factors and the original p. -/
@[simp]
theorem cotangentIso_tensor (P : Over A) (b : target.{u, v, w} k K A) (a : A) (p : P.left) :
    (cotangentIso.{u, v, w} k K A P).hom.hom
        (b ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P a p) =
      CommAlgCat.cotangentTensor.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
        (b * algebraMap A (target.{u, v, w} k K A) a) (algebraUnit.{u, v, w} k K P.left p) := by
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : IsScalarTower k P.left A := CommAlgCat.cotangentScalarTower.{u, max v w} k A P
  letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
    CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
  letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
  letI : IsScalarTower P.left A (target.{u, v, w} k K A) := pointTower.{u, v, w} k K A P
  letI : IsScalarTower P.left ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
    pointPushoutTower.{u, v, w} k K A P
  exact KaehlerDifferential.coefficientPushoutEquiv_tmul_D
    k K P.left ((overFunctor.{u, v, w} k K A).obj P).left A (target.{u, v, w} k K A) b a p

/-- The inverse recovers the original actual differential tensor. -/
@[simp]
theorem cotangentIso_inv_tensor (P : Over A) (b : target.{u, v, w} k K A) (p : P.left) :
    (cotangentIso.{u, v, w} k K A P).inv.hom
        (CommAlgCat.cotangentTensor.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
          b (algebraUnit.{u, v, w} k K P.left p)) =
      b ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p := by
  have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
    (cotangentIso.{u, v, w} k K A P).hom_inv_id)
      (b ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p)
  change (cotangentIso.{u, v, w} k K A P).inv.hom
    ((cotangentIso.{u, v, w} k K A P).hom.hom
      (b ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p)) =
        b ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p at h
  rw [cotangentIso_tensor.{u, v, w} k K A P b 1 p, map_one, mul_one] at h
  exact h

/-- Every original augmentation map commutes with the earned cotangent pushout map. -/
@[reassoc]
theorem cotangentIso_naturality {P Q : Over A} (f : P ⟶ Q) :
    (moduleFunctor.{u, v, w} k K A).map (CommAlgCat.cotangentMap.{u, max v w} k A f) ≫
        (cotangentIso.{u, v, w} k K A Q).hom =
      (cotangentIso.{u, v, w} k K A P).hom ≫
        CommAlgCat.cotangentMap.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).map f) := by
  let B := target.{u, v, w} k K A
  let C := CommAlgCat.cotangent.{w, max u v} K B ((overFunctor.{u, v, w} k K A).obj Q)
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w}
    (algebraMap A B)
  apply (adj.homEquiv (CommAlgCat.cotangent.{u, max v w} k A P) C).injective
  apply ModuleCat.hom_ext
  apply CommAlgCat.cotangent_hom_ext.{u, max v w, max u v w} k A P
    ((ModuleCat.restrictScalars (algebraMap A B)).obj C)
  intro p
  change (cotangentIso.{u, v, w} k K A Q).hom.hom
      ((1 : B) ⊗ₜ[A] (CommAlgCat.cotangentMap.{u, max v w} k A f).hom
        (CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p)) =
    (CommAlgCat.cotangentMap.{w, max u v} K B
      ((overFunctor.{u, v, w} k K A).map f)).hom
        ((cotangentIso.{u, v, w} k K A P).hom.hom
          ((1 : B) ⊗ₜ[A] CommAlgCat.cotangentTensor.{u, max v w} k A P 1 p))
  rw [CommAlgCat.cotangentMap_tensor.{u, max v w} k A f,
    cotangentIso_tensor.{u, v, w}, cotangentIso_tensor.{u, v, w},
    CommAlgCat.cotangentMap_tensor.{w, max u v} K B]
  simp only [map_one, mul_one]
  have h :
      ((overFunctor.{u, v, w} k K A).map f).left.hom
          (algebraUnit.{u, v, w} k K P.left p) =
        algebraUnit.{u, v, w} k K Q.left (f.left.hom p) :=
    AlgHom.congr_fun (algebraUnit_naturality.{u, v, w} k K f.left) p
  exact congrArg (fun q : ((overFunctor.{u, v, w} k K A).obj Q).left =>
    CommAlgCat.cotangentTensor.{w, max u v} K B
      ((overFunctor.{u, v, w} k K A).obj Q) 1 q) h.symm

/-- The whole actual cotangent linearization commutes naturally with tensor pushout. -/
def cotangentNatIso :
    CommAlgCat.cotangentFunctor.{u, max v w} k A ⋙ moduleFunctor.{u, v, w} k K A ≅
      overFunctor.{u, v, w} k K A ⋙ CommAlgCat.cotangentFunctor.{w, max u v} K (target.{u, v, w} k K A) :=
  NatIso.ofComponents (cotangentIso.{u, v, w} k K A) (cotangentIso_naturality.{u, v, w} k K A)

end CommAlgCat.CotangentPushout

end
