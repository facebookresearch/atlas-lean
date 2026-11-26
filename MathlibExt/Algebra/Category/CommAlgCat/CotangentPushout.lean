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
# Cotangent linearization under tensor pushout

Let `k : Type u` and `K : Type w` be commutative rings with `Algebra k K`, and let `A :
CommAlgCat.{max u v w} k`. Put `B=K ⊗_k A`. Tensoring sends an algebra `P→A` to `K ⊗_k P → B`;
its structural maps give the `k`, `K`, and `P` scalar towers.

Cotangent linearization commutes with this pushout: `B ⊗_A (A ⊗_P Ω_{P/k}) ≅ B ⊗_{K⊗_k P}
Ω_{(K⊗_k P)/K}`. The forward map sends `b ⊗ (a ⊗ dp)` to `b·j_A(a) ⊗ d(j_P(p))`, where
`j_A,j_P` are the right tensor inclusions. The inverse and naturality equations retain these
coefficient and algebra maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`. On algebra carriers of
universe `max u v w`, `algebraFunctor k K` sends `P` to `K ⊗[k] P` and a morphism `f` to `id_K
⊗ f`. It is `CommAlgCat.extendScalarsOfAlgebra k K`. -/
abbrev algebraFunctor :
    CommAlgCat.{max u v w} k ⥤ CommAlgCat.{max u v w} K :=
  CommAlgCat.extendScalarsOfAlgebra.{u, w, v} k K

/-- Let `k,K` be commutative rings with `Algebra k K` and `P` a commutative `k`-algebra. The
action `tensorGroundAlgebra k K P` makes `K ⊗_k P` a `k`-algebra via `k→K→K ⊗_k P`. On pure
tensors, `r·(b⊗p)=(algebraMap k K r·b)⊗p`. -/
abbrev tensorGroundAlgebra (P : CommAlgCat.{max u v w} k) :
    Algebra k ((algebraFunctor.{u, v, w} k K).obj P) := by
  change Algebra k (K ⊗[k] P)
  infer_instance

/-- For commutative `k`-algebras `K,P`, the structure `tensorRightAlgebra k K P` is the
`P`-algebra structure on `K ⊗_k P` defined by `p↦1⊗p`. Multiplication by `p` on a pure tensor
`b⊗q` gives `b⊗(p q)`. -/
abbrev tensorRightAlgebra (P : CommAlgCat.{max u v w} k) :
    Algebra P ((algebraFunctor.{u, v, w} k K).obj P) := by
  change Algebra P (K ⊗[k] P)
  infer_instance

attribute [local instance] tensorGroundAlgebra tensorRightAlgebra

/-- For commutative `k`-algebras `K,P`, the tensor pushout satisfies `IsScalarTower k K (K ⊗_k
P)`. Its structural map `k→K ⊗_k P` factors through `K`, and the corresponding scalar actions
compose. -/
abbrev tensorGroundTower (P : CommAlgCat.{max u v w} k) :
    IsScalarTower k K ((algebraFunctor.{u, v, w} k K).obj P) := by
  change IsScalarTower k K (K ⊗[k] P)
  infer_instance

/-- For commutative `k`-algebras `K,P`, the right tensor inclusion `P→K ⊗_k P` gives
`IsScalarTower k P (K ⊗_k P)`. The composite `k→P→K ⊗_k P` agrees with the ground-ring action
on the tensor product. -/
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

/-- For commutative `k`-algebras `K,P`, `algebraUnit k K P : P →ₐ[k] K ⊗_k P` is
`Algebra.TensorProduct.includeRight`. It sends `p` to `1⊗p`. -/
def algebraUnit (P : CommAlgCat.{max u v w} k) :
    P →ₐ[k] (algebraFunctor.{u, v, w} k K).obj P :=
  Algebra.TensorProduct.includeRight

@[simp]
theorem algebraUnit_apply (P : CommAlgCat.{max u v w} k) (p : P) :
    algebraUnit.{u, v, w} k K P p = (1 : K) ⊗ₜ[k] p := rfl

/-- Let `k,K` be commutative rings with `Algebra k K`, and `f : P → Q` a morphism of commutative
`k`-algebras. The right inclusions satisfy `(id_K ⊗ f) ∘ algebraUnit(P) = algebraUnit(Q) ∘ f`,
as `k`-algebra maps from `P` to `K ⊗_k Q`. -/
theorem algebraUnit_naturality {P Q : CommAlgCat.{max u v w} k} (f : P ⟶ Q) :
    (((algebraFunctor.{u, v, w} k K).map f).hom.restrictScalars k).comp
        (algebraUnit.{u, v, w} k K P) =
      (algebraUnit.{u, v, w} k K Q).comp f.hom :=
  Algebra.TensorProduct.map_restrictScalars_comp_includeRight (AlgHom.id K K) f.hom

variable (A : CommAlgCat.{max u v w} k)

/-- Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`, and `A :
CommAlgCat.{max u v w} k`. The new coefficient algebra `target k K A` is `K ⊗_k A`, regarded
as a commutative `K`-algebra with its left-factor structural map. -/
abbrev target : CommAlgCat.{max u v w} K := (algebraFunctor.{u, v, w} k K).obj A

/-- Let `k,K` be commutative rings with `Algebra k K`, `A` a commutative `k`-algebra, and `B=K ⊗_k
A`. The functor `overFunctor k K A : Over A → Over B` is `Over.post (algebraFunctor k K)`. It
sends `P→A` to `K ⊗_k P → K ⊗_k A` by `id_K ⊗ P.hom`. -/
abbrev overFunctor : Over A ⥤ Over (target.{u, v, w} k K A) :=
  Over.post (algebraFunctor.{u, v, w} k K)

/-- For commutative `k`-algebras `K,A` and `P∈Over A`, the underlying algebra of `overFunctor k K
A P` is `K ⊗_k P.left`. Its `k`-algebra action is the composite `k→K→K ⊗_k P.left`, as given
by `overGroundAlgebra`. -/
abbrev overGroundAlgebra (P : Over A) :
    Algebra k ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra k ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorGroundAlgebra.{u, v, w} k K P.left

/-- For commutative `k`-algebras `K,A` and `P∈Over A`, the algebra `K ⊗_k P.left` has the
`P.left`-action supplied by the right inclusion `p↦1⊗p`. This is `overRightAlgebra k K A P`. -/
abbrev overRightAlgebra (P : Over A) :
    Algebra P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra P.left ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorRightAlgebra.{u, v, w} k K P.left

attribute [local instance] overGroundAlgebra overRightAlgebra

/-- Let `K,A` be commutative `k`-algebras and `P∈Over A`. The structural actions on the pushed-out
source satisfy `IsScalarTower k K (K ⊗_k P.left)`, so the ground action factors through the
left tensor factor. -/
abbrev overGroundTower (P : Over A) :
    IsScalarTower k K ((overFunctor.{u, v, w} k K A).obj P).left := by
  change IsScalarTower k K ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorGroundTower.{u, v, w} k K P.left

/-- Let `K,A` be commutative `k`-algebras and `P∈Over A`. The right tensor inclusion gives
`IsScalarTower k P.left (K ⊗_k P.left)`. The ground action agrees with the action obtained
through the source algebra `P.left`. -/
abbrev overRightTower (P : Over A) :
    IsScalarTower k P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change IsScalarTower k P.left ((algebraFunctor.{u, v, w} k K).obj P.left)
  exact tensorRightTower.{u, v, w} k K P.left

attribute [local instance] overGroundTower overRightTower

/-- For commutative `k`-algebras `K,A` and `P∈Over A`, the square with maps `k→K`, `k→P.left`,
`K→K ⊗_k P.left`, and `P.left→K ⊗_k P.left` is an algebra pushout. This is `Algebra.IsPushout
k K P.left ((overFunctor k K A).obj P).left`. -/
abbrev overIsPushout (P : Over A) :
    Algebra.IsPushout k K P.left ((overFunctor.{u, v, w} k K A).obj P).left := by
  change Algebra.IsPushout k K P.left (K ⊗[k] P.left)
  infer_instance

attribute [local instance] overIsPushout

/-- Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`, `A : CommAlgCat.{max u
v w} k`, and `B=K ⊗_k A`. The coefficient functor `moduleFunctor k K A : ModuleCat A →
ModuleCat B` at carrier height `max u v w` is extension along `algebraMap A B`, sending `L` to
`B ⊗_A L`. -/
abbrev moduleFunctor :
    ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} (target.{u, v, w} k K A) :=
  ModuleCat.extendScalars (algebraMap A (target.{u, v, w} k K A))

/-- Let `K,A` be commutative `k`-algebras, `P∈Over A`, and `p∈P.left`. For `j_P(p)=1⊗p` and
`j_A(a)=1⊗a`, the pushed-out augmentation satisfies `(id_K ⊗ P.hom)(j_P(p)) = j_A(P.hom(p))`.
This is equality of the two maps from the source algebra to `K ⊗_k A`. -/
theorem algebraUnit_augmentation (P : Over A) (p : P.left) :
    ((overFunctor.{u, v, w} k K A).obj P).hom.hom (algebraUnit.{u, v, w} k K P.left p) =
      algebraUnit.{u, v, w} k K A (P.hom.hom p) :=
  algebraFunctor_map_tmul.{u, v, w} k K P.hom 1 p

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, and `P∈Over A`. The `P.left`-algebra
structure on `B` is given by `P.left → A → B`, namely `p ↦ 1 ⊗ P.hom(p)`. This is
`pointAlgebra k K A P`. -/
abbrev pointAlgebra (P : Over A) : Algebra P.left (target.{u, v, w} k K A) :=
  ((algebraMap A (target.{u, v, w} k K A)).comp P.hom.hom.toRingHom).toAlgebra

/-- For commutative `k`-algebras `K,A` and `P∈Over A`, the source action on `A` from `P.hom` and
the right inclusion `A→K ⊗_k A` give `IsScalarTower P.left A (K ⊗_k A)`. The induced
`P.left`-action on the pushed-out target is `pointAlgebra k K A P`. -/
abbrev pointTower (P : Over A) :
    letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
    letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
    IsScalarTower P.left A (target.{u, v, w} k K A) := by
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : Algebra P.left (target.{u, v, w} k K A) := pointAlgebra.{u, v, w} k K A P
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Let `K,A` be commutative `k`-algebras and `P∈Over A`. Put `P_K=K ⊗_k P.left` and `B=K ⊗_k A`,
with augmentation `P_K→B` induced by `P.hom`. The right inclusion `P.left→P_K` and this
augmentation give `IsScalarTower P.left P_K B`, with the same source action on `B` as
`P.left→A→B`. -/
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

/-- Let `k,K` be commutative rings with `Algebra k K`, `A` a `k`-algebra, `B=K ⊗_k A`, and `P∈Over
A`. For `P_K=K ⊗_k P.left`, there is a `B`-linear isomorphism `B ⊗_A (A ⊗_{P.left}
Ω_{P.left/k}) ≅ B ⊗_{P_K} Ω_{P_K/K}`. It is `cotangentIso k K A P`, comparing coefficient
extension with cotangent linearization of the pushed-out source. -/
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

/-- Let `K,A` be commutative `k`-algebras, `P∈Over A`, and `B=K ⊗_k A`. For `b∈B`, `a∈A`, and
`p∈P.left`, the forward cotangent pushout map sends `b ⊗ (a ⊗ dp)` to `b·j_A(a) ⊗ d(j_P(p))`.
Here `j_A(a)=1⊗a`, `j_P(p)=1⊗p`, and the target differential is relative to `K` on `K ⊗_k
P.left`. -/
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

/-- Let `K,A` be commutative `k`-algebras, `P∈Over A`, and `B=K ⊗_k A`. For `b∈B` and `p∈P.left`,
the inverse of `cotangentIso k K A P` sends `b ⊗ d(1⊗p)` in the `K`-relative pushed-out
cotangent module to `b ⊗ (1 ⊗ dp)` in `B ⊗_A (A ⊗_{P.left} Ω_{P.left/k})`. -/
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

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, and `f : P → Q` in `Over A`. For
coefficient extension `E : ModuleCat A → ModuleCat B`, pushed-out algebra functor `F`, and
cotangent comparison `γ`, `E(cotangentMap k A f) ≫ γ_Q.hom = γ_P.hom ≫ cotangentMap K B (F.map
f)`. Both maps have coefficient algebra `B`. -/
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

/-- Let `k,K` be commutative rings with `Algebra k K`, `A` a `k`-algebra, and `B=K ⊗_k A`. There
is a natural isomorphism `cotangentFunctor k A ⋙ moduleFunctor k K A ≅ overFunctor k K A ⋙
cotangentFunctor K B`. Its component at `P∈Over A` is `cotangentIso k K A P`. -/
def cotangentNatIso :
    CommAlgCat.cotangentFunctor.{u, max v w} k A ⋙ moduleFunctor.{u, v, w} k K A ≅
      overFunctor.{u, v, w} k K A ⋙ CommAlgCat.cotangentFunctor.{w, max u v} K (target.{u, v, w} k K A) :=
  NatIso.ofComponents (cotangentIso.{u, v, w} k K A) (cotangentIso_naturality.{u, v, w} k K A)

end CommAlgCat.CotangentPushout

end
