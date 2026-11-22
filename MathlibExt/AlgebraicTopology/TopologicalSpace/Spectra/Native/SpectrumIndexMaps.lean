/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricOrthogonalOperatorIndex
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Basic
import MathlibExt.AlgebraicTopology.Spectra.Sequential.EnrichedPresentation

/-!
# Actual maps between spectrum operator indices

The ordered sequential inclusion uses the original sphere powers and genuine
symmetric operator generators. The full symmetric-to-orthogonal map and source
forgetting are supplied by `SymmetricOrthogonalOperatorIndex`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits BraidedCategory
open scoped MonoidalClosed
open CategoryTheory.SequentialSpectrum.EnrichedIndex
namespace CategoryTheory.Spectra.SpectrumIndexMaps
attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

private abbrev finiteDegree (n : ℕ) : I := ⟨FintypeCat.Skeleton.mk n⟩

private def orderedArrow (a n k : ℕ) (h : a + n = k) :
    finiteDegree a ⊗ finiteDegree n ⟶ finiteDegree k :=
  eqToHom (show finiteDegree a ⊗ finiteDegree n = finiteDegree k from congrArg finiteDegree h)

private theorem smallFiniteBijection_injective {A B : I} {f g : A ⟶ B}
    (h : smallFiniteBijection f = smallFiniteBijection g) : f = g := by
  apply Core.hom_ext
  funext z
  rcases z with ⟨z⟩
  have hz := congrArg (fun e : Fin A.of.len ≃ Fin B.of.len => ULift.up (e z)) h
  exact hz

private theorem orderedArrow_finite (a n k : ℕ) (h : a + n = k) :
    smallFiniteBijection (orderedArrow a n k h) = finCongr h := by
  change smallFiniteBijection (eqToHom (congrArg finiteDegree h)) = finCongr h
  cases h
  rw [eqToHom_refl, smallFiniteBijection_id]
  rfl

private theorem finiteBijectionSum_cast_right (p m n : ℕ) (h : m = n) :
    finiteBijectionSum (Equiv.refl (Fin p)) (finCongr h) =
      finCongr (congrArg (fun q => p + q) h) := by
  cases h
  change finiteBijectionSum (Equiv.refl (Fin p)) (Equiv.refl (Fin m)) = Equiv.refl _
  ext i
  dsimp only [finiteBijectionSum, Equiv.trans_apply]
  simp only [Equiv.sumCongr_refl, Equiv.refl_apply, Equiv.apply_symm_apply]

private theorem orderedArrow_comp (a b n k l : ℕ) (ha : a + n = k) (hb : b + k = l) :
    (α_ (finiteDegree b) (finiteDegree a) (finiteDegree n)).hom ≫
      (𝟙 (finiteDegree b) ⊗ₘ orderedArrow a n k ha) ≫ orderedArrow b k l hb =
    orderedArrow (b + a) n l
      ((Nat.add_assoc b a n).trans ((congrArg (fun x => b + x) ha).trans hb)) := by
  apply smallFiniteBijection_injective
  rw [smallFiniteBijection_comp, smallFiniteBijection_comp,
    smallFiniteBijection_tensor, smallFiniteBijection_id]
  let e : Fin ((b + a) + n) ≃ Fin (b + (a + n)) :=
    smallFiniteBijection (α_ (finiteDegree b) (finiteDegree a) (finiteDegree n)).hom
  let f : Fin (a + n) ≃ Fin k := smallFiniteBijection (orderedArrow a n k ha)
  let g : Fin (b + k) ≃ Fin l := smallFiniteBijection (orderedArrow b k l hb)
  let h := (Nat.add_assoc b a n).trans ((congrArg (fun x => b + x) ha).trans hb)
  let r : Fin ((b + a) + n) ≃ Fin l := smallFiniteBijection (orderedArrow (b + a) n l h)
  have he : e = finCongr (Nat.add_assoc b a n) :=
    smallFiniteBijection_associator (finiteDegree b) (finiteDegree a) (finiteDegree n)
  have hf : f = finCongr ha := orderedArrow_finite a n k ha
  have hg : g = finCongr hb := orderedArrow_finite b k l hb
  have hr : r = finCongr h := orderedArrow_finite (b + a) n l h
  change e.trans ((finiteBijectionSum (Equiv.refl (Fin b)) f).trans g) = r
  rw [he, hf, hg, hr, finiteBijectionSum_cast_right]
  ext i
  rfl

/-- The complete ordered sphere coefficient enters the actual symmetric operator Hom. -/
def orderedSymmetricOperatorHom (n k a : ℕ) (h : a + n = k) :
    TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a ⟶
      (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[PointedCGWH.{u, v}]
        PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k)) :=
  PointedCGWH.SymmetricModulePresentation.operatorGenerator
    (finiteDegree a) (finiteDegree n) (finiteDegree k) (orderedArrow a n k h)

/-- Degree transports retain the same original ordered coefficient generator. -/
theorem orderedSymmetricOperatorHom_cast (n k a b : ℕ) (h : a = b)
    (ha : a + n = k) (hb : b + n = k) :
    eqToHom (congrArg (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v}) h) ≫
      orderedSymmetricOperatorHom.{u, v} n k b hb =
        orderedSymmetricOperatorHom.{u, v} n k a ha := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

/-- The original zero-sphere coefficient is the actual symmetric operator identity. -/
theorem orderedSymmetricOperatorHom_zero (n : ℕ) :
    orderedSymmetricOperatorHom.{u, v} n n 0 (Nat.zero_add n) =
      eId PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)) := by
  let V := PointedCGWH.{u, v}
  have ha : orderedArrow 0 n n (Nat.zero_add n) = (λ_ (finiteDegree n)).hom := by
    apply smallFiniteBijection_injective
    rw [orderedArrow_finite, smallFiniteBijection_leftUnitor]
    rfl
  let H : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)
  let g : 𝟙_ V ⟶ H := PointedCGWH.SymmetricModulePresentation.operatorGenerator
    (𝟙_ I) (finiteDegree n) (finiteDegree n) (λ_ (finiteDegree n)).hom
  let f : 𝟙_ V ⟶ H := orderedSymmetricOperatorHom.{u, v} n n 0 (Nat.zero_add n)
  have hi : eId V (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)) = (𝟙 (𝟙_ V)) ≫ g :=
    PointedCGWH.SymmetricModulePresentation.operatorGenerator_unit.{u, v} (finiteDegree n)
  have hf : f = g := congrArg
    (fun h => PointedCGWH.SymmetricModulePresentation.operatorGenerator
      (finiteDegree 0) (finiteDegree n) (finiteDegree n) h) ha
  change f = _
  exact hf.trans ((Category.id_comp g).symm.trans hi.symm)

/-- Full ordered coefficients compose by the original late-power-first sphere multiplication. -/
theorem orderedSymmetricOperatorHom_comp (a b n k l : ℕ) (ha : a + n = k) (hb : b + k = l) :
    (orderedSymmetricOperatorHom.{u, v} n k a ha ⊗ₘ
      orderedSymmetricOperatorHom.{u, v} k l b hb) ≫
      eComp PointedCGWH.{u, v}
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l)) =
    (β_ (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a)
      (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} b)).hom ≫
      (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v} b a).inv ≫
      orderedSymmetricOperatorHom.{u, v} n l (b + a)
        ((Nat.add_assoc b a n).trans ((congrArg (fun x => b + x) ha).trans hb)) := by
  let V := PointedCGWH.{u, v}
  let A := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a
  let B := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} b
  let C := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} (b + a)
  let h := (Nat.add_assoc b a n).trans ((congrArg (fun x => b + x) ha).trans hb)
  let μ : B ⊗ A ⟶ C := PointedCGWH.sphereCopowerLaxData.{u, v}.mu
    ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj (finiteDegree b))
    ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj (finiteDegree a))
  let t : (finiteDegree b ⊗ finiteDegree a) ⊗ finiteDegree n ⟶ finiteDegree l :=
    (α_ (finiteDegree b) (finiteDegree a) (finiteDegree n)).hom ≫
      (𝟙 (finiteDegree b) ⊗ₘ orderedArrow a n k ha) ≫ orderedArrow b k l hb
  let g : C ⟶ (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[V]
      PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l)) :=
    PointedCGWH.SymmetricModulePresentation.operatorGenerator
      (finiteDegree b ⊗ finiteDegree a) (finiteDegree n) (finiteDegree l) t
  let f : C ⟶ (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[V]
      PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l)) :=
    orderedSymmetricOperatorHom.{u, v} n l (b + a) h
  have hm : μ = (TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v} b a).inv := rfl
  have hg : g = f := congrArg
    (fun t => PointedCGWH.SymmetricModulePresentation.operatorGenerator
      (finiteDegree (b + a)) (finiteDegree n) (finiteDegree l) t)
    (orderedArrow_comp a b n k l ha hb)
  have hc := PointedCGWH.SymmetricModulePresentation.operatorGenerator_comp.{u, v}
    (finiteDegree a) (finiteDegree b) (finiteDegree n) (finiteDegree k) (finiteDegree l)
    (orderedArrow a n k ha) (orderedArrow b k l hb)
  change _ = (β_ A B).hom ≫ μ ≫ g at hc
  rw [hm, hg] at hc
  exact hc

/-- Every full sequential Hom maps by its original ordered sphere coefficient;
backward Hom objects use their actual initial map. -/
def sequentialSymmetricOperatorHomMap
    (n k : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    (n ⟶[PointedCGWH.{u, v}] k) ⟶
      (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree) ⟶[PointedCGWH.{u, v}]
        PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree)) :=
  if h : n.degree ≤ k.degree then
    eqToHom (indexHom_of_le PointedCGWH.sphereOne.{u, v} n k h) ≫
      orderedSymmetricOperatorHom.{u, v} n.degree k.degree (k.degree - n.degree)
        (Nat.sub_add_cancel h)
  else
    eqToHom (indexHom_of_gt PointedCGWH.sphereOne.{u, v} n k (Nat.lt_of_not_ge h)) ≫
      initial.to _

/-- Forward Homs retain the entire original degree-difference sphere power. -/
theorem sequentialSymmetricOperatorHomMap_of_le
    (n k : PointedCGWH.Spectra.Sequential.Index.{u, v}) (h : n.degree ≤ k.degree) :
    sequentialSymmetricOperatorHomMap.{u, v} n k =
      eqToHom (indexHom_of_le PointedCGWH.sphereOne.{u, v} n k h) ≫
        orderedSymmetricOperatorHom.{u, v} n.degree k.degree (k.degree - n.degree)
          (Nat.sub_add_cancel h) := dite_eq_left h

/-- The original degree-zero sequential identity maps to the genuine operator identity. -/
theorem sequentialSymmetricOperatorHomMap_id
    (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    eId PointedCGWH.{u, v} n ≫ sequentialSymmetricOperatorHomMap.{u, v} n n =
      eId PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree)) := by
  let V := PointedCGWH.{u, v}
  let K := PointedCGWH.sphereOne.{u, v}
  let d := n.degree - n.degree
  let H : V := indexHom K n n
  let P : V := TensorPower.tensorPowObj K d
  let Z : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree)
  let eH : H = P := indexHom_of_le K n n (Nat.le_refl n.degree)
  let eZ : P = 𝟙_ V := congrArg (TensorPower.tensorPowObj K) (Nat.sub_self n.degree)
  let p : 𝟙_ V ⟶ H := indexId K n
  let q : H ⟶ P := eqToHom eH
  let t : P ⟶ 𝟙_ V := eqToHom eZ
  let m : H ⟶ Z := sequentialSymmetricOperatorHomMap.{u, v} n n
  let a : P ⟶ Z := orderedSymmetricOperatorHom.{u, v} n.degree n.degree d
    (Nat.sub_add_cancel (Nat.le_refl n.degree))
  let z : 𝟙_ V ⟶ Z := orderedSymmetricOperatorHom.{u, v} n.degree n.degree 0 (Nat.zero_add _)
  have hm : m = q ≫ a := sequentialSymmetricOperatorHomMap_of_le.{u, v} n n (Nat.le_refl _)
  have ha : a = t ≫ z := (orderedSymmetricOperatorHom_cast.{u, v}
    n.degree n.degree d 0 (Nat.sub_self n.degree)
    (Nat.sub_add_cancel (Nat.le_refl n.degree)) (Nat.zero_add _)).symm
  have hq : p ≫ q ≫ t = 𝟙 (𝟙_ V) := by
    change eqToHom _ ≫ eqToHom _ ≫ eqToHom _ = _
    rw [eqToHom_trans, eqToHom_trans]
    rfl
  change p ≫ m = _
  rw [hm, ha]
  rw [← Category.assoc q t z, ← Category.assoc p (q ≫ t) z, hq, Category.id_comp]
  exact orderedSymmetricOperatorHom_zero.{u, v} n.degree

private theorem tensorCast_eq {X Y X' Y' : PointedCGWH.{u, v}}
    (h : X = X') (k : Y = Y') :
    (eqToHom h ⊗ₘ eqToHom k) = eqToHom (congrArg₂ (fun A B => A ⊗ B) h k) := by
  cases h
  cases k
  exact MonoidalCategory.id_tensorHom_id X Y

/-- Forward-degree composition uses all original powers and exact degree transports. -/
theorem sequentialSymmetricOperatorHomMap_comp_of_le
    (n k l : PointedCGWH.Spectra.Sequential.Index.{u, v})
    (hnk : n.degree ≤ k.degree) (hkl : k.degree ≤ l.degree) :
    eComp PointedCGWH.{u, v} n k l ≫ sequentialSymmetricOperatorHomMap.{u, v} n l =
    (sequentialSymmetricOperatorHomMap.{u, v} n k ⊗ₘ
      sequentialSymmetricOperatorHomMap.{u, v} k l) ≫
      eComp PointedCGWH.{u, v}
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l.degree)) := by
  let V := PointedCGWH.{u, v}
  let K := PointedCGWH.sphereOne.{u, v}
  let p := k.degree - n.degree
  let q := l.degree - k.degree
  let r := l.degree - n.degree
  let H₁ : V := indexHom K n k
  let H₂ : V := indexHom K k l
  let H₃ : V := indexHom K n l
  let P : V := TensorPower.tensorPowObj K p
  let Q : V := TensorPower.tensorPowObj K q
  let R : V := TensorPower.tensorPowObj K r
  let J₁ : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree)
  let J₂ : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l.degree)
  let J₃ : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l.degree)
  let e₁ : H₁ = P := indexHom_of_le K n k hnk
  let e₂ : H₂ = Q := indexHom_of_le K k l hkl
  let e₃ : H₃ = R := indexHom_of_le K n l (hnk.trans hkl)
  let s : H₁ ⟶ P := eqToHom e₁
  let t : H₂ ⟶ Q := eqToHom e₂
  let u : H₃ ⟶ R := eqToHom e₃
  let u' : R ⟶ H₃ := eqToHom e₃.symm
  let st : H₁ ⊗ H₂ ⟶ P ⊗ Q := eqToHom (congrArg₂ (fun A B => A ⊗ B) e₁ e₂)
  have hst : st = s ⊗ₘ t := (tensorCast_eq.{u, v} e₁ e₂).symm
  have hp : p + n.degree = k.degree := Nat.sub_add_cancel hnk
  have hq : q + k.degree = l.degree := Nat.sub_add_cancel hkl
  have hr : r + n.degree = l.degree := Nat.sub_add_cancel (hnk.trans hkl)
  have hd : p + q = r := by dsimp only [p, q, r]; omega
  let d : TensorPower.tensorPowObj K (p + q) ⟶ R :=
    eqToHom (congrArg (TensorPower.tensorPowObj K) hd)
  let rev : P ⊗ Q ⟶ TensorPower.tensorPowObj K (p + q) := reversePair K p q
  let m₁ : P ⟶ J₁ := orderedSymmetricOperatorHom.{u, v} n.degree k.degree p hp
  let m₂ : Q ⟶ J₂ := orderedSymmetricOperatorHom.{u, v} k.degree l.degree q hq
  let m₃ : R ⟶ J₃ := orderedSymmetricOperatorHom.{u, v} n.degree l.degree r hr
  let φ₁ : H₁ ⟶ J₁ := sequentialSymmetricOperatorHomMap.{u, v} n k
  let φ₂ : H₂ ⟶ J₂ := sequentialSymmetricOperatorHomMap.{u, v} k l
  let φ₃ : H₃ ⟶ J₃ := sequentialSymmetricOperatorHomMap.{u, v} n l
  let ci : H₁ ⊗ H₂ ⟶ H₃ := indexComp K n k l
  let co : J₁ ⊗ J₂ ⟶ J₃ := eComp V
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree))
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree))
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l.degree))
  have hc : ci = st ≫ rev ≫ d ≫ u' := indexComp_of_le K n k l hnk hkl
  have hφ₁ : φ₁ = s ≫ m₁ := sequentialSymmetricOperatorHomMap_of_le.{u, v} n k hnk
  have hφ₂ : φ₂ = t ≫ m₂ := sequentialSymmetricOperatorHomMap_of_le.{u, v} k l hkl
  have hφ₃ : φ₃ = u ≫ m₃ := sequentialSymmetricOperatorHomMap_of_le.{u, v} n l (hnk.trans hkl)
  have hu : u' ≫ u = 𝟙 R := by rw [eqToHom_trans]; rfl
  let e : TensorPower.tensorPowObj K (q + p) ⟶ TensorPower.tensorPowObj K (p + q) :=
    eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm q p))
  let ed : TensorPower.tensorPowObj K (q + p) ⟶ R :=
    eqToHom (congrArg (TensorPower.tensorPowObj K) ((Nat.add_comm q p).trans hd))
  let μ : Q ⊗ P ⟶ TensorPower.tensorPowObj K (q + p) := (TensorPower.tensorPowObj_add K q p).inv
  let hqp := (Nat.add_assoc q p n.degree).trans ((congrArg (fun x => q + x) hp).trans hq)
  let mq : TensorPower.tensorPowObj K (q + p) ⟶ J₃ :=
    orderedSymmetricOperatorHom.{u, v} n.degree l.degree (q + p) hqp
  have hed : e ≫ d = ed := eqToHom_trans _ _
  have hdeg : ed ≫ m₃ = mq := orderedSymmetricOperatorHom_cast.{u, v}
    n.degree l.degree (q + p) r ((Nat.add_comm q p).trans hd) hqp hr
  have hrev : rev = (β_ P Q).hom ≫ μ ≫ e := rfl
  have hOrd : (m₁ ⊗ₘ m₂) ≫ co = (β_ P Q).hom ≫ μ ≫ mq :=
    orderedSymmetricOperatorHom_comp.{u, v} p q n.degree k.degree l.degree hp hq
  have hCore : rev ≫ d ≫ m₃ = (m₁ ⊗ₘ m₂) ≫ co := by
    rw [hrev]
    simp only [Category.assoc]
    rw [← Category.assoc e d m₃, hed, hdeg]
    exact hOrd.symm
  change ci ≫ φ₃ = (φ₁ ⊗ₘ φ₂) ≫ co
  rw [hc, hφ₁, hφ₂, hφ₃]
  simp only [Category.assoc]
  rw [← Category.assoc u' u m₃, hu, Category.id_comp,
    ← tensorHom_comp_tensorHom_assoc, ← hst]
  simpa only [Category.assoc] using congrArg (fun f => st ≫ f) hCore

/-- All full sequential Hom compositions, including each backward initial case, are preserved. -/
theorem sequentialSymmetricOperatorHomMap_comp
    (n k l : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    eComp PointedCGWH.{u, v} n k l ≫ sequentialSymmetricOperatorHomMap.{u, v} n l =
    (sequentialSymmetricOperatorHomMap.{u, v} n k ⊗ₘ
      sequentialSymmetricOperatorHomMap.{u, v} k l) ≫
      eComp PointedCGWH.{u, v}
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree k.degree))
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree l.degree)) := by
  let K := PointedCGWH.sphereOne.{u, v}
  by_cases hnk : n.degree ≤ k.degree
  · by_cases hkl : k.degree ≤ l.degree
    · exact sequentialSymmetricOperatorHomMap_comp_of_le.{u, v} n k l hnk hkl
    · have h : IsInitial (indexHom K n k ⊗ indexHom K k l) := by
        rw [indexHom_of_gt K k l (Nat.lt_of_not_ge hkl)]
        exact MonoidalCategory.tensorInitialLeft _
      exact h.hom_ext _ _
  · have h : IsInitial (indexHom K n k ⊗ indexHom K k l) := by
      rw [indexHom_of_gt K n k (Nat.lt_of_not_ge hnk)]
      exact MonoidalCategory.tensorInitialRight _
    exact h.hom_ext _ _

/-- The actual enriched ordered sequential-to-symmetric spectrum operator inclusion. -/
def sequentialSymmetricOperatorIndexFunctor :
    EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v} where
  obj n := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree)
  map := sequentialSymmetricOperatorHomMap.{u, v}
  map_id := sequentialSymmetricOperatorHomMap_id.{u, v}
  map_comp := sequentialSymmetricOperatorHomMap_comp.{u, v}

/-- The original one-circle successor inclusion retains the original degree-one tensor power. -/
theorem sequentialSymmetricOperatorHomMap_successor (n : ℕ) :
    (indexHomSuccessorIso PointedCGWH.sphereOne.{u, v} n).inv ≫
      sequentialSymmetricOperatorHomMap.{u, v}
        (degree PointedCGWH.sphereOne.{u, v} n)
        (degree PointedCGWH.sphereOne.{u, v} (n + 1)) =
    (λ_ PointedCGWH.sphereOne.{u, v}).inv ≫
      orderedSymmetricOperatorHom.{u, v} n (n + 1) 1 (Nat.add_comm 1 n) := by
  let V := PointedCGWH.{u, v}
  let K := PointedCGWH.sphereOne.{u, v}
  let i := degree K n
  let j := degree K (n + 1)
  let d := (n + 1) - n
  have hd : d = 1 := by dsimp only [d]; omega
  have hij : i.degree ≤ j.degree := by change n ≤ n + 1; omega
  let H : V := indexHom K i j
  let P : V := TensorPower.tensorPowObj K d
  let Q : V := TensorPower.tensorPowObj K 1
  let Z : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1))
  let eH : H = P := indexHom_of_le K i j hij
  let eP : P = Q := congrArg (TensorPower.tensorPowObj K) hd
  let s : K ⟶ H := (indexHomSuccessorIso K n).inv
  let q : H ⟶ P := eqToHom eH
  let t : P ⟶ Q := eqToHom eP
  let m : H ⟶ Z := sequentialSymmetricOperatorHomMap.{u, v} i j
  let a : P ⟶ Z := orderedSymmetricOperatorHom.{u, v} n (n + 1) d (Nat.sub_add_cancel hij)
  let z : Q ⟶ Z := orderedSymmetricOperatorHom.{u, v} n (n + 1) 1 (Nat.add_comm 1 n)
  let l : K ⟶ Q := (λ_ K).inv
  have hm : m = q ≫ a := sequentialSymmetricOperatorHomMap_of_le.{u, v} i j hij
  have ha : a = t ≫ z := (orderedSymmetricOperatorHom_cast.{u, v}
    n (n + 1) d 1 hd (Nat.sub_add_cancel hij) (Nat.add_comm 1 n)).symm
  have hs : s = l ≫ eqToHom (eH.trans eP).symm := by
    rfl
  have hCast : s ≫ q ≫ t = l := by
    rw [hs]
    simp only [Category.assoc]
    rw [eqToHom_trans, eqToHom_trans]
    exact Category.comp_id l
  change s ≫ m = l ≫ z
  rw [hm, ha, ← Category.assoc q t z, ← Category.assoc s (q ≫ t) z, hCast]

/-- The concrete original left successor map obtained by forgetting permutations. -/
def symmetricToSequentialSourceStructureMap
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    PointedCGWH.sphereOne.{u, v} ⊗
      F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)) ⟶
      F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1))) :=
  ((λ_ PointedCGWH.sphereOne.{u, v}).inv ⊗ₘ 𝟙 _) ≫
    (β_ (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)))
      (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} 1)).inv ≫
    F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)) ◁
      orderedSymmetricOperatorHom.{u, v} n (n + 1) 1 (Nat.add_comm 1 n) ≫
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map
      (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
      (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1))))

/-- The actual operator restriction has precisely the original left successor map. -/
theorem symmetricToSequentialSourceStructureMap_eq
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    CategoryTheory.Spectra.Sequential.structureMap
      ((EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj F) n =
        symmetricToSequentialSourceStructureMap.{u, v} F n := by
  let V := PointedCGWH.{u, v}
  let K := PointedCGWH.sphereOne.{u, v}
  let i := degree K n
  let j := degree K (n + 1)
  let X : V := F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
  let Y : V := F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1)))
  let H : V := indexHom K i j
  let P : V := TensorPower.tensorPowObj K 1
  let J : V := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n) ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1))
  let s : K ⟶ H := (indexHomSuccessorIso K n).inv
  let φ : H ⟶ J := sequentialSymmetricOperatorHomMap.{u, v} i j
  let l : K ⟶ P := (λ_ K).inv
  let g : P ⟶ J := orderedSymmetricOperatorHom.{u, v} n (n + 1) 1 (Nat.add_comm 1 n)
  let f : J ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1)))
  have hs : s ≫ φ = l ≫ g := sequentialSymmetricOperatorHomMap_successor.{u, v} n
  have hPair : (s ⊗ₘ 𝟙 X) ≫ (φ ⊗ₘ 𝟙 X) = (s ≫ φ) ⊗ₘ 𝟙 X := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hSplit : ((l ≫ g) ⊗ₘ 𝟙 X) = (l ⊗ₘ 𝟙 X) ≫ (g ⊗ₘ 𝟙 X) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  change (s ⊗ₘ 𝟙 X) ≫ (β_ X H).inv ≫ MonoidalClosed.uncurry (φ ≫ f) =
    (l ⊗ₘ 𝟙 X) ≫ (β_ X P).inv ≫ X ◁ g ≫ MonoidalClosed.uncurry f
  rw [MonoidalClosed.uncurry_natural_left, ← braiding_inv_naturality_left_assoc]
  rw [← tensorHom_id, ← Category.assoc (s ⊗ₘ 𝟙 X) (φ ⊗ₘ 𝟙 X)
    ((β_ X J).inv ≫ MonoidalClosed.uncurry f), hPair, hs]
  rw [hSplit]
  simp only [Category.assoc, tensorHom_id, braiding_inv_naturality_left_assoc]

/-- Forgetting the original symmetric spectrum keeps its levels and original left structure maps. -/
def symmetricToSequentialSourceSpectrum
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    CategoryTheory.SequentialSpectrum PointedCGWH.{u, v} PointedCGWH.sphereOne.{u, v} where
  level n := F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
  structureMap := symmetricToSequentialSourceStructureMap.{u, v} F

/-- The original structure spectrum is recovered from the full operator restriction. -/
theorem symmetricToSequentialSourceSpectrum_eq
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    symmetricToSequentialSourceSpectrum.{u, v} F =
      CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor
        PointedCGWH.sphereOne.{u, v}
        ((EnrichedFunctorCat.restriction
          sequentialSymmetricOperatorIndexFunctor.{u, v}).obj F) := by
  let V := PointedCGWH.{u, v}
  let K := PointedCGWH.sphereOne.{u, v}
  let L := fun n => F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
  have h : (fun n => symmetricToSequentialSourceStructureMap.{u, v} F n) =
      (fun n => CategoryTheory.Spectra.Sequential.structureMap
        ((EnrichedFunctorCat.restriction
          sequentialSymmetricOperatorIndexFunctor.{u, v}).obj F) n) := by
    funext n
    exact (symmetricToSequentialSourceStructureMap_eq.{u, v} F n).symm
  exact congrArg (fun s : ∀ n, K ⊗ L n ⟶ L (n + 1) =>
    (⟨L, s⟩ : CategoryTheory.SequentialSpectrum V K)) h

/-- The concrete original forgetting structure supplies its actual full-Hom sequential functor. -/
def symmetricToSequentialSourceObject
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    PointedCGWH.Spectra.Sequential.Spectrum.{u, v} :=
  CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctor
    PointedCGWH.sphereOne.{u, v} (symmetricToSequentialSourceSpectrum.{u, v} F)

/-- Original structure forgetting and operator restriction agree on the complete spectrum object. -/
theorem symmetricToSequentialSourceObject_eq
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    symmetricToSequentialSourceObject.{u, v} F =
      (EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj F := by
  exact (congrArg (CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctor
      PointedCGWH.sphereOne.{u, v}) (symmetricToSequentialSourceSpectrum_eq.{u, v} F)).trans
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.to_from PointedCGWH.sphereOne.{u, v} _)

/-- An original symmetric morphism retains all levels and commutes with each left structure map. -/
def symmetricToSequentialSourceStructureMorphism
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (q : F ⟶ G) :
    symmetricToSequentialSourceSpectrum.{u, v} F ⟶
      symmetricToSequentialSourceSpectrum.{u, v} G where
  levelMap n := EnrichedFunctorCat.component q
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n))
  naturality n := by
    let K := PointedCGWH.sphereOne.{u, v}
    let r := EnrichedFunctorCat.restrictionMap sequentialSymmetricOperatorIndexFunctor.{u, v} q
    have h := CategoryTheory.Spectra.Sequential.structureMap_naturality r n
    have hn : CategoryTheory.Spectra.Sequential.levelMap r n =
        EnrichedFunctorCat.component q
          (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n)) :=
      EnrichedFunctorCat.restrictionMap_component sequentialSymmetricOperatorIndexFunctor.{u, v}
        q (degree K n)
    have hn' : CategoryTheory.Spectra.Sequential.levelMap r (n + 1) =
        EnrichedFunctorCat.component q
          (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree (n + 1))) :=
      EnrichedFunctorCat.restrictionMap_component sequentialSymmetricOperatorIndexFunctor.{u, v}
        q (degree K (n + 1))
    rw [hn, hn', symmetricToSequentialSourceStructureMap_eq,
      symmetricToSequentialSourceStructureMap_eq] at h
    exact h

/-- The original level morphism induces its genuine full-Hom sequential transformation. -/
def symmetricToSequentialSourceMorphism
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (q : F ⟶ G) : symmetricToSequentialSourceObject.{u, v} F ⟶
      symmetricToSequentialSourceObject.{u, v} G :=
  CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctorMap
    PointedCGWH.sphereOne.{u, v} (symmetricToSequentialSourceStructureMorphism.{u, v} q)

/-- Every genuine sequential morphism component is the original symmetric level component. -/
theorem symmetricToSequentialSourceMorphism_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (q : F ⟶ G) (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    EnrichedFunctorCat.component (symmetricToSequentialSourceMorphism.{u, v} q) n =
      EnrichedFunctorCat.component q
        (PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree)) :=
  CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctorMap_component
    PointedCGWH.sphereOne.{u, v} (symmetricToSequentialSourceStructureMorphism.{u, v} q) n

/-- Actual source forgetting keeps the original left structure spectrum and complete morphisms. -/
def symmetricToSequentialSourceForget :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      PointedCGWH.Spectra.Sequential.Spectrum.{u, v} where
  obj := symmetricToSequentialSourceObject.{u, v}
  map := symmetricToSequentialSourceMorphism.{u, v}
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [symmetricToSequentialSourceMorphism_component, EnrichedFunctorCat.component_id]
    rfl
  map_comp q r := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [symmetricToSequentialSourceMorphism_component, EnrichedFunctorCat.component_comp]
    rfl

/-- Restriction of the complete sequential operator action equals original structure forgetting. -/
theorem symmetricToSequentialSourceForget_eq_restriction :
    symmetricToSequentialSourceForget.{u, v} =
      EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v} := by
  refine Functor.ext (fun F => symmetricToSequentialSourceObject_eq.{u, v} F) ?_
  intro F G q
  let SF := symmetricToSequentialSourceObject.{u, v} F
  let SG := symmetricToSequentialSourceObject.{u, v} G
  let RF := (EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj F
  let RG := (EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj G
  let qs : SF ⟶ SG := symmetricToSequentialSourceMorphism.{u, v} q
  let qr : RF ⟶ RG :=
    EnrichedFunctorCat.restrictionMap sequentialSymmetricOperatorIndexFunctor.{u, v} q
  let f : SF ⟶ RF := eqToHom (symmetricToSequentialSourceObject_eq.{u, v} F)
  let g : RG ⟶ SG := eqToHom (symmetricToSequentialSourceObject_eq.{u, v} G).symm
  change qs = f ≫ qr ≫ g
  apply EnrichedFunctorCat.hom_ext
  intro n
  let N := PointedCGWH.symmetricOperatorObj.{u, v} (finiteDegree n.degree)
  let X := F.toEnrichedFunctor.obj N
  let Y := G.toEnrichedFunctor.obj N
  let cs : X ⟶ Y := EnrichedFunctorCat.component qs n
  let cr : X ⟶ Y := EnrichedFunctorCat.component qr n
  let cf : X ⟶ X := EnrichedFunctorCat.component f n
  let cg : Y ⟶ Y := EnrichedFunctorCat.component g n
  have hf : cf = 𝟙 X := by
    have h := eqToHom_map (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) n)
      (symmetricToSequentialSourceObject_eq.{u, v} F)
    change cf = eqToHom _ at h
    exact h.trans (by rfl)
  have hg : cg = 𝟙 Y := by
    have h := eqToHom_map (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) n)
      (symmetricToSequentialSourceObject_eq.{u, v} G).symm
    change cg = eqToHom _ at h
    exact h.trans (by rfl)
  have hS : cs = EnrichedFunctorCat.component q N :=
    symmetricToSequentialSourceMorphism_component.{u, v} q n
  have hR : cr = EnrichedFunctorCat.component q N :=
    EnrichedFunctorCat.restrictionMap_component sequentialSymmetricOperatorIndexFunctor.{u, v} q n
  simp only [EnrichedFunctorCat.component_comp]
  change cs = cf ≫ cr ≫ cg
  rw [hf, hg, Category.id_comp, Category.comp_id]
  exact hS.trans hR.symm

/-- The composite uses both genuine full operator maps without changing original coefficients. -/
def sequentialOrthogonalOperatorIndexFunctor :
    EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v}
      OrthogonalOperatorIndex.{u, v} :=
  sequentialSymmetricOperatorIndexFunctor.{u, v}.comp PointedCGWH.{u, v}
    symmetricOrthogonalOperatorIndexFunctor.{u, v}

end CategoryTheory.Spectra.SpectrumIndexMaps
