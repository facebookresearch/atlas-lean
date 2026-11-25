/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialExtension
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatFiber

/-!
# Bruhat fibers of the Tits monomial extension

A Bruhat fiber records a special linear matrix together with a lift of its
monomial Bruhat middle in the Tits monomial extension. Projection identities,
coefficient operations and functorial comparisons describe these fibers, and
surjectivity of the extension projection supplies a chosen fiber element above
each matrix.
-/

@[expose] public section

noncomputable section

universe u v w

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsMonomialExtension

namespace MatsumotoTitsBruhatFiber

variable (F : Type u) [Field F] (n : ℕ)

/-- Pullback set `X(F,n)` from Milnor section 12. -/
abbrev X (F : Type u) [Field F] (n : ℕ) : Type u :=
  Matrix.GeneralLinearGroup.BruhatFiber F n (projHom F n)

variable {F n}

abbrev X.fst (x : X F n) : Matrix.SpecialLinearGroup (Fin n) F :=
  Matrix.GeneralLinearGroup.BruhatFiber.fst x

abbrev X.snd (x : X F n) : HMTits F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.snd x

theorem X.prop_eq (x : X F n) :
    bruhatMiddle (X.fst (F := F) (n := n) x) =
      projHom F n (X.snd (F := F) (n := n) x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.prop_eq x

@[ext]
theorem X.ext {x y : X F n} (h1 : x.val.1 = y.val.1)
    (h2 : x.val.2 = y.val.2) : x = y :=
  Matrix.GeneralLinearGroup.BruhatFiber.ext h1 h2

@[simp]
theorem X.mk_fst (s : Matrix.SpecialLinearGroup (Fin n) F) (w : HMTits F n)
    (h : bruhatMiddle s = projHom F n w) :
    X.fst (F := F) (n := n) (⟨(s, w), h⟩ : X F n) = s := rfl

@[simp]
theorem X.mk_snd (s : Matrix.SpecialLinearGroup (Fin n) F) (w : HMTits F n)
    (h : bruhatMiddle s = projHom F n w) :
    X.snd (F := F) (n := n) (⟨(s, w), h⟩ : X F n) = w := rfl

@[simp] theorem X.coe_fst (x : X F n) : (x.val : _).1 = X.fst x := rfl
@[simp] theorem X.coe_snd (x : X F n) : (x.val : _).2 = X.snd x := rfl

section BruhatMiddleInvariance

variable {F : Type u} [Field F] {n : ℕ}

theorem bruhatMiddle_upper_left_mul
    (g : Matrix.SpecialLinearGroup (Fin n) F)
    (u : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (UpperElementary.toSLHom u * g) = bruhatMiddle g :=
  Matrix.GeneralLinearGroup.BruhatFiber.bruhatMiddle_upper_left_mul g u

theorem bruhatMiddle_upper_right_mul
    (g : Matrix.SpecialLinearGroup (Fin n) F)
    (u : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (g * UpperElementary.toSLHom u) = bruhatMiddle g :=
  Matrix.GeneralLinearGroup.BruhatFiber.bruhatMiddle_upper_right_mul g u

theorem bruhatMiddle_upper_mul
    (g : Matrix.SpecialLinearGroup (Fin n) F)
    (u v : upperElementarySubgroup (Fin n) F) :
    bruhatMiddle (UpperElementary.toSLHom u * g *
      UpperElementary.toSLHom v) = bruhatMiddle g :=
  Matrix.GeneralLinearGroup.BruhatFiber.bruhatMiddle_upper_mul g u v

theorem bruhatMiddle_one (F : Type u) [Field F] (n : ℕ) :
    bruhatMiddle (1 : Matrix.SpecialLinearGroup (Fin n) F) = 1 :=
  Matrix.GeneralLinearGroup.BruhatFiber.bruhatMiddle_one F n

end BruhatMiddleInvariance

section UpperActions

variable {F : Type u} [Field F] {n : ℕ}

def leftUpper (u : upperElementarySubgroup (Fin n) F) (x : X F n) : X F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpper u x

def rightUpper (u : upperElementarySubgroup (Fin n) F) (x : X F n) : X F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpper u x

@[simp] theorem leftUpper_fst (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) :
    X.fst (leftUpper (F := F) u x) = UpperElementary.toSLHom u * X.fst x := rfl

@[simp] theorem leftUpper_snd (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) : X.snd (leftUpper (F := F) u x) = X.snd x := rfl

@[simp] theorem rightUpper_fst (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) :
    X.fst (rightUpper (F := F) u x) = X.fst x * UpperElementary.toSLHom u := rfl

@[simp] theorem rightUpper_snd (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) : X.snd (rightUpper (F := F) u x) = X.snd x := rfl

theorem leftUpper_one (x : X F n) :
    leftUpper (1 : upperElementarySubgroup (Fin n) F) x = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpper_one x

theorem rightUpper_one (x : X F n) :
    rightUpper (1 : upperElementarySubgroup (Fin n) F) x = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpper_one x

theorem leftUpper_mul (u v : upperElementarySubgroup (Fin n) F) (x : X F n) :
    leftUpper (u * v) x = leftUpper u (leftUpper v x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpper_mul u v x

theorem rightUpper_mul (u v : upperElementarySubgroup (Fin n) F) (x : X F n) :
    rightUpper (u * v) x = rightUpper v (rightUpper u x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpper_mul u v x

theorem leftUpper_inv (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    leftUpper u⁻¹ (leftUpper u x) = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpper_inv u x

theorem rightUpper_inv (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    rightUpper u⁻¹ (rightUpper u x) = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpper_inv u x

def leftUpperPerm (u : upperElementarySubgroup (Fin n) F) : Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperPerm (p := projHom F n) u

def rightUpperPerm (u : upperElementarySubgroup (Fin n) F) : Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpperPerm (p := projHom F n) u

@[simp] theorem leftUpperPerm_apply (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) : leftUpperPerm (F := F) u x = leftUpper u x := rfl

@[simp] theorem rightUpperPerm_apply (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) : rightUpperPerm (F := F) u x = rightUpper u x := rfl

theorem leftUpperPerm_one :
    leftUpperPerm (F := F) (n := n) (1 : upperElementarySubgroup (Fin n) F) =
      (1 : Equiv.Perm (X F n)) :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperPerm_one

theorem rightUpperPerm_one :
    rightUpperPerm (F := F) (n := n) (1 : upperElementarySubgroup (Fin n) F) =
      (1 : Equiv.Perm (X F n)) :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpperPerm_one

theorem leftUpperPerm_mul (u v : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (F := F) (n := n) (u * v) = leftUpperPerm u * leftUpperPerm v :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperPerm_mul u v

theorem rightUpperPerm_mul (u v : upperElementarySubgroup (Fin n) F) :
    rightUpperPerm (F := F) (n := n) (u * v) = rightUpperPerm v * rightUpperPerm u :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpperPerm_mul u v

theorem leftUpperPerm_inv (u : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (F := F) (n := n) u⁻¹ = (leftUpperPerm (F := F) u)⁻¹ :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperPerm_inv u

theorem rightUpperPerm_inv (u : upperElementarySubgroup (Fin n) F) :
    rightUpperPerm (F := F) (n := n) u⁻¹ = (rightUpperPerm (F := F) u)⁻¹ :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpperPerm_inv u

def leftUpperHom : upperElementarySubgroup (Fin n) F →* Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperHom (p := projHom F n)

def rightUpperHomOp : MulOpposite (upperElementarySubgroup (Fin n) F) →*
    Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.rightUpperHomOp (p := projHom F n)

@[simp] theorem leftUpperHom_apply (u : upperElementarySubgroup (Fin n) F)
    (x : X F n) : leftUpperHom (F := F) (n := n) u x = leftUpper u x := rfl

@[simp] theorem rightUpperHomOp_apply
    (u : MulOpposite (upperElementarySubgroup (Fin n) F)) (x : X F n) :
    rightUpperHomOp (F := F) (n := n) u x = rightUpper u.unop x := rfl

theorem rightUpperHomOp_unop_apply
    (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    rightUpperHomOp (F := F) (MulOpposite.op u) x = rightUpper u x := rfl

theorem left_right_commute (u v : upperElementarySubgroup (Fin n) F) (x : X F n) :
    leftUpper u (rightUpper v x) = rightUpper v (leftUpper u x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.left_right_commute u v x

theorem leftUpperPerm_rightUpperPerm_comm
    (u v : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (F := F) (n := n) u * rightUpperPerm v =
      rightUpperPerm v * leftUpperPerm u :=
  Matrix.GeneralLinearGroup.BruhatFiber.leftUpperPerm_rightUpperPerm_comm u v

end UpperActions

section CentralAction

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def central (c : Multiplicative (MilnorK F 2)) (x : X F n) : X F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.central (inlHom F n)
    (projHom_inl F n) c x

@[simp] theorem central_fst (c : Multiplicative (MilnorK F 2)) (x : X F n) :
    X.fst (central (F := F) c x) = X.fst x := rfl

@[simp] theorem central_snd (c : Multiplicative (MilnorK F 2)) (x : X F n) :
    X.snd (central (F := F) c x) = inlHom F n c * X.snd x := rfl

theorem central_one (x : X F n) :
    central (1 : Multiplicative (MilnorK F 2)) x = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.central_one
    (inlHom F n) (projHom_inl F n) x

theorem central_mul (c₁ c₂ : Multiplicative (MilnorK F 2)) (x : X F n) :
    central (c₁ * c₂) x = central c₁ (central c₂ x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.central_mul
    (inlHom F n) (projHom_inl F n) c₁ c₂ x

theorem central_inv (c : Multiplicative (MilnorK F 2)) (x : X F n) :
    central c⁻¹ (central c x) = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.central_inv
    (inlHom F n) (projHom_inl F n) c x

noncomputable def centralPerm (c : Multiplicative (MilnorK F 2)) : Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm (inlHom F n)
    (projHom_inl F n) c

@[simp] theorem centralPerm_apply (c : Multiplicative (MilnorK F 2))
    (x : X F n) : centralPerm (F := F) c x = central c x := rfl

theorem centralPerm_one :
    centralPerm (F := F) (n := n) (1 : Multiplicative (MilnorK F 2)) =
      (1 : Equiv.Perm (X F n)) :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm_one
    (inlHom F n) (projHom_inl F n)

theorem centralPerm_mul (c₁ c₂ : Multiplicative (MilnorK F 2)) :
    centralPerm (F := F) (n := n) (c₁ * c₂) =
      centralPerm (F := F) c₁ * centralPerm (F := F) c₂ :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm_mul
    (inlHom F n) (projHom_inl F n) c₁ c₂

theorem centralPerm_inv (c : Multiplicative (MilnorK F 2)) :
    centralPerm (F := F) (n := n) c⁻¹ = (centralPerm (F := F) c)⁻¹ :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm_inv
    (inlHom F n) (projHom_inl F n) c

noncomputable def centralHom : Multiplicative (MilnorK F 2) →* Equiv.Perm (X F n) :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralHom (inlHom F n)
    (projHom_inl F n)

@[simp] theorem centralHom_apply (c : Multiplicative (MilnorK F 2))
    (x : X F n) : centralHom (F := F) (n := n) c x = central c x := rfl

theorem inlHom_injective (F : Type u) [Field F] (n : ℕ) :
    Function.Injective (inlHom F n) := (titsMonomialExtension F n).inl_injective

noncomputable def X_one (F : Type u) [Field F] (n : ℕ) : X F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.basepoint F n (projHom F n)

@[simp] theorem X_one_fst (F : Type u) [Field F] (n : ℕ) :
    X.fst (X_one F n) = 1 := rfl

@[simp] theorem X_one_snd (F : Type u) [Field F] (n : ℕ) :
    X.snd (X_one F n) = 1 := rfl

theorem centralHom_injective :
    Function.Injective (centralHom (F := F) (n := n)) :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralHom_injective
    (inlHom F n) (projHom_inl F n) (inlHom_injective F n)

theorem central_left_commute (c : Multiplicative (MilnorK F 2))
    (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    central c (leftUpper u x) = leftUpper u (central c x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.central_left_commute
    (inlHom F n) (projHom_inl F n) c u x

theorem central_right_commute (c : Multiplicative (MilnorK F 2))
    (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    central c (rightUpper u x) = rightUpper u (central c x) :=
  Matrix.GeneralLinearGroup.BruhatFiber.central_right_commute
    (inlHom F n) (projHom_inl F n) c u x

theorem centralPerm_leftUpperPerm_comm (c : Multiplicative (MilnorK F 2))
    (u : upperElementarySubgroup (Fin n) F) :
    centralPerm (F := F) c * leftUpperPerm u =
      leftUpperPerm u * centralPerm c :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm_leftUpperPerm_comm
    (inlHom F n) (projHom_inl F n) c u

theorem centralPerm_rightUpperPerm_comm (c : Multiplicative (MilnorK F 2))
    (u : upperElementarySubgroup (Fin n) F) :
    centralPerm (F := F) c * rightUpperPerm u =
      rightUpperPerm u * centralPerm c :=
  Matrix.GeneralLinearGroup.BruhatFiber.centralPerm_rightUpperPerm_comm
    (inlHom F n) (projHom_inl F n) c u

end CentralAction

section FieldMap

variable {F : Type u} [Field F] {K : Type v} [Field K]
  {L : Type w} [Field L] {n : ℕ}

noncomputable def XMap (f : F →+* K) (x : X F n) : X K n :=
  ⟨(Matrix.SpecialLinearGroup.map f x.val.1,
    HMTitsMap (F := F) (K := K) f n x.val.2),
    by
      let φ : Matrix.GeneralLinearGroup.BruhatFiber.MapData F K n
          (projHom F n) (projHom K n) :=
        { mapSL := Matrix.SpecialLinearGroup.map f
          mapMiddle := MMap (F := F) (K := K) f n
          mapFiber := HMTitsMap (F := F) (K := K) f n
          commSL s := by
            simpa [MMap] using
              (bruhatMiddle_map (F := F) (K := K) (f := f) (g := s))
          commFiber a := HMTitsMap_snd (F := F) (K := K) f n a }
      exact (Matrix.GeneralLinearGroup.BruhatFiber.map φ x).2⟩

@[simp] theorem XMap_fst (f : F →+* K) (x : X F n) :
    X.fst (XMap (F := F) (K := K) f x) =
      Matrix.SpecialLinearGroup.map f (X.fst x) := rfl

@[simp] theorem XMap_snd (f : F →+* K) (x : X F n) :
    X.snd (XMap (F := F) (K := K) f x) =
      HMTitsMap (F := F) (K := K) f n (X.snd x) := rfl

theorem XMap_wellDefined (f : F →+* K) (x : X F n) :
    bruhatMiddle (Matrix.SpecialLinearGroup.map f x.val.1) =
      projHom K n (HMTitsMap (F := F) (K := K) f n x.val.2) :=
  (XMap (F := F) (K := K) f x).2

private theorem SL_map_id_aux (s : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup.map (RingHom.id F) s = s := by
  apply Subtype.ext
  rfl

private theorem SL_map_comp_aux (f : F →+* K) (g : K →+* L)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup.map (g.comp f) s =
      Matrix.SpecialLinearGroup.map g (Matrix.SpecialLinearGroup.map f s) := by
  apply Subtype.ext
  rfl

theorem XMap_id (x : X F n) :
    XMap (F := F) (K := F) (RingHom.id F) x = x := by
  apply X.ext
  · exact SL_map_id_aux x.val.1
  · exact DFunLike.congr_fun (HMTitsMap_id (F := F) n) x.val.2

theorem XMap_comp (f : F →+* K) (g : K →+* L) (x : X F n) :
    XMap (F := F) (K := L) (g.comp f) x =
      XMap (K := L) g (XMap (F := F) f x) := by
  apply X.ext
  · exact SL_map_comp_aux f g x.val.1
  · exact DFunLike.congr_fun
      (HMTitsMap_comp (F := F) (K := K) (L := L) f g n) x.val.2

theorem XMap_leftUpper_naturality (f : F →+* K)
    (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    XMap (F := F) f (leftUpper u x) =
      leftUpper (UpperElementary.mapRingHom f u) (XMap (F := F) f x) :=
  by
    apply X.ext
    · simp only [XMap, leftUpper]
      calc Matrix.SpecialLinearGroup.map f
            (UpperElementary.toSLHom u * X.fst x) =
          Matrix.SpecialLinearGroup.map f (UpperElementary.toSLHom u) *
            Matrix.SpecialLinearGroup.map f (X.fst x) := by rw [map_mul]
        _ = UpperElementary.toSLHom (UpperElementary.mapRingHom f u) *
            Matrix.SpecialLinearGroup.map f (X.fst x) := by
              rw [UpperElementary.toSLHom_mapRingHom]
    · rfl

theorem XMap_rightUpper_naturality (f : F →+* K)
    (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    XMap (F := F) f (rightUpper u x) =
      rightUpper (UpperElementary.mapRingHom f u) (XMap (F := F) f x) :=
  by
    apply X.ext
    · simp only [XMap, rightUpper]
      calc Matrix.SpecialLinearGroup.map f
            (X.fst x * UpperElementary.toSLHom u) =
          Matrix.SpecialLinearGroup.map f (X.fst x) *
            Matrix.SpecialLinearGroup.map f (UpperElementary.toSLHom u) := by rw [map_mul]
        _ = Matrix.SpecialLinearGroup.map f (X.fst x) *
            UpperElementary.toSLHom (UpperElementary.mapRingHom f u) := by
              rw [UpperElementary.toSLHom_mapRingHom]
    · rfl

theorem XMap_central_naturality (f : F →+* K)
    (c : Multiplicative (MilnorK F 2)) (x : X F n) :
    XMap (F := F) f (central c x) =
      central (MilnorK.mapMultiplicative f 2 c) (XMap (F := F) f x) := by
  apply X.ext
  · rfl
  · simp only [XMap, central]
    have hInl : HMTitsMap (F := F) (K := K) f n (inlHom F n c) =
        inlHom K n (MilnorK.mapMultiplicative f 2 c) := by
      exact DFunLike.congr_fun (inlHom_naturality (F := F) (K := K) f n) c
    calc HMTitsMap (F := F) (K := K) f n (inlHom F n c * X.snd x) =
        HMTitsMap (F := F) (K := K) f n (inlHom F n c) *
          HMTitsMap (F := F) (K := K) f n (X.snd x) := by rw [map_mul]
      _ = inlHom K n (MilnorK.mapMultiplicative f 2 c) *
          HMTitsMap (F := F) (K := K) f n (X.snd x) := by rw [hInl]

end FieldMap

section CanonicalLift

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def chooseLiftHMTits (F : Type u) [Field F] (n : ℕ)
    (x : M F n) : HMTits F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.chooseLift
    (titsMonomialExtension F n).rightHom_surjective x

theorem chooseLiftHMTits_spec (F : Type u) [Field F] (n : ℕ)
    (x : M F n) : projHom F n (chooseLiftHMTits F n x) = x :=
  Matrix.GeneralLinearGroup.BruhatFiber.chooseLift_spec
    (titsMonomialExtension F n).rightHom_surjective x

noncomputable def mkX (s : Matrix.SpecialLinearGroup (Fin n) F) : X F n :=
  Matrix.GeneralLinearGroup.BruhatFiber.mk
    (titsMonomialExtension F n).rightHom_surjective s

@[simp] theorem mkX_fst (s : Matrix.SpecialLinearGroup (Fin n) F) :
    X.fst (mkX (F := F) s) = s := rfl

theorem mkX_snd_proj (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (X.snd (mkX (F := F) s)) = bruhatMiddle s :=
  chooseLiftHMTits_spec F n (bruhatMiddle s)

theorem mkX_prop (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (X.fst (mkX (F := F) s)) =
      projHom F n (X.snd (mkX (F := F) s)) :=
  (mkX (F := F) s).2

end CanonicalLift

end MatsumotoTitsBruhatFiber

end
