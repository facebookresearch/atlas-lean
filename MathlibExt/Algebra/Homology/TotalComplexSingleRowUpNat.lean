/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexUpNat
public import Mathlib.Algebra.Homology.Single

/-!
# Totals of cochain bicomplexes concentrated in outer degree zero

Let C be preadditive with a zero object and finite coproducts. Put a nonnegative cochain complex
A in outer degree zero of a bicomplex B, with every other outer row zero. The inclusion of the
(0,n) summand and the projection onto it are inverse cochain maps A ≅ Tot(B). These maps and the
resulting total isomorphism are natural in A.
-/

/-
Authorship of the adapted portions: @junekim623, Muse.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open _root_.CategoryTheory CategoryTheory Category Limits

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object and A a nonnegative cochain complex. The bicomplex
singleRowUpNat A has row A in outer degree zero, zero rows in positive outer degrees, and zero
outer differentials. -/
noncomputable abbrev singleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((HomologicalComplex.single _ _ 0).obj A)

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative cochain complex
A, let B = singleRowUpNat A. The cochain map A → Tot(B) has degree-n component the canonical
identification A_n → B_{0,n} followed by the summand inclusion ι_{0,n}. -/
noncomputable def fromSingleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    A ⟶ (singleRowUpNat A).total (ComplexShape.up ℕ) where
  f n :=
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫
      (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)
  comm' i j hij := by
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
    have hA₁ : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp)) ≫
        (singleRowUpNat A).D₁ (ComplexShape.up ℕ) i j) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp) ≫
            (singleRowUpNat A).D₁ (ComplexShape.up ℕ) i j)) :=
      Category.assoc _ _ _
    have hA₂ : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp)) ≫
        (singleRowUpNat A).D₂ (ComplexShape.up ℕ) i j) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp) ≫
            (singleRowUpNat A).D₂ (ComplexShape.up ℕ) i j)) :=
      Category.assoc _ _ _
    have hI₁ : (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp) ≫
        (singleRowUpNat A).D₁ (ComplexShape.up ℕ) i j =
        (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 i j :=
      (singleRowUpNat A).ι_D₁ (ComplexShape.up ℕ) i j 0 i (by simp)
    have hI₂ : (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp) ≫
        (singleRowUpNat A).D₂ (ComplexShape.up ℕ) i j =
        (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j :=
      (singleRowUpNat A).ι_D₂ (ComplexShape.up ℕ) i j 0 i (by simp)
    have hC₁ : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp)) ≫
        (singleRowUpNat A).D₁ (ComplexShape.up ℕ) i j) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 i j) :=
      Eq.trans hA₁ (congrArg
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫ ·) hI₁)
    have hC₂ : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 i i (by simp)) ≫
        (singleRowUpNat A).D₂ (ComplexShape.up ℕ) i j) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j) :=
      Eq.trans hA₂ (congrArg
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫ ·) hI₂)
    rw [hC₁, hC₂]
    have hKd : (singleRowUpNat A).d 0 ((ComplexShape.up ℕ).next 0) = 0 :=
      HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 A 0
        ((ComplexShape.up ℕ).next 0)
    have hKdf : (((singleRowUpNat A).d 0 ((ComplexShape.up ℕ).next 0)).f i) = 0 := by
      rw [hKd, HomologicalComplex.zero_f]
    have hD₁ : (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 i j = 0 := by
      simp only [HomologicalComplex₂.d₁, hKdf]
      exact (congrArg _ zero_comp).trans (smul_zero _)
    have hH₁ : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 i j) = 0 :=
      Eq.trans (congrArg
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫ ·) hD₁)
        (comp_zero)
    rw [hH₁]
    have hAdd : (0 : _) +
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j) :=
      zero_add _
    rw [hAdd]
    have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (ComplexShape.up ℕ) (0, i) = 1 := by
      simp
    have hD₂ : (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j =
        ((singleRowUpNat A).X 0).d i j ≫
          (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp) := by
      rw [(singleRowUpNat A).d₂_eq (ComplexShape.up ℕ) 0 hij j (by simp),
        hε₂, one_smul]
    have hComm := HomologicalComplex.Hom.comm
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv i j
    have hComm' : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        ((singleRowUpNat A).X 0).d i j) =
        (A.d i j ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f j) :=
      hComm
    have hAssocB : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (((singleRowUpNat A).X 0).d i j ≫
          (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp))) =
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
          ((singleRowUpNat A).X 0).d i j) ≫
          (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp)) :=
      (Category.assoc _ _ _).symm
    have hB : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (((singleRowUpNat A).X 0).d i j ≫
          (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp))) =
        ((A.d i j ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f j) ≫
          (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp)) :=
      Eq.trans hAssocB (congrArg (· ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp)) hComm')
    have hFin : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫
        (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 i j)) =
        (A.d i j ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f j ≫
            (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j (by simp)) :=
      Eq.trans (congrArg
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f i ≫ ·) hD₂)
        (Eq.trans hB (Category.assoc _ _ _))
    rw [hFin]

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative cochain complex
A, let B = singleRowUpNat A. The cochain map Tot(B) → A restricts on bidegree (0,n) to the
canonical identification B_{0,n} → A_n and sends all summands with positive outer degree to
zero. -/
noncomputable def toSingleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    (singleRowUpNat A).total (ComplexShape.up ℕ) ⟶ A where
  f n :=
    (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
      if h : i₁ = 0 then
        (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
          (A.XIsoOfEq (by subst h; simpa using hi)).hom
      else 0)
  comm' i j hij := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hp : p = 0
    · subst hp
      have hq : q = i := by simpa using hpq
      subst hq
      have hL_assoc :
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            ((singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0) ≫ A.d q j)) =
          (((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0)) ≫ A.d q j) :=
        (Category.assoc _ _ _).symm
      have hL_desc :
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0)) =
          (if h : (0 : ℕ) = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f q) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f q) ≫
              (A.XIsoOfEq (by simp)).hom
           else 0) :=
        (singleRowUpNat A).ι_totalDesc _ 0 q hpq
      have hR_assoc :
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            (((singleRowUpNat A).total (ComplexShape.up ℕ)).d q j ≫
              (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
                if h : i₁ = 0 then
                  (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                    (A.XIsoOfEq (by subst h; simpa using hi)).hom
                else 0))) =
          (((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            ((singleRowUpNat A).total (ComplexShape.up ℕ)).d q j) ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0)) :=
        (Category.assoc _ _ _).symm
      have hR_comp :
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            ((singleRowUpNat A).total (ComplexShape.up ℕ)).d q j) =
          (((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            (singleRowUpNat A).D₁ (ComplexShape.up ℕ) q j) +
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
            (singleRowUpNat A).D₂ (ComplexShape.up ℕ) q j)) := by
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
      have hI₁ : (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
          (singleRowUpNat A).D₁ (ComplexShape.up ℕ) q j =
          (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 q j :=
        (singleRowUpNat A).ι_D₁ (ComplexShape.up ℕ) q j 0 q hpq
      have hI₂ : (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q hpq ≫
          (singleRowUpNat A).D₂ (ComplexShape.up ℕ) q j =
          (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 q j :=
        (singleRowUpNat A).ι_D₂ (ComplexShape.up ℕ) q j 0 q hpq
      have hKd : (singleRowUpNat A).d 0 ((ComplexShape.up ℕ).next 0) = 0 :=
        HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 A 0
          ((ComplexShape.up ℕ).next 0)
      have hKdf : (((singleRowUpNat A).d 0 ((ComplexShape.up ℕ).next 0)).f q) = 0 := by
        rw [hKd, HomologicalComplex.zero_f]
      have hD₁ : (singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 q j = 0 := by
        simp only [HomologicalComplex₂.d₁, hKdf]
        exact (congrArg _ zero_comp).trans (smul_zero _)
      have hJhp : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (0, j) = j := by simp
      have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (ComplexShape.up ℕ) (0, q) = 1 := by
        simp
      have hD₂ : (singleRowUpNat A).d₂ (ComplexShape.up ℕ) 0 q j =
          ((singleRowUpNat A).X 0).d q j ≫
            (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j hJhp := by
        rw [(singleRowUpNat A).d₂_eq (ComplexShape.up ℕ) 0 hij j hJhp,
          hε₂, one_smul]
      let E := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A
      have hE_eq : E = HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A :=
        rfl
      have hL_sel :
          (if h : (0 : ℕ) = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f q) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f q) ≫
              (A.XIsoOfEq (by simp)).hom
           else 0) = E.hom.f q := by
        rw [hE_eq]
        simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
          HomologicalComplex.id_f, Category.id_comp]
        exact Category.comp_id _
      have hJ_desc :
          ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j hJhp ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0)) =
          (if h : (0 : ℕ) = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f j) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f j) ≫
              (A.XIsoOfEq (by simp)).hom
           else 0) :=
        (singleRowUpNat A).ι_totalDesc _ 0 j hJhp
      have hJ_sel :
          (if h : (0 : ℕ) = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f j) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f j) ≫
              (A.XIsoOfEq (by simp)).hom
           else 0) = E.hom.f j := by
        rw [hE_eq]
        simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
          HomologicalComplex.id_f, Category.id_comp]
        exact Category.comp_id _
      have hZero₁ :
          ((singleRowUpNat A).d₁ (ComplexShape.up ℕ) 0 q j ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0)) = 0 := by
        rw [hD₁, zero_comp]
      have hD₂_assoc :
          (((singleRowUpNat A).X 0).d q j ≫
              (singleRowUpNat A).ιTotal
                (ComplexShape.up ℕ) 0 j j hJhp) ≫
            (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
              if h : i₁ = 0 then
                (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                  (A.XIsoOfEq (by subst h; simpa using hi)).hom
              else 0) =
          ((singleRowUpNat A).X 0).d q j ≫
            ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 j j hJhp ≫
              (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
                if h : i₁ = 0 then
                  (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                    (A.XIsoOfEq (by subst h; simpa using hi)).hom
                else 0)) :=
        Category.assoc _ _ _
      rw [hL_assoc, hL_desc, hL_sel, hR_assoc, hR_comp, hI₁, hI₂]
      rw [Preadditive.add_comp, hZero₁, zero_add, hD₂]
      rw [hD₂_assoc, hJ_desc, hJ_sel]
      exact HomologicalComplex.Hom.comm E.hom q j
    · have hZ : IsZero (((singleRowUpNat A).X p).X q) :=
        Functor.map_isZero (HomologicalComplex.eval _ _ q)
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp)
      exact IsZero.eq_of_src hZ _ _

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative cochain complex
A and q ∈ ℕ, the inclusion ι_{0,q} into Tot(singleRowUpNat A) followed by the degree-q
projection to A is the degree-q component of the canonical isomorphism from the row-zero single
complex to A. -/
@[reassoc]
theorem ιTotal_comp_toSingleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) (q : ℕ) :
    (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 q q
        (Nat.zero_add q) ≫
      (toSingleRowUpNat A).f q =
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℕ) 0 A).hom.f q := by
  unfold toSingleRowUpNat
  dsimp only
  rw [HomologicalComplex₂.ι_totalDesc]
  simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, HomologicalComplex.id_f, Category.id_comp]
  exact Category.comp_id _

theorem fromSingleRowUpNat_toSingleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    fromSingleRowUpNat A ≫ toSingleRowUpNat A = 𝟙 A := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hfrom : (fromSingleRowUpNat A).f n =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) :=
    rfl
  have hto : (toSingleRowUpNat A).f n =
      (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
        if h : i₁ = 0 then
          (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
            (A.XIsoOfEq (by subst h; simpa using hi)).hom
        else 0) :=
    rfl
  have hassoc : ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) ≫
      (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
        if h : i₁ = 0 then
          (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
            (A.XIsoOfEq (by subst h; simpa using hi)).hom
        else 0)) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫
        ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
          (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0))) :=
    Category.assoc _ _ _
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, hfrom, hto, hassoc]
  have hdesc : ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
      (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
        if h : i₁ = 0 then
          (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
            (A.XIsoOfEq (by subst h; simpa using hi)).hom
        else 0)) =
      (if h : (0 : ℕ) = 0 then
        (((singleRowUpNat A).XIsoOfEq h).hom.f n) ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n) ≫
          (A.XIsoOfEq (by simp)).hom
      else 0) :=
    HomologicalComplex₂.ι_totalDesc _ _ _ _ _
  have hsel : (if h : (0 : ℕ) = 0 then
        (((singleRowUpNat A).XIsoOfEq h).hom.f n) ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n) ≫
          (A.XIsoOfEq (by simp)).hom
      else 0) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n := by
    rw [dite_eq_left rfl]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, HomologicalComplex.id_f,
      Category.id_comp]
    exact Category.comp_id _
  have hinv : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n =
      𝟙 (A.X n) := by
    have hE := Iso.inv_hom_id
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A)
    have hEf := congrArg (fun φ => φ.f n) hE
    exact hEf
  have hmain : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫
      ((singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
        (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
          if h : i₁ = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
              (A.XIsoOfEq (by subst h; simpa using hi)).hom
          else 0))) = 𝟙 (A.X n) :=
    (congrArg (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫ ·)
      hdesc).trans
      ((congrArg (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).inv.f n) ≫ ·)
        hsel).trans hinv)
  exact hmain

theorem toSingleRowUpNat_fromSingleRowUpNat
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    toSingleRowUpNat A ≫ fromSingleRowUpNat A =
      𝟙 ((singleRowUpNat A).total (ComplexShape.up ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst hp
    have hq : n = q := by simpa using hpq.symm
    subst hq
    let E := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A
    have hE_eq : E = HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℕ) (0 : ℕ) A := rfl
    have hto : (toSingleRowUpNat A).f n =
        (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
          if h : i₁ = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
              (A.XIsoOfEq (by subst h; simpa using hi)).hom
          else 0) :=
      rfl
    have hfrom : (fromSingleRowUpNat A).f n =
        E.inv.f n ≫
          (singleRowUpNat A).ιTotal
            (ComplexShape.up ℕ) 0 n n hpq :=
      rfl
    have hdesc : ((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0)) =
        (if h : (0 : ℕ) = 0 then
          (((singleRowUpNat A).XIsoOfEq h).hom.f n) ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n) ≫
            (A.XIsoOfEq (by simp)).hom
        else 0) :=
      (singleRowUpNat A).ι_totalDesc _ 0 n hpq
    have hsel : (if h : (0 : ℕ) = 0 then
            (((singleRowUpNat A).XIsoOfEq h).hom.f n) ≫
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f n) ≫
              (A.XIsoOfEq (by simp)).hom
          else 0) = E.hom.f n := by
      rw [hE_eq]
      simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        HomologicalComplex.id_f, Category.id_comp]
      exact Category.comp_id _
    have hIT : ((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0)) = E.hom.f n :=
      Eq.trans hdesc hsel
    have hEiso : E.hom ≫ E.inv = 𝟙 _ := Iso.hom_inv_id E
    have hEcomp0 := congrArg (fun φ => φ.f n) hEiso
    have hEf : E.hom.f n ≫ E.inv.f n = 𝟙 _ := by
      simpa using hEcomp0
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, hto, hfrom]
    have hassoc1 : ((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          ((singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0) ≫
          (E.inv.f n ≫ (singleRowUpNat A).ιTotal
            (ComplexShape.up ℕ) 0 n n hpq))) =
        (((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0)) ≫
          (E.inv.f n ≫ (singleRowUpNat A).ιTotal
            (ComplexShape.up ℕ) 0 n n hpq)) :=
      (Category.assoc _ _ _).symm
    have hstep : ((((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          (singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0)) ≫
          (E.inv.f n ≫ (singleRowUpNat A).ιTotal
            (ComplexShape.up ℕ) 0 n n hpq))) =
        (E.hom.f n ≫ (E.inv.f n ≫ (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq)) :=
      congrArg (· ≫ (E.inv.f n ≫ (singleRowUpNat A).ιTotal
        (ComplexShape.up ℕ) 0 n n hpq)) hIT
    have hassoc2 : (E.hom.f n ≫ (E.inv.f n ≫
        (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq)) =
        ((E.hom.f n ≫ E.inv.f n) ≫ (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq) :=
      (Category.assoc _ _ _).symm
    have hstep2 : ((E.hom.f n ≫ E.inv.f n) ≫
        (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq) =
        (𝟙 _ ≫ (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq) :=
      congrArg (· ≫ (singleRowUpNat A).ιTotal
        (ComplexShape.up ℕ) 0 n n hpq) hEf
    have hstep3 : (𝟙 _ ≫ (singleRowUpNat A).ιTotal
        (ComplexShape.up ℕ) 0 n n hpq) =
        (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq :=
      Category.id_comp _
    have hL : ((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          ((singleRowUpNat A).totalDesc (fun i₁ i₂ hi =>
            if h : i₁ = 0 then
              (((singleRowUpNat A).XIsoOfEq h).hom.f i₂) ≫
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) (0 : ℕ) A).hom.f i₂) ≫
                (A.XIsoOfEq (by subst h; simpa using hi)).hom
            else 0) ≫
          (E.inv.f n ≫ (singleRowUpNat A).ιTotal
            (ComplexShape.up ℕ) 0 n n hpq))) =
        (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq :=
      Eq.trans hassoc1 (Eq.trans hstep (Eq.trans hassoc2
        (Eq.trans hstep2 hstep3)))
    have hR : ((singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq ≫
          𝟙 (((singleRowUpNat A).total
            (ComplexShape.up ℕ)).X n)) =
        (singleRowUpNat A).ιTotal
          (ComplexShape.up ℕ) 0 n n hpq :=
      Category.comp_id _
    exact Eq.trans hL hR.symm
  · have hZ : Limits.IsZero ((((singleRowUpNat A).X p).X q)) :=
      Functor.map_isZero (HomologicalComplex.eval _ _ q)
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp)
    exact Limits.IsZero.eq_of_src hZ _ _

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative cochain complex
A, Tot(singleRowUpNat A) ≅ A. Its forward map is toSingleRowUpNat A and its inverse is
fromSingleRowUpNat A. -/
noncomputable def singleRowUpNatTotalIso
    (A : HomologicalComplex C (ComplexShape.up ℕ)) :
    (singleRowUpNat A).total (ComplexShape.up ℕ) ≅ A where
  hom := toSingleRowUpNat A
  inv := fromSingleRowUpNat A
  hom_inv_id := toSingleRowUpNat_fromSingleRowUpNat A
  inv_hom_id := fromSingleRowUpNat_toSingleRowUpNat A

/-- Let C be preadditive with a zero object. The functor singleRowFunctorUpNat places a nonnegative
cochain complex A in outer degree zero of a bicomplex, with all other rows zero, and sends a
cochain map to its degree-zero outer component. -/
noncomputable abbrev singleRowFunctorUpNat :
    HomologicalComplex C (ComplexShape.up ℕ) ⥤
      HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex.single
    (HomologicalComplex C (ComplexShape.up ℕ)) (ComplexShape.up ℕ) 0

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive with a zero object and finite coproducts. For a map f : A → B of
nonnegative cochain complexes, let e_A and e_B be the row-zero total isomorphisms. Then
Tot(singleRowFunctorUpNat(f)) ≫ e_B.hom = e_A.hom ≫ f. -/
theorem singleRowUpNatTotalIso_hom_naturality
    {A B : HomologicalComplex C (ComplexShape.up ℕ)} (f : A ⟶ B) :
    HomologicalComplex₂.total.map (singleRowFunctorUpNat.map f)
          (ComplexShape.up ℕ) ≫
        (singleRowUpNatTotalIso B).hom =
      (singleRowUpNatTotalIso A).hom ≫ f := by
  dsimp only [singleRowFunctorUpNat, singleRowUpNatTotalIso]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  cases p with
  | zero =>
      have hq : q = n := by simpa using h
      subst q
      simp only [HomologicalComplex.comp_f,
        HomologicalComplex₂.ιTotal_map_assoc]
      change (((HomologicalComplex.single
          (HomologicalComplex C (ComplexShape.up ℕ))
          (ComplexShape.up ℕ) 0).map f).f 0).f n ≫
            ((singleRowUpNat B).ιTotal (ComplexShape.up ℕ) 0 n n
                (Nat.zero_add n) ≫ (toSingleRowUpNat B).f n) =
        (singleRowUpNat A).ιTotal (ComplexShape.up ℕ) 0 n n
            (Nat.zero_add n) ≫ ((toSingleRowUpNat A).f n ≫ f.f n)
      rw [ιTotal_comp_toSingleRowUpNat,
        ιTotal_comp_toSingleRowUpNat_assoc]
      rw [HomologicalComplex.single_map_f_self]
      simp only [HomologicalComplex.comp_f]
      have hinv := congrArg (fun φ ↦ φ.f n)
        (Iso.inv_hom_id
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 B))
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
        at hinv
      rw [← Category.assoc
          ((HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 A).hom.f n)
          (f.f n)
          ((HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 B).inv.f n)]
      rw [Category.assoc
          ((HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 A).hom.f n ≫ f.f n)
          ((HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 B).inv.f n)
          ((HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 B).hom.f n),
        hinv, Category.comp_id]
  | succ p =>
      have hZ : IsZero (((singleRowUpNat A).X (p + 1)).X q) :=
        Functor.map_isZero (HomologicalComplex.eval _ _ q)
          (HomologicalComplex.isZero_single_obj_X _ _ _ _
            (Nat.succ_ne_zero p))
      exact hZ.eq_of_src _ _

/-- Let C be preadditive with a zero object and finite coproducts. The composite functor placing a
nonnegative cochain complex in outer degree zero and then totalizing is naturally isomorphic to
the identity. Its component at A is singleRowUpNatTotalIso A. -/
noncomputable def singleRowTotalNatIsoUpNat :
    singleRowFunctorUpNat (C := C) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (ComplexShape.up ℕ) ≅
      𝟭 (HomologicalComplex C (ComplexShape.up ℕ)) :=
  NatIso.ofComponents singleRowUpNatTotalIso
    singleRowUpNatTotalIso_hom_naturality

end HomologicalComplex₂

end
