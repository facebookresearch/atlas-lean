/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.TwistingHomComplexMap
import MathlibExt.Algebra.Homology.TwistingHomComplexModule
import MathlibExt.Algebra.Homology.TwistingMaurerCartanReduced
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.NormNum

/-!
# Reduced scalar cochains and twisting Hom transport

Native monoid limits and their opposite construct a two-point coalgebra and
a product coefficient algebra. A reduced cochain has the nonzero coordinate 2;
swapping the coefficient factors moves that coordinate and preserves its sign.
The Hom complex uses the zero Maurer–Cartan cochain, whose equation is proved.

A second integer complex has one nonzero differential, multiplication by 2.
Its nonzero degree-minus-one Hom cochain tests the positive source term in
the odd Hom differential used by the twisting construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open CochainComplex Opposite

namespace MathlibExtTest.ReducedTwistingHom

private def unitProduct (D : Type*) [Category D] [MonoidalCategory D]
    [HasBinaryProduct (𝟙_ D) (𝟙_ D)] :
    LimitCone (pair (Mon.mk (𝟙_ D)) (Mon.mk (𝟙_ D))) :=
  let F := pair (Mon.mk (𝟙_ D)) (Mon.mk (𝟙_ D))
  let c₀ : BinaryFan (𝟙_ D) (𝟙_ D) :=
    BinaryFan.mk (prod.fst : (𝟙_ D) ⨯ (𝟙_ D) ⟶ 𝟙_ D) prod.snd
  let e := pairComp (Mon.mk (𝟙_ D)) (Mon.mk (𝟙_ D)) (Mon.forget D)
  let c : Cone (F ⋙ Mon.forget D) := (Cone.postcompose e.inv).obj c₀
  let hc : IsLimit c :=
    (IsLimit.postcomposeInvEquiv e c₀).symm (prodIsProd (𝟙_ D) (𝟙_ D))
  ⟨Mon.limitCone F c hc, Mon.limitConeIsLimit F c hc⟩

private abbrev M := ModuleCat.{0} ℤ

local instance : ∀ (X Y : GradedObject ℤ M), GradedObject.HasTensor X Y := by
  intro X Y
  dsimp only [GradedObject.HasTensor, GradedObject.HasMap]
  intro i
  infer_instance

local instance : ∀ (X : M), PreservesColimit (Functor.empty.{0} M)
    ((curriedTensor M).obj X) := by
  intros
  infer_instance

local instance : ∀ (X : M), PreservesColimit (Functor.empty.{0} M)
    ((curriedTensor M).flip.obj X) := by
  intros
  infer_instance

local instance : ∀ (X Y Z : GradedObject ℤ M), GradedObject.HasGoodTensor₁₂Tensor X Y Z := by
  intros
  infer_instance

local instance : ∀ (X Y Z : GradedObject ℤ M), GradedObject.HasGoodTensorTensor₂₃ X Y Z := by
  intros
  infer_instance

local instance : ∀ (W X Y Z : GradedObject ℤ M),
    GradedObject.HasTensor₄ObjExt W X Y Z := by
  intros
  infer_instance

private abbrev H := CochainComplex M ℤ
private abbrev I : H := 𝟙_ H
private abbrev algebra : Mon H := (unitProduct H).cone.pt
private abbrev oppositeAlgebra : Mon Hᵒᵖ := (unitProduct Hᵒᵖ).cone.pt
private abbrev A : H := algebra.X
private abbrev C : H := unop oppositeAlgebra.X

private instance : MonObj A := algebra.mon
private instance : ComonObj C := (Comon.MonOpOpToComonObj oppositeAlgebra).comon

private abbrev p₀Mon : algebra ⟶ Mon.mk I :=
  (unitProduct H).cone.π.app ⟨WalkingPair.left⟩
private abbrev p₁Mon : algebra ⟶ Mon.mk I :=
  (unitProduct H).cone.π.app ⟨WalkingPair.right⟩
private abbrev p₀ : A ⟶ I := p₀Mon.hom
private abbrev p₁ : A ⟶ I := p₁Mon.hom

private instance : IsMonHom p₀ := p₀Mon.isMonHom_hom
private instance : IsMonHom p₁ := p₁Mon.isMonHom_hom

private abbrev ι₀ : I ⟶ C :=
  ((unitProduct Hᵒᵖ).cone.π.app ⟨WalkingPair.left⟩).hom.unop
private abbrev ι₁ : I ⟶ C :=
  ((unitProduct Hᵒᵖ).cone.π.app ⟨WalkingPair.right⟩).hom.unop

private def secondScalar : I ⟶ A := prod.lift 0 ((2 : ℤ) • 𝟙 I)
private def scalarMap : C ⟶ A := (prod.lift (0 : I ⟶ A).op secondScalar.op).unop
private abbrev scalarCochain : HomComplex.Cochain C A 0 :=
  HomComplex.Cochain.ofHom scalarMap

private lemma first_zero : ι₀ ≫ scalarMap = 0 := by
  change ((prod.lift (0 : I ⟶ A).op secondScalar.op) ≫ prod.fst).unop = 0
  exact congrArg (fun f : op A ⟶ op I => f.unop)
    (prod.lift_fst (0 : I ⟶ A).op secondScalar.op)

private lemma scalar_first_zero : scalarMap ≫ p₀ = 0 := by
  apply Quiver.Hom.op_inj
  rw [op_comp]
  dsimp only [scalarMap]
  apply prod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, prod.lift_snd, zero_comp]
    change (secondScalar ≫ p₀).op = 0
    simp [secondScalar]

private lemma second_coordinate : ι₁ ≫ scalarMap ≫ p₁ = (2 : ℤ) • 𝟙 I := by
  have hs : ι₁ ≫ scalarMap = secondScalar := by
    change ((prod.lift (0 : I ⟶ A).op secondScalar.op) ≫ prod.snd).unop = _
    exact congrArg (fun f : op A ⟶ op I => f.unop)
      (prod.lift_snd (0 : I ⟶ A).op secondScalar.op)
  rw [← Category.assoc, hs]
  simp [secondScalar]

example : CochainComplex.IsReducedCochain ι₀ p₀ scalarCochain := by
  constructor
  · rw [← HomComplex.Cochain.ofHom_comp, first_zero]
    exact HomComplex.Cochain.ofHom_zero _ _
  · rw [← HomComplex.Cochain.ofHom_comp, scalar_first_zero]
    exact HomComplex.Cochain.ofHom_zero _ _

private abbrev unitCoordinate : I.X 0 ≅ ModuleCat.of ℤ ℤ :=
  singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)

private def probe (p : A ⟶ I) (f : HomComplex.Cochain C A 0) : ℤ :=
  unitCoordinate.hom.hom
    ((ι₁.f 0 ≫ f.v 0 0 (add_zero 0) ≫ p.f 0).hom (unitCoordinate.inv.hom (1 : ℤ)))

private lemma probe_coordinate (g : C ⟶ A) (p : A ⟶ I) (n : ℤ)
    (hg : ι₁ ≫ g ≫ p = n • 𝟙 I) : probe p (HomComplex.Cochain.ofHom g) = n := by
  unfold probe
  rw [HomComplex.Cochain.ofHom_v]
  change unitCoordinate.hom.hom
    (((ι₁ ≫ g ≫ p).f 0).hom (unitCoordinate.inv.hom (1 : ℤ))) = n
  rw [hg]
  change unitCoordinate.hom.hom (n • unitCoordinate.inv.hom (1 : ℤ)) = n
  rw [map_smul]
  have hu : unitCoordinate.hom.hom (unitCoordinate.inv.hom (1 : ℤ)) = 1 :=
    ConcreteCategory.congr_hom unitCoordinate.inv_hom_id (1 : ℤ)
  rw [hu]
  simp

private lemma original_coordinate : probe p₁ scalarCochain = 2 :=
  probe_coordinate scalarMap p₁ 2 second_coordinate

private lemma original_first_zero : probe p₀ scalarCochain = 0 := by
  apply probe_coordinate
  rw [scalar_first_zero, comp_zero]
  simp

example : scalarCochain ≠ 0 := by
  intro h
  have hv := original_coordinate
  rw [h] at hv
  norm_num [probe] at hv

private abbrev zeroMC : CochainComplex.MaurerCartan (R := ℤ) (C := C) (A := A) :=
  CochainComplex.MaurerCartan.zero

example : CochainComplex.twistedBarDifferential zeroMC.tau scalarCochain = 0 := by
  simp [zeroMC, scalarCochain, CochainComplex.twistedBarDifferential,
    CochainComplex.conv_zero_right]

example : CochainComplex.twistedCobarDifferential zeroMC.tau scalarCochain = 0 := by
  simp [zeroMC, scalarCochain, CochainComplex.twistedCobarDifferential,
    CochainComplex.conv_zero_left]

example :
    ((CochainComplex.twistedHomComplexModule zeroMC.tau zeroMC.isMC).d 0 1).hom
      scalarCochain = 0 := by
  change CochainComplex.twistedDifferentialLinear zeroMC.tau 0 1 scalarCochain = 0
  simp [CochainComplex.twistedDifferentialLinear, zeroMC, scalarCochain,
    CochainComplex.twistedDifferential, CochainComplex.conv_zero_left,
    CochainComplex.conv_zero_right]

private def swapMon : algebra ⟶ algebra :=
  (unitProduct H).isLimit.lift (BinaryFan.mk p₁Mon p₀Mon)
private abbrev swap : A ⟶ A := swapMon.hom
private instance : IsMonHom swap := swapMon.isMonHom_hom

private lemma swap_first : swap ≫ p₀ = p₁ := by
  have h : swapMon ≫ p₀Mon = p₁Mon :=
    (unitProduct H).isLimit.fac (BinaryFan.mk p₁Mon p₀Mon) ⟨WalkingPair.left⟩
  exact congrArg (fun f : algebra ⟶ Mon.mk I => f.hom) h

private lemma swapped_coordinate : probe p₀ (HomComplex.Cochain.ofHom (scalarMap ≫ swap)) = 2 := by
  apply probe_coordinate
  simpa only [Category.assoc, swap_first] using second_coordinate

example : swap ≠ 𝟙 A := by
  intro h
  have hv := swapped_coordinate
  rw [h, Category.comp_id] at hv
  change probe p₀ scalarCochain = 2 at hv
  rw [original_first_zero] at hv
  norm_num at hv

private lemma transported_cochain :
    CochainComplex.twistedHomComplexMapCochain zeroMC (𝟙 C) swap scalarCochain =
      HomComplex.Cochain.ofHom (scalarMap ≫ swap) := by
  simp [CochainComplex.twistedHomComplexMapCochain, scalarCochain,
    ← HomComplex.Cochain.ofHom_comp]

example :
    probe p₀ (((CochainComplex.twistedHomComplexMap zeroMC (𝟙 C) swap).f 0).hom
      scalarCochain) = 2 := by
  change probe p₀ (CochainComplex.twistedHomComplexMapCochain zeroMC (𝟙 C) swap
    scalarCochain) = 2
  rw [transported_cochain]
  exact swapped_coordinate

example :
    probe p₀ ((CochainComplex.twistedHomComplexMapHom zeroMC (𝟙 C) swap)
      (-scalarCochain)) = -2 := by
  rw [map_neg]
  change probe p₀ (-CochainComplex.twistedHomComplexMapCochain zeroMC (𝟙 C) swap
    scalarCochain) = -2
  rw [transported_cochain, ← HomComplex.Cochain.ofHom_neg]
  apply probe_coordinate
  simp [Category.assoc, swap_first, Preadditive.comp_neg, Preadditive.neg_comp,
    second_coordinate, neg_smul]

private abbrev Z : M := ModuleCat.of ℤ ℤ
private abbrev twice : Z ⟶ Z := ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
private abbrev stepDifferential (n : ℤ) : Z ⟶ Z := if n = -1 then twice else 0
private abbrev E : H := CochainComplex.of (fun _ => Z) stepDifferential (by
  intro n
  by_cases hn : n = -1
  · subst n
    norm_num [stepDifferential]
  · simp [stepDifferential, hn])

private lemma step_value : E.d (-1) 0 = twice := by
  simpa [stepDifferential] using
    CochainComplex.of_d (fun _ => Z) stepDifferential (-1 : ℤ)

private abbrev oddCochain : HomComplex.Cochain E E (-1) :=
  HomComplex.Cochain.single (p := 0) (q := -1) (𝟙 Z) (-1)

example : oddCochain ≠ 0 := by
  intro h
  have hv := HomComplex.Cochain.congr_v h 0 (-1) (by decide)
  have hx := ConcreteCategory.congr_hom hv (1 : ℤ)
  norm_num [oddCochain, HomComplex.Cochain.single] at hx

example : ((HomComplex.δ (-1) 0 oddCochain).v (-1) (-1) (by decide)).hom (1 : ℤ) = 2 := by
  rw [HomComplex.δ_v (-1) 0 (by decide) oddCochain (-1) (-1) (by decide) (-2) 0 rfl rfl]
  rw [step_value]
  norm_num [oddCochain, HomComplex.Cochain.single, twice]

example : ((HomComplex.δ (-1) 0 oddCochain).v 0 0 (by decide)).hom (1 : ℤ) = 2 := by
  rw [HomComplex.δ_v (-1) 0 (by decide) oddCochain 0 0 (by decide) (-1) 1 rfl rfl]
  rw [step_value]
  norm_num [oddCochain, HomComplex.Cochain.single, twice]

end MathlibExtTest.ReducedTwistingHom
