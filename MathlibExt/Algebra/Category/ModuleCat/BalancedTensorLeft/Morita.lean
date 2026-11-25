/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaLeft
public import Mathlib.CategoryTheory.Equivalence

/-!
# Morita equivalence of the original left-module categories

The functors are the existing `Q ⊗_R −` and `P ⊗_S −` functors. Their
return maps use the actual associator, contractions and unitors. The
bundled inner ground action is compared with the original quotient action
by the proved ground-action equation, for arbitrary k.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe u r s v

namespace ModuleCat.BalancedTensor.Left.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R]
  (S : Type s) [Ring S] [Algebra k S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module k P] [Module R P] [Module Sᵐᵒᵖ P]
  [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  [Module k Q] [Module S Q] [Module Rᵐᵒᵖ Q]
  [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]

local notation "F" =>
  (ModuleCat.BalancedTensor.Left.functor k R S Q)
local notation "G" =>
  (ModuleCat.BalancedTensor.Left.functor k S R P)

/-- Bundle the original right-parenthesized tensor with its computed R action. -/
def rawObject (X : ModuleCat.{v} R) : ModuleCat.{v} R := by
  letI : Module k X := Module.compHom X (algebraMap k R)
  letI : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI := TensorProduct.Balanced.Morita.leftReturnModule k R S P Q X
  exact ModuleCat.of R (TensorProduct.Balanced.Morita.leftReturnSource k R S P Q X)

/-- The actual ordered pure class in the composite existing functor. -/
def compositeMk (X : ModuleCat.{v} R) (p : P) (q : Q) (x : X) : (F ⋙ G).obj X := by
  letI : Module k X := Module.compHom X (algebraMap k R)
  let A := ModuleCat.BalancedTensor.Left.obj k R S Q X
  letI : Module k A := Module.compHom A (algebraMap k S)
  exact mk k S P A p (mk k R Q X q x)

/-- The same pure factors in the original ground-module parentheses. -/
def rawMk (X : ModuleCat.{v} R) (p : P) (q : Q) (x : X) : rawObject k R S P Q X := by
  letI : Module k X := Module.compHom X (algebraMap k R)
  letI : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI := leftModule k R S Q X
  exact mk k S P (TensorProduct.Balanced k R Q X) p (mk k R Q X q x)

omit [IsScalarTower k Sᵐᵒᵖ P] [IsScalarTower k Rᵐᵒᵖ Q] in
/-- Pure ordered factors determine an additive map on the actual composite. -/
theorem compositeHom_ext (X : ModuleCat.{v} R)
    {C' : Type*} [AddCommMonoid C'] {f g : (F ⋙ G).obj X →+ C'}
    (h : ∀ (p : P) (q : Q) (x : X),
      f (compositeMk k R S P Q X p q x) = g (compositeMk k R S P Q X p q x)) :
    f = g := by
  let : Module k X := Module.compHom X (algebraMap k R)
  let A := ModuleCat.BalancedTensor.Left.obj k R S Q X
  let : Module k A := Module.compHom A (algebraMap k S)
  apply addHom_ext k S P A
  intro p a
  have ha : f.comp ((mk k S P A p).toAddMonoidHom) =
      g.comp ((mk k S P A p).toAddMonoidHom) := by
    apply addHom_ext k R Q X
    intro q x
    exact h p q x
  exact DFunLike.congr_fun ha a

omit [IsScalarTower k Sᵐᵒᵖ P] [IsScalarTower k Rᵐᵒᵖ Q] in
/-- The composite acts on the original module coefficient only. -/
@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_map simplifies LHS
theorem compositeMap_mk {X Y : ModuleCat.{v} R} (f : X ⟶ Y)
    (p : P) (q : Q) (x : X) :
    ((F ⋙ G).map f).hom (compositeMk k R S P Q X p q x) =
      compositeMk k R S P Q Y p q (f.hom x) := by
  let : Module k X := Module.compHom X (algebraMap k R)
  let : Module k Y := Module.compHom Y (algebraMap k R)
  let A := ModuleCat.BalancedTensor.Left.obj k R S Q X
  let B := ModuleCat.BalancedTensor.Left.obj k R S Q Y
  let : Module k A := Module.compHom A (algebraMap k S)
  let : Module k B := Module.compHom B (algebraMap k S)
  let a₀ : A := mk k R Q X q x
  let a₁ : B := mk k R Q Y q (f.hom x)
  have houter : (ModuleCat.BalancedTensor.Left.map k S R P
        (ModuleCat.BalancedTensor.Left.map k R S Q f)).hom
        (mk k S P A p a₀) =
      mk k S P B p ((ModuleCat.BalancedTensor.Left.map k R S Q f).hom a₀) :=
    ModuleCat.BalancedTensor.Left.map_mk
      (k := k) (R := S) (S := R) (Q := P) (N := A) (N' := B)
      (ModuleCat.BalancedTensor.Left.map k R S Q f) p a₀
  have hinner : (ModuleCat.BalancedTensor.Left.map k R S Q f).hom a₀ = a₁ :=
    ModuleCat.BalancedTensor.Left.map_mk
      (k := k) (R := R) (S := S) (Q := Q) (N := X) (N' := Y) f q x
  change (ModuleCat.BalancedTensor.Left.map k S R P
      (ModuleCat.BalancedTensor.Left.map k R S Q f)).hom
      (mk k S P A p a₀) = mk k S P B p a₁
  exact houter.trans (congrArg (fun y : B => mk k S P B p y) hinner)

/-- The complete computed comparison and its actual pure-coordinate equation. -/
def coordinateData (X : ModuleCat.{v} R) :
    {e : (F ⋙ G).obj X ≅ rawObject k R S P Q X //
      ∀ (p : P) (q : Q) (x : X),
        e.hom.hom (compositeMk k R S P Q X p q x) = rawMk k R S P Q X p q x} := by
  letI : Module k X := Module.compHom X (algebraMap k R)
  letI : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let C := TensorProduct.Balanced k R Q X
  let d₁ : Module k C := inferInstance
  let l : Module S C := leftModule k R S Q X
  letI : Module S C := l
  let d₀ : Module k C := Module.compHom C (algebraMap k S)
  have hd : d₀ = d₁ := by
    apply Module.ext'
    intro c x
    change leftAction k R S Q X (algebraMap k S c) x = d₁.smul c x
    exact DFunLike.congr_fun (leftAction_algebraMap k R S Q X c) x
  let K : Module k C → ModuleCat.{v} R := fun d =>
    letI : Module k C := d
    letI : Module S C := l
    letI := leftModule k S R P C
    ModuleCat.of R (TensorProduct.Balanced k S P C)
  let z : ∀ d : Module k C, P → Q → X → K d := fun d p q x =>
    letI : Module k C := d
    letI : Module S C := l
    mk k S P C p (mk k R Q X q x)
  have compare (d d' : Module k C) (h : d = d') :
      {e : K d ≅ K d' // ∀ (p : P) (q : Q) (x : X),
        e.hom.hom (z d p q x) = z d' p q x} := by
    cases h
    exact ⟨Iso.refl _, fun _ _ _ => rfl⟩
  exact compare d₀ d₁ hd

/-- The actual composite-to-raw module comparison, preserving original factors. -/
def coordinates (X : ModuleCat.{v} R) :
    (F ⋙ G).obj X ≅ rawObject k R S P Q X :=
  (coordinateData k R S P Q X).1

omit [IsScalarTower k Sᵐᵒᵖ P] [IsScalarTower k Rᵐᵒᵖ Q] in
@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem coordinates_mk (X : ModuleCat.{v} R) (p : P) (q : Q) (x : X) :
    (coordinates k R S P Q X).hom.hom (compositeMk k R S P Q X p q x) =
      rawMk k R S P Q X p q x :=
  (coordinateData k R S P Q X).2 p q x

variable
  (u : letI := leftModule k S R P Q
    letI := rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule k S R P Q
    letI := rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

include u hu in
/-- The actual return to the original native left R-module. -/
def returnIso (X : ModuleCat.{v} R) : (F ⋙ G).obj X ≅ X := by
  letI : Module k X := Module.compHom X (algebraMap k R)
  letI : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (coordinates k R S P Q X).trans
    (TensorProduct.Balanced.Morita.leftReturn k R S P Q X u hu).toModuleIso

/-- The returned ordered pure class is the original contraction acting on X. -/
@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem returnIso_mk (X : ModuleCat.{v} R) (p : P) (q : Q) (x : X) :
    (returnIso k R S P Q u hu X).hom.hom (compositeMk k R S P Q X p q x) =
      u (mk k S P Q p q) • x := by
  let : Module k X := Module.compHom X (algebraMap k R)
  let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change TensorProduct.Balanced.Morita.leftReturn k R S P Q X u hu
      ((coordinates k R S P Q X).hom.hom (compositeMk k R S P Q X p q x)) = _
  rw [coordinates_mk]
  exact TensorProduct.Balanced.Morita.leftReturn_mk k R S P Q X u hu p q x

include u hu in
/-- The actual contraction is natural in the original native module morphisms. -/
def returnNatIso : F ⋙ G ≅ 𝟭 (ModuleCat.{v} R) :=
  NatIso.ofComponents (returnIso k R S P Q u hu) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply compositeHom_ext k R S P Q X
    intro p q x
    change (returnIso k R S P Q u hu Y).hom.hom
        (((F ⋙ G).map f).hom (compositeMk k R S P Q X p q x)) =
      f.hom ((returnIso k R S P Q u hu X).hom.hom
        (compositeMk k R S P Q X p q x))
    rw [compositeMap_mk, returnIso_mk, returnIso_mk]
    exact (f.hom.map_smul (u (mk k S P Q p q)) x).symm)

variable
  (w : letI := leftModule k R S Q P
    letI := rightModule k R S Q P
    TensorProduct.Balanced k R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule k R S Q P
    letI := rightModule k R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced k R Q P), w (s • b) = s * w b)

include u hu w hw in
/-- The source's actual left-module tensor equivalence, without normalized inputs. -/
def equivalence : ModuleCat.{v} R ≌ ModuleCat.{v} S :=
  CategoryTheory.Equivalence.mk F G
    (returnNatIso k R S P Q u hu).symm (returnNatIso k S R Q P w hw)

@[simp]
theorem equivalence_functor : (equivalence k R S P Q u hu w hw).functor = F := rfl

@[simp]
theorem equivalence_inverse : (equivalence k R S P Q u hu w hw).inverse = G := rfl

/-- Native adjointification retains the actual symmetric return counit. -/
theorem equivalence_counitIso : (equivalence k R S P Q u hu w hw).counitIso =
    returnNatIso k S R Q P w hw := rfl

/-- The chosen unit is the native refinement of the actual original return. -/
theorem equivalence_unitIso : (equivalence k R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (returnNatIso k R S P Q u hu).symm
      (returnNatIso k S R Q P w hw) := rfl

/-- The actual counit applies w to q⊗p in that order. -/
@[simp, nolint simpNF] -- stated with the equivalence for rw; equivalence_functor simplifies LHS
theorem equivalence_counitIso_mk (Y : ModuleCat.{v} S) (q : Q) (p : P) (y : Y) :
    ((equivalence k R S P Q u hu w hw).counitIso.hom.app Y).hom
        (compositeMk k S R Q P Y q p y) = w (mk k R Q P q p) • y :=
  returnIso_mk k S R Q P w hw Y q p y

end ModuleCat.BalancedTensor.Left.Morita
