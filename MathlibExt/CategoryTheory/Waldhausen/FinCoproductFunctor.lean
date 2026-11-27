/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductExact
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductCofibration
public import MathlibExt.CategoryTheory.Waldhausen.CoproductExactFunctorIso
public import MathlibExt.CategoryTheory.Waldhausen.ProductExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.Pi
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Ordered finite coproduct folds in Waldhausen categories

Let C have a chosen zero and a Waldhausen structure without gluing. The finite fold Tₙ on Fin
n-families uses the selected zero when n=0, and the chosen binary coproduct of the head with the
folded tail at a successor. Its recursive injections are cofibrations and form a colimiting
finite cofan.

The gluing axiom says that a weak morphism between cofibration-pushout diagrams induces a weak
comparison of their apices. If C satisfies this axiom, each fold Tₙ is Waldhausen exact for the
pointwise finite-family model. A given Waldhausen-exact functor F:C→D maps the selected fold
cofans, and any supplied colimiting finite cofan, to colimiting cofans with their actual mapped
legs.

The object and Hom universes of C and D are independent. Tail restriction itself requires only a
category and drops the first coordinate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C]

/-- For any category C and n∈ℕ, restrict a family indexed by Fin(n+1) to its tail, sending
coordinate i to the original coordinate i+1. -/
def finTail (n : ℕ) : (Fin (n + 1) → C) ⥤ (Fin n → C) :=
  Functor.pi' (fun i => Pi.eval (fun _ : Fin (n + 1) => C) i.succ)

/-- For X:Fin(n+1)→C, the tail family has value X_(i+1) at i∈Fin n. -/
theorem finTail_obj (n : ℕ) (X : Fin (n + 1) → C) :
    (finTail C n).obj X = fun i : Fin n => X i.succ := rfl

/-- For a family morphism f:X→Y indexed by Fin(n+1), its tail map has component f_(i+1) at i∈Fin n. -/
theorem finTail_map (n : ℕ) {X Y : Fin (n + 1) → C} (f : X ⟶ Y) :
    (finTail C n).map f = fun i : Fin n => f i.succ := rfl

variable [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. Tail restriction from
Fin(n+1)-families to Fin n-families is Waldhausen exact for the pointwise family models. -/
theorem finTail_isWaldhausenExact (n : ℕ) :
    letI := piWaldhausen (fun _ : Fin (n + 1) => C)
    letI := piWaldhausen (fun _ : Fin n => C)
    (finTail C n).IsWaldhausenExact := by
  let _ := piWaldhausen (fun _ : Fin (n + 1) => C)
  exact Functor.IsWaldhausenExact.pi' (fun _ : Fin n => C)
    (fun i => Pi.eval (fun _ : Fin (n + 1) => C) i.succ)
    (fun i => Pi.eval_isWaldhausenExact (fun _ : Fin (n + 1) => C) i.succ)

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The empty fold is the selected zero; a
successor is the chosen binary coproduct of X₀ with Tₙ of the tail, in that order. -/
def waldhausenFinCoproductFunctor : (n : ℕ) → (Fin n → C) ⥤ C
  | 0 => (Functor.const (Fin 0 → C)).obj (0 : C)
  | n + 1 =>
    ((Pi.eval (fun _ : Fin (n + 1) => C) 0).prod'
      (finTail C n ⋙ waldhausenFinCoproductFunctor n)) ⋙ waldhausenCoproductFunctor C

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. T₀ is the constant functor at the
selected zero object of C. -/
theorem waldhausenFinCoproductFunctor_zero :
    waldhausenFinCoproductFunctor C 0 = (Functor.const (Fin 0 → C)).obj (0 : C) := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. Tₙ₊₁ is head evaluation paired with
the n-fold tail and followed by the chosen binary coproduct functor. -/
theorem waldhausenFinCoproductFunctor_succ (n : ℕ) :
    waldhausenFinCoproductFunctor C (n + 1) =
      ((Pi.eval (fun _ : Fin (n + 1) => C) 0).prod'
        (finTail C n ⋙ waldhausenFinCoproductFunctor C n)) ⋙ waldhausenCoproductFunctor C :=
  rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. On X:Fin(n+1)→C, the successor object
is the chosen coproduct apex of X₀ and Tₙ(tail X). -/
theorem waldhausenFinCoproductFunctor_obj_succ (n : ℕ) (X : Fin (n + 1) → C) :
    (waldhausenFinCoproductFunctor C (n + 1)).obj X =
      (binaryCoproductColimitCocone C
        (pair (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))).cocone.pt :=
  waldhausenCoproductFunctor_obj C
    (X 0, (waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X))

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The successor map of f:X→Y is the
chosen binary coproduct map of f₀ and Tₙ(tail f), under the head-and-tail object charts. -/
theorem waldhausenFinCoproductFunctor_map_succ (n : ℕ)
    {X Y : Fin (n + 1) → C} (f : X ⟶ Y) :
    (waldhausenFinCoproductFunctor C (n + 1)).map f =
      eqToHom (waldhausenFinCoproductFunctor_obj_succ C n X) ≫
        binaryCoproductMap C (f 0)
          ((waldhausenFinCoproductFunctor C n).map ((finTail C n).map f)) ≫
            eqToHom (waldhausenFinCoproductFunctor_obj_succ C n Y).symm :=
  waldhausenCoproductFunctor_map C
    (p := (X 0, (waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))
    (q := (Y 0, (waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj Y)))
    (f 0, (waldhausenFinCoproductFunctor C n).map ((finTail C n).map f))

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The successor value Tₙ₊₁(X) has the
binary cofan with terms X₀ and Tₙ(tail X), using the selected coproduct injections. -/
@[implicit_reducible]
def waldhausenFinCoproductStepCofan (n : ℕ) (X : Fin (n + 1) → C) :
    BinaryCofan (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)) :=
  let c : BinaryCofan (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)) :=
    (binaryCoproductColimitCocone C
      (pair (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))).cocone
  BinaryCofan.mk
    (c.inl ≫ eqToHom (waldhausenFinCoproductFunctor_obj_succ C n X).symm)
    (c.inr ≫ eqToHom (waldhausenFinCoproductFunctor_obj_succ C n X).symm)

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The head-and-tail cofan apex is
Tₙ₊₁(X). -/
theorem waldhausenFinCoproductStepCofan_pt (n : ℕ) (X : Fin (n + 1) → C) :
    (waldhausenFinCoproductStepCofan C n X).pt =
      (waldhausenFinCoproductFunctor C (n + 1)).obj X := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The head-and-tail binary cofan is
colimiting, representing the coproduct of X₀ and Tₙ(tail X). -/
def waldhausenFinCoproductStepCofanIsColimit (n : ℕ) (X : Fin (n + 1) → C) :
    IsColimit (waldhausenFinCoproductStepCofan C n X) := by
  let c : BinaryCofan (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)) :=
    (binaryCoproductColimitCocone C
      (pair (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))).cocone
  refine IsColimit.ofIsoColimit
    (binaryCoproductColimitCocone C
      (pair (X 0) ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))).isColimit ?_
  apply Cocone.ext _ _
  · exact eqToIso (waldhausenFinCoproductFunctor_obj_succ C n X).symm
  rintro ⟨i⟩
  cases i <;> rfl

private theorem stepCofan_inl_naturality (n : ℕ)
    {X Y : Fin (n + 1) → C} (f : X ⟶ Y) :
    (waldhausenFinCoproductStepCofan C n X).inl ≫
        (waldhausenFinCoproductFunctor C (n + 1)).map f =
      f 0 ≫ (waldhausenFinCoproductStepCofan C n Y).inl := by
  dsimp only [waldhausenFinCoproductStepCofan, BinaryCofan.mk_inl]
  rw [waldhausenFinCoproductFunctor_map_succ]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simpa only [Category.assoc] using (congrArg
    (fun k => k ≫ eqToHom (waldhausenFinCoproductFunctor_obj_succ C n Y).symm)
    (binaryCoproductMap_inl C (f 0)
      ((waldhausenFinCoproductFunctor C n).map ((finTail C n).map f))))

private theorem stepCofan_inr_naturality (n : ℕ)
    {X Y : Fin (n + 1) → C} (f : X ⟶ Y) :
    (waldhausenFinCoproductStepCofan C n X).inr ≫
        (waldhausenFinCoproductFunctor C (n + 1)).map f =
      (waldhausenFinCoproductFunctor C n).map ((finTail C n).map f) ≫
        (waldhausenFinCoproductStepCofan C n Y).inr := by
  dsimp only [waldhausenFinCoproductStepCofan, BinaryCofan.mk_inr]
  rw [waldhausenFinCoproductFunctor_map_succ]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simpa only [Category.assoc] using (congrArg
    (fun k => k ≫ eqToHom (waldhausenFinCoproductFunctor_obj_succ C n Y).symm)
    (binaryCoproductMap_inr C (f 0)
      ((waldhausenFinCoproductFunctor C n).map ((finTail C n).map f))))

private theorem stepCofan_injections_isCofibration (n : ℕ) (X : Fin (n + 1) → C) :
    IsCofibration (waldhausenFinCoproductStepCofan C n X).inl ∧
      IsCofibration (waldhausenFinCoproductStepCofan C n X).inr := by
  have hc := binaryCoproductColimitCocone_injections_isCofibration C (X 0)
    ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X))
  have ht : IsCofibration (eqToHom (waldhausenFinCoproductFunctor_obj_succ C n X).symm) :=
    WaldhausenCategoryWithoutGluing.cofibrations.of_isIso _
  exact ⟨WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _ hc.1 ht,
    WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _ hc.2 ht⟩

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. Each coordinate i has its recursive
injection ηᵢ:Xᵢ→Tₙ(X); the first injection is the head leg and tail injections pass through the
second leg. -/
def waldhausenFinCoproductInjection :
    (n : ℕ) → (X : Fin n → C) → (i : Fin n) → X i ⟶ (waldhausenFinCoproductFunctor C n).obj X
  | 0, _, i => Fin.elim0 i
  | n + 1, X, i =>
    let c := waldhausenFinCoproductStepCofan C n X
    Fin.cases c.inl
      (fun k => waldhausenFinCoproductInjection n ((finTail C n).obj X) k ≫ c.inr) i

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The coordinate-zero injection into
Tₙ₊₁(X) is the head leg of the successor binary cofan. -/
theorem waldhausenFinCoproductInjection_zero (n : ℕ) (X : Fin (n + 1) → C) :
    waldhausenFinCoproductInjection C (n + 1) X 0 =
      (waldhausenFinCoproductStepCofan C n X).inl := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The injection of coordinate i+1 is ηᵢ
of the folded tail followed by the successor cofan's second leg. -/
theorem waldhausenFinCoproductInjection_succ (n : ℕ) (X : Fin (n + 1) → C) (i : Fin n) :
    waldhausenFinCoproductInjection C (n + 1) X i.succ =
      waldhausenFinCoproductInjection C n ((finTail C n).obj X) i ≫
        (waldhausenFinCoproductStepCofan C n X).inr := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. For f:X→Y and i∈Fin n,
ηXᵢ≫Tₙ(f)=fᵢ≫ηYᵢ. -/
theorem waldhausenFinCoproductInjection_naturality :
    ∀ (n : ℕ) (X Y : Fin n → C) (f : X ⟶ Y) (i : Fin n),
      waldhausenFinCoproductInjection C n X i ≫ (waldhausenFinCoproductFunctor C n).map f =
        f i ≫ waldhausenFinCoproductInjection C n Y i
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, X, Y, f, i => by
    refine Fin.cases ?_ ?_ i
    · exact stepCofan_inl_naturality C n f
    · intro k
      let cX := waldhausenFinCoproductStepCofan C n X
      let cY := waldhausenFinCoproductStepCofan C n Y
      change (waldhausenFinCoproductInjection C n ((finTail C n).obj X) k ≫ cX.inr) ≫
          (waldhausenFinCoproductFunctor C (n + 1)).map f =
        f k.succ ≫ (waldhausenFinCoproductInjection C n ((finTail C n).obj Y) k ≫ cY.inr)
      rw [Category.assoc, stepCofan_inr_naturality, ← Category.assoc,
        waldhausenFinCoproductInjection_naturality n
          ((finTail C n).obj X) ((finTail C n).obj Y) ((finTail C n).map f) k,
        Category.assoc]
      rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. Every recursive coordinate injection
Xᵢ→Tₙ(X) is a cofibration. -/
theorem waldhausenFinCoproductInjection_isCofibration :
    ∀ (n : ℕ) (X : Fin n → C) (i : Fin n),
      IsCofibration (waldhausenFinCoproductInjection C n X i)
  | 0, _, i => Fin.elim0 i
  | n + 1, X, i => by
    refine Fin.cases ?_ ?_ i
    · exact (stepCofan_injections_isCofibration C n X).1
    · intro k
      exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem _ _
        (waldhausenFinCoproductInjection_isCofibration n ((finTail C n).obj X) k)
        (stepCofan_injections_isCofibration C n X).2

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The apex Tₙ(X) and recursive
coordinate injections form the finite cofan of X. -/
@[implicit_reducible]
def waldhausenFinCoproductCofan (n : ℕ) (X : Fin n → C) : Cofan X :=
  Cofan.mk ((waldhausenFinCoproductFunctor C n).obj X) (waldhausenFinCoproductInjection C n X)

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The finite cofan's apex is the chosen
fold value Tₙ(X). -/
theorem waldhausenFinCoproductCofan_pt (n : ℕ) (X : Fin n → C) :
    (waldhausenFinCoproductCofan C n X).pt = (waldhausenFinCoproductFunctor C n).obj X := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The i-th leg of the finite cofan is
the recursive coordinate injection ηᵢ. -/
theorem waldhausenFinCoproductCofan_inj (n : ℕ) (X : Fin n → C) (i : Fin n) :
    (waldhausenFinCoproductCofan C n X).inj i = waldhausenFinCoproductInjection C n X i := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The successor finite cofan is the
extension of the tail cofan by the head-and-tail binary cofan. -/
theorem waldhausenFinCoproductCofan_succ (n : ℕ) (X : Fin (n + 1) → C) :
    waldhausenFinCoproductCofan C (n + 1) X =
      extendCofan (waldhausenFinCoproductCofan C n ((finTail C n).obj X))
        (waldhausenFinCoproductStepCofan C n X) := rfl

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. For every n and X, the cofan with apex
Tₙ(X) and legs ηᵢ is colimiting. -/
def waldhausenFinCoproductCofanIsColimit :
    (n : ℕ) → (X : Fin n → C) → IsColimit (waldhausenFinCoproductCofan C n X)
  | 0, X =>
    Cofan.IsColimit.mk (waldhausenFinCoproductCofan C 0 X)
      (fun s => (isZero_zero C).to_ s.pt)
      (fun _ i => Fin.elim0 i)
      (fun s m _ => (isZero_zero C).eq_of_src m ((isZero_zero C).to_ s.pt))
  | n + 1, X =>
    extendCofanIsColimit X
      (waldhausenFinCoproductCofanIsColimit n ((finTail C n).obj X))
      (waldhausenFinCoproductStepCofanIsColimit C n X)

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. The map Tₙ(f) is the unique descent
whose restriction along ηXᵢ is fᵢ≫ηYᵢ for every coordinate i. -/
theorem waldhausenFinCoproductFunctor_map_eq_desc (n : ℕ)
    {X Y : Fin n → C} (f : X ⟶ Y) :
    (waldhausenFinCoproductFunctor C n).map f =
      Cofan.IsColimit.desc (waldhausenFinCoproductCofanIsColimit C n X)
        (fun i => f i ≫ waldhausenFinCoproductInjection C n Y i) := by
  apply Cofan.IsColimit.hom_ext (waldhausenFinCoproductCofanIsColimit C n X)
  intro i
  exact (waldhausenFinCoproductInjection_naturality C n X Y f i).trans
    (Cofan.IsColimit.fac (waldhausenFinCoproductCofanIsColimit C n X)
      (fun j => f j ≫ waldhausenFinCoproductInjection C n Y j) i).symm

/-- Let C be a category with a chosen zero object and a Waldhausen structure without gluing. Write
Tₙ(X) for its ordered finite coproduct fold of X:Fin n→C. Assume the Waldhausen gluing axiom for
C: weak morphisms of cofibration-pushout diagrams induce weak comparisons of their apices. Then
every Tₙ is Waldhausen exact from the pointwise Fin n-family model to C. -/
theorem waldhausenFinCoproductFunctor_isWaldhausenExact
    (hG : WaldhausenGluingAxiom (C := C)) : ∀ n : ℕ,
    letI := piWaldhausen (fun _ : Fin n => C)
    (waldhausenFinCoproductFunctor C n).IsWaldhausenExact
  | 0 => by
    let _ := piWaldhausen (fun _ : Fin 0 => C)
    exact Functor.IsWaldhausenExact.constantZero (Fin 0 → C) C
  | n + 1 => by
    let _ := piWaldhausen (fun _ : Fin (n + 1) => C)
    let _ := piWaldhausen (fun _ : Fin n => C)
    let _ : WaldhausenCategoryWithoutGluing (C × C) := prodWaldhausen (C := C) (D := C)
    let hHead := Pi.eval_isWaldhausenExact (fun _ : Fin (n + 1) => C) 0
    let hTail := (finTail_isWaldhausenExact C n).comp
      (waldhausenFinCoproductFunctor_isWaldhausenExact hG n)
    exact (hHead.prod' hTail).comp (waldhausenCoproductFunctor_isWaldhausenExact C hG)

end CategoryTheory.Waldhausen

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Let F:C→D be Waldhausen exact between categories with chosen zeros and Waldhausen structures
without gluing. For any colimiting binary cofan c on X,Y in C, the cofan in D with apex F(c.pt)
and legs F(c.inl),F(c.inr) is colimiting. -/
def mapBinaryCofanIsColimit {X Y : C}
    (c : BinaryCofan X Y) (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk (F.map c.inl) (F.map c.inr)) := by
  let d : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
  let hd : IsColimit d := (binaryCoproductColimitCocone C (pair X Y)).isColimit
  let e : d.pt ≅ c.pt := IsColimit.coconePointUniqueUpToIso hd hc
  refine IsColimit.ofIsoColimit (mappedCoproductCoconeIsColimit hF X Y) ?_
  apply Cocone.ext _ _
  · exact F.mapIso e
  rintro ⟨j⟩
  cases j
  · change F.map d.inl ≫ F.map e.hom = F.map c.inl
    rw [← F.map_comp]
    exact congrArg F.map (IsColimit.comp_coconePointUniqueUpToIso_hom hd hc ⟨WalkingPair.left⟩)
  · change F.map d.inr ≫ F.map e.hom = F.map c.inr
    rw [← F.map_comp]
    exact congrArg F.map (IsColimit.comp_coconePointUniqueUpToIso_hom hd hc ⟨WalkingPair.right⟩)

/-- Let F:C→D be Waldhausen exact between categories with chosen zeros and Waldhausen structures
without gluing. Applying F to the chosen finite fold cofan gives a colimiting cofan with apex
F(Tₙ(X)) and legs F(ηᵢ). -/
def mappedFinCoproductCofanIsColimit : (n : ℕ) → (X : Fin n → C) →
    IsColimit (Cofan.mk (F.obj ((waldhausenFinCoproductFunctor C n).obj X))
      (fun i => F.map (waldhausenFinCoproductInjection C n X i)))
  | 0, X =>
    Cofan.IsColimit.mk _ (fun s => (hF.map_isZero (isZero_zero C)).to_ s.pt)
      (fun _ i => Fin.elim0 i)
      (fun s m _ => (hF.map_isZero (isZero_zero C)).eq_of_src m
        ((hF.map_isZero (isZero_zero C)).to_ s.pt))
  | n + 1, X => by
    let c := waldhausenFinCoproductStepCofan C n X
    let tail := Cofan.mk (F.obj ((waldhausenFinCoproductFunctor C n).obj ((finTail C n).obj X)))
      (fun i => F.map (waldhausenFinCoproductInjection C n ((finTail C n).obj X) i))
    let binary := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    have hc : IsColimit (extendCofan tail binary) :=
      extendCofanIsColimit (fun i => F.obj (X i))
        (mappedFinCoproductCofanIsColimit n ((finTail C n).obj X))
        (mapBinaryCofanIsColimit hF c (waldhausenFinCoproductStepCofanIsColimit C n X))
    refine IsColimit.ofIsoColimit hc ?_
    apply Cocone.ext _ _
    · exact Iso.refl _
    rintro ⟨i⟩
    refine Fin.cases ?_ ?_ i
    · exact Category.comp_id _
    · intro k
      change (F.map (waldhausenFinCoproductInjection C n ((finTail C n).obj X) k) ≫
          F.map c.inr) ≫ 𝟙 _ =
        F.map (waldhausenFinCoproductInjection C n ((finTail C n).obj X) k ≫ c.inr)
      rw [Category.comp_id, F.map_comp]

/-- Let F:C→D be Waldhausen exact between categories with chosen zeros and Waldhausen structures
without gluing. Every supplied colimiting finite cofan c is sent to a colimiting cofan with its
actual mapped apex and every mapped leg. -/
def mapFinCofanIsColimit {n : ℕ} {X : Fin n → C} (c : Cofan X) (hc : IsColimit c) :
    IsColimit (Cofan.mk (F.obj c.pt) (fun i => F.map (c.inj i))) := by
  let d := waldhausenFinCoproductCofan C n X
  let hd := waldhausenFinCoproductCofanIsColimit C n X
  let e : d.pt ≅ c.pt := IsColimit.coconePointUniqueUpToIso hd hc
  have hmd : IsColimit (Cofan.mk (F.obj d.pt) (fun i => F.map (d.inj i))) :=
    mappedFinCoproductCofanIsColimit hF n X
  refine IsColimit.ofIsoColimit hmd ?_
  apply Cocone.ext _ _
  · exact F.mapIso e
  rintro ⟨i⟩
  change F.map (d.inj i) ≫ F.map e.hom = F.map (c.inj i)
  rw [← F.map_comp]
  exact congrArg F.map (IsColimit.comp_coconePointUniqueUpToIso_hom hd hc ⟨i⟩)

end CategoryTheory.Functor.IsWaldhausenExact

end
