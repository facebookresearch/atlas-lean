/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionHomAdditive

/-!
# Naturality of finite-resolution homotopy functors

Let i : P → A and j : Q → B be additive full faithful functors from preadditive categories to
abelian categories, with projective resolving images. An additive source functor F and additive
homology-preserving target functor H with Hi ≅ jF identify the F-image resolution of X with a
finite resolution of H(X).

For chosen families R(X) and S(Y), identity comparisons over H(X) give a natural isomorphism
between the F-image of the R homotopy functor and the S homotopy functor after H. The
represented source and target complexes retain the support bounds of their respective chosen
families.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {i : P ⥤ A} [i.Additive] [i.Full] [i.Faithful]
variable {j : Q ⥤ B} [j.Additive] [j.Full] [j.Faithful]

/-- Let P,Q be preadditive, A abelian and i : P → A additive full faithful with projective resolving
images. For an additive F : P → Q and a resolution family R, the source homotopy functor at X
represents the degreewise F-image of R(X).complex. -/
theorem finiteResolutionHomotopyFunctorNaturality_source_obj_as
    (F : P ⥤ Q) [F.Additive] (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    (((finiteResolutionHomotopyFunctor R hproj) ⋙
      F.mapHomotopyCategory (ComplexShape.down ℕ)).obj X).as =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (R X).complex :=
  rfl

/-- Let P,Q be preadditive, A abelian and i : P → A additive full faithful with all i(P₀)
projective. For additive F and a finite-resolution family R, the represented source-image
complex at X is zero in every degree n>R(X).bound. -/
theorem finiteResolutionHomotopyFunctorNaturality_source_isZero_above
    (F : P ⥤ Q) [F.Additive] (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n : ℕ) (hn : (R X).bound < n) :
    IsZero ((((finiteResolutionHomotopyFunctor R hproj) ⋙
      F.mapHomotopyCategory (ComplexShape.down ℕ)).obj X).as.X n) :=
  F.map_isZero ((R X).isZero_above n hn)

omit [Abelian A] in
/-- Let A be a category, B abelian, Q preadditive and j : Q → B additive full faithful with
projective resolving images. For any functor H : A → B and a resolution family S, the target
homotopy functor at X represents S(H(X)).complex. -/
theorem finiteResolutionHomotopyFunctorNaturality_target_obj_as
    (H : A ⥤ B) (S : ∀ Y : B, FiniteResolution j Y)
    (hproj : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) :
    ((H ⋙ finiteResolutionHomotopyFunctor S hproj).obj X).as =
      (S (H.obj X)).complex :=
  rfl

omit [Abelian A] in
/-- Let A be a category, B abelian, Q preadditive and j : Q → B additive full faithful with
projective resolving images. For H : A → B and family S, the represented target complex at X is
zero for n>S(H(X)).bound. -/
theorem finiteResolutionHomotopyFunctorNaturality_target_isZero_above
    (H : A ⥤ B) (S : ∀ Y : B, FiniteResolution j Y)
    (hproj : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) (n : ℕ)
    (hn : (S (H.obj X)).bound < n) :
    IsZero (((H ⋙ finiteResolutionHomotopyFunctor S hproj).obj X).as.X n) :=
  (S (H.obj X)).isZero_above n hn

section Naturality

variable (F : P ⥤ Q) [F.Additive] (H : A ⥤ B) [H.Additive] [H.PreservesHomology]

/-- Let P,Q be preadditive, A,B abelian, and i : P → A and j : Q → B additive full faithful. Let F :
P → Q be additive and H : A → B additive and homology-preserving, with compatibility H ∘ i ≅ j ∘
F. Let R(X) and S(Y) be chosen finite-resolution families for i and j, and assume every i(P₀)
and j(Q₀) is projective. There is a natural isomorphism from the F-image of the R
finite-resolution homotopy functor to the S homotopy functor after H. Each component is the
homotopy class of an identity comparison between the transported R(X) resolution of H(X) and
S(H(X)). -/
def finiteResolutionHomotopyFunctorNaturality (e : i ⋙ H ≅ F ⋙ j)
    (R : ∀ X : A, FiniteResolution i X) (S : ∀ Y : B, FiniteResolution j Y)
    (hprojP : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojQ : ∀ Q₀ : Q, Projective (j.obj Q₀)) :
    finiteResolutionHomotopyFunctor R hprojP ⋙
        F.mapHomotopyCategory (ComplexShape.down ℕ) ≅
      H ⋙ finiteResolutionHomotopyFunctor S hprojQ :=
  NatIso.ofComponents (fun X =>
    (F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).app ((R X).complex) ≪≫
      finiteResolutionComparisonIso
        (((R X).mapTarget H e).mapSource F (Iso.refl (F ⋙ j)))
        (S (H.obj X)) hprojQ) (by
    intro X Y f
    simp only [CategoryTheory.Functor.comp_map]
    let T (Z : A) : FiniteResolution j (H.obj Z) :=
      ((R Z).mapTarget H e).mapSource F (Iso.refl (F ⋙ j))
    let φ : Hom (R X) (R Y) f := comparisonHom (R X) (R Y) f hprojP
    let χ : Hom (T X) (T Y) (H.map f) :=
      (φ.mapTarget H e).mapSource F (Iso.refl (F ⋙ j))
    let βX := comparisonHom (T X) (S (H.obj X)) (𝟙 (H.obj X)) hprojQ
    let βY := comparisonHom (T Y) (S (H.obj Y)) (𝟙 (H.obj Y)) hprojQ
    let σ := comparisonHom (S (H.obj X)) (S (H.obj Y)) (H.map f) hprojQ
    let q := HomotopyCategory.quotient Q (ComplexShape.down ℕ)
    let a := F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)
    have hχ : χ.map = (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map :=
      (Hom.mapSource_map F (Iso.refl (F ⋙ j)) (φ.mapTarget H e)).trans
        (congrArg (fun t : (R X).complex ⟶ (R Y).complex =>
          (F.mapHomologicalComplex (ComplexShape.down ℕ)).map t) (Hom.mapTarget_map H e φ))
    let DX := (F.mapHomotopyCategory (ComplexShape.down ℕ)).obj
      ((HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R X).complex)
    let DY := (F.mapHomotopyCategory (ComplexShape.down ℕ)).obj
      ((HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R Y).complex)
    let IX := q.obj (T X).complex
    let IY := q.obj (T Y).complex
    let SX := q.obj (S (H.obj X)).complex
    let SY := q.obj (S (H.obj Y)).complex
    let d : DX ⟶ DY := (F.mapHomotopyCategory (ComplexShape.down ℕ)).map
      ((HomotopyCategory.quotient P (ComplexShape.down ℕ)).map φ.map)
    let ax : DX ⟶ IX := a.hom.app ((R X).complex)
    let ay : DY ⟶ IY := a.hom.app ((R Y).complex)
    let u : IX ⟶ IY := q.map χ.map
    let bx : IX ⟶ SX := q.map βX.map
    let bY : IY ⟶ SY := q.map βY.map
    let s : SX ⟶ SY := q.map σ.map
    change d ≫ (ay ≫ bY) = (ax ≫ bx) ≫ s
    have hchart : d ≫ ay = ax ≫ u := by
      have hn := a.hom.naturality φ.map
      simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hn
      rw [← hχ] at hn
      exact hn
    let c (t : H.obj X ⟶ H.obj Y) := comparisonHom (T X) (S (H.obj Y)) t hprojQ
    have hleft := comparisonHomotopy (χ.comp βY)
      (c (H.map f ≫ 𝟙 (H.obj Y))) hprojQ
    have hright := comparisonHomotopy (c (𝟙 (H.obj X) ≫ H.map f))
      (βX.comp σ) hprojQ
    have hindexLeft := congrArg (fun t : H.obj X ⟶ H.obj Y => (c t).map)
      (Category.comp_id (H.map f))
    have hindexRight := congrArg (fun t : H.obj X ⟶ H.obj Y => (c t).map)
      (Category.id_comp (H.map f))
    have h : Homotopy (χ.map ≫ βY.map) (βX.map ≫ σ.map) :=
      hleft.trans ((Homotopy.ofEq hindexLeft).trans
        ((Homotopy.ofEq hindexRight).symm.trans hright))
    have hquot : u ≫ bY = bx ≫ s := by
      change q.map χ.map ≫ q.map βY.map = q.map βX.map ≫ q.map σ.map
      rw [← q.map_comp, ← q.map_comp]
      exact HomotopyCategory.eq_of_homotopy _ _ h
    calc
      _ = (d ≫ ay) ≫ bY := (Category.assoc d ay bY).symm
      _ = (ax ≫ u) ≫ bY := congrArg (fun t : DX ⟶ IY => t ≫ bY) hchart
      _ = ax ≫ (u ≫ bY) := Category.assoc ax u bY
      _ = ax ≫ (bx ≫ s) := congrArg (fun t : IX ⟶ SY => ax ≫ t) hquot
      _ = (ax ≫ bx) ≫ s := (Category.assoc ax bx s).symm)

/-- Let P,Q be preadditive, A,B abelian, and i : P → A and j : Q → B additive full faithful. Let F :
P → Q be additive and H : A → B additive and homology-preserving, with compatibility H ∘ i ≅ j ∘
F. Let R(X) and S(Y) be chosen finite-resolution families for i and j, and assume every i(P₀)
and j(Q₀) is projective. At X, the forward component identifies the homotopy object of
F(R(X).complex) with the transported resolution of H(X), then uses the chosen comparison over
id_{H(X)} to S(H(X)). -/
theorem finiteResolutionHomotopyFunctorNaturality_hom_app (e : i ⋙ H ≅ F ⋙ j)
    (R : ∀ X : A, FiniteResolution i X) (S : ∀ Y : B, FiniteResolution j Y)
    (hprojP : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojQ : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) :
    (finiteResolutionHomotopyFunctorNaturality F H e R S hprojP hprojQ).hom.app X =
      (F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).hom.app ((R X).complex) ≫
        (HomotopyCategory.quotient Q (ComplexShape.down ℕ)).map
          (comparisonHom (((R X).mapTarget H e).mapSource F (Iso.refl (F ⋙ j)))
            (S (H.obj X)) (𝟙 (H.obj X)) hprojQ).map :=
  rfl

/-- Let P,Q be preadditive, A,B abelian, and i : P → A and j : Q → B additive full faithful. Let F :
P → Q be additive and H : A → B additive and homology-preserving, with compatibility H ∘ i ≅ j ∘
F. Let R(X) and S(Y) be chosen finite-resolution families for i and j, and assume every i(P₀)
and j(Q₀) is projective. At X, the inverse component uses the chosen reverse identity comparison
from S(H(X)) to the transported F-image resolution, followed by the canonical homotopy-category
identification with F(R(X).complex). -/
theorem finiteResolutionHomotopyFunctorNaturality_inv_app (e : i ⋙ H ≅ F ⋙ j)
    (R : ∀ X : A, FiniteResolution i X) (S : ∀ Y : B, FiniteResolution j Y)
    (hprojP : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojQ : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) :
    (finiteResolutionHomotopyFunctorNaturality F H e R S hprojP hprojQ).inv.app X =
      (HomotopyCategory.quotient Q (ComplexShape.down ℕ)).map
          (comparisonHom (S (H.obj X))
            (((R X).mapTarget H e).mapSource F (Iso.refl (F ⋙ j)))
            (𝟙 (H.obj X)) hprojQ).map ≫
        (F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).inv.app ((R X).complex) :=
  rfl

end Naturality

end CategoryTheory.Abelian.FiniteResolution

end
