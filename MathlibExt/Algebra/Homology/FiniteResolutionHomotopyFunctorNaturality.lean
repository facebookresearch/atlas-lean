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
# Naturality of original finite-resolution homotopy functors

An compatibility isomorphism `i ⋙ H ≅ F ⋙ j` transports the given finite resolutions first along
the target functor and then along the source functor. The resulting complexes are the original
`F`-image complexes, with the original support bounds.

The stock homotopy-category factorization chart and the original chosen identity comparisons give
a natural isomorphism to a given target resolution family. Naturality follows from the transported
augmentation squares and constructive comparison uniqueness. The source and target resolving
images retain their explicit projectivity hypotheses.
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

/--
The represented source complex is the image of the original given-family complex under the source
functor.
-/
theorem finiteResolutionHomotopyFunctorNaturality_source_obj_as
    (F : P ⥤ Q) [F.Additive] (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    (((finiteResolutionHomotopyFunctor R hproj) ⋙
      F.mapHomotopyCategory (ComplexShape.down ℕ)).obj X).as =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (R X).complex :=
  rfl

/--
The represented source image retains the original object's inclusive support bound. The original
zero terms map to zero terms.
-/
theorem finiteResolutionHomotopyFunctorNaturality_source_isZero_above
    (F : P ⥤ Q) [F.Additive] (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n : ℕ) (hn : (R X).bound < n) :
    IsZero ((((finiteResolutionHomotopyFunctor R hproj) ⋙
      F.mapHomotopyCategory (ComplexShape.down ℕ)).obj X).as.X n) :=
  F.map_isZero ((R X).isZero_above n hn)

omit [Abelian A] in
/-- The represented target complex is the original target-family complex at the image object. -/
theorem finiteResolutionHomotopyFunctorNaturality_target_obj_as
    (H : A ⥤ B) (S : ∀ Y : B, FiniteResolution j Y)
    (hproj : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) :
    ((H ⋙ finiteResolutionHomotopyFunctor S hproj).obj X).as =
      (S (H.obj X)).complex :=
  rfl

omit [Abelian A] in
/-- The represented target complex retains its original object-dependent target-family support bound. -/
theorem finiteResolutionHomotopyFunctorNaturality_target_isZero_above
    (H : A ⥤ B) (S : ∀ Y : B, FiniteResolution j Y)
    (hproj : ∀ Q₀ : Q, Projective (j.obj Q₀)) (X : A) (n : ℕ)
    (hn : (S (H.obj X)).bound < n) :
    IsZero (((H ⋙ finiteResolutionHomotopyFunctor S hproj).obj X).as.X n) :=
  (S (H.obj X)).isZero_above n hn

section Naturality

variable (F : P ⥤ Q) [F.Additive] (H : A ⥤ B) [H.Additive] [H.PreservesHomology]

/--
An mixed source/target compatibility gives naturality of the same original resolution homotopy
functors. The components use the stock factorization chart and the original chosen identity
comparison maps.
-/
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

/--
The forward component is the stock factorization chart followed by the original chosen identity
comparison for the mixed resolution.
-/
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

/-- The inverse component uses the original reverse identity comparison
followed by the inverse of the same stock factorization chart. -/
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
