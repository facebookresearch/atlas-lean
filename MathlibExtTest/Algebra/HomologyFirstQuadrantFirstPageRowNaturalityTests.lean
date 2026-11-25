/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageRowNaturality

/-! # Tests for first-page row restriction naturality -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageRowNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFirstPageRowMapOfBicomplex
#check horizontalFirstPageRowMapOfBicomplex_f
#check horizontalFirstPageRowMapOfBicomplex_id
#check horizontalFirstPageRowMapOfBicomplex_comp
#check horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex

example (f : K ⟶ L) (q : ℕ) :
    horizontalFirstPageRowComplex K q ⟶
      horizontalFirstPageRowComplex L q :=
  horizontalFirstPageRowMapOfBicomplex f q

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f q).f p =
      (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) :=
  horizontalFirstPageRowMapOfBicomplex_f f p q

example (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex (𝟙 K) q = 𝟙 _ :=
  horizontalFirstPageRowMapOfBicomplex_id K q

example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex (f ≫ g) q =
      horizontalFirstPageRowMapOfBicomplex f q ≫
        horizontalFirstPageRowMapOfBicomplex g q :=
  horizontalFirstPageRowMapOfBicomplex_comp f g q

example (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (by omega)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso L p q).inv =
      (horizontalFirstPageRowHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) p :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex f p q

example (f : K ⟶ L) (q : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f q).f 0 =
      (horizontalPageMapOfBicomplex f 1 (by omega)).f (0, q) :=
  horizontalFirstPageRowMapOfBicomplex_f f 0 q

example (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f 0).f p =
      (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, 0) :=
  horizontalFirstPageRowMapOfBicomplex_f f p 0

example (f : K ⟶ L) :
    (horizontalFirstPageRowMapOfBicomplex f 0).f 0 =
      (horizontalPageMapOfBicomplex f 1 (by omega)).f (0, 0) :=
  horizontalFirstPageRowMapOfBicomplex_f f 0 0

example (f : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (by omega)) (0, q) ≫
        (horizontalFirstPageRowHomologyIso L 0 q).inv =
      (horizontalFirstPageRowHomologyIso K 0 q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) 0 :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex f 0 q

example (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (by omega)) (p, 0) ≫
        (horizontalFirstPageRowHomologyIso L p 0).inv =
      (horizontalFirstPageRowHomologyIso K p 0).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f 0) p :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex f p 0

example (f : K ⟶ L) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (by omega)) (0, 0) ≫
        (horizontalFirstPageRowHomologyIso L 0 0).inv =
      (horizontalFirstPageRowHomologyIso K 0 0).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f 0) 0 :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex f 0 0

example (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex (𝟙 K) 1 (by omega)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso K p q).inv =
      (horizontalFirstPageRowHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex (𝟙 K) q) p :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex (f ≫ g) 1 (by omega)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso M p q).inv =
      (horizontalFirstPageRowHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex (f ≫ g) q) p :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex
    (f ≫ g) p q

example (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex
            (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
              (ComplexShape.down ℕ) (ComplexShape.down ℕ)))
            1 (by omega)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso
          (HomologicalComplex.zero : HomologicalComplex₂ C
            (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p q).inv =
      (horizontalFirstPageRowHomologyIso
        (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex
            (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
              (ComplexShape.down ℕ) (ComplexShape.down ℕ))) q) p :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex _ p q

section ZeroRing

variable {K₀ L₀ : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K₀ ⟶ L₀) (p q : ℕ) :=
  horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex f p q

end ZeroRing

#print axioms horizontalFirstPageRowMapOfBicomplex
#print axioms horizontalFirstPageRowMapOfBicomplex_f
#print axioms horizontalFirstPageRowMapOfBicomplex_id
#print axioms horizontalFirstPageRowMapOfBicomplex_comp
#print axioms horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantFirstPageRowNaturalityTests

end
