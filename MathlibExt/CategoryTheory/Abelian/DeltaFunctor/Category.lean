/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Basic
public import MathlibExt.CategoryTheory.Dialgebra.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Categories and degree evaluation of δ-functors

A morphism of δ-functors is a family of natural transformations compatible
with connecting maps. A graded dialgebra category provides this category
structure and its degree-evaluation functors.

## References

* C. Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.1.4.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace DeltaFunctor

variable (A : Type u₁) [Category.{v₁} A] [HasZeroMorphisms A]
variable (B : Type u₂) [Category.{v₂} B]

/-- Reindex a graded family of functors and pull it back along an object functor. -/
def degreeWhiskering (P : ShortComplex.ShortExactSequences A ⥤ A) (i : ℕ → ℕ) :
    (ℕ → (A ⥤ B)) ⥤ (ℕ → (ShortComplex.ShortExactSequences A ⥤ B)) :=
  Pi.comap (fun _ : ℕ => A ⥤ B) i ⋙
    Functor.pi (fun _ : ℕ => (Functor.whiskeringLeft _ A B).obj P)

/-- Graded systems of natural connecting maps with prescribed source and target degrees. -/
abbrev System (sourceDegree targetDegree : ℕ → ℕ) :=
  Dialgebra
    (degreeWhiskering A B ((ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₃)
      sourceDegree)
    (degreeWhiskering A B ((ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₁)
      targetDegree)

namespace System

variable {A B} {sourceDegree targetDegree : ℕ → ℕ}
variable {X Y : System A B sourceDegree targetDegree}

/-- Construct a morphism from its degree maps and pointwise connecting-map compatibility. -/
def homMk (f : ∀ n, X.A n ⟶ Y.A n)
    (hf : ∀ n (S : ShortComplex.ShortExactSequences A),
      (X.a n).app S ≫ (f (targetDegree n)).app S.obj.X₁ =
        (f (sourceDegree n)).app S.obj.X₃ ≫ (Y.a n).app S) : X ⟶ Y where
  f := f
  h := by
    funext n
    apply NatTrans.ext
    funext S
    exact (hf n S).symm

/-- The compatibility equation at a chosen degree and short exact sequence. -/
theorem comm (f : X ⟶ Y) (n : ℕ) (S : ShortComplex.ShortExactSequences A) :
    (X.a n).app S ≫ (f.f (targetDegree n)).app S.obj.X₁ =
      (f.f (sourceDegree n)).app S.obj.X₃ ≫ (Y.a n).app S := by
  have h := congrArg (fun η => (η n).app S) f.h
  exact h.symm

end System

end DeltaFunctor

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
variable (B : Type u₂) [Category.{v₂} B] [Preadditive B]

namespace HomologicalDeltaFunctor

/-- Forget exactness, retaining the degree functors and connecting maps. -/
def toSystem (D : HomologicalDeltaFunctor A B) :
    DeltaFunctor.System A B (fun n => n + 1) id where
  A := D.T
  a := D.connecting

instance : Category (HomologicalDeltaFunctor A B) :=
  inferInstanceAs (Category (InducedCategory _ (toSystem A B)))

/-- Morphisms of homological δ-functors. -/
abbrev Hom (S T : HomologicalDeltaFunctor A B) := S ⟶ T

namespace Hom

variable {A B} {S T : HomologicalDeltaFunctor A B}

/-- The natural transformation in a chosen degree. -/
abbrev app (f : Hom A B S T) (n : ℕ) : S.T n ⟶ T.T n := f.hom.f n

/-- The degree map of the identity is the identity natural transformation. -/
@[simp]
theorem id_app (S : HomologicalDeltaFunctor A B) (n : ℕ) : app (𝟙 S) n = 𝟙 (S.T n) :=
  rfl

/-- Degree maps preserve composition of δ-functor morphisms. -/
@[simp]
theorem comp_app {R : HomologicalDeltaFunctor A B} (f : S ⟶ T) (g : T ⟶ R) (n : ℕ) :
    app (f ≫ g) n = app f n ≫ app g n := rfl

end Hom

/-- Construct a homological δ-functor morphism from compatible degree maps. -/
def homMk {S T : HomologicalDeltaFunctor A B} (f : ∀ n, S.T n ⟶ T.T n)
    (hf : ∀ n (Z : ShortComplex.ShortExactSequences A),
      (S.connecting n).app Z ≫ (f n).app Z.obj.X₁ =
        (f (n + 1)).app Z.obj.X₃ ≫ (T.connecting n).app Z) : S ⟶ T :=
  InducedCategory.homMk (DeltaFunctor.System.homMk f hf)

/-- A morphism is determined by its degree maps. -/
@[ext]
theorem hom_ext {S T : HomologicalDeltaFunctor A B} {f g : S ⟶ T}
    (h : ∀ n, Hom.app f n = Hom.app g n) : f = g :=
  InducedCategory.hom_ext (Dialgebra.Hom.ext (funext h))

/-- Evaluate a homological δ-functor in one degree. -/
@[simps]
def evaluation (n : ℕ) : HomologicalDeltaFunctor A B ⥤ (A ⥤ B) where
  obj D := D.T n
  map f := Hom.app f n

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- Forget exactness, retaining the degree functors and connecting maps. -/
def toSystem (D : CohomologicalDeltaFunctor A B) :
    DeltaFunctor.System A B id (fun n => n + 1) where
  A := D.T
  a := D.connecting

instance : Category (CohomologicalDeltaFunctor A B) :=
  inferInstanceAs (Category (InducedCategory _ (toSystem A B)))

/-- Morphisms of cohomological δ-functors. -/
abbrev Hom (S T : CohomologicalDeltaFunctor A B) := S ⟶ T

namespace Hom

variable {A B} {S T : CohomologicalDeltaFunctor A B}

/-- The natural transformation in a chosen degree. -/
abbrev app (f : Hom A B S T) (n : ℕ) : S.T n ⟶ T.T n := f.hom.f n

/-- The degree map of the identity is the identity natural transformation. -/
@[simp]
theorem id_app (S : CohomologicalDeltaFunctor A B) (n : ℕ) : app (𝟙 S) n = 𝟙 (S.T n) :=
  rfl

/-- Degree maps preserve composition of δ-functor morphisms. -/
@[simp]
theorem comp_app {R : CohomologicalDeltaFunctor A B} (f : S ⟶ T) (g : T ⟶ R) (n : ℕ) :
    app (f ≫ g) n = app f n ≫ app g n := rfl

end Hom

/-- Construct a cohomological δ-functor morphism from compatible degree maps. -/
def homMk {S T : CohomologicalDeltaFunctor A B} (f : ∀ n, S.T n ⟶ T.T n)
    (hf : ∀ n (Z : ShortComplex.ShortExactSequences A),
      (S.connecting n).app Z ≫ (f (n + 1)).app Z.obj.X₁ =
        (f n).app Z.obj.X₃ ≫ (T.connecting n).app Z) : S ⟶ T :=
  InducedCategory.homMk (DeltaFunctor.System.homMk f hf)

/-- A morphism is determined by its degree maps. -/
@[ext]
theorem hom_ext {S T : CohomologicalDeltaFunctor A B} {f g : S ⟶ T}
    (h : ∀ n, Hom.app f n = Hom.app g n) : f = g :=
  InducedCategory.hom_ext (Dialgebra.Hom.ext (funext h))

/-- Evaluate a cohomological δ-functor in one degree. -/
@[simps]
def evaluation (n : ℕ) : CohomologicalDeltaFunctor A B ⥤ (A ⥤ B) where
  obj D := D.T n
  map f := Hom.app f n

end CohomologicalDeltaFunctor

end CategoryTheory
