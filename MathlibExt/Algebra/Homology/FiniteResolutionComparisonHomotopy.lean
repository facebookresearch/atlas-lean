/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionHomTransport

/-!
# Homotopy uniqueness and transport of finite-resolution comparisons

Let P be preadditive, A abelian and i : P → A additive full faithful. Two augmented
finite-resolution maps over the same base morphism are homotopic if the images of their
resolution terms are projective. Chosen comparison maps therefore preserve identities and
composition after passing to the homotopy category.

Additive source functors transport the resolving complexes and homotopies. Homology-preserving
target functors transport the augmentations while retaining the original resolving chain maps.
Compatibility isomorphisms identify the image terms, and the stated projectivity hypotheses give
comparison homotopies in the changed setting.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]
variable {X₁ X₂ X₃ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {R₃ : FiniteResolution i X₃}
variable {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. For two comparisons φ,ψ over the same f, assume each i(R₁,ₙ)
and i(R₂,ₙ) is projective, for all n ∈ ℕ. Then their resolving chain maps are homotopic in P. -/
def comparisonHomotopyOfProjectiveTerms [i.Full] [i.Faithful]
    (φ ψ : Hom R₁ R₂ f)
    (h₁ : ∀ n : ℕ, Projective (i.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (i.obj (R₂.complex.X n))) :
    Homotopy φ.map ψ.map := by
  let Q₁ : ProjectiveResolution X₁ :=
    { complex := R₁.mappedComplex
      projective := h₁
      π := R₁.augmentation
      quasiIso := R₁.quasiIso }
  let Q₂ : ProjectiveResolution X₂ :=
    { complex := R₂.mappedComplex
      projective := h₂
      π := R₂.augmentation
      quasiIso := R₂.quasiIso }
  apply i.preimageHomotopy
  exact ProjectiveResolution.liftHomotopy f (P := Q₁) (Q := Q₂)
    ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map)
    ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.map)
    φ.augmentation_comm ψ.augmentation_comm

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. Any two
augmented comparisons R₁ → R₂ over f have homotopic resolving chain maps. -/
def comparisonHomotopy [i.Full] [i.Faithful] (φ ψ : Hom R₁ R₂ f)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) : Homotopy φ.map ψ.map :=
  comparisonHomotopyOfProjectiveTerms φ ψ
    (fun n => hproj (R₁.complex.X n)) (fun n => hproj (R₂.complex.X n))

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. For a
finite resolution R of X₁, the chosen comparison over id_X₁ is homotopic to id_{R.complex}. -/
def comparisonHomotopyId [i.Full] [i.Faithful] (R : FiniteResolution i X₁)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R R (𝟙 X₁) hproj).map (𝟙 R.complex) :=
  comparisonHomotopy (comparisonHom R R (𝟙 X₁) hproj) (Hom.id R) hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. For a
third resolution R₃ of X₃ and g : X₂ → X₃, the chosen comparison over g ∘ f is homotopic to the
chosen comparison over f followed by that over g. -/
def comparisonHomotopyComp [i.Full] [i.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (R₃ : FiniteResolution i X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₃ (f ≫ g) hproj).map
      ((comparisonHom R₁ R₂ f hproj).map ≫ (comparisonHom R₂ R₃ g hproj).map) :=
  comparisonHomotopy (comparisonHom R₁ R₃ (f ≫ g) hproj)
    ((comparisonHom R₁ R₂ f hproj).comp (comparisonHom R₂ R₃ g hproj)) hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. In the
homotopy category of nonnegative complexes in P, the chosen comparison of R with itself over
id_X is the identity of [R.complex]. -/
theorem comparisonHom_quotient_id [i.Full] [i.Faithful] (R : FiniteResolution i X₁)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R R (𝟙 X₁) hproj).map =
      𝟙 ((HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj R.complex) := by
  simpa only [CategoryTheory.Functor.map_id] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyId R hproj)

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. The
homotopy class of the chosen comparison over g ∘ f is the composite of the homotopy classes of
the chosen comparisons over f and g. -/
theorem comparisonHom_quotient_comp [i.Full] [i.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (R₃ : FiniteResolution i X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R₁ R₃ (f ≫ g) hproj).map =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₁ R₂ f hproj).map ≫
        (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₂ R₃ g hproj).map := by
  simpa only [CategoryTheory.Functor.map_comp] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyComp R₁ R₂ R₃ f g hproj)

section SourceChange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {j : Q ⥤ A} [j.Additive]
variable (F : P ⥤ Q) [F.Additive] (e : F ⋙ j ≅ i)

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let Q be preadditive, j : Q → A additive, and F : P → Q additive with
compatibility e : j ∘ F ≅ i. A homotopy between two augmented resolving maps φ,ψ is sent by F to
a homotopy between their source-changed comparison maps, with the compatibility e supplying
their augmentations. -/
def Hom.mapSourceHomotopy (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map) :
    Homotopy (φ.mapSource F e).map (ψ.mapSource F e).map :=
  F.mapHomotopy h

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let Q be preadditive, j : Q → A additive, and F : P → Q additive with
compatibility e : j ∘ F ≅ i. The resolution-degree-(n,m) component of the transported homotopy
is F applied to the original homotopy component h(n,m). -/
theorem Hom.mapSourceHomotopy_hom (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map)
    (n m : ℕ) : (Hom.mapSourceHomotopy F e φ ψ h).hom n m = F.map (h.hom n m) :=
  rfl

/-- Let P,Q be preadditive, A abelian, i : P → A and j : Q → A additive, and F : P → Q additive with
jF ≅ i. For a finite resolution R of X and n ∈ ℕ, projectivity of i(Rₙ) implies projectivity of
j(F(Rₙ)), by the component of the compatibility isomorphism. -/
theorem mapSource_projective_term (R : FiniteResolution i X₁) (n : ℕ)
    (h : Projective (i.obj (R.complex.X n))) :
    Projective (j.obj ((R.mapSource F e).complex.X n)) :=
  Projective.of_iso (e.app (R.complex.X n)).symm h

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let Q be preadditive, j : Q → A additive, and F : P → Q additive with
compatibility e : j ∘ F ≅ i. Assume j is full faithful and the original image terms of R₁,R₂
under i are projective. The source transport of a comparison φ is homotopic to any augmented
comparison over f between the source-changed resolutions, because compatibility transports term
projectivity. -/
def sourceComparisonHomotopy [j.Full] [j.Faithful]
    (φ : Hom R₁ R₂ f) (ψ : Hom (R₁.mapSource F e) (R₂.mapSource F e) f)
    (h₁ : ∀ n : ℕ, Projective (i.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (i.obj (R₂.complex.X n))) :
    Homotopy (φ.mapSource F e).map ψ.map :=
  comparisonHomotopyOfProjectiveTerms (φ.mapSource F e) ψ
    (fun n => mapSource_projective_term F e R₁ n (h₁ n))
    (fun n => mapSource_projective_term F e R₂ n (h₂ n))

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. Let Q be
preadditive, j : Q → A additive, and F : P → Q additive with compatibility e : j ∘ F ≅ i. Assume
j is full faithful and every j(Q₀) is projective. The F-transport of the chosen original
comparison over f is homotopic to the chosen comparison between the source-changed finite
resolutions. -/
def comparisonHomotopySourceChange [i.Full] [i.Faithful] [j.Full] [j.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hprojP : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojQ : ∀ Q₀ : Q, Projective (j.obj Q₀)) :
    Homotopy ((comparisonHom R₁ R₂ f hprojP).mapSource F e).map
      (comparisonHom (R₁.mapSource F e) (R₂.mapSource F e) f hprojQ).map :=
  sourceComparisonHomotopy F e (comparisonHom R₁ R₂ f hprojP)
    (comparisonHom (R₁.mapSource F e) (R₂.mapSource F e) f hprojQ)
    (fun n => hprojP (R₁.complex.X n)) (fun n => hprojP (R₂.complex.X n))

end SourceChange

section TargetChange

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : P ⥤ B} [j.Additive]
variable (H : A ⥤ B) [H.Additive] [H.PreservesHomology] (e : i ⋙ H ≅ j)

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let B be abelian, j : P → B additive, and H : A → B additive and
homology-preserving, with compatibility e : H ∘ i ≅ j. Target transport leaves the resolving
complexes and their chain maps in P unchanged. Thus a homotopy h between φ and ψ is also a
homotopy between their target-changed comparison maps over H(f). -/
def Hom.mapTargetHomotopy (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map) :
    Homotopy (φ.mapTarget H e).map (ψ.mapTarget H e).map :=
  h

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let B be abelian, j : P → B additive, and H : A → B additive and
homology-preserving, with compatibility e : H ∘ i ≅ j. Every component h(n,m) of the original
homotopy remains the same morphism in P under target transport. -/
theorem Hom.mapTargetHomotopy_hom (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map)
    (n m : ℕ) : (Hom.mapTargetHomotopy H e φ ψ h).hom n m = h.hom n m :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose image commutes with
augmentation. Let B be abelian, j : P → B additive, and H : A → B additive and
homology-preserving, with compatibility e : H ∘ i ≅ j. Assume j is full faithful and the terms
of the two resolving complexes have projective j-images. The target transport of φ is homotopic
to any augmented comparison over H(f) between the target-changed resolutions. -/
def targetComparisonHomotopy [j.Full] [j.Faithful]
    (φ : Hom R₁ R₂ f)
    (ψ : Hom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f))
    (h₁ : ∀ n : ℕ, Projective (j.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (j.obj (R₂.complex.X n))) :
    Homotopy (φ.mapTarget H e).map ψ.map :=
  comparisonHomotopyOfProjectiveTerms (φ.mapTarget H e) ψ h₁ h₂

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. Let B be
abelian, j : P → B additive, and H : A → B additive and homology-preserving, with compatibility
e : H ∘ i ≅ j. Assume j is full faithful and every j(P₀) is projective. The target transport of
the chosen comparison over f is homotopic to the chosen comparison over H(f) between the
target-changed resolutions. -/
def comparisonHomotopyTargetChange [i.Full] [i.Faithful] [j.Full] [j.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hprojA : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojB : ∀ P₀ : P, Projective (j.obj P₀)) :
    Homotopy ((comparisonHom R₁ R₂ f hprojA).mapTarget H e).map
      (comparisonHom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f) hprojB).map :=
  targetComparisonHomotopy H e (comparisonHom R₁ R₂ f hprojA)
    (comparisonHom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f) hprojB)
    (fun n => hprojB (R₁.complex.X n)) (fun n => hprojB (R₂.complex.X n))

end TargetChange

end CategoryTheory.Abelian.FiniteResolution

end
