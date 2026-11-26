/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.ExactCategory.FiniteResolving
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Augmented comparisons of finite resolutions

Let P be preadditive, A abelian and i : P → A additive. A morphism between finite resolutions
over f : X₁ → X₂ is a chain map of resolving complexes whose image under i commutes with the
augmentations. These morphisms have identity and composition operations.

If i is full faithful and every i(P₀) is projective, projective-resolution comparison maps in A
return augmented comparisons in P. Two finite resolutions of the same object then have
homotopy-equivalent resolving complexes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe vP uP vA uA

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
in A, by nonnegative complexes in P, and f : X₁ → X₂. A comparison over f is a chain map φ :
R₁.complex → R₂.complex whose image under i commutes with the augmentations: ε₂ ∘ i(φ)=f[0] ∘
ε₁. -/
structure Hom {X₁ X₂ : A}
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (f : X₁ ⟶ X₂) where
  /-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
in A, by nonnegative complexes in P, and f : X₁ → X₂. The chain-map component of a comparison
over f is a morphism R₁.complex → R₂.complex in the resolving category P. -/
  map : R₁.complex ⟶ R₂.complex
  /-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
in A, by nonnegative complexes in P, and f : X₁ → X₂. The comparison φ satisfies ε₂ ∘ i(φ)=f[0]
∘ ε₁, as maps from i(R₁.complex) to the nonnegative complex concentrated on X₂. -/
  augmentation_comm :
    (i.mapHomologicalComplex (ComplexShape.down ℕ)).map map ≫
        R₂.augmentation =
      R₁.augmentation ≫ (ChainComplex.single₀ A).map f

namespace Hom

variable {X₁ X₂ X₃ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {R₃ : FiniteResolution i X₃}
variable {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}

/-- Let P be preadditive, A abelian and i : P → A additive. For a finite resolution R of X, the
identity comparison over id_X has chain map id_{R.complex} and the identity augmentation square. -/
def id (R : FiniteResolution i X₁) : Hom R R (𝟙 X₁) where
  map := 𝟙 R.complex
  augmentation_comm := by simp

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
in A, by nonnegative complexes in P, and f : X₁ → X₂. For a third resolution R₃ of X₃ and g : X₂
→ X₃, comparisons φ : R₁ → R₂ over f and ψ : R₂ → R₃ over g compose to a comparison over g ∘ f,
with chain map ψ ∘ φ. -/
def comp (φ : Hom R₁ R₂ f) (ψ : Hom R₂ R₃ g) :
    Hom R₁ R₃ (f ≫ g) where
  map := φ.map ≫ ψ.map
  augmentation_comm := by
    simp only [Functor.map_comp]
    rw [Category.assoc, ψ.augmentation_comm]
    rw [← Category.assoc, φ.augmentation_comm]
    rw [Category.assoc, ← Functor.map_comp]

end Hom

/-- Let P be preadditive, A abelian and i : P → A additive. Let R be a finite resolution of X and
assume i(P₀) is projective for every resolving object P₀ of P. Then i(R.complex), with its
original augmentation, is a projective resolution of X in A. -/
noncomputable def toProjectiveResolution {X : A}
    (R : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    ProjectiveResolution X where
  complex := R.mappedComplex
  projective n := hproj (R.complex.X n)
  π := R.augmentation
  quasiIso := R.quasiIso

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of X₁,X₂
in A, by nonnegative complexes in P, and f : X₁ → X₂. Assume i is full faithful and every i(P₀)
is projective. A projective-resolution lift in A lifts back to an augmented comparison R₁ → R₂
over f in P. -/
noncomputable def comparisonHom [i.Full] [i.Faithful]
    {X₁ X₂ : A} (R₁ : FiniteResolution i X₁)
    (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) : Hom R₁ R₂ f := by
  let F := i.mapHomologicalComplex (ComplexShape.down ℕ)
  let Q₁ := R₁.toProjectiveResolution hproj
  let Q₂ := R₂.toProjectiveResolution hproj
  let φ : R₁.complex ⟶ R₂.complex :=
    F.preimage (ProjectiveResolution.lift f Q₁ Q₂)
  have hφ : F.map φ = ProjectiveResolution.lift f Q₁ Q₂ :=
    F.map_preimage _
  refine { map := φ, augmentation_comm := ?_ }
  change F.map φ ≫ R₂.augmentation = _
  rw [hφ]
  exact ProjectiveResolution.lift_commutes f Q₁ Q₂

/-- Let P be preadditive, A abelian and i : P → A additive full faithful, with every i(P₀)
projective. Two finite resolutions R₁,R₂ of the same object X have homotopy-equivalent resolving
complexes in P. -/
noncomputable def comparisonHomotopyEquiv [i.Full] [i.Faithful]
    {X : A} (R₁ R₂ : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    HomotopyEquiv R₁.complex R₂.complex := by
  let F := i.mapHomologicalComplex (ComplexShape.down ℕ)
  let Q₁ := R₁.toProjectiveResolution hproj
  let Q₂ := R₂.toProjectiveResolution hproj
  let eA : HomotopyEquiv (F.obj R₁.complex) (F.obj R₂.complex) :=
    ProjectiveResolution.homotopyEquiv Q₁ Q₂
  let hom : R₁.complex ⟶ R₂.complex := F.preimage eA.hom
  let inv : R₂.complex ⟶ R₁.complex := F.preimage eA.inv
  refine
    { hom := hom
      inv := inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · apply i.preimageHomotopy
    simpa [F, hom, inv] using eA.homotopyHomInvId
  · apply i.preimageHomotopy
    simpa [F, hom, inv] using eA.homotopyInvHomId

end CategoryTheory.Abelian.FiniteResolution

end
