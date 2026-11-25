/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeLefschetz

@[expose] public section

/-!
# Tests for the relative Lefschetz operators

The zeroth shifted power of a degree-two map is the canonical identification
`K ≅ K⟦0⟧`, its first power is the map itself followed by the canonical
identification of shifts, and the powers of the zero map vanish from the first
on. The relative projective space lies over its base and over `ℙⁿ`, and the
classifying map of a relative embedding factors through it. For `k = 0` the
pulled-back and pushed-forward hyperplane powers are isomorphisms, and the
perverse power map of an isomorphism is an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.RelativeLefschetz

namespace MathlibExtTest.AlgebraicGeometry.RelativeLefschetz

attribute [local instance] HasDerivedCategory.standard

section Power

variable {C : Type*} [Category* C] [HasShift C ℤ] (K : C) (η : K ⟶ K⟦(2 : ℤ)⟧)

/-- The zeroth power is the canonical identification `K ≅ K⟦0⟧`. -/
example : degreeTwoPower K η 0 = (shiftFunctorZero C ℤ).inv.app K := rfl

example : IsIso (degreeTwoPower K η 0) := by
  rw [degreeTwoPower]
  infer_instance

/-- The first power is `η` followed by canonical identifications of shifts. -/
example : degreeTwoPower K η 1 =
    (shiftFunctorZero C ℤ).inv.app K ≫ η⟦2 * ((0 : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' C (2 : ℤ) (2 * ((0 : ℕ) : ℤ)) (2 * ((0 + 1 : ℕ) : ℤ))
        (by omega)).inv.app K := rfl

/-- The powers of the zero map vanish from the first on. -/
example [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] (k : ℕ) :
    degreeTwoPower K 0 (k + 1) = 0 := by
  simp [degreeTwoPower]

end Power

/-- The relative projective space lies over the base. -/
example (Y : PerverseSheaves.ComplexScheme) (n : ℕ) :
    (relativeProjectiveSpace Y n).hom = (toBase Y n).left ≫ Y.hom := rfl

/-- Its projection to `ℙⁿ` is compatible with the structure maps. -/
example (Y : PerverseSheaves.ComplexScheme) (n : ℕ) :
    (toProjectiveSpace Y n).left ≫ (ProjectiveSpace.projectiveSpace ℂ n).hom =
      (relativeProjectiveSpace Y n).hom :=
  (toProjectiveSpace Y n).w

/-- The classifying map of a relative embedding is the embedding followed by
the projection to `ℙⁿ`. -/
example {X Y : PerverseSheaves.ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) :
    E.classifyingMap = E.embedding ≫ toProjectiveSpace Y n := rfl

/-- The embedding lies over `Y`. -/
example {X Y : PerverseSheaves.ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) : E.embedding ≫ toBase Y n = f := E.over

section Pipeline

variable {X Y : PerverseSheaves.ComplexScheme} {f : X ⟶ Y} {n : ℕ}
  (E : RelativeProjectiveEmbedding f n) (d : ℕ)
  (η : unitComplex (ProjectiveSpace.projectiveSpace ℂ n) ⟶ (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦(2 : ℤ)⟧)
  (C : HyperplaneComparisons E d 0)

/-- For `k = 0` the pulled-back power is a composite of identifications, hence an
isomorphism. -/
theorem isIso_hyperplanePullbackMap_zero : IsIso (hyperplanePullbackMap E d 0 η C) := by
  unfold hyperplanePullbackMap degreeTwoPower
  infer_instance

/-- For `k = 0` its direct image is an isomorphism. -/
example : IsIso (hyperplaneImageMap E d 0 η C) := by
  have key : ∀ g : DerivedCategory.Plus.ι.obj (constantInput X d) ⟶
      DerivedCategory.Plus.ι.obj (constantInput X (d + 2 * 0)), IsIso g →
      IsIso ((ConstructibleComplexes.derivedPushforwardPlus ℚ f).map
        (DerivedCategory.Plus.ι.preimage g) ≫ C.directImageTarget.hom) := by
    intro g hg
    have h1 : IsIso (DerivedCategory.Plus.ι.preimage g) := by
      rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι, Functor.map_preimage]
      exact hg
    have h2 : IsIso ((ConstructibleComplexes.derivedPushforwardPlus ℚ f).map
        (DerivedCategory.Plus.ι.preimage g)) :=
      Functor.map_isIso (ConstructibleComplexes.derivedPushforwardPlus ℚ f) _
    exact IsIso.comp_isIso' h2 (Iso.isIso_hom _)
  exact key _ (isIso_hyperplanePullbackMap_zero E d η C)

end Pipeline

/-- For `k = 0` the perverse power map of an isomorphism is an isomorphism. -/
example (Y : PerverseSheaves.ComplexScheme) [IsComplexVariety Y] [PerverseSheafTheory Y]
    (K : (boundedConstructible Y).FullSubcategory)
    (u : K.obj ⟶ K.obj⟦2 * ((0 : ℕ) : ℤ)⟧) [IsIso u] :
    IsIso (perversePowerMap Y K 0 u) := by
  let I := (boundedConstructible Y).ι
  let v : I.obj (K⟦-((0 : ℕ) : ℤ)⟧) ⟶ I.obj (K⟦((0 : ℕ) : ℤ)⟧) :=
    ((I.commShiftIso (-((0 : ℕ) : ℤ))).app K).hom ≫ u⟦-((0 : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' (RationalDerived (ComplexAnalytification.space Y)) (2 * ((0 : ℕ) : ℤ))
        (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) (by omega)).inv.app K.obj ≫
      ((I.commShiftIso ((0 : ℕ) : ℤ)).app K).inv
  have : IsIso (I.map (I.preimage v)) := by
    rw [Functor.map_preimage]
    dsimp only [v]
    infer_instance
  have : IsIso (I.preimage v) := isIso_of_fully_faithful I _
  have : IsIso ((perverseTStructure Y).heart.ι.map (perversePowerMap Y K 0 u)) :=
    Functor.map_isIso ((perverseTStructure Y).truncGELE 0 0) (I.preimage v)
  exact isIso_of_fully_faithful (perverseTStructure Y).heart.ι _

end MathlibExtTest.AlgebraicGeometry.RelativeLefschetz
