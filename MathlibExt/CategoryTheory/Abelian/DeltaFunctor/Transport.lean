/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Universal
public import MathlibExt.CategoryTheory.Dialgebra.Iso

/-!
# Changing degree functors of a δ-functor

Natural isomorphisms of the degree functors conjugate the connecting maps
by their endpoint components. The resulting δ-functor is isomorphic to the
original and has the same universality property. Exactness transfers through
the corresponding short-complex isomorphisms.

## References

* C. Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.1.4.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace DeltaFunctor.System

variable {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]
variable {B : Type u₂} [Category.{v₂} B]
variable {sourceDegree targetDegree : ℕ → ℕ}

/-- Replace the degree family of a graded connecting system by naturally
isomorphic functors. -/
def transport (X : DeltaFunctor.System A B sourceDegree targetDegree)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ X.A n) :
    DeltaFunctor.System A B sourceDegree targetDegree where
  A := T
  a :=
    (degreeWhiskering A B ((ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₃)
      sourceDegree).map (Pi.isoMk e).hom ≫ X.a ≫
      (degreeWhiskering A B ((ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₁)
        targetDegree).map (Pi.isoMk e).inv

/-- The transported system has the prescribed degree family. -/
@[simp]
theorem transport_A (X : DeltaFunctor.System A B sourceDegree targetDegree)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ X.A n) :
    (transport X T e).A = T := rfl

/-- The connecting components are conjugated by the degree isomorphisms. -/
@[simp]
theorem transport_a_app (X : DeltaFunctor.System A B sourceDegree targetDegree)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ X.A n) (n : ℕ)
    (S : ShortComplex.ShortExactSequences A) :
    ((transport X T e).a n).app S =
      (e (sourceDegree n)).hom.app S.obj.X₃ ≫ (X.a n).app S ≫
        (e (targetDegree n)).inv.app S.obj.X₁ := rfl

/-- The degree isomorphisms form an isomorphism of connecting systems. -/
def transportIso (X : DeltaFunctor.System A B sourceDegree targetDegree)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ X.A n) : transport X T e ≅ X := by
  refine Dialgebra.isoMk (Pi.isoMk e) ?_
  simp only [transport, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id]

end DeltaFunctor.System

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]

namespace DeltaFunctor

private theorem exists_exact_of_iso {S : ShortComplex B} (hS : S.Exact)
    {X₁ X₂ X₃ : B} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    (e₁ : X₁ ≅ S.X₁) (e₂ : X₂ ≅ S.X₂) (e₃ : X₃ ≅ S.X₃)
    (hf : e₁.hom ≫ S.f = f ≫ e₂.hom)
    (hg : e₂.hom ≫ S.g = g ≫ e₃.hom) :
    ∃ w : f ≫ g = 0,
      (ShortComplex.mk _ _ w).Exact := by
  have w : f ≫ g = 0 := by
    apply (cancel_mono e₃.hom).1
    rw [Category.assoc, ← hg, ← Category.assoc, ← hf, Category.assoc,
      S.zero, comp_zero, zero_comp]
  refine ⟨w, ?_⟩
  let ε : ShortComplex.mk _ _ w ≅ S :=
    ShortComplex.isoMk e₁ e₂ e₃ hf hg
  exact ShortComplex.exact_of_iso ε.symm hS

end DeltaFunctor

namespace HomologicalDeltaFunctor

/-- Replace the degree functors of a homological δ-functor by specified
naturally isomorphic functors. -/
def transport (D : HomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : HomologicalDeltaFunctor A B where
  T := T
  additive n := Functor.additive_of_iso (e n).symm
  connecting := (DeltaFunctor.System.transport (toSystem A B D) T e).a
  exactLeft n S := by
    obtain ⟨_w, hw⟩ := D.exactLeft n S
    refine DeltaFunctor.exists_exact_of_iso hw
      ((e (n + 1)).app S.obj.X₃) ((e n).app S.obj.X₁) ((e n).app S.obj.X₂) ?_ ?_
    · exact (DeltaFunctor.System.comm
        (DeltaFunctor.System.transportIso (toSystem A B D) T e).hom n S).symm
    · exact ((e n).hom.naturality S.obj.f).symm
  exactMiddle n S := by
    obtain ⟨_w, hw⟩ := D.exactMiddle n S
    exact DeltaFunctor.exists_exact_of_iso hw
      ((e n).app S.obj.X₁) ((e n).app S.obj.X₂) ((e n).app S.obj.X₃)
      ((e n).hom.naturality S.obj.f).symm ((e n).hom.naturality S.obj.g).symm
  exactRight n S := by
    obtain ⟨_w, hw⟩ := D.exactRight n S
    refine DeltaFunctor.exists_exact_of_iso hw
      ((e (n + 1)).app S.obj.X₂) ((e (n + 1)).app S.obj.X₃) ((e n).app S.obj.X₁) ?_ ?_
    · exact ((e (n + 1)).hom.naturality S.obj.g).symm
    · exact (DeltaFunctor.System.comm
        (DeltaFunctor.System.transportIso (toSystem A B D) T e).hom n S).symm
  epiZero S := by
    have : Epi ((D.T 0).map S.obj.g) := D.epiZero S
    rw [← NatIso.naturality_2 (e 0) S.obj.g]
    infer_instance

/-- Degree-family transport is an isomorphism of homological δ-functors. -/
def transportIso (D : HomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : transport D T e ≅ D :=
  InducedCategory.isoMk (DeltaFunctor.System.transportIso (toSystem A B D) T e)

/-- Degree evaluation of the transport is the supplied natural isomorphism. -/
@[simp]
theorem transportIso_hom_app (D : HomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) (n : ℕ) :
    Hom.app (transportIso D T e).hom n = (e n).hom := rfl

/-- The transported family is exactly the specified family. -/
@[simp]
theorem transport_T (D : HomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : (transport D T e).T = T := rfl

/-- The homological connecting component has the prescribed conjugation. -/
@[simp]
theorem transport_connecting_app (D : HomologicalDeltaFunctor A B)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ D.T n) (n : ℕ)
    (S : ShortComplex.ShortExactSequences A) :
    ((transport D T e).connecting n).app S =
      (e (n + 1)).hom.app S.obj.X₃ ≫ (D.connecting n).app S ≫
        (e n).inv.app S.obj.X₁ := rfl

/-- Universality is preserved by degree-family transport. -/
theorem isUniversal_transport (D : HomologicalDeltaFunctor A B)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ D.T n) (hD : IsUniversal A B D) :
    IsUniversal A B (transport D T e) :=
  isUniversal_of_iso A B hD (transportIso D T e)

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- Replace the degree functors of a cohomological δ-functor by specified
naturally isomorphic functors. -/
def transport (D : CohomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : CohomologicalDeltaFunctor A B where
  T := T
  additive n := Functor.additive_of_iso (e n).symm
  connecting := (DeltaFunctor.System.transport (toSystem A B D) T e).a
  exactLeft n S := by
    obtain ⟨_w, hw⟩ := D.exactLeft n S
    refine DeltaFunctor.exists_exact_of_iso hw
      ((e n).app S.obj.X₃) ((e (n + 1)).app S.obj.X₁) ((e (n + 1)).app S.obj.X₂) ?_ ?_
    · exact (DeltaFunctor.System.comm
        (DeltaFunctor.System.transportIso (toSystem A B D) T e).hom n S).symm
    · exact ((e (n + 1)).hom.naturality S.obj.f).symm
  exactMiddle n S := by
    obtain ⟨_w, hw⟩ := D.exactMiddle n S
    exact DeltaFunctor.exists_exact_of_iso hw
      ((e n).app S.obj.X₁) ((e n).app S.obj.X₂) ((e n).app S.obj.X₃)
      ((e n).hom.naturality S.obj.f).symm ((e n).hom.naturality S.obj.g).symm
  exactRight n S := by
    obtain ⟨_w, hw⟩ := D.exactRight n S
    refine DeltaFunctor.exists_exact_of_iso hw
      ((e n).app S.obj.X₂) ((e n).app S.obj.X₃) ((e (n + 1)).app S.obj.X₁) ?_ ?_
    · exact ((e n).hom.naturality S.obj.g).symm
    · exact (DeltaFunctor.System.comm
        (DeltaFunctor.System.transportIso (toSystem A B D) T e).hom n S).symm
  monoZero S := by
    have : Mono ((D.T 0).map S.obj.f) := D.monoZero S
    rw [← NatIso.naturality_2 (e 0) S.obj.f]
    infer_instance

/-- Degree-family transport is an isomorphism of cohomological δ-functors. -/
def transportIso (D : CohomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : transport D T e ≅ D :=
  InducedCategory.isoMk (DeltaFunctor.System.transportIso (toSystem A B D) T e)

/-- Degree evaluation of the transport is the supplied natural isomorphism. -/
@[simp]
theorem transportIso_hom_app (D : CohomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) (n : ℕ) :
    Hom.app (transportIso D T e).hom n = (e n).hom := rfl

/-- The transported family is exactly the specified family. -/
@[simp]
theorem transport_T (D : CohomologicalDeltaFunctor A B) (T : ℕ → (A ⥤ B))
    (e : ∀ n, T n ≅ D.T n) : (transport D T e).T = T := rfl

/-- The cohomological connecting component has the prescribed conjugation. -/
@[simp]
theorem transport_connecting_app (D : CohomologicalDeltaFunctor A B)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ D.T n) (n : ℕ)
    (S : ShortComplex.ShortExactSequences A) :
    ((transport D T e).connecting n).app S =
      (e n).hom.app S.obj.X₃ ≫ (D.connecting n).app S ≫
        (e (n + 1)).inv.app S.obj.X₁ := rfl

/-- Universality is preserved by degree-family transport. -/
theorem isUniversal_transport (D : CohomologicalDeltaFunctor A B)
    (T : ℕ → (A ⥤ B)) (e : ∀ n, T n ≅ D.T n) (hD : IsUniversal A B D) :
    IsUniversal A B (transport D T e) :=
  isUniversal_of_iso A B hD (transportIso D T e)

end CohomologicalDeltaFunctor

end CategoryTheory
