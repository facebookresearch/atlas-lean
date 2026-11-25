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

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Projective resolutions with finite terms

Finite generators give an actual finite free cover of every finite module.
The category of finite modules therefore has enough projectives. A projective
object in this category is a retract of its finite free cover, so it remains
projective after forgetting to the category of all modules.

Over a Noetherian ring the original finite-module category is abelian. Its
projective resolutions give resolutions in `ModuleCat` whose terms are all
finite. No finite projective dimension or termination is asserted. The ring
and the module carrier have independent universes.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe u v

namespace FGModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

/-- Every actual finite module has a surjection from a finite free module
in the original module universe. -/
theorem exists_finiteFree_cover (M : FGModuleCat.{v} R) :
    ∃ (P : FGModuleCat.{v} R) (f : P ⟶ M),
      Module.Free R P ∧ Function.Surjective f.hom.hom := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let P := Fin n →₀ Shrink.{v} R
  let e : P ≃ₗ[R] (Fin n →₀ R) :=
    Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)
  let b : Module.Basis (Fin n) R P :=
    (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R)).map e.symm
  let : Module.Free R P := Module.Free.of_basis b
  let : Module.Finite R P := Module.Finite.of_basis b
  let f : P →ₗ[R] M := (Finsupp.linearCombination R s).comp e.toLinearMap
  have hcomb : Function.Surjective (Finsupp.linearCombination R s) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hs
  exact ⟨FGModuleCat.of R P, FGModuleCat.ofHom f, inferInstance, hcomb.comp e.surjective⟩

/-- The actual finite free cover is a projective presentation in the
category of finite modules. -/
theorem exists_projectivePresentation (M : FGModuleCat.{v} R) :
    Nonempty (ProjectivePresentation M) := by
  obtain ⟨P, f, hfree, hf⟩ := exists_finiteFree_cover R M
  let : Module.Free R P := hfree
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  have hP : Projective P := by
    apply U.projective_of_map_projective
    change Projective P.obj
    infer_instance
  have huf : Epi (U.map f) :=
    (ModuleCat.epi_iff_surjective _).mpr hf
  let : Epi (U.map f) := huf
  have hf' : Epi f := Functor.epi_of_epi_map U (by infer_instance)
  exact ⟨{ p := P, projective := hP, f := f, epi := hf' }⟩

/-- Finite free covers earn enough projectives without a Noetherian
or finite projective dimension assumption. -/
theorem enoughProjectives : EnoughProjectives (FGModuleCat.{v} R) where
  presentation M := exists_projectivePresentation R M

/-- A projective finite-module object is an actual retract of its finite
free cover after forgetting, and hence is projective in `ModuleCat`. -/
theorem projective_toModuleCat (P : FGModuleCat.{v} R) [Projective P] :
    Projective P.obj := by
  obtain ⟨Q, f, hfree, hf⟩ := exists_finiteFree_cover R P
  let : Module.Free R Q := hfree
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let : Epi (U.map f) := (ModuleCat.epi_iff_surjective _).mpr hf
  let : Epi f := Functor.epi_of_epi_map U (by infer_instance)
  let i : P ⟶ Q := Projective.factorThru (𝟙 P) f
  have hi : i ≫ f = 𝟙 P := Projective.factorThru_comp (𝟙 P) f
  let r : Retract P.obj Q.obj :=
    { i := U.map i
      r := U.map f
      retract := by
        change U.map i ≫ U.map f = 𝟙 (U.obj P)
        rw [← U.map_comp, hi, U.map_id] }
  let : Projective Q.obj := inferInstance
  exact r.projective

/-- The actual finite-module forgetful functor preserves projective
objects through their finite free retracts. -/
theorem forget_preservesProjectiveObjects :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesProjectiveObjects where
  projective_obj hP := by
    let := hP
    exact projective_toModuleCat R _

variable [IsNoetherianRing R]

/-- Forget an original finite-module projective resolution along the
actual exact inclusion. Every resolving term remains the same module. -/
def toModuleCatProjectiveResolution {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) : ProjectiveResolution M.obj := by
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let : U.Additive := { map_add := fun {_ _} _ _ => rfl }
  let : U.PreservesProjectiveObjects := forget_preservesProjectiveObjects R
  let : U.PreservesHomology := inferInstance
  exact U.mapProjectiveResolution P

/-- The forgotten resolution retains the literal original underlying
module in every degree. -/
theorem toModuleCatProjectiveResolution_X {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    (toModuleCatProjectiveResolution R P).complex.X n = (P.complex.X n).obj := rfl

/-- The forgotten resolution retains the literal original differential
linear map in every pair of degrees. -/
theorem toModuleCatProjectiveResolution_d {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n m : ℕ) :
    ((toModuleCatProjectiveResolution R P).complex.d n m).hom =
      (P.complex.d n m).hom.hom := rfl

/-- Every degree of the forgotten original resolution is finite. -/
theorem toModuleCatProjectiveResolution_finite {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    Module.Finite R ((toModuleCatProjectiveResolution R P).complex.X n) := by
  rw [toModuleCatProjectiveResolution_X]
  exact (P.complex.X n).property

end FGModuleCat

namespace ModuleCat

variable (R : Type u) [Ring R] [IsNoetherianRing R] [Small.{v} R]

/-- The actual projective resolution of a finite module obtained from
the existing projective resolution in the category of finite modules.
Its terms are finite without a caller supplying a resolution. -/
def degreewiseFiniteProjectiveResolution (M : ModuleCat.{v} R) [Module.Finite R M] :
    ProjectiveResolution M := by
  let : EnoughProjectives (FGModuleCat.{v} R) := FGModuleCat.enoughProjectives R
  let N : FGModuleCat.{v} R := ⟨M, inferInstanceAs (Module.Finite R M)⟩
  exact FGModuleCat.toModuleCatProjectiveResolution R (projectiveResolution N)

/-- Every term of the constructed original resolution is a finite
module over the original ring. -/
theorem degreewiseFiniteProjectiveResolution_finite
    (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ) :
    Module.Finite R ((degreewiseFiniteProjectiveResolution R M).complex.X n) := by
  let : EnoughProjectives (FGModuleCat.{v} R) := FGModuleCat.enoughProjectives R
  let N : FGModuleCat.{v} R := ⟨M, inferInstanceAs (Module.Finite R M)⟩
  exact FGModuleCat.toModuleCatProjectiveResolution_finite R (projectiveResolution N) n

end ModuleCat
