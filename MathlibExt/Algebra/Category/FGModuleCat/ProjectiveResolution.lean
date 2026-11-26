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
# Projective resolutions with finitely generated terms

Let R be a ring in universe u whose carrier admits a representative in the module universe v.
Every finitely generated left R-module in v has a surjection from a finite free module in v.
These covers give enough projectives in the category of finitely generated modules. A projective
object of that category is a retract of its finite free cover, so it remains projective in the
category of all R-modules.

If R is Noetherian, the finitely generated module category is abelian and its inclusion into all
modules is exact. Applying this inclusion to a projective resolution preserves the underlying
modules, differentials, and augmentation. Every resolving term remains finitely generated. Thus
each finitely generated R-module has a projective resolution with finitely generated terms in
all nonnegative degrees.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe u v

namespace FGModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. For M, there exist a finitely generated module P
and an R-linear morphism f:P→M such that P is free and f is surjective. P has a finite basis,
obtained from a finite generating family of M. -/
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

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Every object M has a projective presentation P --f→
M with P projective in the finitely generated module category and f epi. A finite free cover
supplies P and the surjective morphism f. -/
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

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. The category FGModuleCat_v(R) has enough
projectives: every object M receives an epimorphism from a projective object P. The
presentations can be chosen from finite free covers, and this conclusion does not require
Noetherianity. -/
theorem enoughProjectives : EnoughProjectives (FGModuleCat.{v} R) where
  presentation M := exists_projectivePresentation R M

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. For P∈FGModuleCat_v(R) that is projective in that
category, its underlying module is a projective object of ModuleCat_v(R). Its finite free cover
splits by projectivity of P, giving a retract of a finite free module after forgetting. -/
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

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. The inclusion U:FGModuleCat_v(R)→ModuleCat_v(R)
preserves projective objects. For each projective P, U(P) is the same underlying R-module and is
a retract of its finite free cover. -/
theorem forget_preservesProjectiveObjects :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesProjectiveObjects where
  projective_obj hP := by
    let := hP
    exact projective_toModuleCat R _

variable [IsNoetherianRing R]

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For M∈FGModuleCat_v(R) and
a projective resolution P→M in that category, the exact inclusion U produces a projective
resolution U(P)→U(M) in ModuleCat_v(R). Every term, differential, and augmentation is the
corresponding underlying R-module or linear map. -/
def toModuleCatProjectiveResolution {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) : ProjectiveResolution M.obj := by
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let : U.Additive := { map_add := fun {_ _} _ _ => rfl }
  let : U.PreservesProjectiveObjects := forget_preservesProjectiveObjects R
  let : U.PreservesHomology := inferInstance
  exact U.mapProjectiveResolution P

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For a projective resolution
P of M∈FGModuleCat_v(R) and n≥0, the n-th term of the induced ModuleCat resolution equals the
underlying module U(P_n). Its carrier and R-action are unchanged. -/
theorem toModuleCatProjectiveResolution_X {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    (toModuleCatProjectiveResolution R P).complex.X n = (P.complex.X n).obj := rfl

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For a projective resolution
P of M∈FGModuleCat_v(R) and all n,m∈ℕ, the R-linear differential U(P)_n→U(P)_m equals the
underlying linear map of P.d_{n,m}. This includes the zero maps outside the chain shape. -/
theorem toModuleCatProjectiveResolution_d {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n m : ℕ) :
    ((toModuleCatProjectiveResolution R P).complex.d n m).hom =
      (P.complex.d n m).hom.hom := rfl

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For M∈FGModuleCat_v(R), a
projective resolution P→M there, and every n≥0, the n-th term of the induced ModuleCat
resolution is finitely generated over R. It is the underlying module of the finite-module object
P_n. -/
theorem toModuleCatProjectiveResolution_finite {M : FGModuleCat.{v} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    Module.Finite R ((toModuleCatProjectiveResolution R P).complex.X n) := by
  rw [toModuleCatProjectiveResolution_X]
  exact (P.complex.X n).property

end FGModuleCat

namespace ModuleCat

variable (R : Type u) [Ring R] [IsNoetherianRing R] [Small.{v} R]

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For M∈ModuleCat_v(R)
finitely generated over R, form a projective resolution of its finitely generated module object
and apply the exact inclusion. This gives a projective resolution of M with finitely generated
terms in every degree n≥0. -/
def degreewiseFiniteProjectiveResolution (M : ModuleCat.{v} R) [Module.Finite R M] :
    ProjectiveResolution M := by
  let : EnoughProjectives (FGModuleCat.{v} R) := FGModuleCat.enoughProjectives R
  let N : FGModuleCat.{v} R := ⟨M, inferInstanceAs (Module.Finite R M)⟩
  exact FGModuleCat.toModuleCatProjectiveResolution R (projectiveResolution N)

/-- Let R be a ring in universe u whose carrier has a representative in universe v, and use finitely
generated left R-modules with carriers in v. Assume R is Noetherian. For a finitely generated
M∈ModuleCat_v(R) and any n≥0, the n-th term of its degreewise finitely generated projective
resolution is finitely generated over R. The assertion holds for the entire nonnegative chain
complex. -/
theorem degreewiseFiniteProjectiveResolution_finite
    (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ) :
    Module.Finite R ((degreewiseFiniteProjectiveResolution R M).complex.X n) := by
  let : EnoughProjectives (FGModuleCat.{v} R) := FGModuleCat.enoughProjectives R
  let N : FGModuleCat.{v} R := ⟨M, inferInstanceAs (Module.Finite R M)⟩
  exact FGModuleCat.toModuleCatProjectiveResolution_finite R (projectiveResolution N) n

end ModuleCat
