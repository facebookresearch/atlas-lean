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

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Logic.Small.Basic

/-!
# Quotient scalars acting through a module annihilator

Let `R` be a commutative ring and `M` an `R`-module with an independently chosen carrier
universe. If an ideal `I` annihilates `M`, its scalar action descends to `R ⧸ I` with `[r] • m
= r • m`. Restricting this action along the quotient map gives the same `R`-module.

The quotient by the full annihilator embeds in the additive endomorphism ring of `M`, so it is
small in the carrier universe of `M`. Restriction along a surjective ring map is full, and
restriction along any ring map preserves epimorphisms. These facts transfer categorical
projectivity to the annihilator quotient; finite generation also descends.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe u v w

variable (R : Type u) [CommRing R]

/-- Annihilator quotient is small in the module-carrier universe.

For a commutative ring `R` and an `R`-module `M : Type v`, the quotient `R ⧸
Module.annihilator R M` is `Small.{v}`. The quotient embeds in the additive endomorphism ring
of `M` through the scalar action. -/
theorem small_annihilatorQuotient (M : Type v) [AddCommGroup M] [Module R M] :
    Small.{v} (R ⧸ Module.annihilator R M) :=
  small_of_injective (RingHom.quotientKerEquivRange (Module.toAddMonoidEnd R M)).injective

/-- Annihilator of a triple product is the intersection.

For `R`-modules `P`, `J`, and `U`, the annihilator of `P × J × U` is `ann(P) ⊓ ann(J) ⊓
ann(U)`. -/
theorem annihilator_tuple (P J U : ModuleCat.{v} R) :
    Module.annihilator R (P × J × U) =
      Module.annihilator R P ⊓ Module.annihilator R J ⊓ Module.annihilator R U := by
  ext r
  simp only [Module.mem_annihilator, Ideal.mem_inf]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro p
      exact congrArg Prod.fst (h (p, 0, 0))
    · intro j
      exact congrArg (fun x : P × J × U => x.2.1) (h (0, j, 0))
    · intro u
      exact congrArg (fun x : P × J × U => x.2.2) (h (0, 0, u))
  · rintro ⟨⟨hP, hJ⟩, hU⟩ ⟨p, j, u⟩
    exact Prod.ext (hP p) (Prod.ext (hJ j) (hU u))

/-- Module action descended through an annihilating ideal.

If `I ≤ Module.annihilator R M`, the scalar-action homomorphism factors through `R ⧸ I` and
gives a quotient-ring module structure on the same carrier `M`. -/
def annihilatorQuotientModule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) :
    Module (R ⧸ I) M :=
  Module.compHom M (Ideal.Quotient.lift I (Module.toAddMonoidEnd R M) hI)

/-- Quotient scalar class acts by its representative.

With the quotient action defined by `annihilatorQuotientModule`, `(Ideal.Quotient.mk I r) • m
= r • m` for every `r : R` and `m : M`. -/
theorem annihilatorQuotientModule_mk_smul (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) (r : R) (m : M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    (Ideal.Quotient.mk I r) • m = r • m := rfl

/-- Annihilator quotient action forms a scalar tower.

For an annihilating ideal `I`, the `R`-action, quotient-ring action, and carrier `M` satisfy
`IsScalarTower R (R ⧸ I) M`. -/
def annihilatorQuotientTower (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    IsScalarTower R (R ⧸ I) M := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  exact IsScalarTower.of_algebraMap_smul
    (annihilatorQuotientModule_mk_smul R I M hI)

/-- Restriction of the quotient action gives the same module.

For `I ≤ ann(M)`, restrict the descended `R ⧸ I`-module along `R → R ⧸ I`. It is isomorphic to
`ModuleCat.of R M` on the same carrier. -/
def annihilatorQuotientRestrictIso (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) :
    (letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI;
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) M)) ≅
        ModuleCat.of R M := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  refine {
    hom := ModuleCat.ofHom {
      toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := annihilatorQuotientModule_mk_smul R I M hI }
    inv := ModuleCat.ofHom {
      toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => (annihilatorQuotientModule_mk_smul R I M hI r m).symm }
    hom_inv_id := ModuleCat.hom_ext rfl
    inv_hom_id := ModuleCat.hom_ext rfl }

end ModuleCat

namespace ModuleCat

universe u v w

variable {R : Type u} {S : Type w} [Ring R] [Ring S]

/-- Surjective ring maps give full restriction of scalars.

For arbitrary rings `R` and `S`, a surjective ring homomorphism `f : R →+* S` makes
`ModuleCat.restrictScalars f` full. Every `R`-linear map between restricted `S`-modules is
`S`-linear. -/
theorem restrictScalars_full_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    let h : M ⟶ N := ModuleCat.ofHom (X := M) (Y := N) {
      toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' s m := by
        obtain ⟨r, rfl⟩ := hf s
        exact g.hom.map_smul r m }
    exact ⟨h, ModuleCat.hom_ext rfl⟩

/-- Restriction of module scalars preserves epimorphisms.

For any ring homomorphism `f : R →+* S`, restriction from `S`-modules to `R`-modules preserves
epimorphisms, since it retains the underlying surjective map. -/
theorem restrictScalars_preservesEpimorphisms (f : R →+* S) :
    (ModuleCat.restrictScalars.{v} f).PreservesEpimorphisms where
  preserves {M N} g := by
    intro hg
    rw [ModuleCat.epi_iff_surjective]
    exact (ModuleCat.epi_iff_surjective g).1 hg

end ModuleCat

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- Categorical projectivity descends to annihilator quotient scalars.

Let `M : ModuleCat R` be categorically projective and let `I ≤ ann(M)`. With the descended
action, `ModuleCat.of (R ⧸ I) M` is categorically projective. -/
theorem annihilatorQuotient_projective (I : Ideal R) (M : ModuleCat.{v} R)
    [CategoryTheory.Projective M] (hI : I ≤ Module.annihilator R M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    CategoryTheory.Projective (ModuleCat.of (R ⧸ I) M) := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  let F := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk I)
  letI : F.Full := restrictScalars_full_of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  letI : F.PreservesEpimorphisms := restrictScalars_preservesEpimorphisms _
  have hM : CategoryTheory.Projective (F.obj (ModuleCat.of (R ⧸ I) M)) :=
    CategoryTheory.Projective.of_iso (annihilatorQuotientRestrictIso R I M hI).symm
      inferInstance
  exact F.projective_of_map_projective hM

/-- Finite generation descends to annihilator quotient scalars.

If `M` is finitely generated over `R` and `I ≤ ann(M)`, then the same carrier with its
descended quotient action is finitely generated over `R ⧸ I`. -/
theorem annihilatorQuotient_finite (I : Ideal R) (M : ModuleCat.{v} R)
    [Module.Finite R M] (hI : I ≤ Module.annihilator R M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    Module.Finite (R ⧸ I) M := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  letI : IsScalarTower R (R ⧸ I) M := annihilatorQuotientTower R I M hI
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

end ModuleCat
