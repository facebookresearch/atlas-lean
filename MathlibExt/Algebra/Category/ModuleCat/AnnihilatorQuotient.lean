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
# Small annihilator quotients

The scalar action maps into the small additive endomorphism ring. Its kernel
is the annihilator, so the first isomorphism theorem gives smallness of the
quotient ring. The module actions descend through this quotient with the
same scalar values.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe u v w

variable (R : Type u) [CommRing R]

/-- Native scalar action and the first isomorphism theorem earn quotient smallness. -/
theorem small_annihilatorQuotient (M : Type v) [AddCommGroup M] [Module R M] :
    Small.{v} (R ⧸ Module.annihilator R M) :=
  small_of_injective (RingHom.quotientKerEquivRange (Module.toAddMonoidEnd R M)).injective

/-- The actual tuple annihilator is the intersection of the three original annihilators. -/
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

/-- Descend the original module action along a genuinely annihilating ideal. -/
def annihilatorQuotientModule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) :
    Module (R ⧸ I) M :=
  Module.compHom M (Ideal.Quotient.lift I (Module.toAddMonoidEnd R M) hI)

/-- Every original R scalar value is retained by the actual descended action. -/
theorem annihilatorQuotientModule_mk_smul (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) (r : R) (m : M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    (Ideal.Quotient.mk I r) • m = r • m := rfl

/-- The actual descended action and original R action form the native scalar tower. -/
def annihilatorQuotientTower (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (hI : I ≤ Module.annihilator R M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    IsScalarTower R (R ⧸ I) M := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  exact IsScalarTower.of_algebraMap_smul
    (annihilatorQuotientModule_mk_smul R I M hI)

/-- The native restriction of the actual descended action has the original carrier
and original R scalar values; both identity components are earned directly. -/
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

/-- Surjectivity of the actual ring map earns full restriction of scalars, by
original scalar-map compatibility; no full-faithfulness premise is supplied. -/
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

/-- Restriction preserves epis because its map has the original underlying function. -/
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

/-- Original categorical projectivity transfers to the actual quotient action through
earned full/faithful restriction, original epis and the actual identity-component Iso. -/
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

/-- The original finite generating family also generates for the actual quotient action. -/
theorem annihilatorQuotient_finite (I : Ideal R) (M : ModuleCat.{v} R)
    [Module.Finite R M] (hI : I ≤ Module.annihilator R M) :
    letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
    Module.Finite (R ⧸ I) M := by
  letI : Module (R ⧸ I) M := annihilatorQuotientModule R I M hI
  letI : IsScalarTower R (R ⧸ I) M := annihilatorQuotientTower R I M hI
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

end ModuleCat
