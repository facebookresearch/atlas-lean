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

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Single

/-!
# Honest complexes of homogeneous submodules

Degreewise submodules preserved by the actual differential give an honest
cochain complex and a degreewise injective chain-map inclusion.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Degreewise original submodules preserved by the original differential. -/
structure HomogeneousSubcomplex where
  /-- The given submodule of the carrier in each degree. -/
  piece : ∀ n : ℤ, Submodule R (C.X n)
  d_mem : ∀ (n : ℤ) (x : C.X n), x ∈ piece n →
    (C.d n (n + 1)).hom x ∈ piece (n + 1)

namespace HomogeneousSubcomplex

variable {C} (S : HomogeneousSubcomplex C)

/-- Restriction of the original differential to the actual degreewise submodules. -/
def differential (n : ℤ) : ModuleCat.of R (S.piece n) ⟶ ModuleCat.of R (S.piece (n + 1)) :=
  ModuleCat.ofHom (((C.d n (n + 1)).hom.comp (S.piece n).subtype).codRestrict
    (S.piece (n + 1)) (fun x => S.d_mem n x x.property))

lemma differential_comp_differential (n : ℤ) :
    S.differential n ≫ S.differential (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (C.d (n + 1) (n + 1 + 1)).hom ((C.d n (n + 1)).hom x.val) = 0
  exact congrArg (fun f : C.X n ⟶ C.X (n + 1 + 1) => f.hom x.val)
    (C.d_comp_d n (n + 1) (n + 1 + 1))

/-- The actual cochain complex of the homogeneous submodules. -/
def complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (S.piece n))
    S.differential S.differential_comp_differential

/-- The original degreewise subtype maps form an honest chain-map inclusion. -/
def inclusion : S.complex ⟶ C :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (S.piece n).subtype) (fun n => by
    simp only [complex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

lemma inclusion_f (n : ℤ) : S.inclusion.f n = ModuleCat.ofHom (S.piece n).subtype := rfl

instance inclusion_f_mono (n : ℤ) : Mono (S.inclusion.f n) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

instance inclusion_mono : Mono S.inclusion := by
  exact HomologicalComplex.mono_of_mono_f S.inclusion (fun _ => inferInstance)

end HomogeneousSubcomplex

section MonoLift

variable {K L T : CochainComplex (ModuleCat.{u} R) ℤ}
variable (m : K ⟶ L) [Mono m] (f : T ⟶ L)
  (hf : ∀ (n : ℤ) (x : T.X n), (f.f n).hom x ∈ LinearMap.range (m.f n).hom)

/-- The actual linear inverse from the range of each original monic degree map. -/
def liftThroughMonoDegree (n : ℤ) : T.X n ⟶ K.X n :=
  ModuleCat.ofHom ((LinearEquiv.ofInjective (m.f n).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)).symm.toLinearMap.comp
      ((f.f n).hom.codRestrict (LinearMap.range (m.f n).hom) (hf n)))

lemma liftThroughMonoDegree_fac (n : ℤ) :
    liftThroughMonoDegree m f hf n ≫ m.f n = f.f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (m.f n).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)).apply_symm_apply ⟨(f.f n).hom x, hf n x⟩)

/-- Pointwise membership in the range of an original monic chain map gives an honest chain-map
lift. -/
def liftThroughMono : T ⟶ K :=
  CochainComplex.ofHom (liftThroughMonoDegree m f hf) (fun n => by
    apply (cancel_mono (m.f (n + 1))).mp
    calc
      (liftThroughMonoDegree m f hf n ≫ K.d n (n + 1)) ≫ m.f (n + 1) =
          (liftThroughMonoDegree m f hf n ≫ m.f n) ≫ L.d n (n + 1) := by
        rw [Category.assoc, ← m.comm, ← Category.assoc]
      _ = f.f n ≫ L.d n (n + 1) := by rw [liftThroughMonoDegree_fac]
      _ = T.d n (n + 1) ≫ f.f (n + 1) := f.comm n (n + 1)
      _ = (T.d n (n + 1) ≫ liftThroughMonoDegree m f hf (n + 1)) ≫ m.f (n + 1) := by
        rw [Category.assoc, liftThroughMonoDegree_fac])

lemma liftThroughMono_fac : liftThroughMono m f hf ≫ m = f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact liftThroughMonoDegree_fac m f hf n

end MonoLift

end CochainComplex
