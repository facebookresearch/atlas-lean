/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Natural maps and augmentation of the native universal enveloping algebra

The native universal property supplies algebra maps from Lie maps, their
identity/composition laws, and the unique scalar augmentation annihilating
Lie generators. No PBW or freeness hypothesis is involved.
-/

@[expose] public section

noncomputable section

universe u v v' v''

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

attribute [local instance] LieRing.ofAssociativeRing

/-- A Lie map induces an algebra map on the original native enveloping algebras. -/
def map (f : L →ₗ⁅R⁆ L') : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L' :=
  lift R ((ι R).comp f)

theorem map_ι (f : L →ₗ⁅R⁆ L') (x : L) : map R f (ι R x) = ι R (f x) :=
  lift_ι_apply R ((ι R).comp f) x

/-- Enveloping maps preserve identities on the actual quotient algebra. -/
@[simp]
theorem map_id : map R (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R _ := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    map_ι, LieHom.id_apply, AlgHom.id_apply]

/-- Enveloping maps preserve composition across independent Lie-carrier universes. -/
theorem map_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    map_ι, AlgHom.comp_apply]

/-- The canonical scalar augmentation of the native enveloping algebra. -/
def augmentation (L : Type v) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  lift R (0 : L →ₗ⁅R⁆ R)

theorem augmentation_ι (x : L) : augmentation R L (ι R x) = 0 :=
  lift_ι_apply R (0 : L →ₗ⁅R⁆ R) x

/-- A scalar algebra map annihilating all Lie generators is the canonical augmentation. -/
theorem augmentation_unique (ε : UniversalEnvelopingAlgebra R L →ₐ[R] R)
    (hε : ∀ x : L, ε (ι R x) = 0) : ε = augmentation R L := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simpa only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    augmentation_ι] using hε x

/-- The actual augmentation is natural in independently sized Lie-algebra maps. -/
theorem augmentation_naturality (f : L →ₗ⁅R⁆ L') :
    (augmentation R L').comp (map R f) = augmentation R L := by
  apply augmentation_unique
  intro x
  simp only [AlgHom.comp_apply, map_ι, augmentation_ι]

end UniversalEnvelopingAlgebra
