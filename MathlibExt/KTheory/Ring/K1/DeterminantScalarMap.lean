/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.K1.Field

/-!
# Determinants and change of coefficients in K₁

For commutative rings, determinants in the stable general linear group
and in K₁ commute with ring homomorphisms. Source and target coefficient
rings may lie in independent universes.

For fields, the determinant isomorphism with the unit group is natural
under field homomorphisms.

## Main results

* `StableGL.det_comp_scalarMap`: naturality of the stable determinant.
* `K1.detHom_comp_mapRingHom`: naturality of the K₁ determinant.
* `K1.detEquivUnitsOfField_comp_mapRingHom`: naturality of the field
  determinant isomorphism.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace AlgebraicKTheory

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The stable determinant commutes with a ring homomorphism. -/
@[simp]
theorem StableGL.det_scalarMap (φ : R →+* S) (g : StableGL R) :
    StableGL.det (R := S) (StableGL.scalarMap φ g) =
      (Units.map φ.toMonoidHom) (StableGL.det (R := R) g) := by
  obtain ⟨n, A, rfl⟩ := StableGL.exists_finite_rep g
  rw [StableGL.scalarMap_of, StableGL.det_of, StableGL.det_of]
  exact Matrix.GeneralLinearGroup.det_mapRingHom φ A

/-- Naturality of the stable determinant as an equality of monoid
homomorphisms. -/
theorem StableGL.det_comp_scalarMap (φ : R →+* S) :
    (StableGL.det (R := S)).comp (StableGL.scalarMap φ) =
      (Units.map φ.toMonoidHom).comp (StableGL.det (R := R)) := by
  apply MonoidHom.ext
  intro g
  exact StableGL.det_scalarMap φ g

/-- The K₁ determinant commutes with change of coefficients. -/
@[simp]
theorem K1.detHom_mapRingHom (φ : R →+* S) (a : K1 R) :
    K1.detHom (R := S) (K1.mapRingHom φ a) =
      (Units.map φ.toMonoidHom).toAdditive (K1.detHom (R := R) a) := by
  obtain ⟨g, rfl⟩ := K1.proj_surjective R a
  rw [K1.mapRingHom_proj, K1.detHom_proj, K1.detHom_proj, StableGL.det_scalarMap]
  rfl

/-- Naturality of the K₁ determinant as an equality of additive
homomorphisms. -/
theorem K1.detHom_comp_mapRingHom (φ : R →+* S) :
    (K1.detHom (R := S)).comp (K1.mapRingHom φ) =
      (Units.map φ.toMonoidHom).toAdditive.comp (K1.detHom (R := R)) := by
  apply AddMonoidHom.ext
  intro a
  exact K1.detHom_mapRingHom φ a

/-- The determinant isomorphism for fields is natural between independent
coefficient universes. -/
theorem K1.detEquivUnitsOfField_mapRingHom {F : Type uR} {E : Type uS}
    [Field F] [Field E] (φ : F →+* E) (a : K1 F) :
    K1.detEquivUnitsOfField (F := E) (K1.mapRingHom φ a) =
      (Units.map φ.toMonoidHom).toAdditive (K1.detEquivUnitsOfField (F := F) a) :=
  K1.detHom_mapRingHom φ a

/-- Naturality of the field determinant isomorphism as an equality of
additive homomorphisms. -/
theorem K1.detEquivUnitsOfField_comp_mapRingHom {F : Type uR} {E : Type uS}
    [Field F] [Field E] (φ : F →+* E) :
    (K1.detEquivUnitsOfField (F := E)).toAddMonoidHom.comp (K1.mapRingHom φ) =
      (Units.map φ.toMonoidHom).toAdditive.comp
        (K1.detEquivUnitsOfField (F := F)).toAddMonoidHom :=
  K1.detHom_comp_mapRingHom φ

end AlgebraicKTheory

end
