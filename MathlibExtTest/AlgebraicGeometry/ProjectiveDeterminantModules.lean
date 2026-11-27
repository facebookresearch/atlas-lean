/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DeterminantScalarHomMaps
public import MathlibExt.AlgebraicGeometry.AffineCoefficientModules

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeterminantScalarHomMaps
open MathlibExt.AlgebraicGeometry.AffineCoefficientModules

universe u

section Determinant

variable {R : Type u} [CommRing R]

-- Rank zero: on the zero module every element of the exterior algebra is annihilated by wedge
-- multiplication, so the determinant is the whole exterior algebra.
example : determinantSubmodule R PUnit.{u + 1} = ⊤ := by
  ext x
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.mulLeft_apply, Submodule.mem_top, iff_true]
  intro m
  rw [Subsingleton.elim m 0, map_zero, zero_mul]

-- Rank one: the generator `ι 1` of the top exterior power of `R` lies in the determinant,
-- since `ι m * ι 1 = m • (ι 1 * ι 1) = 0`.
example : ExteriorAlgebra.ι R (1 : R) ∈ determinantSubmodule R R := by
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.mulLeft_apply]
  intro m
  have h : ExteriorAlgebra.ι R m = m • ExteriorAlgebra.ι R (1 : R) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]

-- ... but the degree-zero unit does not: `ι 1 * 1 = ι 1 ≠ 0` over a nontrivial ring.
example [Nontrivial R] : (1 : ExteriorAlgebra R R) ∉ determinantSubmodule R R := by
  simp only [determinantSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.mulLeft_apply, mul_one, not_forall]
  exact ⟨1, (ExteriorAlgebra.ι_eq_zero_iff (1 : R)).not.mpr one_ne_zero⟩

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- The induced determinant equivalence is the exterior map on the underlying elements.
example (e : M ≃ₗ[R] N) (x : determinantModule R M) :
    (determinantEquiv e x).val = ExteriorAlgebra.map e.toLinearMap x.val := rfl

-- The identity equivalence induces the identity of the determinant.
example (x : determinantModule R M) : determinantEquiv (LinearEquiv.refl R M) x = x := by
  apply Subtype.ext
  change ExteriorAlgebra.map (LinearEquiv.refl R M).toLinearMap x.val = x.val
  rw [LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id, AlgHom.id_apply]

-- The determinant equivalence of a composite is the composite of the determinant equivalences.
example {P : Type u} [AddCommGroup P] [Module R P] (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P)
    (x : determinantModule R M) :
    determinantEquiv (e.trans f) x = determinantEquiv f (determinantEquiv e x) := by
  apply Subtype.ext
  change ExteriorAlgebra.map (e.trans f).toLinearMap x.val =
    ExteriorAlgebra.map f.toLinearMap (ExteriorAlgebra.map e.toLinearMap x.val)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rfl

/-- The identity is a scalar extension along the identity ring map. -/
theorem isScalarExtension_id (M : Type u) [AddCommGroup M] [Module R M] :
    IsScalarExtension (RingHom.id R) (LinearMap.id : M →ₗ[R] M) := fun _ ↦
  ⟨fun g h e ↦ by simpa using e, fun g ↦ ⟨g, LinearMap.comp_id g⟩⟩

-- Along the identity scalar extension, the scalar Hom map is the identity: its normalization
-- `scalarHomMap a ha b f (a x) = b (f x)` pins it down.
example (f : M →ₗ[R] N) :
    scalarHomMap (LinearMap.id : M →ₗ[R] M) (isScalarExtension_id M)
      (LinearMap.id : N →ₗ[R] N) f = f :=
  LinearMap.ext fun x ↦ scalarHomMap_normalization _ (isScalarExtension_id M) _ f x

end Determinant

section AffineCoefficients

variable {R S : CommRingCat.{u}} (g : R ⟶ S) (M : ModuleCat.{u} R)

-- The affine coefficient comparison is the unique map satisfying its unit equation.
example (φ : (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map g)).obj M ⟶
      (ModuleCat.extendScalars g.hom ⋙ tilde.functor S).obj M)
    (h : (pullbackTildeAdjunction g).unit.app M ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars g.hom).map φ =
        (scalarTildeAdjunction g).unit.app M) :
    φ = (pullbackTildeIso g).hom.app M := by
  apply ((pullbackTildeAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h, pullbackTildeIso_unit]

end AffineCoefficients

end MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
