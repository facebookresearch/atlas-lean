/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor

/-!
# Chevalley–Eilenberg chains under Lie algebra maps

For `f : L →ₗ⁅R⁆ L'`, an `L'`-module `N`, and a compatible map
`g : M →ₗ⁅R,L⁆ f* N`, the induced chain map is the exterior map of `f`
tensored with `g`. Exterior-word induction proves boundary compatibility.

The linear formulas allow independent Lie and coefficient universes.
Bundled chain maps use one module-category universe. Restriction maps are
natural in the target representation and respect composition of Lie maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v v' w w'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

section LinearNaturality

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : LieModuleCat.{w} R L) (N : LieModuleCat.{w'} R L')

/-- The ambient exterior and coefficient tensor map. -/
def coefficientLieAmbientMap (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    (ExteriorAlgebra R L ⊗[R] M) →ₗ[R] (ExteriorAlgebra R L' ⊗[R] N) :=
  TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap g.toLinearMap

@[simp]
theorem coefficientLieAmbientMap_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N)
    (a : ExteriorAlgebra R L) (m : M) :
    coefficientLieAmbientMap R L f M N g (a ⊗ₜ[R] m) =
      ExteriorAlgebra.map f.toLinearMap a ⊗ₜ[R] g m := by
  simp only [coefficientLieAmbientMap, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LieModuleHom.coe_toLinearMap]

/-- The native source coefficient map intertwines the two diagonal actions. -/
theorem coefficientLieDiagonalAction_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L) :
    (coefficientLieAmbientMap R L f M N g).comp
        (coefficientDiagonalAction R L M x) =
      (coefficientDiagonalAction R L' N (f x)).comp
        (coefficientLieAmbientMap R L f M N g) := by
  have haction (a : ExteriorAlgebra R L) :
      ExteriorAlgebra.map f.toLinearMap (adjointAction R L x a) =
        adjointAction R L' (f x) (ExteriorAlgebra.map f.toLinearMap a) :=
    LinearMap.congr_fun (adjointAction_naturality R L f x) a
  have hg (m : M) : g ⁅x, m⁆ = (⁅f x, g m⁆ : N) := by
    simpa only [LieModuleCat.restrictObj_lie] using g.map_lie x m
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientDiagonalAction_tmul, map_add,
    coefficientLieAmbientMap_tmul, haction, hg]

theorem coefficientLieDiagonalAction_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientDiagonalAction R L M x p) =
      coefficientDiagonalAction R L' N (f x)
        (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieDiagonalAction_naturality R L f M N g x) p

/-- Exterior insertion commutes with the concrete tensor map. -/
theorem coefficientLieInsertion_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L) :
    (coefficientLieAmbientMap R L f M N g).comp (coefficientInsertion R L M x) =
      (coefficientInsertion R L' N (f x)).comp
        (coefficientLieAmbientMap R L f M N g) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientInsertion_tmul,
    coefficientLieAmbientMap_tmul, map_mul, ExteriorAlgebra.map_apply_ι,
    LieHom.coe_toLinearMap]

theorem coefficientLieInsertion_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientInsertion R L M x p) =
      coefficientInsertion R L' N (f x) (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieInsertion_naturality R L f M N g x) p

/-- Lie and coefficient maps jointly intertwine the ambient CE boundary. -/
theorem coefficientLieBoundary_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    (coefficientLieAmbientMap R L f M N g).comp (coefficientBoundary R L M) =
      (coefficientBoundary R L' N).comp (coefficientLieAmbientMap R L f M N g) := by
  apply TensorProduct.ext'
  intro a m
  change coefficientLieAmbientMap R L f M N g
      (coefficientBoundary R L M (a ⊗ₜ[R] m)) =
    coefficientBoundary R L' N
      (coefficientLieAmbientMap R L f M N g (a ⊗ₜ[R] m))
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [coefficientBoundary_algebraMap_tmul, map_zero,
        coefficientLieAmbientMap_tmul, AlgHom.commutes,
        coefficientBoundary_algebraMap_tmul]
  | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [coefficientLieAmbientMap_tmul, map_mul,
        ExteriorAlgebra.map_apply_ι, LieHom.coe_toLinearMap] at ha ⊢
      rw [coefficientBoundary_ι_mul_tmul, coefficientBoundary_ι_mul_tmul,
        map_sub, map_neg, coefficientLieDiagonalAction_naturality_apply,
        coefficientLieInsertion_naturality_apply, ha]
      simp only [coefficientLieAmbientMap_tmul]

theorem coefficientLieBoundary_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientBoundary R L M p) =
      coefficientBoundary R L' N (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieBoundary_naturality R L f M N g) p

/-- Degree `n` is the exterior map tensored with the native restricted coefficient map. -/
def coefficientLieDegreeMap
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    ((⋀[R]^n L) ⊗[R] M) →ₗ[R] ((⋀[R]^n L') ⊗[R] N) :=
  TensorProduct.map (exteriorPower.map n f.toLinearMap) g.toLinearMap

@[simp]
theorem coefficientLieDegreeMap_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    coefficientLieDegreeMap R L f M N g n (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] g m := by
  simp only [coefficientLieDegreeMap, TensorProduct.map_tmul,
    LieModuleHom.coe_toLinearMap]

/-- The homogeneous map is the restriction of the concrete ambient tensor map. -/
theorem coefficientLieDegreeMap_inclusion
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    ((⋀[R]^n L').subtype.rTensor N).comp (coefficientLieDegreeMap R L f M N g n) =
      (coefficientLieAmbientMap R L f M N g).comp ((⋀[R]^n L).subtype.rTensor M) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientLieDegreeMap_tmul,
    LinearMap.rTensor_tmul, Submodule.subtype_apply, exteriorPower.coe_map,
    coefficientLieAmbientMap_tmul]

/-- Every positive-degree homogeneous differential is natural, with independent
Lie algebra and coefficient universes and no flatness hypothesis. -/
theorem coefficientLieDifferential_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    (coefficientLieDegreeMap R L f M N g n).comp (coefficientDifferential R L M n) =
      (coefficientDifferential R L' N n).comp
        (coefficientLieDegreeMap R L f M N g (n + 1)) := by
  have hinclusion (k : ℕ) (p : (⋀[R]^k L) ⊗[R] M) :=
    LinearMap.congr_fun (coefficientLieDegreeMap_inclusion R L f M N g k) p
  simp only [LinearMap.comp_apply] at hinclusion
  apply LinearMap.ext
  intro p
  apply DirectSum.subtype_rTensor_injective (fun k : ℕ => ⋀[R]^k L') N n
  change ((⋀[R]^n L').subtype.rTensor N)
      (coefficientLieDegreeMap R L f M N g n (coefficientDifferential R L M n p)) =
    ((⋀[R]^n L').subtype.rTensor N)
      (coefficientDifferential R L' N n (coefficientLieDegreeMap R L f M N g (n + 1) p))
  rw [hinclusion, coefficientDifferential_inclusion_apply,
    coefficientDifferential_inclusion_apply, hinclusion]
  exact coefficientLieBoundary_naturality_apply R L f M N g
    (((⋀[R]^(n + 1) L).subtype.rTensor M) p)

end LinearNaturality

section NativeMaps

variable {L' L'' : Type v}
variable [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
variable (f : L →ₗ⁅R⁆ L')
variable (M : LieModuleCat.{w} R L) (N : LieModuleCat.{w} R L')

/-- The native CE chain map from joint differential naturality. -/
def coefficientLieComplexMap (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    coefficientComplex R L M ⟶ coefficientComplex R L' N :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (coefficientLieDegreeMap R L f M N g n))
    (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom
        (coefficientLieDifferential_naturality R L f M N g n).symm)

@[simp]
theorem coefficientLieComplexMap_f
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    (coefficientLieComplexMap R L f M N g).f n =
      ModuleCat.ofHom (coefficientLieDegreeMap R L f M N g n) := rfl

theorem coefficientLieComplexMap_f_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    ((coefficientLieComplexMap R L f M N g).f n).hom (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] g m :=
  coefficientLieDegreeMap_tmul R L f M N g n a m

/-- An `L'`-representation gives the canonical restriction map
`CE(L,f* N) → CE(L',N)`. The coefficient factor is the identity. -/
def coefficientRestrictionMap :
    coefficientComplex R L (LieModuleCat.restrictObj f N) ⟶ coefficientComplex R L' N :=
  coefficientLieComplexMap R L f (LieModuleCat.restrictObj f N) N LieModuleHom.id

theorem coefficientRestrictionMap_f_tmul (n : ℕ) (a : ⋀[R]^n L) (m : N) :
    ((coefficientRestrictionMap R L f N).f n).hom (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] m := by
  rw [coefficientRestrictionMap, coefficientLieComplexMap_f_tmul, LieModuleHom.id_apply]

/-- Restriction is natural in the target coefficient representation. -/
theorem coefficientRestrictionMap_naturality
    {P : LieModuleCat.{w} R L'} (g : N ⟶ P) :
    coefficientRestrictionMap R L f N ≫ coefficientComplexMap R L' N g =
      coefficientComplexMap R L (LieModuleCat.restrictObj f N)
        (LieModuleCat.restrictMap f g) ≫ coefficientRestrictionMap R L f P := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a m
  change ((coefficientComplexMap R L' N g).f n).hom
      (((coefficientRestrictionMap R L f N).f n).hom (a ⊗ₜ[R] m)) =
    ((coefficientRestrictionMap R L f P).f n).hom
      (((coefficientComplexMap R L (LieModuleCat.restrictObj f N)
        (LieModuleCat.restrictMap f g)).f n).hom (a ⊗ₜ[R] m))
  rw [coefficientRestrictionMap_f_tmul, coefficientComplexMap_f_tmul,
    coefficientComplexMap_f_tmul, coefficientRestrictionMap_f_tmul]
  rfl

/-- The canonical maps form a natural transformation from restricted
coefficient chains to the target Lie algebra's coefficient chains. -/
def coefficientRestrictionNatTrans :
    LieModuleCat.restrict f ⋙ coefficientComplexFunctor R L ⟶
      coefficientComplexFunctor R L' where
  app N := coefficientRestrictionMap R L f N
  naturality N P g := (coefficientRestrictionMap_naturality R L f N g).symm

/-- Composition of Lie algebra maps gives the composite canonical restriction map. -/
theorem coefficientRestrictionMap_comp (h : L' →ₗ⁅R⁆ L'')
    (P : LieModuleCat.{w} R L'') :
    coefficientRestrictionMap R L f (LieModuleCat.restrictObj h P) ≫
        coefficientRestrictionMap R L' h P =
      coefficientRestrictionMap R L (h.comp f) P := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a m
  change ((coefficientRestrictionMap R L' h P).f n).hom
      (((coefficientRestrictionMap R L f (LieModuleCat.restrictObj h P)).f n).hom
        (a ⊗ₜ[R] m)) =
    ((coefficientRestrictionMap R L (h.comp f) P).f n).hom (a ⊗ₜ[R] m)
  rw [coefficientRestrictionMap_f_tmul, coefficientRestrictionMap_f_tmul,
    coefficientRestrictionMap_f_tmul, LieHom.toLinearMap_comp,
    exteriorPower.map_comp, LinearMap.comp_apply]

end NativeMaps

end ChevalleyEilenberg
