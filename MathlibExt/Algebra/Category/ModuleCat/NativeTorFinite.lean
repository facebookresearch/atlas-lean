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

public import MathlibExt.Algebra.Category.FGModuleCat.ProjectiveResolution
public import MathlibExt.Algebra.Homology.FiniteHomology
public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLinearity
public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedUniverse

/-!
# Finiteness and annihilators of the original native Tor

The actual finite-term projective resolution of the right coefficient gives
finite Tor modules in every degree over a Noetherian ring. The native Tor
objects are the existing derived tensor objects.

The existing first-variable linear map of native Tor transports an
annihilating scalar to zero. Canonical native Tor symmetry proves the same
statement for the other coefficient. Thus the sum of both actual coefficient
annihilators annihilates each original Tor module. Ring and module universes
are independent, and no finiteness of Tor or resolution is a caller input.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

universe u v

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The original derived tensor module is finite in every degree when
both coefficients are finite over a Noetherian ring. -/
theorem nativeTor_finite [IsNoetherianRing R]
    (M N : ModuleCat.{max u v} R) [Module.Finite R M] [Module.Finite R N] (q : ℕ) :
    Module.Finite R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  let P := degreewiseFiniteProjectiveResolution R N
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let : Module.Finite R (P.complex.X q) := degreewiseFiniteProjectiveResolution_finite R N q
  let : Module.Finite R (K.X q) :=
    Module.Finite.tensorProduct R M (P.complex.X q)
  let : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
        (ComplexShape.down ℕ) q).obj K) := by
    change Module.Finite R (K.homology q)
    exact HomologicalComplex.homology_finite_of_finite R K q
  exact Module.Finite.equiv (P.isoLeftDerivedObj F q).toLinearEquiv.symm

/-- The annihilator of the first original coefficient annihilates its
actual native Tor with every other coefficient and in every degree. -/
theorem annihilator_le_nativeTor_left
    (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.annihilator R M ≤
      Module.annihilator R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  intro r hr
  let T := ((Tor (ModuleCat.{max u v} R) q).obj M).obj N
  let L := ModuleCat.UniverseTensor.nativeTorFirstMapLinear R N q (X₁ := M) (X₂ := M)
  have hM : (r • 𝟙 M : M ⟶ M) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change r • m = 0
    exact Module.mem_annihilator.mp hr m
  have hmap : L (r • 𝟙 M) = r • L (𝟙 M) := L.map_smul r (𝟙 M)
  have hid : L (𝟙 M) = 𝟙 T := by
    change ((Tor (ModuleCat.{max u v} R) q).map (𝟙 M)).app N = 𝟙 T
    rw [(Tor (ModuleCat.{max u v} R) q).map_id]
    rfl
  rw [hM, L.map_zero, hid] at hmap
  apply Module.mem_annihilator.mpr
  intro x
  have hx := congrArg (fun f : T ⟶ T => f x) hmap
  change 0 = r • x at hx
  exact hx.symm

/-- Canonical symmetry transports the other original coefficient
annihilator to the actual native Tor object in its original order. -/
theorem annihilator_le_nativeTor_right
    (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.annihilator R N ≤
      Module.annihilator R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  intro r hr
  let e := ModuleCat.UniverseTensor.nativeTorSymmetry R M N q
  have hswap := annihilator_le_nativeTor_left R N M q hr
  apply Module.mem_annihilator.mpr
  intro x
  apply e.toLinearEquiv.injective
  rw [map_smul, Module.mem_annihilator.mp hswap, map_zero]

/-- Both original scalar annihilators annihilate the same actual native
Tor carrier, including every higher degree. -/
theorem annihilator_sup_le_nativeTor
    (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.annihilator R M ⊔ Module.annihilator R N ≤
      Module.annihilator R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  sup_le (annihilator_le_nativeTor_left R M N q) (annihilator_le_nativeTor_right R M N q)

end ModuleCat
