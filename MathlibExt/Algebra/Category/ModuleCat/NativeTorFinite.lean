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
# Finite generation and annihilators of Tor modules

For a commutative noetherian ring R and finitely generated modules M and N, every Tor_q^R(M,N)
is finitely generated. A resolution of N with finitely generated projective terms gives this
finiteness through the homology of M tensored with that resolution.

For any commutative R, the annihilator of either coefficient module is contained in the
annihilator of Tor_q^R(M,N). Consequently the sum of the two coefficient annihilator ideals
annihilates Tor in every degree. The ring and common coefficient carrier heights are
independent.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

universe u v

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- Finite generation of every Tor degree.

Over a commutative noetherian ring R, finitely generated M and N have finitely generated
Tor_q^R(M,N) for every q ≥ 0. -/
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

/-- The first coefficient annihilator annihilates Tor.

For any commutative ring R and modules M,N, Ann_R(M) is contained in Ann_R(Tor_q^R(M,N)) in
every degree q. -/
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

/-- The second coefficient annihilator annihilates Tor.

For any commutative ring R and modules M,N, Ann_R(N) is contained in Ann_R(Tor_q^R(M,N)) in
every degree q. -/
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

/-- The sum of coefficient annihilators annihilates Tor.

The ideal Ann_R(M) + Ann_R(N) is contained in Ann_R(Tor_q^R(M,N)) for every q. -/
theorem annihilator_sup_le_nativeTor
    (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.annihilator R M ⊔ Module.annihilator R N ≤
      Module.annihilator R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  sup_le (annihilator_le_nativeTor_left R M N q) (annihilator_le_nativeTor_right R M N q)

end ModuleCat
