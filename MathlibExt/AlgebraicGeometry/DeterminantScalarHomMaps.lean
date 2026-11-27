/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Homology/TwoTermComplex/LineBaseChange.lean`

Modifications: the semilinear Hom map is constructed by the scalar-extension universal
property of its source-module map, with its normalization on every element.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules

/-!
# Actual scalar-extension maps of determinant Hom modules

The determinant of a two-term complex is an actual Hom module. Its scalar
map is the unique linear lift of the positive-term scalar map after the
negative-term scalar extension. The defining equation is retained for every
linear map and every source element, with additivity/semilinearity proved.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeterminantScalarHomMaps

open ProjectiveDeterminantModules

universe u

variable {R S M N M' N' : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  {g : R →+* S}

/-- The actual unique linear lift of the prescribed semilinear composite. -/
def scalarHomLift (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') (f : M →ₗ[R] N) : M' →ₗ[S] N' :=
  Classical.choose ((ha (ModuleCat.of S N')).2 (b.comp f))

/-- The full scalar-extension square of the actual lift. -/
theorem scalarHomLift_comp (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') (f : M →ₗ[R] N) :
    (scalarHomLift a ha b f).comp a = b.comp f :=
  Classical.choose_spec ((ha (ModuleCat.of S N')).2 (b.comp f))

/-- Its elementwise normalization uses both actual coefficient maps. -/
theorem scalarHomLift_apply (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') (f : M →ₗ[R] N) (x : M) :
    scalarHomLift a ha b f (a x) = b (f x) :=
  LinearMap.congr_fun (scalarHomLift_comp a ha b f) x

/-- The actual scalar Hom map, constructed from the fixed module maps. -/
def scalarHomMap (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') : (M →ₗ[R] N) →ₛₗ[g] (M' →ₗ[S] N') where
  toFun := scalarHomLift a ha b
  map_add' f h := by
    apply (ha (ModuleCat.of S N')).1
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, scalarHomLift_apply, map_add]
  map_smul' r f := by
    apply (ha (ModuleCat.of S N')).1
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, scalarHomLift_apply, map_smulₛₗ]

/-- Exact source/target element normalization of the constructed Hom map. -/
theorem scalarHomMap_normalization (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') (f : M →ₗ[R] N) (x : M) :
    scalarHomMap a ha b f (a x) = b (f x) := scalarHomLift_apply a ha b f x

/-- The proposition that extension of scalars commutes with Hom out of a finite projective module:
for a ring map $g : R \to S$, a finite projective $R$-module $M$, an $R$-module $N$, and
$g$-semilinear maps $a : M \to M'$ and $b : N \to N'$ exhibiting the $S$-modules $M'$ and $N'$ as
the scalar extensions of $M$ and $N$ (`IsScalarExtension`), the $g$-semilinear map
$\operatorname{Hom}_R(M, N) \to \operatorname{Hom}_S(M', N')$ sending $f$ to the unique $S$-linear
map $f'$ with $f' \circ a = b \circ f$ (`scalarHomMap`) exhibits $\operatorname{Hom}_S(M', N')$ as
the scalar extension of $\operatorname{Hom}_R(M, N)$. -/
structure ScalarHomExtension [Module.Finite R M] [Module.Projective R M]
    (a : M →ₛₗ[g] M') (ha : IsScalarExtension g a)
    (b : N →ₛₗ[g] N') (hb : IsScalarExtension g b) : Prop where
  scalarExtension : IsScalarExtension g (scalarHomMap a ha b)

end MathlibExt.AlgebraicGeometry.DeterminantScalarHomMaps
