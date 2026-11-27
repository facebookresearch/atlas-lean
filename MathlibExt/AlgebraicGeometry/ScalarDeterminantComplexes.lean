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

* `StacksFrontier/Homology/TwoTermComplex/PresentationBaseChange.lean`
* `StacksFrontier/Homology/TwoTermComplex/LineBaseChange.lean`
* `StacksFrontier/Homology/TwoTermComplex/DeterminantBaseChange.lean`

Modifications: the literal native scalar-extension cochain source with its adjunction unit and
counit, the exterior-annihilator term determinants and the constructed scalar Hom map are used.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeDeterminantPresentations
public import MathlibExt.AlgebraicGeometry.DeterminantScalarHomMaps

/-!
# Actual scalar-extension complexes and determinant maps

The base-changed complex is literal termwise native scalar extension.
Its derived comparison is the actual derived counit on that finite-
projective complex. The determinant scalar map uses the actual negative
and zero term exterior maps and their full scalar-extension square.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ScalarDeterminantComplexes

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open ProjectiveDeterminantModules SchemeDeterminantPresentations
open AffineDerivedCoefficientModules DeterminantScalarHomMaps

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] LocalComplex.finite LocalComplex.projective

variable {R S : CommRingCat.{u}} (g : R ⟶ S)

/-- The actual native extension-of-scalars adjunction unit, read semilinearly. -/
def scalarUnit (M : ModuleCat.{u} R) : M →ₛₗ[g.hom] (ModuleCat.extendScalars g.hom).obj M where
  toFun x := ((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app M).hom x
  map_add' x y := ((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app M).hom.map_add x y
  map_smul' r x := ((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app M).hom.map_smul r x

variable [HasDerivedScalarExtensions.{u}]

/-- Conditions on the termwise extension of scalars $S \otimes_R P$ of a two-term complex $P$ of
finite projective $R$-modules (in degrees $-1$ and $0$) along a ring homomorphism $g : R \to S$,
given derived scalar extensions (`HasDerivedScalarExtensions`): every term of $S \otimes_R P$ is a
finite projective $S$-module, $S \otimes_R P$ is concentrated in degrees $-1$ and $0$, and the
counit of derived scalar extension at $P$, from $S \otimes^{L}_R P$ to $S \otimes_R P$ in the
derived category of $S$-modules, is an isomorphism. -/
structure ScalarComplexData (P : LocalComplex R) where
  finite : ∀ i : ℤ, Module.Finite S ((scalarComplex g P.complex).X i)
  projective : ∀ i : ℤ, Module.Projective S ((scalarComplex g P.complex).X i)
  strictlyGE : (scalarComplex g P.complex).IsStrictlyGE (-1)
  strictlyLE : (scalarComplex g P.complex).IsStrictlyLE 0
  counit_isIso : IsIso ((derivedScalarExtensionCounit g).app P.complex)

/-- The actual base-changed finite-projective complex. -/
def baseComplex (P : LocalComplex R) (C : ScalarComplexData g P) : LocalComplex S :=
  ⟨scalarComplex g P.complex, C.finite, C.projective, C.strictlyGE, C.strictlyLE⟩

/-- Actual comparison with derived scalar extension, computed from its native counit. -/
def baseComplexIso (P : LocalComplex R) (C : ScalarComplexData g P) :
    (derivedScalarExtension g).obj P.derivedObject ≅ (baseComplex g P C).derivedObject :=
  @asIso _ _ _ _ ((derivedScalarExtensionCounit g).app P.complex) C.counit_isIso

/-- Source-normalized term determinant scalar maps and their universal properties. -/
structure TermDeterminantData (P : LocalComplex R) (C : ScalarComplexData g P)
    (unit_extension : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i))) where
  negative :
    letI : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) := C.finite (-1)
    letI : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) :=
      C.projective (-1)
    BaseChangeDeterminant g.hom (scalarUnit g (P.complex.X (-1))) (unit_extension (-1))
  zero :
    letI : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := C.finite 0
    letI : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) :=
      C.projective 0
    BaseChangeDeterminant g.hom (scalarUnit g (P.complex.X 0)) (unit_extension 0)

/-- The actual negative-term exterior scalar map with all instance heads fixed. -/
def negativeMap (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) :
    determinantModule R (P.complex.X (-1)) →ₛₗ[g.hom]
      determinantModule S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) := by
  letI : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) := C.finite (-1)
  letI : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) :=
    C.projective (-1)
  exact T.negative.map

theorem negativeMap_extension (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) : IsScalarExtension g.hom (negativeMap g P C U T) := by
  let : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) := C.finite (-1)
  let : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X (-1))) :=
    C.projective (-1)
  exact T.negative.scalarExtension

/-- The actual zero-term exterior scalar map with all instance heads fixed. -/
def zeroMap (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) :
    determinantModule R (P.complex.X 0) →ₛₗ[g.hom]
      determinantModule S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := by
  letI : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := C.finite 0
  letI : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := C.projective 0
  exact T.zero.map

theorem zeroMap_extension (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) : IsScalarExtension g.hom (zeroMap g P C U T) := by
  let : Module.Finite S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := C.finite 0
  let : Module.Projective S ((ModuleCat.extendScalars g.hom).obj (P.complex.X 0)) := C.projective 0
  exact T.zero.scalarExtension

/-- The actual determinant scalar map is the constructed Hom map of the two term maps. -/
def determinantMap (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) :
    P.determinant →ₛₗ[g.hom] (baseComplex g P C).determinant :=
  scalarHomMap (negativeMap g P C U T) (negativeMap_extension g P C U T) (zeroMap g P C U T)

/-- Every source determinant element satisfies the actual two-term scalar square. -/
theorem determinantMap_normalization (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) (f : P.determinant)
    (x : determinantModule R (P.complex.X (-1))) :
    determinantMap g P C U T f (negativeMap g P C U T x) = zeroMap g P C U T (f x) :=
  scalarHomMap_normalization (negativeMap g P C U T) (negativeMap_extension g P C U T)
    (zeroMap g P C U T) f x

/-- The condition that the determinant map of a base-changed two-term complex is a scalar extension.
Let $P$ be a two-term complex of finite projective $R$-modules, $g : R \to S$ a ring homomorphism,
`C` the conditions `ScalarComplexData` on the termwise extension of scalars $S \otimes_R P$, `U` the
fact that each unit map $P^i \to S \otimes_R P^i$ is a scalar extension, and `T` determinant
base-change maps for the terms in degrees $-1$ and $0$. The condition is that the $g$-semilinear map
`determinantMap` from $\operatorname{Hom}_R(\det P^{-1}, \det P^0)$ to
$\operatorname{Hom}_S(\det(S \otimes_R P^{-1}), \det(S \otimes_R P^0))$ induced by `T` is a scalar
extension (`IsScalarExtension`): composition with it is a bijection from $S$-linear maps out of its
target to $g$-semilinear maps out of its source, into every $S$-module. Here $\det$ is the
determinant module `determinantModule`. -/
structure DeterminantExtension (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) : Prop where
  scalarExtension : IsScalarExtension (M := P.determinant)
    (N := (baseComplex g P C).determinant) g.hom (determinantMap g P C U T)

end MathlibExt.AlgebraicGeometry.ScalarDeterminantComplexes
