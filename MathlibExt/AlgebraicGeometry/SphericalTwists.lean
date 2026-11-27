/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedCoherent
public import MathlibExt.AlgebraicGeometry.FourierMukai
public import MathlibExt.AlgebraicGeometry.SchemeModuleLinear
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# A fixed geometric spherical-twist kernel

The kernel is the actual cone O_{X×X} → Δ_*O_X, with the canonical
unit-to-pushforward-unit morphism. The derived operator uses the completed
fixed Fourier--Mukai cochain sources. The coefficient action is the actual
base-ring action on all regular sections, rather than an arbitrary linear
structure. Sphericality of the structure sheaf of a noetherian scheme is the
finite graded self-Hom condition and nondegeneracy of actual composition into
the top trace line, conditions (S2)–(S4) of Seidel–Thomas; their condition (S1),
a finite resolution by quasi-coherent injectives, follows from (S4) on a
noetherian scheme (their Lemma 2.16).

Source: Seidel--Thomas, *Braid group actions on derived categories of
coherent sheaves*, https://arxiv.org/abs/math/0001043, Definition 2.14,
Lemma 2.16, Proposition 2.10 and Theorem 1.2. Generic bounded/coherent preservation
and Fourier--Mukai comparison results are positively covered in Axiom's
DerivedVarieties/FourierMukai source and are not requested as new results.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SphericalTwists

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open BoundedCoherent FourierMukai SchemeModuleLinear

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The structure-sheaf spherical twist has a literal degree-zero mapping-cone kernel. -/
def kernel {k : Type u} [Field k] (X : Over (Spec (.of k))) : D (pullback X.hom X.hom) :=
  let P := pullback X.hom X.hom
  let e : SheafOfModules.unit P.ringCatSheaf ⟶
      (Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
        (SheafOfModules.unit X.left.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit (pullback.diagonal X.hom).toRingCatSheafHom
  DerivedCategory.Q.obj (CochainComplex.mappingCone
    ((CochainComplex.singleFunctor P.Modules 0).map e))

section Sphericality

variable (k : Type u) [Field k] (X : Over (Spec (.of k)))

local instance : Linear k X.left.Modules := modulesLinear k X

/-- The actual structure sheaf in the actual derived category. -/
abbrev structureObject : D X.left := (DerivedCategory.singleFunctor X.left.Modules 0).obj
  (SheafOfModules.unit X.left.ringCatSheaf)

/-- Composition into the actual degree-d endomorphism space, with shifts normalized. -/
def traceComposition {M : D X.left} (d i : ℤ)
    (a : M ⟶ (structureObject k X)⟦i⟧)
    (b : structureObject k X ⟶ M⟦d - i⟧) :
    structureObject k X ⟶ (structureObject k X)⟦d⟧ :=
  b ≫ a⟦d - i⟧' ≫
    (shiftFunctorAdd' (D X.left) i (d - i) d (by omega)).inv.app (structureObject k X)

/-- The structure sheaf of a noetherian scheme `X` over `k` is `d`-spherical for `d > 0`
(Seidel--Thomas, Definition 2.14), tied to actual Hom and composition maps: its graded
self-Homs are `k` in degrees `0` and `d` and vanish otherwise (S3), its graded Homs with
bounded coherent objects are finite-dimensional and bounded (S2), and composition into
the degree-`d` self-Homs is a nondegenerate pairing (S4). Condition (S1), a finite
resolution by quasi-coherent injectives, follows from (S4) on a noetherian scheme
(Seidel--Thomas, Lemma 2.16). -/
structure SphericalStructure [IsNoetherian X.left] (d : ℤ) where
  /-- Sphericality is defined in positive degree; degree zero is a different notion. -/
  positive : 0 < d
  degreeZero : k ≃ₗ[k] (structureObject k X ⟶ structureObject k X)
  degreeZero_normalization : ∀ c : k, degreeZero c = c • 𝟙 (structureObject k X)
  trace : (structureObject k X ⟶ (structureObject k X)⟦d⟧) →ₗ[k] k
  trace_bijective : Function.Bijective trace
  vanish : ∀ i : ℤ, i ≠ 0 → i ≠ d →
    Subsingleton (structureObject k X ⟶ (structureObject k X)⟦i⟧)
  finiteHom : ∀ (M : D X.left), boundedCoherent X.left M →
    (∀ i : ℤ, Module.Finite k (M ⟶ (structureObject k X)⟦i⟧) ∧
      Module.Finite k (structureObject k X ⟶ M⟦i⟧)) ∧
    {i : ℤ | Nontrivial (M ⟶ (structureObject k X)⟦i⟧)}.Finite ∧
    {i : ℤ | Nontrivial (structureObject k X ⟶ M⟦i⟧)}.Finite
  left_nondegenerate : ∀ (M : D X.left), boundedCoherent X.left M →
    ∀ (i : ℤ) (a : M ⟶ (structureObject k X)⟦i⟧), a ≠ 0 →
      ∃ b : structureObject k X ⟶ M⟦d - i⟧,
        trace (traceComposition k X d i a b) ≠ 0
  right_nondegenerate : ∀ (M : D X.left), boundedCoherent X.left M →
    ∀ (i : ℤ) (b : structureObject k X ⟶ M⟦d - i⟧), b ≠ 0 →
      ∃ a : M ⟶ (structureObject k X)⟦i⟧,
        trace (traceComposition k X d i a b) ≠ 0

end Sphericality

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}] [HasDerivedTensors.{u}]

/-- The actual fixed geometric integral transform. -/
def twist {k : Type u} [Field k] (X : Over (Spec (.of k))) : D X.left ⥤ D X.left :=
  fourierMukai X.hom X.hom (SphericalTwists.kernel X)

/-- Restriction along the genuine covered coherent-preservation property. -/
def twistOn {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (h : ∀ M : (boundedCoherent X.left).FullSubcategory,
      boundedCoherent X.left ((twist X).obj M.obj)) :
    (boundedCoherent X.left).FullSubcategory ⥤ (boundedCoherent X.left).FullSubcategory :=
  (boundedCoherent X.left).lift ((boundedCoherent X.left).ι ⋙ twist X) h

end MathlibExt.AlgebraicGeometry.SphericalTwists
