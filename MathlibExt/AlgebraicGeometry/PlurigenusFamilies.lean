/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

@[expose] public noncomputable section

/-!
# Canonical lines and actual pluricanonical section growth

A canonical line is characterized by natural Serre duality on the actual
finite-rank vector bundles and their actual degree-n coherent cohomology.
On a smooth projective scheme that characterization uniquely fixes the
canonical line. It is explicit toolbox input, with no global provider
asserted. General type is positive order-m^n growth of sections of its
actual tensor powers.

Sources: Hartshorne, *Algebraic Geometry*, Chapter III, §7 (Serre duality);
Siu, *Invariance of Plurigenera*, Main Theorem;
Kawamata, *Deformations of canonical singularities*, Theorem 6.
-/

namespace MathlibExt.AlgebraicGeometry.PlurigenusFamilies

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveVectorBundles
open _root_.MathlibExt.AlgebraicGeometry.CurvePositivity

universe u

/-- Serre duality pins the actual canonical line, including naturality
for all maps between finite-rank vector bundles. Restriction to this
subcategory suffices by Yoneda, since the canonical line is locally free. -/
structure SerreDualizingLine {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (K : X.Modules) (n : ℕ) where
  line : IsLineBundle K
  duality : ∀ (r : ℕ) (F : X.Modules), IsVectorBundle F r →
    (F ⟶ K) ≃+ ((cohomology f F n) →ₗ[k] k)
  naturality : ∀ (r s : ℕ) (F G : X.Modules)
    (hF : IsVectorBundle F r) (hG : IsVectorBundle G s)
    (a : F ⟶ G) (b : G ⟶ K),
    duality r F hF (a ≫ b) =
      (duality s G hG b).comp (((sectionsFunctor f).rightDerived n).map a).hom

/-- Dimension-n bigness of the actual canonical line. -/
def HasGeneralTypeGrowth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (K : X.Modules) (n : ℕ) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ m ≥ N,
    c * (m : ℚ) ^ n ≤
      (Module.finrank k (cohomology f (power K m) 0) : ℚ)

/-- Relative projectivity is a genuine closed immersion into projective
space over the parameter scheme, with the projection equation fixed. -/
def IsProjectiveOver {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B) : Prop :=
  ∃ N : ℕ,
    ∃ i : X ⟶ prod (SurfaceHilbertSchemes.projectiveSpace k N) B,
      IsClosedImmersion i.left ∧
        i ≫ (prod.snd : prod (SurfaceHilbertSchemes.projectiveSpace k N) B ⟶ B) = f

/-- The actual scheme-theoretic fiber at a rational field point. -/
abbrev fiberScheme {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ B) : Scheme.{u} :=
  pullback f.left x.left

/-- The actual field-valued structure map on that fiber. -/
abbrev fiberStructure {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ B) :
    fiberScheme f x ⟶ Spec (.of k) :=
  pullback.snd f.left x.left

/-- Restriction of the actual relative canonical line to the fiber. -/
abbrev fiberCanonical {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B) (K : X.left.Modules)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ B) : (fiberScheme f x).Modules :=
  (Scheme.Modules.pullback (pullback.fst f.left x.left)).obj K

/-- A smooth projective general-type family, with its canonical line
characterized on every fiber. It contains no constancy conclusion. -/
structure SmoothGeneralTypeFamily {k : Type u} [Field k] (n : ℕ) where
  B : Over (Spec (.of k))
  [smoothBase : SmoothOfRelativeDimension 1 B.hom]
  [connectedBase : GeometricallyIrreducible B.hom]
  [finiteTypeBase : QuasiCompact B.hom]
  X : Over (Spec (.of k))
  f : X ⟶ B
  [proper : IsProper f.left]
  [smoothFibers : SmoothOfRelativeDimension n f.left]
  projective : IsProjectiveOver f
  canonical : X.left.Modules
  canonicalLine : IsLineBundle canonical
  fiberIrreducible : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B,
    GeometricallyIrreducible (fiberStructure f x)
  fiberDuality : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B,
    SerreDualizingLine (fiberStructure f x) (fiberCanonical f canonical x) n
  generalType : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B,
    HasGeneralTypeGrowth (fiberStructure f x) (fiberCanonical f canonical x) n

/-- The actual plurigenus, computed by coherent global sections. -/
def plurigenus {k : Type u} [Field k] {n : ℕ}
    (P : SmoothGeneralTypeFamily (k := k) n)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ P.B) (m : ℕ) : ℕ :=
  Module.finrank k
    (cohomology (fiberStructure P.f x)
      (power (fiberCanonical P.f P.canonical x) m) 0)

end MathlibExt.AlgebraicGeometry.PlurigenusFamilies

