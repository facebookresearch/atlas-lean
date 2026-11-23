/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import MathlibExt.AlgebraicGeometry.RelativeProjectivity

@[expose] public noncomputable section

/-!
# Canonical lines and actual pluricanonical section growth

A canonical line is characterized by natural Serre duality on the actual
finite-rank vector bundles and their actual degree-n coherent cohomology.
On a smooth projective scheme that characterization uniquely fixes the
canonical line. It is explicit toolbox input, with no global provider
asserted. On a proper scheme, general type is positive order-m^n growth of
the sections of its actual tensor powers. The fiber conditions of a family
are tested at every geometric point `Spec Ω ⟶ B` (`Ω` algebraically
closed), with the fiber and its cohomology over `Ω`, so a base without
rational points does not make them vacuous.

Sources: Hartshorne, *Algebraic Geometry*, Chapter III, §7 (Serre duality);
Siu, *Invariance of Plurigenera*, Main Theorem;
Kawamata, *Deformations of canonical singularities*, Theorem 6.
-/

namespace MathlibExt.AlgebraicGeometry.PlurigenusFamilies

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveVectorBundles
open _root_.MathlibExt.AlgebraicGeometry.CurvePositivity

export _root_.MathlibExt.AlgebraicGeometry.RelativeProjectivity (IsHProjectiveOver)

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

/-- Growth of order `m^n` of the sections of the tensor powers of a line bundle `K` on a
proper scheme: `h⁰(K^{⊗ m}) ≥ c m^n` for some `c > 0` and all large `m`. For the
canonical line of a smooth projective `n`-dimensional variety this is general type
(bigness of the canonical line). Sections of a line bundle on a proper scheme form a
finite-dimensional space, so `Module.finrank` is the actual dimension. -/
def HasGeneralTypeGrowth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (K : X.Modules) (_hK : IsLineBundle K) (n : ℕ) :
    Prop :=
  ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ m ≥ N,
    c * (m : ℚ) ^ n ≤
      (Module.finrank k (cohomology f (power K m) 0) : ℚ)

/-- The actual scheme-theoretic fiber at a field-valued point `Spec Ω ⟶ B`. -/
abbrev fiberScheme {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B)
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ B.left) : Scheme.{u} :=
  pullback f.left x

/-- The actual structure map of that fiber to `Spec Ω`. -/
abbrev fiberStructure {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B)
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ B.left) :
    fiberScheme f x ⟶ Spec (.of Ω) :=
  pullback.snd f.left x

/-- Restriction of a sheaf `K` on the total space to the fiber. -/
abbrev fiberCanonical {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B) (K : X.left.Modules)
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ B.left) : (fiberScheme f x).Modules :=
  (Scheme.Modules.pullback (pullback.fst f.left x)).obj K

/-- A smooth projective family of `n`-dimensional varieties of general type over a smooth,
geometrically irreducible, quasi-compact curve `B` over `k` (the setting of Siu's
invariance of plurigenera, stated over a disc; families over other bases are not covered).
It is H-projective (embedded in `ℙᴺ_B` over the base) and carries a line bundle that
restricts to the canonical line of every geometric fiber (characterized there by Serre
duality). It contains no constancy conclusion. -/
structure SmoothGeneralTypeFamilyOverCurve {k : Type u} [Field k] (n : ℕ) where
  /-- The base curve. -/
  B : Over (Spec (.of k))
  /-- The base is a smooth curve over `k`. -/
  [smoothBase : SmoothOfRelativeDimension 1 B.hom]
  /-- The base curve is geometrically irreducible. -/
  [irreducibleBase : GeometricallyIrreducible B.hom]
  [finiteTypeBase : QuasiCompact B.hom]
  X : Over (Spec (.of k))
  f : X ⟶ B
  [proper : IsProper f.left]
  [smoothFibers : SmoothOfRelativeDimension n f.left]
  projective : IsHProjectiveOver f
  /-- A line bundle on the total space whose restriction to every geometric fiber is
  that fiber's canonical line (determined only up to twists pulled back from the base). -/
  canonical : X.left.Modules
  canonicalLine : IsLineBundle canonical
  fiberIrreducible : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B.left),
    GeometricallyIrreducible (fiberStructure f x)
  fiberDuality : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B.left),
    SerreDualizingLine (fiberStructure f x) (fiberCanonical f canonical x) n
  generalType : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B.left),
    HasGeneralTypeGrowth (fiberStructure f x) (fiberCanonical f canonical x)
      (fiberDuality Ω x).line n

attribute [instance] SmoothGeneralTypeFamilyOverCurve.proper

/-- The actual plurigenus `h⁰(K^{⊗ m})` of the fiber at a field-valued point
`Spec Ω ⟶ B`, computed by coherent global sections over `Ω`. -/
def plurigenus {k : Type u} [Field k] {n : ℕ}
    (P : SmoothGeneralTypeFamilyOverCurve (k := k) n)
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ P.B.left) (m : ℕ) : ℕ :=
  Module.finrank Ω
    (cohomology (fiberStructure P.f x)
      (power (fiberCanonical P.f P.canonical x) m) 0)

end MathlibExt.AlgebraicGeometry.PlurigenusFamilies
