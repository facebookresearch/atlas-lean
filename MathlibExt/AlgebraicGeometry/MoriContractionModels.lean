/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalCurveCones
public import MathlibExt.AlgebraicGeometry.RationalResolution
public import MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

/-!
# Geometric Mori contractions and flips

The cone is made from actual curve degrees. A contraction records a proper
map to a normal projective variety, its canonical structure-sheaf unit,
connected fibers and the exact numerical criterion for contracted curves.

A flip has a genuine small morphism over that same target, with a dense-open
isomorphism over the target. Its canonical rational line is a specified
reflexive tensor power of the actual Serre-characterized canonical module.
Relative ampleness uses the coherent global-generation criterion locally
on affine target opens. None of these predicates is an unspecified oracle.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MoriContractionModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

universe u

/-- `f` contracts the curve `C` when `C` maps to a single point of `Y`. The point
need not be `k`-rational: over a field that is not algebraically closed, a curve
can be contracted to a closed point with a larger residue field. -/
def IsContracted {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))} (f : X ⟶ Y) (C : Curve X) : Prop :=
  (Set.range (C.map.left ≫ f.left).base).Subsingleton

structure Contraction {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (v : N1 X) where
  target : Over (Spec (.of k))
  [integral : IsIntegral target.left]
  [properTarget : IsProper target.hom]
  normal : IsNormalIntegral target.left
  projectiveTarget : ProjectiveSpace.IsProjective target
  map : X ⟶ target
  [proper : IsProper map.left]
  [connected : GeometricallyConnected map.left]
  unit : IsIso (structureUnit map.left)
  locallyProjective : IsLocallyProjectiveOver map
  curves : ∀ C : Curve X, IsContracted map C ↔ curveClass C ∈ ray v

/-- The actual locus on which no local scheme-isomorphism presentation exists. -/
def exceptionalLocus {Y X : Scheme.{u}} (f : Y ⟶ X) : Set Y :=
  {y | ¬∃ U : Y.Opens, y ∈ U ∧ ∃ V : X.Opens, ∃ e : U.toScheme ≅ V.toScheme,
    U.ι ≫ f = e.hom ≫ V.ι}

/-- A small birational morphism from an integral `n`-dimensional source: the source
is integral of dimension `n` and the exceptional locus is nonempty of dimension at
most `n - 2`, stated without natural-number subtraction (so no small morphism has a
source of dimension below two). For an integral source of finite type over a field
(the varieties of the flip interfaces) this says the exceptional locus has
codimension at least two; integrality excludes, e.g., the disjoint union of a point
blow-up of a surface with a threefold. -/
def IsSmall {Y X : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) : Prop :=
  IsBirationalMorphism f ∧ (exceptionalLocus f).Nonempty ∧
    topologicalKrullDim (exceptionalLocus f) + 2 ≤ (n : WithBot ℕ∞) ∧
    topologicalKrullDim Y = (n : WithBot ℕ∞) ∧ IsIntegral Y

/-- Canonical module of a proper `n`-dimensional scheme over `k`, fixed by natural
top-degree Serre duality: it represents `F ↦ Hⁿ(X, F)^∨` on vector bundles. Properness
and the dimension are part of the data: on a nonproper scheme the duality is not
Serre's (on `𝔸¹`, `ω = 0` would satisfy it for `n = 1`). On a projective scheme this
determines the dualizing sheaf, every coherent sheaf being a quotient of vector
bundles. -/
structure CanonicalModule {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (n : ℕ) where
  dimension : topologicalKrullDim X.left = (n : WithBot ℕ∞)
  omega : X.left.Modules
  coherent : SheafOfModules.IsFinitePresentation (R := X.left.ringCatSheaf) omega
  duality : ∀ r : ℕ, ∀ F : X.left.Modules, IsVectorBundle F r →
    (F ⟶ omega) ≃+ ((cohomology X.hom F n) →ₗ[k] k)
  naturality : ∀ (r s : ℕ) (F G : X.left.Modules)
    (hF : IsVectorBundle F r) (hG : IsVectorBundle G s)
    (a : F ⟶ G) (b : G ⟶ omega),
    duality r F hF (a ≫ b) =
      (duality s G hG b).comp (((sectionsFunctor X.hom).rightDerived n).map a).hom

/-- A positive reflexive canonical power that is genuinely a line bundle. -/
structure CanonicalQLine {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (n : ℕ) where
  canonical : CanonicalModule X n
  index : ℕ
  positive : 0 < index
  firstDual : SheafDual (power canonical.omega index)
  secondDual : SheafDual firstDual.dual
  line : IsLineBundle secondDual.dual

def CanonicalQLine.lineBundle {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [IsProper X.hom] {n : ℕ} (K : CanonicalQLine X n) :
    LineBundle X.left :=
  ⟨K.secondDual.dual, K.line⟩

/-- Relative ampleness for a Noetherian source: the target is covered by affine opens over
which the restriction of `L` is ample. -/
def IsRelativelyAmple {k : Type u} [Field k]
    {Y X : Over (Spec (.of k))} [IsNoetherian Y.left] (f : Y ⟶ X) (L : LineBundle Y.left) :
    Prop :=
  ∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.1 ∧
    ∃ h : IsLineBundle ((Scheme.Modules.pullback (f.left ⁻¹ᵁ U.1).ι).obj L.val),
      letI : IsNoetherian (f.left ⁻¹ᵁ U.1 : Scheme.{u}) :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp
            (TopologicalSpace.NoetherianSpace.isCompact _) }
      IsAmpleLine ⟨(Scheme.Modules.pullback (f.left ⁻¹ᵁ U.1).ι).obj L.val, h⟩

structure Flip {k : Type u} [Field k]
    {X : Over (Spec (.of k))} {v : N1 X} (C : Contraction X v) (n : ℕ) where
  source : Over (Spec (.of k))
  [integral : IsIntegral source.left]
  [properSource : IsProper source.hom]
  [noetherianSource : IsNoetherian source.left]
  normal : IsNormalIntegral source.left
  projectiveSource : ProjectiveSpace.IsProjective source
  map : source ⟶ C.target
  [proper : IsProper map.left]
  unit : IsIso (structureUnit map.left)
  small : IsSmall map.left n
  identification : Scheme.PartialIso X.left source.left
  over : identification.iso.hom ≫ identification.target.ι ≫ map.left =
    identification.source.ι ≫ C.map.left
  canonical : CanonicalQLine source n
  positiveCanonical : IsRelativelyAmple map canonical.lineBundle

end MathlibExt.AlgebraicGeometry.MoriContractionModels
