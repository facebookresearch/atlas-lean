/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.BundleTrace

/-!
# The actual Nash blowup and Nash tangent bundle

The Grassmannian represents rank-d locally free quotients of the
actual sheaf Ω_V, on all scheme tests, over a possibly singular and
nonproper base. The Gauss map on the actual smooth locus is selected
by its identity quotient. The Nash blowup is the native scheme image
of that map, namely the kernel subscheme of its structure-sheaf map.
It is not a separately supplied proper modification.

The Nash tangent bundle is the dual of the restricted universal
quotient. Point fibres are literal scheme-theoretic pullbacks, so
their nilpotent normal cones are retained for Euler obstruction.

Reference: Behrend, arXiv:math/0507523v2, §1.2, equation (3).
Ω uses the completed AlgebraicDifferentialSheaves.forms construction;
native scheme image uses Mathlib IdealSheaf/Subscheme.lean.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NashBlowupModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open IntegralChowChernModels CoherentCurveLinearSeries AlgebraicBundleGeometry
open ComplexAnalytification

variable (V : SchemeData)

/-- The ordinary algebraic cotangent sheaf, computed directly by sheafification. -/
abbrev differentials := AlgebraicDifferentialSheaves.forms ℂ V.scheme 1

/-- The generic quotient Grassmannian has no smoothness requirement on its base. -/
structure QuotientGrassmannian (d : ℕ) where
  total : SchemeData
  projection : total.scheme ⟶ V.scheme
  [proper : IsProper projection.left]
  universalQuotient : total.scheme.left.Modules
  bundle : IsBundle universalQuotient d
  quotient : (Scheme.Modules.pullback projection.left).obj (differentials V) ⟶ universalQuotient
  [epi : Epi quotient]
  universal : ∀ (T : Over (Spec (.of ℂ))) (f : T ⟶ V.scheme) (Q : T.left.Modules)
    (_hQ : IsBundle Q d) (q : (Scheme.Modules.pullback f.left).obj (differentials V) ⟶ Q)
    (_hq : Epi q), ∃! g : T ⟶ total.scheme, ∃ (h : g ≫ projection = f)
      (e : (Scheme.Modules.pullback g.left).obj universalQuotient ≅ Q),
      q = pulledQuotient (differentials V) universalQuotient projection quotient f g h Q e

attribute [instance] QuotientGrassmannian.proper QuotientGrassmannian.epi

/-- The true smooth locus, defined as the union of all smooth opens. -/
def smoothLocus : V.scheme.left.Opens :=
  sSup {U | Smooth (U.ι ≫ V.scheme.hom)}

def smoothParameter : Over (Spec (.of ℂ)) := Over.mk ((smoothLocus V).ι ≫ V.scheme.hom)

def smoothInclusion : smoothParameter V ⟶ V.scheme := Over.homMk (smoothLocus V).ι rfl

/-- The condition that the smooth locus of $V$ (the union of the opens that are smooth over $ℂ$) is
smooth over $ℂ$ and that the restriction of $Ω_V$ to it is locally free of rank $d$. -/
structure SmoothDifferentials (d : ℕ) : Prop where
  smooth : Smooth ((smoothLocus V).ι ≫ V.scheme.hom)
  bundle : IsBundle ((Scheme.Modules.pullback (smoothLocus V).ι).obj (differentials V)) d

variable {V}

/-- The Gauss map is the unique classifying map of the identity quotient of Ω on V_sm. -/
def gaussMap {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    smoothParameter V ⟶ G.total.scheme :=
  Classical.choose (G.universal (smoothParameter V) (smoothInclusion V)
    ((Scheme.Modules.pullback (smoothLocus V).ι).obj (differentials V)) S.bundle
    (𝟙 _) inferInstance)

theorem gaussMap_projection {d : ℕ} (G : QuotientGrassmannian V d)
    (S : SmoothDifferentials V d) : gaussMap G S ≫ G.projection = smoothInclusion V :=
  Classical.choose (Classical.choose_spec (G.universal (smoothParameter V) (smoothInclusion V)
    ((Scheme.Modules.pullback (smoothLocus V).ι).obj (differentials V)) S.bundle
    (𝟙 _) inferInstance)).1

/-- The actual scheme-theoretic closure of the smooth Gauss image. -/
abbrev nashScheme {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    Scheme := (gaussMap G S).left.image

def nashInclusion {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    nashScheme G S ⟶ G.total.scheme.left := (gaussMap G S).left.imageι

def nashProjection {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    nashScheme G S ⟶ V.scheme.left := nashInclusion G S ≫ G.projection.left

def nashParameter {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    Over (Spec (.of ℂ)) := Over.mk (nashProjection G S ≫ V.scheme.hom)

/-- The universal rank-d quotient restricted to the genuine Gauss-image closure. -/
def nashQuotient {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    (nashScheme G S).Modules :=
  (Scheme.Modules.pullback (nashInclusion G S)).obj G.universalQuotient

/-- The actual Nash tangent sheaf is the dual universal quotient. -/
def nashTangent {d : ℕ} (G : QuotientGrassmannian V d) (S : SmoothDifferentials V d) :
    (nashScheme G S).Modules :=
  BundleTrace.homSheaf (nashScheme G S) (nashQuotient G S) (structureModule (nashScheme G S))

/-- Only geometric properties of this computed image remain to prove. -/
class NashGeometry {d : ℕ} (G : QuotientGrassmannian V d)
    (S : SmoothDifferentials V d) : Prop where
  [integral : IsIntegral (nashScheme G S)]
  [finiteType : LocallyOfFiniteType (nashParameter G S).hom]
  [quasiCompact : QuasiCompact (nashParameter G S).hom]
  [noetherian : IsNoetherian (nashScheme G S)]
  [proper : IsProper (nashProjection G S)]
  tangentBundle : IsBundle (nashTangent G S) d

attribute [instance] NashGeometry.integral NashGeometry.finiteType
  NashGeometry.quasiCompact NashGeometry.noetherian NashGeometry.proper

def nashData {d : ℕ} {G : QuotientGrassmannian V d} {S : SmoothDifferentials V d}
    (N : NashGeometry G S) : SchemeData :=
  { scheme := nashParameter G S, finiteType := N.finiteType,
    quasiCompact := N.quasiCompact, noetherian := N.noetherian }

def nashMap {d : ℕ} {G : QuotientGrassmannian V d} {S : SmoothDifferentials V d}
    (N : NashGeometry G S) : (nashData N).scheme ⟶ V.scheme :=
  Over.homMk (nashProjection G S) rfl

/-- The dimension is the actual dimension of the integral subvariety. -/
structure IntegralDimension (V : SchemeData) where
  [integral : IsIntegral V.scheme.left]
  dimension : ℕ
  normalized : topologicalKrullDim V.scheme.left = (dimension : ℕ)

/-- All Nash data are attached to the computed cotangent quotient and image. -/
structure NashModel (V : SchemeData) where
  dimension : IntegralDimension V
  grassmannian : QuotientGrassmannian V dimension.dimension
  smooth : SmoothDifferentials V dimension.dimension
  geometry : NashGeometry grassmannian smooth

/-- The scheme-theoretic fibre over the actual complex point. -/
def fibreScheme {V : SchemeData} (N : NashModel V) (p : space V.scheme) : Scheme :=
  pullback (nashProjection N.grassmannian N.smooth) p.hom

def fibreStructure {V : SchemeData} (N : NashModel V) (p : space V.scheme) :
    fibreScheme N p ⟶ Spec (.of ℂ) :=
  pullback.snd (nashProjection N.grassmannian N.smooth) p.hom

/-- Properness and finite type apply to the literal fibre, including its nilpotents. -/
class FibreGeometry {V : SchemeData} (N : NashModel V) (p : space V.scheme) : Prop where
  [proper : IsProper (fibreStructure N p)]
  [finiteType : LocallyOfFiniteType (fibreStructure N p)]
  [quasiCompact : QuasiCompact (fibreStructure N p)]
  [noetherian : IsNoetherian (fibreScheme N p)]
  [closed : IsClosedImmersion
    (pullback.fst (nashProjection N.grassmannian N.smooth) p.hom)]

attribute [instance] FibreGeometry.proper FibreGeometry.finiteType
  FibreGeometry.quasiCompact FibreGeometry.noetherian FibreGeometry.closed

def fibreData {V : SchemeData} {N : NashModel V} {p : space V.scheme}
    (F : FibreGeometry N p) : SchemeData :=
  { scheme := Over.mk (fibreStructure N p), finiteType := F.finiteType,
    quasiCompact := F.quasiCompact, noetherian := F.noetherian }

def fibreInclusion {V : SchemeData} {N : NashModel V} {p : space V.scheme}
    (F : FibreGeometry N p) : (fibreData F).scheme ⟶ (nashData N.geometry).scheme :=
  Over.homMk (pullback.fst (nashProjection N.grassmannian N.smooth) p.hom) (by
    change (pullback.fst (nashProjection N.grassmannian N.smooth) p.hom) ≫
      (nashProjection N.grassmannian N.smooth ≫ V.scheme.hom) = fibreStructure N p
    rw [← Category.assoc,pullback.condition,Category.assoc,p.hom_comp,Category.comp_id]
    rfl)

end MathlibExt.AlgebraicGeometry.NashBlowupModels
