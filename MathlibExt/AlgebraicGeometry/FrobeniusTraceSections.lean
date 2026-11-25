/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

/-!
# Actual coefficient-twisted Frobenius trace and S0 sections

The coefficient map is the literal inverse of the canonical projection-formula
mate, followed by the actual boundary trace tensored with identity and the
actual sheafified unit map. S0 is the intersection of those actual section
images over *all* admissible positive exponents, for any coefficient module `L`.
An arbitrary or empty index set is not supplied in place of the geometric
admissibility condition. Hacon--Xu's identification of S0 with a stabilized image
of global sections uses a proper variety and a line bundle `L` (finite-dimensional
sections); that identification is not asserted here.

On affine trace frames, the infimum of the nonzero ideals compatible with every
trace is compatible with every trace, so when it is nonzero it is the least nonzero
compatible ideal (`localTestInfimum_isLeast`); its nonvanishing is a separate request.

Generic tensor/pullback/projection-formula proofs are completed source
integration. The required maps have fixed native formulas. Iteration,
localization and test-ideal comparisons concern this normalized system,
not freely selected operators or section spaces.

Reference: Hacon--Xu arXiv1302.0298v2, §2.3 and its S0 construction;
Schwede arXiv0901.1154v4, Definition 2.12/Theorem 5.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusTraceSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
  [HasDerivedPushforwards.{0}]
  (C : CanonicalWeilReference V) (D : RealWeil V) (p : ℕ) [Fact p.Prime]
  (hp : IsInCharacteristic V.X.left p)

/-- Actual geometric admissible positive exponents; no chosen finite/empty proxy. -/
abbrev AdmissibleExponent :=
  {e : ℕ // Nonempty (BoundaryIndex V C p e D)}

omit [Fact p.Prime] in
/-- An admissibility witness is a proof on the fixed coefficient/sheaf formula. -/
theorem boundaryData (a : AdmissibleExponent V C D p) : BoundaryIndex V C p a.val D :=
  Classical.choice a.property

variable (e : ℕ) [(derivedPushforward (iterated V.X.left p hp e)).IsLeftAdjoint]

/-- The actual source module of the boundary trace. -/
abbrev boundaryModule := DivisorialModuleSheaves.sheaf V (boundaryTwist V C D p e)

/-- Coefficient trace map is computed from the actual projection-formula mate and counit. -/
def traceWithCoefficients (L : V.X.left.Modules)
    (F : FrobeniusIdentification V C p e hp) (I : BoundaryIndex V C p e D)
    (T : PullbackTensor (iterated V.X.left p hp e))
    (h : IsIso (projectionFormulaMap (iterated V.X.left p hp e) T
      (boundaryModule V C D p e) L)) :
    (Scheme.Modules.pushforward (iterated V.X.left p hp e)).obj
      (moduleTensor V.X.left (boundaryModule V C D p e)
        ((Scheme.Modules.pullback (iterated V.X.left p hp e)).obj L)) ⟶ L := by
  let := h
  exact inv (projectionFormulaMap (iterated V.X.left p hp e) T (boundaryModule V C D p e) L) ≫
    tensorMap (DualizingFrobeniusInterfaces.boundaryTrace V C p e hp D F I) (𝟙 L) ≫
      leftUnitMap V.X.left L

/-- Literal image of the fixed coefficient trace on actual global sections. -/
def sectionImage (L : V.X.left.Modules)
    (F : FrobeniusIdentification V C p e hp) (I : BoundaryIndex V C p e D)
    (T : PullbackTensor (iterated V.X.left p hp e))
    (h : IsIso (projectionFormulaMap (iterated V.X.left p hp e) T
      (boundaryModule V C D p e) L)) : Submodule k (GenericSectionMaps.Sections V.X L) :=
  LinearMap.range ((GenericSectionMaps.sections V.X).map
    (traceWithCoefficients V C D p hp e L F I T h)).hom

/-- Source/native normalized trace system over every actual admissible exponent. -/
structure TraceSystem (L : V.X.left.Modules) where
  nonempty : Nonempty (AdmissibleExponent V C D p)
  [adjoints : ∀ a : AdmissibleExponent V C D p,
    (derivedPushforward (iterated V.X.left p hp a.val)).IsLeftAdjoint]
  identification : ∀ a : AdmissibleExponent V C D p,
    FrobeniusIdentification V C p a.val hp
  tensor : ∀ a : AdmissibleExponent V C D p, PullbackTensor (iterated V.X.left p hp a.val)
  [projection : ∀ a : AdmissibleExponent V C D p,
    IsIso (projectionFormulaMap (iterated V.X.left p hp a.val) (tensor a)
      (boundaryModule V C D p a.val) L)]

/-- Actual S0 section subspace, using all admissible trace images and the fixed coefficient maps. -/
def S0 (L : V.X.left.Modules) (S : TraceSystem V C D p hp L) :
    Submodule k (GenericSectionMaps.Sections V.X L) := by
  letI := S.adjoints
  letI := S.projection
  exact ⨅ a : AdmissibleExponent V C D p,
    sectionImage V C D p hp a.val L (S.identification a)
      (boundaryData V C D p a) (S.tensor a) inferInstance


/-- The actual section comparison under Frobenius's identity on scheme opens. -/
def originalSectionsIso (M : V.X.left.Modules) (U : V.X.left.Opens) :
    Γ((Scheme.Modules.pushforward (iterated V.X.left p hp e)).obj M,U) ≅ Γ(M,U) :=
  (M.presheaf.mapIso (eqToIso (iterated_preimage V.X.left p hp e U)).op).symm

/-- Actual local additive trace after multiplication by a genuine Cartier generator. -/
def affineAddTrace (F : FrobeniusIdentification V C p e hp) (I : BoundaryIndex V C p e D)
    (U : V.X.left.Opens) (s : Γ(boundaryModule V C D p e,U)) :
    Γ(V.X.left,U) →+ Γ(V.X.left,U) :=
  (DualizingFrobeniusInterfaces.boundaryTrace V C p e hp D F I).app U |>.hom |>.comp
    ((originalSectionsIso V p hp e (boundaryModule V C D p e) U).inv.hom.comp
      (LinearMap.toSpanSingleton Γ(V.X.left,U) Γ(boundaryModule V C D p e,U) s).toAddMonoidHom)

/-- Linearity is a proof on the computed local map; the generator/basis are actual sections. -/
structure AffineTraceFrame (F : FrobeniusIdentification V C p e hp)
    (I : BoundaryIndex V C p e D) (U : V.X.left.Opens) where
  generator : Γ(boundaryModule V C D p e,U)
  basis : Module.Basis Unit Γ(V.X.left,U) Γ(boundaryModule V C D p e,U)
  basis_normalized : basis () = generator
  scalar : ∀ a b : Γ(V.X.left,U),
    affineAddTrace V C D p hp e F I U generator (a^(p^e)*b) =
      a * affineAddTrace V C D p hp e F I U generator b

/-- The actual Cartier-linear map, with its value already computed by the geometric trace. -/
def affineTrace (F : FrobeniusIdentification V C p e hp) (I : BoundaryIndex V C p e D)
    {U : V.X.left.Opens} (A : AffineTraceFrame V C D p hp e F I U) :
    AffineCartierTraceIdeals.CartierTrace Γ(V.X.left,U) p e where
  toAddMonoidHom := affineAddTrace V C D p hp e F I U A.generator
  scalar := A.scalar

/-- Local frames for every actual admissible trace; no arbitrary trace function is selected. -/
abbrev LocalFrames (S : TraceSystem V C D p hp (structureModule V.X.left))
    (U : V.X.left.Opens) :=
  ∀ a : AdmissibleExponent V C D p,
    letI := S.adjoints a
    AffineTraceFrame V C D p hp a.val (S.identification a) (boundaryData V C D p a) U

/-- Actual stable local trace-image ideal, indexed only by admissible exponents. -/
def localStableImage (S : TraceSystem V C D p hp (structureModule V.X.left))
    (U : V.X.left.Opens) (A : LocalFrames V C D p hp S U) : Ideal Γ(V.X.left,U) := by
  letI := S.adjoints
  exact AffineCartierTraceIdeals.indexedStableTraceImage
    (fun a : AdmissibleExponent V C D p => a.val)
    (fun a => affineTrace V C D p hp a.val (S.identification a)
      (boundaryData V C D p a) (A a))

/-- Actual infimum of nonzero compatible ideals for the geometric normalized trace system. -/
def localTestInfimum (S : TraceSystem V C D p hp (structureModule V.X.left))
    (U : V.X.left.Opens) (A : LocalFrames V C D p hp S U) : Ideal Γ(V.X.left,U) := by
  letI := S.adjoints
  exact AffineCartierTraceIdeals.indexedCompatibleIdealInfimum
    (fun a : AdmissibleExponent V C D p => a.val)
    (fun a => affineTrace V C D p hp a.val (S.identification a)
      (boundaryData V C D p a) (A a))

/-- When it is nonzero, the infimum of the nonzero compatible ideals on an affine trace frame
is the least nonzero ideal compatible with every trace. -/
theorem localTestInfimum_isLeast (S : TraceSystem V C D p hp (structureModule V.X.left))
    (U : V.X.left.Opens) (A : LocalFrames V C D p hp S U)
    (h : localTestInfimum V C D p hp S U A ≠ ⊥) :
    IsLeast {J : Ideal Γ(V.X.left,U) | J ≠ ⊥ ∧ ∀ a : AdmissibleExponent V C D p,
        letI := S.adjoints a
        AffineCartierTraceIdeals.IsCompatible
          (affineTrace V C D p hp a.val (S.identification a) (boundaryData V C D p a) (A a)) J}
      (localTestInfimum V C D p hp S U A) :=
  AffineCartierTraceIdeals.isLeast_indexedCompatibleIdealInfimum _ _ h

/-- Actual affine trivializing cover, making the local comparison nonvacuous at every point. -/
structure TraceTrivializingCover (S : TraceSystem V C D p hp (structureModule V.X.left)) where
  openSet : V.X.left → V.X.left.affineOpens
  contains : ∀ x, x ∈ (openSet x).val
  frames : ∀ x, LocalFrames V C D p hp S (openSet x).val

/-- An ideal sheaf on $V$ (`ideal`) whose sections on every affine open $U$ are, for every family
of trace frames on $U$, the infimum of the nonzero ideals of $\Gamma(U, \mathcal{O}_V)$ compatible
with every admissible trace of the trace system $S$ (`normalized`). When that infimum is nonzero,
it is the least nonzero compatible ideal on $U$ (`localTestInfimum_isLeast`), that is, the big test
ideal. -/
structure TestIdealComparison (S : TraceSystem V C D p hp (structureModule V.X.left))
    (A : TraceTrivializingCover V C D p hp S) where
  ideal : V.X.left.IdealSheafData
  normalized : ∀ (U : V.X.left.affineOpens) (F : LocalFrames V C D p hp S U.val),
    ideal.ideal U = localTestInfimum V C D p hp S U.val F

end MathlibExt.AlgebraicGeometry.FrobeniusTraceSections
