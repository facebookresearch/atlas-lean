/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras
public import Mathlib.Basic.Complex.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Individual quasimap regularization and restricted family comparisons

The GIT target is native Proj of the actual homogeneous invariant
algebra. Its stable-locus torsor is an actual quotient torsor and its
affine-quotient projection is the native degree-zero map.

An individual regularization extends the actual map outside the
scheme-theoretic base locus. Its regular torsor is the literal pullback
of the stable-locus torsor and its Picard degree is the native descended
line degree. The numerical defect operator tests only L_theta.

Family comparison records an explicit parameter shrinking and a common
source-curve modification. It asserts no same-curve regularization
operation compatible with arbitrary parameter maps.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
§2.2, Definition 7.1.1, Lemma 7.1.2/equation (7.1.3), and the proof
of Theorem 7.1.6, pp. 44–45.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapRegularizationModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj Opposite
open _root_.AlgebraicGeometry
open GroupTorsorGeometry QuasimapAssociatedFamilies
open LinearizedLineBundles LineBundleTaskContracts CoherentCurveLinearSeries
open QuasimapBasepointDefects QuasimapSectionLengths QuasimapPicardDegrees
open QuasimapInvariantAlgebras

variable (G W : Over (Spec (.of ℂ))) [GrpObj G] [ModObj G W]
variable [IsAffine G.left] [IsAffine W.left]
variable (L : CharacterPolarization G W) [A : InvariantAlgebraModel G W L]

/-- Source-normalized stable-locus geometry for the actual GIT Proj. -/
structure StableGITTarget where
  [finite : Algebra.FiniteType (invariantRing G W) (InvariantAlgebra G W L)]
  baseScalars : ℂ →+* invariantRing G W
  base_normalized : ∀ z, (baseScalars z).val = (globalScalarMap W.hom) z
  stable : W.left.Opens
  stable_complement : ∀ x : W.left, x ∈ stable ↔ x ∉ Set.range (unstableInclusion L)
  stable_nonempty : Nonempty stable
  irrelevant_covers : IrrelevantCovers (invariantGrading G W L) (gitEvaluation G W L stable)
  [stable_smooth : Smooth (stable.ι ≫ W.hom)]
  [proper : IsProper (gitAffineProjection G W L)]
  torsor : Torsor G
    (Over.mk (gitAffineProjection G W L ≫ Spec.map (CommRingCat.ofHom baseScalars)))
  total : torsor.total ≅ Over.mk (stable.ι ≫ W.hom)
  projection_normalized : torsor.projection.left =
    total.hom.left ≫ gitOrbitMap G W L stable irrelevant_covers
  equivariant : γ[G,torsor.total] ≫
      (total.hom ≫ Over.homMk stable.ι (by rfl)) =
    (G ◁ (total.hom ≫ Over.homMk stable.ι (by rfl))) ≫ γ[G,W]

variable {G W L}

def StableGITTarget.target (Q : StableGITTarget G W L) : Over (Spec (.of ℂ)) :=
  Over.mk (gitAffineProjection G W L ≫ Spec.map (CommRingCat.ofHom Q.baseScalars))

/-- The actual quotient-stack point underlying the stable-locus torsor. -/
def StableGITTarget.point (Q : StableGITTarget G W L) :
    QuotientObject G W Q.target where
  torsor := Q.torsor
  map := Q.total.hom ≫ Over.homMk Q.stable.ι (by rfl)
  equivariant := Q.equivariant

variable {n g : ℕ} {T : Over (Spec (.of ℂ))}
variable (F : Family G W n g T) (B : AssociatedFamily F)
variable (U : AssociatedUnstable L F.quotient B)

instance basepointInclusion_closed : IsClosedImmersion (basepointInclusion L U) := by
  dsimp [basepointInclusion]
  infer_instance

/-- The actual complement of the embedded basepoint scheme. -/
def nonbaseOpen : F.curve.X.Opens :=
  ⟨(Set.range (basepointInclusion L U))ᶜ,
    (basepointInclusion L U).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def nonbaseOver : Over (Spec (.of ℂ)) :=
  Over.mk ((nonbaseOpen F B U).ι ≫ F.curve.π ≫ T.hom)

def nonbaseCurveMap :
    nonbaseOver F B U ⟶ Over.mk (F.curve.π ≫ T.hom) :=
  Over.homMk (nonbaseOpen F B U).ι (by simp [nonbaseOver])

/-- A prestable quasimap on an individual complex curve has finite base support,
contained in the smooth curve locus and disjoint from all actual markings
(Ciocan-Fontanine–Kim–Maulik, Definitions 3.1.1–3.1.2). For a family these
conditions are imposed on every geometric fibre, not on the total space, so the
predicate is stated for an individual curve. -/
def IsPrestable (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ))))) (B : AssociatedFamily F)
    (U : AssociatedUnstable L F.quotient B) : Prop :=
  (Set.range (basepointInclusion L U)).Finite ∧
    (∀ x ∈ Set.range (basepointInclusion L U), (F.curve.π.stalkMap x).hom.FormallySmooth) ∧
      ∀ i : Fin n, Disjoint (Set.range (F.curve.marking i))
        (Set.range (basepointInclusion L U))

/-- The actual outside-base map, fixed by a full equivariant torsor comparison. -/
structure OffBaseMap (Q : StableGITTarget G W L) where
  map : nonbaseOver F B U ⟶ Q.target
  source : Reindex G F.quotient.torsor (nonbaseCurveMap F B U)
  target : Reindex G Q.point.torsor map
  comparison : QuotientIso G W
    (reindexObject G W F.quotient (nonbaseCurveMap F B U) source)
    (reindexObject G W Q.point map target)

/-- An individual regular map extends this actual outside-base map, with
its regular torsor computed from the same stable-locus quotient. -/
structure RegularizedMap (Q : StableGITTarget G W L) (O : OffBaseMap F B U Q) where
  map : Over.mk (F.curve.π ≫ T.hom) ⟶ Q.target
  extension : nonbaseCurveMap F B U ≫ map = O.map
  regularTorsor : Reindex G Q.point.torsor map

/-- The regular quasimap is the literal reindexed stable-locus torsor and map. -/
def RegularizedMap.point {Q : StableGITTarget G W L} {O : OffBaseMap F B U Q}
    (R : RegularizedMap F B U Q O) : QuotientObject G W (Over.mk (F.curve.π ≫ T.hom)) :=
  reindexObject G W Q.point R.map R.regularTorsor

/-- A line-degree packet for an individual complex curve. -/
structure IndividualDegrees
    {F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ))))}
    {B : AssociatedFamily F} {U : AssociatedUnstable L F.quotient B}
    {Q : StableGITTarget G W L} {O : OffBaseMap F B U Q}
    (R : RegularizedMap F B U Q O) where
  original : InducedDegrees G W F.quotient
  originalBeta : DegreeFunctional original
  regular : InducedDegrees G W R.point
  regularBeta : DegreeFunctional regular

/-- The defect is a Picard functional evaluated only on the chosen polarization. -/
def thetaDegreeDefect
    {F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ))))}
    {B : AssociatedFamily F} {U : AssociatedUnstable L F.quotient B}
    {Q : StableGITTarget G W L} {O : OffBaseMap F B U Q}
    {R : RegularizedMap F B U Q O} (D : IndividualDegrees R) : ℤ :=
  D.originalBeta.beta (lineClass G W L.line) - D.regularBeta.beta (lineClass G W L.line)

/-- Total length sums the source-normalized rational lengths over the actual base support. -/
def totalBasepointLength (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ)))))
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B) (h : IsPrestable F B U)
    (D : ∀ x : F.curve.X, BasepointLength G W F.quotient L x) : ℚ :=
  ∑ x ∈ h.1.toFinset, (D x).value

/-- A family shrinking is an actual open parameter and an actual Cartesian
curve/torsor family restriction. It contains no blanket regularization law. -/
def openParameterMap (T : Over (Spec (.of ℂ))) (V : T.left.Opens) :
    Over.mk (V.ι ≫ T.hom) ⟶ T := Over.homMk V.ι (by rfl)

structure FamilyShrinking where
  parameter : T.left.Opens
  nonempty : Nonempty parameter
  curve : CurveReindex F (openParameterMap T parameter)
  torsor : Reindex G F.quotient.torsor curve.overMap
  bundle : AssociatedFamily
    (reindexFamily F (openParameterMap T parameter) curve torsor)
  bundleComparison : AssociatedFamilyReindex F (openParameterMap T parameter)
    curve torsor B bundle
  unstable : AssociatedUnstable L
    (reindexFamily F (openParameterMap T parameter) curve torsor).quotient bundle
  basepointMap : basepointScheme L unstable ⟶ basepointScheme L U
  basepoint_square : IsPullback basepointMap (basepointInclusion L unstable)
    (basepointInclusion L U) curve.map

/-- The actual family after the specified shrinking. -/
@[implicit_reducible]
def FamilyShrinking.family (D : FamilyShrinking F B U) :
    Family G W n g (Over.mk (D.parameter.ι ≫ T.hom)) :=
  reindexFamily F (openParameterMap T D.parameter) D.curve D.torsor

end MathlibExt.AlgebraicGeometry.QuasimapRegularizationModels
