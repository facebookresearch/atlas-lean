/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapRegularizationModels
public import MathlibExt.AlgebraicGeometry.RationalResolution

/-!
# Constant-defect loci and common-curve quasimap regularization

This is the restricted family situation used in the proof of
Theorem 7.1.6: a smooth curve parameter, smooth total curve, irreducible
geometric fibres, basepoints presented by actual sections, and their
source-normalized rational lengths constant along those sections.

A family regularization keeps the specified shrinking and a common
marked source modification. All added markings come from those actual
basepoint sections. The regular target map agrees outside the common
basepoint scheme through the full torsor comparison. Both contractions
retain the actual canonical structure-sheaf map and R¹ vanishing.

No arbitrary-family flat base locus, constancy of length, or same-curve
base-change regularization theorem is asserted.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
proof of Theorem 7.1.6, pp. 44–45, equations (7.1.5)–(7.1.7).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapConstantDefectFamilies

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GroupTorsorGeometry QuasimapAssociatedFamilies
open QuasimapBasepointDefects QuasimapSectionLengths QuasimapPicardDegrees
open QuasimapInvariantAlgebras QuasimapRegularizationModels
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

variable {G W : Over (Spec (.of ℂ))} [GrpObj G] [ModObj G W]
variable [IsAffine G.left] [IsAffine W.left]
variable {L : CharacterPolarization G W} [InvariantAlgebraModel G W L]
variable {n g : ℕ} {T : Over (Spec (.of ℂ))}
variable (F : Family G W n g T) (B : AssociatedFamily F)
variable (U : AssociatedUnstable L F.quotient B)

/-- The literal geometric source fibre, viewed over the original complex base. -/
def fibreOver (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T.left) :
    Over (Spec (.of ℂ)) :=
  Over.mk (pullback.snd F.curve.π p ≫ p ≫ T.hom)

def fibreMap (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T.left) :
    fibreOver F Ω p ⟶ Over.mk (F.curve.π ≫ T.hom) :=
  Over.homMk (pullback.fst F.curve.π p) (by
    change pullback.fst F.curve.π p ≫ (F.curve.π ≫ T.hom) =
      pullback.snd F.curve.π p ≫ p ≫ T.hom
    rw [← Category.assoc, pullback.condition, Category.assoc])

def fibreSection (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ T.left)
    (s : T.left ⟶ F.curve.X) (hs : s ≫ F.curve.π = 𝟙 T.left) :
    Spec (.of Ω) ⟶ (fibreOver F Ω p).left :=
  pullback.lift (p ≫ s) (𝟙 _) (by simp [Category.assoc, hs])

/-- The paper's explicitly restricted, section-presented constant-length locus. -/
structure ConstantDefectPresentation where
  parameter_nonempty : Nonempty T.left
  [parameter_smooth : SmoothOfRelativeDimension 1 T.hom]
  [total_smooth : Smooth (F.curve.π ≫ T.hom)]
  irreducible : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left),
    IrreducibleSpace (fibreOver F Ω p).left
  count : ℕ
  basepoint : Fin count → (T.left ⟶ F.curve.X)
  section_eq : ∀ i, basepoint i ≫ F.curve.π = 𝟙 T.left
  support : Set.range (basepointInclusion L U) = ⋃ i : Fin count, Set.range (basepoint i)
  disjoint : Pairwise fun i j => Disjoint (Set.range (basepoint i)) (Set.range (basepoint j))
  lengths : Fin count → ℚ
  fibreTorsor : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left),
    Reindex G F.quotient.torsor (fibreMap F Ω p)
  fibreLength : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left)
    (i : Fin count),
    BasepointLength G W
      (reindexObject G W F.quotient (fibreMap F Ω p) (fibreTorsor Ω p)) L
      (fibreSection F Ω p (basepoint i) (section_eq i) (IsLocalRing.closedPoint Ω))
  smooth_basepoints : ∀ i x, x ∈ Set.range (basepoint i) →
    (F.curve.π.stalkMap x).hom.FormallySmooth
  avoid_markings : ∀ i j, Disjoint (Set.range (basepoint i)) (Set.range (F.curve.marking j))
  constant_length : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left)
    (i : Fin count), (fibreLength Ω p i).value = lengths i

/-- A curve map over the actual parameter induces the literal quotient-point pullback. -/
def curveMapOver {m : ℕ} (C : MarkedFamily T.left m g) (c : C.X ⟶ F.curve.X)
    (h : c ≫ F.curve.π = C.π) :
    Over.mk (C.π ≫ T.hom) ⟶ Over.mk (F.curve.π ≫ T.hom) :=
  Over.homMk c (by
    change c ≫ (F.curve.π ≫ T.hom) = C.π ≫ T.hom
    rw [← Category.assoc, h])

@[implicit_reducible]
def onCurve {m : ℕ} (C : MarkedFamily T.left m g) (c : C.X ⟶ F.curve.X)
    (h : c ≫ F.curve.π = C.π)
    (P : Reindex G F.quotient.torsor (curveMapOver F C c h)) :
    Family G W m g T where
  curve := C
  quotient := reindexObject G W F.quotient (curveMapOver F C c h) P

/-- A genuine source modification uses the native structure-sheaf map. -/
def IsCanonicalGenusContraction {C D : Scheme} (c : C ⟶ D) : Prop :=
  IsProper c ∧ Function.Surjective c ∧ IsIso (RationalResolution.structureUnit c) ∧
    IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (CoherentCurveLinearSeries.structureModule C))

/-- Family regularization after the actual shrinking and source modification.
Its target map is tied to the original quasimap by the outside-base torsor comparison. -/
structure CommonCurveRegularization (Q : StableGITTarget G W L) where
  shrinking : FamilyShrinking F B U
  constant : ConstantDefectPresentation shrinking.family shrinking.bundle shrinking.unstable
  regularCurve : MarkedFamily shrinking.parameter.toScheme (n + constant.count) g
  common : MarkedFamily shrinking.parameter.toScheme (n + constant.count) g
  toOriginal : common.X ⟶ shrinking.curve.curve.X
  toRegular : common.X ⟶ regularCurve.X
  original_over : toOriginal ≫ shrinking.curve.curve.π = common.π
  regular_over : toRegular ≫ regularCurve.π = common.π
  original_marks : ∀ i : Fin n,
    common.marking (Fin.castAdd constant.count i) ≫ toOriginal = shrinking.curve.curve.marking i
  basepoint_marks : ∀ i : Fin constant.count,
    common.marking (Fin.natAdd n i) ≫ toOriginal = constant.basepoint i
  regular_marks : ∀ i, common.marking i ≫ toRegular = regularCurve.marking i
  original_contraction : IsCanonicalGenusContraction toOriginal
  regular_contraction : IsCanonicalGenusContraction toRegular
  map : regularCurve.X ⟶ Q.target.left
  over : map ≫ Q.target.hom = regularCurve.π ≫ shrinking.parameter.ι ≫ T.hom
  commonTorsor : Reindex G shrinking.family.quotient.torsor
    (curveMapOver shrinking.family common toOriginal original_over)
  bundle : AssociatedFamily (onCurve shrinking.family common toOriginal original_over commonTorsor)
  unstable : AssociatedUnstable L
    (onCurve shrinking.family common toOriginal original_over commonTorsor).quotient bundle
  offBase : OffBaseMap
    (onCurve shrinking.family common toOriginal original_over commonTorsor) bundle unstable Q
  agreement :
    nonbaseCurveMap (onCurve shrinking.family common toOriginal original_over commonTorsor)
        bundle unstable ≫
      Over.homMk (toRegular ≫ map) (by
        change (toRegular ≫ map) ≫ Q.target.hom =
          common.π ≫ (shrinking.parameter.ι ≫ T.hom)
        rw [Category.assoc, over, ← Category.assoc, regular_over]) =
      offBase.map

/-- Existing basepoint labels and constant defects are transported through
the actual shrinking curve map, up to the specified finite relabelling. -/
structure CommonNormalization (K : ConstantDefectPresentation F B U)
    {Q : StableGITTarget G W L} (R : CommonCurveRegularization F B U Q) where
  labels : Fin R.constant.count ≃ Fin K.count
  section_normalized : ∀ i, R.constant.basepoint i ≫ R.shrinking.curve.map =
    R.shrinking.parameter.ι ≫ K.basepoint (labels i)
  length_normalized : ∀ i, R.constant.lengths i = K.lengths (labels i)

end MathlibExt.AlgebraicGeometry.QuasimapConstantDefectFamilies
