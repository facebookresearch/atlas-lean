/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.QuasiSeparated
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
public import MathlibExt.AlgebraicGeometry.IntegralTiltModels

/-!
# Actual geometric point fields and finite geometric transcendence bounds

Geometric point fields are complete algebraically closed nonarchimedean
fields with their actual perfectoid pair and scalar map. Their residue
embedding is fixed on the native fraction field of the valuation support,
and its algebraic elements are dense. Thus no freely enlarged field is
silently substituted for the completed geometric residue field.

The bound tr.gc <= n uses a further complete algebraically closed field
extension and an actual dense intermediate subfield of transcendence
degree <= n. It is the source's geometric topological transcendence
degree, not the ordinary algebraic transcendence degree of a completion.
Totally disconnected affines retain the actual splitting of every open
cover. These bounds qualify local affine coefficient identifications.

Sources: Scholze, arXiv:1709.07343v4, Definitions 7.1, 21.2, the paragraph
following Question 21.4 and Definitions 21.5--21.7; Anschuetz--Mann,
arXiv:2403.01951v2, Theorem 1.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds

open CategoryTheory TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels
open AffinePerfectoidVSite

variable (p : ℕ) [Fact p.Prime]

/-- An actual complete algebraically closed nonarchimedean point field. -/
structure GeometricField where
  carrier : Type
  [normedField : NormedField carrier]
  [complete : CompleteSpace carrier]
  [algebraicallyClosed : IsAlgClosed carrier]
  nonarchimedean : ∀ a b : carrier, ‖a + b‖ ≤ max ‖a‖ ‖b‖
  pair : Affine p
  ringEquiv : pair.ring ≃+* carrier
  continuous : Continuous ringEquiv
  continuous_inverse : Continuous ringEquiv.symm
  plus_valuation : ∀ a : carrier,
    ringEquiv.symm a ∈ pair.plus ∨ ringEquiv.symm (a⁻¹) ∈ pair.plus

attribute [instance] GeometricField.normedField GeometricField.complete
  GeometricField.algebraicallyClosed

/-- The native prime support of the actual all-rank valuation point. -/
def pointSupport (P : Affine p) (x : P.toHuberPair.Space) : Ideal P.ring :=
  let : ValuativeRel P.ring := x.1.relation
  ValuativeRel.supp P.ring

instance pointSupport_prime (P : Affine p) (x : P.toHuberPair.Space) :
    (pointSupport p P x).IsPrime := by
  let : ValuativeRel P.ring := x.1.relation
  change (ValuativeRel.supp P.ring).IsPrime
  infer_instance

/-- The actual residue fraction field, before completion and algebraic closure. -/
abbrev PointResidue (P : Affine p) (x : P.toHuberPair.Space) :=
  FractionRing (P.ring ⧸ pointSupport p P x)

/-- The actual scalar map to the residue fraction field. -/
def pointResidueMap (P : Affine p) (x : P.toHuberPair.Space) :
    P.ring →+* PointResidue p P x :=
  (algebraMap _ _).comp (Ideal.Quotient.mk (pointSupport p P x))

/-- A geometric field at a specified actual valuation point. -/
structure GeometricPoint (P : Affine p) (x : P.toHuberPair.Space) where
  field : GeometricField p
  map : RingMap P.toHuberPair field.pair.toHuberPair
  point : field.pair.toHuberPair.Space
  closed_point : ∀ a b : field.carrier,
    point.1.relation.vle (field.ringEquiv.symm a) (field.ringEquiv.symm b) ↔
      a = 0 ∨ b ≠ 0 ∧ field.ringEquiv.symm (a / b) ∈ field.pair.plus
  point_normalized : map.spa point = x
  residueEmbedding : PointResidue p P x →+* field.carrier
  scalar_normalized : field.ringEquiv.toRingHom.comp map.hom =
    residueEmbedding.comp (pointResidueMap p P x)
  dense_algebraic :
    letI := residueEmbedding.toAlgebra
    Dense {a : field.carrier | IsAlgebraic (PointResidue p P x) a}

/-- A compatible system of actual geometric point fields for an actual perfectoid map: each field
extension is compatible with the scalar maps and sends the selected geometric point of the source
to that of the target. -/
structure GeometricFieldSystem {P Q : Affine p} (f : P ⟶ Q) where
  source : ∀ x : P.toHuberPair.Space, GeometricPoint p P x
  target : ∀ x : P.toHuberPair.Space, GeometricPoint p Q (spaceMap p f x)
  extension : ∀ x : P.toHuberPair.Space,
    RingMap (target x).field.pair.toHuberPair (source x).field.pair.toHuberPair
  normalized : ∀ x : P.toHuberPair.Space,
    (extension x).hom.comp (target x).map.hom = (source x).map.hom.comp f.hom
  point_normalized : ∀ x : P.toHuberPair.Space,
    (extension x).spa (source x).point = (target x).point

variable {p}

/-- The actual scalar field map induced by the fixed pair map. -/
def fieldMap {K L : GeometricField p}
    (f : RingMap K.pair.toHuberPair L.pair.toHuberPair) : K.carrier →+* L.carrier :=
  L.ringEquiv.toRingHom.comp (f.hom.comp K.ringEquiv.symm.toRingHom)

/-- The source's bound tr.gc <= n, through an actual complete algebraically closed extension. -/
def HasGeometricTrdegLE {K L : GeometricField p}
    (f : RingMap K.pair.toHuberPair L.pair.toHuberPair) (n : ℕ) : Prop :=
  ∃ (E : GeometricField p) (g : RingMap L.pair.toHuberPair E.pair.toHuberPair),
    letI := ((fieldMap g).comp (fieldMap f)).toAlgebra
    ∃ M : IntermediateField K.carrier E.carrier,
      Dense (M : Set E.carrier) ∧
        ∃ m : ℕ, m ≤ n ∧ ∃ t : Fin m → M, IsTranscendenceBasis K.carrier t

variable (p)

/-- Actual affine total disconnectedness (Scholze, *Étale cohomology of diamonds*, Def. 7.1): the
space is quasicompact and quasi-separated, and every open cover splits. -/
def IsTotallyDisconnected (P : Affine p) : Prop :=
  IsCompact (Set.univ : Set P.toHuberPair.Space) ∧
    QuasiSeparatedSpace P.toHuberPair.Space ∧
    ∀ (I : Type 1) (U : I → Opens P.toHuberPair.Space),
      (∀ x : P.toHuberPair.Space, ∃ i, x ∈ U i) →
      ∃ s : P.toHuberPair.Space → Σ i, U i,
        Continuous s ∧ ∀ x, (s x).2.val = x

/-- The finite dim.trg certificate is a uniform bound on these actual field extensions. -/
def HasFiniteDimTrg {P Q : Affine p} (f : P ⟶ Q)
    (G : GeometricFieldSystem p f) : Prop :=
  ∃ n : ℕ, ∀ x : P.toHuberPair.Space, HasGeometricTrdegLE (G.extension x) n

/-- Exactly the geometric qualification used for local integral coefficient identification. -/
def HasBoundedTotallyDisconnectedMap (P : Affine p) : Prop :=
  ∃ (Q : Affine p) (f : P ⟶ Q) (G : GeometricFieldSystem p f),
    IsTotallyDisconnected p Q ∧ HasFiniteDimTrg p f G

end MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds
