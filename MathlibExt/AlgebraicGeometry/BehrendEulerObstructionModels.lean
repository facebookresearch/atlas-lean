/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NashBlowupModels
public import MathlibExt.AlgebraicGeometry.OrdinaryNormalConeModels
public import MathlibExt.AlgebraicGeometry.ConeSegreOperations
public import MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

/-!
# Euler obstruction and the canonical scheme Behrend weight

Euler obstruction is degree on the actual Nash point fibre of
c(T_tilde)∩s(fibre,V_tilde). The fibre, tangent bundle, ordinary
normal cone, general cone completion, Chern caps and residue-degree
map are the specified native objects and operations.

The weight on a closed embedding is the linear Euler obstruction
of its distinguished normal-cone cycle. Every summand uses the
actual prime image closure. A scheme Behrend model agrees with
this formula on a genuine open cover and has a genuine finite
constructible presentation. No independent weight function is an
input. Construction and chart-independence remain separate requests.

Reference: Behrend, arXiv:math/0507523v2, §1.1–1.2,
equation (3), Definition 1.4 and Proposition 1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BehrendEulerObstructionModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open IntegralChowChernModels GradedConeProjectiveModels OrdinaryNormalConeModels
open NashBlowupModels ConeSegreOperations ConstructibleEulerCharacteristics
open ComplexAnalytification

/-- All terms in formula (3) are attached to the literal Nash point fibre. -/
structure EulerObstructionData (V : SchemeData) where
  nash : NashModel V
  fibre : ∀ p : space V.scheme, FibreGeometry nash p
  normal : ∀ p : space V.scheme, OrdinaryNormalCone (fibreInclusion (fibre p))
  segre : ∀ p : space V.scheme, SegreData (normal p).cone
  chern : ∀ p : space V.scheme,
    ChernConstruction (fibreData (fibre p))
      ((Scheme.Modules.pullback (fibreInclusion (fibre p)).left).obj
        (nashTangent nash.grassmannian nash.smooth)) nash.dimension.dimension
  degree : ∀ p : space V.scheme,
    letI : IsProper (fibreData (fibre p)).scheme.hom := by
      change IsProper (fibreStructure nash p)
      exact (fibre p).proper
    IntegerSchemeChow.DegreeComparison (fibreData (fibre p))

/-- Behrend's actual Euler-obstruction formula Eu_V(p). -/
def eulerObstruction {V : SchemeData} (D : EulerObstructionData V) (p : space V.scheme) : ℤ := by
  letI : IsProper (fibreData (D.fibre p)).scheme.hom := by
    change IsProper (fibreStructure D.nash p)
    exact (D.fibre p).proper
  exact chernSegreDegree (D.segre p) (D.chern p) (D.degree p)

/-- The subvariety is the native kernel closure of the actual prime point. -/
structure PrimeClosureModel (X : SchemeData) (x : X.scheme.left) where
  variety : SchemeData
  normalized : variety.scheme =
    Over.mk (GeometricChowOperators.pointInclusion X.scheme.left x ≫ X.scheme.hom)

def primeInclusion {X : SchemeData} {x : X.scheme.left} (P : PrimeClosureModel X x) :
    P.variety.scheme ⟶ X.scheme := by
  rw [P.normalized]
  exact Over.homMk (GeometricChowOperators.pointInclusion X.scheme.left x) rfl

structure PrimeEulerData (X : SchemeData) (x : X.scheme.left) where
  closure : PrimeClosureModel X x
  euler : EulerObstructionData closure.variety

/-- Extend Eu_V by zero along the actual closed prime-subvariety map. -/
def primeEuler {X : SchemeData} {x : X.scheme.left} (D : PrimeEulerData X x)
    (p : space X.scheme) : ℤ := by
  classical
  exact if h : ∃ q : space D.closure.variety.scheme, spaceMap (primeInclusion D.closure) q = p
    then eulerObstruction D.euler (Classical.choose h) else 0

/-- Linear Euler obstruction of an actual nonhomogeneous integer cycle. -/
def cycleEuler (X : SchemeData) (c : AlgebraicCycle X.scheme.left ℤ)
    (D : ∀ x : X.scheme.left, PrimeEulerData X x) (p : space X.scheme) : ℤ :=
  (cycleFinsupp X.scheme.left c).sum (fun x n => n * primeEuler (D x) p)

/-- Closed-embedding weight data have the actual ordinary normal cone and its sign profile. -/
structure EmbeddingWeightData (X : SchemeData) where
  ambient : SchemeData
  embedding : X.scheme ⟶ ambient.scheme
  [closed : IsClosedImmersion embedding.left]
  [smooth : Smooth ambient.scheme.hom]
  normal : OrdinaryNormalCone embedding
  dimension : DistinguishedDimension normal
  euler : ∀ x : X.scheme.left, PrimeEulerData X x

/-- The intrinsic candidate ν_X=Eu(c_(X/M)) is explicitly computed. -/
def embeddingWeight {X : SchemeData} (D : EmbeddingWeightData X) : space X.scheme → ℤ :=
  cycleEuler X (distinguishedCycle D.normal D.dimension) D.euler

/-- The actual scheme over an open-cover chart. -/
def chartScheme (X : SchemeData) (C : X.scheme.left.OpenCover.{0}) (i : C.I₀) :
    Over (Spec (.of ℂ)) := Over.mk (C.f i ≫ X.scheme.hom)

def chartInclusion {X : SchemeData} {C : X.scheme.left.OpenCover.{0}} {i : C.I₀}
    (U : SchemeData) (h : U.scheme=chartScheme X C i) : U.scheme ⟶ X.scheme := by
  rw [h]
  exact Over.homMk (C.f i) rfl

/-- A canonical weight is fixed by ordinary normal-cone/Nash formulas on a real cover. -/
structure SchemeBehrendModel (X : SchemeData) where
  cover : X.scheme.left.OpenCover.{0}
  chart : cover.I₀ → SchemeData
  chart_normalized : ∀ i, (chart i).scheme=chartScheme X cover i
  localWeight : ∀ i, EmbeddingWeightData (chart i)
  value : space X.scheme → ℤ
  complexCover : ∀ p : space X.scheme, ∃ (i : cover.I₀) (q : space (chart i).scheme),
    spaceMap (chartInclusion (chart i) (chart_normalized i)) q=p
  normalized : ∀ (i : cover.I₀) (q : space (chart i).scheme),
    value (spaceMap (chartInclusion (chart i) (chart_normalized i)) q)=
      embeddingWeight (localWeight i) q
  constructible : ConstructiblePresentation X.scheme value

end MathlibExt.AlgebraicGeometry.BehrendEulerObstructionModels
