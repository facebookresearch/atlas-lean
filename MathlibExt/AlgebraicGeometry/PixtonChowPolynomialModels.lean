/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PixtonChowOperators

/-!
# Geometric Pixton polynomials with Chow-valued coefficients

The catalogue contains one representative of each actual stable-graph
isomorphism class. Its geometric entries use the actual vertex families,
clutching maps, cotangent lines and graph fundamental cycles. The resulting
sum is the actual rational Chow expression in Equation (7). Its eventual
polynomial has coefficients in that same Chow group; the value at zero is
the actual constant Chow class.
Source: JPPZ arXiv:1602.04705v2, Equation (7), Proposition 3, printed pp10--11.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PixtonChowPolynomialModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open UniversalCurveStability StableCurveStackModels StableGraphCurveGluing
open GraphClutchingModels PixtonChowOperators
open StackCycleGeometry StackCycleRelations StackChowGroups
open scoped BigOperators

structure GraphCatalogue (g n : ℕ) where
  size : ℕ
  graph : Fin size → StableGraph g n
  exhaustive : ∀ G : StableGraph g n, ∃ i : Fin size, Nonempty (GraphIso G (graph i))
  distinct : ∀ i j : Fin size, Nonempty (GraphIso (graph i) (graph j)) → i = j

variable {k : Type} [Field k] {g n : ℕ}
  {D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)} {K : KreschPresentation D}
  (L : GraphCatalogue g n) (M : StableCurveStackModel (k := k) g n)

structure CatalogueGeometry where
  vertex : ∀ i : Fin L.size, ∀ v : Fin (L.graph i).vertices,
    StableCurveStackModel (k := k) ((L.graph i).genus v) (vertexValence (L.graph i) v)
  product : ∀ i : Fin L.size, GraphProductData (L.graph i) (vertex i)
  clutch : ∀ i : Fin L.size, GraphClutchingData (L.graph i) (vertex i) (product i) M
  chow : ∀ i : Fin L.size,
    GraphChowData (D := D) (K := K) (L.graph i) (vertex i) (product i) M (clutch i)

variable (B : CatalogueGeometry (D := D) (K := K) L M)

def pixtonClassAt (a : Fin n → ℤ) (d r : ℕ) (positive : 0 < r) :
    RationalChowGroup D K M.stack M.finiteType (3 * (g : ℤ) - 3 + n - d) :=
  ∑ i : Fin L.size,
    weightedGraphClass (L.graph i) (B.vertex i) (B.product i) M (B.clutch i) (B.chow i)
      a d r positive

/-- Eventual polynomial agreement is for the fixed actual geometric graph sum. -/
structure PixtonPolynomial (a : Fin n → ℤ) (d : ℕ) where
  coefficients : ChowPolynomial (D := D) (K := K) M d
  eventual : ∃ N : ℕ, ∀ (r : ℕ) (positive : 0 < r), N ≤ r →
    evaluateChowPolynomial M coefficients (r : ℚ) = pixtonClassAt L M B a d r positive

def pixtonConstant {a : Fin n → ℤ} {d : ℕ}
    (Q : PixtonPolynomial (D := D) (K := K) L M B a d) :
    RationalChowGroup D K M.stack M.finiteType (3 * (g : ℤ) - 3 + n - d) :=
  Q.coefficients 0

end MathlibExt.AlgebraicGeometry.PixtonChowPolynomialModels
