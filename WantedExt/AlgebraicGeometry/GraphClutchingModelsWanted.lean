/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PixtonChowPolynomialModels

/-!
# Geometric stable-graph, cotangent and Pixton construction requests

These constructors use actual vertex marked curves, their scheme quotient,
native stack arrows/base changes, section-normalized cotangent modules,
and Chow-valued graph sums. Source scalar weights and ordinary scheme
Chow operators are reused. No rubber double-ramification class is defined
by the desired Pixton formula.
Source: JPPZ arXiv:1602.04705v2, Sections 0.3.2--0.4.2, printed pp8--11.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GraphClutchingModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open UniversalCurveStability StableCurveStackModels StableGraphCurveGluing GraphClutchingModels
open GraphCotangentLines PixtonChowOperators PixtonChowPolynomialModels
open StackCycleGeometry StackCycleRelations StackChowGroups
open scoped BigOperators

def_wanted stableGraphCatalogue (g n : ℕ) : GraphCatalogue g n

def_wanted stableCurveNodeGluing (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {g n : ℕ} (G : StableGraph g n) (T : Over (Spec (.of k))) (F : VertexFamilies G T) :
    CurveGluing G T F

def_wanted graphProductStack (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {g n : ℕ} (G : StableGraph g n)
    (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v)) :
    GraphProductData G V

def_wanted geometricGraphClutching (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {g n : ℕ} (G : StableGraph g n)
    (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v))
    (P : GraphProductData G V) (M : StableCurveStackModel (k := k) g n) :
    GraphClutchingData G V P M

def_wanted stableCurveCotangentLine (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    (X : Stack (Spec (.of k))) (p : StackHom X M.stack) (i : Fin n) :
    CotangentLine M p i

def_wanted geometricGraphChowData (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    {g n : ℕ} (G : StableGraph g n)
    (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v))
    (P : GraphProductData G V) (M : StableCurveStackModel (k := k) g n)
    (C : GraphClutchingData G V P M) :
    GraphChowData (D := D) (K := K) G V P M C

def_wanted geometricPixtonPolynomial
    (D : CycleConstructionData (Spec (.of ℂ)) (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
    {g n : ℕ} (stable_range : 0 < 2 * (g : ℤ) - 2 + n)
    (L : GraphCatalogue g n) (M : StableCurveStackModel (k := ℂ) g n)
    (B : CatalogueGeometry (D := D) (K := K) L M) (a : Fin n → ℤ)
    (balanced : (∑ i, a i) = 0) (d : ℕ) : PixtonPolynomial (D := D) (K := K) L M B a d

theorem_wanted geometricPixtonPolynomialUnique
    (D : CycleConstructionData (Spec (.of ℂ)) (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
    {g n : ℕ} (L : GraphCatalogue g n) (M : StableCurveStackModel (k := ℂ) g n)
    (B : CatalogueGeometry (D := D) (K := K) L M) (a : Fin n → ℤ) (d : ℕ)
    (P Q : PixtonPolynomial (D := D) (K := K) L M B a d) :
    P.coefficients = Q.coefficients

end WantedExt.AlgebraicGeometry.GraphClutchingModelsWanted
