/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GraphCotangentLines
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Actual Chow-valued Pixton graph expressions

Each psi is the first Chern cap of its computed cotangent line. Powers and
products are literal compositions of these operators on Kresch rational
Chow groups. The graph class is applied to its atlas-normalized fundamental
cycle and pushed along the actual family-normalized clutching morphism.

Leg coefficients are exp(a_i^2 psi_i). Edge coefficients are those of
(1-exp(-w(h)w(h')(psi_h+psi_h')))/(psi_h+psi_h'). The graph codimension
|E| is included before degree extraction. Both |Aut(Gamma)| and r^h1
denominators are retained. Polynomial coefficients below are Chow classes,
not rational scalar substitutes.
Source: JPPZ arXiv:1602.04705v2, Equation (7), printed pp10--11.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PixtonChowOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StackCycleGeometry StackCycleRelations StackChowGroups StackFirstChernOperators
open StableCurveStackModels StableGraphCurveGluing GraphClutchingModels GraphCotangentLines
open UniversalCurveStability PixtonWeightings
open scoped BigOperators

variable {k : Type} [Field k]
  {D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)} {K : KreschPresentation D}

abbrev GradedChow (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X) :=
  ∀ d : ℤ, RationalChowGroup D K X hX d

def gradedFirstChern {X : Stack (Spec (.of k))} {hX : FiniteTypeArtin k X}
    {E : StackVectorBundles.VectorBundle X} (C : FirstChernData D K hX E) :
    Module.End ℚ (GradedChow (D := D) (K := K) X hX) :=
  LinearMap.pi (fun d =>
    (rationalMap (chowRegrade D K X hX (by omega))).comp
      ((rationalFirstChern C (d + 1)).comp (LinearMap.proj (d + 1))))

def supportedClass {X : Stack (Spec (.of k))} {hX : FiniteTypeArtin k X}
    (d : ℤ) (a : RationalChowGroup D K X hX d) : GradedChow (D := D) (K := K) X hX :=
  fun e => if h : d = e then rationalMap (chowRegrade D K X hX h) a else 0

def gradedPush {X Y : Stack (Spec (.of k))} {hX : FiniteTypeArtin k X}
    {hY : FiniteTypeArtin k Y} {p : StackHom X Y}
    (P : ProjectiveChowPushData D K hX hY p) :
    GradedChow (D := D) (K := K) X hX →ₗ[ℚ] GradedChow (D := D) (K := K) Y hY :=
  LinearMap.pi (fun d => (rationalMap (P.map d)).comp (LinearMap.proj d))

def edgeCoefficient (c : ℚ) (p q : ℕ) : ℚ :=
  (-1) ^ (p + q) * c ^ (p + q + 1) * ((p + q).choose p : ℚ) /
    ((p + q + 1).factorial : ℚ)

variable {g n : ℕ} (G : StableGraph g n)

abbrev Exponent (d : ℕ) := HalfEdge G → Fin (d + 1)

def totalExponent {d : ℕ} (e : Exponent G d) : ℕ := ∑ h, (e h).val

def decoratedCodimension {d : ℕ} (e : Exponent G d) : ℕ := G.edges + totalExponent G e

def decorationCoefficient (a : Fin n → ℤ) (r : ℕ) [NeZero r]
    (w : Weighting G a r) {d : ℕ} (e : Exponent G d) : ℚ :=
  (∏ i : Fin n,
    (a i : ℚ) ^ (2 * (e (Sum.inl i)).val) / ((e (Sum.inl i)).val.factorial : ℚ)) *
  ∏ j : Fin G.edges,
    edgeCoefficient ((w.val (j, 0)).val * (w.val (j, 1)).val : ℚ)
      (e (Sum.inr (j, 0))).val (e (Sum.inr (j, 1))).val

variable
  (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v))
  (P : GraphProductData G V) (M : StableCurveStackModel (k := k) g n)
  (C : GraphClutchingData G V P M)

/-- Every geometric factor is tied to the same actual graph families and maps. -/
structure GraphChowData where
  cotangent : ∀ h : HalfEdge G,
    CotangentLine (V (vertexOf G h)) (P.vertex (vertexOf G h)) (halfEdgeIndex G h)
  chern : ∀ h : HalfEdge G, FirstChernData D K P.finiteType (cotangent h).line
  fundamental : FundamentalCycleData D P.stack P.finiteType
    (3 * (g : ℤ) - 3 + n - G.edges)
  classes : CycleClassData D K P.stack P.finiteType
  push : ProjectiveChowPushData D K P.finiteType M.finiteType C.clutch

variable (B : GraphChowData (D := D) (K := K) G V P M C)

def cotangentWord {d : ℕ} (e : Exponent G d) :
    Module.End ℚ (GradedChow (D := D) (K := K) P.stack P.finiteType) :=
  (List.ofFn (fun i : Fin (Fintype.card (HalfEdge G)) =>
    (Fintype.equivFin (HalfEdge G)).symm i)).foldr
      (fun h A => gradedFirstChern (B.chern h) ^ (e h).val * A) 1

def graphFundamental : GradedChow (D := D) (K := K) P.stack P.finiteType :=
  supportedClass (3 * (g : ℤ) - 3 + n - G.edges)
    (rationalCycleClass D K B.classes (3 * (g : ℤ) - 3 + n - G.edges) B.fundamental.cycle)

/-- The finite sum is extracted in codimension d only after the actual
clutching push; its edge codimension is retained in the admissible decorations. -/
def weightedGraphClass (a : Fin n → ℤ) (d r : ℕ) (positive : 0 < r) :
    RationalChowGroup D K M.stack M.finiteType (3 * (g : ℤ) - 3 + n - d) := by
  classical
  letI : NeZero r := ⟨ne_of_gt positive⟩
  exact
    ((1 : ℚ) / ((automorphismOrder G : ℚ) * (r : ℚ) ^ firstBetti G)) •
      ∑ w : Weighting G a r, ∑ e : Exponent G d,
        if decoratedCodimension G e = d then
          decorationCoefficient G a r w e •
            (gradedPush B.push (cotangentWord G V P M C B e (graphFundamental G V P M C B)))
              (3 * (g : ℤ) - 3 + n - d)
        else 0

/-- A polynomial in r with actual Chow-valued coefficients. -/
abbrev ChowPolynomial (d : ℕ) :=
  ℕ →₀ RationalChowGroup D K M.stack M.finiteType (3 * (g : ℤ) - 3 + n - d)

def evaluateChowPolynomial {d : ℕ} (p : ChowPolynomial (D := D) (K := K) M d) (r : ℚ) :=
  p.sum (fun i c => r ^ i • c)

end MathlibExt.AlgebraicGeometry.PixtonChowOperators
