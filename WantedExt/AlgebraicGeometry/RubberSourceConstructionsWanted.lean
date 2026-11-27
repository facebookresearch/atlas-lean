/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LiFamilySourceDescent
public import MathlibExt.AlgebraicGeometry.RubberPOTSourceCharts

/-!
# Native framed-rubber source construction requests

The actual schemes, module coefficients, standard-target frames, torus
actions/jets, marked-curve universal extension, Cech differences and Lie
quotient are already fixed in MathlibExt. The source construction refines
the affine atlas where its finite-free frames and target coordinates are
available. It assumes no double-ramification or graph-sum comparison.
Source: Jun Li arXiv:math/0009097v1 and math/0110113v1, Sections1 and4;
JPPZ arXiv:1602.04705v2, Section0.2.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RubberSourceConstructionsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpansionParameterModels RubberMapFamilies RubberModuliStackModels
open scoped BigOperators

def_wanted nativeOriginalRubberScaling (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (m : ℕ) (H : TorusTheory k (m + 1)) : RubberStandardScalingModels.OriginalAction O P D m H

def_wanted nativeStandardRubberScaling (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    (m : ℕ) (H : TorusTheory k (m + 1)) : RubberStandardScalingModels.StandardAction O P D R S m H

def_wanted nativeTorusActionEtaleJet (k : Type) [Field k] {m : ℕ} (H : TorusTheory k m)
    (A : Type) [CommRing A] [Algebra k A] (X : Over (Spec (.of k)))
    (action : letI := H.group; ModObj (torusScheme k m) X)
    (f : Over.mk (Spec.algebraMap k A) ⟶ X) (etale : Etale f.left) (j : Fin m) :
    TorusInfinitesimalPoints.EtaleJet H A X action f j

def_wanted nativeUniversalMarkedSourceExtension (A : Type) [CommRing A] {n g : ℕ}
    (F : MarkedCurveStabilization.MarkedFamily (Spec (.of A)) n g)
    (C : LiMarkedCurveExtensions.Classification F) : LiUniversalSourceExtensions.Data F C

def_wanted nativeNormalizedLiLiftDifference {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    {C X Z : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
    (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))
    (a : LiAffineMapCharts.Chart p q f) (I : ModuleCat.{0} A)
    (E : LiLocalLiftDifferences.LocalExtension a I) (P : LiLocalLiftDifferences.Pair t a I E)
    (o : LiCechChartModules.Mode g J t a) (r : LiLocalLiftDifferences.Ratios g J t a I E P o) :
    {x : LiCechChartModules.value g J t I o // LiLocalLiftDifferences.Normalized g J t a I E P o r x}

def_wanted nativeFramedRubberModuli (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    (m : ℕ) {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) :
    FramedRubberModuliModels.Model O P D R S m (g := g) a

def_wanted nativeFramedRubberForget (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    (m : ℕ) {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0)
    (H : FramedRubberModuliModels.Model O P D R S m (g := g) a)
    (B : RubberModuliModel O P D R S (g := g) a) : FramedRubberModuliModels.Forget O P D R S m a H B

def_wanted nativeFramedRubberQuotientChart (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    (m : ℕ) (G : TorusTheory k (m + 1)) (A : RubberStandardScalingModels.StandardAction O P D R S m G)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0)
    (H : FramedRubberModuliModels.Model O P D R S m (g := g) a)
    (B : RubberModuliModel O P D R S (g := g) a) (F : FramedRubberModuliModels.Forget O P D R S m a H B) :
    FramedRubberQuotientCharts.Model O P D R S m G A a H B F

def_wanted nativeRubberPOTSourceRefinement (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (B : RubberModuliModel O P D R S (g := g) a)
    (U : Over (Spec (.of k))) [IsNoetherian U.left] [LocallyOfFiniteType U.hom] (y : B.stack.Fibre U) :
    RubberPOTSourceCharts.Refinement O P D R S a B U y

/-- The global source complex of Li's family deformation theory for rubber maps: let $k$ be an
algebraically closed field of characteristic zero, with the rubber target data `O`, `P`, `D`, `R`,
`S` over $k$, a genus $g$, a ramification profile $a \in \mathbb{Z}^n$ with $\sum_i a_i = 0$ and
$2g + n > 2$, and a rubber moduli model `B`. Then there is a descent datum
(`LiFamilySourceDescent.Descent`): a global cochain complex on the affine points of the moduli
stack, cofibrant at every point, with an étale surjective map from a chart point onto every
Noetherian affine point of finite type over $k$ (`SourceCover`), quasi-isomorphic base-change maps
along every map of affine points, quasi-isomorphisms from its evaluation at every chart point to
the local quotient complex, and homotopies relating these augmentations along every arrow after
refinement. -/
def_wanted nativeLiFamilySourceDescent (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (stableRange : 2 * g + n > 2)
    (B : RubberModuliModel O P D R S (g := g) a) :
    LiFamilySourceDescent.Descent (O := O) (P := P) (D := D) (R := R) (S := S) (a := a) (B := B)

/-- A strict cochain realization of the module diagram of a vector bundle stack: let $k$ be a field,
with the rubber target data `O`, `P`, `D`, `R`, `S` over $k$, a genus $g$, a ramification profile
$a \in \mathbb{Z}^n$, a rubber moduli model `B` and a vector bundle stack $E$ over its stack. Then
there is a `BundleRealization` of $E$: a global cochain complex of module presheaves on the affine
points of the stack, with a quasi-isomorphism from its value at every affine point $p$ to the cone
of the differential $E^0_p \to E^1_p$ of the module diagram of $E$ (both placed in degree $2$) and,
for every arrow $f : p \to q$, the map of cones induced by the restriction maps of the diagram
along $f$ and a homotopy between the two resulting maps from the value at $q$ to the restriction
along $f$ of the cone at $p$. These homotopies need not be compatible with identities and
composition. -/
def_wanted nativeRubberBundleSourceRealization (k : Type) [Field k]
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P D R S (g := g) a)
    (E : StackBundleCones.VectorBundleStack B.stack) :
    LiFamilySourceDescent.BundleRealization E

end WantedExt.AlgebraicGeometry.RubberSourceConstructionsWanted
