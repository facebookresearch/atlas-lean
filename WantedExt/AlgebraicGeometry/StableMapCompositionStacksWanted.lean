/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableMapCompositionStacks
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import Batteries.Util.ProofWanted

/-!
# Actual stable-map composition and stabilization requests

Stabilization is requested only for admissible target projections. The
source stack and its Cartesian family normalization are chosen jointly;
arbitrary fibrewise equivalences do not prescribe base change.
References: Graber–Harris–Starr math/0109220v1, §2;
Knudsen, Stable curves II, §1; Stacks Project, Tag 0E7N.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.StableMapCompositionStacks

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

def_wanted actualStableMapStabilization (k : Type) [Field k] [CharZero k]
    (V Y T : Over (Spec (.of k))) (projectiveV : ProjectiveSpace.IsProjective V)
    (projectiveY : ProjectiveSpace.IsProjective Y) (h : V ⟶ Y) (n m g : ℕ)
    (a : Fin m → Fin n) (injective : Function.Injective a)
    (F : Family V.hom n g T.left T.hom)
    (stable : IsGeometricallyStable F) (admissible : IsStabilizable F h.left m) :
    Stabilization F h.left (Over.w h) a injective

def_wanted actualCompositionDomain (k : Type) [Field k] [CharZero k]
    (V Y : Over (Spec (.of k))) (projectiveV : ProjectiveSpace.IsProjective V)
    (projectiveY : ProjectiveSpace.IsProjective Y) (h : V ⟶ Y) (n m g : ℕ) :
    (D : CompositionDomain V.hom h.left n m g) × DomainBaseChange D

def_wanted actualStableMapStackComposition (k : Type) [Field k] [CharZero k]
    (V Y : Over (Spec (.of k))) (projectiveV : ProjectiveSpace.IsProjective V)
    (projectiveY : ProjectiveSpace.IsProjective Y) (h : V ⟶ Y) (n m g : ℕ)
    (a : Fin m → Fin n) (injective : Function.Injective a)
    (D : CompositionDomain V.hom h.left n m g) (B : DomainBaseChange D)
    (M : VaryingModel Y.hom m g) : CompositionModel D B M a injective (Over.w h)

def_wanted actualCompositionChartDifferential (k : Type) [CommRing k]
    {X Z : RelativeStack (Spec (.of k))}
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (a : X.SmoothAtlas) (b : Z.SmoothAtlas) (C : StackMapChart f a b) : ChartDifferential C

end MathlibExt.AlgebraicGeometry.StableMapCompositionStacks
