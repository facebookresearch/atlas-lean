/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels

/-!
# The literal pointed K(p,q,A) source

The coefficient input is the actual Tate complex with its published
coefficient tensor. A functorial augmented K-injective resolution is
applied before the native good truncation and Dold--Kan realization.
This definition does not include motivic fibrancy or representability.

Source: Voevodsky, arXiv:math/0107109v1, Section 2; Mazza--Voevodsky--Weibel,
Lectures 3 and 14. The native Dold--Kan operations are Mathlib source
primitives, with source credits retained in the imported modules.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicEilenbergMacLaneModels

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
open MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels
open MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
open MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels
open MathlibExt.AlgebraicGeometry.PointedMotivicModels
open scoped Simplicial

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)

/-- Native coefficient change after the same functorial K-injective resolution. -/
def resolvedCoefficientFunctor (q : ℤ) := B.weightFunctor q ⋙ I.functor

/-- Actual K(p,q,A), retaining all integer degree/weight and abelian coefficients. -/
def K (p q : ℤ) (V : ModuleCat.{1} ℤ) : PointedSpaces (k := k) :=
  doldKanRealization Q (I.functor.obj ((B.weightFunctor q).obj V)) p

/-- The same realization on every actual coefficient morphism. -/
def KFunctor (p q : ℤ) : ModuleCat.{1} ℤ ⥤ PointedSpaces (k := k) :=
  resolvedCoefficientFunctor B I q ⋙
    shiftFunctor (CochainComplex (NisModules (k := k)) ℤ) p ⋙
    negativeEmbedding.truncLE'Functor (NisModules (k := k)) ⋙
    (Abelian.DoldKan.Γ : ChainComplex (NisModules (k := k)) ℕ ⥤
      SimplicialObject (NisModules (k := k))) ⋙ Q.functor

theorem KFunctor_obj (p q : ℤ) (V : ModuleCat.{1} ℤ) :
    (KFunctor B I Q p q).obj V = K B I Q p q V := rfl

def coefficientMap (p q : ℤ) {V W : ModuleCat.{1} ℤ} (f : V ⟶ W) :
    K B I Q p q V ⟶ K B I Q p q W := (KFunctor B I Q p q).map f

/-- The actual cochain augmentation into the resolution used by K(p,q,A). -/
def augmentation (q : ℤ) (V : ModuleCat.{1} ℤ) :
    (B.weightFunctor q).obj V ⟶ I.functor.obj ((B.weightFunctor q).obj V) :=
  I.augmentation.app ((B.weightFunctor q).obj V)

end MathlibExt.AlgebraicGeometry.MotivicEilenbergMacLaneModels
