/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import MathlibExt.Condensed.SolidWeakPerfectModels
public import MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds

/-!
# Actual overconvergent local Fp scalars

On a strictly totally disconnected perfectoid chart the source category
is the actual derived category of locally constant Fp-valued functions.
The scalar map into A^+/pi is fixed on every characteristic function by
the actual plus-ring idempotent and its all-rank valuation support.
Frobenius fixes this whole actual scalar ring.

Source: Mann, arXiv:2206.02022v1, Definitions 3.9.17--3.9.21,
Lemma 3.9.18(iii); Scholze, arXiv:1709.07343v4, Definition 7.15.
Global overconvergence and scalar-extension comparison are separate
construction requests; no constant discrete ring replaces geometric coefficients.
-/

@[expose] public noncomputable section

namespace MathlibExt.Condensed.SolidFpScalarModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarNerveMaps
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
open MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels SolidWeakPerfectModels

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)

local instance : TopologicalSpace (ZMod p) := ⊥
local instance : DiscreteTopology (ZMod p) := ⟨rfl⟩
local instance : IsTopologicalRing (ZMod p) := inferInstance

/-- The actual locally constant finite-field function ring on the original adic chart. -/
abbrev FpFunctions := ULift.{1} C(P.pair.toHuberPair.Space, ZMod p)

/-- The function ring carries its actual pointwise commutative-ring structure. -/
instance fpFunctionsCommRing : CommRing (FpFunctions p P) := inferInstance

/-- Strict total disconnectedness retains actual splittings of every etale cover. -/
def IsStrictlyTotallyDisconnected : Prop :=
  IsTotallyDisconnected p P.tilt.pair ∧
    ∀ (I : Type 1) (U : I → Affine p) (f : ∀ i, U i ⟶ P.tilt.pair),
      (∀ i, MathlibExt.AlgebraicGeometry.PerfectoidLocalModels.IsEtale p (f i)) →
      IsVCover p P.tilt.pair U f →
      ∃ s : affineSheaf p P.tilt.pair ⟶ ∐ (fun i ↦ affineSheaf p (U i)),
        s ≫ Sigma.desc (fun i ↦ affineMap p (f i)) = 𝟙 _

/-- The actual one-object ordinary local Fp coefficient category. -/
def fpCoefficientCategory := discreteCoefficientCategory (FpFunctions p P)

/-- Its full derived module nerve is the source on the qualified disconnected chart. -/
def fpDerivedNerve : SSet.{2} :=
  integerNerve (R := FpFunctions p P) (DGDerivedModules (FpFunctions p P)
    (fpCoefficientCategory p P))

variable (π : Pseudouniformizer p P)

/-- The coefficient map is fixed by every actual clopen plus-ring idempotent. -/
structure FpScalarModel where
  map : FpFunctions p P →+* TorsionRing p P π
  idempotents : ∀ f : C(P.pair.toHuberPair.Space, ZMod p),
    (∀ x, f x = 0 ∨ f x = 1) →
    ∃ e : P.pair.plus, e * e = e ∧
      (∀ x : P.pair.toHuberPair.Space, ¬ x.1.relation.vle (e : P.pair.ring) 0 ↔ f x = 1) ∧
      map (ULift.up f) = reduction p P π (ULift.up e)

/-- Frobenius fixes the actual finite-field scalars in every geometric section. -/
theorem frobenius_scalar_fixed (h : π.element ∣ (p : P.pair.plus))
    (S : FpScalarModel p P π) : (coefficientFrobenius p P π h).comp S.map = S.map := by
  ext f
  have hf : f ^ p = f := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact ZMod.pow_card (f.down x)
  rw [RingHom.comp_apply, coefficientFrobenius_apply, ← map_pow]
  rw [hf]

end MathlibExt.Condensed.SolidFpScalarModels
