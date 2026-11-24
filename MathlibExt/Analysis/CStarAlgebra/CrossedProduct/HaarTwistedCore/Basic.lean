/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# The original measure- and action-indexed Haar core carrier

The carrier is a one-field wrapper of the literal original C_c(G,A) function.
Both the given measure and coefficient action are indices, so different Haar
measures or actions have their own future twisted algebra structures. Exact
maps to and from C_c transport only the original additive and complex-module
data and function evaluation. Multiplication, star and norm are not inherited.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CompactlySupported

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- The actual original compact-support function, indexed by its measure and coefficient action. -/
structure Carrier (μ : Measure G) (α : PointNormCStarAction G A) where
  /-- The same literal source compactly supported continuous coefficient function. -/
  toCc : C_c(G, A)

variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- Read the original compact-support function without changing its values or topology. -/
def toCc (f : Carrier μ α) : C_c(G, A) := f.toCc

/-- Put the original compact-support function into its actual measure/action-indexed carrier. -/
def fromCc (f : C_c(G, A)) : Carrier μ α := ⟨f⟩

/-- The wrapper retains every original compact-support function exactly. -/
@[simp]
theorem toCc_fromCc (f : C_c(G, A)) : toCc μ α (fromCc μ α f) = f :=
  rfl

/-- The exact original function determines the same indexed wrapper. -/
@[simp]
theorem fromCc_toCc (f : Carrier μ α) : fromCc μ α (toCc μ α f) = f := by
  cases f
  rfl

/-- The measure/action-indexed carrier is exactly the original function type as a set of values. -/
def equivCc : Carrier μ α ≃ C_c(G, A) where
  toFun := toCc μ α
  invFun := fromCc μ α
  left_inv := fromCc_toCc μ α
  right_inv := toCc_fromCc μ α

/-- Only the original pointwise additive group is transported to the indexed core. -/
instance instAddCommGroupCarrier : AddCommGroup (Carrier μ α) :=
  (equivCc μ α).addCommGroup

/-- Only the original pointwise complex module is transported to the indexed core. -/
instance instModuleCarrier : Module ℂ (Carrier μ α) := by
  let e : Carrier μ α ≃+ C_c(G, A) := (equivCc μ α).addEquiv
  exact e.module ℂ

/-- Evaluation is the literal original compact-support coefficient value. -/
instance instCoeFunCarrier : CoeFun (Carrier μ α) (fun _ => G → A) :=
  ⟨fun f => (toCc μ α f : G → A)⟩

/-- The indexed additive zero is the same original zero coefficient function. -/
@[simp]
theorem toCc_zero : toCc μ α (0 : Carrier μ α) = 0 :=
  rfl

/-- Indexed addition retains the original pointwise additive coefficient function. -/
@[simp]
theorem toCc_add (f g : Carrier μ α) : toCc μ α (f + g) = toCc μ α f + toCc μ α g :=
  rfl

/-- Indexed complex scaling retains the original scalar coefficient function. -/
@[simp]
theorem toCc_smul (c : ℂ) (f : Carrier μ α) : toCc μ α (c • f) = c • toCc μ α f :=
  rfl

/-- The indexed core functions agree precisely when all original coefficient values agree. -/
@[ext]
theorem ext {f g : Carrier μ α} (h : ∀ s : G, f s = g s) : f = g := by
  apply (equivCc μ α).injective
  apply CompactlySupportedContinuousMap.ext
  intro s
  exact h s

end

end HaarTwistedCore
