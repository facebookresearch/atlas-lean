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
# Compactly supported coefficients for twisted convolution

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The space Carrier μ α consists of
compactly supported continuous coefficients f:G→A; C_c(G,A) denotes the same coefficient
function space. The carrier is complex-linearly equivalent to C_c(G,A). Addition and scalar
multiplication are pointwise: (f+h)(s)=f(s)+h(s) and (c•f)(s)=c•f(s). The parameters μ and α
identify the measure and action used for its twisted convolution.
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

/-- **Compactly supported coefficient carrier.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The space Carrier μ α consists of
compactly supported continuous coefficients f:G→A; C_c(G,A) denotes the same coefficient
function space. An element is specified by its compactly supported continuous coefficient
function.
-/
structure Carrier (μ : Measure G) (α : PointNormCStarAction G A) where
  /-- **Coefficient function of a core element.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For f:Carrier μ α, the field toCc
is its function in C_c(G,A), with the same values f(s) for s∈G.
-/
  toCc : C_c(G, A)

variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- **Underlying compactly supported coefficient.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The map toCc μ α:Carrier μ
α→C_c(G,A) sends each core element f to its compactly supported continuous coefficient
function s↦f(s).
-/
def toCc (f : Carrier μ α) : C_c(G, A) := f.toCc

/-- **Core element associated with a compact coefficient.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The map fromCc μ
α:C_c(G,A)→Carrier μ α sends a compactly supported continuous function f to the core element
with coefficient values f(s).
-/
def fromCc (f : C_c(G, A)) : Carrier μ α := ⟨f⟩

/-- **Recovering a compact coefficient from its core element.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For every f∈C_c(G,A), toCc μ α
(fromCc μ α f)=f.
-/
@[simp]
theorem toCc_fromCc (f : C_c(G, A)) : toCc μ α (fromCc μ α f) = f :=
  rfl

/-- **Recovering a core element from its coefficient.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For every f∈Carrier μ α, fromCc μ
α (toCc μ α f)=f.
-/
@[simp]
theorem fromCc_toCc (f : Carrier μ α) : fromCc μ α (toCc μ α f) = f := by
  cases f
  rfl

/-- **Equivalence with compactly supported continuous functions.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The equivalence equivCc μ
α:Carrier μ α≃C_c(G,A) sends a core element to its coefficient function, with inverse fromCc μ
α.
-/
def equivCc : Carrier μ α ≃ C_c(G, A) where
  toFun := toCc μ α
  invFun := fromCc μ α
  left_inv := fromCc_toCc μ α
  right_inv := toCc_fromCc μ α

/-- **Pointwise additive group of core coefficients.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Carrier μ α is an additive
commutative group under pointwise operations: (f+h)(s)=f(s)+h(s), (-f)(s)=-f(s), and 0(s)=0.
-/
instance instAddCommGroupCarrier : AddCommGroup (Carrier μ α) :=
  (equivCc μ α).addCommGroup

/-- **Complex vector space of core coefficients.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Carrier μ α is a complex vector
space with pointwise scalar multiplication (c•f)(s)=c•f(s).
-/
instance instModuleCarrier : Module ℂ (Carrier μ α) := by
  let e : Carrier μ α ≃+ C_c(G, A) := (equivCc μ α).addEquiv
  exact e.module ℂ

/-- **Evaluation of a core coefficient.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Each f∈Carrier μ α is evaluated as
the function G→A given by its compactly supported continuous coefficient toCc; evaluation at s
is f(s).
-/
instance instCoeFunCarrier : CoeFun (Carrier μ α) (fun _ => G → A) :=
  ⟨fun f => (toCc μ α f : G → A)⟩

/-- **Coefficient function of the zero core element.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The zero of Carrier μ α has zero
coefficient function: toCc μ α (0:Carrier μ α)=0 in C_c(G,A).
-/
@[simp]
theorem toCc_zero : toCc μ α (0 : Carrier μ α) = 0 :=
  rfl

/-- **Coefficient function of a sum.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For f,h∈Carrier μ α, toCc μ α
(f+h)=toCc μ α f+toCc μ α h, with pointwise addition in C_c(G,A).
-/
@[simp]
theorem toCc_add (f g : Carrier μ α) : toCc μ α (f + g) = toCc μ α f + toCc μ α g :=
  rfl

/-- **Coefficient function of a scalar multiple.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For c∈ℂ and f∈Carrier μ α, toCc μ
α (c•f)=c•toCc μ α f, with pointwise complex scaling in C_c(G,A).
-/
@[simp]
theorem toCc_smul (c : ℂ) (f : Carrier μ α) : toCc μ α (c • f) = c • toCc μ α f :=
  rfl

/-- **Equality determined by coefficient values.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. If f,h∈Carrier μ α satisfy
f(s)=h(s) for every s∈G, then f=h.
-/
@[ext]
theorem ext {f g : Carrier μ α} (h : ∀ s : G, f s = g s) : f = g := by
  apply (equivCc μ α).injective
  apply CompactlySupportedContinuousMap.ext
  intro s
  exact h s

end

end HaarTwistedCore
