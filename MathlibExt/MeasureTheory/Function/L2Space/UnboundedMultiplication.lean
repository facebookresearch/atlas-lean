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

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.Ring

/-!
# Maximal-domain multiplication on L²

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. The partial complex linear operator M_m:D_m→H sends u to the
L² class of x↦m(x)u(x). The domain definition includes exactly those products that belong to
L²; m itself has no measurability or boundedness premise.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory.Lp

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable (μ : Measure X) (m : X → ℂ)

/-- **Maximal L² product domain.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. The submodule multiplicationDomain μ m is D_m.
-/
def multiplicationDomain : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {u | MemLp (fun x => m x * u x) 2 μ}
  zero_mem' := by
    have hzero : (fun x => m x * (0 : Lp ℂ 2 μ) x) =ᵐ[μ] fun _ => (0 : ℂ) := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx
      simp only [hx, Pi.zero_apply, mul_zero]
    exact (memLp_congr_ae hzero).2 MemLp.zero'
  add_mem' := by
    intro u v hu hv
    change MemLp (fun x => m x * u x) 2 μ at hu
    change MemLp (fun x => m x * v x) 2 μ at hv
    have hsum := hu.add hv
    refine (memLp_congr_ae (show (fun x => m x * (u + v) x) =ᵐ[μ]
      (fun x => m x * u x) + (fun x => m x * v x) from ?_)).2 hsum
    filter_upwards [Lp.coeFn_add u v] with x hx
    simp only [hx, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c u hu
    change MemLp (fun x => m x * u x) 2 μ at hu
    have hsmul := hu.const_smul c
    refine (memLp_congr_ae (show (fun x => m x * (c • u) x) =ᵐ[μ]
      c • (fun x => m x * u x) from ?_)).2 hsmul
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Membership criterion for the maximal multiplication domain.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. For u∈H, u∈multiplicationDomain μ m if and only if
MemLp(x↦m(x)u(x),2,μ), meaning that this product is a.e. strongly measurable with finite L²
seminorm.
-/
theorem mem_multiplicationDomain (u : Lp ℂ 2 μ) :
    u ∈ multiplicationDomain μ m ↔ MemLp (fun x => m x * u x) 2 μ := Iff.rfl

/-- **L² value of a maximal-domain product.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. For u∈D_m, multiplicationValue μ m u is the L² class of
x↦m(x)u(x).
-/
def multiplicationValue (u : multiplicationDomain μ m) : Lp ℂ 2 μ :=
  (u.property : MemLp (fun x => m x * (u : Lp ℂ 2 μ) x) 2 μ).toLp
    (fun x => m x * (u : Lp ℂ 2 μ) x)

/-- **Almost-everywhere value of a maximal-domain product.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. For u∈D_m, multiplicationValue μ m u equals x↦m(x)u(x)
μ-almost everywhere.
-/
theorem multiplicationValue_ae_eq (u : multiplicationDomain μ m) :
    multiplicationValue μ m u =ᵐ[μ] fun x => m x * (u : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp _

/-- **Linear multiplication map on the maximal domain.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. The complex linear map multiplicationLinearMap μ m:D_m→H sends
u to the L² class of m*u.
-/
def multiplicationLinearMap : multiplicationDomain μ m →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := multiplicationValue μ m
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [multiplicationValue_ae_eq μ m (u + v),
      Lp.coeFn_add (u : Lp ℂ 2 μ) (v : Lp ℂ 2 μ),
      Lp.coeFn_add (multiplicationValue μ m u) (multiplicationValue μ m v),
      multiplicationValue_ae_eq μ m u, multiplicationValue_ae_eq μ m v]
      with x huv hin hout hu hv
    rw [huv, hout]
    simp only [Submodule.coe_add]
    rw [hin]
    change m x * ((u : Lp ℂ 2 μ) x + (v : Lp ℂ 2 μ) x) =
      multiplicationValue μ m u x + multiplicationValue μ m v x
    rw [hu, hv]
    exact mul_add _ _ _
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [multiplicationValue_ae_eq μ m (c • u),
      Lp.coeFn_smul c (u : Lp ℂ 2 μ), Lp.coeFn_smul c (multiplicationValue μ m u),
      multiplicationValue_ae_eq μ m u] with x hcu hin hout hu
    change multiplicationValue μ m (c • u) x = (c • multiplicationValue μ m u) x
    rw [hcu, hout]
    simp only [Submodule.coe_smul]
    rw [hin]
    simp only [Pi.smul_apply]
    rw [hu]
    simp only [smul_eq_mul]
    ring

/-- **Partial multiplication operator with maximal product domain.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. The partial linear map multiplicationOperator μ m:H→ₗ.[ℂ]H has
domain D_m and value M_m u=[m*u] for u∈D_m.
-/
def multiplicationOperator : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  LinearPMap.mk (multiplicationDomain μ m) (multiplicationLinearMap μ m)

/-- **Domain of the partial L² multiplication operator.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. The equality (multiplicationOperator μ
m).domain=multiplicationDomain μ m states that its domain is exactly D_m.
-/
theorem multiplicationOperator_domain :
    (multiplicationOperator μ m).domain = multiplicationDomain μ m := rfl

/-- **Almost-everywhere action of the partial multiplication operator.**

Let X be a measurable space, μ any measure on X and m:X→ℂ an arbitrary function. On
H=L²(X,μ;ℂ) set D_m={u∈H:m*u is a.e. strongly measurable and square-integrable}, with
multiplication taken pointwise. For u in the domain of multiplicationOperator μ m, its value
equals x↦m(x)u(x) μ-almost everywhere.
-/
theorem multiplicationOperator_ae_eq (u : (multiplicationOperator μ m).domain) :
    multiplicationOperator μ m u =ᵐ[μ] fun x => m x * (u : Lp ℂ 2 μ) x :=
  multiplicationValue_ae_eq μ m u

end MeasureTheory.Lp

end
