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

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInfty.BoundedMultiplication
public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.PointCutoff
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Recover bounded scalar functions from actual C0 multipliers

Centrality and point cutoffs determine the scalar function of a C0 double
centralizer. Its continuity uses one fixed local cutoff at a time, not
continuity of the chosen cutoff family. All norms and actions are the
existing ones, without a multiplier-equivalence or Source existence oracle.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ZeroAtInfty MultiplierAlgebra Topology BoundedContinuousFunction

namespace DoubleCentralizer

universe u

variable {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

The scalar value extracted using the unit-norm-bounded point cutoff. -/
noncomputable def scalarFunction (T : 𝓜(ℂ, C₀(X, ℂ))) (x : X) : ℂ :=
  T.fst (ZeroAtInftyContinuousMap.pointCutoff x) x

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

Centrality determines the right action from the extracted scalar value. -/
theorem snd_apply_scalarFunction
    (T : 𝓜(ℂ, C₀(X, ℂ))) (f : C₀(X, ℂ)) (x : X) :
    T.snd f x = f x * scalarFunction T x := by
  have h := congrArg (fun a : C₀(X, ℂ) => a x)
    (T.central f (ZeroAtInftyContinuousMap.pointCutoff x))
  simpa only [ZeroAtInftyContinuousMap.mul_apply,
    ZeroAtInftyContinuousMap.pointCutoff_apply, mul_one, scalarFunction] using h

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

Centrality determines the left action on every C0 function. -/
theorem fst_apply_scalarFunction
    (T : 𝓜(ℂ, C₀(X, ℂ))) (f : C₀(X, ℂ)) (x : X) :
    T.fst f x = scalarFunction T x * f x := by
  have h := congrArg (fun a : C₀(X, ℂ) => a x)
    (T.central (ZeroAtInftyContinuousMap.pointCutoff x) f)
  simp only [ZeroAtInftyContinuousMap.mul_apply,
    ZeroAtInftyContinuousMap.pointCutoff_apply, one_mul] at h
  rw [snd_apply_scalarFunction T (ZeroAtInftyContinuousMap.pointCutoff x) x,
    ZeroAtInftyContinuousMap.pointCutoff_apply, one_mul] at h
  exact h.symm

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

Every extracted value is bounded by the existing double-centralizer norm. -/
theorem norm_scalarFunction_le (T : 𝓜(ℂ, C₀(X, ℂ))) (x : X) :
    ‖scalarFunction T x‖ ≤ ‖T‖ := by
  change ‖T.fst (ZeroAtInftyContinuousMap.pointCutoff x) x‖ ≤ ‖T‖
  calc
    ‖T.fst (ZeroAtInftyContinuousMap.pointCutoff x) x‖ ≤
        ‖(T.fst (ZeroAtInftyContinuousMap.pointCutoff x)).toBCF‖ :=
      (T.fst (ZeroAtInftyContinuousMap.pointCutoff x)).toBCF.norm_coe_le_norm x
    _ = ‖T.fst (ZeroAtInftyContinuousMap.pointCutoff x)‖ :=
      ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
    _ ≤ ‖T.fst‖ :=
      T.fst.unit_le_opNorm (ZeroAtInftyContinuousMap.pointCutoff x)
        (ZeroAtInftyContinuousMap.norm_pointCutoff_le x)
    _ = ‖T‖ := DoubleCentralizer.norm_fst T

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

A fixed nonvanishing local cutoff proves continuity of the extracted function. -/
theorem continuous_scalarFunction (T : 𝓜(ℂ, C₀(X, ℂ))) :
    Continuous (scalarFunction T) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let φ : C₀(X, ℂ) := ZeroAtInftyContinuousMap.pointCutoff x
  have hx : φ x ≠ 0 := by
    change ZeroAtInftyContinuousMap.pointCutoff x x ≠ 0
    rw [ZeroAtInftyContinuousMap.pointCutoff_apply]
    exact one_ne_zero
  have hquot : ContinuousAt (fun y => T.fst φ y / φ y) x :=
    (T.fst φ).continuous_toFun.continuousAt.div φ.continuous_toFun.continuousAt hx
  have hne : ∀ᶠ y in 𝓝 x, φ y ≠ 0 := φ.continuous_toFun.continuousAt.eventually_ne hx
  have heq : scalarFunction T =ᶠ[𝓝 x] (fun y => T.fst φ y / φ y) :=
    hne.mono fun y hy =>
      (eq_div_iff hy).2 (fst_apply_scalarFunction T φ y).symm
  exact hquot.congr_of_eventuallyEq heq

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

Bundle the recovered function using its proved uniform norm bound. -/
noncomputable def toBoundedContinuousFunction (T : 𝓜(ℂ, C₀(X, ℂ))) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (scalarFunction T) (continuous_scalarFunction T) ‖T‖ (norm_scalarFunction_le T)

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

The bundled value is literally the cutoff evaluation, without a new model. -/
@[simp]
theorem toBoundedContinuousFunction_apply (T : 𝓜(ℂ, C₀(X, ℂ))) (x : X) :
    toBoundedContinuousFunction T x =
      T.fst (ZeroAtInftyContinuousMap.pointCutoff x) x := rfl

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

The existing BCF norm of the recovered function is bounded by the multiplier norm. -/
theorem norm_toBoundedContinuousFunction_le (T : 𝓜(ℂ, C₀(X, ℂ))) :
    ‖toBoundedContinuousFunction T‖ ≤ ‖T‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (continuous_scalarFunction T) (norm_nonneg T) (norm_scalarFunction_le T)

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

The recovered bounded function gives the left multiplier action. -/
theorem fst_apply_toBoundedContinuousFunction
    (T : 𝓜(ℂ, C₀(X, ℂ))) (f : C₀(X, ℂ)) (x : X) :
    T.fst f x = toBoundedContinuousFunction T x * f x :=
  fst_apply_scalarFunction T f x

/-- Let `X` be a regular locally compact topological space. The coefficient algebra is `C₀(X,ℂ)`
with its supremum norm, and its multipliers are bounded complex-linear double centralizers.

The recovered bounded function gives the right multiplier action. -/
theorem snd_apply_toBoundedContinuousFunction
    (T : 𝓜(ℂ, C₀(X, ℂ))) (f : C₀(X, ℂ)) (x : X) :
    T.snd f x = f x * toBoundedContinuousFunction T x :=
  snd_apply_scalarFunction T f x


end DoubleCentralizer
