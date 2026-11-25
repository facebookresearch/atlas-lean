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

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.Compactification.StoneCech

/-!
# Bounded scalar functions and StoneCech

Restriction along the actual compactification unit is a unital star algebra
homomorphism. Bounded scalar functions extend through their actual compact
closed ball in ℂ, and density proves the two inverse laws.
No compactness of the whole scalar field or multiplier-equivalence oracle
is used. The domain may be any topological space, including an empty one.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BoundedContinuousFunction

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

Restrict a continuous function on StoneCech through the unit map. -/
noncomputable def stoneCechRestrictHom :
    C(StoneCech X, ℂ) →⋆ₐ[ℂ] (X →ᵇ ℂ) where
  toFun f := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    ⟨stoneCechUnit, continuous_stoneCechUnit⟩
  map_zero' := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_one' := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_mul' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  commutes' z := by
    apply BoundedContinuousFunction.ext
    intro x
    change (algebraMap ℂ C(StoneCech X, ℂ) z) (stoneCechUnit x) =
      (algebraMap ℂ (X →ᵇ ℂ) z) x
    simp only [_root_.algebraMap_apply, BoundedContinuousFunction.algebraMap_apply]
  map_star' f := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

Restriction has its compactification-unit value. -/
@[simp]
theorem stoneCechRestrictHom_apply (f : C(StoneCech X, ℂ)) (x : X) :
    stoneCechRestrictHom f x = f (stoneCechUnit x) := rfl

end ContinuousMap

namespace BoundedContinuousFunction

variable {X : Type u} [TopologicalSpace X]

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

Extend a bounded scalar function via its compact norm-bounded ball. -/
noncomputable def stoneCechExtension (g : X →ᵇ ℂ) : C(StoneCech X, ℂ) :=
  let gK : C(X, Metric.closedBall (0 : ℂ) ‖g‖) :=
    { toFun x := ⟨g x, mem_closedBall_zero_iff.2 (g.norm_coe_le_norm x)⟩
      continuous_toFun := g.continuous.subtype_mk
        (fun x => mem_closedBall_zero_iff.2 (g.norm_coe_le_norm x)) }
  let eK : StoneCech X → Metric.closedBall (0 : ℂ) ‖g‖ :=
    stoneCechExtend (g := (gK : X → Metric.closedBall (0 : ℂ) ‖g‖)) gK.continuous
  { toFun y := (eK y).val
    continuous_toFun := continuous_subtype_val.comp
      (continuous_stoneCechExtend
        (g := (gK : X → Metric.closedBall (0 : ℂ) ‖g‖)) gK.continuous) }

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

The compact-ball extension has exactly the given value on the unit image. -/
@[simp]
theorem stoneCechExtension_stoneCechUnit (g : X →ᵇ ℂ) (x : X) :
    stoneCechExtension g (stoneCechUnit x) = g x := by
  let gK : C(X, Metric.closedBall (0 : ℂ) ‖g‖) :=
    { toFun y := ⟨g y, mem_closedBall_zero_iff.2 (g.norm_coe_le_norm y)⟩
      continuous_toFun := g.continuous.subtype_mk
        (fun y => mem_closedBall_zero_iff.2 (g.norm_coe_le_norm y)) }
  change (stoneCechExtend
    (g := (gK : X → Metric.closedBall (0 : ℂ) ‖g‖))
      gK.continuous (stoneCechUnit x)).val = g x
  rw [stoneCechExtend_stoneCechUnit]
  rfl

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

Restriction recovers every bounded scalar function from its extension. -/
@[simp]
theorem stoneCechRestrict_extension (g : X →ᵇ ℂ) :
    ContinuousMap.stoneCechRestrictHom (stoneCechExtension g) = g := by
  apply BoundedContinuousFunction.ext
  intro x
  simp only [ContinuousMap.stoneCechRestrictHom_apply, stoneCechExtension_stoneCechUnit]

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

Density makes the extension of a restricted continuous scalar function unique. -/
@[simp]
theorem stoneCechExtension_restrict (f : C(StoneCech X, ℂ)) :
    stoneCechExtension (ContinuousMap.stoneCechRestrictHom f) = f := by
  have h :
      (stoneCechExtension (ContinuousMap.stoneCechRestrictHom f) : StoneCech X → ℂ) =
        (f : StoneCech X → ℂ) :=
    stoneCech_hom_ext
      (stoneCechExtension (ContinuousMap.stoneCechRestrictHom f)).continuous f.continuous
      (funext fun x =>
        (stoneCechExtension_stoneCechUnit (ContinuousMap.stoneCechRestrictHom f) x).trans
          (ContinuousMap.stoneCechRestrictHom_apply f x))
  exact ContinuousMap.ext fun y => congrFun h y

end BoundedContinuousFunction

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

restriction and compact-ball extension form a scalar star algebra equivalence. -/
noncomputable def stoneCechRestrictEquiv :
    C(StoneCech X, ℂ) ≃⋆ₐ[ℂ] (X →ᵇ ℂ) where
  toFun := stoneCechRestrictHom
  invFun := BoundedContinuousFunction.stoneCechExtension
  left_inv := BoundedContinuousFunction.stoneCechExtension_restrict
  right_inv := BoundedContinuousFunction.stoneCechRestrict_extension
  map_mul' := map_mul stoneCechRestrictHom
  map_add' := map_add stoneCechRestrictHom
  map_star' := map_star stoneCechRestrictHom
  map_smul' := map_smul stoneCechRestrictHom

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

The equivalence keeps the restriction map as its forward value. -/
@[simp]
theorem stoneCechRestrictEquiv_apply (f : C(StoneCech X, ℂ)) :
    stoneCechRestrictEquiv f = stoneCechRestrictHom f := rfl

/-- Let `X` be an arbitrary topological space. The scalar function spaces are the bounded continuous
complex functions on `X` and the continuous complex functions on its Stone–Čech
compactification.

The inverse equivalence keeps the compact-ball extension as its value. -/
@[simp]
theorem stoneCechRestrictEquiv_symm_apply (g : X →ᵇ ℂ) :
    stoneCechRestrictEquiv.symm g = BoundedContinuousFunction.stoneCechExtension g := rfl

end ContinuousMap
