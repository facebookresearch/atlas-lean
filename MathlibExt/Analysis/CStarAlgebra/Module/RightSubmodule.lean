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

public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Right submodules of right C-star modules

This file packages a complex submodule of a right C-star module which is
stable under the right coefficient action.  Its subtype inherits the exact
coefficient-valued inner product and norm.  A closed right submodule of a
complete module is complete.

The construction is deliberately independent of orthogonal complementability:
closed Hilbert-module submodules need not be ranges of adjointable projections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule

universe uB uE

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- A complex submodule stable under the right coefficient action of `B`.

No closedness or complementability is stored.  Thus its subtype is always a
right pre-Hilbert module, and it becomes a Hilbert module when its carrier is
closed in a complete ambient module. -/
structure RightSubmodule (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    extends Submodule ℂ E where
  /-- The carrier is stable under Blackadar's right coefficient action. -/
  right_smul_mem' : ∀ {x : E}, x ∈ carrier → ∀ b : B, x <• b ∈ carrier

namespace RightSubmodule

variable (S : RightSubmodule B E)

instance : SetLike (RightSubmodule B E) E where
  coe S := S.carrier
  coe_injective S T h := by
    cases S
    cases T
    congr
    exact SetLike.coe_injective h

@[simp, nolint simpNF]
theorem mem_carrier {x : E} : x ∈ S.carrier ↔ x ∈ S :=
  Iff.rfl

/-- The underlying complex submodule. -/
def toComplexSubmodule : Submodule ℂ E :=
  S.toSubmodule

instance : AddCommGroup S :=
  inferInstanceAs (AddCommGroup S.toSubmodule)

instance : Module ℂ S :=
  inferInstanceAs (Module ℂ S.toSubmodule)

instance : NormedAddCommGroup S :=
  inferInstanceAs (NormedAddCommGroup S.toSubmodule)

instance : NormedSpace ℂ S :=
  inferInstanceAs (NormedSpace ℂ S.toSubmodule)

/-- Right coefficients act on a right submodule by restriction. -/
instance : SMul Bᵐᵒᵖ S where
  smul b x := ⟨(b : Bᵐᵒᵖ) • (x : E), S.right_smul_mem' x.property b.unop⟩

@[simp]
theorem coe_right_smul (x : S) (b : B) :
    ((x <• b : S) : E) = (x : E) <• b :=
  rfl

/-- The restricted coefficient-valued inner product makes every right
submodule a right pre-Hilbert C-star module. -/
instance : CStarModule Bᵐᵒᵖ S where
  inner x y := inner Bᵐᵒᵖ (x : E) (y : E)
  inner_add_right := by
    intro x y z
    exact CStarModule.inner_add_right
  inner_self_nonneg := by
    intro x
    exact CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      exact (CStarModule.inner_self (A := Bᵐᵒᵖ) (x := (x : E))).mp hx
    · rintro rfl
      exact (CStarModule.inner_self (A := Bᵐᵒᵖ) (x := (0 : E))).mpr rfl
  inner_op_smul_right := by
    intro b x y
    exact CStarModule.inner_op_smul_right
  inner_smul_right_complex := by
    intro c x y
    exact CStarModule.inner_smul_right_complex
  star_inner := by
    intro x y
    exact CStarModule.star_inner (A := Bᵐᵒᵖ) (x : E) (y : E)
  norm_eq_sqrt_norm_inner_self := by
    intro x
    exact CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x : E)

@[simp]
theorem inner_coe (x y : S) :
    inner Bᵐᵒᵖ x y = inner Bᵐᵒᵖ (x : E) (y : E) :=
  by
    change inner Bᵐᵒᵖ (x : E) (y : E) = _
    rfl

@[simp]
theorem rightInner_coe (x y : S) :
    rightInner (B := B) x y = rightInner (B := B) (x : E) (y : E) :=
  by
    change MulOpposite.unop (inner Bᵐᵒᵖ (x : E) (y : E)) = _
    rfl

/-- Closedness of a right submodule, stated on its literal ambient carrier. -/
def IsClosed : Prop :=
  _root_.IsClosed (S : Set E)

/-- A closed right submodule of a complete module is complete.  The result is
plain locally activatable data, so different closed carriers do not introduce
competing global instances on the ambient type. -/
theorem completeSpace [CompleteSpace E] (hS : S.IsClosed) : CompleteSpace S :=
  IsComplete.completeSpace_coe hS.isComplete

/-- The subtype inclusion of a right submodule as a complex-linear isometry. -/
def subtypeLIE : S →ₗᵢ[ℂ] E :=
  S.toSubmodule.subtypeₗᵢ

@[simp]
theorem subtypeLIE_apply (x : S) : S.subtypeLIE x = x :=
  rfl

/-- The full ambient module, viewed as a right submodule. -/
def top : RightSubmodule B E where
  toSubmodule := ⊤
  right_smul_mem' := by
    intro x _ b
    exact Submodule.mem_top

@[simp]
theorem mem_top (x : E) : x ∈ (top : RightSubmodule B E) :=
  trivial

/-- The zero right submodule. -/
def bot : RightSubmodule B E where
  toSubmodule := ⊥
  right_smul_mem' := by
    intro x hx b
    change x ∈ (⊥ : Submodule ℂ E) at hx
    change x <• b ∈ (⊥ : Submodule ℂ E)
    rw [Submodule.mem_bot] at hx ⊢
    simp [hx]

@[simp]
theorem mem_bot {x : E} :
    x ∈ (RightSubmodule.bot (B := B) (E := E)) ↔ x = 0 := by
  constructor
  · intro hx
    change x ∈ (⊥ : Submodule ℂ E) at hx
    exact (Submodule.mem_bot ℂ).mp hx
  · rintro rfl
    exact Submodule.zero_mem _

end RightSubmodule

end CStarModule
