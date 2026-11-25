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
# Right submodules of C-star modules

For a right C-star module `E` over a nonunital C-star algebra `B`, a `RightSubmodule B E` is a
complex submodule stable under `x ↦ x <• b` for every `b : B`. Its subtype has the restricted
right action and coefficient-valued inner product, and norm `‖x‖ = ‖(x : E)‖`.

Every such submodule is a right pre-Hilbert module. A submodule closed in a complete ambient
module is complete; its inclusion is a complex-linear isometry.
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

/-- **Right submodule of a C-star module.** Let `E` be a right C-star module over a nonunital
C-star algebra `B`. A complex submodule `S` of `E` with `x <• b ∈ S` whenever `x ∈ S` and `b :
B`. Its norm and inner product are restricted from `E`; closedness is a separate property. -/
structure RightSubmodule (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    extends Submodule ℂ E where
  /-- **Closure under right coefficients.** Let `E` be a right C-star module over a nonunital
  C-star algebra `B`. If `x` belongs to the carrier, then `x <• b` belongs to it for every
  coefficient `b : B`. -/
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

/-- **Underlying complex submodule.** Let `E` be a right C-star module over a nonunital C-star
algebra `B`. `S.toComplexSubmodule` has the same vectors as `S` and retains its closure under
complex addition and scalar multiplication. -/
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

/-- **Right coefficient action on a submodule.** Let `E` be a right C-star module over a nonunital
C-star algebra `B`. Restrict the coefficient action of `E` to `S`; closure under `x <• b`
makes this action well-defined. -/
instance : SMul Bᵐᵒᵖ S where
  smul b x := ⟨(b : Bᵐᵒᵖ) • (x : E), S.right_smul_mem' x.property b.unop⟩

@[simp]
theorem coe_right_smul (x : S) (b : B) :
    ((x <• b : S) : E) = (x : E) <• b :=
  rfl

/-- **C-star module structure on a right submodule.** Let `E` be a right C-star module over a
nonunital C-star algebra `B`. The subtype has the restricted coefficient inner product `inner
x y = inner (x : E) (y : E)` and norm `‖x‖ = ‖(x : E)‖`. -/
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

/-- **Closed right submodule.** Let `E` be a right C-star module over a nonunital C-star algebra
`B`. `S.IsClosed` means that its carrier `(S : Set E)` is closed in the topology of `E`. -/
def IsClosed : Prop :=
  _root_.IsClosed (S : Set E)

/-- **Completeness of a closed right submodule.** Let `E` be a right C-star module over a
nonunital C-star algebra `B`. If `E` is complete and `S.IsClosed`, then the subtype `S` is
complete for its restricted norm and uniformity. -/
theorem completeSpace [CompleteSpace E] (hS : S.IsClosed) : CompleteSpace S :=
  IsComplete.completeSpace_coe hS.isComplete

/-- **Isometric inclusion of a right submodule.** Let `E` be a right C-star module over a
nonunital C-star algebra `B`. `S.subtypeLIE : S →ₗᵢ[ℂ] E` sends a subtype vector to its
ambient vector and preserves its norm. -/
def subtypeLIE : S →ₗᵢ[ℂ] E :=
  S.toSubmodule.subtypeₗᵢ

@[simp]
theorem subtypeLIE_apply (x : S) : S.subtypeLIE x = x :=
  rfl

/-- **Whole right module.** Let `E` be a right C-star module over a nonunital C-star algebra `B`.
`RightSubmodule.top` consists of all vectors of `E`, with its complex and right coefficient
actions. -/
def top : RightSubmodule B E where
  toSubmodule := ⊤
  right_smul_mem' := by
    intro x _ b
    exact Submodule.mem_top

@[simp]
theorem mem_top (x : E) : x ∈ (top : RightSubmodule B E) :=
  trivial

/-- **Zero right submodule.** Let `E` be a right C-star module over a nonunital C-star algebra
`B`. `RightSubmodule.bot` is the submodule consisting of the zero vector. -/
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
