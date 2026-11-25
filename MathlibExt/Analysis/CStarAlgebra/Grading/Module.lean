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

public import MathlibExt.Analysis.CStarAlgebra.Grading.Constructions
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

import Mathlib.Tactic.Module

/-!
# Gradings of right C-star modules

A module grading is stored as one explicit involutive continuous linear
equivalence, compatible with the coefficient grading, right action, and
coefficient-valued inner product. No ambient `ZMod 2` action and no second
Hilbert-module class is installed.
-/

@[expose] public section

noncomputable section

open Set
open scoped RightActions

universe uB uE uF uG

/-- **Grading of a complete right Hilbert module.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. These covariance identities define
compatibility with the coefficient grading. -/
structure CStarModuleGrading
    {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    (γ : CStarGrading B) (E : Type uE)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] where
  /-- The degree-one module automorphism. -/
  generator : E ≃L[ℂ] E
  /-- The generator has order two. -/
  generator_involutive : Function.Involutive generator
  /-- The generator intertwines the right action with the coefficient
  grading. -/
  generator_right_smul : ∀ (x : E) (b : B),
    generator (x <• b) = generator x <• γ.generatorAut b
  /-- The generator is covariant for the coefficient-valued inner product. -/
  generator_rightInner : ∀ x y : E,
    CStarModule.rightInner (B := B) (generator x) (generator y) =
      γ.generatorAut (CStarModule.rightInner (B := B) x y)

namespace CStarModuleGrading

variable {B : Type uB} {E : Type uE}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {γ : CStarGrading B}

@[ext]
theorem ext {δ₁ δ₂ : CStarModuleGrading γ E}
    (h : δ₁.generator = δ₂.generator) : δ₁ = δ₂ := by
  cases δ₁
  cases δ₂
  cases h
  rfl

private theorem zmod_two_eq_zero_or_one (n : ZMod 2) : n = 0 ∨ n = 1 := by
  fin_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Bounded linear module-grading generator.** Let `B` be a graded nonunital complex C*-algebra with
an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The module generator `G` is a
continuous complex-linear endomorphism of `E`. -/
def generatorCLM (δ : CStarModuleGrading γ E) : E →L[ℂ] E :=
  δ.generator.toContinuousLinearMap

@[simp]
theorem generatorCLM_apply (δ : CStarModuleGrading γ E) (x : E) :
    δ.generatorCLM x = δ.generator x :=
  rfl

/-- **Even part of a Hilbert-module grading.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The even part is the complex-linear subspace `{x
∈ E : Gx = x}`. -/
def evenPart (δ : CStarModuleGrading γ E) : Submodule ℂ E :=
  LinearMap.ker (δ.generatorCLM.toLinearMap - LinearMap.id)

/-- **Odd part of a Hilbert-module grading.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The odd part is the complex-linear subspace `{x ∈
E : Gx = -x}`. -/
def oddPart (δ : CStarModuleGrading γ E) : Submodule ℂ E :=
  LinearMap.ker (δ.generatorCLM.toLinearMap + LinearMap.id)

/-- **Degree-indexed Hilbert-module parts.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The part of degree zero is the positive
eigenspace of `G`; the part of degree one is its negative eigenspace. -/
def part (δ : CStarModuleGrading γ E) : ZMod 2 → Submodule ℂ E :=
  fun n ↦ if n = 0 then δ.evenPart else δ.oddPart

@[simp]
theorem part_zero (δ : CStarModuleGrading γ E) :
    δ.part 0 = δ.evenPart := by
  simp [part]

@[simp]
theorem part_one (δ : CStarModuleGrading γ E) :
    δ.part 1 = δ.oddPart := by
  simp [part]

theorem mem_evenPart_iff_generator (δ : CStarModuleGrading γ E) (x : E) :
    x ∈ δ.evenPart ↔ δ.generator x = x := by
  change δ.generator x - x = 0 ↔ δ.generator x = x
  exact sub_eq_zero

theorem mem_oddPart_iff_generator (δ : CStarModuleGrading γ E) (x : E) :
    x ∈ δ.oddPart ↔ δ.generator x = -x := by
  change δ.generator x + x = 0 ↔ δ.generator x = -x
  exact add_eq_zero_iff_eq_neg

theorem mem_part_iff_generator (δ : CStarModuleGrading γ E)
    (n : ZMod 2) (x : E) :
    x ∈ δ.part n ↔
      δ.generator x = CStarGrading.degreeSign n • x := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · simpa using δ.mem_evenPart_iff_generator x
  · rw [part_one, mem_oddPart_iff_generator,
      CStarGrading.degreeSign_one, neg_one_smul]

theorem isClosed_evenPart (δ : CStarModuleGrading γ E) :
    IsClosed (δ.evenPart : Set E) := by
  exact ContinuousLinearMap.isClosed_ker
    (δ.generatorCLM - ContinuousLinearMap.id ℂ E)

theorem isClosed_oddPart (δ : CStarModuleGrading γ E) :
    IsClosed (δ.oddPart : Set E) := by
  exact ContinuousLinearMap.isClosed_ker
    (δ.generatorCLM + ContinuousLinearMap.id ℂ E)

theorem isClosed_part (δ : CStarModuleGrading γ E) (n : ZMod 2) :
    IsClosed (δ.part n : Set E) := by
  rcases zmod_two_eq_zero_or_one n with rfl | rfl
  · exact δ.isClosed_evenPart
  · exact δ.isClosed_oddPart

/-! ## Projections and decomposition -/

/-- **Even projection of a Hilbert-module grading.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The continuous complex-linear even
projection is `x ↦ (x+Gx)/2`. -/
def evenProjection (δ : CStarModuleGrading γ E) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ E + δ.generatorCLM)

/-- **Odd projection of a Hilbert-module grading.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The continuous complex-linear odd
projection is `x ↦ (x-Gx)/2`. -/
def oddProjection (δ : CStarModuleGrading γ E) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ E - δ.generatorCLM)

@[simp]
theorem evenProjection_apply (δ : CStarModuleGrading γ E) (x : E) :
    δ.evenProjection x = (2 : ℂ)⁻¹ • (x + δ.generator x) := by
  rfl

@[simp]
theorem oddProjection_apply (δ : CStarModuleGrading γ E) (x : E) :
    δ.oddProjection x = (2 : ℂ)⁻¹ • (x - δ.generator x) := by
  rfl

theorem generator_evenProjection (δ : CStarModuleGrading γ E) (x : E) :
    δ.generator (δ.evenProjection x) = δ.evenProjection x := by
  rw [evenProjection_apply, map_smul, map_add,
    δ.generator_involutive]
  congr 1
  abel

theorem generator_oddProjection (δ : CStarModuleGrading γ E) (x : E) :
    δ.generator (δ.oddProjection x) = -δ.oddProjection x := by
  rw [oddProjection_apply, map_smul, map_sub,
    δ.generator_involutive]
  module

theorem evenProjection_mem (δ : CStarModuleGrading γ E) (x : E) :
    δ.evenProjection x ∈ δ.evenPart :=
  (δ.mem_evenPart_iff_generator _).2 (δ.generator_evenProjection x)

theorem oddProjection_mem (δ : CStarModuleGrading γ E) (x : E) :
    δ.oddProjection x ∈ δ.oddPart :=
  (δ.mem_oddPart_iff_generator _).2 (δ.generator_oddProjection x)

theorem evenProjection_add_oddProjection
    (δ : CStarModuleGrading γ E) (x : E) :
    δ.evenProjection x + δ.oddProjection x = x := by
  rw [evenProjection_apply, oddProjection_apply]
  module

theorem evenProjection_eq_self_of_mem
    (δ : CStarModuleGrading γ E) {x : E} (hx : x ∈ δ.evenPart) :
    δ.evenProjection x = x := by
  rw [evenProjection_apply, (δ.mem_evenPart_iff_generator x).1 hx]
  module

theorem oddProjection_eq_self_of_mem
    (δ : CStarModuleGrading γ E) {x : E} (hx : x ∈ δ.oddPart) :
    δ.oddProjection x = x := by
  rw [oddProjection_apply, (δ.mem_oddPart_iff_generator x).1 hx]
  module

theorem evenProjection_eq_zero_of_mem_odd
    (δ : CStarModuleGrading γ E) {x : E} (hx : x ∈ δ.oddPart) :
    δ.evenProjection x = 0 := by
  rw [evenProjection_apply, (δ.mem_oddPart_iff_generator x).1 hx]
  module

theorem oddProjection_eq_zero_of_mem_even
    (δ : CStarModuleGrading γ E) {x : E} (hx : x ∈ δ.evenPart) :
    δ.oddProjection x = 0 := by
  rw [oddProjection_apply, (δ.mem_evenPart_iff_generator x).1 hx]
  module

/-- **Even-odd topological decomposition of a Hilbert module.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The even and odd
projections give a continuous complex-linear equivalence from `E` to the product of its even and odd
parts, with inverse addition. -/
def decomposition (δ : CStarModuleGrading γ E) :
    E ≃L[ℂ] δ.evenPart × δ.oddPart := by
  let forward : E →L[ℂ] δ.evenPart × δ.oddPart :=
    (δ.evenProjection.codRestrict δ.evenPart δ.evenProjection_mem).prod
      (δ.oddProjection.codRestrict δ.oddPart δ.oddProjection_mem)
  let inverse : δ.evenPart × δ.oddPart →L[ℂ] E :=
    δ.evenPart.subtypeL.coprod δ.oddPart.subtypeL
  exact ContinuousLinearEquiv.equivOfInverse forward inverse
    δ.evenProjection_add_oddProjection
    (fun p ↦ by
      apply Prod.ext
      · apply Subtype.ext
        change δ.evenProjection ((p.1 : E) + (p.2 : E)) = p.1
        rw [map_add, δ.evenProjection_eq_self_of_mem p.1.property,
          δ.evenProjection_eq_zero_of_mem_odd p.2.property, add_zero]
      · apply Subtype.ext
        change δ.oddProjection ((p.1 : E) + (p.2 : E)) = p.2
        rw [map_add, δ.oddProjection_eq_zero_of_mem_even p.1.property,
          δ.oddProjection_eq_self_of_mem p.2.property, zero_add])

/-! ## Isometry and homogeneous laws -/

/-- **Norm of the module-grading generator.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. For every `x ∈ E`, `‖Gx‖ = ‖x‖`. -/
@[simp]
theorem norm_generator
    (δ : CStarModuleGrading γ E) (x : E) :
    ‖δ.generator x‖ = ‖x‖ := by
  calc
    ‖δ.generator x‖ =
        √‖CStarModule.rightInner (B := B)
          (δ.generator x) (δ.generator x)‖ :=
      CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = √‖γ.generatorAut
        (CStarModule.rightInner (B := B) x x)‖ := by
      rw [δ.generator_rightInner]
    _ = √‖CStarModule.rightInner (B := B) x x‖ := by
      rw [StarAlgEquiv.norm_map]
    _ = ‖x‖ :=
      (CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner x).symm

/-- **Module-grading generator is an isometry.** Let `B` be a graded nonunital complex C*-algebra with
an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The involution `G : E → E` preserves
distances. -/
theorem isometry_generator
    (δ : CStarModuleGrading γ E) : Isometry δ.generator := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, δ.norm_generator]

/-- **Degree of a homogeneous right product.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. For `x` of module degree `m` and `b` of
coefficient degree `n`, the vector `x b` has degree `m+n`. -/
theorem right_smul_mem_part (δ : CStarModuleGrading γ E)
    {m n : ZMod 2} {x : E} {b : B}
    (hx : x ∈ δ.part m) (hb : b ∈ γ.part n) :
    x <• b ∈ δ.part (m + n) := by
  rw [δ.mem_part_iff_generator] at hx ⊢
  rw [γ.mem_part_iff_generator] at hb
  rw [δ.generator_right_smul, hx, hb]
  simp only [CStarModule.right_smul_smul,
    CStarModule.smul_right_smul, smul_smul]
  rw [mul_comm, ← CStarGrading.degreeSign_add]
  rw [add_comm n m]

/-- **Degree of a Hilbert-module inner product.** Let `B` be a graded nonunital complex C*-algebra with
an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. For module vectors `x,y` of degrees
`m,n`, the coefficient-valued inner product `⟨x,y⟩_B` has degree `m+n`. -/
theorem rightInner_mem_part (δ : CStarModuleGrading γ E)
    {m n : ZMod 2} {x y : E}
    (hx : x ∈ δ.part m) (hy : y ∈ δ.part n) :
    CStarModule.rightInner (B := B) x y ∈ γ.part (m + n) := by
  rw [γ.mem_part_iff_generator]
  rw [← δ.generator_rightInner]
  rw [(δ.mem_part_iff_generator m x).1 hx,
    (δ.mem_part_iff_generator n y).1 hy]
  simp only [CStarModule.rightInner_smul_left,
    CStarModule.rightInner_smul_right,
    CStarGrading.star_degreeSign, smul_smul]
  rw [mul_comm, ← CStarGrading.degreeSign_add]

/-- **Moving the generator from the second inner-product slot.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. For `x,y ∈ E`,
`⟨x,Gy⟩_B = σ(⟨Gx,y⟩_B)`. -/
theorem rightInner_generator_right
    (δ : CStarModuleGrading γ E) (x y : E) :
    CStarModule.rightInner (B := B) x (δ.generator y) =
      γ.generatorAut
        (CStarModule.rightInner (B := B) (δ.generator x) y) := by
  have h := δ.generator_rightInner (δ.generator x) y
  rw [δ.generator_involutive] at h
  exact h

/-- **Moving the generator from the first inner-product slot.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. For `x,y ∈ E`,
`⟨Gx,y⟩_B = σ(⟨x,Gy⟩_B)`. -/
theorem rightInner_generator_left
    (δ : CStarModuleGrading γ E) (x y : E) :
    CStarModule.rightInner (B := B) (δ.generator x) y =
      γ.generatorAut
        (CStarModule.rightInner (B := B) x (δ.generator y)) := by
  have h := δ.generator_rightInner x (δ.generator y)
  rw [δ.generator_involutive] at h
  exact h

/-! ## Opposite grading -/

/-- **Opposite module-grading generator.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete
right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying
`G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. The negated involution `-G` is a continuous
complex-linear equivalence of `E`, interchanging the even and odd parts. -/
def oppositeGenerator (δ : CStarModuleGrading γ E) : E ≃L[ℂ] E where
  toFun x := -δ.generator x
  invFun x := -δ.generator x
  left_inv x := by
    change -δ.generator (-δ.generator x) = x
    rw [map_neg, δ.generator_involutive, neg_neg]
  right_inv x := by
    change -δ.generator (-δ.generator x) = x
    rw [map_neg, δ.generator_involutive, neg_neg]
  map_add' x y := by
    rw [map_add]
    abel
  map_smul' z x := by simp
  continuous_toFun := δ.generator.continuous.neg
  continuous_invFun := δ.generator.continuous.neg

@[simp]
theorem oppositeGenerator_apply (δ : CStarModuleGrading γ E) (x : E) :
    δ.oppositeGenerator x = -δ.generator x :=
  rfl

/-- **Opposite Hilbert-module grading.** Let `B` be a graded nonunital complex C*-algebra with an order
on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a complete right
Hilbert `B`-module. A module grading has a continuous complex-linear involution `G` satisfying `G(x
b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. Replacing `G` by `-G` gives another grading of the
same right Hilbert module over the same coefficient grading, with even and odd parts interchanged. -/
def opposite (δ : CStarModuleGrading γ E) : CStarModuleGrading γ E where
  generator := δ.oppositeGenerator
  generator_involutive := δ.oppositeGenerator.left_inv
  generator_right_smul x b := by
    change -δ.generator (x <• b) =
      (-δ.generator x) <• γ.generatorAut b
    rw [δ.generator_right_smul]
    have hneg :
        (-δ.generator x) <• γ.generatorAut b =
          -(δ.generator x <• γ.generatorAut b) := by
      change CStarModule.rightSMulLinear (B := B) (-δ.generator x)
          (γ.generatorAut b) =
        -(CStarModule.rightSMulLinear (B := B) (δ.generator x)
          (γ.generatorAut b))
      rw [map_neg]
      rfl
    exact hneg.symm
  generator_rightInner x y := by
    change CStarModule.rightInner (B := B)
      (-δ.generator x) (-δ.generator y) =
        γ.generatorAut (CStarModule.rightInner (B := B) x y)
    simpa using δ.generator_rightInner x y

@[simp]
theorem opposite_generator_apply
    (δ : CStarModuleGrading γ E) (x : E) :
    δ.opposite.generator x = -δ.generator x :=
  rfl

theorem mem_opposite_evenPart_iff
    (δ : CStarModuleGrading γ E) (x : E) :
    x ∈ δ.opposite.evenPart ↔ x ∈ δ.oddPart := by
  rw [δ.opposite.mem_evenPart_iff_generator,
    δ.mem_oddPart_iff_generator]
  constructor
  · intro h
    have h' := congrArg Neg.neg h
    simpa using h'
  · intro h
    rw [opposite_generator_apply, h]
    simp

theorem mem_opposite_oddPart_iff
    (δ : CStarModuleGrading γ E) (x : E) :
    x ∈ δ.opposite.oddPart ↔ x ∈ δ.evenPart := by
  rw [δ.opposite.mem_oddPart_iff_generator,
    δ.mem_evenPart_iff_generator]
  constructor
  · intro h
    have h' := congrArg Neg.neg h
    simpa using h'
  · intro h
    rw [opposite_generator_apply, h]

/-! ## Homogeneous adjointable operators -/

section Operators

variable {F : Type uF} {G : Type uG}
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]

/-- **Degree of an adjointable operator.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with compatible
grading generators `G_E,G_F`. An adjointable operator `T : E → F` has degree `n ∈ ℤ/2ℤ` when `G_F T
= (-1)^n T G_E`. -/
def IsHomogeneousOperator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (n : ZMod 2)
    (T : CStarModule.AdjointableOperator B E F) : Prop :=
  ∀ x, δF.generator (T x) =
    CStarGrading.degreeSign n • T (δE.generator x)

theorem zero_isHomogeneousOperator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F) (n : ZMod 2) :
    IsHomogeneousOperator δE δF n 0 := by
  intro x
  simp

theorem id_isHomogeneousOperator
    (δE : CStarModuleGrading γ E) :
    IsHomogeneousOperator δE δE 0
      CStarModule.AdjointableOperator.id := by
  intro x
  simp

theorem comp_isHomogeneousOperator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (δG : CStarModuleGrading γ G)
    {m n : ZMod 2}
    {T : CStarModule.AdjointableOperator B E F}
    {S : CStarModule.AdjointableOperator B F G}
    (hT : IsHomogeneousOperator δE δF m T)
    (hS : IsHomogeneousOperator δF δG n S) :
    IsHomogeneousOperator δE δG (m + n) (S.comp T) := by
  intro x
  rw [CStarModule.AdjointableOperator.comp_apply, hS, hT, map_smul,
    smul_smul]
  rw [mul_comm, ← CStarGrading.degreeSign_add]
  rfl

/-- **Adjoint of a homogeneous module operator.** Let `B` be a graded nonunital complex C*-algebra with
an order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with
compatible grading generators `G_E,G_F`. If an adjointable `T : E → F` has degree `n`, its adjoint
`T* : F → E` has the same degree. -/
theorem adjoint_isHomogeneousOperator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    {n : ZMod 2}
    {T : CStarModule.AdjointableOperator B E F}
    (hT : IsHomogeneousOperator δE δF n T) :
    IsHomogeneousOperator δF δE n T.adjointOperator := by
  intro y
  apply CStarModule.ext_rightInner (B := B)
  intro x
  have hT' : T (δE.generator x) =
      CStarGrading.degreeSign n • δF.generator (T x) := by
    have h := congrArg
      (fun z : F ↦ CStarGrading.degreeSign n • z) (hT x)
    rw [smul_smul, CStarGrading.degreeSign_sq, one_smul] at h
    exact h.symm
  calc
    CStarModule.rightInner (B := B) x
        (δE.generator (T.adjointOperator y)) =
        γ.generatorAut
          (CStarModule.rightInner (B := B)
            (δE.generator x) (T.adjointOperator y)) :=
      δE.rightInner_generator_right x (T.adjointOperator y)
    _ = γ.generatorAut
        (CStarModule.rightInner (B := B) (T (δE.generator x)) y) := by
      rw [CStarModule.AdjointableOperator.adjointOperator_apply,
        T.adjoint_inner]
    _ = γ.generatorAut
        (CStarModule.rightInner (B := B)
          (CStarGrading.degreeSign n • δF.generator (T x)) y) := by
      rw [hT']
    _ = CStarGrading.degreeSign n •
        γ.generatorAut
          (CStarModule.rightInner (B := B) (δF.generator (T x)) y) := by
      rw [CStarModule.rightInner_smul_left, map_smul,
        CStarGrading.star_degreeSign]
    _ = CStarGrading.degreeSign n •
        CStarModule.rightInner (B := B) (T x) (δF.generator y) := by
      rw [δF.rightInner_generator_right]
    _ = CStarGrading.degreeSign n •
        CStarModule.rightInner (B := B) x
          (T.adjointOperator (δF.generator y)) := by
      rw [CStarModule.AdjointableOperator.adjointOperator_apply,
        T.adjoint_inner]
    _ = CStarModule.rightInner (B := B) x
        (CStarGrading.degreeSign n •
          T.adjointOperator (δF.generator y)) := by
      rw [CStarModule.rightInner_smul_right]

/-- **Operator degree under opposite module gradings.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with
compatible grading generators `G_E,G_F`. An adjointable `T : E → F` has degree `n` for the
generators `-G_E,-G_F` exactly when it has degree `n` for `G_E,G_F`. -/
theorem opposite_isHomogeneousOperator_iff
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (n : ZMod 2)
    (T : CStarModule.AdjointableOperator B E F) :
    IsHomogeneousOperator δE.opposite δF.opposite n T ↔
      IsHomogeneousOperator δE δF n T := by
  constructor
  · intro h x
    have hx := h x
    change -δF.generator (T x) =
      CStarGrading.degreeSign n • T (-δE.generator x) at hx
    rw [map_neg, smul_neg] at hx
    have hx' := congrArg Neg.neg hx
    simpa using hx'
  · intro h x
    change -δF.generator (T x) =
      CStarGrading.degreeSign n • T (-δE.generator x)
    rw [map_neg, smul_neg, h x]

/-- **Degree of a rank-one module operator.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with compatible
grading generators `G_E,G_F`. For `x ∈ F` of degree `m` and `y ∈ E` of degree `n`, the rank-one
adjointable operator `z ↦ x ⟨y,z⟩_B` has degree `m+n`. -/
theorem rankOne_isHomogeneousOperator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    {m n : ZMod 2} {x : F} {y : E}
    (hx : x ∈ δF.part m) (hy : y ∈ δE.part n) :
    IsHomogeneousOperator δE δF (m + n)
      (CStarModule.AdjointableOperator.rankOne x y) := by
  intro z
  have hinner : γ.generatorAut
      (CStarModule.rightInner (B := B) y z) =
      CStarGrading.degreeSign n •
        CStarModule.rightInner (B := B) y (δE.generator z) := by
    rw [← δE.generator_rightInner]
    rw [(δE.mem_part_iff_generator n y).1 hy]
    rw [CStarModule.rightInner_smul_left,
      CStarGrading.star_degreeSign]
  rw [CStarModule.AdjointableOperator.rankOne_apply,
    δF.generator_right_smul,
    (δF.mem_part_iff_generator m x).1 hx, hinner]
  simp only [CStarModule.right_smul_smul,
    CStarModule.smul_right_smul, smul_smul,
    CStarModule.AdjointableOperator.rankOne_apply]
  rw [mul_comm, ← CStarGrading.degreeSign_add]
  rw [add_comm n m]

/-! ### The induced grading on adjointable endomorphisms -/

section InducedEnd

variable [StarOrderedRing Bᵐᵒᵖ]

/-- **Conjugation of adjointable endomorphisms by a grading.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. Assume also that the
order on `Bᵐᵒᵖ` is star-compatible. For an adjointable endomorphism `T` of `E`, the formula `G T G`
defines another adjointable endomorphism. -/
def operatorConjugate
    (δ : CStarModuleGrading γ E)
    (T : CStarModule.AdjointableOperator.End B E) :
    CStarModule.AdjointableOperator.End B E where
  toContinuousLinearMap :=
    δ.generator.toContinuousLinearMap.comp
      (T.toContinuousLinearMap.comp δ.generator.toContinuousLinearMap)
  adjoint :=
    δ.generator.toContinuousLinearMap.comp
      (T.adjoint.comp δ.generator.toContinuousLinearMap)
  isAdjointPair' :=
    (CStarModule.AdjointableOperator.isAdjointPair_iff_adjoint_inner _ _).2 <| by
      intro x y
      change CStarModule.rightInner (B := B)
          (δ.generator (T (δ.generator x))) y =
        CStarModule.rightInner (B := B) x
          (δ.generator (T.adjoint (δ.generator y)))
      calc
        CStarModule.rightInner (B := B)
            (δ.generator (T (δ.generator x))) y =
            γ.generatorAut
              (CStarModule.rightInner (B := B)
                (T (δ.generator x)) (δ.generator y)) :=
          δ.rightInner_generator_left (T (δ.generator x)) y
        _ = γ.generatorAut
            (CStarModule.rightInner (B := B)
              (δ.generator x) (T.adjoint (δ.generator y))) := by
          rw [T.adjoint_inner]
        _ = CStarModule.rightInner (B := B) x
            (δ.generator (T.adjoint (δ.generator y))) :=
          (δ.rightInner_generator_right x
            (T.adjoint (δ.generator y))).symm

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem operatorConjugate_apply
    (δ : CStarModuleGrading γ E)
    (T : CStarModule.AdjointableOperator.End B E) (x : E) :
    operatorConjugate δ T x = δ.generator (T (δ.generator x)) :=
  rfl

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem operatorConjugate_adjointOperator
    (δ : CStarModuleGrading γ E)
    (T : CStarModule.AdjointableOperator.End B E) :
    operatorConjugate δ T.adjointOperator =
      (operatorConjugate δ T).adjointOperator := by
  ext x
  rfl

/-- **Grading automorphism of adjointable endomorphisms.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. Assume also that the
order on `Bᵐᵒᵖ` is star-compatible. Conjugation `T ↦ G T G` is an involutive complex star-algebra
automorphism of the adjointable endomorphism C*-algebra of `E`. -/
def operatorGenerator (δ : CStarModuleGrading γ E) :
    CStarModule.AdjointableOperator.End B E ≃⋆ₐ[ℂ]
      CStarModule.AdjointableOperator.End B E where
  toFun := operatorConjugate δ
  invFun := operatorConjugate δ
  left_inv T := by
    ext x
    change δ.generator
      (δ.generator (T (δ.generator (δ.generator x)))) = T x
    rw [δ.generator_involutive, δ.generator_involutive]
  right_inv T := by
    ext x
    change δ.generator
      (δ.generator (T (δ.generator (δ.generator x)))) = T x
    rw [δ.generator_involutive, δ.generator_involutive]
  map_add' T S := by
    ext x
    simp [operatorConjugate_apply]
  map_mul' T S := by
    ext x
    change δ.generator (T (S (δ.generator x))) =
      δ.generator
        (T (δ.generator (δ.generator (S (δ.generator x)))))
    rw [δ.generator_involutive]
  map_star' T := by
    change operatorConjugate δ T.adjointOperator =
      (operatorConjugate δ T).adjointOperator
    exact operatorConjugate_adjointOperator δ T
  map_smul' z T := by
    ext x
    simp [operatorConjugate_apply]

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem operatorGenerator_apply
    (δ : CStarModuleGrading γ E)
    (T : CStarModule.AdjointableOperator.End B E) (x : E) :
    operatorGenerator δ T x = δ.generator (T (δ.generator x)) :=
  rfl

omit [StarOrderedRing Bᵐᵒᵖ] in
theorem operatorGenerator_involutive
    (δ : CStarModuleGrading γ E) :
    Function.Involutive (operatorGenerator δ) :=
  (operatorGenerator δ).left_inv

/-- **Induced grading on adjointable endomorphisms.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let `E` be a
complete right Hilbert `B`-module. A module grading has a continuous complex-linear involution `G`
satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. Assume also that the order on `Bᵐᵒᵖ`
is star-compatible. Conjugation by `G` defines a point-norm continuous `ℤ/2ℤ` grading on the
adjointable endomorphism C*-algebra of `E`. -/
def operatorGrading (δ : CStarModuleGrading γ E) :
    CStarGrading (CStarModule.AdjointableOperator.End B E) :=
  CStarGrading.ofInvolution (operatorGenerator δ)
    (operatorGenerator_involutive δ)

@[simp]
theorem operatorGrading_generatorAut
    (δ : CStarModuleGrading γ E) :
    δ.operatorGrading.generatorAut = operatorGenerator δ :=
  CStarGrading.ofInvolution_generatorAut _ _

theorem mem_operatorGrading_part_iff
    (δ : CStarModuleGrading γ E) (n : ZMod 2)
    (T : CStarModule.AdjointableOperator.End B E) :
    T ∈ δ.operatorGrading.part n ↔
      IsHomogeneousOperator δ δ n T := by
  rw [δ.operatorGrading.mem_part_iff_generator]
  constructor
  · intro h x
    have hx := congrArg
      (fun S : CStarModule.AdjointableOperator.End B E ↦
        S (δ.generator x)) h
    change operatorGenerator δ T (δ.generator x) =
      CStarGrading.degreeSign n • T (δ.generator x) at hx
    rw [operatorGenerator_apply, δ.generator_involutive] at hx
    exact hx
  · intro h
    apply CStarModule.AdjointableOperator.ext
    intro x
    have hx := h (δ.generator x)
    change operatorGenerator δ T x =
      (CStarGrading.degreeSign n • T) x
    rw [operatorGenerator_apply]
    rw [δ.generator_involutive] at hx
    simpa using hx

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem operatorConjugate_rankOne
    (δ : CStarModuleGrading γ E) (x y : E) :
    operatorConjugate δ
        (CStarModule.AdjointableOperator.rankOne x y) =
      CStarModule.AdjointableOperator.rankOne
        (δ.generator x) (δ.generator y) := by
  ext z
  change δ.generator
      (x <• CStarModule.rightInner (B := B) y (δ.generator z)) =
    δ.generator x <•
      CStarModule.rightInner (B := B) (δ.generator y) z
  rw [δ.generator_right_smul,
    ← δ.rightInner_generator_left y z]

omit [StarOrderedRing Bᵐᵒᵖ] in
theorem operatorConjugate_mem_finiteRank
    (δ : CStarModuleGrading γ E)
    {T : CStarModule.AdjointableOperator.End B E}
    (hT : T ∈ CStarModule.AdjointableOperator.finiteRankSubmodule
      (B := B) (E := E) (F := E)) :
    operatorConjugate δ T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E) := by
  refine Submodule.span_induction
    (p := fun T _ ↦ operatorConjugate δ T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E)) ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [operatorConjugate_rankOne]
    exact CStarModule.AdjointableOperator.rankOne_mem_finiteRank
      (B := B) (E := E) (F := E) (δ.generator x) (δ.generator y)
  · change operatorGenerator δ 0 ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E)
    simpa only [map_zero] using
      (Submodule.zero_mem
        (CStarModule.AdjointableOperator.finiteRankSubmodule
          (B := B) (E := E) (F := E)))
  · intro T S _ _ hT hS
    change operatorGenerator δ (T + S) ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E)
    change operatorGenerator δ T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E) at hT
    change operatorGenerator δ S ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E) at hS
    simpa only [map_add] using Submodule.add_mem _ hT hS
  · intro c T _ hT
    change operatorGenerator δ (c • T) ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E)
    change operatorGenerator δ T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := B) (E := E) (F := E) at hT
    simpa only [map_smul] using Submodule.smul_mem _ c hT

theorem operatorConjugate_mem_compact
    (δ : CStarModuleGrading γ E)
    {T : CStarModule.AdjointableOperator.End B E}
    (hT : T ∈ CStarModule.AdjointableOperator.compactSubmodule
      (B := B) (E := E) (F := E)) :
    operatorConjugate δ T ∈
      CStarModule.AdjointableOperator.compactSubmodule
        (B := B) (E := E) (F := E) := by
  change T ∈ closure
    (CStarModule.AdjointableOperator.finiteRankSubmodule
      (B := B) (E := E) (F := E) :
        Set (CStarModule.AdjointableOperator.End B E)) at hT
  change operatorConjugate δ T ∈ closure
    (CStarModule.AdjointableOperator.finiteRankSubmodule
      (B := B) (E := E) (F := E) :
        Set (CStarModule.AdjointableOperator.End B E))
  exact map_mem_closure
    (StarAlgEquiv.isometry (operatorGenerator δ)).continuous hT
    (fun _ h ↦ operatorConjugate_mem_finiteRank δ h)

/-- **Induced grading on compact module endomorphisms.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, let `γ` be its grading with generator `σ`, and let
`E` be a complete right Hilbert `B`-module. A module grading has a continuous complex-linear
involution `G` satisfying `G(x b) = G(x) σ(b)` and `⟨Gx,Gy⟩_B = σ(⟨x,y⟩_B)`. Assume also that the
order on `Bᵐᵒᵖ` is star-compatible. Conjugation by `G` restricts to a grading of the compact
endomorphism C*-algebra, the norm-closed span of rank-one module operators. -/
def compactGrading (δ : CStarModuleGrading γ E) :
    CStarGrading
      (CStarModule.AdjointableOperator.CompactEnd B E) :=
  CStarGrading.restrictSubalgebra δ.operatorGrading
    CStarModule.AdjointableOperator.compactStarSubalgebra
    (fun T h ↦
      (CStarModule.AdjointableOperator.mem_compactStarSubalgebra _).2
        (operatorConjugate_mem_compact δ
          ((CStarModule.AdjointableOperator.mem_compactStarSubalgebra T).1 h)))

theorem mem_compactGrading_part_iff
    (δ : CStarModuleGrading γ E) (n : ZMod 2)
    (T : CStarModule.AdjointableOperator.CompactEnd B E) :
    T ∈ δ.compactGrading.part n ↔
      IsHomogeneousOperator δ δ n
        (T : CStarModule.AdjointableOperator.End B E) := by
  rw [compactGrading]
  rw [CStarGrading.mem_restrictSubalgebra_part_iff,
    mem_operatorGrading_part_iff]

end InducedEnd

end Operators

/-! ## Grading-equivariant unitary equivalences -/

section Unitary

variable {F : Type uF} {G : Type uG}
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]

/-- **Graded unitary module equivalence.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with compatible
grading generators `G_E,G_F`. A unitary right-module equivalence `U : E → F` is graded when it
satisfies `U G_E = G_F U`. -/
def IsGradedUnitaryEquiv
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (U : CStarModule.UnitaryEquiv B E F) : Prop :=
  ∀ x, U (δE.generator x) = δF.generator (U x)

theorem refl_isGradedUnitaryEquiv
    (δE : CStarModuleGrading γ E) :
    IsGradedUnitaryEquiv δE δE
      (CStarModule.UnitaryEquiv.refl (B := B) (E := E)) :=
  fun _ ↦ rfl

theorem symm_isGradedUnitaryEquiv
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (U : CStarModule.UnitaryEquiv B E F)
    (hU : IsGradedUnitaryEquiv δE δF U) :
    IsGradedUnitaryEquiv δF δE U.symm := by
  intro y
  calc
    U.symm (δF.generator y) =
        U.symm (δF.generator (U (U.symm y))) := by
      rw [U.apply_symm_apply]
    _ = U.symm (U (δE.generator (U.symm y))) := by
      rw [hU]
    _ = δE.generator (U.symm y) := U.symm_apply_apply _

theorem trans_isGradedUnitaryEquiv
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (δG : CStarModuleGrading γ G)
    (U : CStarModule.UnitaryEquiv B E F)
    (V : CStarModule.UnitaryEquiv B F G)
    (hU : IsGradedUnitaryEquiv δE δF U)
    (hV : IsGradedUnitaryEquiv δF δG V) :
    IsGradedUnitaryEquiv δE δG (U.trans V) := by
  intro x
  change V (U (δE.generator x)) = δG.generator (V (U x))
  rw [hU, hV]

end Unitary

/-! ## Direct sums -/

section Prod

variable {F : Type uF}
variable [StarOrderedRing Bᵐᵒᵖ]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- **Generator on the topological product of graded modules.** Let `B` be a graded nonunital complex
C*-algebra with an order on its opposite algebra, and let `E,F` be complete right Hilbert
`B`-modules with compatible grading generators `G_E,G_F`. The coordinate map `(x,y) ↦ (G_E x,G_F y)`
is a continuous complex-linear equivalence of `E × F` with its product norm topology. -/
def prodGeneratorRaw
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F) :
    (E × F) ≃L[ℂ] (E × F) where
  toFun p := (δE.generator p.1, δF.generator p.2)
  invFun p := (δE.generator p.1, δF.generator p.2)
  left_inv p := by
    ext
    · exact δE.generator_involutive p.1
    · exact δF.generator_involutive p.2
  right_inv p := by
    ext
    · exact δE.generator_involutive p.1
    · exact δF.generator_involutive p.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  continuous_toFun :=
    (δE.generator.continuous.comp continuous_fst).prodMk
      (δF.generator.continuous.comp continuous_snd)
  continuous_invFun :=
    (δE.generator.continuous.comp continuous_fst).prodMk
      (δF.generator.continuous.comp continuous_snd)

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem prodGeneratorRaw_apply
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F) (p : E × F) :
    prodGeneratorRaw δE δF p =
      (δE.generator p.1, δF.generator p.2) :=
  rfl

/-- **Generator of the Hilbert-module direct sum.** Let `B` be a graded nonunital complex C*-algebra
with an order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with
compatible grading generators `G_E,G_F`. Assume also that the opposite coefficient order is
star-compatible. On the direct-sum module `E ⊕ F`, with coefficient-valued inner product
`⟨(x,y),(x′,y′)⟩ = ⟨x,x′⟩ + ⟨y,y′⟩` and its induced norm, the generator acts by `(G_E x,G_F y)`. -/
def prodGenerator
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F) :
    WithCStarModule Bᵐᵒᵖ (E × F) ≃L[ℂ]
      WithCStarModule Bᵐᵒᵖ (E × F) :=
  (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
    (E := E × F)).trans
    ((prodGeneratorRaw δE δF).trans
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := E × F)).symm)

omit [StarOrderedRing Bᵐᵒᵖ] in
@[simp]
theorem prodGenerator_apply
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    WithCStarModule.equiv Bᵐᵒᵖ (E × F)
        (prodGenerator δE δF x) =
      (δE.generator x.1, δF.generator x.2) :=
  rfl

/-- **Grading of the Hilbert-module direct sum.** Let `B` be a graded nonunital complex C*-algebra with
an order on its opposite algebra, and let `E,F` be complete right Hilbert `B`-modules with
compatible grading generators `G_E,G_F`. Assume also that the opposite coefficient order is
star-compatible. The coordinatewise generator `(x,y) ↦ (G_E x,G_F y)` defines a compatible grading
on the complete right Hilbert-module direct sum `E ⊕ F`. -/
def prod
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F) :
    CStarModuleGrading γ (WithCStarModule Bᵐᵒᵖ (E × F)) where
  generator := prodGenerator δE δF
  generator_involutive x := by
    apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
    ext
    · exact δE.generator_involutive x.1
    · exact δF.generator_involutive x.2
  generator_right_smul x b := by
    apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
    ext
    · exact δE.generator_right_smul x.1 b
    · exact δF.generator_right_smul x.2 b
  generator_rightInner x y := by
    change CStarModule.rightInner (B := B)
          (δE.generator x.1) (δE.generator y.1) +
        CStarModule.rightInner (B := B)
          (δF.generator x.2) (δF.generator y.2) =
      γ.generatorAut
        (CStarModule.rightInner (B := B) x.1 y.1 +
          CStarModule.rightInner (B := B) x.2 y.2)
    rw [δE.generator_rightInner, δF.generator_rightInner, map_add]

@[simp]
theorem prod_generator_apply
    (δE : CStarModuleGrading γ E)
    (δF : CStarModuleGrading γ F)
    (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    WithCStarModule.equiv Bᵐᵒᵖ (E × F)
        ((prod δE δF).generator x) =
      (δE.generator x.1, δF.generator x.2) :=
  rfl

end Prod

/-! ## The coefficient self-module -/

section Self

open scoped CStarModule.Right

/-- **Generator on the coefficient self-module.** For a nonunital complex C*-algebra `B` with a `ℤ/2ℤ`
grading, its degree-one star automorphism is a continuous complex-linear equivalence of the
underlying vector space `B`. -/
def selfGenerator (γ : CStarGrading B) : B ≃L[ℂ] B where
  toFun x := γ.generatorAut x
  invFun x := γ.generatorAut x
  left_inv x := γ.generator_apply_generator x
  right_inv x := γ.generator_apply_generator x
  map_add' := map_add γ.generatorAut
  map_smul' := map_smul γ.generatorAut
  continuous_toFun := by
    have h : (fun x ↦ γ.generatorAut x) = ⇑γ.generatorCLM :=
      funext fun a ↦ (γ.generatorCLM_apply a).symm
    rw [h]
    exact γ.generatorCLM.continuous
  continuous_invFun := by
    have h : (fun x ↦ γ.generatorAut x) = ⇑γ.generatorCLM :=
      funext fun a ↦ (γ.generatorCLM_apply a).symm
    rw [h]
    exact γ.generatorCLM.continuous

omit [PartialOrder Bᵐᵒᵖ] in
@[simp]
theorem selfGenerator_apply (γ : CStarGrading B) (b : B) :
    selfGenerator γ b = γ.generatorAut b :=
  rfl

variable [StarOrderedRing Bᵐᵒᵖ]

/-- **Grading of the right coefficient self-module.** For a graded nonunital complex C*-algebra `B` with
a star-compatible order on `Bᵐᵒᵖ`, regard `B` as its own complete right Hilbert module, with right
multiplication and inner product `⟨x,y⟩_B = x* y`. Its coefficient grading generator defines the
compatible module grading. -/
def self (γ : CStarGrading B) : CStarModuleGrading γ B where
  generator := selfGenerator γ
  generator_involutive x := γ.generator_apply_generator x
  generator_right_smul x b := by
    simp only [selfGenerator_apply,
      CStarModule.Right.right_smul_self, map_mul]
  generator_rightInner x y := by
    simp only [selfGenerator_apply,
      CStarModule.Right.rightInner_self, map_mul, map_star]

@[simp]
theorem self_generator_apply (γ : CStarGrading B) (b : B) :
    (self γ).generator b = γ.generatorAut b :=
  rfl

end Self

end CStarModuleGrading
