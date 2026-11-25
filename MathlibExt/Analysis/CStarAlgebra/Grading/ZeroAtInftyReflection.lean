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

public import MathlibExt.Analysis.CStarAlgebra.Grading
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInfty

/-!
# Reflection gradings of zero-at-infinity functions

Continuous involutive negation on a domain gives its existing zero-at-infinity
function algebra a grading by precomposition. The coefficient algebra can be
any nonunital C-star algebra. The norm, topology and algebra operations remain
the original function-space structures.

For the real-line domain, the two homogeneous parts consist of even and odd
functions, with the usual averaging projections.
-/

@[expose] public section

open scoped CStarAlgebra ZeroAtInfty

noncomputable section

namespace CStarGrading

universe uX uA

variable (X : Type uX) [TopologicalSpace X] [InvolutiveNeg X] [ContinuousNeg X]
variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- **Reflection grading of vanishing functions.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. Precomposition by negation defines a `ℤ/2ℤ` grading, with generator `f(x)
↦ f(-x)`. -/
def zeroAtInftyNeg : CStarGrading C₀(X, A) :=
  ofInvolution
    (ZeroAtInftyContinuousMap.starAlgEquivPrecomp (Homeomorph.neg X))
    (by
      intro f
      ext x
      change f (- -x) = f x
      rw [neg_neg])

/-- **Reflection automorphism of vanishing functions.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. The degree-one generator is the star-algebra automorphism given by
precomposition with the negation homeomorphism. -/
@[simp]
theorem zeroAtInftyNeg_generatorAut :
    (zeroAtInftyNeg X A).generatorAut =
      ZeroAtInftyContinuousMap.starAlgEquivPrecomp (Homeomorph.neg X) :=
  ofInvolution_generatorAut _ _

/-- **Values of the reflection generator.** Let `X` be a topological space with a continuous involutive
negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)` carries the
supremum norm. For every `f ∈ C₀(X,A)` and `x ∈ X`, the generator has value `f(-x)`. -/
theorem zeroAtInftyNeg_generator_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInftyNeg X A).generatorAut f x = f (-x) := by
  rw [zeroAtInftyNeg_generatorAut]
  rfl

/-- **Even functions for reflection grading.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. A function `f ∈ C₀(X,A)` belongs to the even part exactly when `f(-x) =
f(x)` for every `x`. -/
theorem mem_zeroAtInftyNeg_evenPart_iff (f : C₀(X, A)) :
    f ∈ (zeroAtInftyNeg X A).evenPart ↔ ∀ x, f (-x) = f x := by
  rw [(zeroAtInftyNeg X A).mem_evenPart_iff_generator]
  constructor
  · intro hf x
    have hx := congrArg (fun g : C₀(X, A) => g x) hf
    simpa only [zeroAtInftyNeg_generator_apply] using hx
  · intro hf
    ext x
    simpa only [zeroAtInftyNeg_generator_apply] using hf x

/-- **Odd functions for reflection grading.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. A function `f ∈ C₀(X,A)` belongs to the odd part exactly when `f(-x) =
-f(x)` for every `x`. -/
theorem mem_zeroAtInftyNeg_oddPart_iff (f : C₀(X, A)) :
    f ∈ (zeroAtInftyNeg X A).oddPart ↔ ∀ x, f (-x) = -f x := by
  rw [(zeroAtInftyNeg X A).mem_oddPart_iff_generator]
  constructor
  · intro hf x
    have hx := congrArg (fun g : C₀(X, A) => g x) hf
    simpa only [zeroAtInftyNeg_generator_apply,
      ZeroAtInftyContinuousMap.neg_apply] using hx
  · intro hf
    ext x
    simpa only [zeroAtInftyNeg_generator_apply,
      ZeroAtInftyContinuousMap.neg_apply] using hf x

/-- **Even projection by reflection averaging.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. For `f ∈ C₀(X,A)`, its even projection at `x` is `(f(x) + f(-x))/2`. -/
theorem zeroAtInftyNeg_evenProjection_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInftyNeg X A).evenProjection f x =
      (2 : ℂ)⁻¹ • (f x + f (-x)) := by
  rw [evenProjection_apply]
  simp only [ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.add_apply, zeroAtInftyNeg_generator_apply]

/-- **Odd projection by reflection averaging.** Let `X` be a topological space with a continuous
involutive negation `x ↦ -x`, and let `A` be a nonunital complex C*-algebra. The algebra `C₀(X,A)`
carries the supremum norm. For `f ∈ C₀(X,A)`, its odd projection at `x` is `(f(x) - f(-x))/2`. -/
theorem zeroAtInftyNeg_oddProjection_apply (f : C₀(X, A)) (x : X) :
    (zeroAtInftyNeg X A).oddProjection f x =
      (2 : ℂ)⁻¹ • (f x - f (-x)) := by
  rw [oddProjection_apply]
  simp only [ZeroAtInftyContinuousMap.smul_apply,
    ZeroAtInftyContinuousMap.sub_apply, zeroAtInftyNeg_generator_apply]

end CStarGrading
