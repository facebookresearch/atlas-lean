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

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral order and opposite C-star algebras

This file proves that quasiregularity, quasispectra, self-adjointness, and the
canonical spectral order are compatible with passing between a C-star algebra
and its opposite algebra.
-/

@[expose] public section

namespace MulOpposite

/-- **Quasiregularity in an opposite ring.** For a nonunital ring `B` and `a ∈ B`, the element `op(a)`
is quasiregular in `Bᵐᵒᵖ` exactly when `a` is quasiregular in `B`. -/
theorem isQuasiregular_op_iff {B : Type*} [NonUnitalRing B] (a : B) :
    IsQuasiregular (op a) ↔ IsQuasiregular a := by
  simp only [isQuasiregular_iff]
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨unop y, ?_, ?_⟩
    · apply op_injective
      simpa [add_comm] using h2
    · apply op_injective
      simpa [add_comm] using h1
  · rintro ⟨y, h1, h2⟩
    refine ⟨op y, ?_, ?_⟩
    · apply unop_injective
      simpa [add_comm] using h2
    · apply unop_injective
      simpa [add_comm] using h1

/-- **Quasispectrum in an opposite ring.** For a commutative semiring `R`, a nonunital ring `B` carrying
an `R`-module structure, and `a ∈ B`, the quasispectrum over `R` of `op(a)` equals that of `a`. -/
theorem quasispectrum_op {R B : Type*} [CommSemiring R]
    [NonUnitalRing B] [Module R B] (a : B) :
    quasispectrum R (op a) = quasispectrum R a := by
  ext r
  simp only [quasispectrum, Set.mem_ofPred_eq]
  constructor
  · intro h hr hq
    apply h hr
    rw [show -(hr.unit⁻¹ • op a) = op (-(hr.unit⁻¹ • a)) by rfl]
    exact (isQuasiregular_op_iff (-(hr.unit⁻¹ • a))).2 hq
  · intro h hr hq
    apply h hr
    rw [show -(hr.unit⁻¹ • op a) = op (-(hr.unit⁻¹ • a)) by rfl] at hq
    exact (isQuasiregular_op_iff (-(hr.unit⁻¹ • a))).1 hq

/-- **Quasispectrum restriction in an opposite ring.** For commutative semirings `R,S` with an
`R`-algebra structure on `S`, a nonunital ring `B` carrying module structures over both scalars, an
element `a ∈ B`, and `f : S → R`, quasispectrum restriction along `f` holds for `op(a)` exactly when
it holds for `a`. -/
theorem quasispectrumRestricts_op_iff
    {R S B : Type*} [CommSemiring R] [CommSemiring S]
    [NonUnitalRing B] [Module R B] [Module S B] [Algebra R S]
    (a : B) (f : S → R) :
    QuasispectrumRestricts (op a) f ↔ QuasispectrumRestricts a f := by
  constructor
  · intro h
    constructor
    · intro s hs
      apply h.rightInvOn
      rwa [quasispectrum_op]
    · exact h.left_inv
  · intro h
    constructor
    · intro s hs
      apply h.rightInvOn
      rwa [quasispectrum_op] at hs
    · exact h.left_inv

/-- **Self-adjointness in an opposite type.** For a type `B` with a star operation and `a ∈ B`, `op(a)`
is self-adjoint exactly when `a` is self-adjoint. -/
theorem isSelfAdjoint_op_iff {B : Type*} [Star B] (a : B) :
    IsSelfAdjoint (op a) ↔ IsSelfAdjoint a := by
  constructor
  · intro h
    have hu := congrArg unop h
    simpa [IsSelfAdjoint] using hu
  · intro h
    have ho := congrArg op h
    simpa [IsSelfAdjoint] using ho

/-- **Positivity from the opposite C*-algebra.** For a nonunital complex C*-algebra `B`, a positive
element of its opposite algebra in canonical spectral order has positive underlying element in the
spectral order of `B`. -/
theorem spectralOrder_unop_nonneg {B : Type*} [NonUnitalCStarAlgebra B]
    {a : Bᵐᵒᵖ}
    (h : @LE.le Bᵐᵒᵖ (CStarAlgebra.spectralOrder Bᵐᵒᵖ).toLE 0 a) :
    @LE.le B (CStarAlgebra.spectralOrder B).toLE 0 (unop a) := by
  change (CStarAlgebra.spectralOrder Bᵐᵒᵖ).le 0 a at h
  change IsSelfAdjoint (a - 0) ∧
    QuasispectrumRestricts (a - 0) ContinuousMap.realToNNReal at h
  change IsSelfAdjoint (unop a - 0) ∧
    QuasispectrumRestricts (unop a - 0) ContinuousMap.realToNNReal
  simp only [sub_zero] at h ⊢
  constructor
  · have hop : IsSelfAdjoint (op (unop a)) := by
      simpa only [op_unop] using h.1
    exact (isSelfAdjoint_op_iff (unop a)).1 hop
  · have hop : QuasispectrumRestricts
        (op (unop a)) ContinuousMap.realToNNReal := by
      simpa only [op_unop] using h.2
    exact (quasispectrumRestricts_op_iff
      (unop a) ContinuousMap.realToNNReal).1 hop

end MulOpposite
