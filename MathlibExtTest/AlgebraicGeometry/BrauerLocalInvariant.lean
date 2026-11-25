/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerLocalInvariant

/-!
# Arithmetic Frobenius normalization of local invariants

Frobenius exponents lie in `[0, [E:K])`, so the primitive cyclic cocycle is
normalized (trivial when either argument is the identity) and vanishes for a
degree-one layer, where the required invariant `1/1` is indeed zero in `ℚ/ℤ`.
A carry contributes the base uniformizer. There are no degree-zero layers.
-/

noncomputable section

namespace MathlibExtTest.BrauerLocalInvariant

open AlgebraicGeometry.BrauerCoefficients AlgebraicGeometry.BrauerLocalInvariant
open ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Layers

variable (E : IntermediateField K (SeparableClosure K))
  [FiniteDimensional K E] [IsGalois K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension K E] (F : FrobeniusLayer K E) (π : Kˣ)

example (g : Field.absoluteGaloisGroup K) :
    frobeniusExponent K E F g =
      (F.exponents ((AlgEquiv.restrictNormalHom E) g.separableClosure)).toAdd.val := rfl

theorem frobeniusExponent_lt (g : Field.absoluteGaloisGroup K) :
    frobeniusExponent K E F g < Module.finrank K E := by
  have : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  exact ZMod.val_lt _

omit [FiniteDimensional K E] in
theorem frobeniusExponent_one : frobeniusExponent K E F 1 = 0 := by
  have h1 : (1 : Field.absoluteGaloisGroup K).separableClosure = 1 := by
    ext x
    rfl
  simp [frobeniusExponent, h1]

/-- The primitive cocycle is normalized at the identity. -/
example (h : Field.absoluteGaloisGroup K) : primitiveValue K E F π 1 h = 0 := by
  have hh := frobeniusExponent_lt K E F h
  rw [primitiveValue, frobeniusExponent_one]
  split_ifs
  · omega
  · rfl

example (g : Field.absoluteGaloisGroup K) : primitiveValue K E F π g 1 = 0 := by
  have hg := frobeniusExponent_lt K E F g
  rw [primitiveValue, frobeniusExponent_one]
  split_ifs
  · omega
  · rfl

/-- A carry contributes the base uniformizer. -/
example (g h : Field.absoluteGaloisGroup K)
    (hc : Module.finrank K E ≤ frobeniusExponent K E F g + frobeniusExponent K E F h) :
    primitiveValue K E F π g h =
      Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)) π) := by
  rw [primitiveValue]
  split_ifs
  · rfl
  · contradiction

/-- A degree-one layer has trivial primitive cocycle. -/
theorem primitiveValue_of_finrank_eq_one (hE : Module.finrank K E = 1)
    (g h : Field.absoluteGaloisGroup K) : primitiveValue K E F π g h = 0 := by
  have hg := frobeniusExponent_lt K E F g
  have hh := frobeniusExponent_lt K E F h
  rw [primitiveValue]
  split_ifs
  · omega
  · rfl

/-- At degree one the normalization asks for the invariant `1/1 = 0` of the zero
cocycle, consistently with additivity. -/
example (I : NormalizedLocalInvariant K) (hπ : valuation K (π : K) = uniformizer K)
    (hE : Module.finrank K E = 1) : I.val (cocycleClass K 0) = 0 := by
  have h := I.2 E F π hπ 0 fun g h => by
    rw [inhomogeneousValue_zero, primitiveValue_of_finrank_eq_one K E F π hE]
  rw [h, hE, Nat.cast_one, div_one]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨1, one_zsmul _⟩

end Layers

/-! ## Layer data -/

example (n : ℕ) (D : UnramifiedLayerData K n) : Module.finrank K D.E = n := D.degree_eq

example (n : ℕ) (D : UnramifiedLayerData K n) : IsGalois K D.E := inferInstance

example (n : ℕ) (D : UnramifiedLayerData K n) : IsNonarchimedeanLocalField D.E := inferInstance

/-- There are no degree-zero layers. -/
example : IsEmpty (UnramifiedLayerData K 0) :=
  ⟨fun D => (Module.finrank_pos (R := K) (M := D.E)).ne' D.degree_eq⟩

end MathlibExtTest.BrauerLocalInvariant
