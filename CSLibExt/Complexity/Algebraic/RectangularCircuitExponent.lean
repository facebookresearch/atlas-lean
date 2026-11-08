/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.MatrixMultiplication
public import CSLibExt.Complexity.Algebraic.MatrixMultiplicationExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Rectangular matrix multiplication in the actual arithmetic-circuit model

The field is fixed before the asymptotic quantifiers. Each circuit must compute
every input matrix pair. Its coefficients and graph may depend on dimension and
epsilon, but not on those input values. The inner dimension is `ceil (n ^ k)`.

This operation exponent is distinct from the tensor-rank exponent. No asymptotic
equivalence, division-elimination result or field-characteristic transfer is assumed.
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

open MatrixMultiplicationExponent Filter

@[expose] public section

/-- Essentially `n^w` actual arithmetic circuits for rectangular matrix multiplication. -/
def HasRectangularCircuitExponent (F : Type u) [Field F] (k w : ℝ) : Prop :=
  0 ≤ k ∧ 0 ≤ w ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∃ c : MatrixArithmeticCircuit F n (rectangularInnerDimension n k) n,
      IsMatrixMultiplication c ∧ (c.size : ℝ) ≤ C * (n : ℝ) ^ (w + ε)

/-- The infimal admissible operation exponent, with an empty family giving infinity. -/
noncomputable def rectangularCircuitExponent (F : Type u) [Field F] (k : ℝ) : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧ HasRectangularCircuitExponent F k w}

/-- The supremum of nonnegative aspects having operation exponent exactly two. -/
noncomputable def dualCircuitExponent (F : Type u) [Field F] : ENNReal :=
  sSup {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
    rectangularCircuitExponent F k = 2}

/-- Every admissible operation exponent bounds its infimum. -/
theorem rectangularCircuitExponent_le_of_admissible (F : Type u) [Field F] {k w : ℝ}
    (h : HasRectangularCircuitExponent F k w) :
    rectangularCircuitExponent F k ≤ ENNReal.ofReal w := sInf_le ⟨w, rfl, h⟩

/-- Uniform lower bounds on admissible operation exponents pass to the infimum. -/
theorem le_rectangularCircuitExponent (F : Type u) [Field F] {k : ℝ} {W : ENNReal}
    (h : ∀ w : ℝ, HasRectangularCircuitExponent F k w → W ≤ ENNReal.ofReal w) :
    W ≤ rectangularCircuitExponent F k := by
  apply le_sInf
  rintro _ ⟨w, rfl, hw⟩
  exact h w hw

/-- An actually quadratic aspect is a lower bound on the dual exponent. -/
theorem le_dualCircuitExponent (F : Type u) [Field F] {k : ℝ} (hk : 0 ≤ k)
    (h : rectangularCircuitExponent F k = 2) : ENNReal.ofReal k ≤ dualCircuitExponent F :=
  le_sSup ⟨k, hk, rfl, h⟩

/-- A bound on every actually quadratic aspect bounds their supremum. -/
theorem dualCircuitExponent_le (F : Type u) [Field F] {K : ENNReal}
    (h : ∀ k : ℝ, 0 ≤ k → rectangularCircuitExponent F k = 2 → ENNReal.ofReal k ≤ K) :
    dualCircuitExponent F ≤ K := by
  apply sSup_le
  rintro _ ⟨k, hk, rfl, he⟩
  exact h k hk he

/-- The actual outer-product circuit gives an essentially quadratic zero-aspect algorithm. -/
theorem hasRectangularCircuitExponent_zero_two (F : Type u) [Field F] :
    HasRectangularCircuitExponent F 0 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro ε hε
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro n hn
  rw [rectangularInnerDimension_zero]
  refine ⟨outerMatrixCircuit F n n, outerMatrixCircuit_correct n n, ?_⟩
  simp only [outerMatrixCircuit_size, Nat.cast_mul, one_mul]
  calc
    (n : ℝ) * n = (n : ℝ) ^ (2 : ℝ) := by norm_num [Real.rpow_natCast, pow_two]
    _ ≤ (n : ℝ) ^ (2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- A positive outer dimension gives a positive rounded inner dimension. -/
theorem rectangularInnerDimension_pos {n : ℕ} (hn : 1 ≤ n) (k : ℝ) :
    0 < rectangularInnerDimension n k := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) k)

/-- Actual output costs prohibit any essentially subquadratic operation exponent. -/
theorem HasRectangularCircuitExponent.two_le {F : Type u} [Field F] {k w : ℝ}
    (h : HasRectangularCircuitExponent F k w) : 2 ≤ w := by
  by_contra hw
  have hε : 0 < (2 - w) / 2 := by linarith
  obtain ⟨C, _, N, hN, hb⟩ := h.2.2 ((2 - w) / 2) hε
  let p : ℝ := w + (2 - w) / 2
  have hd : 0 < 2 - p := by dsimp [p]; linarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 - p)) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hnC, hn⟩ :=
    ((ht.eventually (eventually_gt_atTop C)).and (eventually_ge_atTop N)).exists
  obtain ⟨c, hc, hs⟩ := hb n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hN.trans hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have ho : (n : ℝ) * n ≤ (c.size : ℝ) := by
    exact_mod_cast hc.output_cost_le ⟨0, rectangularInnerDimension_pos (hN.trans hn) k⟩
  have hmul := mul_lt_mul_of_pos_left hnC (Real.rpow_pos_of_pos hnpos p)
  rw [mul_comm ((n : ℝ) ^ p) C, ← Real.rpow_add hnpos] at hmul
  have he : p + (2 - p) = 2 := by linarith
  rw [he] at hmul
  have ho' : (n : ℝ) ^ (2 : ℝ) ≤ C * (n : ℝ) ^ p := by
    calc
      (n : ℝ) ^ (2 : ℝ) = (n : ℝ) * n := by norm_num [Real.rpow_natCast, pow_two]
      _ ≤ C * (n : ℝ) ^ p := ho.trans hs
  exact (not_lt_of_ge ho') hmul

/-- The infimal operation exponent is at least two, including the infinite case. -/
theorem two_le_rectangularCircuitExponent (F : Type u) [Field F] (k : ℝ) :
    2 ≤ rectangularCircuitExponent F k := by
  apply le_rectangularCircuitExponent F
  intro w hw
  simpa using ENNReal.ofReal_le_ofReal hw.two_le

/-- The exact zero-aspect operation exponent follows from actual outer-product circuits. -/
theorem rectangularCircuitExponent_zero (F : Type u) [Field F] :
    rectangularCircuitExponent F 0 = 2 := by
  apply le_antisymm
  · simpa using rectangularCircuitExponent_le_of_admissible F
      (hasRectangularCircuitExponent_zero_two F)
  · exact two_le_rectangularCircuitExponent F 0

/-- The family defining the dual exponent contains an actual quadratic endpoint. -/
theorem dualCircuitExponent_family_nonempty (F : Type u) [Field F] :
    {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
      rectangularCircuitExponent F k = 2}.Nonempty :=
  ⟨0, 0, by norm_num, by norm_num, rectangularCircuitExponent_zero F⟩

/-- Increasing an admissible operation exponent preserves every actual circuit witness. -/
theorem HasRectangularCircuitExponent.mono {F : Type u} [Field F] {k w w' : ℝ}
    (h : HasRectangularCircuitExponent F k w) (hww' : w ≤ w') :
    HasRectangularCircuitExponent F k w' := by
  obtain ⟨hk, hw, h⟩ := h
  refine ⟨hk, hw.trans hww', ?_⟩
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h ε hε
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn
  obtain ⟨c, hc, hs⟩ := hb n hn
  refine ⟨c, hc, hs.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.trans hn)
    (by linarith)

/-- Every positive exponent above the infimum has actual epsilon-qualified circuit witnesses. -/
theorem hasRectangularCircuitExponent_of_inf_lt (F : Type u) [Field F] {k w : ℝ}
    (hw : 0 < w) (h : rectangularCircuitExponent F k < ENNReal.ofReal w) :
    HasRectangularCircuitExponent F k w := by
  obtain ⟨_, ⟨v, rfl, hv⟩, hvw⟩ := sInf_lt_iff.mp h
  exact hv.mono ((ENNReal.ofReal_lt_ofReal_iff hw).mp hvw).le

/-- The infimum formulation is equivalent to the source's every-epsilon operation bound. -/
theorem rectangularCircuitExponent_le_iff (F : Type u) [Field F] {k w : ℝ}
    (hk : 0 ≤ k) (hw : 0 ≤ w) :
    rectangularCircuitExponent F k ≤ ENNReal.ofReal w ↔ HasRectangularCircuitExponent F k w := by
  constructor
  · intro h
    refine ⟨hk, hw, ?_⟩
    intro ε hε
    have hp : 0 < w + ε / 2 := by linarith
    have hl : rectangularCircuitExponent F k < ENNReal.ofReal (w + ε / 2) :=
      h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith))
    obtain ⟨C, hC, N, hN, hb⟩ :=
      (hasRectangularCircuitExponent_of_inf_lt F hp hl).2.2 (ε / 2) (by linarith)
    refine ⟨C, hC, N, hN, ?_⟩
    intro n hn
    have he : (w + ε / 2) + ε / 2 = w + ε := by ring
    simpa only [he] using hb n hn
  · exact rectangularCircuitExponent_le_of_admissible F

/-- When finite, the infimal exponent itself is the minimum in the every-epsilon sense. -/
theorem rectangularCircuitExponent_endpoint (F : Type u) [Field F] {k : ℝ}
    (hk : 0 ≤ k) (hfinite : rectangularCircuitExponent F k ≠ ⊤) :
    HasRectangularCircuitExponent F k (rectangularCircuitExponent F k).toReal := by
  apply (rectangularCircuitExponent_le_iff F hk ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal hfinite]

/-- The square matrix-multiplication operation exponent is the aspect-one case. At aspect
one the rounded inner dimension is exactly `n`, so this is the infimal exponent for actual
`n × n` by `n × n` arithmetic circuits in the every-epsilon sense. -/
noncomputable def squareMatrixMultiplicationCircuitExponent (F : Type u) [Field F] :
    ENNReal :=
  rectangularCircuitExponent F 1

/-- The square operation exponent is definitionally the aspect-one rectangular exponent. -/
theorem squareMatrixMultiplicationCircuitExponent_def (F : Type u) [Field F] :
    squareMatrixMultiplicationCircuitExponent F = rectangularCircuitExponent F 1 :=
  rfl

/-- Actual output costs give the trivial lower bound two for the square exponent. -/
theorem two_le_squareMatrixMultiplicationCircuitExponent (F : Type u) [Field F] :
    2 ≤ squareMatrixMultiplicationCircuitExponent F :=
  two_le_rectangularCircuitExponent F 1

/-- A real upper bound on the square exponent is exactly an every-epsilon family of
actual square matrix-multiplication circuits. -/
theorem squareMatrixMultiplicationCircuitExponent_le_iff (F : Type u) [Field F]
    {w : ℝ} (hw : 0 ≤ w) :
    squareMatrixMultiplicationCircuitExponent F ≤ ENNReal.ofReal w ↔
      HasRectangularCircuitExponent F 1 w :=
  rectangularCircuitExponent_le_iff F (by norm_num) hw

/-- When finite, the square exponent itself is admissible in the every-epsilon sense. -/
theorem squareMatrixMultiplicationCircuitExponent_endpoint (F : Type u) [Field F]
    (hfinite : squareMatrixMultiplicationCircuitExponent F ≠ ⊤) :
    HasRectangularCircuitExponent F 1
      (squareMatrixMultiplicationCircuitExponent F).toReal :=
  rectangularCircuitExponent_endpoint F (by norm_num) hfinite

end

end Cslib.Complexity.Algebraic
