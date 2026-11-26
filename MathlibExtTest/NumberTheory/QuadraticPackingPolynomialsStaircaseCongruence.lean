/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.quadraticPackingPolynomial_staircase_congruence.Test

private noncomputable def examplePolynomial (x y : ℝ) :=
  6 * (x - y / 2) * (x - y / 2 - 3 / 2) + x + y + 2

private theorem packing_example :
    IsQuadraticPackingPolynomial (sectorLatticePoints ((12 : ℝ) / 7)) examplePolynomial := by
  refine ⟨⟨6, -6, 3 / 2, -8, 11 / 2, 2, Or.inl (by norm_num), fun x y => ?_⟩, ?_⟩
  · unfold examplePolynomial
    ring
  let M (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - 1 / 2 * p.2, p.2)
  have hinj : Function.Injective M := by
    rintro ⟨x, y⟩ ⟨u, v⟩ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    dsimp at h₁ h₂
    exact Prod.ext (by linarith) h₂
  have hbij := isQuadraticPackingPolynomial_sheared_example_twelve_sevenths.2.comp
    (hinj.injOn.bijOn_image (s := sectorLatticePoints ((12 : ℝ) / 7)))
  convert hbij using 1
  funext p
  dsimp [Function.comp_def, M, examplePolynomial]
  ring

-- The interior point (2, 3) on J₁ has value 4. Every point on J₄ has that residue modulo 3.
example {q : ℝ × ℝ} (hq : q ∈ sectorStaircase 7 12 4) :
    ∃ z : ℤ, examplePolynomial q.1 q.2 = 4 + 3 * z := by
  have hp : ((2, 3) : ℝ × ℝ) ∈ sectorStaircase 7 12 1 :=
    ⟨⟨2, 3, by norm_num⟩, by norm_num⟩
  obtain ⟨z, hz⟩ := quadraticPackingPolynomial_staircase_congruence
    (by decide) (by decide) (by decide) packing_example (by decide)
    consecutiveStepDifference_example_twelve_sevenths 1 hp hq
  have hval : examplePolynomial 2 3 = 4 := by norm_num [examplePolynomial]
  exact ⟨z, by dsimp only at hz; rw [hval] at hz; push_cast at hz; linarith⟩

-- For an integral slope the staircases are vertical. Use the origin and the top of Jₖ.
example {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints n) P)
    (hstep : consecutiveStepDifference 1 n P = k) :
    ∃ z : ℤ, P k (n * k) - P 0 0 = z * k := by
  have hq : ((k : ℝ), (n : ℝ) * k) ∈ sectorStaircase 1 n (0 + k) := by
    refine ⟨⟨k, (n : ℤ) * k, by simp, by positivity, by simp⟩, by simp⟩
  exact quadraticPackingPolynomial_staircase_congruence (by decide) hn (by simp)
    (by simpa using hP) hk hstep 0 (zero_mem_sectorStaircase_zero 1 n) hq

end MetaMathlibExt.quadraticPackingPolynomial_staircase_congruence.Test
