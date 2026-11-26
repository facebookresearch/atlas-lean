/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ConductorLogGluing

/-!
# Tests for conductor branches and ideal orders

A branch involution of the normalized conductor is its own inverse, the branch different is the
normalized residue divisor `(1/m) · div` minus the canonical divisor of the branch, and the
ideal order of the zero ideal is the empty-set convention `0`.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogResidueDifferent
open MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches

variable {X N : Scheme.{0}} {ν : N ⟶ X} {C : ConductorSheaf ν}
  {G : ComponentGenerics (reducedConductor ν C)}
  [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]

/-- A branch involution is its own inverse. -/
example (I : BranchInvolution ν C G) : I.involution.inv = I.involution.hom :=
  calc I.involution.inv = I.involution.inv ≫ I.involution.hom ≫ I.involution.hom := by
        rw [I.square, Category.comp_id]
    _ = I.involution.hom := by rw [Iso.inv_hom_id_assoc]

/-- The branch different is the normalized residue divisor minus the canonical divisor. -/
example {k : Type} [Field k] {d : ℕ} (B : ConductorResidueBranch (k := k) (d := d) ν C G) :
    branchDifferent B =
      (1 / (B.degree : ℝ)) • LogPairs.realCast B.comparison.cartier.divisor -
        LogPairs.realCast (LogPairs.canonicalDivisor B.canonical) :=
  rfl

/-- The zero ideal has no nonzero local section: its order is the `sInf ∅ = 0` convention. -/
example {k : Type} [Field k] {d : ℕ} (V : LogPairs.NormalVariety k d)
    (p : LogPairs.PrimePoint V) : ConductorLogGluing.idealOrder V ⊥ p = 0 := by
  rw [ConductorLogGluing.idealOrder]
  convert Int.csInf_empty
  refine iff_of_false ?_ (by simp)
  rintro ⟨U, hU, hp, s, hs, hsI, -⟩
  exact hs (by simpa [Scheme.IdealSheafData.ideal_bot] using hsI)
