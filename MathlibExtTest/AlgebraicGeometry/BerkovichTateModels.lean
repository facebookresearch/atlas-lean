/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
public import MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory

/-!
# A nonreduced boundary probe for the actual Tate-model carrier

The quotient by T² retains a nonzero square-zero element. This protects the
analytic interfaces' use of actual polynomial-ideal quotients against a
replacement by reduced pointwise function rings.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.BerkovichTateModels

variable (K : Type) [NormedField K] [IsUltrametricDist K]

/--
error: failed to synthesize
  CategoryTheory.Category.{0, 1}
    (MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory.RealizedScheme K)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth CategoryTheory.Category.{0, 1}
  (MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory.RealizedScheme K)

open MathlibExt.AlgebraicGeometry.BerkovichAnalyticCategory in
example [BoundedComposition K] : CategoryTheory.Category (RealizedScheme K) :=
  inferInstance

abbrev Tate := MvPowerSeries.Restricted K (fun _ : Fin 1 ↦ (1 : ℝ))

def coordinate : Tate K := MvPowerSeries.Restricted.X K (fun _ ↦ 1) 0

abbrev DualNumbers := Tate K ⧸ Ideal.span {coordinate K ^ 2}

def epsilon : DualNumbers K := Ideal.Quotient.mk _ (coordinate K)

example : epsilon K ^ 2 = 0 := by
  change (Ideal.Quotient.mk _ (coordinate K)) ^ 2 = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

example : epsilon K ≠ 0 := by
  intro h
  have hm : coordinate K ∈ Ideal.span {coordinate K ^ 2} :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.mp hm
  have hf' := congrArg (fun s : Tate K ↦ s.1) hf
  change f.1 * (MvPowerSeries.X (0 : Fin 1)) ^ 2 = MvPowerSeries.X 0 at hf'
  have hd : (MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ 2 ∣
      MvPowerSeries.X 0 := ⟨f.1, ((mul_comm _ _).trans hf').symm⟩
  have hc := MvPowerSeries.X_pow_dvd_iff.mp hd
    (Finsupp.single (0 : Fin 1) 1) (by simp)
  simp at hc

end MathlibExtTest.AlgebraicGeometry.BerkovichTateModels
