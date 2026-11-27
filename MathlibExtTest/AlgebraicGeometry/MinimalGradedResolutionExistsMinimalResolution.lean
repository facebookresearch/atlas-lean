/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MinimalGradedResolutionExistsMinimalResolution
public import MathlibExtTest.RingTheory.MinimalGradedResolution
public import MathlibExt.RingTheory.MinimalGradedResolution
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Tests for minimal graded resolutions over polynomial rings

The existence theorem applied to the polynomial ring in two variables over a
field with its standard grading: the zeroth rank is nonzero, ranks vanish past
the number of variables, and minimality forces all coordinates of syzygies to
have zero constant term.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MinimalGradedResolutionExistsMinimalResolution

open MathlibExt.RingTheory.MinimalGradedResolution
open MathlibExtTest.RingTheory.MinimalGradedResolution
open WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted

variable {k : Type*} [Field k]

/-- Elements of the irrelevant ideal have zero constant term. -/
theorem mem_irrelevant_constantCoeff_eq_zero (p : PolynomialRing k 2)
    (h : p ∈ irrelevant (k := k) (n := 2)) :
    MvPolynomial.constantCoeff p = 0 := by
  have hI : p ∈ MvPolynomial.idealOfVars (Fin 2) k := h
  have h1 : MvPolynomial.idealOfVars (Fin 2) k
      = MvPolynomial.idealOfVars (Fin 2) k ^ 1 := by rw [pow_one]
  rw [h1, MvPolynomial.mem_pow_idealOfVars_iff'] at hI
  have h0 := hI 0 (by simp : Finsupp.degree (0 : Fin 2 →₀ ℕ) < 1)
  rw [MvPolynomial.constantCoeff_eq]
  exact h0

/-- The minimal resolution of the polynomial ring needs a generator in degree zero. -/
theorem resolution_ranks_zero_ne_zero :
    ∃ P : MinimalResolution (selfGrading (k := k) (n := 2)), P.ranks 0 ≠ 0 := by
  obtain ⟨P⟩ := exists_minimalResolution (selfGrading (k := k) (n := 2))
  refine ⟨P, ?_⟩
  intro h0
  have hforall : ∀ f : Fin (P.ranks 0) → PolynomialRing k 2, f = 0 := by
    intro f
    funext j
    exfalso
    have h2 := j.isLt
    omega
  obtain ⟨x, hx⟩ := P.augmentation_surjective 1
  have hx0 : x = 0 := hforall x
  rw [hx0, map_zero] at hx
  exact one_ne_zero hx.symm

/-- The minimal resolution of the polynomial ring stops past two variables. -/
theorem resolution_ranks_three_eq_zero :
    ∃ P : MinimalResolution (selfGrading (k := k) (n := 2)), P.ranks 3 = 0 := by
  obtain ⟨P⟩ := exists_minimalResolution (selfGrading (k := k) (n := 2))
  exact ⟨P, P.length_bound 3 (by norm_num)⟩

/-- Minimality forces syzygy coordinates to have zero constant term. -/
theorem resolution_minimal_coords :
    ∃ P : MinimalResolution (selfGrading (k := k) (n := 2)),
      ∀ (y : Fin (P.ranks 0) → PolynomialRing k 2),
        y ∈ LinearMap.range (P.differential 0) →
          ∀ j, MvPolynomial.constantCoeff (y j) = 0 := by
  obtain ⟨P⟩ := exists_minimalResolution (selfGrading (k := k) (n := 2))
  refine ⟨P, ?_⟩
  intro y hy j
  have hymem : y ∈ irrelevant (k := k) (n := 2) • (⊤ :
      Submodule (PolynomialRing k 2) (Fin (P.ranks 0) → PolynomialRing k 2)) :=
    P.minimal 0 hy
  refine Submodule.smul_induction_on hymem ?_ ?_
  · intro r hr n hn
    have hr0 : MvPolynomial.constantCoeff r = 0 :=
      mem_irrelevant_constantCoeff_eq_zero r hr
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hr0, zero_mul]
  · intro x y hx hy
    rw [Pi.add_apply, map_add, hx, hy, add_zero]

/-- The existence theorem applies to the polynomial ring in two variables. -/
theorem resolution_exists_two_vars :
    Nonempty (MinimalResolution (selfGrading (k := k) (n := 2))) :=
  exists_minimalResolution (selfGrading (k := k) (n := 2))

end MathlibExtTest.AlgebraicGeometry.MinimalGradedResolutionExistsMinimalResolution
