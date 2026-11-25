/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanes
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

open MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted

-- In the smallest allowed dimension the matched hyperplane must be the point itself.
example (P : Set (Fin 1 → ℝ)) (hP : affineSpan ℝ P = ⊤) :
    ∃ f : P → ITSP.SpannedHyperplaneSet 1 P, Function.Injective f ∧
      ∀ p, (f p).val = ({p.val} : AffineSubspace ℝ (Fin 1 → ℝ)) := by
  obtain ⟨f, hf, hmem⟩ := OWR1183Question_holds 1 le_rfl P hP
  refine ⟨f, hf, fun p ↦ ?_⟩
  obtain ⟨l, c, hl, hH⟩ := (f p).property.1
  have hinj : Function.Injective l :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr
      (LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hl))
  ext x
  rw [AffineSubspace.mem_singleton_iff, hH, ← (hH p.val).mp (hmem p), hinj.eq_iff]

private abbrev Plane := Fin 2 → ℝ

private noncomputable def normal (t : ℝ) : Plane →ₗ[ℝ] ℝ :=
  LinearMap.proj 1 - t • LinearMap.proj 0

private noncomputable def slopeLine (t : ℝ) : AffineSubspace ℝ Plane :=
  (normal t).ker.toAffineSubspace

private theorem on_slopeLine (t : ℝ) (x : Plane) : x ∈ slopeLine t ↔ x 1 = t * x 0 := by
  change x 1 - t * x 0 = 0 ↔ _
  exact sub_eq_zero

-- The full plane has infinitely many spanned hyperplanes through the origin.
example : Infinite {H : ITSP.SpannedHyperplaneSet 2 Set.univ // (0 : Plane) ∈ H.val} := by
  have line (t : ℝ) : slopeLine t ∈ ITSP.SpannedHyperplaneSet 2 Set.univ := by
    refine ⟨⟨normal t, 0, ?_, fun _ ↦ Iff.rfl⟩, (slopeLine t : Set Plane),
      Set.subset_univ _, AffineSubspace.affineSpan_coe _⟩
    intro he
    have h := LinearMap.congr_fun he (![0, 1] : Plane)
    simp [normal] at h
  let pencil (t : ℝ) : {H : ITSP.SpannedHyperplaneSet 2 Set.univ // (0 : Plane) ∈ H.val} :=
    ⟨⟨slopeLine t, line t⟩, (on_slopeLine t 0).mpr (by simp)⟩
  apply Infinite.of_injective pencil
  intro s t he
  have heq : slopeLine s = slopeLine t := congrArg (fun H ↦ H.val.val) he
  have hs : (![1, s] : Plane) ∈ slopeLine s := (on_slopeLine _ _).mpr (by simp)
  have h : s = t * 1 := (on_slopeLine t _).mp (heq ▸ hs)
  simpa only [mul_one] using h
