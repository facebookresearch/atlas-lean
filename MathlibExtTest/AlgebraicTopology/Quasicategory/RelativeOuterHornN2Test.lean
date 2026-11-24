/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.RelativeOuterHornN2

/-!
# Public client for strict relative right two-horn filling

Construct the horn from its two edges, as in a relative inverse-triangle
argument. Check that the returned triangle has both prescribed edges
and maps to the whole prescribed base triangle. The source carries no
separate quasicategory hypothesis.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory SSet
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.RelativeOuterHornN2Test

/-- A caller supplying the `{1,2}` and `{0,2}` edges retains both of
them and the exact base triangle after relative filling. -/
example {C D : SSet.{u}} {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    (g h : (Δ[1] : SSet.{u}) ⟶ C)
    (hgh : stdSimplex.δ (0 : Fin 2) ≫ g = stdSimplex.δ (0 : Fin 2) ≫ h)
    (σBar : (Δ[2] : SSet.{u}) ⟶ D)
    (hgq : g ≫ q = stdSimplex.δ (0 : Fin 3) ≫ σBar)
    (hhq : h ≫ q = stdSimplex.δ (1 : Fin 3) ≫ σBar)
    (hg : (Edge.mk' (yonedaEquiv g)).IsEquivalence) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ C,
      stdSimplex.δ (0 : Fin 3) ≫ σ = g ∧
      stdSimplex.δ (1 : Fin 3) ≫ σ = h ∧ σ ≫ q = σBar := by
  let f : ∀ (j : Fin 3) (_ : j ≠ 2), (Δ[1] : SSet.{u}) ⟶ C :=
    fun j _ ↦ ![g, h, h] j
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;>
      simp only [f, Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
        Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;> simp_all
  let φ : (Λ[2, 2] : SSet.{u}) ⟶ C := hf.desc
  have hφ0 : horn.ι 2 0 (by decide) ≫ φ = g := hf.ι_desc 0 (by decide)
  have hφ1 : horn.ι 2 1 (by decide) ≫ φ = h := hf.ι_desc 1 (by decide)
  have hφq : φ ≫ q = Λ[2, 2].ι ≫ σBar := by
    apply horn.hom_ext'
    intro j hj
    fin_cases j <;> simp only [Fin.reduceFinMk]
    · calc
        _ = g ≫ q := by rw [← Category.assoc, hφ0]
        _ = stdSimplex.δ (0 : Fin 3) ≫ σBar := hgq
        _ = _ := by rw [horn.ι_ι_assoc]
    · calc
        _ = h ≫ q := by rw [← Category.assoc, hφ1]
        _ = stdSimplex.δ (1 : Fin 3) ≫ σBar := hhq
        _ = _ := by rw [horn.ι_ι_assoc]
    · exact (hj rfl).elim
  have hcritical : (Edge.mk' (yonedaEquiv (horn.ι 2 0 (by decide) ≫ φ))).IsEquivalence := by
    rwa [hφ0]
  obtain ⟨σ, hσ, hσq⟩ :=
    exists_fill_relativeSpecialOuterHorn_two_two φ σBar hφq hcritical
  refine ⟨σ, ?_, ?_, hσq⟩
  · have h0 := congrArg (fun θ ↦ horn.ι 2 0 (by decide) ≫ θ) hσ
    simpa only [horn.ι_ι_assoc, hφ0] using h0
  · have h1 := congrArg (fun θ ↦ horn.ι 2 1 (by decide) ≫ θ) hσ
    simpa only [horn.ι_ι_assoc, hφ1] using h1

end MathlibExtTest.AlgebraicTopology.Quasicategory.RelativeOuterHornN2Test
