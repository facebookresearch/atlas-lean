/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Probability.Distributions.Uniform

/-!
# Uniformity of a finite-field dot product

If a weight vector has a nonzero coordinate, its dot product with a uniform vector is uniform
on the field. For each target, the fiber is equivalent to the assignments to all other
coordinates: the missing coordinate is obtained by subtracting their contribution and dividing
by its weight. This gives exactly `|F| ^ (|ι| - 1)` vectors in each fiber.

## References

* Neal Young, UCR CS 260 course notes, *FreivaldsTrick* (2004):
  <https://www.cs.ucr.edu/~neal/2004/cs260-static-mirror/wiki.pl%3Faction=browse&diff=2&id=FreivaldsTrick.html>.
  The notes pair vectors over `𝔽₂` by flipping a distinguished coordinate and pose the
  finite-field generalization as an exercise. The fiber construction adapts that argument
  by solving for the distinguished coordinate over an arbitrary field.
* Alon, Dietzfelbinger, Miltersen, Petrank and Tardos, *Linear Hash Functions*, §1,
  <https://web.math.princeton.edu/~nalon/PDFS/linhash13.pdf>, discusses universality of
  families of linear maps over finite fields, a related application.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MetaMathlibExt

variable {ι F : Type*} [Fintype ι] [Field F] {d : ι → F} {i₀ : ι}

/-- Restrict a vector in the fiber of `t` to the coordinates other than `i₀`. The inverse
fills in `i₀` by solving the dot product equation using the nonzero weight `d i₀`. -/
@[expose] noncomputable def dotProductFiberEquiv (hd : d i₀ ≠ 0) (t : F) :
    {r : ι → F // r ⬝ᵥ d = t} ≃ ({i : ι // i ≠ i₀} → F) := by
  classical
  let rest (u : {i : ι // i ≠ i₀} → F) : F := ∑ i, u i * d i
  have hsplit (r : ι → F) : r ⬝ᵥ d = r i₀ * d i₀ + rest (fun i ↦ r i) := by
    calc
      r ⬝ᵥ d = r i₀ * d i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * d i :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
      _ = _ := by
        rw [Finset.sum_subtype (p := fun i ↦ i ≠ i₀) _ (by simp)]
  let fill (u : {i : ι // i ≠ i₀} → F) (i : ι) : F :=
    if h : i = i₀ then (t - rest u) / d i₀ else u ⟨i, h⟩
  have hfill (u : {i : ι // i ≠ i₀} → F) : (fun i : {i : ι // i ≠ i₀} ↦ fill u i) = u := by
    funext i
    simp [fill, i.property]
  refine
    { toFun := fun r i ↦ r.1 i
      invFun := fun u ↦ ⟨fill u, ?_⟩
      left_inv := ?_
      right_inv := hfill }
  · rw [hsplit, hfill]
    simp only [fill, dite_eq_left rfl]
    rw [div_mul_cancel₀ _ hd, sub_add_cancel]
  · intro r
    apply Subtype.ext
    funext i
    change fill (fun j ↦ r.1 j) i = r.1 i
    by_cases hi : i = i₀
    · subst i
      have hr := r.property
      rw [hsplit] at hr
      simp only [fill, dite_eq_left rfl]
      exact ((eq_div_iff_mul_eq hd).2 (eq_sub_of_add_eq hr)).symm
    · simp [fill, hi]

/-- Every fiber of a dot product with a nonzero weight vector has `|F| ^ (|ι| - 1)` elements. -/
theorem card_dotProduct_fiber [Fintype F] (hd : d i₀ ≠ 0) (t : F) :
    Nat.card {r : ι → F // r ⬝ᵥ d = t} = Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  rw [Nat.card_congr (dotProductFiberEquiv hd t), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_subtype_compl (· = i₀), Fintype.card_subtype_eq]

variable [Fintype F] [DecidableEq ι] [MeasurableSpace F] [MeasurableSingletonClass F]

/-- Under the uniform law on vectors, a dot product with a nonzero weight vector equals any
fixed target (including zero) with probability `1 / |F|`. -/
theorem uniformOfFinset_dotProduct_eq (hd : d i₀ ≠ 0) (t : F) :
    Measure.uniformOfFinset (Finset.univ : Finset (ι → F)) {r | r ⬝ᵥ d = t} =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  have hi : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hF : (Fintype.card F : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hF' := ENNReal.natCast_ne_top (Fintype.card F)
  rw [Measure.uniformOfFinset_apply, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  simp only [Set.mem_ofPred_eq, card_dotProduct_fiber hd t, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow]
  conv_lhs =>
    arg 2
    rw [← Nat.sub_add_cancel hi, pow_succ]
  simpa only [mul_one, ENNReal.div_eq_inv_mul] using
    ENNReal.mul_div_mul_left 1 (Fintype.card F : ℝ≥0∞)
      (ENNReal.pow_ne_zero hF _) (ENNReal.pow_ne_top hF')

/-- The dot product with a weight vector having a nonzero coordinate sends the uniform measure
on all vectors to the uniform measure on the field. -/
theorem map_uniformOfFinset_dotProduct (hd : d i₀ ≠ 0) :
    (Measure.uniformOfFinset (Finset.univ : Finset (ι → F))).map (fun r ↦ r ⬝ᵥ d) =
      Measure.uniformOfFinset (Finset.univ : Finset F) := by
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton t),
    Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ t), Finset.card_univ]
  exact uniformOfFinset_dotProduct_eq hd t

end MetaMathlibExt
