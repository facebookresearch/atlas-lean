/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`lean/ComparatorChallenges/EuclideanRamseySpherical.lean` (openai/math,
https://github.com/openai/math), revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source file and the applicable license files name no copyright holder or authors.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Euclidean Ramsey configurations

An injective finite indexed Euclidean Ramsey configuration is cospherical in its original
ambient space. No full-span assumption is needed, and the empty configuration is cospherical
vacuously. In the nonempty case, an affine dependence with a nonzero weighted difference of
squared norms obstructs a sphere. This obstruction persists in every congruent copy. A finite
coloring by residues of scaled integer parts then rules out a monochromatic copy in every
host dimension.

## References

* P. Erdös, R. L. Graham, P. Montgomery, B. L. Rothschild, J. Spencer, and E. G. Straus,
  [*Euclidean Ramsey Theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3),
  Journal of Combinatorial Theory, Series A **14** (1973), 341–363, §1 (Ramsey property),
  §3 (Theorem 13 and Lemmas 14–15), §4 (Theorem 16). We use the affine-dependence and
  squared-norm coloring argument of §3, with linear factorization for Lemma 14 and a direct
  floor-residue coloring for the real case of Lemma 15.
* R. Rado, *Note on combinatorial analysis*, Proceedings of the London Mathematical Society
  (2) **48** (1943), 122–160. The inhomogeneous-equation coloring in §4 of the above paper
  extends Rado's work.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- **Euclidean Ramsey configurations.** A fixed finite indexed family $a$ of points in Euclidean
space is Euclidean Ramsey if, for each finite palette with at least two colors, there is a positive
host dimension such that every coloring of that Euclidean space by that palette contains an
indexed monochromatic copy of $a$ with the same pairwise distances. The family $a$ may be empty
and may have repeated points. The distances are preserved, not merely proportional, and there is
no regularity restriction on colorings.

Sources: Erdős, Graham, Montgomery, Rothschild, Spencer and Straus,
[*Euclidean Ramsey theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3), §1, pp. 342–344;
[proof comparator, indexed formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseySpherical.lean#L10-L17). -/
@[expose] public def IsEuclideanRamsey {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ color : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j, dist (b i) (b j) = dist (a i) (a j)) ∧ ∃ k : Fin r, ∀ i, color (b i) = k

open scoped BigOperators InnerProductSpace

-- If the squared-norm functional vanishes on all linear relations among the differences,
-- it descends to their span. Extend it and represent it by an inner product to get a center.
private theorem cospherical_of_relations {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (o : ι)
    (h : ∀ w : ι → ℝ, (∑ i, w i • (a i - a o)) = 0 → (∑ i, w i * ‖a i - a o‖ ^ 2) = 0) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  classical
  let A := Fintype.linearCombination ℝ (fun i ↦ a i - a o)
  let q := Fintype.linearCombination ℝ (fun i ↦ ‖a i - a o‖ ^ 2)
  have hker : LinearMap.ker A ≤ LinearMap.ker q := by
    intro w hw
    simp only [LinearMap.mem_ker, A, q, Fintype.linearCombination_apply, smul_eq_mul] at hw ⊢
    exact h w hw
  let L := ((LinearMap.ker A).liftQ q hker).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨f, hf⟩ := L.exists_extend
  have hfactor (w : ι → ℝ) : f (A w) = q w := by
    simpa only [L, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply] using
      LinearMap.congr_fun hf ⟨A w, LinearMap.mem_range_self A w⟩
  let z := (InnerProductSpace.toDual ℝ E).symm f.toContinuousLinearMap
  have hz (i : ι) : ⟪z, a i - a o⟫_ℝ = ‖a i - a o‖ ^ 2 := by
    simpa only [A, q, Fintype.linearCombination_apply_single, one_smul, z,
      InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap'] using
      (hfactor (Pi.single i (1 : ℝ)))
  let u := (1 / 2 : ℝ) • z
  refine (EuclideanGeometry.cospherical_def _).2 ⟨a o + u, ‖u‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  apply (sq_eq_sq₀ dist_nonneg (norm_nonneg _)).1
  rw [dist_eq_norm, ← sub_sub, norm_sub_sq_real, real_inner_comm u (a i - a o)]
  have hu : ⟪u, a i - a o⟫_ℝ = (1 / 2 : ℝ) * ‖a i - a o‖ ^ 2 := by
    simp only [u, real_inner_smul_left, hz]
  rw [hu]
  ring

-- The Gram matrix of the differences from `o` is determined by the pairwise distances.
-- Consequently the same linear relation holds in the copy, even in another dimension.
private theorem weighted_sub_eq_zero_of_dist_eq {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ι → E} {b : ι → F} (o : ι) (w : ι → ℝ)
    (hd : ∀ i j, dist (b i) (b j) = dist (a i) (a j))
    (hw : (∑ i, w i • (a i - a o)) = 0) : (∑ i, w i • (b i - b o)) = 0 := by
  have hinner (i j : ι) : ⟪b i - b o, b j - b o⟫_ℝ = ⟪a i - a o, a j - a o⟫_ℝ := by
    simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hd]
  have hsq : ‖∑ i, w i • (b i - b o)‖ ^ 2 = ‖∑ i, w i • (a i - a o)‖ ^ 2 := by
    simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, hinner]
  simpa [hw] using hsq

private theorem sum_mul_sq_norm_sub_eq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : ι → E) (o : ι) (w : ι → ℝ)
    (hw : (∑ i, w i • (b i - b o)) = 0) :
    (∑ i, w i * (‖b i‖ ^ 2 - ‖b o‖ ^ 2)) = ∑ i, w i * ‖b i - b o‖ ^ 2 := by
  calc
    _ = ∑ i, (w i * ‖b i - b o‖ ^ 2 + 2 * ⟪w i • (b i - b o), b o⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_left]
      have hi := norm_add_sq_real (b i - b o) (b o)
      rw [sub_add_cancel] at hi
      rw [hi]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hw, inner_zero_left, mul_zero,
        add_zero]

-- Record, for each coefficient, the floor of its scaled contribution modulo twice `m`.
-- Matching colors make the total floor difference divisible by `2 * m`, but its distance
-- from `m` is at most the number of summands (strictly less than `m`).
private theorem exists_coloring_avoiding_weighted_sub {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∃ (r : ℕ), 2 ≤ r ∧ ∃ color : ℝ → Fin r, ∀ x y : ι → ℝ,
      (∀ i, color (x i) = color (y i)) → (∑ i, w i * (x i - y i)) ≠ c := by
  classical
  let m := Fintype.card ι + 1
  let N := 2 * m
  have hN : 2 ≤ N := by dsimp [N, m]; omega
  have : NeZero N := ⟨by omega⟩
  let palette := ι → ZMod N
  let e := Fintype.equivFin palette
  have hr : 2 ≤ Fintype.card palette := by
    rw [← ZMod.card N] at hN
    exact hN.trans (Fintype.card_le_of_injective (fun k : ZMod N ↦ fun _ : ι ↦ k)
      (fun _ _ h ↦ congrFun h (Classical.arbitrary ι)))
  let t (x : ℝ) (i : ι) : ℝ := (m : ℝ) / c * (w i * x)
  let color (x : ℝ) : Fin (Fintype.card palette) := e (fun i ↦ (⌊t x i⌋ : ZMod N))
  refine ⟨_, hr, color, fun x y hcolor hsum ↦ ?_⟩
  let z (i : ι) : ℤ := ⌊t (x i) i⌋ - ⌊t (y i) i⌋
  have hdvd : (N : ℤ) ∣ ∑ i, z i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    rw [Int.cast_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrFun (e.injective (hcolor i)) i
    exact (Int.cast_sub _ _).trans (sub_eq_zero.mpr hi)
  have htotal : (∑ i, (t (x i) i - t (y i) i)) = (m : ℝ) := by
    simp only [t, ← mul_sub, ← Finset.mul_sum, hsum]
    exact div_mul_cancel₀ _ hc
  have hbounds (i : ι) :
      t (x i) i - t (y i) i - 1 ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ t (x i) i - t (y i) i + 1 := by
    simp only [z, Int.cast_sub]
    constructor <;> linarith [Int.floor_le (t (x i) i), Int.floor_le (t (y i) i),
      Int.lt_floor_add_one (t (x i) i), Int.lt_floor_add_one (t (y i) i)]
  have hlo := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ (hbounds i).1
  have hhi := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ (hbounds i).2
  simp only [Finset.sum_sub_distrib _ (fun _ ↦ (1 : ℝ)), Finset.sum_add_distrib, htotal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Int.cast_sum] at hlo hhi
  have hm : (m : ℝ) = Fintype.card ι + 1 := by simp [m]
  have hN' : (N : ℝ) = 2 * (m : ℝ) := by simp [N]
  have hpos : 0 < ((∑ i, z i : ℤ) : ℝ) := by linarith
  have hlt : ((∑ i, z i : ℤ) : ℝ) < (N : ℝ) := by linarith
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (show 0 ≤ ∑ i, z i by exact_mod_cast hpos.le) (by exact_mod_cast hlt) hdvd
  simp [hzero] at hpos

/-- **Finite Euclidean Ramsey configurations are cospherical.** An injective indexed
configuration with the Euclidean Ramsey property lies on a sphere in its original
ambient space. There is no full-span requirement; empty configurations and singletons
are included. This is a necessary condition, not a converse.

Source: Erdős, Graham, Montgomery, Rothschild, Spencer and Straus,
[*Euclidean Ramsey theorems. I*](https://doi.org/10.1016/0097-3165(73)90011-3),
Theorem 13; [indexed statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseySpherical.lean#L19-L23). -/
public theorem euclideanRamsey_configurations_cospherical {s d : ℕ}
    (a : Fin s → EuclideanSpace ℝ (Fin d)) (ha : Function.Injective a)
    (hRamsey : IsEuclideanRamsey a) : EuclideanGeometry.Cospherical (Set.range a) := by
  have _ := ha
  cases s with
  | zero => simpa using (EuclideanGeometry.cospherical_empty (P := EuclideanSpace ℝ (Fin d)))
  | succ s =>
    by_contra h
    let o : Fin (s + 1) := 0
    have hrel : ¬ ∀ w : Fin (s + 1) → ℝ,
        (∑ i, w i • (a i - a o)) = 0 → (∑ i, w i * ‖a i - a o‖ ^ 2) = 0 :=
      fun hw ↦ h (cospherical_of_relations a o hw)
    push Not at hrel
    obtain ⟨w, hw, hc⟩ := hrel
    obtain ⟨r, hr, color, hcolor⟩ := exists_coloring_avoiding_weighted_sub w hc
    obtain ⟨D, _, hD⟩ := hRamsey r hr
    obtain ⟨b, hb, k, hk⟩ := hD (fun x ↦ color (‖x‖ ^ 2))
    apply hcolor (fun i ↦ ‖b i‖ ^ 2) (fun _ ↦ ‖b o‖ ^ 2) (fun i ↦ (hk i).trans (hk o).symm)
    rw [sum_mul_sq_norm_sub_eq b o w (weighted_sub_eq_zero_of_dist_eq o w hb hw)]
    simp_rw [← dist_eq_norm, hb]
