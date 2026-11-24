/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Best `M`-term approximation in an orthonormal basis

Let `(b i)_{i ∈ ι}` be a finite orthonormal basis of an inner product space `E` and write
`cᵢ = ⟨b i, f⟩` for the coefficients of `f`. An `M`-term approximation of `f` is a vector
`∑_{i ∈ T} aᵢ b i` with `#T ≤ M` (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7
(1998), 51–150, Section 2, (2.2)–(2.3)). Because the basis is orthonormal,

`‖f - ∑_{i ∈ T} aᵢ b i‖² = ∑_{i ∈ T} |cᵢ - aᵢ|² + ∑_{i ∉ T} |cᵢ|²`,

so for a fixed support the best coefficients are `aᵢ = cᵢ` (orthogonal projection, DeVore (2.7)–
(2.8)), and the best support keeps the `M` largest coefficients: the error of the best `M`-term
approximation is the sum of the squares of the remaining coefficients (DeVore (2.19)). In signal
processing this is thresholding of the coefficients in a basis, the core of nonlinear (sparse)
approximation in wavelet bases (DeVore, Section 3.6 for the Haar basis and Section 7.4 for
wavelet bases).

## Main declarations

* `norm_sub_sum_smul_sq` : the error formula above for an arbitrary support and coefficients.
* `sum_le_sum_of_forall_le` : on nonnegative weights, a set holding the largest weights has the
  largest sum among sets of no larger cardinality.
* `norm_sub_sum_inner_smul_sq` : the error of keeping the coefficients on `S`.
* `norm_sub_sum_inner_smul_le` : keeping the `#S` largest coefficients is a best
  `#S`-term approximation.

The statements are for a finite orthonormal basis (`OrthonormalBasis`); the separable Hilbert
space case of DeVore's Section 2 is not formalized here.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.BestMTermApproximation

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- **Error of an `M`-term approximation in an orthonormal basis** (R. A. DeVore, *Nonlinear
approximation*, Acta Numerica 7 (1998), Section 2, the computation behind (2.8) and (2.19)).
For a finite orthonormal basis `b`, a finite set `T` of indices and coefficients `a`,
`‖f - ∑_{i ∈ T} aᵢ b i‖² = ∑_{i ∈ T} |⟨b i, f⟩ - aᵢ|² + ∑_{i ∉ T} |⟨b i, f⟩|²`. -/
theorem norm_sub_sum_smul_sq (b : OrthonormalBasis ι 𝕜 E) (f : E) (T : Finset ι)
    (a : ι → 𝕜) :
    ‖f - ∑ i ∈ T, a i • b i‖ ^ 2 =
      ∑ i ∈ T, ‖⟪b i, f⟫_𝕜 - a i‖ ^ 2 + ∑ i ∈ Tᶜ, ‖⟪b i, f⟫_𝕜‖ ^ 2 := by
  have hcoord : ∀ i, b.repr (f - ∑ j ∈ T, a j • b j) i =
      ⟪b i, f⟫_𝕜 - if i ∈ T then a i else 0 := by
    intro i
    simp only [map_sub, map_sum, map_smul, OrthonormalBasis.repr_self, PiLp.sub_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      OrthonormalBasis.repr_apply_apply]
    simp
  rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_sum_compl T]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcoord]; simp [hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcoord]; simp [Finset.mem_compl.mp hi]

omit [Fintype ι] [DecidableEq ι] in
/-- **The largest weights have the largest sum.** Let `w ≥ 0` and let `S` hold the largest
weights: `w j ≤ w i` whenever `i ∈ S` and `j ∉ S`. Then every `T` with `#T ≤ #S` has
`∑_{i ∈ T} w i ≤ ∑_{i ∈ S} w i`. This is the rearrangement step behind DeVore, *Nonlinear
approximation*, Acta Numerica 7 (1998), (2.19). -/
theorem sum_le_sum_of_forall_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {S T : Finset ι}
    (hcard : T.card ≤ S.card) (hS : ∀ i ∈ S, ∀ j ∉ S, w j ≤ w i) :
    ∑ i ∈ T, w i ≤ ∑ i ∈ S, w i := by
  classical
  rw [← Finset.sum_inter_add_sum_sdiff T S w, ← Finset.sum_inter_add_sum_sdiff S T w,
    Finset.inter_comm T S]
  refine add_le_add_right (?_ : ∑ x ∈ T \ S, w x ≤ ∑ x ∈ S \ T, w x) _
  have hc : (T \ S).card ≤ (S \ T).card := by
    have h1 := Finset.card_sdiff_add_card_inter T S
    have h2 := Finset.card_sdiff_add_card_inter S T
    rw [Finset.inter_comm] at h2
    omega
  rcases (S \ T).eq_empty_or_nonempty with hST | hST
  · rw [hST, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at hc
    simp [hc, hST]
  · set m := (S \ T).inf' hST w
    have hle : ∀ j ∈ T \ S, w j ≤ m := fun j hj =>
      Finset.le_inf' hST w fun i hi =>
        hS i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
    have hm : 0 ≤ m := Finset.le_inf' hST w fun i _ => hw i
    calc ∑ j ∈ T \ S, w j ≤ (T \ S).card • m := Finset.sum_le_card_nsmul _ _ _ hle
      _ ≤ (S \ T).card • m := nsmul_le_nsmul_left hm hc
      _ ≤ ∑ i ∈ S \ T, w i :=
        Finset.card_nsmul_le_sum _ _ _ fun i hi => Finset.inf'_le w hi

/-- **Error of keeping the coefficients on a set.** For a finite orthonormal basis `b` and a
set `S`, `‖f - ∑_{i ∈ S} ⟨b i, f⟩ b i‖² = ∑_{i ∉ S} |⟨b i, f⟩|²` (DeVore, *Nonlinear
approximation*, Acta Numerica 7 (1998), (2.8), and (2.19) when `S` holds the largest
coefficients). -/
theorem norm_sub_sum_inner_smul_sq (b : OrthonormalBasis ι 𝕜 E) (f : E) (S : Finset ι) :
    ‖f - ∑ i ∈ S, ⟪b i, f⟫_𝕜 • b i‖ ^ 2 = ∑ i ∈ Sᶜ, ‖⟪b i, f⟫_𝕜‖ ^ 2 := by
  rw [norm_sub_sum_smul_sq]
  simp

omit [DecidableEq ι] in
/-- **Best `M`-term approximation in an orthonormal basis** (R. A. DeVore, *Nonlinear
approximation*, Acta Numerica 7 (1998), Section 2, (2.3) and (2.19)). Let `b` be a finite
orthonormal basis and let `S` hold the largest coefficients of `f`:
`|⟨b j, f⟩| ≤ |⟨b i, f⟩|` whenever `i ∈ S` and `j ∉ S`. Then `∑_{i ∈ S} ⟨b i, f⟩ b i` is a
best `#S`-term approximation of `f`: for every set `T` with `#T ≤ #S` and all coefficients `a`,
`‖f - ∑_{i ∈ S} ⟨b i, f⟩ b i‖ ≤ ‖f - ∑_{i ∈ T} aᵢ b i‖`. With
`norm_sub_sum_inner_smul_sq`, the best `M`-term error `σ_M(f)` satisfies
`σ_M(f)² = ∑_{i ∉ S} |⟨b i, f⟩|²`, the sum of the squares of all but the `M` largest
coefficients. -/
theorem norm_sub_sum_inner_smul_le (b : OrthonormalBasis ι 𝕜 E) (f : E) {S T : Finset ι}
    (hcard : T.card ≤ S.card) (hS : ∀ i ∈ S, ∀ j ∉ S, ‖⟪b j, f⟫_𝕜‖ ≤ ‖⟪b i, f⟫_𝕜‖)
    (a : ι → 𝕜) :
    ‖f - ∑ i ∈ S, ⟪b i, f⟫_𝕜 • b i‖ ≤ ‖f - ∑ i ∈ T, a i • b i‖ := by
  classical
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sub_sum_inner_smul_sq, norm_sub_sum_smul_sq]
  set w : ι → ℝ := fun i => ‖⟪b i, f⟫_𝕜‖ ^ 2
  have htot : ∀ U : Finset ι, ∑ i ∈ Uᶜ, w i = ∑ i, w i - ∑ i ∈ U, w i := fun U => by
    rw [← Finset.sum_add_sum_compl U w]; ring
  have hTS : ∑ i ∈ T, w i ≤ ∑ i ∈ S, w i :=
    sum_le_sum_of_forall_le w (fun i => sq_nonneg _) hcard fun i hi j hj =>
      pow_le_pow_left₀ (norm_nonneg _) (hS i hi j hj) 2
  have hnn : 0 ≤ ∑ i ∈ T, ‖⟪b i, f⟫_𝕜 - a i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  change ∑ i ∈ Sᶜ, w i ≤ _ + ∑ i ∈ Tᶜ, w i
  rw [htot S, htot T]
  linarith

end MathlibExt.Analysis.InnerProductSpace.BestMTermApproximation
