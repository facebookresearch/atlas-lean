/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PosDef.GreedyMinima
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Minkowski's second theorem (weak form) for a positive definite form on `ℤ^g`

Let `Y` be a real symmetric positive definite `g × g` matrix, `Q(x) = ᵗx Y x`, and let
`λ₁ ≤ ⋯ ≤ λ_g` be greedy successive minima of `Q` on `ℤ^g`
(`Matrix.IsGreedyMinima`, `Matrix.PosDef.succMin`). This module proves

* `Matrix.IsGreedyMinima.prod_le_pow_mul_det`, `Matrix.PosDef.prod_succMin_le_pow_mul_det`:
  `λ₁ λ₂ ⋯ λ_g ≤ g ^ g det Y`.

This is the weak form of Minkowski's second theorem in O. Regev, *Lattices in computer
science*, lecture notes, Tel Aviv University, Fall 2004, Lecture 1, §3, Theorem 3, p. 8:
`(∏ λ_i(Λ)) ^ (1/n) ≤ √n (det Λ) ^ (1/n)`, squared, for the lattice `Λ = ℤ^g` with the norm `√Q`:
the squared determinant `(det Λ)²` is `det Y`, and the greedy minima `λ_i` take the place of the
squared successive minima `λ_i(Λ)²`.

The proof follows Regev's. Write `Y = ᵗB B`, so that `Q(x) = |Bx|²`, and let `e₁, …, e_g` be the
Gram–Schmidt orthonormalization of `Bv₁, …, Bv_g`, with coordinates `c_i(x) = ⟨e_i, Bx⟩`, so that
`Q(x) = ∑ c_i(x)²`. The open box `{x : |c_i(x)| < √(λ_i / g)}`, the cube of Regev's Claim 1 (p. 7)
inside his ellipsoid `T`, is convex and symmetric, and contains no nonzero integral `y`: for the
least `k` with `y ∈ span(v₁, …, v_k)`, property (b) of greedy minima gives `λ_k ≤ Q(y)`, while
`c_i(y) = 0` for `i > k`, so `Q(y) < ∑_{i ≤ k} λ_i / g ≤ λ_k`. Its volume is
`∏ 2 √(λ_i / g) / |det B|`, so Minkowski's convex body theorem (Regev's Theorem 9, p. 7;
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) bounds it by `2 ^ g`.
-/

@[expose] public section

open Module MeasureTheory

namespace Matrix

variable {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}

namespace IsGreedyMinima

variable {v : Fin g → Fin g → ℤ}

/-- **Minkowski's second theorem, weak form**, for a positive definite form on `ℤ^g`. Let `Y` be a
real symmetric positive definite `g × g` matrix, `Q(x) = ᵗx Y x`, and `v₁, …, v_g` greedy
successive minima vectors of `Q` (`Matrix.IsGreedyMinima`), with `λ_k = Q(v_k)`. Then
$$\lambda_1 \lambda_2 \cdots \lambda_g \le g^g \det Y.$$
This is Regev's Theorem 3, `(∏ λ_i(Λ)) ^ (1/n) ≤ √n (det Λ) ^ (1/n)`, squared, for the lattice
`ℤ^g` with the norm `√Q`, with the greedy minima in place of the successive minima.

The proof applies Minkowski's convex body theorem to the open box `|c_i(x)| < √(λ_i / g)` in the
coordinates `c_i` along the Gram–Schmidt orthonormalization of the `v_i` for the form `Q`.

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Theorem 3 (Minkowski's second theorem), p. 8, proof pp. 8–9; Theorem 9 and
Claim 1, p. 7. -/
theorem prod_le_pow_mul_det (hY : Y.PosDef) (hv : IsGreedyMinima Y v) :
    ∏ k, (Int.cast ∘ v k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v k) ≤ (g : ℝ) ^ g * Y.det := by
  classical
  set w : Fin g → Fin g → ℝ := fun i ↦ Int.cast ∘ v i
  set lam : Fin g → ℝ := fun k ↦ w k ⬝ᵥ Y *ᵥ w k
  change ∏ k, lam k ≤ _
  obtain ⟨B, hYB, hB⟩ := hY.exists_eq_transpose_mul_self
  have hQ : ∀ x, x ⬝ᵥ Y *ᵥ x = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := fun x ↦ by
    rw [hYB, dotProduct_transpose_mul_self_mulVec]
  have hdet : Y.det = B.det ^ 2 := by rw [hYB, det_mul, det_transpose, sq]
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    simp
  have hlam_pos : ∀ i, 0 < lam i := hv.pos hY
  -- Coordinates along the Gram–Schmidt basis of the vectors `B v_i`.
  let T : (Fin g → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm.toLinearMap ∘ₗ Matrix.toLin' B
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin g)) = Fintype.card (Fin g) := by simp
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis hfin fun i ↦ T (w i)
  let Φ : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).toLinearMap ∘ₗ e.repr.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm.toLinearMap
  let c : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℝ) := Φ ∘ₗ Matrix.toLin' B
  have hc_apply : ∀ x i, c x i = inner ℝ (e i) (T x) := fun x i ↦ by
    simp [c, Φ, T, OrthonormalBasis.repr_apply_apply]
  have hc_sum : ∀ x, x ⬝ᵥ Y *ᵥ x = ∑ i, c x i ^ 2 := fun x ↦ by
    have h1 : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = ‖T x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [T, dotProduct, sq]
    have h3 : ‖e.repr (T x)‖ ^ 2 = ∑ i, c x i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [c, Φ, T]
    rw [hQ, h1, ← e.repr.norm_map, h3]
  have hc_zero : ∀ x k, x ∈ Submodule.span ℝ (w '' Set.Iic k) → ∀ j, k < j → c x j = 0 := by
    intro x k hx j hkj
    have : Submodule.span ℝ (w '' Set.Iic k) ≤ LinearMap.ker (LinearMap.proj j ∘ₗ c) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_proj, Function.eval]
      rw [hc_apply]
      exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hfin _
        (lt_of_le_of_lt (Set.mem_Iic.mp hi) hkj)
    simpa using this hx
  -- The open box `s` of half-sides `r i = √(λ_i / g)` in these coordinates.
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set r : Fin g → ℝ := fun i ↦ √(lam i / g)
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ Real.sqrt_nonneg _
  have hr_sq : ∀ i, r i ^ 2 = lam i / g := fun i ↦
    Real.sq_sqrt (div_nonneg (hlam_pos i).le hgR.le)
  set box : Set (Fin g → ℝ) := Set.univ.pi fun i ↦ Set.Ioo (-r i) (r i)
  set s : Set (Fin g → ℝ) := c ⁻¹' box
  -- `s` contains no nonzero integral vector.
  have hno : ∀ y : Fin g → ℤ, y ≠ 0 → (Int.cast ∘ y : Fin g → ℝ) ∉ s := by
    intro y hy hys
    set x : Fin g → ℝ := Int.cast ∘ y
    have hx0 : x ≠ 0 := fun h ↦ hy (funext fun i ↦ by simpa [x] using congrFun h i)
    have hlast : x ∈ Submodule.span ℝ (w '' Set.Iic ⟨g - 1, by omega⟩) := by
      have : Set.Iic (⟨g - 1, by omega⟩ : Fin g) = Set.univ := by
        ext i
        simp only [Set.mem_Iic, Set.mem_univ, iff_true, Fin.le_def]
        omega
      rw [this, Set.image_univ, hv.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, hkmin⟩ := WellFounded.has_min wellFounded_lt
      {k : Fin g | x ∈ Submodule.span ℝ (w '' Set.Iic k)} ⟨_, hlast⟩
    have hnot : x ∉ Submodule.span ℝ (w '' Set.Iio k) := by
      intro hmem
      obtain ⟨k, hkg⟩ := k
      rcases k with _ | m
      · have : Set.Iio (⟨0, hkg⟩ : Fin g) = ∅ := by
          ext i
          simp [Fin.lt_def]
        rw [this, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hmem
        exact hx0 hmem
      · have : Set.Iio (⟨m + 1, hkg⟩ : Fin g) = Set.Iic ⟨m, by omega⟩ := by
          ext i
          simp only [Set.mem_Iio, Set.mem_Iic, Fin.lt_def, Fin.le_def]
          omega
        rw [this] at hmem
        exact hkmin ⟨m, by omega⟩ hmem (Fin.lt_def.mpr (by simp))
    have hlamk : lam k ≤ x ⬝ᵥ Y *ᵥ x := hv.le_of_notMem_span k y hnot
    have hcoord : ∀ j, c x j ^ 2 < r j ^ 2 := fun j ↦ by
      have := hys j (Set.mem_univ j)
      exact sq_lt_sq' this.1 this.2
    have hsum : x ⬝ᵥ Y *ᵥ x = ∑ j ∈ Finset.Iic k, c x j ^ 2 := by
      rw [hc_sum]
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_).symm
      rw [hc_zero x k hk j (not_le.mp (by simpa using hj)), sq, mul_zero]
    have hlt : x ⬝ᵥ Y *ᵥ x < lam k := by
      calc x ⬝ᵥ Y *ᵥ x = ∑ j ∈ Finset.Iic k, c x j ^ 2 := hsum
        _ < ∑ j ∈ Finset.Iic k, r j ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨k, Finset.mem_Iic.mpr le_rfl⟩ fun j _ ↦ hcoord j
        _ ≤ ∑ _j ∈ Finset.Iic k, lam k / g := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            rw [hr_sq]
            gcongr
            exact hv.monotone (Finset.mem_Iic.mp hj)
        _ = (k + 1 : ℕ) * (lam k / g) := by rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
        _ ≤ g * (lam k / g) := by
            gcongr
            · exact div_nonneg (hlam_pos k).le hgR.le
            · exact_mod_cast k.2
        _ = lam k := by field_simp
    exact absurd hlamk (not_le.mpr hlt)
  -- If the bound failed, `s` would have volume `> 2 ^ g`.
  by_contra hcon
  push Not at hcon
  have hgg : (0 : ℝ) < (g : ℝ) ^ g := by positivity
  have hprod_sq : (∏ i, r i) ^ 2 = (∏ i, lam i) / (g : ℝ) ^ g := by
    rw [← Finset.prod_pow, Finset.prod_congr rfl fun i _ ↦ hr_sq i, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdetB : |B.det| < ∏ i, r i := by
    refine lt_of_pow_lt_pow_left₀ 2 (Finset.prod_nonneg fun i _ ↦ hr0 i) ?_
    rw [sq_abs, ← hdet, hprod_sq, lt_div_iff₀ hgg, mul_comm]
    exact hcon
  let Ψ : (Fin g → ℝ) → (Fin g → ℝ) := fun z ↦ (e.repr (WithLp.toLp 2 z)).ofLp
  have hΨ : MeasurePreserving Ψ volume volume :=
    (PiLp.volume_preserving_ofLp _).comp
      (e.measurePreserving_repr.comp (PiLp.volume_preserving_toLp _))
  have hs_eq : s = (Matrix.toLin' B) ⁻¹' (Ψ ⁻¹' box) := rfl
  have hdetB0 : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hs_vol : volume s = ENNReal.ofReal (|B.det|⁻¹ * ∏ i, (2 * r i)) := by
    rw [hs_eq, Measure.addHaar_preimage_linearMap _ hdetB0, LinearMap.det_toLin',
      hΨ.measure_preimage (MeasurableSet.univ_pi fun i ↦ measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, ← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ by linarith [hr0 i],
      ← ENNReal.ofReal_mul (by positivity), abs_inv]
    congr 2
    exact Finset.prod_congr rfl fun i _ ↦ by ring
  set b := Pi.basisFun ℝ (Fin g)
  have hfund := ZSpan.isAddFundamentalDomain b volume
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [map_neg, Pi.neg_apply, Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hconv : Convex ℝ s := (convex_pi fun i _ ↦ convex_Ioo _ _).linear_preimage c
  have hlt : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin g → ℝ) < volume s := by
    rw [hF, one_mul, hs_vol, finrank_fin_fun, show (2 : ENNReal) ^ g = ENNReal.ofReal (2 ^ g) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, lt_inv_mul_iff₀ (abs_pos.mpr hB),
      mul_comm]
    exact mul_lt_mul_of_pos_left hdetB (by positivity)
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup) hfund hsymm hconv hlt
  choose y hy using (b.mem_span_iff_repr_mem ℤ (x : Fin g → ℝ)).mp x.2
  have hxy : (x : Fin g → ℝ) = Int.cast ∘ y := by
    ext i
    simpa [b] using (hy i).symm
  refine hno y (fun h ↦ hx0 (Subtype.ext ?_)) (hxy ▸ hxs)
  rw [hxy, h]
  ext
  simp

end IsGreedyMinima

namespace PosDef

/-- **Minkowski's second theorem, weak form**, for the greedy successive minima of a real positive
definite `g × g` matrix `Y` (`Matrix.PosDef.succMin`):
$$\lambda_1 \lambda_2 \cdots \lambda_g \le g^g \det Y.$$

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Theorem 3 (Minkowski's second theorem), p. 8. -/
theorem prod_succMin_le_pow_mul_det (hY : Y.PosDef) :
    ∏ k, hY.succMin k ≤ (g : ℝ) ^ g * Y.det :=
  hY.isGreedyMinima_greedyMinVec.prod_le_pow_mul_det hY

end PosDef

end Matrix
