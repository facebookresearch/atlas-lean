/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Area of a fundamental parallelogram

For a period pair `(ω₁, ω₂)` and `α ∈ ℂ`, the fundamental parallelogram
`{α + t₁ ω₁ + t₂ ω₂ : t₁, t₂ ∈ [0, 1)}` has Lebesgue measure `|Im(conj ω₁ · ω₂)|`, and its
translates by the lattice `ℤω₁ + ℤω₂` are pairwise disjoint and cover `ℂ`: every `z ∈ ℂ` lies in
exactly one of them.

## Main results

* `PeriodPair.volume_fundamentalParallelogram`: the measure is `|Im(conj ω₁ · ω₂)|`.
* `PeriodPair.volume_fundamentalParallelogram_of_ω₁_eq_one`: for `(1, τ)` with `Im τ > 0`, it is
  `Im τ`.
* `PeriodPair.existsUnique_sub_mem_fundamentalParallelogram`: the translates tile `ℂ`.
-/

@[expose] public section

open MeasureTheory

namespace PeriodPair

/-- The unit square `{z : Re z ∈ [0, 1), Im z ∈ [0, 1)}`, the fundamental domain of the basis
`1, i` of `ℂ`, has Lebesgue measure `1`. -/
theorem _root_.Complex.volume_fundamentalDomain_basisOneI :
    volume (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  have hset : ZSpan.fundamentalDomain Complex.basisOneI =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Complex.coe_basisOneI_repr, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_preimage, Set.mem_prod,
      Complex.measurableEquivRealProd_apply]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
  simp

/-- The determinant of the period basis `ω₁, ω₂` in the basis `1, i` of `ℂ` is
`Im(conj ω₁ · ω₂) = Re ω₁ Im ω₂ - Im ω₁ Re ω₂`. -/
theorem basisOneI_det_basis (L : PeriodPair) :
    Complex.basisOneI.det L.basis = (starRingEnd ℂ L.ω₁ * L.ω₂).im := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, basis_zero, basis_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **Area of a fundamental parallelogram.** Let $\omega_1, \omega_2$ be $\mathbb{R}$-linearly
independent complex numbers and let $\alpha \in \mathbb{C}$. With $\mathbb{C}$ identified with
$\mathbb{R}^2$ by $z = x + iy$ and given Lebesgue measure, the fundamental parallelogram
$P = \{\alpha + t_1\omega_1 + t_2\omega_2 : t_1, t_2 \in [0, 1)\}$ has measure
$|\operatorname{Im}(\bar\omega_1 \omega_2)|$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1, p. 86,
for the period parallelogram of a lattice; the measure is computed here by the change of
variables formula for linear maps. -/
theorem volume_fundamentalParallelogram (L : PeriodPair) (α : ℂ) :
    volume (L.fundamentalParallelogram α) =
      ENNReal.ofReal |(starRingEnd ℂ L.ω₁ * L.ω₂).im| := by
  rw [fundamentalParallelogram, Set.image_add_left, measure_preimage_add,
    ZSpan.measure_fundamentalDomain L.basis volume Complex.basisOneI,
    Complex.volume_fundamentalDomain_basisOneI, mul_one, basisOneI_det_basis]

/-- **Area of the fundamental parallelogram of $\mathbb{Z} + \mathbb{Z}\tau$.** For a period pair
$(1, \tau)$ with $\operatorname{Im}\tau > 0$ and $\alpha \in \mathbb{C}$, the fundamental
parallelogram $\{\alpha + t_1 + t_2\tau : t_1, t_2 \in [0, 1)\}$ has Lebesgue measure
$\operatorname{Im}\tau$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1, p. 86,
for the period parallelogram; the measure is computed here. -/
theorem volume_fundamentalParallelogram_of_ω₁_eq_one (L : PeriodPair) (h₁ : L.ω₁ = 1)
    (hτ : 0 < L.ω₂.im) (α : ℂ) :
    volume (L.fundamentalParallelogram α) = ENNReal.ofReal L.ω₂.im := by
  rw [volume_fundamentalParallelogram, h₁]
  simp [abs_of_pos hτ]

/-- **The translates of a fundamental parallelogram tile the plane.** Let $\omega_1, \omega_2$ be
$\mathbb{R}$-linearly independent complex numbers,
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$
and $P$ the fundamental parallelogram with vertex $\alpha$. Every $z \in \mathbb{C}$ lies in
exactly one translate $P + \lambda$, $\lambda \in \Lambda$: there is a unique $\lambda \in \Lambda$
with $z - \lambda \in P$. So the translates are pairwise disjoint and cover $\mathbb{C}$.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1, p. 86,
for the period parallelogram; the tiling is proved here from the coordinates in the basis
$\omega_1, \omega_2$. -/
theorem existsUnique_sub_mem_fundamentalParallelogram (L : PeriodPair) (α z : ℂ) :
    ∃! l : ℂ, l ∈ L.lattice ∧ z - l ∈ L.fundamentalParallelogram α := by
  have hspan := L.lattice_eq_span_range_basis
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain L.basis (z - α)
  have hmem : ∀ l : ℂ, z - l ∈ L.fundamentalParallelogram α ↔
      -l + (z - α) ∈ ZSpan.fundamentalDomain L.basis := by
    intro l
    simp only [fundamentalParallelogram, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      convert hw using 1
      linear_combination -hwz
    · intro h
      exact ⟨_, h, by ring⟩
  have hv' : (v : ℂ) ∈ L.lattice := by rw [hspan]; exact v.2
  refine ⟨-(v : ℂ), ⟨neg_mem hv', ?_⟩, ?_⟩
  · rw [hmem, neg_neg]
    exact hv
  · rintro l ⟨hl, hlP⟩
    have hl' : -l ∈ Submodule.span ℤ (Set.range L.basis) := by rw [← hspan]; exact neg_mem hl
    have := huniq ⟨-l, hl'⟩ ((hmem l).mp hlP)
    rw [← this]
    simp

end PeriodPair
