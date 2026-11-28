/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TreeMetric
public import Domains.Biology.PopulationGenetics.FStatisticsCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Distributions.Gaussian.Fernique
import MathlibExt.Analysis.Convex.Straszewicz

/-!
# Conditional negative definiteness and realizability of f2 matrices

The `f2` matrix of any square-integrable model is conditionally negative semidefinite,
since the centred covariance is positive semidefinite. Conversely (Schoenberg), a
symmetric zero-diagonal matrix is conditionally negative semidefinite iff it is a
squared-Euclidean distance matrix, iff it is realized as the `f2` matrix of an
unconstrained drift model, via the centred Gaussian vector with covariance the double
centring. For frequencies bounded in `[0, 1]` there is the extra constraint `f2 ≤ 1`:
the realizable matrices are then characterized through the closed convex hull of the
unit `f2` points, and already `[[0, 4], [4, 0]]` separates the two notions. Every
symmetric zero-diagonal 3-by-3 conditionally negative semidefinite matrix whose
largest off-diagonal entry is the `0 1` entry, as can be arranged by relabeling the
populations, is realized by the three-population admixture model with nonnegative
lengths. The 4-by-4 square is realizable but not a tree metric.

## Main results

* `Admixture.f2_isCondNegSemidef`, `Admixture.posSemidef_centredCov`: every `f2` matrix
  is conditionally negative semidefinite.
* `Admixture.isF2Realizable_iff`, `Admixture.isCondNegSemidef_iff_exists_sqDist`:
  Schoenberg's characterization.
* `Admixture.isF2RealizableUnit_iff`, `Admixture.f2_le_one`: the `[0, 1]`-bounded case.
* `Admixture.exists_driftModel_admix_three`: realization, after relabeling so the
  `0 1` entry is largest, of symmetric zero-diagonal 3-by-3 matrices by the admixture
  model.
* `Admixture.not_isTreeMetric_squareF2`, `Admixture.not_isF2Realizable_nonCndF2`: the
  separating examples.

## References

* I. J. Schoenberg, "Remarks to Maurice Fréchet's article", *Annals of Mathematics* 36
  (1935), 724–732.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
  MathlibExt.Biology.Phylogenetics.Buneman
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

universe u

namespace MathlibExt.Biology.PopulationGenetics.Admixture

/-! ### Definitions -/

/-- `D` is conditionally negative semidefinite: `∑ i j, c i * c j * D i j ≤ 0` whenever
`∑ i, c i = 0`. -/
def IsCondNegSemidef {P : Type*} [Fintype P] (D : P → P → ℝ) : Prop :=
  ∀ c : P → ℝ, ∑ i, c i = 0 → ∑ i, ∑ j, c i * c j * D i j ≤ 0

/-- `D` is the `f2` matrix of an unconstrained (real-valued) drift model on a probability space:
some finite edge set, square-integrable increments that are pairwise orthogonal in L², and
arbitrary real weights. -/
def IsF2Realizable {P : Type u} (D : P → P → ℝ) : Prop :=
  ∃ (E : Type u) (_ : Fintype E) (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
    (_ : IsProbabilityMeasure μ) (M : DriftModel μ E P), ∀ X Y, f2 μ M.freq X Y = D X Y

/-- The `f2` matrices `((x i - x j) ^ 2)_{ij}` of single frequency vectors `x ∈ [0,1]^P`. -/
def unitF2Points (P : Type u) : Set (P → P → ℝ) :=
  Set.range fun x : P → Set.Icc (0 : ℝ) 1 => fun i j => ((x i : ℝ) - x j) ^ 2

/-- `D` is the `f2` matrix of a model with measurable frequencies in `[0,1]` on a probability
space. -/
def IsF2RealizableUnit {P : Type u} (D : P → P → ℝ) : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (p : P → Ω → ℝ), (∀ X, Measurable (p X)) ∧ (∀ X ω, p X ω ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ X Y, f2 μ p X Y = D X Y

/-- Two populations at `f2` distance `4`. -/
def twoF2 : Fin 2 → Fin 2 → ℝ := ![![0, 4], ![4, 0]]

/-- The squared distances of the corners `00, 10, 01, 11` of the unit square. -/
def squareF2 : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 1, 2], ![1, 0, 2, 1], ![1, 2, 0, 1], ![2, 1, 1, 0]]

/-- A symmetric zero-diagonal matrix that is not conditionally negative semidefinite
(`√9 > √1 + √1`). -/
def nonCndF2 : Fin 3 → Fin 3 → ℝ := ![![0, 1, 1], ![1, 0, 9], ![1, 9, 0]]


/-! ### Algebra of conditional negative definiteness -/

section Algebra

variable {P : Type*} [Fintype P]

private theorem sum_sum_mul_sq_sub (c a : P → ℝ) (hc : ∑ i, c i = 0) :
    ∑ i, ∑ j, c i * c j * (a i - a j) ^ 2 = -2 * (∑ i, c i * a i) ^ 2 := by
  have h : ∀ i j, c i * c j * (a i - a j) ^ 2 =
      c j * (c i * a i ^ 2) + c i * (c j * a j ^ 2) - 2 * ((c i * a i) * (c j * a j)) := by
    intro i j; ring
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ i, ∑ j, c j * (c i * a i ^ 2) = 0 := by
    simp only [← Finset.sum_mul, hc, zero_mul, Finset.sum_const_zero]
  have e2 : ∑ i, ∑ j, c i * (c j * a j ^ 2) = 0 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hc, zero_mul]
  have e3 : ∑ i, ∑ j, 2 * ((c i * a i) * (c j * a j)) = 2 * (∑ i, c i * a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [e1, e2, e3]; ring

private theorem sum_sum_mul_doubleCenter (D : P → P → ℝ) (x : P → ℝ) :
    ∑ i, ∑ j, x i * x j * doubleCenter D i j =
      -∑ i, ∑ j, (x i - (∑ k, x k) / Fintype.card P) * (x j - (∑ k, x k) / Fintype.card P) *
        D i j := by
  unfold doubleCenter
  set s := ∑ k, x k with hs
  set n := (Fintype.card P : ℝ)
  set g := ∑ k, ∑ l, D k l with hg
  set r : P → ℝ := fun i => ∑ k, D i k with hr
  set q : P → ℝ := fun j => ∑ k, D k j with hq
  have h1 : ∀ i j, x i * x j * ((∑ k, D i k) / n + (∑ k, D k j) / n - D i j - g / n ^ 2)
      = x j * (x i * r i / n) + x i * (x j * q j / n) - x i * x j * D i j
        - x i * x j * (g / n ^ 2) := by intro i j; simp only [hr, hq]; ring
  have h2 : ∀ i j, (x i - s / n) * (x j - s / n) * D i j = x i * x j * D i j
      - s / n * (x j * D i j) - s / n * (x i * D i j) + (s / n) ^ 2 * D i j := by intro i j; ring
  simp_rw [h1, h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ i, ∑ j, x j * (x i * r i / n) = s * ((∑ i, x i * r i) / n) := by
    simp only [← Finset.sum_mul, ← hs, Finset.sum_div, Finset.mul_sum]
  have e2 : ∑ i, ∑ j, x i * (x j * q j / n) = s * ((∑ j, x j * q j) / n) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, ← hs, Finset.sum_div]
  have e3 : ∑ i, ∑ j, x i * x j * (g / n ^ 2) = s ^ 2 * (g / n ^ 2) := by
    have hxx : (∑ i, ∑ j, x i * x j) = s ^ 2 := by rw [hs, sq, Finset.sum_mul_sum]
    simp only [← Finset.sum_mul, hxx]
  have e4 : ∑ i, ∑ j, s / n * (x j * D i j) = s / n * ∑ j, x j * q j := by
    rw [Finset.sum_comm]; simp only [← Finset.mul_sum, hq]
  have e5 : ∑ i, ∑ j, s / n * (x i * D i j) = s / n * ∑ i, x i * r i := by
    simp only [← Finset.mul_sum, hr]
  have e6 : ∑ i, ∑ j, (s / n) ^ 2 * D i j = (s / n) ^ 2 * g := by
    simp only [← Finset.mul_sum, hg, hr]
  rw [e1, e2, e3, e4, e5, e6]
  ring

theorem doubleCenter_comm {D : P → P → ℝ} (hsymm : ∀ i j, D i j = D j i) (i j : P) :
    doubleCenter D i j = doubleCenter D j i := by
  unfold doubleCenter
  have h1 : ∑ k, D i k = ∑ k, D k i := Finset.sum_congr rfl fun k _ => hsymm i k
  have h2 : ∑ k, D k j = ∑ k, D j k := Finset.sum_congr rfl fun k _ => hsymm k j
  rw [h1, h2, hsymm i j]; ring

theorem posSemidef_doubleCenter {D : P → P → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hcnd : IsCondNegSemidef D) : (Matrix.of fun i j => doubleCenter D i j / 2).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [doubleCenter_comm hsymm]
  · have hc : ∑ i, (x i - (∑ k, x k) / Fintype.card P) = 0 := by
      rcases isEmpty_or_nonempty P with hP | hP
      · simp
      · have hn : (Fintype.card P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel₀ _ hn, sub_self]
    have key := sum_sum_mul_doubleCenter D x
    have hq := hcnd _ hc
    have e : star x ⬝ᵥ ((Matrix.of fun i j => doubleCenter D i j / 2) *ᵥ x) =
        (∑ i, ∑ j, x i * x j * doubleCenter D i j) / 2 := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, key]
    linarith

theorem doubleCenter_reconstruct {D : P → P → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (i j : P) :
    doubleCenter D i i / 2 + doubleCenter D j j / 2 - 2 * (doubleCenter D i j / 2) = D i j := by
  unfold doubleCenter
  have h1 : ∑ k, D k i = ∑ k, D i k := Finset.sum_congr rfl fun k _ => hsymm k i
  have h2 : ∑ k, D k j = ∑ k, D j k := Finset.sum_congr rfl fun k _ => hsymm k j
  rw [h1, h2, hdiag i, hdiag j]; ring

private theorem exists_gram_of_posSemidef {K : Matrix P P ℝ} (hK : K.PosSemidef) :
    ∃ B : Matrix P P ℝ, ∀ i j, K i j = ∑ k, B k i * B k j := by
  classical
  set S := CFC.sqrt K
  have hS : S * S = K := CFC.sqrt_mul_sqrt_self K hK.nonneg
  have hSh : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian
  refine ⟨S, fun i j => ?_⟩
  rw [← hS, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hSh.apply k i
  simp only [star_trivial] at this
  rw [this]

theorem exists_sqDist_of_isCondNegSemidef {D : P → P → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (hcnd : IsCondNegSemidef D) :
    ∃ B : Matrix P P ℝ, ∀ i j, D i j = ∑ k, (B k i - B k j) ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := exists_gram_of_posSemidef (posSemidef_doubleCenter hsymm hcnd)
  refine ⟨B, fun i j => ?_⟩
  rw [← doubleCenter_reconstruct hsymm hdiag i j]
  have h := fun a b => hB a b
  simp only [Matrix.of_apply] at h
  rw [h i i, h j j, h i j, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem isCondNegSemidef_of_sqDist {D : P → P → ℝ} {ι : Type*} [Fintype ι] (B : ι → P → ℝ)
    (hD : ∀ i j, D i j = ∑ k, (B k i - B k j) ^ 2) : IsCondNegSemidef D := by
  intro c hc
  have : ∑ i, ∑ j, c i * c j * D i j = ∑ k : ι, ∑ i, ∑ j, c i * c j * (B k i - B k j) ^ 2 := by
    simp_rw [hD, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [this]
  refine Finset.sum_nonpos fun k _ => ?_
  rw [sum_sum_mul_sq_sub c (B k) hc]
  nlinarith [sq_nonneg (∑ i, c i * B k i)]

theorem isCondNegSemidef_iff_exists_sqDist {D : P → P → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) :
    IsCondNegSemidef D ↔ ∃ x : P → EuclideanSpace ℝ P, ∀ i j, D i j = ‖x i - x j‖ ^ 2 := by
  constructor
  · intro hcnd
    obtain ⟨B, hB⟩ := exists_sqDist_of_isCondNegSemidef hsymm hdiag hcnd
    refine ⟨fun i => WithLp.toLp 2 fun k => B k i, fun i j => ?_⟩
    rw [hB, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  · rintro ⟨x, hx⟩
    refine isCondNegSemidef_of_sqDist (fun k i => x i k) fun i j => ?_
    rw [hx, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]

end Algebra

/-! ### Square-integrable models: K is PSD and f2 is CND -/

section Models

variable {Ω P : Type*} {m : MeasurableSpace Ω} [Fintype P] {μ : Measure Ω}
  {p : P → Ω → ℝ}

/-- integral of a double sum. -/
private theorem sum_sum_integral {f : P → P → Ω → ℝ} (hf : ∀ i j, Integrable (f i j) μ) :
    ∑ i, ∑ j, ∫ ω, f i j ω ∂μ = ∫ ω, ∑ i, ∑ j, f i j ω ∂μ := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hf i j]

theorem f2_isCondNegSemidef (hp : ∀ X, MemLp (p X) 2 μ) : IsCondNegSemidef (f2 μ p) := by
  intro c hc
  have h : ∑ i, ∑ j, c i * c j * f2 μ p i j =
      ∫ ω, ∑ i, ∑ j, c i * c j * (p i ω - p j ω) ^ 2 ∂μ := by
    rw [← sum_sum_integral fun i j => (integrable_sub_sq hp i j).const_mul (c i * c j)]
    simp only [f2, integral_const_mul]
  rw [h]
  refine integral_nonpos fun ω => ?_
  rw [Pi.zero_apply, sum_sum_mul_sq_sub c (fun i => p i ω) hc]
  nlinarith [sq_nonneg (∑ i, c i * p i ω)]

private theorem memLp_sub_popMean (hp : ∀ X, MemLp (p X) 2 μ) (X : P) :
    MemLp (fun ω => p X ω - popMean p ω) 2 μ := by
  have h : MemLp (fun ω => ∑ Z, p Z ω) 2 μ := memLp_finsetSum Finset.univ fun Z _ => hp Z
  have e : (fun ω => popMean p ω) = fun ω => (Fintype.card P : ℝ)⁻¹ * ∑ Z, p Z ω := by
    funext ω
    rw [popMean, div_eq_inv_mul]
  have h2 : MemLp (fun ω => popMean p ω) 2 μ := by
    rw [e]
    exact h.const_mul _
  exact (hp X).sub h2

theorem posSemidef_centredCov (hp : ∀ X, MemLp (p X) 2 μ) :
    (Matrix.of (centredCov μ p)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact centredCov_comm j i
  · set q : P → Ω → ℝ := fun X ω => p X ω - popMean p ω
    have hq : ∀ i j, Integrable (fun ω => x i * x j * (q i ω * q j ω)) μ := fun i j =>
      ((memLp_sub_popMean hp i).integrable_mul (memLp_sub_popMean hp j)).const_mul _
    have e : star x ⬝ᵥ (Matrix.of (centredCov μ p) *ᵥ x) =
        ∫ ω, (∑ i, x i * q i ω) ^ 2 ∂μ := by
      have : ∀ ω, (∑ i, x i * q i ω) ^ 2 = ∑ i, ∑ j, x i * x j * (q i ω * q j ω) := fun ω => by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      simp_rw [this]
      rw [← sum_sum_integral hq]
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum,
        integral_const_mul, centredCov]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact integral_nonneg fun ω => sq_nonneg _

end Models

/-! ### Unconstrained models: realizable iff CND (Schoenberg) -/

theorem exists_driftModel {E P : Type u} [Fintype E] (w : P → E → ℝ) (len : E → ℝ)
    (hlen : ∀ e, 0 ≤ len e) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ E P), M.weight = w ∧ M.len = len := by
  classical
  let _ : MeasurableSpace (Option E) := ⊤
  have : DiscreteMeasurableSpace (Option E) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set N : ℝ := (Fintype.card (Option E) : ℝ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let μ : Measure (Option E) := ProbabilityTheory.uniformOn Set.univ
  have hμ : ∀ ω, μ.real {ω} = N⁻¹ := fun ω => by
    simp [μ, Measure.real, ProbabilityTheory.uniformOn_univ, N, ENNReal.toReal_inv]
    norm_cast
  let incr : E → Option E → ℝ := fun e ω => if ω = some e then Real.sqrt (N * len e) else 0
  refine ⟨Option E, ⊤, μ, inferInstance,
    { root := 0, incr := incr, len := len, weight := w,
      memLp_root := MemLp.of_discrete, memLp_incr := fun e => MemLp.of_discrete,
      inner_incr := fun e f hef => ?_, sq_incr := fun e => ?_ }, rfl, rfl⟩
  · have h0 : (fun ω => incr e ω * incr f ω) = 0 := by
      funext ω
      by_cases he : ω = some e
      · have hf : ω ≠ some f := by rw [he]; simpa using hef
        simp [incr, hf]
      · simp [incr, he]
    rw [h0]; simp
  · rw [integral_fintype Integrable.of_finite]
    simp only [hμ, incr, smul_eq_mul]
    rw [Finset.sum_eq_single (some e)]
    · simp only [ite_true]
      rw [Real.sq_sqrt (mul_nonneg (by positivity) (hlen e))]
      field_simp
    · intro b _ hb; simp [hb]
    · simp

theorem isF2Realizable_iff {P : Type u} [Fintype P] {D : P → P → ℝ} :
    IsF2Realizable D ↔ (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0) ∧ IsCondNegSemidef D := by
  constructor
  · rintro ⟨E, _, Ω, _, μ, _, M, hM⟩
    have hD : D = f2 μ M.freq := funext fun X => funext fun Y => (hM X Y).symm
    subst hD
    exact ⟨fun i j => f2_comm i j, fun i => f2_self i, f2_isCondNegSemidef M.memLp_freq⟩
  · rintro ⟨hsymm, hdiag, hcnd⟩
    obtain ⟨B, hB⟩ := exists_sqDist_of_isCondNegSemidef hsymm hdiag hcnd
    obtain ⟨Ω, _, μ, hμ, M, hw, hl⟩ :=
      exists_driftModel (E := P) (P := P) (fun X e => B e X) (fun _ => 1) fun _ => zero_le_one
    refine ⟨P, inferInstance, Ω, _, μ, hμ, M, fun X Y => ?_⟩
    rw [M.f2_freq, hw, hl, hB]
    simp

theorem f2_multivariateGaussian_of_posSemidef {P : Type*} [Fintype P] [DecidableEq P] {S : Matrix P P ℝ} (hS : S.PosSemidef) (X Y : P) :
    f2 (multivariateGaussian 0 S) (fun i x => x i) X Y = S X X + S Y Y - 2 * S X Y := by
  set v : EuclideanSpace ℝ P := EuclideanSpace.single X 1 - EuclideanSpace.single Y 1
  have hv : ∀ z : EuclideanSpace ℝ P, ⟪v, z⟫ = z X - z Y := fun z => by
    simp [v, inner_sub_left, EuclideanSpace.inner_single_left]
  have h := covarianceBilin_apply (μ := multivariateGaussian 0 S) IsGaussian.memLp_two_id v v
  rw [integral_id_multivariateGaussian', covarianceBilin_multivariateGaussian hS] at h
  simp only [sub_zero, hv] at h
  unfold f2
  simp only [← sq] at h
  rw [← h]
  have hsym := hS.isHermitian.apply X Y
  simp only [star_trivial] at hsym
  simp [v, dotProduct, mulVec, Finset.sum_sub_distrib, sub_mul, mul_sub]
  linarith

theorem f2_multivariateGaussian {P : Type*} [Fintype P] [DecidableEq P] {D : P → P → ℝ}
    (hsymm : ∀ i j, D i j = D j i) (hdiag : ∀ i, D i i = 0) (hcnd : IsCondNegSemidef D)
    (X Y : P) :
    f2 (multivariateGaussian 0 (Matrix.of fun i j => doubleCenter D i j / 2)) (fun i x => x i)
      X Y = D X Y := by
  rw [f2_multivariateGaussian_of_posSemidef (posSemidef_doubleCenter hsymm hcnd)]
  simp only [Matrix.of_apply]
  exact doubleCenter_reconstruct hsymm hdiag X Y

/-! ### Frequencies in [0,1] -/

section Unit

variable {P : Type u}

theorem isCompact_unitF2Points [Finite P] : IsCompact (unitF2Points P) :=
  isCompact_range (continuous_pi fun i => continuous_pi fun j => by fun_prop)

theorem closedConvexHull_unitF2Points [Finite P] :
    closedConvexHull ℝ (unitF2Points P) = convexHull ℝ (unitF2Points P) := by
  have := Fintype.ofFinite P
  rw [closedConvexHull_eq_closure_convexHull,
    (MathlibExt.Analysis.Convex.Straszewicz.IsCompact.convexHull_of_compact
      isCompact_unitF2Points).isClosed.closure_eq]

theorem mem_closedConvexHull_of_isF2RealizableUnit [Finite P] {D : P → P → ℝ}
    (hD : IsF2RealizableUnit D) : D ∈ closedConvexHull ℝ (unitF2Points P) := by
  have := Fintype.ofFinite P
  obtain ⟨Ω, _, μ, _, p, hpm, hp01, hf2⟩ := hD
  set F : Ω → P → P → ℝ := fun ω i j => (p i ω - p j ω) ^ 2
  have hFi : ∀ i j, Integrable (fun ω => F ω i j) μ := fun i j => by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun ω => ?_)
    have h1 := hp01 i ω
    have h2 := hp01 j ω
    simp only [Set.mem_Icc] at h1 h2
    simp only [F, Real.norm_eq_abs, abs_pow]
    rw [sq_abs]
    nlinarith
  have hF : Integrable F μ := Integrable.of_eval fun i => Integrable.of_eval fun j => hFi i j
  have hmem := Convex.integral_mem (μ := μ) convex_closedConvexHull isClosed_closedConvexHull
    (ae_of_all _ fun ω => subset_closedConvexHull
      (show F ω ∈ unitF2Points P from ⟨fun i => ⟨p i ω, hp01 i ω⟩, rfl⟩)) hF
  convert hmem using 1
  funext i j
  rw [eval_integral (fun i => Integrable.of_eval fun j => hFi i j),
    eval_integral (fun j => hFi i j), ← hf2]
  rfl

theorem isF2RealizableUnit_of_mem_convexHull {D : P → P → ℝ}
    (hD : D ∈ convexHull ℝ (unitF2Points P)) : IsF2RealizableUnit D := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hD⟩ := mem_convexHull_iff_exists_fintype.mp hD
  choose x hx using hz
  let _ : MeasurableSpace (ULift.{u} ι) := ⊤
  have : MeasurableSingletonClass (ULift.{u} ι) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let μ : Measure (ULift.{u} ι) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (ULift.up i)
  have hμ : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]⟩
  refine ⟨ULift.{u} ι, ⊤, μ, hμ, fun X ω => (x ω.down X : ℝ), fun X => ?_, fun X ω => (x ω.down X).2,
    fun X Y => ?_⟩
  · exact fun _ _ => MeasurableSpace.measurableSet_top
  · rw [f2, integral_finsetSum_measure fun i _ => by
      have := Measure.smul_finite (Measure.dirac (ULift.up.{u} i)) (ENNReal.ofReal_ne_top (r := w i))
      exact Integrable.of_finite]
    simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
    rw [← hD]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hx i]

theorem isF2RealizableUnit_iff [Finite P] {D : P → P → ℝ} :
    IsF2RealizableUnit D ↔ D ∈ closedConvexHull ℝ (unitF2Points P) :=
  ⟨mem_closedConvexHull_of_isF2RealizableUnit, fun h =>
    isF2RealizableUnit_of_mem_convexHull (closedConvexHull_unitF2Points (P := P) ▸ h)⟩

theorem f2_le_one {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : P → Ω → ℝ} (hp01 : ∀ X ω, p X ω ∈ Set.Icc (0 : ℝ) 1)
    (X Y : P) : f2 μ p X Y ≤ 1 := by
  have h : ∀ ω, (p X ω - p Y ω) ^ 2 ≤ 1 := fun ω => by
    have h1 := hp01 X ω
    have h2 := hp01 Y ω
    simp only [Set.mem_Icc] at h1 h2
    nlinarith
  calc f2 μ p X Y ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const 1)
          (ae_of_all _ h)
    _ = 1 := by simp

theorem isCondNegSemidef_twoF2 : IsCondNegSemidef twoF2 := by
  intro c hc
  simp only [Fin.sum_univ_two, twoF2, Matrix.cons_val_zero, Matrix.cons_val_one] at hc ⊢
  have : c 1 = -c 0 := by linarith
  rw [this]
  nlinarith [sq_nonneg (c 0)]

theorem isF2Realizable_twoF2 : IsF2Realizable twoF2 :=
  isF2Realizable_iff.mpr ⟨by intro i j; fin_cases i <;> fin_cases j <;> simp [twoF2],
    by intro i; fin_cases i <;> simp [twoF2], isCondNegSemidef_twoF2⟩

theorem not_isF2RealizableUnit_twoF2 : ¬ IsF2RealizableUnit twoF2 := by
  rintro ⟨Ω, _, μ, _, p, -, hp01, hf2⟩
  have h := f2_le_one (μ := μ) hp01 0 1
  rw [hf2] at h
  norm_num [twoF2] at h

end Unit

/-! ### Three populations: admixture-graph realization -/

/-- The three-population admixture weights and lengths realizing a symmetric
zero-diagonal conditionally negative semidefinite matrix in which `D 0 1` is at least
the other two off-diagonal entries: some `0 ≤ α ≤ 1` and `a, b, c ≥ 0` with `a + b = D 0 1`
give `D X Y = ∑ e, (admixWeight α X e - admixWeight α Y e) ^ 2 * ![a, b, c] e`, with
`1 - α = (D 0 1 + D 0 2 - D 1 2) / (2 * D 0 1)` and `c = D 0 2 - (1 - α) ^ 2 * D 0 1` when
`D 0 1 > 0`. For a general symmetric zero-diagonal conditionally negative semidefinite
matrix, relabel the populations so that the largest off-diagonal entry is in the `0 1`
position before applying this theorem. -/
theorem exists_admix_three {D : Fin 3 → Fin 3 → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (hcnd : IsCondNegSemidef D) (h02 : D 0 2 ≤ D 0 1)
    (h12 : D 1 2 ≤ D 0 1) :
    ∃ α a b c : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b = D 0 1 ∧
      (0 < D 0 1 → 1 - α = (D 0 1 + D 0 2 - D 1 2) / (2 * D 0 1) ∧
        c = D 0 2 - (1 - α) ^ 2 * D 0 1) ∧
      ∀ X Y, ∑ e, (admixWeight α X e - admixWeight α Y e) ^ 2 * ![a, b, c] e = D X Y := by
  have hQ : ∀ c0 c1 c2 : ℝ, c0 + c1 + c2 = 0 →
      c0 * c1 * D 0 1 + c0 * c2 * D 0 2 + c1 * c2 * D 1 2 ≤ 0 := fun c0 c1 c2 hc => by
    have h := hcnd ![c0, c1, c2] (by simpa [Fin.sum_univ_three] using hc)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hdiag] at h
    rw [hsymm 1 0, hsymm 2 0, hsymm 2 1] at h
    linarith
  have hu : 0 ≤ D 0 2 := by nlinarith [hQ 1 0 (-1) (by ring)]
  have hv : 0 ≤ D 1 2 := by nlinarith [hQ 0 1 (-1) (by ring)]
  have hD10 := hsymm 1 0
  have hD20 := hsymm 2 0
  have hD21 := hsymm 2 1
  rcases (show (0 : ℝ) ≤ D 0 1 by linarith).eq_or_lt with hd | hd
  · refine ⟨1 / 2, 0, 0, 0, by norm_num, by norm_num, le_rfl, le_rfl, le_rfl, by linarith,
      fun h => absurd h (by rw [← hd]; exact lt_irrefl 0), fun X Y => ?_⟩
    have hu0 : D 0 2 = 0 := by linarith
    have hv0 : D 1 2 = 0 := by linarith
    fin_cases X <;> fin_cases Y <;>
      simp [admixWeight, starWeight, Fin.sum_univ_three, hdiag] <;> linarith
  · set d := D 0 1
    set t := (d + D 0 2 - D 1 2) / (2 * d) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have htd : t * (2 * d) = d + D 0 2 - D 1 2 := div_mul_cancel₀ _ (by positivity)
    have hc : 0 ≤ D 0 2 - t ^ 2 * d := by
      have h := hQ (-(1 - t)) (-t) 1 (by ring)
      nlinarith
    refine ⟨1 - t, d, 0, D 0 2 - t ^ 2 * d, by linarith, by linarith, hd.le, le_rfl, hc,
      by ring, fun _ => ⟨by rw [ht]; ring, by ring⟩, fun X Y => ?_⟩
    fin_cases X <;> fin_cases Y <;>
      simp [admixWeight, starWeight, Fin.sum_univ_three, hdiag] <;> nlinarith

/-- The drift-model form of `exists_admix_three`, under the same symmetry,
zero-diagonal, conditional negative semidefiniteness, and `D 0 1`-dominance
hypotheses. -/
theorem exists_driftModel_admix_three {D : Fin 3 → Fin 3 → ℝ} (hsymm : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (hcnd : IsCondNegSemidef D) (h02 : D 0 2 ≤ D 0 1)
    (h12 : D 1 2 ≤ D 0 1) :
    ∃ α a b c : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b = D 0 1 ∧
      (0 < D 0 1 → 1 - α = (D 0 1 + D 0 2 - D 1 2) / (2 * D 0 1) ∧
        c = D 0 2 - (1 - α) ^ 2 * D 0 1) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (M : DriftModel μ (Fin 3) (Fin 3)), M.weight = admixWeight α ∧ M.len = ![a, b, c] ∧
          ∀ X Y, f2 μ M.freq X Y = D X Y := by
  obtain ⟨α, a, b, c, h0, h1, ha, hb, hc, hab, hform, hf⟩ :=
    exists_admix_three hsymm hdiag hcnd h02 h12
  have hlen : ∀ e, 0 ≤ (![a, b, c] : Fin 3 → ℝ) e := by
    intro e; fin_cases e <;> simpa
  obtain ⟨Ω, _, μ, hμ, M, hw, hl⟩ := exists_driftModel (P := Fin 3) (admixWeight α) ![a, b, c] hlen
  exact ⟨α, a, b, c, h0, h1, ha, hb, hc, hab, hform, Ω, _, μ, hμ, M, hw, hl, fun X Y => by
    rw [M.f2_freq, hw, hl, hf]⟩

/-! ### Examples -/


theorem isF2Realizable_squareF2 : IsF2Realizable squareF2 := by
  obtain ⟨Ω, _, μ, hμ, M, hw, hl⟩ := exists_driftModel (E := Fin 2) (P := Fin 4)
    ![![0, 0], ![1, 0], ![0, 1], ![1, 1]] (fun _ => 1) fun _ => zero_le_one
  refine ⟨Fin 2, inferInstance, Ω, _, μ, hμ, M, fun X Y => ?_⟩
  rw [M.f2_freq, hw, hl]
  fin_cases X <;> fin_cases Y <;> simp [squareF2, Fin.sum_univ_two] <;> norm_num

theorem isCondNegSemidef_squareF2 : IsCondNegSemidef squareF2 :=
  (isF2Realizable_iff.mp isF2Realizable_squareF2).2.2

theorem not_fourPointCondition_squareF2 : ¬ FourPointCondition squareF2 := by
  intro h
  have := h 0 3 1 2
  norm_num [squareF2] at this

theorem not_isTreeMetric_squareF2 : ¬ IsTreeMetric squareF2 := fun h =>
  not_fourPointCondition_squareF2 h.fourPointCondition

theorem not_isCondNegSemidef_nonCndF2 : ¬ IsCondNegSemidef nonCndF2 := by
  intro h
  have := h ![-2, 1, 1] (by simp [Fin.sum_univ_three]; norm_num)
  simp [nonCndF2, Fin.sum_univ_three] at this
  norm_num at this

theorem not_isF2Realizable_nonCndF2 : ¬ IsF2Realizable nonCndF2 := fun h =>
  not_isCondNegSemidef_nonCndF2 (isF2Realizable_iff.mp h).2.2

end MathlibExt.Biology.PopulationGenetics.Admixture
