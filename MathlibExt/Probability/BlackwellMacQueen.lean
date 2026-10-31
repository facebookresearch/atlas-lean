/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
public import MathlibExt.Probability.DirichletProcess

/-!
# The Blackwell–MacQueen urn

The **Blackwell–MacQueen urn** (Blackwell–MacQueen 1973) with parameter `α > 0` and base
probability measure `H` draws `X₀ ∼ H` and, given `X₀, …, X_{n-1}`, draws `X_n` from the
predictive law `(α H + ∑_{i<n} δ_{Xᵢ}) / (α + n)` (`polyaUrnPredictive`). Classically it is
the law of observations `X₀, X₁, … | G` i.i.d. `G` from a Dirichlet process `G ∼ DP(α, H)`
(Blackwell–MacQueen 1973); here this link is proved for at most two observations.

## Main results

* `blackwellMacQueen α H n`: the joint law of the first `n` draws, built by `Measure.bind`;
  `blackwellMacQueen_succ_pi` is the predictive rule
  `P(X₀ ∈ A₀, …, X_n ∈ A_n) = ∫_{A₀ × ⋯ × A_{n-1}} P(X_n ∈ A_n | x) dP(x)`.
* `map_perm_blackwellMacQueen`: **exchangeability** — relabeling the draws by any permutation
  does not change their joint law (Blackwell–MacQueen 1973).
* `blackwellMacQueen_tiePartition`: for an atomless base measure, the partition of the indices
  into groups of equal draws (`tiePartition`) follows the **Chinese restaurant process**:
  `P(π) = α^{|π|} ∏_{B ∈ π} (|B| - 1)! / α^{(n)}` (`crpProb`; Pitman 2006, §3.1).
* `lintegral_dirichletProcess_prod_of_le_two`: for at most two draws, the moments of the
  Dirichlet process are the urn probabilities, `E[∏_{i<n} G(Aᵢ)] = P(X₀ ∈ A₀, …)` for `n ≤ 2`.

Along the way: `polyaUrnPredictive_comp_perm` (the predictive law is symmetric in the previous
draws), `measurable_polyaUrnPredictive`, `isProbabilityMeasure_blackwellMacQueen`, and for the
tie partition `tiePartition_eq_iff`, `measurableSet_tiePartition_eq`,
`comap_castSucc_tiePartition_snoc`, `tiePartition_snoc_eq_seat_none_iff` and
`tiePartition_snoc_eq_seat_some_iff` (a new draw opens a new table iff it differs from every
earlier draw, and joins table `B` iff it equals the draws in `B`).

The proof of exchangeability reduces, by `Equiv.Perm.mclosure_swap_castSucc_succ`, to adjacent
transpositions: a transposition of two earlier draws is handled by induction and the symmetry
of the predictive law, and the transposition of the last two draws by the symmetry in `(B, C)`
of the two-step predictive probability
`[(α H(B) + c_B)(α H(C) + c_C) + α H(B ∩ C) + c_{B ∩ C}] / ((α + n)(α + n + 1))`, with
`c_S = #{i < n | xᵢ ∈ S}`.

## Not covered

The moment identity for `n ≥ 3` draws, the Dirichlet finite-dimensional marginals of the
stick-breaking process (Sethuraman 1994, Theorem 3.4), and Ferguson's posterior conjugacy are
stated in `WantedExt/Probability/DirichletProcessWanted.lean`. The tie law assumes an atomless
base measure: with atoms, distinct tables can receive equal values (for `H = δ_b` all draws are
equal).

## References

* D. Blackwell, J. B. MacQueen, *Ferguson distributions via Pólya urn schemes*, Ann. Statist. 1
  (1973), 353–355.
* T. S. Ferguson, *A Bayesian analysis of some nonparametric problems*, Ann. Statist. 1 (1973),
  209–230.
* J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875 (2006), ch. 3.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The predictive law depends measurably on the previous draws. -/
theorem measurable_polyaUrnPredictive (α : ℝ) (H : Measure X) (n : ℕ) :
    Measurable fun xs : Fin n → X ↦ polyaUrnPredictive α H xs := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [polyaUrnPredictive, Measure.smul_apply, Measure.add_apply, Measure.finsetSum_apply,
    smul_eq_mul]
  refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun i _ ↦ ?_))
  exact (Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp (measurable_pi_apply i))

/-- The predictive probability of a fixed measurable set depends measurably on the previous
draws. -/
private theorem measurable_polyaUrnPredictive_apply (α : ℝ) (H : Measure X) (n : ℕ) {A : Set X}
    (hA : MeasurableSet A) : Measurable fun xs : Fin n → X ↦ polyaUrnPredictive α H xs A :=
  (Measure.measurable_coe hA).comp (measurable_polyaUrnPredictive α H n)

/-- Appending a coordinate is measurable. -/
private theorem measurable_snoc_prod (n : ℕ) :
    Measurable fun p : (Fin n → X) × X ↦ Fin.snoc (α := fun _ ↦ X) p.1 p.2 := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

/-- Appending a coordinate to fixed `xs` is measurable. -/
private theorem measurable_snoc {n : ℕ} (xs : Fin n → X) :
    Measurable fun x : X ↦ Fin.snoc (α := fun _ ↦ X) xs x :=
  (measurable_snoc_prod n).comp measurable_prodMk_left

/-- The urn kernel is measurable. -/
private theorem measurable_map_snoc (α : ℝ) (H : Measure X) [SFinite H] (n : ℕ) :
    Measurable fun xs : Fin n → X ↦
      (polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x := by
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  have hT := measurable_snoc_prod (X := X) n hS
  have h : ∀ xs : Fin n → X,
      ((polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x) S =
        (ENNReal.ofReal (α + n))⁻¹ * (ENNReal.ofReal α * H (Prod.mk xs ⁻¹'
          ((fun p : (Fin n → X) × X ↦ Fin.snoc (α := fun _ ↦ X) p.1 p.2) ⁻¹' S)) +
          ∑ i, ((fun p : (Fin n → X) × X ↦ Fin.snoc (α := fun _ ↦ X) p.1 p.2) ⁻¹' S).indicator
            1 (xs, xs i)) := fun xs ↦ by
    rw [Measure.map_apply (measurable_snoc xs) hS]
    simp only [polyaUrnPredictive, Measure.smul_apply, Measure.add_apply,
      Measure.finsetSum_apply, smul_eq_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Measure.dirac_apply' _ (measurable_snoc xs hS)]
    rfl
  simp_rw [h]
  refine measurable_const.mul (((measurable_measure_prodMk_left hT).const_mul _).add
    (Finset.measurable_sum _ fun i _ ↦ ?_))
  exact (measurable_one.indicator hT).comp (measurable_id.prodMk (measurable_pi_apply i))

/-- The **Blackwell–MacQueen urn** with parameter `α` and base measure `H`: the joint law of the
first `n` draws, where draw `n` has law `polyaUrnPredictive α H xs` given the previous draws
`xs` (Blackwell–MacQueen 1973). -/
noncomputable def blackwellMacQueen (α : ℝ) (H : Measure X) : (n : ℕ) → Measure (Fin n → X)
  | 0 => Measure.dirac fun i ↦ i.elim0
  | n + 1 => (blackwellMacQueen α H n).bind fun xs ↦
      (polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x

/-- The urn law is a probability measure. -/
theorem isProbabilityMeasure_blackwellMacQueen {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (n : ℕ) : IsProbabilityMeasure (blackwellMacQueen α H n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    constructor
    have hk : Measurable fun xs : Fin n → X ↦
        (polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x :=
      measurable_map_snoc α H n
    rw [blackwellMacQueen, Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
    have : ∀ xs : Fin n → X,
        ((polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x) Set.univ = 1 :=
      fun xs ↦ by
        have := isProbabilityMeasure_polyaUrnPredictive hα (H := H) xs
        rw [Measure.map_apply (measurable_snoc xs) MeasurableSet.univ, Set.preimage_univ,
          measure_univ]
    simp_rw [this, lintegral_const, measure_univ, one_mul]

/-- **The predictive rule of the urn**: `P(X₀ ∈ A₀, …, X_n ∈ A_n)` is the integral over
`A₀ × ⋯ × A_{n-1}` of the predictive probability `(α H(A_n) + #{i < n | xᵢ ∈ A_n}) / (α + n)`. -/
theorem blackwellMacQueen_succ_pi (α : ℝ) (H : Measure X) [SFinite H] {n : ℕ}
    (A : Fin (n + 1) → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    blackwellMacQueen α H (n + 1) (Set.univ.pi A) =
      ∫⁻ xs in Set.univ.pi fun i ↦ A (Fin.castSucc i),
        polyaUrnPredictive α H xs (A (Fin.last n)) ∂blackwellMacQueen α H n := by
  rw [blackwellMacQueen, Measure.bind_apply (MeasurableSet.univ_pi hA)
      (measurable_map_snoc α H n).aemeasurable,
    ← lintegral_indicator (f := fun xs ↦ polyaUrnPredictive α H xs (A (Fin.last n)))
      (MeasurableSet.univ_pi fun i ↦ hA i.castSucc)]
  refine lintegral_congr fun xs ↦ ?_
  rw [Measure.map_apply (measurable_snoc xs) (MeasurableSet.univ_pi hA)]
  by_cases hxs : xs ∈ Set.univ.pi fun i ↦ A (Fin.castSucc i)
  · rw [Set.indicator_of_mem hxs]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_succ', Fin.snoc_castSucc,
      Fin.snoc_last]
    simp only [Set.mem_univ_pi] at hxs
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxs, h⟩⟩
  · rw [Set.indicator_of_notMem hxs]
    convert measure_empty (μ := polyaUrnPredictive α H xs)
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_succ', Fin.snoc_castSucc,
      Set.mem_empty_iff_false, iff_false, not_and]
    simp only [Set.mem_univ_pi] at hxs
    exact fun h ↦ absurd h hxs

/-- The predictive law does not depend on the order of the previous draws. -/
theorem polyaUrnPredictive_comp_perm (α : ℝ) (H : Measure X) {n : ℕ} (xs : Fin n → X)
    (σ : Equiv.Perm (Fin n)) : polyaUrnPredictive α H (xs ∘ σ) = polyaUrnPredictive α H xs := by
  simp only [polyaUrnPredictive, Function.comp_apply]
  congr 2
  exact Equiv.sum_comp σ fun i ↦ Measure.dirac (xs i)

/-- The predictive law after appending a draw `x`. -/
private theorem polyaUrnPredictive_snoc (α : ℝ) (H : Measure X) {n : ℕ} (xs : Fin n → X)
    (x : X) : polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) =
      (ENNReal.ofReal (α + (n + 1)))⁻¹ •
        (ENNReal.ofReal α • H + ∑ i, Measure.dirac (xs i) + Measure.dirac x) := by
  simp only [polyaUrnPredictive, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Nat.cast_succ, add_assoc]

private theorem measurable_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable fun xs : Fin n → X ↦ xs ∘ σ :=
  measurable_pi_iff.2 fun i ↦ measurable_pi_apply (σ i)

/-- The permutation of `Fin (n + 1)` acting as `σ` on the first `n` indices and fixing the last
one. -/
private def permSnoc {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquivLast.trans (Equiv.optionCongr σ)).trans finSuccEquivLast.symm

omit [MeasurableSpace X] in
private theorem snoc_comp_permSnoc {n : ℕ} (xs : Fin n → X) (x : X) (σ : Equiv.Perm (Fin n)) :
    Fin.snoc (α := fun _ ↦ X) (xs ∘ σ) x = Fin.snoc (α := fun _ ↦ X) xs x ∘ permSnoc σ := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [permSnoc, finSuccEquivLast_last]
  | cast i => simp [permSnoc, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]

/-- Permuting the first `n` draws and keeping the last one in place preserves the urn law. -/
private theorem map_permSnoc_blackwellMacQueen (α : ℝ) (H : Measure X) [IsFiniteMeasure H]
    {n : ℕ} (ih : ∀ σ : Equiv.Perm (Fin n),
      (blackwellMacQueen α H n).map (fun xs ↦ xs ∘ σ) = blackwellMacQueen α H n)
    (σ : Equiv.Perm (Fin n)) :
    (blackwellMacQueen α H (n + 1)).map (fun xs ↦ xs ∘ permSnoc σ) =
      blackwellMacQueen α H (n + 1) := by
  have hk := measurable_map_snoc α H n
  rw [blackwellMacQueen, Measure.map_bind hk.aemeasurable (measurable_comp_perm _).aemeasurable]
  have h : ∀ xs : Fin n → X,
      ((polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x).map
          (fun ys ↦ ys ∘ permSnoc σ) =
        (polyaUrnPredictive α H (xs ∘ σ)).map
          fun x ↦ Fin.snoc (α := fun _ ↦ X) (xs ∘ σ) x := by
    intro xs
    rw [Measure.map_map (measurable_comp_perm _) (measurable_snoc xs),
      polyaUrnPredictive_comp_perm]
    congr 1
    funext x
    exact (snoc_comp_permSnoc xs x σ).symm
  simp_rw [h]
  conv_rhs => rw [← ih σ]
  rw [Measure.bind_map (measurable_comp_perm σ).aemeasurable hk.aemeasurable]

/-- The two-step predictive integral `∫_B P(X_{n+1} ∈ C | xs, x) dP(x | xs)` is symmetric in
`B` and `C`. -/
private theorem setLIntegral_polyaUrnPredictive_snoc_comm (α : ℝ) (H : Measure X) {n : ℕ}
    (xs : Fin n → X) {B C : Set X} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    ∫⁻ x in B, polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) C
        ∂polyaUrnPredictive α H xs =
      ∫⁻ x in C, polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) B
        ∂polyaUrnPredictive α H xs := by
  set M : Measure X := ENNReal.ofReal α • H + ∑ i, Measure.dirac (xs i)
  have key : ∀ {B C : Set X}, MeasurableSet B → MeasurableSet C →
      ∫⁻ x in B, polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) C
        ∂polyaUrnPredictive α H xs =
      (ENNReal.ofReal (α + n))⁻¹ * ((ENNReal.ofReal (α + (n + 1)))⁻¹ *
        (M C * M B + M (C ∩ B))) := by
    intro B C hB hC
    have hpt : ∀ x, polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) C =
        (ENNReal.ofReal (α + (n + 1)))⁻¹ * (M C + C.indicator 1 x) := fun x ↦ by
      rw [polyaUrnPredictive_snoc, Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply' _ hC, smul_eq_mul]
    simp_rw [hpt]
    rw [show polyaUrnPredictive α H xs = (ENNReal.ofReal (α + n))⁻¹ • M from rfl,
      Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    congr 1
    rw [lintegral_const_mul (f := fun x ↦ M C + C.indicator 1 x) _
        (measurable_const.add (measurable_one.indicator hC)),
      lintegral_add_left measurable_const, setLIntegral_const, lintegral_indicator_one hC,
      Measure.restrict_apply hC]
  rw [key hB hC, key hC hB, mul_comm (M C), Set.inter_comm]

omit [MeasurableSpace X] in
private theorem snoc_mem_pi_iff {n : ℕ} (xs : Fin n → X) (x : X) (A : Fin (n + 1) → Set X) :
    Fin.snoc (α := fun _ ↦ X) xs x ∈ Set.univ.pi A ↔
      xs ∈ (Set.univ.pi fun i ↦ A (Fin.castSucc i)) ∧ x ∈ A (Fin.last n) := by
  simp only [Set.mem_univ_pi, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

/-- The probability of a box for `n + 2` draws, as an integral over the first `n` draws of the
two-step predictive integral. -/
private theorem blackwellMacQueen_add_two_pi (α : ℝ) (H : Measure X) [SFinite H] {n : ℕ}
    (A : Fin (n + 2) → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    blackwellMacQueen α H (n + 2) (Set.univ.pi A) =
      ∫⁻ xs in Set.univ.pi fun i ↦ A (Fin.castSucc (Fin.castSucc i)),
        ∫⁻ x in A (Fin.castSucc (Fin.last n)),
          polyaUrnPredictive α H (Fin.snoc (α := fun _ ↦ X) xs x) (A (Fin.last (n + 1)))
            ∂polyaUrnPredictive α H xs ∂blackwellMacQueen α H n := by
  have hk := measurable_map_snoc α H n
  have hpi : MeasurableSet (Set.univ.pi fun i : Fin (n + 1) ↦ A (Fin.castSucc i)) :=
    MeasurableSet.univ_pi fun i ↦ hA _
  have hpi' : MeasurableSet (Set.univ.pi fun i : Fin n ↦ A (Fin.castSucc (Fin.castSucc i))) :=
    MeasurableSet.univ_pi fun i ↦ hA _
  have hf := measurable_polyaUrnPredictive_apply α H (n + 1) (hA (Fin.last (n + 1)))
  rw [blackwellMacQueen_succ_pi α H A hA, ← lintegral_indicator hpi, ← lintegral_indicator hpi',
    show blackwellMacQueen α H (n + 1) = (blackwellMacQueen α H n).bind fun xs ↦
      (polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x from rfl,
    Measure.lintegral_bind hk.aemeasurable (hf.indicator hpi).aemeasurable]
  refine lintegral_congr fun xs ↦ ?_
  rw [lintegral_map (hf.indicator hpi) (measurable_snoc xs)]
  by_cases hxs : xs ∈ Set.univ.pi fun i ↦ A (Fin.castSucc (Fin.castSucc i))
  · rw [Set.indicator_of_mem hxs, ← lintegral_indicator (hA _)]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ A (Fin.castSucc (Fin.last n))
    · rw [Set.indicator_of_mem ((snoc_mem_pi_iff xs x _).2 ⟨hxs, hx⟩), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h ↦ hx ((snoc_mem_pi_iff xs x _).1 h).2),
        Set.indicator_of_notMem hx]
  · rw [Set.indicator_of_notMem hxs]
    refine (lintegral_congr fun x ↦ ?_).trans (lintegral_zero)
    rw [Set.indicator_of_notMem (fun h ↦ hxs ((snoc_mem_pi_iff xs x _).1 h).1)]

/-- Swapping the last two draws preserves the urn law. -/
private theorem map_swap_last_blackwellMacQueen {α : ℝ} (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (n : ℕ) :
    (blackwellMacQueen α H (n + 2)).map
        (fun xs ↦ xs ∘ Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))) =
      blackwellMacQueen α H (n + 2) := by
  set τ := Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))
  have := isProbabilityMeasure_blackwellMacQueen hα H (n + 2)
  have : IsProbabilityMeasure ((blackwellMacQueen α H (n + 2)).map fun xs ↦ xs ∘ τ) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_comp_perm τ).aemeasurable).2 inferInstance
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ (by simp)
  rintro _ ⟨A, hA, rfl⟩
  have hA' : ∀ i, MeasurableSet (A i) := fun i ↦ hA i (Set.mem_univ i)
  have hpre : (fun xs : Fin (n + 2) → X ↦ xs ∘ τ) ⁻¹' Set.univ.pi A =
      Set.univ.pi fun j ↦ A (τ j) := by
    ext ys
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h j
      simpa [τ] using h (τ j)
    · intro h i
      simpa [τ] using h (τ i)
  rw [Measure.map_apply (measurable_comp_perm τ) (MeasurableSet.univ_pi hA'), hpre,
    blackwellMacQueen_add_two_pi α H _ fun j ↦ hA' (τ j), blackwellMacQueen_add_two_pi α H _ hA']
  have h1 : ∀ i : Fin n, τ (Fin.castSucc (Fin.castSucc i)) = Fin.castSucc (Fin.castSucc i) :=
    fun i ↦ Equiv.swap_apply_of_ne_of_ne
      (by simp) (Fin.castSucc_lt_last _).ne
  have h2 : τ (Fin.castSucc (Fin.last n)) = Fin.last (n + 1) := Equiv.swap_apply_left _ _
  have h3 : τ (Fin.last (n + 1)) = Fin.castSucc (Fin.last n) := Equiv.swap_apply_right _ _
  simp only [h1, h2, h3]
  refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun i ↦ hA' _) fun xs _ ↦ ?_
  exact setLIntegral_polyaUrnPredictive_snoc_comm α H xs (hA' _) (hA' _)

omit [MeasurableSpace X] in
private theorem permSnoc_swap {m : ℕ} (j : Fin m) :
    permSnoc (Equiv.swap (Fin.castSucc j) j.succ) =
      Equiv.swap (Fin.castSucc (Fin.castSucc j)) (Fin.castSucc j).succ := by
  rw [Fin.succ_castSucc]
  ext k
  induction k using Fin.lastCases with
  | last =>
    simp only [permSnoc, Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
      Option.map_none, finSuccEquivLast_symm_none]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne' (Fin.castSucc_lt_last _).ne']
  | cast k =>
    simp only [permSnoc, Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionCongr_apply,
      Option.map_some, finSuccEquivLast_symm_some]
    rw [(Fin.castSucc_injective _).swap_apply]

/-- **Exchangeability of the Blackwell–MacQueen urn** (Blackwell–MacQueen 1973): relabeling the
draws by a permutation does not change their joint law. -/
theorem map_perm_blackwellMacQueen (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (blackwellMacQueen α H n).map (fun xs ↦ xs ∘ σ) = blackwellMacQueen α H n := by
  induction n with
  | zero =>
    rw [Subsingleton.elim σ 1]
    exact Measure.map_id
  | succ n ih =>
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n ↦ Equiv.swap (Fin.castSucc i) i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | one => exact Measure.map_id
    | mul σ τ _ _ hσ hτ =>
      rw [Equiv.Perm.coe_mul, show (fun xs : Fin (n + 1) → X ↦ xs ∘ (⇑σ ∘ ⇑τ)) =
          (fun xs ↦ xs ∘ τ) ∘ (fun xs ↦ xs ∘ σ) from rfl,
        ← Measure.map_map (measurable_comp_perm τ) (measurable_comp_perm σ), hσ, hτ]
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      cases n with
      | zero => exact i.elim0
      | succ m =>
        induction i using Fin.lastCases with
        | last => exact map_swap_last_blackwellMacQueen hα H m
        | cast j =>
          dsimp only
          rw [← permSnoc_swap]
          exact map_permSnoc_blackwellMacQueen α H ih _

omit [MeasurableSpace X] in
/-- The partition of the indices `{0, …, n-1}` into groups of equal entries of `xs`. -/
noncomputable def tiePartition {n : ℕ} (xs : Fin n → X) : Finpartition (univ : Finset (Fin n)) :=
  haveI := Classical.decRel (Setoid.ker xs).r
  Finpartition.ofSetoid (Setoid.ker xs)

omit [MeasurableSpace X] in
/-- Two indices lie in the same block of `tiePartition xs` iff the entries agree. -/
theorem mem_part_tiePartition {n : ℕ} (xs : Fin n → X) (i j : Fin n) :
    j ∈ (tiePartition xs).part i ↔ xs i = xs j := by
  classical
  unfold tiePartition
  convert Finpartition.mem_part_ofSetoid_iff_rel (s := Setoid.ker xs) (a := i) (b := j)

omit [MeasurableSpace X] in
private theorem finpartition_ext_part {n : ℕ} {P Q : Finpartition (univ : Finset (Fin n))}
    (h : ∀ i j, j ∈ P.part i ↔ j ∈ Q.part i) : P = Q := by
  have key : ∀ {P Q : Finpartition (univ : Finset (Fin n))},
      (∀ i j, j ∈ P.part i ↔ j ∈ Q.part i) → ∀ B ∈ P.parts, B ∈ Q.parts := by
    intro P Q h B hB
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    have hPi : P.part i = B := P.part_eq_of_mem hB hi
    have : Q.part i = B := by
      rw [← hPi]
      ext j
      exact (h i j).symm
    rw [← this]
    exact Q.part_mem.2 (mem_univ i)
  exact Finpartition.ext (Finset.ext fun B ↦
    ⟨key h B, key (fun i j ↦ (h i j).symm) B⟩)

omit [MeasurableSpace X] in
/-- `tiePartition xs = π` iff equal entries are exactly the pairs in a common block of `π`. -/
theorem tiePartition_eq_iff {n : ℕ} (xs : Fin n → X) (π : Finpartition (univ : Finset (Fin n))) :
    tiePartition xs = π ↔ ∀ i j, (xs i = xs j ↔ j ∈ π.part i) := by
  constructor
  · rintro rfl i j
    exact (mem_part_tiePartition xs i j).symm
  · intro h
    exact finpartition_ext_part fun i j ↦ (mem_part_tiePartition xs i j).trans (h i j)

omit [MeasurableSpace X] in
private theorem part_comap {n m : ℕ} (f : Fin n → Fin m) (P : Finpartition (univ : Finset (Fin m)))
    (i j : Fin n) : j ∈ (P.comap f).part i ↔ f j ∈ P.part (f i) := by
  have hmem : (univ.filter fun a ↦ f a ∈ P.part (f i)) ∈ (P.comap f).parts :=
    Finpartition.mem_comap_parts.2 ⟨⟨i, by simp [P.mem_part_self.2 (mem_univ _)]⟩,
      P.part (f i), P.part_mem.2 (mem_univ _), rfl⟩
  rw [(P.comap f).part_eq_of_mem hmem (by simp [P.mem_part_self.2 (mem_univ _)])]
  simp

omit [MeasurableSpace X] in
/-- Forgetting the last draw restricts the tie partition to the earlier draws. -/
theorem comap_castSucc_tiePartition_snoc {n : ℕ} (xs : Fin n → X) (x : X) :
    (tiePartition (Fin.snoc (α := fun _ ↦ X) xs x)).comap Fin.castSucc = tiePartition xs := by
  refine finpartition_ext_part fun i j ↦ ?_
  rw [part_comap, mem_part_tiePartition, mem_part_tiePartition, Fin.snoc_castSucc,
    Fin.snoc_castSucc]

private theorem part_last_newTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    (newTable π).part (Fin.last n) = {Fin.last n} :=
  (newTable π).part_eq_of_mem (by simp) (mem_singleton_self _)

private theorem part_last_joinTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (B : Finset (Fin n)) (hB : B ∈ π.parts) :
    (joinTable π B hB).part (Fin.last n) = insert (Fin.last n) (B.map Fin.castSuccEmb) :=
  (joinTable π B hB).part_eq_of_mem (by simp) (mem_insert_self _ _)

omit [MeasurableSpace X] in
private theorem castSucc_mem_part_last_iff {n : ℕ} (xs : Fin n → X) (x : X) (j : Fin n) :
    Fin.castSucc j ∈ (tiePartition (Fin.snoc (α := fun _ ↦ X) xs x)).part (Fin.last n) ↔
      x = xs j := by
  rw [mem_part_tiePartition, Fin.snoc_last, Fin.snoc_castSucc]

omit [MeasurableSpace X] in
private theorem exists_tiePartition_snoc_eq_seat {n : ℕ} (xs : Fin n → X) (x : X) :
    ∃ c, tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) = seat (tiePartition xs) c := by
  obtain ⟨c, hc⟩ := exists_seat_eq (tiePartition (Fin.snoc (α := fun _ ↦ X) xs x))
  revert c
  rw [comap_castSucc_tiePartition_snoc]
  exact fun c hc ↦ ⟨c, hc.symm⟩

private theorem castSucc_mem_part_last_seat {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (c : Option π.parts) (j : Fin n) :
    Fin.castSucc j ∈ (seat π c).part (Fin.last n) ↔ ∃ B ∈ c, j ∈ B.1 := by
  rcases c with _ | ⟨B, hB⟩
  · simp [seat, part_last_newTable, Fin.castSucc_ne_last]
  · simp [seat, part_last_joinTable, Fin.castSucc_ne_last]

omit [MeasurableSpace X] in
/-- Where the last draw sits: a new table iff it differs from all earlier draws. -/
theorem tiePartition_snoc_eq_seat_none_iff {n : ℕ} (xs : Fin n → X) (x : X) :
    tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) = seat (tiePartition xs) none ↔
      x ∉ Set.range xs := by
  constructor
  · rintro h ⟨j, rfl⟩
    have := (castSucc_mem_part_last_iff xs (xs j) j).2 rfl
    rw [h, castSucc_mem_part_last_seat] at this
    simp at this
  · intro hx
    obtain ⟨c, hc⟩ := exists_tiePartition_snoc_eq_seat xs x
    rcases c with _ | ⟨B, hB⟩
    · exact hc
    · exfalso
      obtain ⟨j, hj⟩ := (tiePartition xs).nonempty_of_mem_parts hB
      have : Fin.castSucc j ∈ (tiePartition (Fin.snoc (α := fun _ ↦ X) xs x)).part
          (Fin.last n) := by
        rw [hc, castSucc_mem_part_last_seat]
        exact ⟨⟨B, hB⟩, rfl, hj⟩
      exact hx ⟨j, ((castSucc_mem_part_last_iff xs x j).1 this).symm⟩

omit [MeasurableSpace X] in
/-- Where the last draw sits: at the table `B` iff it equals the earlier draws in `B`. -/
theorem tiePartition_snoc_eq_seat_some_iff {n : ℕ} (xs : Fin n → X) (x : X)
    (B : (tiePartition xs).parts) {i : Fin n} (hi : i ∈ B.1) :
    tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) = seat (tiePartition xs) (some B) ↔
      x = xs i := by
  constructor
  · intro h
    rw [← castSucc_mem_part_last_iff, h, castSucc_mem_part_last_seat]
    exact ⟨B, rfl, hi⟩
  · intro hx
    obtain ⟨c, hc⟩ := exists_tiePartition_snoc_eq_seat xs x
    have hmem := (castSucc_mem_part_last_iff xs x i).2 hx
    rw [hc, castSucc_mem_part_last_seat] at hmem
    obtain ⟨B', rfl, hB'⟩ := hmem
    rw [hc]
    congr 2
    exact Subtype.ext ((tiePartition xs).eq_of_mem_parts B'.2 B.2 hB' hi)

/-- The event that the draws have a given tie partition is measurable. -/
theorem measurableSet_tiePartition_eq [MeasurableSingletonClass X]
    [MeasurableSpace.CountablySeparated X] {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    MeasurableSet {xs : Fin n → X | tiePartition xs = π} := by
  obtain ⟨f, hf, hinj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated X
  have heq : ∀ i j : Fin n, MeasurableSet {xs : Fin n → X | xs i = xs j} := by
    intro i j
    have : {xs : Fin n → X | xs i = xs j} = ⋂ k, {xs | f (xs i) k = f (xs j) k} := by
      ext xs
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h k ↦ by rw [h], fun h ↦ hinj (funext h)⟩
    rw [this]
    exact MeasurableSet.iInter fun k ↦ measurableSet_eq_fun
      ((measurable_pi_apply k).comp (hf.comp (measurable_pi_apply i)))
      ((measurable_pi_apply k).comp (hf.comp (measurable_pi_apply j)))
  have : {xs : Fin n → X | tiePartition xs = π} =
      ⋂ i, ⋂ j, {xs | xs i = xs j ↔ j ∈ π.part i} := by
    ext xs
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, tiePartition_eq_iff]
  rw [this]
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
  by_cases hij : j ∈ π.part i
  · simpa only [hij, iff_true] using heq i j
  · simp only [hij, iff_false]
    exact (heq i j).compl

/-- One seating multiplies the Chinese restaurant law by the seating probability. -/
private theorem crpProb_seat' {θ : ℝ} (hθ : 0 < θ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) (c : Option π.parts) :
    crpProb θ (seat π c) = crpProb θ π * seatWeight θ π c := by
  have h : crp θ hθ (n + 1) (seat π c) = crp θ hθ n π * ENNReal.ofReal (seatWeight θ π c) := by
    change ((crp θ hθ n).bind (crpStep θ hθ)) (seat π c) = _
    rw [PMF.bind_apply, tsum_fintype, sum_eq_single π]
    · congr 1
      rw [crpStep, PMF.map_apply, tsum_fintype, sum_eq_single c]
      · simp [seatChoice]
      · intro c' _ hc'
        split_ifs with h
        · exact absurd (seat_injective π h).symm hc'
        · rfl
      · simp
    · intro π' _ hπ'
      rw [crpStep, PMF.map_apply, tsum_fintype, sum_eq_zero, mul_zero]
      intro c' _
      split_ifs with h
      · refine absurd ?_ hπ'
        rw [← comap_castSucc_seat π c, h, comap_castSucc_seat]
      · rfl
    · simp
  have h' := congrArg ENNReal.toReal h
  rw [crp_toReal, ENNReal.toReal_mul, crp_toReal,
    ENNReal.toReal_ofReal (seatWeight_nonneg hθ π c)] at h'
  exact h'

omit [MeasurableSpace X] in
open scoped Classical in
private theorem card_filter_eq_part {n : ℕ} (xs : Fin n → X) (i : Fin n) :
    #(univ.filter fun j ↦ xs j = xs i) = #((tiePartition xs).part i) := by
  congr 1
  ext j
  simp [mem_part_tiePartition, eq_comm]

/-- The predictive probability that the next draw sits at a given table of the tie partition. -/
private theorem polyaUrnPredictive_seat [MeasurableSingletonClass X]
    [MeasurableSpace.CountablySeparated X] {α : ℝ} (hα : 0 < α) {H : Measure X}
    [IsProbabilityMeasure H] (hH : ∀ x, H {x} = 0) {n : ℕ} (xs : Fin n → X)
    (c : Option (tiePartition xs).parts) :
    polyaUrnPredictive α H xs
        {x | tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) = seat (tiePartition xs) c} =
      ENNReal.ofReal (seatWeight α (tiePartition xs) c) := by
  classical
  have : NullSingletonClass H := ⟨hH⟩
  have hfin : H (Set.range xs) = 0 := (Set.finite_range xs).measure_zero H
  have hpos : (0 : ℝ) < α + n := by positivity
  rcases c with _ | ⟨B, hB⟩
  · have hset : {x | tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) =
        seat (tiePartition xs) none} = (Set.range xs)ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, tiePartition_snoc_eq_seat_none_iff, Set.mem_compl_iff]
    have hmeas : MeasurableSet (Set.range xs) := (Set.finite_range xs).measurableSet
    rw [hset, polyaUrnPredictive_apply α H xs hmeas.compl, measure_compl hmeas (measure_ne_top _ _),
      hfin, measure_univ, tsub_zero, mul_one]
    rw [seatWeight, add_comm (n : ℝ), ENNReal.ofReal_div_of_pos hpos]
    simp
  · obtain ⟨i, hi⟩ := (tiePartition xs).nonempty_of_mem_parts hB
    have hset : {x | tiePartition (Fin.snoc (α := fun _ ↦ X) xs x) =
        seat (tiePartition xs) (some ⟨B, hB⟩)} = {xs i} := by
      ext x
      simp only [Set.mem_ofPred_eq, tiePartition_snoc_eq_seat_some_iff xs x ⟨B, hB⟩ hi,
        Set.mem_singleton_iff]
    have hBi : (tiePartition xs).part i = B := (tiePartition xs).part_eq_of_mem hB hi
    rw [hset, polyaUrnPredictive_apply α H xs (measurableSet_singleton _), hH, mul_zero, zero_add]
    simp only [Set.mem_singleton_iff]
    rw [card_filter_eq_part, hBi, seatWeight, add_comm (n : ℝ), ENNReal.ofReal_div_of_pos hpos,
      ENNReal.ofReal_natCast]

/-- **The ties of the Blackwell–MacQueen urn follow the Chinese restaurant process** (Pitman
2006, §3.1): for an atomless base measure, the partition of the first `n` draws into groups of
equal values has the law `α^{|π|} ∏_{B ∈ π} (|B| - 1)! / α^{(n)}`. -/
theorem blackwellMacQueen_tiePartition [MeasurableSingletonClass X]
    [MeasurableSpace.CountablySeparated X] (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (hH : ∀ x, H {x} = 0) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) :
    blackwellMacQueen α H n {xs | tiePartition xs = π} =
      ENNReal.ofReal (MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crpProb α π) := by
  induction n with
  | zero =>
    have hparts : π.parts = ∅ := Finpartition.parts_eq_empty_iff.2 (by simp)
    have hπ : tiePartition (fun i : Fin 0 ↦ i.elim0 : Fin 0 → X) = π :=
      Finpartition.ext (by rw [hparts, Finpartition.parts_eq_empty_iff.2 (by simp)])
    rw [blackwellMacQueen, Measure.dirac_apply' _ (measurableSet_tiePartition_eq π)]
    simp [hπ, crpProb, Finpartition.cardProd, hparts]
  | succ n ih =>
    obtain ⟨c, hc⟩ := exists_seat_eq π
    rw [← hc]
    generalize π.comap Fin.castSucc = π0 at c
    have hk := measurable_map_snoc α H n
    rw [blackwellMacQueen, Measure.bind_apply (measurableSet_tiePartition_eq _) hk.aemeasurable]
    have hpt : ∀ xs : Fin n → X,
        ((polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x)
            {xs' | tiePartition xs' = seat π0 c} =
          {xs | tiePartition xs = π0}.indicator
            (fun _ ↦ ENNReal.ofReal (seatWeight α π0 c)) xs := by
      intro xs
      rw [Measure.map_apply (measurable_snoc xs) (measurableSet_tiePartition_eq _)]
      by_cases h : tiePartition xs = π0
      · rw [Set.indicator_of_mem (show xs ∈ {xs | tiePartition xs = π0} from h)]
        subst h
        exact polyaUrnPredictive_seat hα hH xs c
      · rw [Set.indicator_of_notMem (show xs ∉ {xs | tiePartition xs = π0} from h)]
        convert measure_empty (μ := polyaUrnPredictive α H xs)
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        apply h
        rw [← comap_castSucc_tiePartition_snoc xs x, hx, comap_castSucc_seat]
    simp_rw [hpt]
    rw [lintegral_indicator_const (measurableSet_tiePartition_eq _), ih, crpProb_seat' hα,
      ENNReal.ofReal_mul (by rw [← crp_toReal hα]; exact ENNReal.toReal_nonneg), mul_comm]

/-- **Moments of the Dirichlet process for at most two draws**: for `n ≤ 2`,
`E[∏_{i<n} G(Aᵢ)] = P(X₀ ∈ A₀, …, X_{n-1} ∈ A_{n-1})` for the Blackwell–MacQueen urn. The case
`n ≥ 3` is the wanted `lintegral_dirichletProcess_prod`. -/
theorem lintegral_dirichletProcess_prod_of_le_two (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {n : ℕ} (hn : n ≤ 2) (A : Fin n → Set X)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫⁻ ν, ∏ i, ν (A i) ∂dirichletProcess α hα H = blackwellMacQueen α H n (Set.univ.pi A) := by
  have hbmq1 : blackwellMacQueen α H 1 = H.map fun x _ ↦ x := by
    have hpred : polyaUrnPredictive α H (fun i : Fin 0 ↦ i.elim0) = H := by
      ext S hS
      rw [polyaUrnPredictive_apply α H _ hS]
      simp only [univ_eq_empty, filter_empty, card_empty, add_zero, CharP.cast_eq_zero]
      rw [mul_comm, ENNReal.mul_div_cancel_right (by simpa using hα) ENNReal.ofReal_ne_top]
    have hsnoc : (fun x ↦ Fin.snoc (α := fun _ ↦ X) (fun i : Fin 0 ↦ i.elim0) x) =
        fun x _ ↦ x := by
      funext x i
      rw [Fin.fin_one_eq_zero i]
      rfl
    rw [blackwellMacQueen, blackwellMacQueen, Measure.dirac_bind (measurable_map_snoc α H 0),
      hpred, hsnoc]
  interval_cases n
  · simp [blackwellMacQueen]
  · rw [hbmq1, Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hA)]
    simp only [univ_unique, Fin.default_eq_zero, prod_singleton]
    rw [lintegral_dirichletProcess_apply α hα H (hA 0)]
    congr 1
    ext x
    simp [Fin.forall_fin_one]
  · simp_rw [Fin.prod_univ_two]
    rw [blackwellMacQueen_succ_pi α H A hA, hbmq1, dirichletProcess,
      lintegral_map (f := fun ν : Measure X ↦ ν (A 0) * ν (A 1))
        ((Measure.measurable_coe (hA 0)).mul (Measure.measurable_coe (hA 1)))
        measurable_stickBreakingMeasure,
      setLIntegral_map (MeasurableSet.univ_pi fun i ↦ hA i.castSucc)
        (measurable_polyaUrnPredictive_apply α H 1 (hA (Fin.last 1))) (by fun_prop)]
    have h := (StickBreakingProcess.isDirichlet_sethuraman α hα H)
      |>.lintegral_G_mul_G_eq_predictive (hA 0) (hA 1)
    convert h using 2
    · rfl
    · change H.restrict _ = H.restrict (A 0)
      congr 1
      ext x
      simp [Fin.forall_fin_one]
    · funext x
      change polyaUrnPredictive α H _ (A 1) = polyaUrnPredictive α H _ (A 1)
      congr 2
      funext i
      rw [Fin.fin_one_eq_zero i]
      rfl

end ProbabilityTheory
