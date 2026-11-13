/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianHadamardLogDerivative
import Code.FrontierA.DyadicInverseSquareSummability
import Code.FrontierA.HadamardQuadraticFactorOrder
import Code.FrontierA.EntireOrderMatchedQuotient
import Code.FrontierA.EntireZeroFreeLogarithm
import Code.FrontierA.EntireExponentialLogAffine
import Code.FrontierA.EntireExponentialCharacteristicAffine
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Lindelof









open Filter Metric
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

noncomputable section


structure EvenExponentialTypeImaginaryZeros (F : Complex → Complex) where
  analytic : AnalyticOnNhd Complex F Set.univ
  value_zero_ne : F 0 ≠ 0
  even : ∀ z, F (-z) = F z
  prefactor : Real
  exponentialType : Real
  prefactor_pos : 0 < prefactor
  exponentialType_nonneg : 0 ≤ exponentialType
  norm_le : ∀ z, ‖F z‖ ≤ prefactor * Real.exp (exponentialType * ‖z‖)
  zeros_imaginary : ∀ z, F z = 0 → z.re = 0


def entireZeroSet (F : Complex → Complex) : Set Complex :=
  {z | F z = 0}


def positiveImaginaryZeroSet (F : Complex → Complex) : Set Real :=
  {y | 0 < y ∧ F (y * Complex.I) = 0}

theorem EvenExponentialTypeImaginaryZeros.entireZeroSet_countable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    (entireZeroSet F).Countable := by
  have hcodiscrete : (entireZeroSet F)ᶜ ∈ Filter.codiscrete Complex := by
    simpa [entireZeroSet] using
      hF.analytic.preimage_zero_mem_codiscrete hF.value_zero_ne
  have hclosed_discrete := compl_mem_codiscrete_iff.mp hcodiscrete
  exact (isLindelof_univ.of_isClosed_subset hclosed_discrete.1
    (Set.subset_univ _)).countable_of_isDiscrete hclosed_discrete.2

theorem EvenExponentialTypeImaginaryZeros.entireZeroSet_closed_discrete
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    IsClosed (entireZeroSet F) ∧ IsDiscrete (entireZeroSet F) := by
  apply compl_mem_codiscrete_iff.mp
  simpa [entireZeroSet] using
    hF.analytic.preimage_zero_mem_codiscrete hF.value_zero_ne

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroSet_countable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    (positiveImaginaryZeroSet F).Countable := by
  have hsubset : positiveImaginaryZeroSet F ⊆
      (fun z : Complex => z.im) '' entireZeroSet F := by
    intro y hy
    refine ⟨y * Complex.I, ?_, ?_⟩
    · exact hy.2
    · simp
  exact (hF.entireZeroSet_countable.image _).mono hsubset



def positiveImaginaryZeroCopies (F : Complex → Complex) : Type :=
  Σ y : positiveImaginaryZeroSet F,
    Fin (analyticOrderAt F ((y.1 : Complex) * Complex.I)).toNat

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopies_countable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Countable (positiveImaginaryZeroCopies F) := by
  letI : Countable (positiveImaginaryZeroSet F) :=
    hF.positiveImaginaryZeroSet_countable.to_subtype
  change Countable (Σ y : positiveImaginaryZeroSet F,
    Fin (analyticOrderAt F ((y.1 : Complex) * Complex.I)).toNat)
  exact inferInstance


def positiveImaginaryZeroMass {F : Complex → Complex}
    (q : positiveImaginaryZeroCopies F) : Real :=
  (q.1.1 ^ 2)⁻¹

theorem positiveImaginaryZeroMass_pos
    {F : Complex → Complex} (q : positiveImaginaryZeroCopies F) :
    0 < positiveImaginaryZeroMass q := by
  exact inv_pos.mpr (sq_pos_of_pos q.1.2.1)


def positiveImaginaryZeroCopiesBelow (F : Complex → Complex) (R : Real) :
    Set (positiveImaginaryZeroCopies F) :=
  {q | q.1.1 ≤ R}

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroCopiesBelow_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    (positiveImaginaryZeroCopiesBelow F R).Finite := by
  let location : positiveImaginaryZeroCopies F → Complex :=
    fun q => (q.1.1 : Complex) * Complex.I
  have hzeroDisk :
      (entireZeroSet F ∩ closedBall (0 : Complex) |R|).Finite := by
    exact ((isCompact_closedBall (0 : Complex) |R|).inter_left
        hF.entireZeroSet_closed_discrete.1).finite
          (hF.entireZeroSet_closed_discrete.2.mono Set.inter_subset_left)
  apply Set.Finite.of_finite_fibers location
  · apply hzeroDisk.subset
    rintro z ⟨q, hq, rfl⟩
    constructor
    · exact q.1.2.2
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [abs_of_pos q.1.2.1]
      exact hq.trans (le_abs_self R)
  · intro z
    intro _hz
    rcases (location ⁻¹' {z}).eq_empty_or_nonempty with hempty | ⟨q₀, hq₀⟩
    · simp [hempty]
    · let embed :
          Fin (analyticOrderAt F ((q₀.1.1 : Complex) * Complex.I)).toNat →
            positiveImaginaryZeroCopies F :=
          fun i => ⟨q₀.1, i⟩
      apply (Set.finite_range embed).subset
      intro q hq
      have hloc : location q = location q₀ := by
        exact hq.2.trans hq₀.symm
      have hy : q.1 = q₀.1 := by
        apply Subtype.ext
        have him := congrArg Complex.im hloc
        simpa [location] using him
      cases q with
      | mk y i =>
          cases q₀ with
          | mk y₀ i₀ =>
              dsimp at hy ⊢
              subst y₀
              exact ⟨i, rfl⟩


def entireDiskZeroSet (F : Complex → Complex) (R : Real) : Type :=
  {z : Complex // z ∈ closedBall 0 R ∧ F z = 0}


def entireDiskZeroCopies (F : Complex → Complex) (R : Real) : Type :=
  Σ z : entireDiskZeroSet F R, Fin (analyticOrderNatAt F z.1)

theorem EvenExponentialTypeImaginaryZeros.entireDiskZeroSet_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Finite (entireDiskZeroSet F R) := by
  let s : Set Complex := entireZeroSet F ∩ closedBall 0 R
  have hs : s.Finite :=
    ((isCompact_closedBall (0 : Complex) R).inter_left
      hF.entireZeroSet_closed_discrete.1).finite
        (hF.entireZeroSet_closed_discrete.2.mono Set.inter_subset_left)
  letI : Finite s := hs.to_subtype
  apply Finite.of_injective
      (fun z : entireDiskZeroSet F R =>
        (⟨z.1, z.2.2, z.2.1⟩ : s))
  intro z w h
  apply Subtype.ext
  exact congrArg (fun x : s => (x : Complex)) h

theorem EvenExponentialTypeImaginaryZeros.entireDiskZeroCopies_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Finite (entireDiskZeroCopies F R) := by
  letI := hF.entireDiskZeroSet_finite R
  change Finite (Σ z : entireDiskZeroSet F R,
    Fin (analyticOrderNatAt F z.1))
  exact inferInstance

private theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_ne_top
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt F z ≠ ⊤ := by
  intro htop
  have hzero : F = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hF.analytic w (Set.mem_univ w))).mp htop
  exact hF.value_zero_ne (congrFun hzero 0)

theorem EvenExponentialTypeImaginaryZeros.card_entireDiskZeroCopies_eq_finsum_divisor
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    (Nat.card (entireDiskZeroCopies F R) : Int) =
      ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
  letI := hF.entireDiskZeroSet_finite R
  letI := hF.entireDiskZeroCopies_finite R
  letI : Fintype (entireDiskZeroSet F R) := Fintype.ofFinite _
  change (Nat.card (Σ z : entireDiskZeroSet F R,
    Fin (analyticOrderNatAt F z.1)) : Int) = _
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  push_cast
  let s : Set Complex := {z | z ∈ closedBall (0 : Complex) R ∧ F z = 0}
  have hs : s.Finite := by
    haveI : Finite s := by
      change Finite (entireDiskZeroSet F R)
      infer_instance
    exact Set.toFinite s
  have hsupport : Function.support
      (fun z : Complex => (MeromorphicOn.divisor F (closedBall 0 R)) z) ⊆
        hs.toFinset := by
    intro z hz
    apply hs.mem_toFinset.mpr
    have hball : z ∈ closedBall (0 : Complex) R := by
      by_contra hnot
      simp [MeromorphicOn.divisor_def, hnot] at hz
    refine ⟨hball, ?_⟩
    by_contra hnonzero
    have horder : analyticOrderAt F z = 0 :=
      (hF.analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr hnonzero
    have hdisc : AnalyticOnNhd Complex F (closedBall 0 R) :=
      hF.analytic.mono (Set.subset_univ _)
    change (MeromorphicOn.divisor F (closedBall 0 R)) z ≠ 0 at hz
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hdisc hball,
      horder] at hz
    simp at hz
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  have hsumSubtype :
      ∑ z ∈ hs.toFinset, (MeromorphicOn.divisor F (closedBall 0 R)) z =
        ∑ z : entireDiskZeroSet F R,
          (MeromorphicOn.divisor F (closedBall 0 R)) z.1 := by
    apply Finset.sum_subtype hs.toFinset
    intro z
    rw [hs.mem_toFinset]
    rfl
  rw [hsumSubtype]
  apply Finset.sum_congr rfl
  intro z _
  have hdisc : AnalyticOnNhd Complex F (closedBall 0 R) :=
    hF.analytic.mono (Set.subset_univ _)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hdisc z.2.1]
  have hfinite := hF.analyticOrderAt_ne_top z.1
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  simp

private def positiveImaginaryZeroCopiesBelowToDisk
    {F : Complex → Complex} {R : Real} (hR : 0 ≤ R) :
    positiveImaginaryZeroCopiesBelow F R → entireDiskZeroCopies F R :=
  fun q => ⟨⟨(q.1.1.1 : Complex) * Complex.I, by
    constructor
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos q.1.1.2.1]
      exact q.2
    · exact q.1.1.2.2⟩, q.1.2⟩

private theorem positiveImaginaryZeroCopiesBelowToDisk_injective
    {F : Complex → Complex} {R : Real} (hR : 0 ≤ R) :
    Function.Injective (positiveImaginaryZeroCopiesBelowToDisk
      (F := F) (R := R) hR) := by
  intro q r h
  apply Subtype.ext
  cases q with
  | mk q hq =>
      cases r with
      | mk r hr =>
          dsimp only [positiveImaginaryZeroCopiesBelowToDisk] at h ⊢
          have hloc := congrArg
            (fun p : entireDiskZeroCopies F R => p.1.1.im) h
          have hy : q.1 = r.1 := by
            apply Subtype.ext
            simpa using hloc
          cases q with
          | mk y i =>
              cases r with
              | mk y' j =>
                  dsimp at hy ⊢
                  subst y'
                  have hi := congrArg
                    (fun p : entireDiskZeroCopies F R => p.2.1) h
                  exact Sigma.ext rfl (by
                    exact heq_of_eq (Fin.ext hi))

theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_divisor
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 ≤ R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Int) ≤
      ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
  letI : Finite (positiveImaginaryZeroCopiesBelow F R) :=
    hF.positiveImaginaryZeroCopiesBelow_finite R |>.to_subtype
  letI := hF.entireDiskZeroCopies_finite R
  have hcard := Nat.card_le_card_of_injective
    (positiveImaginaryZeroCopiesBelowToDisk (F := F) (R := R) hR)
    (positiveImaginaryZeroCopiesBelowToDisk_injective
      (F := F) (R := R) hR)
  have hcardInt :
      (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Int) ≤
        (Nat.card (entireDiskZeroCopies F R) : Int) := by
    exact_mod_cast hcard
  rw [hF.card_entireDiskZeroCopies_eq_finsum_divisor R] at hcardInt
  exact hcardInt



def hadamardJensenMajorant {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) (R : Real) : Real :=
  max 1 (hF.prefactor * Real.exp (hF.exponentialType * (2 * R)))

theorem hadamardJensenMajorant_one_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    1 ≤ hadamardJensenMajorant hF R :=
  le_max_left _ _



theorem EvenExponentialTypeImaginaryZeros.zeroMultiplicity_finsum_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    ((∑ᶠ z : Complex,
      (MeromorphicOn.divisor F (closedBall 0 R)) z : Int) : Real) ≤
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
        Real.log ((2 * R) / R) := by
  have hbound : ∀ z ∈ sphere (0 : Complex) |2 * R|,
      ‖F z‖ ≤ hadamardJensenMajorant hF R := by
    intro z hz
    have hnorm : ‖z‖ = 2 * R := by
      simpa [abs_of_pos (by positivity : 0 < 2 * R)] using hz
    calc
      ‖F z‖ ≤ hF.prefactor *
          Real.exp (hF.exponentialType * ‖z‖) := hF.norm_le z
      _ = hF.prefactor *
          Real.exp (hF.exponentialType * (2 * R)) := by rw [hnorm]
      _ ≤ hadamardJensenMajorant hF R :=
        le_max_right _ _
  have hj := AnalyticOnNhd.sum_divisor_le
    (c := (0 : Complex)) (r := R) (R := 2 * R)
    (M := hadamardJensenMajorant hF R)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR,
      abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    (hadamardJensenMajorant_one_le hF R)
    (hF.analytic.mono (Set.subset_univ _)) hF.value_zero_ne hbound
  rw [abs_of_pos hR] at hj
  exact hj

theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_jensen
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
        Real.log ((2 * R) / R) := by
  have hcardInt := hF.card_positiveImaginaryZeroCopiesBelow_le_divisor hR.le
  have hcardReal :
      (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
        ((∑ᶠ z : Complex,
          (MeromorphicOn.divisor F (closedBall 0 R)) z : Int) : Real) := by
    exact_mod_cast hcardInt
  exact hcardReal.trans (hF.zeroMultiplicity_finsum_le hR)


def hadamardZeroCountIntercept {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Real :=
  max 0 (Real.log ((1 + hF.prefactor) / ‖F 0‖) / Real.log 2)


def hadamardZeroCountSlope {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Real :=
  2 * hF.exponentialType / Real.log 2

theorem hadamardZeroCountIntercept_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ hadamardZeroCountIntercept hF :=
  le_max_left _ _

theorem hadamardZeroCountSlope_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ hadamardZeroCountSlope hF := by
  unfold hadamardZeroCountSlope
  exact div_nonneg (mul_nonneg (by norm_num) hF.exponentialType_nonneg)
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le


theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_affine
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 < R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
      hadamardZeroCountIntercept hF + hadamardZeroCountSlope hF * R := by
  have hj := hF.card_positiveImaginaryZeroCopiesBelow_le_jensen hR
  have hlogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hratio : (2 * R) / R = (2 : Real) := by
    field_simp
  rw [hratio] at hj
  let E : Real := Real.exp (hF.exponentialType * (2 * R))
  have hEpos : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp (mul_nonneg hF.exponentialType_nonneg (by positivity))
  have hmajorant : hadamardJensenMajorant hF R ≤
      (1 + hF.prefactor) * E := by
    unfold hadamardJensenMajorant
    apply max_le
    · nlinarith [hF.prefactor_pos]
    · nlinarith [hF.prefactor_pos]
  have hnorm : 0 < ‖F 0‖ := norm_pos_iff.mpr hF.value_zero_ne
  have hquotPos : 0 < hadamardJensenMajorant hF R / ‖F 0‖ := by
    exact div_pos (lt_of_lt_of_le zero_lt_one
      (hadamardJensenMajorant_one_le hF R)) hnorm
  have hupperPos : 0 < ((1 + hF.prefactor) * E) / ‖F 0‖ := by
    exact div_pos (mul_pos (by linarith [hF.prefactor_pos]) hEpos) hnorm
  have hlog :
      Real.log (hadamardJensenMajorant hF R / ‖F 0‖) ≤
        Real.log (((1 + hF.prefactor) * E) / ‖F 0‖) := by
    apply Real.strictMonoOn_log.monotoneOn hquotPos hupperPos
    exact div_le_div_of_nonneg_right hmajorant hnorm.le
  have hrewrite :
      Real.log (((1 + hF.prefactor) * E) / ‖F 0‖) =
        Real.log ((1 + hF.prefactor) / ‖F 0‖) +
          2 * hF.exponentialType * R := by
    rw [Real.log_div
        (mul_ne_zero (by linarith [hF.prefactor_pos]) hEpos.ne') hnorm.ne',
      Real.log_mul (by linarith [hF.prefactor_pos] :
        (1 + hF.prefactor) ≠ 0) hEpos.ne']
    dsimp [E]
    rw [Real.log_exp, Real.log_div
      (by linarith [hF.prefactor_pos]) hnorm.ne']
    ring
  rw [hrewrite] at hlog
  calc
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Real) ≤
        Real.log (hadamardJensenMajorant hF R / ‖F 0‖) /
          Real.log 2 := hj
    _ ≤ (Real.log ((1 + hF.prefactor) / ‖F 0‖) +
          2 * hF.exponentialType * R) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog hlogTwo.le
    _ ≤ (max 0 (Real.log ((1 + hF.prefactor) / ‖F 0‖) /
          Real.log 2)) +
          (2 * hF.exponentialType / Real.log 2) * R := by
      have hbase : Real.log ((1 + hF.prefactor) / ‖F 0‖) /
          Real.log 2 ≤
          max 0 (Real.log ((1 + hF.prefactor) / ‖F 0‖) /
            Real.log 2) := le_max_right _ _
      rw [add_div]
      have hterm : (2 * hF.exponentialType * R) / Real.log 2 =
          (2 * hF.exponentialType / Real.log 2) * R := by ring
      rw [hterm]
      simpa [add_comm] using add_le_add_right hbase
        ((2 * hF.exponentialType / Real.log 2) * R)
    _ = hadamardZeroCountIntercept hF +
          hadamardZeroCountSlope hF * R := rfl



def encodedCountableSequence (α : Type*) [Countable α]
    (f : α → Real) (n : Nat) : Real :=
  match @Encodable.decode₂ α (Encodable.ofCountable α) n with
  | some a => f a
  | none => 0

theorem encodedCountableSequence_encode
    {α : Type*} [Countable α] (f : α → Real) (a : α) :
    encodedCountableSequence α f
      (@Encodable.encode α (Encodable.ofCountable α) a) = f a := by
  letI : Encodable α := Encodable.ofCountable α
  simp [encodedCountableSequence]

theorem encodedCountableSequence_eq_zero_of_notMem_range
    {α : Type*} [Countable α] (f : α → Real) (n : Nat)
    (hn : n ∉ Set.range
      (@Encodable.encode α (Encodable.ofCountable α))) :
    encodedCountableSequence α f n = 0 := by
  letI : Encodable α := Encodable.ofCountable α
  unfold encodedCountableSequence
  rw [show Encodable.decode₂ α n = none by
    exact Option.eq_none_iff_forall_not_mem.mpr fun a ha =>
      hn ⟨a, Encodable.mem_decode₂.mp ha⟩]

theorem exists_encode_eq_of_encodedCountableSequence_ne_zero
    {α : Type*} [Countable α] (f : α → Real) (n : Nat)
    (hn : encodedCountableSequence α f n ≠ 0) :
    ∃ a : α,
      @Encodable.encode α (Encodable.ofCountable α) a = n ∧
        encodedCountableSequence α f n = f a := by
  letI : Encodable α := Encodable.ofCountable α
  unfold encodedCountableSequence at hn ⊢
  split at *
  · rename_i a ha
    exact ⟨a, Encodable.decode₂_eq_some.mp ha, rfl⟩
  · exact (hn rfl).elim

theorem summable_encodedCountableSequence
    {α : Type*} [Countable α] {f : α → Real} (hf : Summable f) :
    Summable (encodedCountableSequence α f) := by
  letI : Encodable α := Encodable.ofCountable α
  let encode : α → Nat := Encodable.encode
  have hcomp : Summable (encodedCountableSequence α f ∘ encode) := by
    apply hf.congr
    intro a
    exact (encodedCountableSequence_encode f a).symm
  exact (Encodable.encode_injective.summable_iff
    (fun n hn => encodedCountableSequence_eq_zero_of_notMem_range f n hn)).mp hcomp

theorem tsum_encodedCountableSequence
    {α : Type*} [Countable α] (f : α → Real) :
    ∑' n, encodedCountableSequence α f n = ∑' a, f a := by
  letI : Encodable α := Encodable.ofCountable α
  let encode : α → Nat := Encodable.encode
  have hzero : ∀ n ∉ Set.range encode,
      encodedCountableSequence α f n = 0 := by
    intro n hn
    exact encodedCountableSequence_eq_zero_of_notMem_range f n hn
  have hsupport : Function.support (encodedCountableSequence α f) ⊆
      Set.range encode := by
    intro n hn
    by_contra hnrange
    exact hn (hzero n hnrange)
  calc
    ∑' n, encodedCountableSequence α f n =
        ∑' a, encodedCountableSequence α f (encode a) :=
      (Encodable.encode_injective.tsum_eq hsupport).symm
    _ = ∑' a, f a := by
      apply tsum_congr
      intro a
      exact encodedCountableSequence_encode f a

@[implicit_reducible] def positiveImaginaryZeroCopiesEncodable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Encodable (positiveImaginaryZeroCopies F) :=
  @Encodable.ofCountable (positiveImaginaryZeroCopies F)
    hF.positiveImaginaryZeroCopies_countable



def extractedHadamardRoots {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Nat → Real := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  exact encodedCountableSequence (positiveImaginaryZeroCopies F)
    positiveImaginaryZeroMass

theorem extractedHadamardRoots_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (n : Nat) :
    0 ≤ extractedHadamardRoots hF n := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  unfold extractedHadamardRoots encodedCountableSequence
  split
  · exact positiveImaginaryZeroMass_pos _ |>.le
  · rfl

theorem extractedHadamardRoots_encode
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (q : positiveImaginaryZeroCopies F) :
    extractedHadamardRoots hF
        (@Encodable.encode (positiveImaginaryZeroCopies F)
          (positiveImaginaryZeroCopiesEncodable hF) q) =
      positiveImaginaryZeroMass q := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change encodedCountableSequence (positiveImaginaryZeroCopies F)
      positiveImaginaryZeroMass
        (@Encodable.encode (positiveImaginaryZeroCopies F)
          (positiveImaginaryZeroCopiesEncodable hF) q) = _
  have henc : positiveImaginaryZeroCopiesEncodable hF =
      Encodable.ofCountable (positiveImaginaryZeroCopies F) := rfl
  rw [henc]
  exact encodedCountableSequence_encode positiveImaginaryZeroMass q

theorem exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (n : Nat) (hn : extractedHadamardRoots hF n ≠ 0) :
    ∃ q : positiveImaginaryZeroCopies F,
      @Encodable.encode (positiveImaginaryZeroCopies F)
        (positiveImaginaryZeroCopiesEncodable hF) q = n ∧
      extractedHadamardRoots hF n = positiveImaginaryZeroMass q := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change encodedCountableSequence (positiveImaginaryZeroCopies F)
      positiveImaginaryZeroMass n ≠ 0 at hn
  obtain ⟨q, hqEncode, hqValue⟩ :=
    exists_encode_eq_of_encodedCountableSequence_ne_zero
      positiveImaginaryZeroMass n hn
  refine ⟨q, ?_, hqValue⟩
  exact hqEncode

theorem EvenExponentialTypeImaginaryZeros.positiveImaginaryZeroMass_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Summable (positiveImaginaryZeroMass (F := F)) := by
  let Q := {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1}
  let size : Q → Real := fun q => q.1.1.1
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  letI : Countable Q := inferInstance
  have hlarge : Summable (fun q : Q => 1 / size q ^ 2) := by
    apply summable_inverse_sq_of_linear_sublevel_count size
    · intro q
      exact q.2
    · intro R
      have hfinite := hF.positiveImaginaryZeroCopiesBelow_finite R
      apply hfinite.preimage Subtype.val_injective.injOn
    · exact hadamardZeroCountIntercept_nonneg hF
    · exact hadamardZeroCountSlope_nonneg hF
    · intro R hR
      let target := positiveImaginaryZeroCopiesBelow F R
      let source := {q : Q // size q ≤ R}
      letI : Finite target :=
        hF.positiveImaginaryZeroCopiesBelow_finite R |>.to_subtype
      let embed : source → target := fun q => ⟨q.1.1, q.2⟩
      have hinjective : Function.Injective embed := by
        intro q r h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : target => x.1) h
      have hcard : Nat.card source ≤ Nat.card target :=
        Nat.card_le_card_of_injective embed hinjective
      have hcardReal : (Nat.card source : Real) ≤
          (Nat.card target : Real) := by exact_mod_cast hcard
      exact hcardReal.trans
        (hF.card_positiveImaginaryZeroCopiesBelow_le_affine
          (lt_of_lt_of_le zero_lt_one hR))
  let large : Set (positiveImaginaryZeroCopies F) :=
    {q | 1 ≤ q.1.1}
  have hlargeIndicator : Summable
      (large.indicator (positiveImaginaryZeroMass (F := F))) := by
    apply summable_subtype_iff_indicator.mp
    simpa [Q, size, large, positiveImaginaryZeroMass, one_div] using hlarge
  have hsmallFinite : largeᶜ.Finite := by
    apply (hF.positiveImaginaryZeroCopiesBelow_finite 1).subset
    intro q hq
    change ¬1 ≤ q.1.1 at hq
    exact (lt_of_not_ge hq).le
  have hsmallIndicator : Summable
      (largeᶜ.indicator (positiveImaginaryZeroMass (F := F))) := by
    apply summable_of_finite_support
    exact hsmallFinite.subset Set.support_indicator_subset
  have hadd := hlargeIndicator.add hsmallIndicator
  apply hadd.congr
  intro q
  exact congrFun (Set.indicator_self_add_compl large
    (positiveImaginaryZeroMass (F := F))) q

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardRoots_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Summable (extractedHadamardRoots hF) := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  change Summable (encodedCountableSequence
    (positiveImaginaryZeroCopies F) positiveImaginaryZeroMass)
  exact summable_encodedCountableSequence
    hF.positiveImaginaryZeroMass_summable



theorem EvenExponentialTypeImaginaryZeros.largeZero_logSlope_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    ∑' q : {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1},
        2 * R / (q.1.1 ^ 2 + R ^ 2) ≤
      13 * hadamardZeroCountIntercept hF +
        18 * hadamardZeroCountSlope hF := by
  let Q := {q : positiveImaginaryZeroCopies F // 1 ≤ q.1.1}
  let size : Q → Real := fun q => q.1.1.1
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  letI : Countable Q := inferInstance
  apply tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count
    size (fun q => q.2)
  · intro S
    exact (hF.positiveImaginaryZeroCopiesBelow_finite S).preimage
      Subtype.val_injective.injOn
  · exact hadamardZeroCountIntercept_nonneg hF
  · exact hadamardZeroCountSlope_nonneg hF
  · intro S hS
    let target := positiveImaginaryZeroCopiesBelow F S
    let source := {q : Q // size q ≤ S}
    letI : Finite target :=
      hF.positiveImaginaryZeroCopiesBelow_finite S |>.to_subtype
    let embed : source → target := fun q => ⟨q.1.1, q.2⟩
    have hinjective : Function.Injective embed := by
      intro q r h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : target => x.1) h
    have hcard : Nat.card source ≤ Nat.card target :=
      Nat.card_le_card_of_injective embed hinjective
    have hcardReal : (Nat.card source : Real) ≤
        (Nat.card target : Real) := by exact_mod_cast hcard
    exact hcardReal.trans
      (hF.card_positiveImaginaryZeroCopiesBelow_le_affine
        (lt_of_lt_of_le zero_lt_one hS))
  · exact hR


def positiveZeroRadialLog {F : Complex → Complex}
    (R : Real) : Real :=
  ∑' q : positiveImaginaryZeroCopies F,
    Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q)

def smallZeroLogSlopeBound {F : Complex → Complex} : Real :=
  ∑' q : {q : positiveImaginaryZeroCopies F // q.1.1 < 1},
    (q.1.1)⁻¹

theorem EvenExponentialTypeImaginaryZeros.smallZeroLogSlopeBound_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ smallZeroLogSlopeBound (F := F) := by
  apply tsum_nonneg
  intro q
  exact inv_nonneg.mpr q.1.1.2.1.le

private theorem EvenExponentialTypeImaginaryZeros.smallZeroCopies_finite
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    Finite {q : positiveImaginaryZeroCopies F // q.1.1 < 1} := by
  let target := positiveImaginaryZeroCopiesBelow F 1
  letI : Finite target :=
    hF.positiveImaginaryZeroCopiesBelow_finite 1 |>.to_subtype
  let embed : {q : positiveImaginaryZeroCopies F // q.1.1 < 1} → target :=
    fun q => ⟨q.1, q.2.le⟩
  exact Finite.of_injective embed (by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun x : target => x.1) h)

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_summable
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    Summable (fun q : positiveImaginaryZeroCopies F =>
      Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q)) := by
  apply Real.summable_log_one_add_of_summable
  exact hF.positiveImaginaryZeroMass_summable.mul_left (R ^ 2)

private theorem positiveZeroRadialLog_term_hasDerivAt
    {F : Complex → Complex} (q : positiveImaginaryZeroCopies F) (R : Real) :
    HasDerivAt
      (fun x => Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
      (2 * R / (q.1.1 ^ 2 + R ^ 2)) R := by
  have hinner : HasDerivAt
      (fun x : Real => 1 + x ^ 2 * positiveImaginaryZeroMass q)
      (2 * R * positiveImaginaryZeroMass q) R := by
    convert (((hasDerivAt_id R).pow 2).mul_const
      (positiveImaginaryZeroMass q) |>.const_add 1) using 1 <;>
        simp [id] <;> ring
  have hpos : 0 < 1 + R ^ 2 * positiveImaginaryZeroMass q := by
    nlinarith [sq_nonneg R, positiveImaginaryZeroMass_pos q]
  convert hinner.log hpos.ne' using 1
  unfold positiveImaginaryZeroMass
  have hy : q.1.1 ≠ 0 := q.1.2.1.ne'
  field_simp

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_hasDerivAt
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) :
    HasDerivAt (positiveZeroRadialLog (F := F))
      (∑' q : positiveImaginaryZeroCopies F,
        2 * R / (q.1.1 ^ 2 + R ^ 2)) R := by
  let M : Real := |R| + 1
  let u : positiveImaginaryZeroCopies F → Real := fun q =>
    2 * M * positiveImaginaryZeroMass q
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hu : Summable u :=
    hF.positiveImaginaryZeroMass_summable.mul_left (2 * M)
  change HasDerivAt (fun x => ∑' q : positiveImaginaryZeroCopies F,
    Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
    (∑' q : positiveImaginaryZeroCopies F,
      2 * R / (q.1.1 ^ 2 + R ^ 2)) R
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun q x => Real.log (1 + x ^ 2 * positiveImaginaryZeroMass q))
    (g' := fun q x => 2 * x / (q.1.1 ^ 2 + x ^ 2))
    (t := Set.Ioo (-M) M) (y₀ := 0) (y := R) hu
    (isOpen_Ioo : IsOpen (Set.Ioo (-M) M)) isPreconnected_Ioo
  · intro q x _hx
    exact positiveZeroRadialLog_term_hasDerivAt q x
  · intro q x hx
    rw [Real.norm_eq_abs]
    have hxabs : |x| ≤ M := by
      rw [abs_le]
      exact ⟨hx.1.le, hx.2.le⟩
    dsimp [u]
    have hy2 : 0 < q.1.1 ^ 2 := sq_pos_of_pos q.1.2.1
    have hden : 0 < q.1.1 ^ 2 + x ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
      abs_of_pos hden]
    norm_num
    calc
      2 * |x| / (q.1.1 ^ 2 + x ^ 2) ≤
          2 * |x| / q.1.1 ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg x))
          hy2 (le_add_of_nonneg_right (sq_nonneg x))
      _ =
          2 * |x| * positiveImaginaryZeroMass q := by
        unfold positiveImaginaryZeroMass
        rw [div_eq_mul_inv]
      _ ≤ 2 * M * positiveImaginaryZeroMass q := by
        have hm : 0 ≤ positiveImaginaryZeroMass q :=
          (positiveImaginaryZeroMass_pos q).le
        gcongr
  · exact ⟨neg_lt_zero.mpr hMpos, hMpos⟩
  · simpa using (summable_zero : Summable
      (fun _ : positiveImaginaryZeroCopies F => (0 : Real)))
  · exact ⟨by dsimp [M]; linarith [neg_abs_le R], by
      dsimp [M]
      linarith [le_abs_self R]⟩

def positiveZeroLogSlopeBound {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Real :=
  smallZeroLogSlopeBound (F := F) +
    13 * hadamardZeroCountIntercept hF +
    18 * hadamardZeroCountSlope hF

theorem EvenExponentialTypeImaginaryZeros.positiveZeroLogSlopeBound_nonneg
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 ≤ positiveZeroLogSlopeBound hF := by
  unfold positiveZeroLogSlopeBound
  exact add_nonneg
    (add_nonneg hF.smallZeroLogSlopeBound_nonneg
      (mul_nonneg (by norm_num) (hadamardZeroCountIntercept_nonneg hF)))
    (mul_nonneg (by norm_num) (hadamardZeroCountSlope_nonneg hF))

theorem EvenExponentialTypeImaginaryZeros.positiveZero_logSlope_le
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    (∑' q : positiveImaginaryZeroCopies F,
      2 * R / (q.1.1 ^ 2 + R ^ 2)) ≤
      positiveZeroLogSlopeBound hF := by
  let slope : positiveImaginaryZeroCopies F → Real := fun q =>
    2 * R / (q.1.1 ^ 2 + R ^ 2)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hslope : Summable slope := by
    apply Summable.of_nonneg_of_le
      (fun q => div_nonneg (mul_nonneg (by norm_num) hRpos.le)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun q => ?_)
      (hF.positiveImaginaryZeroMass_summable.mul_left (2 * R))
    dsimp [slope]
    unfold positiveImaginaryZeroMass
    have hy : q.1.1 ≠ 0 := q.1.2.1.ne'
    calc
      2 * R / (q.1.1 ^ 2 + R ^ 2) ≤ 2 * R / q.1.1 ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hRpos.le)
          (sq_pos_of_pos q.1.2.1) (le_add_of_nonneg_right (sq_nonneg R))
      _ = 2 * R * (q.1.1 ^ 2)⁻¹ := by rw [div_eq_mul_inv]
  let large : Set (positiveImaginaryZeroCopies F) := {q | 1 ≤ q.1.1}
  let small : Set (positiveImaginaryZeroCopies F) := {q | q.1.1 < 1}
  have hcompl : largeᶜ = small := by
    ext q
    change (¬1 ≤ q.1.1) ↔ q.1.1 < 1
    exact not_le
  have hsplit := hslope.tsum_subtype_add_tsum_subtype_compl large
  rw [hcompl] at hsplit
  letI : Finite small := by
    exact hF.smallZeroCopies_finite
  have hinvSmall : Summable (fun q : small => (q.1.1.1)⁻¹) := by
    exact summable_of_finite_support (Set.finite_univ.subset (Set.subset_univ _))
  have hsmall : (∑' q : small, slope q.1) ≤
      smallZeroLogSlopeBound (F := F) := by
    change (∑' q : small, slope q.1) ≤ ∑' q : small, (q.1.1.1)⁻¹
    apply (hslope.subtype small).tsum_le_tsum
    · intro q
      dsimp [slope]
      have hy : 0 < q.1.1.1 := q.1.1.2.1
      have hden : 0 < q.1.1.1 ^ 2 + R ^ 2 := by positivity
      rw [inv_eq_one_div, le_div_iff₀ hy, div_mul_eq_mul_div,
        div_le_iff₀ hden]
      nlinarith [sq_nonneg (R - q.1.1.1)]
    · exact hinvSmall
  have hlarge : (∑' q : large, slope q.1) ≤
      13 * hadamardZeroCountIntercept hF +
        18 * hadamardZeroCountSlope hF := by
    exact hF.largeZero_logSlope_le hR
  change (∑' q, slope q) ≤ _
  rw [← hsplit]
  unfold positiveZeroLogSlopeBound
  linarith

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_linear
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 1 ≤ R) :
    positiveZeroRadialLog (F := F) R ≤
      positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * (R - 1) := by
  have hdiff : Differentiable Real (positiveZeroRadialLog (F := F)) :=
    fun x => (hF.positiveZeroRadialLog_hasDerivAt x).differentiableAt
  rw [add_comm]
  rw [← sub_le_iff_le_add]
  apply (convex_Ici (1 : Real)).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
  · intro x hx
    have hxone : 1 ≤ x := interior_subset hx
    rw [(hF.positiveZeroRadialLog_hasDerivAt x).deriv]
    exact hF.positiveZero_logSlope_le hxone
  · exact Set.mem_Ici.mpr le_rfl
  · exact Set.mem_Ici.mpr hR
  · exact hR

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_copies_tprod
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    hadamardRootProduct (extractedHadamardRoots hF) z =
      ∏' q : positiveImaginaryZeroCopies F,
        (1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2) := by
  letI : Countable (positiveImaginaryZeroCopies F) :=
    hF.positiveImaginaryZeroCopies_countable
  let encode : positiveImaginaryZeroCopies F → Nat :=
    @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF)
  let f : Nat → Complex := fun n =>
    hadamardRootFactor (extractedHadamardRoots hF) n z
  have hsupport : Function.mulSupport f ⊆ Set.range encode := by
    intro n hn
    by_contra hnrange
    have hroot : extractedHadamardRoots hF n = 0 := by
      apply encodedCountableSequence_eq_zero_of_notMem_range
        (α := positiveImaginaryZeroCopies F) positiveImaginaryZeroMass n
      simpa [encode, positiveImaginaryZeroCopiesEncodable,
        extractedHadamardRoots] using hnrange
    exact hn (by simp [f, hadamardRootFactor, hroot])
  have hreindex := (@Encodable.encode_injective
    (positiveImaginaryZeroCopies F) (positiveImaginaryZeroCopiesEncodable hF)).tprod_eq
      (f := f) hsupport
  rw [hadamardRootProduct]
  rw [← hreindex]
  apply tprod_congr
  intro q
  simp [f, hadamardRootFactor, encode, extractedHadamardRoots_encode]

theorem EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_radialLog
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
      Real.exp (positiveZeroRadialLog (F := F) ‖z‖) := by
  let g : positiveImaginaryZeroCopies F → Complex := fun q =>
    1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2
  let a : positiveImaginaryZeroCopies F → Real := fun q =>
    1 + ‖z‖ ^ 2 * positiveImaginaryZeroMass q
  have hmassScaled : Summable (fun q : positiveImaginaryZeroCopies F =>
      ‖z‖ ^ 2 * positiveImaginaryZeroMass q) :=
    hF.positiveImaginaryZeroMass_summable.mul_left (‖z‖ ^ 2)
  have hpert : Summable (fun q : positiveImaginaryZeroCopies F =>
      ‖(positiveImaginaryZeroMass q : Complex) * z ^ 2‖) := by
    apply hmassScaled.congr
    intro q
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (positiveImaginaryZeroMass_pos q), norm_pow]
    ring
  have hgMult : Multipliable g := by
    apply multipliable_one_add_of_summable
    exact hpert
  have hterm : ∀ q, ‖g q‖ ≤ a q := by
    intro q
    dsimp [g, a]
    calc
      ‖1 + (positiveImaginaryZeroMass q : Complex) * z ^ 2‖ ≤
          1 + ‖(positiveImaginaryZeroMass q : Complex) * z ^ 2‖ := by
        simpa only [norm_one] using norm_add_le (1 : Complex)
          ((positiveImaginaryZeroMass q : Complex) * z ^ 2)
      _ = 1 + ‖z‖ ^ 2 * positiveImaginaryZeroMass q := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (positiveImaginaryZeroMass_pos q), norm_pow]
        ring
  by_cases hzero : ∃ q, g q = 0
  · obtain ⟨q, hq⟩ := hzero
    rw [hF.hadamardRootProduct_eq_copies_tprod z,
      tprod_of_exists_eq_zero ⟨q, hq⟩, norm_zero]
    positivity
  · have hall : ∀ q, g q ≠ 0 := by simpa only [not_exists] using hzero
    have hlogG : Summable (fun q => Real.log ‖g q‖) := by
      simpa [g] using hpert.summable_log_norm_one_add
    have hlogA : Summable (fun q => Real.log (a q)) := by
      simpa [a] using Real.summable_log_one_add_of_summable hmassScaled
    have hlogTerm : ∀ q, Real.log ‖g q‖ ≤ Real.log (a q) := by
      intro q
      have haPos : 0 < a q := by
        dsimp [a]
        nlinarith [sq_nonneg ‖z‖, positiveImaginaryZeroMass_pos q]
      apply Real.strictMonoOn_log.monotoneOn
        (norm_pos_iff.mpr (hall q)) haPos (hterm q)
    rw [hF.hadamardRootProduct_eq_copies_tprod z, hgMult.norm_tprod,
      ← Real.rexp_tsum_eq_tprod (fun q => norm_pos_iff.mpr (hall q)) hlogG]
    exact Real.exp_le_exp.mpr (hlogG.tsum_le_tsum hlogTerm hlogA)

def hadamardRootProductPrefactor {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Real :=
  Real.exp (positiveZeroRadialLog (F := F) 1)

theorem hadamardRootProductPrefactor_pos
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    0 < hadamardRootProductPrefactor hF := Real.exp_pos _

theorem EvenExponentialTypeImaginaryZeros.positiveZeroRadialLog_le_affine
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (R : Real) (hR : 0 ≤ R) :
    positiveZeroRadialLog (F := F) R ≤
      positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * R := by
  by_cases hRone : 1 ≤ R
  · have hlin := hF.positiveZeroRadialLog_le_linear hRone
    nlinarith [hF.positiveZeroLogSlopeBound_nonneg]
  · have hRle : R ≤ 1 := le_of_not_ge hRone
    have hR2 : R ^ 2 ≤ (1 : Real) ^ 2 :=
      (sq_le_sq₀ hR (by norm_num)).2 hRle
    have hterm : ∀ q : positiveImaginaryZeroCopies F,
        Real.log (1 + R ^ 2 * positiveImaginaryZeroMass q) ≤
          Real.log (1 + 1 ^ 2 * positiveImaginaryZeroMass q) := by
      intro q
      have hm : 0 ≤ positiveImaginaryZeroMass q :=
        (positiveImaginaryZeroMass_pos q).le
      have hleftPos : 0 < 1 + R ^ 2 * positiveImaginaryZeroMass q := by
        nlinarith [mul_nonneg (sq_nonneg R) hm]
      have hrightPos : 0 < 1 + 1 ^ 2 * positiveImaginaryZeroMass q := by
        nlinarith
      apply Real.strictMonoOn_log.monotoneOn
        hleftPos hrightPos
      gcongr
    have hsum := (hF.positiveZeroRadialLog_summable R).tsum_le_tsum hterm
      (hF.positiveZeroRadialLog_summable 1)
    calc
      positiveZeroRadialLog (F := F) R ≤
          positiveZeroRadialLog (F := F) 1 := hsum
      _ ≤ positiveZeroRadialLog (F := F) 1 +
          positiveZeroLogSlopeBound hF * R := by
        exact le_add_of_nonneg_right
          (mul_nonneg hF.positiveZeroLogSlopeBound_nonneg hR)

theorem EvenExponentialTypeImaginaryZeros.norm_hadamardRootProduct_le_exp
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
      hadamardRootProductPrefactor hF *
        Real.exp (positiveZeroLogSlopeBound hF * ‖z‖) := by
  calc
    ‖hadamardRootProduct (extractedHadamardRoots hF) z‖ ≤
        Real.exp (positiveZeroRadialLog (F := F) ‖z‖) :=
      hF.norm_hadamardRootProduct_le_radialLog z
    _ ≤ Real.exp (positiveZeroRadialLog (F := F) 1 +
        positiveZeroLogSlopeBound hF * ‖z‖) :=
      Real.exp_le_exp.mpr (hF.positiveZeroRadialLog_le_affine ‖z‖ (norm_nonneg z))
    _ = hadamardRootProductPrefactor hF *
        Real.exp (positiveZeroLogSlopeBound hF * ‖z‖) := by
      rw [Real.exp_add]
      rfl

theorem hasProdLocallyUniformlyOn_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    HasProdLocallyUniformlyOn (hadamardRootFactor roots)
      (hadamardRootProduct roots) Set.univ := by
  rcases multipliableLocallyUniformlyOn_hadamardRootFactor hroots hsum with
    ⟨g, hg⟩
  have heq : g = hadamardRootProduct roots := by
    funext z
    have hp : HasProd (fun n => hadamardRootFactor roots n z) (g z) :=
      hg.tendsto_at (Set.mem_univ z)
    exact hp.tprod_eq.symm
  rw [← heq]
  exact hg

theorem analyticOnNhd_hadamardRootProduct
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    AnalyticOnNhd Complex (hadamardRootProduct roots) Set.univ := by
  have hprod := hasProdLocallyUniformlyOn_hadamardRootFactor hroots hsum
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hprod
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  apply hprod.differentiableOn _ isOpen_univ
  exact Filter.Eventually.of_forall fun s => by
    intro z _hz
    apply DifferentiableAt.differentiableWithinAt
    unfold hadamardRootFactor
    fun_prop

theorem hadamardVanishingIndices_finite
    {roots : Nat → Real} (hsum : Summable roots) (z : Complex) :
    {n | hadamardRootFactor roots n z = 0}.Finite := by
  have hroots0 : Tendsto (fun n => (roots n : Complex)) cofinite (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp
      hsum.tendsto_cofinite_zero
  have hfactors1 : Tendsto (fun n => hadamardRootFactor roots n z)
      cofinite (nhds 1) := by
    convert tendsto_const_nhds.add (hroots0.mul_const (z ^ 2)) using 1 <;> simp
  have hevent : ∀ᶠ n in cofinite, hadamardRootFactor roots n z ≠ 0 := by
    filter_upwards [hfactors1.eventually
      (ball_mem_nhds (1 : Complex) zero_lt_one)] with n hn
    intro hzero
    rw [hzero] at hn
    norm_num [mem_ball] at hn
  simpa only [not_ne_iff] using Filter.eventually_cofinite.mp hevent


def hadamardVanishingIndices
    {roots : Nat → Real} (hsum : Summable roots) (z : Complex) : Finset Nat :=
  (hadamardVanishingIndices_finite hsum z).toFinset

@[simp] theorem mem_hadamardVanishingIndices
    {roots : Nat → Real} (hsum : Summable roots) (z : Complex) (n : Nat) :
    n ∈ hadamardVanishingIndices hsum z ↔
      hadamardRootFactor roots n z = 0 := by
  simp [hadamardVanishingIndices]

theorem hasProdLocallyUniformlyOn_hadamardQuadraticFactor
    {ι : Type*} {r : ι → Real} (hr : ∀ i, 0 ≤ r i)
    (hsum : Summable r) :
    HasProdLocallyUniformlyOn (fun i z => hadamardQuadraticFactor (r i) z)
      (fun z => ∏' i, hadamardQuadraticFactor (r i) z) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let u : ι → Real := fun i => r i * ‖z₀‖ ^ 2
    have hu : Summable u := hsum.mul_right _
    apply hu.hasProdUniformlyOn_one_add hcompact
    · exact Filter.Eventually.of_forall fun i z hz => by
        dsimp [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hr i), norm_pow]
        exact mul_le_mul_of_nonneg_left (hmax z hz) (hr i)
    · intro i
      fun_prop


def hadamardRootProductAway
    {roots : Nat → Real} (S : Finset Nat) (w : Complex) : Complex :=
  ∏' n : Nat, if n ∈ S then 1 else hadamardRootFactor roots n w

theorem analyticOnNhd_hadamardRootProductAway
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (S : Finset Nat) :
    AnalyticOnNhd Complex (hadamardRootProductAway (roots := roots) S) Set.univ := by
  let roots' : Nat → Real := fun n => if n ∈ S then 0 else roots n
  have hroots' : ∀ n, 0 ≤ roots' n := by
    intro n
    dsimp [roots']
    split <;> simp_all
  have hsum' : Summable roots' := by
    have hi := hsum.indicator (S : Set Nat)ᶜ
    apply hi.congr
    intro n
    by_cases hn : n ∈ S <;> simp [roots', Set.indicator, hn]
  have ha := analyticOnNhd_hadamardRootProduct hroots' hsum'
  convert ha using 1
  funext w
  unfold hadamardRootProductAway hadamardRootProduct
  apply tprod_congr
  intro n
  by_cases hn : n ∈ S <;>
    simp [roots', hadamardRootFactor, hn]

theorem hadamardRootProduct_eq_finset_prod_mul_away
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (S : Finset Nat) (w : Complex) :
    hadamardRootProduct roots w =
      (∏ n ∈ S, hadamardRootFactor roots n w) *
        hadamardRootProductAway (roots := roots) S w := by
  let f : Nat → Complex := fun n => hadamardRootFactor roots n w
  let fS : Nat → Complex := fun n => if n ∈ S then f n else 1
  let fSc : Nat → Complex := fun n => if n ∈ S then 1 else f n
  have hmultS : Multipliable fS := by
    apply multipliable_of_finite_mulSupport
    apply S.finite_toSet.subset
    intro n hn
    by_contra hnS
    change n ∉ S at hnS
    change fS n ≠ 1 at hn
    exact hn (if_neg hnS)
  have hmultSc : Multipliable fSc := by
    let delta : Nat → Complex := fun n =>
      if n ∈ S then 0 else (roots n : Complex) * w ^ 2
    have hi := (summable_norm_hadamardRootFactor_sub_one hroots hsum w).indicator
      (S : Set Nat)ᶜ
    have hdelta : Summable (fun n => ‖delta n‖) := by
      apply hi.congr
      intro n
      by_cases hn : n ∈ S <;>
        simp [delta, hn, Set.indicator]
    have hm := multipliable_one_add_of_summable hdelta
    apply hm.congr
    intro n
    by_cases hn : n ∈ S <;>
      simp [fSc, f, delta, hadamardRootFactor, hn]
  change (∏' n, f n) = (∏ n ∈ S, f n) * ∏' n, fSc n
  calc
    (∏' n, f n) = ∏' n, fS n * fSc n := by
      apply tprod_congr
      intro n
      simp only [fS, fSc]
      split <;> simp_all
    _ = (∏' n, fS n) * ∏' n, fSc n := hmultS.tprod_mul hmultSc
    _ = (∏ n ∈ S, f n) * ∏' n, fSc n := by
      have ht : (∏' n, fS n) = ∏ n ∈ S, fS n := by
        apply tprod_eq_prod (s := S)
        intro n hn
        simp [fS, hn]
      simpa [fS] using congrArg (fun x => x * ∏' n, fSc n) ht

theorem hadamardRootProductAway_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    hadamardRootProductAway (roots := roots)
      (hadamardVanishingIndices hsum z) z ≠ 0 := by
  let S := hadamardVanishingIndices hsum z
  let delta : Nat → Complex := fun n =>
    if n ∈ S then 0 else (roots n : Complex) * z ^ 2
  have hprod : (∏' n : Nat, ((1 : Complex) + delta n)) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro n hzero
      by_cases hn : n ∈ S
      · simp only [delta, if_pos hn, add_zero, one_ne_zero] at hzero
      · apply hn
        apply (mem_hadamardVanishingIndices hsum z n).mpr
        simpa only [delta, if_neg hn, hadamardRootFactor] using hzero
    · have hi := (summable_norm_hadamardRootFactor_sub_one hroots hsum z).indicator
        (S : Set Nat)ᶜ
      apply hi.congr
      intro n
      by_cases hn : n ∈ S <;>
        simp [delta, hn, Set.indicator]
  have heq :
      (∏' n : Nat, ((1 : Complex) + delta n)) =
        ∏' n : Nat, (if n ∈ S then 1 else hadamardRootFactor roots n z) := by
    apply tprod_congr
    intro n
    by_cases hn : n ∈ S
    · simp only [delta, if_pos hn, add_zero]
    · simp only [delta, if_neg hn, hadamardRootFactor]
  change (∏' n : Nat,
    (if n ∈ S then 1 else hadamardRootFactor roots n z)) ≠ 0
  rw [← heq]
  exact hprod



theorem analyticOrderAt_hadamardRootProduct_eq_card
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    analyticOrderAt (hadamardRootProduct roots) z =
      (hadamardVanishingIndices hsum z).card := by
  let S := hadamardVanishingIndices hsum z
  let finitePart : Complex → Complex := fun w =>
    ∏ n ∈ S, hadamardRootFactor roots n w
  let awayPart : Complex → Complex :=
    hadamardRootProductAway (roots := roots) (hadamardVanishingIndices hsum z)
  have hfun : hadamardRootProduct roots = finitePart * awayPart := by
    funext w
    exact hadamardRootProduct_eq_finset_prod_mul_away hroots hsum S w
  have hfiniteAnalytic : AnalyticAt Complex finitePart z := by
    dsimp [finitePart]
    unfold hadamardRootFactor
    fun_prop
  have hawayAnalytic : AnalyticAt Complex awayPart z :=
    (analyticOnNhd_hadamardRootProductAway hroots hsum
      (hadamardVanishingIndices hsum z)) z (Set.mem_univ z)
  have hawayOrder : analyticOrderAt awayPart z = 0 :=
    hawayAnalytic.analyticOrderAt_eq_zero.mpr
      (hadamardRootProductAway_ne_zero hroots hsum z)
  have hpositive : ∀ n ∈ S, 0 < roots n := by
    intro n hn
    apply lt_of_le_of_ne (hroots n)
    intro hzero
    have hfactor : hadamardRootFactor roots n z = 0 := by
      simpa [S] using hn
    unfold hadamardRootFactor at hfactor
    rw [← hzero] at hfactor
    norm_num at hfactor
  rw [hfun, analyticOrderAt_mul hfiniteAnalytic hawayAnalytic, hawayOrder,
    add_zero]
  change analyticOrderAt (fun w =>
    ∏ n ∈ S, hadamardQuadraticFactor (roots n) w) z = (S.card : ENat)
  rw [analyticOrderAt_hadamardQuadraticFactor_prod S roots hpositive z]
  congr 1
  rw [Finset.filter_eq_self.mpr]
  intro n hn
  have hfactor : hadamardRootFactor roots n z = 0 := by
    simpa [S] using hn
  simpa [hadamardRootFactor, hadamardQuadraticFactor] using hfactor

private noncomputable def EvenExponentialTypeImaginaryZeros.positiveZeroCopy
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {y : Real} (hy : 0 < y) (hzero : F ((y : Complex) * Complex.I) = 0) :
    positiveImaginaryZeroCopies F := by
  let y₀ : positiveImaginaryZeroSet F := ⟨y, hy, hzero⟩
  have hfinite := hF.analyticOrderAt_ne_top ((y : Complex) * Complex.I)
  have horder : analyticOrderAt F ((y : Complex) * Complex.I) ≠ 0 :=
    (hF.analytic ((y : Complex) * Complex.I) (Set.mem_univ _)).analyticOrderAt_ne_zero.mpr
      hzero
  have hnat : analyticOrderNatAt F ((y : Complex) * Complex.I) ≠ 0 := by
    intro hn
    have hcast := Nat.cast_analyticOrderNatAt hfinite
    rw [hn] at hcast
    exact horder (by simpa using hcast.symm)
  exact ⟨y₀, ⟨0, Nat.pos_of_ne_zero hnat⟩⟩

private theorem inverseSq_mul_imaginary_sq
    (y : Real) (hy : 0 < y) :
    1 + ((((y ^ 2)⁻¹ : Real) : Complex)) *
      (((y : Complex) * Complex.I) ^ 2) = 0 := by
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring_nf
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne')]
  ring

private theorem hadamardQuadraticFactor_imaginary_eq_zero_iff
    (y r : Real) (hy : 0 < y) :
    hadamardQuadraticFactor r ((y : Complex) * Complex.I) = 0 ↔
      r = (y ^ 2)⁻¹ := by
  constructor
  · intro h
    unfold hadamardQuadraticFactor at h
    rw [mul_pow, Complex.I_sq] at h
    ring_nf at h
    norm_cast at h
    rw [inv_eq_one_div, eq_div_iff (pow_ne_zero 2 hy.ne')]
    nlinarith [h]
  · intro h
    rw [h]
    exact inverseSq_mul_imaginary_sq y hy

private theorem eq_pos_or_neg_imaginary_of_inverseSq_factor_zero
    (y : Real) (hy : 0 < y) (z : Complex)
    (hzero : 1 + ((((y ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0) :
    z = (y : Complex) * Complex.I ∨
      z = -((y : Complex) * Complex.I) := by
  have hy0 : (y : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpoly :
      (z - (y : Complex) * Complex.I) *
        (z + (y : Complex) * Complex.I) = 0 := by
    push_cast at hzero
    field_simp at hzero
    simp at hzero
    calc
      (z - (y : Complex) * Complex.I) *
          (z + (y : Complex) * Complex.I) =
          z ^ 2 - (y : Complex) ^ 2 * Complex.I ^ 2 := by ring
      _ = z ^ 2 + (y : Complex) ^ 2 := by
        rw [Complex.I_sq]
        ring
      _ = 0 := by simpa [add_comm] using hzero
  rcases mul_eq_zero.mp hpoly with hpos | hneg
  · exact Or.inl (sub_eq_zero.mp hpos)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hneg)

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_of_eq_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {z : Complex} (hz : F z = 0) :
    hadamardRootProduct (extractedHadamardRoots hF) z = 0 := by
  have hre : z.re = 0 := hF.zeros_imaginary z hz
  have hzform : z = (z.im : Complex) * Complex.I := by
    apply Complex.ext
    · simpa [hre]
    · simp
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hF.value_zero_ne hz
  have him0 : z.im ≠ 0 := by
    intro him
    apply hz0
    rw [hzform, him]
    simp
  by_cases himpos : 0 < z.im
  · let q := hF.positiveZeroCopy himpos (by simpa [← hzform] using hz)
    let n : Nat := @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) q
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    unfold hadamardRootFactor
    rw [extractedHadamardRoots_encode hF q]
    change 1 + ((((z.im ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0
    have hzsq : z ^ 2 = (((z.im : Complex) * Complex.I) ^ 2) :=
      congrArg (fun w : Complex => w ^ 2) hzform
    rw [hzsq]
    exact inverseSq_mul_imaginary_sq z.im himpos
  · have himneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt himpos) him0
    let y : Real := -z.im
    have hy : 0 < y := neg_pos.mpr himneg
    have hyz : (y : Complex) * Complex.I = -z := by
      rw [hzform]
      dsimp [y]
      push_cast
      ring
    have hyzero : F ((y : Complex) * Complex.I) = 0 := by
      rw [hyz, hF.even, hz]
    let q := hF.positiveZeroCopy hy hyzero
    let n : Nat := @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) q
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    unfold hadamardRootFactor
    rw [extractedHadamardRoots_encode hF q]
    change 1 + ((((y ^ 2)⁻¹ : Real) : Complex)) * z ^ 2 = 0
    have hzneg : z = -((y : Complex) * Complex.I) := by
      rw [hzform]
      dsimp [y]
      push_cast
      ring
    have hzsq : z ^ 2 = (((y : Complex) * Complex.I) ^ 2) := by
      rw [hzneg]
      ring
    rw [hzsq]
    exact inverseSq_mul_imaginary_sq y hy

theorem EvenExponentialTypeImaginaryZeros.eq_zero_of_hadamardRootProduct_eq_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {z : Complex} (hz : hadamardRootProduct (extractedHadamardRoots hF) z = 0) :
    F z = 0 := by
  have hfactor : ∃ n,
      hadamardRootFactor (extractedHadamardRoots hF) n z = 0 := by
    by_contra hnone
    have hall : ∀ n,
        1 + (extractedHadamardRoots hF n : Complex) * z ^ 2 ≠ 0 := by
      intro n hn
      exact hnone ⟨n, hn⟩
    have hnonzero : hadamardRootProduct (extractedHadamardRoots hF) z ≠ 0 := by
      unfold hadamardRootProduct hadamardRootFactor
      apply tprod_one_add_ne_zero_of_summable hall
      exact summable_norm_hadamardRootFactor_sub_one
        (extractedHadamardRoots_nonneg hF)
        hF.extractedHadamardRoots_summable z
    exact hnonzero hz
  obtain ⟨n, hn⟩ := hfactor
  have hroot : extractedHadamardRoots hF n ≠ 0 := by
    intro hzero
    simp [hadamardRootFactor, hzero] at hn
  obtain ⟨q, _hqEncode, hqValue⟩ :=
    exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
      hF n hroot
  let y : Real := q.1.1
  have hy : 0 < y := q.1.2.1
  have hfactorEq :
      1 + (((y ^ 2)⁻¹ : Real) : Complex) * z ^ 2 = 0 := by
    unfold hadamardRootFactor at hn
    rw [hqValue] at hn
    simpa [positiveImaginaryZeroMass, y] using hn
  rcases eq_pos_or_neg_imaginary_of_inverseSq_factor_zero y hy z hfactorEq with
    hzloc | hzloc
  ·
    rw [hzloc]
    exact q.1.2.2
  ·
    rw [hzloc, hF.even]
    exact q.1.2.2

theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_eq_zero_iff
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    hadamardRootProduct (extractedHadamardRoots hF) z = 0 ↔ F z = 0 :=
  ⟨hF.eq_zero_of_hadamardRootProduct_eq_zero,
    hF.hadamardRootProduct_eq_zero_of_eq_zero⟩



theorem EvenExponentialTypeImaginaryZeros.card_hadamardVanishingIndices_positive
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (y : positiveImaginaryZeroSet F) :
    (hadamardVanishingIndices hF.extractedHadamardRoots_summable
      ((y.1 : Complex) * Complex.I)).card =
      analyticOrderNatAt F ((y.1 : Complex) * Complex.I) := by
  let roots := extractedHadamardRoots hF
  let hsum := hF.extractedHadamardRoots_summable
  let z : Complex := (y.1 : Complex) * Complex.I
  let S := hadamardVanishingIndices hsum z
  let encodeAt : Fin (analyticOrderNatAt F z) → Nat := fun i =>
    @Encodable.encode (positiveImaginaryZeroCopies F)
      (positiveImaginaryZeroCopiesEncodable hF) ⟨y, i⟩
  have hfactorIff (n : Nat) :
      hadamardRootFactor roots n z = 0 ↔ roots n = (y.1 ^ 2)⁻¹ := by
    simpa [roots, z, hadamardRootFactor, hadamardQuadraticFactor] using
      hadamardQuadraticFactor_imaginary_eq_zero_iff
        y.1 (roots n) y.2.1
  have hS : S = Finset.univ.image encodeAt := by
    apply Finset.ext
    intro n
    rw [Finset.mem_image]
    constructor
    · intro hn
      have hfactor : hadamardRootFactor roots n z = 0 := by
        exact (mem_hadamardVanishingIndices hsum z n).mp (by simpa [S] using hn)
      have hrootValue : roots n = (y.1 ^ 2)⁻¹ := (hfactorIff n).mp hfactor
      have hrootNe : roots n ≠ 0 := by
        rw [hrootValue]
        exact inv_ne_zero (pow_ne_zero 2 y.2.1.ne')
      obtain ⟨q, hqEncode, hqValue⟩ :=
        exists_positiveImaginaryZeroCopy_of_extractedHadamardRoots_ne_zero
          hF n (by simpa [roots] using hrootNe)
      have hmass : (q.1.1 ^ 2)⁻¹ = (y.1 ^ 2)⁻¹ := by
        calc
          (q.1.1 ^ 2)⁻¹ = positiveImaginaryZeroMass q := rfl
          _ = roots n := by simpa [roots] using hqValue.symm
          _ = (y.1 ^ 2)⁻¹ := hrootValue
      have hsq : q.1.1 ^ 2 = y.1 ^ 2 := by
        have := congrArg (fun x : Real => x⁻¹) hmass
        simpa using this
      have hy : q.1.1 = y.1 := by
        nlinarith [q.1.2.1, y.2.1]
      have hqLocation : q.1 = y := Subtype.ext hy
      cases q with
      | mk qy qi =>
          dsimp at hqLocation hqEncode hqValue ⊢
          subst qy
          exact ⟨qi, Finset.mem_univ _, by simpa [encodeAt, z] using hqEncode⟩
    · rintro ⟨i, _hi, rfl⟩
      have hroot := extractedHadamardRoots_encode hF
        (⟨y, i⟩ : positiveImaginaryZeroCopies F)
      apply (mem_hadamardVanishingIndices hsum z _).mpr
      apply (hfactorIff _).mpr
      simpa [roots, positiveImaginaryZeroMass] using hroot
  have hencodeAt : Function.Injective encodeAt := by
    intro i j hij
    have hq : (⟨y, i⟩ : positiveImaginaryZeroCopies F) = ⟨y, j⟩ :=
      @Encodable.encode_injective (positiveImaginaryZeroCopies F)
        (positiveImaginaryZeroCopiesEncodable hF) _ _
          (by simpa [encodeAt] using hij)
    apply Fin.ext
    exact congrArg (fun q : positiveImaginaryZeroCopies F => q.2.1) hq
  change S.card = analyticOrderNatAt F z
  rw [hS, Finset.card_image_of_injective _ hencodeAt]
  simp

private theorem analyticOrderAt_neg_eq_of_even
    {f : Complex → Complex} (hf : ∀ z, AnalyticAt Complex f z)
    (heven : ∀ z, f (-z) = f z) (z : Complex) :
    analyticOrderAt f (-z) = analyticOrderAt f z := by
  let neg : Complex → Complex := fun w => -w
  have hnegAnalytic : AnalyticAt Complex neg z := by
    dsimp [neg]
    fun_prop
  have hnegDeriv : deriv neg z ≠ 0 := by
    have hderiv := (hasDerivAt_id z).neg.deriv
    simpa [neg] using hderiv
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) hnegAnalytic hnegDeriv
  have hfun : f ∘ neg = f := by
    funext w
    exact heven w
  rw [hfun] at hcomp
  simpa [neg] using hcomp.symm

theorem hadamardRootProduct_neg (roots : Nat → Real) (z : Complex) :
    hadamardRootProduct roots (-z) = hadamardRootProduct roots z := by
  unfold hadamardRootProduct
  apply tprod_congr
  intro n
  unfold hadamardRootFactor
  ring

theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq_positive
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (y : positiveImaginaryZeroSet F) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF))
        ((y.1 : Complex) * Complex.I) =
      analyticOrderAt F ((y.1 : Complex) * Complex.I) := by
  rw [analyticOrderAt_hadamardRootProduct_eq_card
    (extractedHadamardRoots_nonneg hF)
    hF.extractedHadamardRoots_summable]
  rw [hF.card_hadamardVanishingIndices_positive y]
  exact Nat.cast_analyticOrderNatAt
    (hF.analyticOrderAt_ne_top ((y.1 : Complex) * Complex.I))



theorem EvenExponentialTypeImaginaryZeros.analyticOrderAt_hadamardRootProduct_eq
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z =
      analyticOrderAt F z := by
  by_cases hz : F z = 0
  · have hre : z.re = 0 := hF.zeros_imaginary z hz
    have hzform : z = (z.im : Complex) * Complex.I := by
      apply Complex.ext
      · simpa [hre]
      · simp
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      exact hF.value_zero_ne hz
    have him0 : z.im ≠ 0 := by
      intro him
      apply hz0
      rw [hzform, him]
      simp
    by_cases himpos : 0 < z.im
    · let y : positiveImaginaryZeroSet F :=
        ⟨z.im, himpos, by simpa [← hzform] using hz⟩
      simpa [y, ← hzform] using
        hF.analyticOrderAt_hadamardRootProduct_eq_positive y
    · have himneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt himpos) him0
      let yval : Real := -z.im
      have hypos : 0 < yval := neg_pos.mpr himneg
      have hyz : (yval : Complex) * Complex.I = -z := by
        rw [hzform]
        dsimp [yval]
        push_cast
        ring
      have hyzero : F ((yval : Complex) * Complex.I) = 0 := by
        rw [hyz, hF.even, hz]
      let y : positiveImaginaryZeroSet F := ⟨yval, hypos, hyzero⟩
      have hpositive := hF.analyticOrderAt_hadamardRootProduct_eq_positive y
      have hprodEvenOrder := analyticOrderAt_neg_eq_of_even
        (fun w => (analyticOnNhd_hadamardRootProduct
          (extractedHadamardRoots_nonneg hF)
          hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
        (hadamardRootProduct_neg (extractedHadamardRoots hF)) z
      have hFEvenOrder := analyticOrderAt_neg_eq_of_even
        (fun w => hF.analytic w (Set.mem_univ w)) hF.even z
      calc
        analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z =
            analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) (-z) :=
          hprodEvenOrder.symm
        _ = analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF))
            ((y.1 : Complex) * Complex.I) := by rw [hyz]
        _ = analyticOrderAt F ((y.1 : Complex) * Complex.I) := hpositive
        _ = analyticOrderAt F (-z) := by rw [hyz]
        _ = analyticOrderAt F z := hFEvenOrder
  · have hprodNe :
        hadamardRootProduct (extractedHadamardRoots hF) z ≠ 0 := by
      intro hzero
      exact hz ((hF.hadamardRootProduct_eq_zero_iff z).mp hzero)
    rw [(analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr
        hprodNe,
      (hF.analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr hz]


def extractedHadamardQuotient {F : Complex → Complex}
    (hF : EvenExponentialTypeImaginaryZeros F) : Complex → Complex :=
  entireOrderMatchedQuotient F
    (hadamardRootProduct (extractedHadamardRoots hF))

private theorem EvenExponentialTypeImaginaryZeros.hadamardRootProduct_order_ne_top
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    analyticOrderAt (hadamardRootProduct (extractedHadamardRoots hF)) z ≠ ⊤ := by
  rw [analyticOrderAt_hadamardRootProduct_eq_card
    (extractedHadamardRoots_nonneg hF)
    hF.extractedHadamardRoots_summable]
  simp

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_analytic
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    AnalyticAt Complex (extractedHadamardQuotient hF) z := by
  apply analyticAt_entireOrderMatchedQuotient
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm)
    hF.hadamardRootProduct_order_ne_top z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_ne_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z ≠ 0 := by
  apply entireOrderMatchedQuotient_ne_zero
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm)
    hF.hadamardRootProduct_order_ne_top z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_mul_eq
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z *
        hadamardRootProduct (extractedHadamardRoots hF) z = F z := by
  exact entireOrderMatchedQuotient_mul_eq
    (fun w => hF.analytic w (Set.mem_univ w))
    (fun w => (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w))
    (fun w => (hF.analyticOrderAt_hadamardRootProduct_eq w).symm) z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_even
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF (-z) = extractedHadamardQuotient hF z := by
  let P := hadamardRootProduct (extractedHadamardRoots hF)
  let Q := extractedHadamardQuotient hF
  have hQanalytic : AnalyticOnNhd Complex Q Set.univ := fun w _ =>
    hF.extractedHadamardQuotient_analytic w
  have hQnegAnalytic : AnalyticOnNhd Complex (fun w => Q (-w)) Set.univ := by
    intro w _
    exact (hQanalytic (-w) (Set.mem_univ _)).comp (by fun_prop)
  have hlocal : (fun w => Q (-w)) =ᶠ[nhds (0 : Complex)] Q := by
    have hnhd : hadamardRootNeighborhood (extractedHadamardRoots hF) ∈
        nhds (0 : Complex) :=
      (isOpen_hadamardRootNeighborhood _).mem_nhds
        (zero_mem_hadamardRootNeighborhood
          (extractedHadamardRoots_nonneg hF))
    filter_upwards [hnhd] with w hw
    apply mul_right_cancel₀ (hadamardRootProduct_ne_zero
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable hw)
    calc
      Q (-w) * P w = Q (-w) * P (-w) := by
        rw [show P (-w) = P w by
          exact hadamardRootProduct_neg (extractedHadamardRoots hF) w]
      _ = F (-w) := hF.extractedHadamardQuotient_mul_eq (-w)
      _ = F w := hF.even w
      _ = Q w * P w := (hF.extractedHadamardQuotient_mul_eq w).symm
  have hglobal : (fun w => Q (-w)) = Q :=
    hQnegAnalytic.eq_of_eventuallyEq hQanalytic hlocal
  exact congrFun hglobal z

theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_zero
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    extractedHadamardQuotient hF 0 = F 0 := by
  have hmul := hF.extractedHadamardQuotient_mul_eq 0
  simpa [hadamardRootProduct, hadamardRootFactor] using hmul



theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue_of_growth
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {A B : Real} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z,
      ‖extractedHadamardQuotient hF z‖ ≤ A * Real.exp (B * ‖z‖))
    (z : Complex) :
    extractedHadamardQuotient hF z = F 0 := by
  have hQdiff : Differentiable Complex (extractedHadamardQuotient hF) :=
    fun w => hF.extractedHadamardQuotient_analytic w |>.differentiableAt
  obtain ⟨g, hgdiff, hgexp⟩ := exists_entireLogarithm
    (extractedHadamardQuotient hF) hQdiff
      hF.extractedHadamardQuotient_ne_zero
  obtain ⟨a, b, hab⟩ := exists_affine_of_entire_exp_growth
    g hgdiff A B hA hB (fun w => by simpa [hgexp w] using hgrowth w)
  have hQform (w : Complex) :
      extractedHadamardQuotient hF w = Complex.exp (a * w + b) := by
    rw [← hgexp w, hab w]
  have hevenExp :
      (fun w : Complex => Complex.exp (a * (-w) + b)) =
        fun w => Complex.exp (a * w + b) := by
    funext w
    rw [← hQform (-w), ← hQform w]
    exact hF.extractedHadamardQuotient_even w
  have hleft : HasDerivAt
      (fun w : Complex => Complex.exp (a * (-w) + b))
      (Complex.exp b * (-a)) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * (-w) + b) (-a) 0 := by
      convert (((hasDerivAt_id (0 : Complex)).neg.const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (-(0 : Complex)) + b)).comp 0 hinner using 1 <;>
      simp
  have hright : HasDerivAt
      (fun w : Complex => Complex.exp (a * w + b))
      (Complex.exp b * a) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * w + b) a 0 := by
      convert (((hasDerivAt_id (0 : Complex)).const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (0 : Complex) + b)).comp 0 hinner using 1 <;>
      simp
  have hderiv := congrArg (fun f : (Complex → Complex) => deriv f 0) hevenExp
  change deriv (fun w : Complex => Complex.exp (a * (-w) + b)) 0 =
    deriv (fun w : Complex => Complex.exp (a * w + b)) 0 at hderiv
  rw [hleft.deriv, hright.deriv] at hderiv
  have ha : a = 0 := by
    by_contra hane
    have hneg : -(a * Complex.exp b) = a * Complex.exp b := by
      simpa [mul_comm] using hderiv
    have htwo : (2 : Complex) * (a * Complex.exp b) = 0 := by
      calc
        (2 : Complex) * (a * Complex.exp b) =
            a * Complex.exp b + a * Complex.exp b := by ring
        _ = -(a * Complex.exp b) + a * Complex.exp b := by rw [hneg]
        _ = 0 := neg_add_cancel _
    exact (mul_ne_zero (by norm_num)
      (mul_ne_zero hane (Complex.exp_ne_zero b))) htwo
  calc
    extractedHadamardQuotient hF z = Complex.exp (a * z + b) := hQform z
    _ = Complex.exp b := by rw [ha]; simp
    _ = extractedHadamardQuotient hF 0 := by
      rw [hQform 0, ha]
      simp
    _ = F 0 := hF.extractedHadamardQuotient_zero

def EvenExponentialTypeImaginaryZeros.factorization_of_quotient_growth
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {A B : Real} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z,
      ‖extractedHadamardQuotient hF z‖ ≤ A * Real.exp (B * ‖z‖)) :
    EvenHadamardFactorization F where
  roots := extractedHadamardRoots hF
  roots_nonneg := extractedHadamardRoots_nonneg hF
  roots_summable := hF.extractedHadamardRoots_summable
  value_zero_ne := hF.value_zero_ne
  normalized_eq := fun z => by
    have hmul := hF.extractedHadamardQuotient_mul_eq z
    rw [hF.extractedHadamardQuotient_eq_zeroValue_of_growth hA hB hgrowth z]
      at hmul
    rw [div_eq_iff hF.value_zero_ne]
    simpa [mul_comm] using hmul.symm




theorem EvenExponentialTypeImaginaryZeros.extractedHadamardQuotient_eq_zeroValue
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    (z : Complex) :
    extractedHadamardQuotient hF z = F 0 := by
  let P := hadamardRootProduct (extractedHadamardRoots hF)
  have hQdiff : Differentiable Complex (extractedHadamardQuotient hF) :=
    fun w => hF.extractedHadamardQuotient_analytic w |>.differentiableAt
  have hPdiff : Differentiable Complex P := fun w =>
    (analyticOnNhd_hadamardRootProduct
      (extractedHadamardRoots_nonneg hF)
      hF.extractedHadamardRoots_summable) w (Set.mem_univ w) |>.differentiableAt
  have hPzero : P 0 ≠ 0 := by
    simp [P, hadamardRootProduct, hadamardRootFactor]
  obtain ⟨g, hgdiff, hgexp⟩ := exists_entireLogarithm
    (extractedHadamardQuotient hF) hQdiff
      hF.extractedHadamardQuotient_ne_zero
  have hfactor (w : Complex) : F w = P w * Complex.exp (g w) := by
    rw [hgexp w]
    calc
      F w = extractedHadamardQuotient hF w * P w :=
        (hF.extractedHadamardQuotient_mul_eq w).symm
      _ = P w * extractedHadamardQuotient hF w := mul_comm _ _
  obtain ⟨a, b, hab⟩ := exists_affine_of_matched_entire_exp_growth
    F P g
    (fun w => (hF.analytic w (Set.mem_univ w)).differentiableAt)
    hPdiff hgdiff hPzero hfactor
    hF.prefactor hF.exponentialType
    (hadamardRootProductPrefactor hF) (positiveZeroLogSlopeBound hF)
    hF.prefactor_pos hF.exponentialType_nonneg
    (hadamardRootProductPrefactor_pos hF)
    hF.positiveZeroLogSlopeBound_nonneg hF.norm_le
    hF.norm_hadamardRootProduct_le_exp
  have hQform (w : Complex) :
      extractedHadamardQuotient hF w = Complex.exp (a * w + b) := by
    rw [← hgexp w, hab w]
  have hevenExp :
      (fun w : Complex => Complex.exp (a * (-w) + b)) =
        fun w => Complex.exp (a * w + b) := by
    funext w
    rw [← hQform (-w), ← hQform w]
    exact hF.extractedHadamardQuotient_even w
  have hleft : HasDerivAt
      (fun w : Complex => Complex.exp (a * (-w) + b))
      (Complex.exp b * (-a)) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * (-w) + b) (-a) 0 := by
      convert (((hasDerivAt_id (0 : Complex)).neg.const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (-(0 : Complex)) + b)).comp 0 hinner using 1 <;>
      simp
  have hright : HasDerivAt
      (fun w : Complex => Complex.exp (a * w + b))
      (Complex.exp b * a) 0 := by
    have hinner : HasDerivAt (fun w : Complex => a * w + b) a 0 := by
      convert (((hasDerivAt_id (0 : Complex)).const_mul a).add_const b) using 1 <;>
        ring
    convert (Complex.hasDerivAt_exp (a * (0 : Complex) + b)).comp 0 hinner using 1 <;>
      simp
  have hderiv := congrArg (fun f : (Complex → Complex) => deriv f 0) hevenExp
  change deriv (fun w : Complex => Complex.exp (a * (-w) + b)) 0 =
    deriv (fun w : Complex => Complex.exp (a * w + b)) 0 at hderiv
  rw [hleft.deriv, hright.deriv] at hderiv
  have ha : a = 0 := by
    by_contra hane
    have hneg : -(a * Complex.exp b) = a * Complex.exp b := by
      simpa [mul_comm] using hderiv
    have htwo : (2 : Complex) * (a * Complex.exp b) = 0 := by
      calc
        (2 : Complex) * (a * Complex.exp b) =
            a * Complex.exp b + a * Complex.exp b := by ring
        _ = -(a * Complex.exp b) + a * Complex.exp b := by rw [hneg]
        _ = 0 := neg_add_cancel _
    exact (mul_ne_zero (by norm_num)
      (mul_ne_zero hane (Complex.exp_ne_zero b))) htwo
  calc
    extractedHadamardQuotient hF z = Complex.exp (a * z + b) := hQform z
    _ = Complex.exp b := by rw [ha]; simp
    _ = extractedHadamardQuotient hF 0 := by
      rw [hQform 0, ha]
      simp
    _ = F 0 := hF.extractedHadamardQuotient_zero



def EvenExponentialTypeImaginaryZeros.factorization
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F) :
    EvenHadamardFactorization F where
  roots := extractedHadamardRoots hF
  roots_nonneg := extractedHadamardRoots_nonneg hF
  roots_summable := hF.extractedHadamardRoots_summable
  value_zero_ne := hF.value_zero_ne
  normalized_eq := fun z => by
    have hmul := hF.extractedHadamardQuotient_mul_eq z
    rw [hF.extractedHadamardQuotient_eq_zeroValue z] at hmul
    rw [div_eq_iff hF.value_zero_ne]
    simpa [mul_comm] using hmul.symm

section FiniteIsingInput

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def finiteIsingWeightedFieldPartition_extractionData
    {beta : Real} (hbeta : 0 ≤ beta)
    (a : V → Real) (ha : ∀ v, 0 < a v) :
    EvenExponentialTypeImaginaryZeros
      (finiteIsingWeightedFieldPartition G beta a) where
  analytic := finiteIsingWeightedFieldPartition_analyticOnNhd G beta a
  value_zero_ne := Complex.ne_zero_of_re_pos
    (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  even := finiteIsingWeightedFieldPartition_neg G beta a
  prefactor := ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s
  exponentialType := finiteIsingWeightedFieldRadius a
  prefactor_pos := by
    have hzero := finiteIsingWeightedFieldPartition_zero_re_pos G beta a
    rw [finiteIsingWeightedFieldPartition_zero] at hzero
    simpa using hzero
  exponentialType_nonneg := finiteIsingWeightedFieldRadius_nonneg a
  norm_le := fun z => by
    simpa [mul_comm] using norm_finiteIsingWeightedFieldPartition_le G beta a z
  zeros_imaginary := fun z hz => by
    by_contra hre
    exact finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero
      G hbeta a ha hre hz



def finiteIsingWeightedFieldPartition_factorization
    {beta : Real} (hbeta : 0 ≤ beta)
    (a : V → Real) (ha : ∀ v, 0 < a v) :
    FiniteIsingWeightedHadamardFactorization (G := G) beta a :=
  (finiteIsingWeightedFieldPartition_extractionData G hbeta a ha).factorization

end FiniteIsingInput

end

end StatMech.FrontierA
