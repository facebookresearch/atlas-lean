/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianHadamardLogDerivative
import Code.FrontierA.IsingGaussianPhysicalCumulants
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas









open Filter
open scoped BigOperators Complex Nat

namespace StatMech.FrontierA

noncomputable section



def hadamardRootLogTerm (r : Real) (z : Complex) : Complex :=
  2 * (r : Complex) * z / (1 + (r : Complex) * z ^ 2)

private theorem hadamardRootLogTerm_eventuallyEq_partialFractions
    {r : Real} (hr : 0 < r) :
    (hadamardRootLogTerm r) =ᶠ[nhds 0]
      (fun z : Complex =>
        (-Complex.I * (Real.sqrt r : Complex)) *
            ((-Complex.I * (Real.sqrt r : Complex)) * z + 1)⁻¹ +
          (Complex.I * (Real.sqrt r : Complex)) *
            ((Complex.I * (Real.sqrt r : Complex)) * z + 1)⁻¹) := by
  let a : Complex := Real.sqrt r
  have ha2 : a ^ 2 = (r : Complex) := by
    dsimp [a]
    norm_cast
    exact Real.sq_sqrt hr.le
  have hminus : ∀ᶠ z : Complex in nhds 0, (-Complex.I * a) * z + 1 ≠ 0 :=
    (show ContinuousAt (fun z : Complex => (-Complex.I * a) * z + 1) 0 by
      fun_prop).eventually_ne (by simp)
  have hplus : ∀ᶠ z : Complex in nhds 0, (Complex.I * a) * z + 1 ≠ 0 :=
    (show ContinuousAt (fun z : Complex => (Complex.I * a) * z + 1) 0 by
      fun_prop).eventually_ne (by simp)
  filter_upwards [hminus, hplus] with z hzminus hzplus
  change 2 * (r : Complex) * z / (1 + (r : Complex) * z ^ 2) =
    (-Complex.I * a) * ((-Complex.I * a) * z + 1)⁻¹ +
      (Complex.I * a) * ((Complex.I * a) * z + 1)⁻¹
  have hden : 1 + (r : Complex) * z ^ 2 =
      ((-Complex.I * a) * z + 1) * ((Complex.I * a) * z + 1) := by
    rw [← ha2]
    rw [show (-Complex.I * a) * z = -(Complex.I * a * z) by ring,
      show (Complex.I * a) * z = Complex.I * a * z by ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hzden : 1 + (r : Complex) * z ^ 2 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hzminus hzplus
  have hzminus' : 1 - a * z * Complex.I ≠ 0 := by
    convert hzminus using 1 <;> ring
  have hzplus' : 1 + a * z * Complex.I ≠ 0 := by
    convert hzplus using 1 <;> ring
  have hzminus'' : -(z * Complex.I * a) + 1 ≠ 0 := by
    convert hzminus using 1 <;> ring
  have hzplus'' : z * Complex.I * a + 1 ≠ 0 := by
    convert hzplus using 1 <;> ring
  apply (div_eq_iff hzden).2
  rw [hden]
  field_simp [hzminus, hzplus, hzminus', hzplus', hzminus'', hzplus'']
  rw [← ha2]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem iteratedDeriv_hadamardRootLogTerm_of_pos
    {r : Real} (hr : 0 < r) (n : Nat) :
    iteratedDeriv n (hadamardRootLogTerm r) 0 =
      (-Complex.I * (Real.sqrt r : Complex)) *
          ((-1 : Complex) ^ n * n ! *
            (-Complex.I * (Real.sqrt r : Complex)) ^ n) +
        (Complex.I * (Real.sqrt r : Complex)) *
          ((-1 : Complex) ^ n * n ! *
            (Complex.I * (Real.sqrt r : Complex)) ^ n) := by
  let a : Complex := Real.sqrt r
  rw [(hadamardRootLogTerm_eventuallyEq_partialFractions hr).iteratedDeriv_eq n]
  change iteratedDeriv n ((fun z : Complex =>
      (-Complex.I * a) * ((-Complex.I * a) * z + 1)⁻¹) +
    (fun z : Complex =>
      (Complex.I * a) * ((Complex.I * a) * z + 1)⁻¹)) 0 = _
  rw [iteratedDeriv_add
    (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  rw [congr_fun (iter_deriv_inv_linear n (-Complex.I * a) 1) 0,
    congr_fun (iter_deriv_inv_linear n (Complex.I * a) 1) 0]
  simp [a]



theorem iteratedDeriv_hadamardRootLogTerm_odd
    (r : Real) (hr : 0 ≤ r) (m : Nat) (hm : 1 ≤ m) :
    iteratedDeriv (2 * m - 1) (hadamardRootLogTerm r) 0 =
      -2 * (-1 : Complex) ^ m * (Nat.factorial (2 * m - 1) : Complex) *
        (r : Complex) ^ m := by
  rcases hr.eq_or_lt with rfl | hr
  · have hzero : hadamardRootLogTerm 0 = (0 : Complex → Complex) := by
      funext z
      simp [hadamardRootLogTerm]
    rw [hzero]
    have hm0 : m ≠ 0 := by omega
    simp [hm0]
  · rw [iteratedDeriv_hadamardRootLogTerm_of_pos hr]
    let a : Complex := Real.sqrt r
    have hs : a ^ 2 = (r : Complex) := by
      dsimp [a]
      norm_cast
      exact Real.sq_sqrt hr.le
    have hn : 2 * m - 1 + 1 = 2 * m := by omega
    have hodd : Odd (2 * m - 1) := by
      use m - 1
      omega
    have hminus : (-Complex.I * a) ^ (2 * m) =
        (-1 : Complex) ^ m * (r : Complex) ^ m := by
      rw [pow_mul]
      have hsq : (-Complex.I * a) ^ 2 = -(a ^ 2) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hsq, neg_pow, hs]
    have hplus : (Complex.I * a) ^ (2 * m) =
        (-1 : Complex) ^ m * (r : Complex) ^ m := by
      rw [pow_mul]
      have hsq : (Complex.I * a) ^ 2 = -(a ^ 2) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hsq, neg_pow, hs]
    change (-Complex.I * a) *
        ((-1 : Complex) ^ (2 * m - 1) * Nat.factorial (2 * m - 1) *
          (-Complex.I * a) ^ (2 * m - 1)) +
      (Complex.I * a) *
        ((-1 : Complex) ^ (2 * m - 1) * Nat.factorial (2 * m - 1) *
          (Complex.I * a) ^ (2 * m - 1)) = _
    rw [hodd.neg_one_pow]
    have hmsucc : (-Complex.I * a) * (-Complex.I * a) ^ (2 * m - 1) =
        (-Complex.I * a) ^ (2 * m) := by
      rw [mul_comm, ← pow_succ, hn]
    have hpsucc : (Complex.I * a) * (Complex.I * a) ^ (2 * m - 1) =
        (Complex.I * a) ^ (2 * m) := by
      rw [mul_comm, ← pow_succ, hn]
    calc
      _ = -(Nat.factorial (2 * m - 1) : Complex) *
          (((-Complex.I * a) * (-Complex.I * a) ^ (2 * m - 1)) +
            ((Complex.I * a) * (Complex.I * a) ^ (2 * m - 1))) := by ring
      _ = -(Nat.factorial (2 * m - 1) : Complex) *
          (((-Complex.I * a) ^ (2 * m)) +
            ((Complex.I * a) ^ (2 * m))) := by rw [hmsucc, hpsucc]
      _ = _ := by rw [hminus, hplus]; ring

theorem iteratedDeriv_hadamardRootLogTerm_one
    (r : Real) (hr : 0 ≤ r) :
    iteratedDeriv 1 (hadamardRootLogTerm r) 0 = 2 * r := by
  simpa using iteratedDeriv_hadamardRootLogTerm_odd r hr 1 (by omega)

theorem iteratedDeriv_hadamardRootLogTerm_three
    (r : Real) (hr : 0 ≤ r) :
    iteratedDeriv 3 (hadamardRootLogTerm r) 0 = -12 * r ^ 2 := by
  convert iteratedDeriv_hadamardRootLogTerm_odd r hr 2 (by omega) using 1 <;>
    norm_num <;> ring

theorem hadamardRootLogTerm_neg (r : Real) (z : Complex) :
    hadamardRootLogTerm r (-z) = -hadamardRootLogTerm r z := by
  unfold hadamardRootLogTerm
  ring

private theorem iteratedDeriv_odd_function_of_even
    (f : Complex → Complex) (hf : ∀ z, f (-z) = -f z)
    (order : Nat) (horder : Even order) :
    iteratedDeriv order f 0 = 0 := by
  have hfun : (fun z => f (-z)) = fun z => -f z := funext hf
  have hderiv := congrArg
    (fun g : Complex → Complex => iteratedDeriv order g 0) hfun
  change iteratedDeriv order (fun z => f (-z)) 0 =
    iteratedDeriv order (fun z => -f z) 0 at hderiv
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg,
    horder.neg_one_pow] at hderiv
  simp only [one_smul] at hderiv
  have hself : iteratedDeriv order f 0 =
      -iteratedDeriv order f 0 := by
    simpa using hderiv
  linear_combination hself / 2

theorem iteratedDeriv_hadamardRootLogTerm_even
    (r : Real) (order : Nat) (horder : Even order) :
    iteratedDeriv order (hadamardRootLogTerm r) 0 = 0 :=
  iteratedDeriv_odd_function_of_even (hadamardRootLogTerm r)
    (hadamardRootLogTerm_neg r) order horder

private theorem AnalyticOnNhd.iteratedDeriv_local
    {f : Complex → Complex} {U : Set Complex}
    (hf : AnalyticOnNhd Complex f U) (n : Nat) :
    AnalyticOnNhd Complex (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private theorem hasSumLocallyUniformlyOn_iteratedDeriv
    {ι : Type*} {f : ι → Complex → Complex} {g : Complex → Complex}
    {U : Set Complex} (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn f g U)
    (hf : ∀ i, AnalyticOnNhd Complex (f i) U) (n : Nat) :
    HasSumLocallyUniformlyOn
      (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) U := by
  induction n with
  | zero => simpa using hsum
  | succ n ih =>
      rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at ih ⊢
      rw [iteratedDeriv_succ]
      have hder := ih.deriv
        (Filter.Eventually.of_forall fun s =>
          DifferentiableOn.fun_sum fun i _ =>
            (AnalyticOnNhd.iteratedDeriv_local (hf i) n).differentiableOn)
        hU
      apply hder.congr
      intro s z hz
      simp only [Function.comp_apply, iteratedDeriv_succ]
      exact deriv_fun_sum fun i hi =>
        ((AnalyticOnNhd.iteratedDeriv_local (hf i) n).differentiableOn z hz).differentiableAt
          (hU.mem_nhds hz)

theorem summableLocallyUniformlyOn_hadamardRootLogTerm
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    SummableLocallyUniformlyOn (fun n => hadamardRootLogTerm (roots n))
      (hadamardRootNeighborhood roots) := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_hadamardRootNeighborhood roots)
  intro K hKU hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · exact ⟨roots, hsum, by simp⟩
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let total : Real := ∑' n, roots n
    let gap : Real := 1 - ‖z₀‖ ^ 2 * total
    have hgap : 0 < gap := by
      dsimp [gap, total]
      exact sub_pos.mpr (hKU hz₀)
    let bound : Real := 2 * ‖z₀‖ / gap
    let u : Nat → Real := fun n => roots n * bound
    have hu : Summable u := hsum.mul_right bound
    refine ⟨u, hu, ?_⟩
    intro n z hz
    have hterm : ‖(roots n : Complex) * z ^ 2‖ ≤ ‖z₀‖ ^ 2 * total := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hroots n), norm_pow]
      calc
        roots n * ‖z‖ ^ 2 ≤ roots n * ‖z₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (hmax z hz) (hroots n)
        _ ≤ total * ‖z₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (hsum.le_tsum n fun k _ => hroots k) (sq_nonneg ‖z₀‖)
        _ = ‖z₀‖ ^ 2 * total := mul_comm _ _
    have hden : gap ≤ ‖1 + (roots n : Complex) * z ^ 2‖ := by
      calc
        gap = 1 - ‖z₀‖ ^ 2 * total := rfl
        _ ≤ 1 - ‖(roots n : Complex) * z ^ 2‖ := sub_le_sub_left hterm 1
        _ = ‖(1 : Complex)‖ - ‖-((roots n : Complex) * z ^ 2)‖ := by simp
        _ ≤ ‖(1 : Complex) - (-((roots n : Complex) * z ^ 2))‖ :=
          norm_sub_norm_le _ _
        _ = ‖1 + (roots n : Complex) * z ^ 2‖ := by ring_nf
    unfold hadamardRootLogTerm
    rw [norm_div]
    calc
      ‖2 * (roots n : Complex) * z‖ / ‖1 + (roots n : Complex) * z ^ 2‖ ≤
          ‖2 * (roots n : Complex) * z‖ / gap :=
        div_le_div_of_nonneg_left (norm_nonneg _) hgap hden
      _ ≤ ‖2 * (roots n : Complex) * z₀‖ / gap := by
        apply div_le_div_of_nonneg_right _ hgap.le
        have hnormz : ‖z‖ ≤ ‖z₀‖ := by
          nlinarith [hmax z hz, norm_nonneg z, norm_nonneg z₀]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left hnormz
          (mul_nonneg (norm_nonneg 2) (norm_nonneg (roots n : Complex)))
      _ = u n := by
        dsimp [u, bound]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hroots n)]
        norm_num
        field_simp

theorem hadamardRootLogTerm_analyticOnNhd
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (n : Nat) :
    AnalyticOnNhd Complex (hadamardRootLogTerm (roots n))
      (hadamardRootNeighborhood roots) := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_hadamardRootNeighborhood roots)
  intro z hz
  unfold hadamardRootLogTerm
  fun_prop (disch := exact hadamardRootFactor_ne_zero hroots hsum hz n)

theorem hasSum_iteratedDeriv_hadamardRootLogTerm
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (order : Nat) :
    HasSum
      (fun n => iteratedDeriv order (hadamardRootLogTerm (roots n)) 0)
      (iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (roots n) z) 0) := by
  have hlocal :=
    (summableLocallyUniformlyOn_hadamardRootLogTerm hroots hsum).hasSumLocallyUniformlyOn
  have hder := hasSumLocallyUniformlyOn_iteratedDeriv
    (isOpen_hadamardRootNeighborhood roots) hlocal
    (hadamardRootLogTerm_analyticOnNhd hroots hsum) order
  exact hder.hasSum (zero_mem_hadamardRootNeighborhood hroots)

private theorem summable_root_pow
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {m : Nat} (hm : 1 ≤ m) :
    Summable fun n => roots n ^ m := by
  let total : Real := ∑' n, roots n
  have htotal : 0 ≤ total := tsum_nonneg hroots
  have hle (n : Nat) : roots n ≤ total :=
    hsum.le_tsum n fun k _ => hroots k
  refine (hsum.mul_right (total ^ (m - 1))).of_nonneg_of_le
    (fun n => pow_nonneg (hroots n) m) ?_
  intro n
  have hm' : m = 1 + (m - 1) := by omega
  have hpow : roots n ^ m = roots n * roots n ^ (m - 1) := by
    calc
      roots n ^ m = roots n ^ (1 + (m - 1)) :=
        congrArg (fun k => roots n ^ k) hm'
      _ = roots n * roots n ^ (m - 1) := by rw [pow_add, pow_one]
  calc
    roots n ^ m = roots n * roots n ^ (m - 1) := hpow
    _ ≤ roots n * total ^ (m - 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hroots n) (hle n) (m - 1)) (hroots n)

theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_rootSum
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) :
    iteratedDeriv order (logDeriv F) 0 =
      iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0 := by
  have heq : Set.EqOn (logDeriv F)
      (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z)
      (hadamardRootNeighborhood hF.roots) := by
    intro z hz
    simpa [hadamardRootLogTerm] using hF.logDeriv_eq_tsum hz
  have hevent : (logDeriv F) =ᶠ[nhds 0]
      (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) := by
    filter_upwards
      [(isOpen_hadamardRootNeighborhood hF.roots).mem_nhds
        (zero_mem_hadamardRootNeighborhood hF.roots_nonneg)] with z hz
    exact heq hz
  exact hevent.iteratedDeriv_eq order

theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) (horder : Even order) :
    iteratedDeriv order (logDeriv F) 0 = 0 := by
  rw [hF.iteratedDeriv_logDeriv_eq_rootSum]
  have hsum := hasSum_iteratedDeriv_hadamardRootLogTerm
    hF.roots_nonneg hF.roots_summable order
  have hzero : HasSum
      (fun _ : Nat => (0 : Complex))
      (iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0) :=
    HasSum.congr_fun hsum fun n =>
      (iteratedDeriv_hadamardRootLogTerm_even
        (hF.roots n) order horder).symm
  simpa using hzero.tsum_eq.symm



theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_odd
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    iteratedDeriv (2 * m - 1) (logDeriv F) 0 =
      -2 * (-1 : Complex) ^ m *
        (Nat.factorial (2 * m - 1) : Complex) *
          (∑' n, hF.roots n ^ m) := by
  rw [hF.iteratedDeriv_logDeriv_eq_rootSum]
  have hsum := hasSum_iteratedDeriv_hadamardRootLogTerm
    hF.roots_nonneg hF.roots_summable (2 * m - 1)
  have hsum' : HasSum
      (fun n => -2 * (-1 : Complex) ^ m *
        (Nat.factorial (2 * m - 1) : Complex) *
          (hF.roots n : Complex) ^ m)
      (iteratedDeriv (2 * m - 1)
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0) :=
    HasSum.congr_fun hsum fun n =>
      (iteratedDeriv_hadamardRootLogTerm_odd
        (hF.roots n) (hF.roots_nonneg n) m hm).symm
  rw [← hsum'.tsum_eq]
  rw [tsum_mul_left]
  rw [Complex.ofReal_tsum]
  apply congrArg
  apply tsum_congr
  intro n
  exact (Complex.ofReal_pow (hF.roots n) m).symm



def hadamardScalarCumulant (F : Complex → Complex) (order : Nat) : Real :=
  if order = 0 then 0
  else (iteratedDeriv (order - 1) (logDeriv F) 0).re



theorem normalizedIteratedDeriv_logDeriv_recurrence
    (F : Complex -> Complex) (hF : AnalyticAt Complex F 0)
    (hF0 : F 0 ≠ 0) (order : Nat) :
    iteratedDeriv (order + 1) F 0 / F 0 =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : Complex) *
          iteratedDeriv k (logDeriv F) 0 *
            (iteratedDeriv (order - k) F 0 / F 0) := by
  have hlog : AnalyticAt Complex (logDeriv F) 0 := by
    change AnalyticAt Complex (fun z => deriv F z / F z) 0
    exact hF.deriv.div hF hF0
  have hnonzero : Filter.Eventually (fun z : Complex => F z ≠ 0)
      (nhds (0 : Complex)) :=
    hF.continuousAt.eventually_ne hF0
  have hidentity : Filter.EventuallyEq (nhds (0 : Complex))
      (deriv F) (fun z => logDeriv F z * F z) := by
    filter_upwards [hnonzero] with z hz
    rw [logDeriv_apply, div_mul_cancel₀ _ hz]
  have hderivative := hidentity.iteratedDeriv_eq order
  change iteratedDeriv order (deriv F) 0 =
    iteratedDeriv order (fun z => logDeriv F z * F z) 0 at hderivative
  rw [← iteratedDeriv_succ'] at hderivative
  have hproduct :
      iteratedDeriv order (fun z => logDeriv F z * F z) 0 =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : Complex) *
            iteratedDeriv k (logDeriv F) 0 *
              iteratedDeriv (order - k) F 0 := by
    simpa only [Pi.mul_apply] using
      (iteratedDeriv_mul (n := order) (x := (0 : Complex))
        hlog.contDiffAt hF.contDiffAt)
  rw [hproduct] at hderivative
  calc
    iteratedDeriv (order + 1) F 0 / F 0 =
        (∑ k ∈ Finset.range (order + 1),
          (order.choose k : Complex) *
            iteratedDeriv k (logDeriv F) 0 *
              iteratedDeriv (order - k) F 0) / F 0 := by
      rw [hderivative]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem EvenHadamardFactorization.hadamardScalarCumulant_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    hadamardScalarCumulant F (2 * m) =
      -2 * (-1 : Real) ^ m * (Nat.factorial (2 * m - 1) : Real) *
        (∑' n, hF.roots n ^ m) := by
  unfold hadamardScalarCumulant
  rw [if_neg (by omega)]
  have hc := hF.iteratedDeriv_logDeriv_odd m hm
  have hcast :
      -2 * (-1 : Complex) ^ m *
          (Nat.factorial (2 * m - 1) : Complex) *
            (∑' n, hF.roots n ^ m) =
        ((-2 * (-1 : Real) ^ m *
          (Nat.factorial (2 * m - 1) : Real) *
            (∑' n, hF.roots n ^ m) : Real) : Complex) := by
    push_cast
    rfl
  rw [hcast] at hc
  exact congrArg Complex.re hc

@[simp] theorem hadamardScalarCumulant_zero (F : Complex → Complex) :
    hadamardScalarCumulant F 0 = 0 := by
  simp [hadamardScalarCumulant]

theorem EvenHadamardFactorization.hadamardScalarCumulant_odd
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) (horder : Odd order) :
    hadamardScalarCumulant F order = 0 := by
  obtain ⟨m, rfl⟩ := horder
  unfold hadamardScalarCumulant
  rw [if_neg (by omega)]
  have heven : Even (2 * m + 1 - 1) := by
    use m
    omega
  rw [hF.iteratedDeriv_logDeriv_even _ heven]
  rfl



theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant
    {F : Complex -> Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) :
    iteratedDeriv order (logDeriv F) 0 =
      (hadamardScalarCumulant F (order + 1) : Complex) := by
  unfold hadamardScalarCumulant
  rw [if_neg (by omega), Nat.add_sub_cancel]
  rcases Nat.even_or_odd order with horder | horder
  · rw [hF.iteratedDeriv_logDeriv_even order horder]
    rfl
  · obtain ⟨m, hm⟩ := horder
    have hindex : order = 2 * (m + 1) - 1 := by omega
    have hformula := hF.iteratedDeriv_logDeriv_odd (m + 1) (by omega)
    rw [← hindex] at hformula
    have hcast :
        -2 * (-1 : Complex) ^ (m + 1) *
            (Nat.factorial order : Complex) *
              (∑' n, hF.roots n ^ (m + 1)) =
          ((-2 * (-1 : Real) ^ (m + 1) *
            (Nat.factorial order : Real) *
              (∑' n, hF.roots n ^ (m + 1)) : Real) : Complex) := by
      push_cast
      rfl
    have hcomplex := hformula.trans hcast
    have hreal := congrArg Complex.re hcomplex
    calc
      iteratedDeriv order (logDeriv F) 0 =
          ((-2 * (-1 : Real) ^ (m + 1) *
            (Nat.factorial order : Real) *
              (∑' n, hF.roots n ^ (m + 1)) : Real) : Complex) := hcomplex
      _ = ((iteratedDeriv order (logDeriv F) 0).re : Complex) := by
        rw [hreal]
        simp only [Complex.ofReal_re]

theorem EvenHadamardFactorization.hadamardScalarCumulant_two
    {F : Complex → Complex} (hF : EvenHadamardFactorization F) :
    hadamardScalarCumulant F 2 = 2 * ∑' n, hF.roots n := by
  convert hF.hadamardScalarCumulant_even 1 (by omega) using 1 <;>
    norm_num

theorem EvenHadamardFactorization.hadamardScalarCumulant_four
    {F : Complex → Complex} (hF : EvenHadamardFactorization F) :
    hadamardScalarCumulant F 4 = -12 * ∑' n, hF.roots n ^ 2 := by
  convert hF.hadamardScalarCumulant_even 2 (by omega) using 1 <;>
    norm_num

private theorem EvenHadamardFactorization.abs_hadamardScalarCumulant_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    |hadamardScalarCumulant F (2 * m)| =
      2 * (Nat.factorial (2 * m - 1) : Real) *
        (∑' n, hF.roots n ^ m) := by
  rw [hF.hadamardScalarCumulant_even m hm]
  have hsum : 0 ≤ ∑' n, hF.roots n ^ m :=
    tsum_nonneg fun n => pow_nonneg (hF.roots_nonneg n) m
  rw [abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
    abs_neg_one_pow,
    abs_of_nonneg (Nat.cast_nonneg (Nat.factorial (2 * m - 1))),
    abs_of_nonneg hsum]
  ring

private theorem two_factorial_pred_le_factorial
    (m : Nat) (hm : 1 ≤ m) :
    2 * (Nat.factorial (2 * m - 1) : Real) ≤
      (Nat.factorial (2 * m) : Real) := by
  have hsucc : 2 * m - 1 + 1 = 2 * m := by omega
  have hfactorial : Nat.factorial (2 * m) =
      (2 * m) * Nat.factorial (2 * m - 1) := by
    rw [← hsucc, Nat.factorial_succ, hsucc]
  rw [hfactorial]
  push_cast
  have hfac : 0 ≤ (Nat.factorial (2 * m - 1) : Real) := by positivity
  have hmReal : (1 : Real) ≤ m := by exact_mod_cast hm
  nlinarith



def newmanRootCumulantRepresentation_of_evenHadamardFactorizations
    (F : Nat → Complex → Complex)
    (hF : ∀ scale, EvenHadamardFactorization (F scale)) :
    NewmanRootCumulantRepresentation
      (fun scale order => hadamardScalarCumulant (F scale) order) where
  roots := fun scale => (hF scale).roots
  roots_nonneg := fun scale => (hF scale).roots_nonneg
  roots_summable := fun scale => (hF scale).roots_summable
  order_zero := fun scale => hadamardScalarCumulant_zero (F scale)
  odd_order := fun scale order horder =>
    (hF scale).hadamardScalarCumulant_odd order horder
  even_power_sum := fun scale m hm => by
    rw [(hF scale).abs_hadamardScalarCumulant_even m (by omega)]
    exact mul_le_mul_of_nonneg_right
      (two_factorial_pred_le_factorial m (by omega))
      (tsum_nonneg fun n => pow_nonneg ((hF scale).roots_nonneg n) m)
  fourth_mass := fun scale => by
    rw [(hF scale).hadamardScalarCumulant_four]
    have hsum : 0 ≤ ∑' n, (hF scale).roots n ^ 2 :=
      tsum_nonneg fun n => sq_nonneg ((hF scale).roots n)
    rw [abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 12),
      abs_of_nonneg hsum]
  variance_mass := fun scale => by
    rw [(hF scale).hadamardScalarCumulant_two]
    have hsum : 0 ≤ ∑' n, (hF scale).roots n :=
      tsum_nonneg (hF scale).roots_nonneg
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsum)]
    linarith



theorem newmanFourthCumulantControl_of_evenHadamardFactorizations
    (F : Nat → Complex → Complex)
    (hF : ∀ scale, EvenHadamardFactorization (F scale)) :
    NewmanFourthCumulantControl
      (fun scale order => hadamardScalarCumulant (F scale) order) :=
  (newmanRootCumulantRepresentation_of_evenHadamardFactorizations F hF).newmanFourthCumulantControl



theorem newmanFourthCumulantControl_of_eq_hadamardScalarCumulant
    (F : Nat -> Complex -> Complex)
    (hF : forall scale, EvenHadamardFactorization (F scale))
    (cumulants : Nat -> Nat -> Real)
    (heq : forall scale order,
      cumulants scale order = hadamardScalarCumulant (F scale) order) :
    NewmanFourthCumulantControl cumulants := by
  have hcontrol :=
    newmanFourthCumulantControl_of_evenHadamardFactorizations F hF
  have hfun : cumulants =
      fun scale order => hadamardScalarCumulant (F scale) order := by
    funext scale order
    exact heq scale order
  rw [hfun]
  exact hcontrol

section FiniteIsingNewman

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]




theorem finiteIsingWeightedRawMoment_hadamard_recurrence
    (beta : Real) (a : V -> Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    finiteIsingWeightedRawMoment G beta a (order + 1) =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : Real) *
          hadamardScalarCumulant
            (finiteIsingWeightedFieldPartition G beta a) (k + 1) *
          finiteIsingWeightedRawMoment G beta a (order - k) := by
  let F := finiteIsingWeightedFieldPartition G beta a
  have hanalytic : AnalyticAt Complex F 0 :=
    finiteIsingWeightedFieldPartition_analyticOnNhd G beta a 0 (by simp)
  have hzero : F 0 ≠ 0 := Complex.ne_zero_of_re_pos
    (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  have hmoment (m : Nat) :
      iteratedDeriv m F 0 / F 0 =
        (finiteIsingWeightedRawMoment G beta a m : Complex) := by
    have h :=
      iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment
        G beta a m
    unfold finiteIsingWeightedMomentGeneratingFunction at h
    rw [iteratedDeriv_div_const] at h
    exact h
  have hrec := normalizedIteratedDeriv_logDeriv_recurrence
    F hanalytic hzero order
  dsimp [F] at hrec hmoment
  rw [hmoment (order + 1)] at hrec
  simp_rw [hF.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant] at hrec
  simp_rw [hmoment] at hrec
  exact_mod_cast hrec



theorem finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
    (beta : Real) (a : V -> Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    PhysicalIsing.finiteIsingWeightedCumulant G beta a order =
      hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G beta a) order := by
  unfold PhysicalIsing.finiteIsingWeightedCumulant
  apply scalarCumulantsOfMoments_eq_of_recurrence
  · exact PhysicalIsing.finiteIsingWeightedRawMoment_zero G beta a
  · exact hadamardScalarCumulant_zero _
  · exact finiteIsingWeightedRawMoment_hadamard_recurrence G beta a hF




theorem finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant
    (beta : Real) (a : V -> Real) (c : Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    scalarCumulantsOfMoments
        (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order =
      hadamardScalarCumulant
        (fun z => finiteIsingWeightedFieldPartition G beta a
          ((c : Complex) * z)) order := by
  let baseF := finiteIsingWeightedFieldPartition G beta a
  let scaledF : Complex -> Complex := fun z => baseF ((c : Complex) * z)
  have hscaled : EvenHadamardFactorization scaledF := hF.scaleArgument c
  have hbaseAnalytic : AnalyticOnNhd Complex baseF Set.univ :=
    finiteIsingWeightedFieldPartition_analyticOnNhd G beta a
  have hscaledAnalytic : AnalyticAt Complex scaledF 0 := by
    dsimp [scaledF]
    exact (hbaseAnalytic ((c : Complex) * 0) (by simp)).comp'
      (by fun_prop)
  have hzero : scaledF 0 ≠ 0 := by
    dsimp [scaledF, baseF]
    simpa using Complex.ne_zero_of_re_pos
      (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  have hbaseMoment (m : Nat) :
      iteratedDeriv m baseF 0 / baseF 0 =
        (finiteIsingWeightedRawMoment G beta a m : Complex) := by
    have h :=
      iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment
        G beta a m
    unfold finiteIsingWeightedMomentGeneratingFunction at h
    rw [iteratedDeriv_div_const] at h
    exact h
  have hscaledMoment (m : Nat) :
      iteratedDeriv m scaledF 0 / scaledF 0 =
        (c ^ m * finiteIsingWeightedRawMoment G beta a m : Real) := by
    have hcomp := congrFun
      (iteratedDeriv_comp_const_mul
        (n := m) (f := baseF) (hbaseAnalytic.contDiff) (c : Complex)) 0
    dsimp [scaledF] at hcomp ⊢
    rw [hcomp, mul_zero]
    calc
      (c : Complex) ^ m * iteratedDeriv m baseF 0 / baseF 0 =
          (c : Complex) ^ m * (iteratedDeriv m baseF 0 / baseF 0) := by ring
      _ = (c : Complex) ^ m *
          (finiteIsingWeightedRawMoment G beta a m : Complex) := by
        rw [hbaseMoment]
      _ = (c ^ m * finiteIsingWeightedRawMoment G beta a m : Real) := by
        push_cast
        rfl
  apply scalarCumulantsOfMoments_eq_of_recurrence
  · simp [PhysicalIsing.finiteIsingWeightedRawMoment_zero G beta a]
  · exact hadamardScalarCumulant_zero _
  · intro n
    have hrec := normalizedIteratedDeriv_logDeriv_recurrence
      scaledF hscaledAnalytic hzero n
    rw [hscaledMoment (n + 1)] at hrec
    simp_rw [hscaled.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant,
      hscaledMoment] at hrec
    exact_mod_cast hrec



theorem finiteIsingWeighted_newmanFourthCumulantControl
    (beta : Nat → Real) (a : Nat → V → Real)
    (hF : ∀ scale,
      FiniteIsingWeightedHadamardFactorization (G := G)
        (beta scale) (a scale)) :
    NewmanFourthCumulantControl
      (fun scale order => hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G (beta scale) (a scale)) order) :=
  newmanFourthCumulantControl_of_evenHadamardFactorizations
    (fun scale => finiteIsingWeightedFieldPartition G
      (beta scale) (a scale)) hF



theorem finiteIsingWeighted_physical_newmanFourthCumulantControl
    (beta : Nat -> Real) (a : Nat -> V -> Real)
    (hF : forall scale,
      FiniteIsingWeightedHadamardFactorization (G := G)
        (beta scale) (a scale)) :
    NewmanFourthCumulantControl
      (fun scale order =>
        PhysicalIsing.finiteIsingWeightedCumulant
          G (beta scale) (a scale) order) := by
  have hcontrol := finiteIsingWeighted_newmanFourthCumulantControl G beta a hF
  have heq :
      (fun scale order =>
        PhysicalIsing.finiteIsingWeightedCumulant
          G (beta scale) (a scale) order) =
      (fun scale order => hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G (beta scale) (a scale)) order) := by
    funext scale order
    exact finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
      G (beta scale) (a scale) (hF scale) order
  rw [heq]
  exact hcontrol

end FiniteIsingNewman

section CriticalFiniteBoxes

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB



theorem criticalFiniteBoxWeighted_physical_newmanFourthCumulantControl
    (d : Nat) (a : (n : Nat) -> sctBox d n -> Real)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
    NewmanFourthCumulantControl
      (fun n order => PhysicalIsing.finiteIsingWeightedCumulant
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) order) := by
  let F : Nat -> Complex -> Complex := fun n =>
    finiteIsingWeightedFieldPartition
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)
  apply newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hF
  intro n order
  exact finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) (hF n) order



theorem criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl
    (d : Nat) (hd : 2 <= d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
    NewmanFourthCumulantControl
      (fun n order => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d n hd (a n) order) := by
  let c : Nat -> Real := fun n =>
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n hd
  let F : Nat -> Complex -> Complex := fun n z =>
    finiteIsingWeightedFieldPartition
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)
        ((c n : Complex) * z)
  have hscaled : forall n, EvenHadamardFactorization (F n) := fun n =>
    (hF n).scaleArgument (c n)
  apply newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hscaled
  intro n order
  unfold PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
  exact finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) (c n)
      (hF n) order




theorem criticalFiniteBoxWeightedScaled_cumulantLimits
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n))
    (variance : Real)
    (hvariance : Tendsto
      (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d n (by omega) (a n) 2) atTop (nhds variance)) :
    forall order,
      Tendsto
        (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
          d n (by omega) (a n) order)
        atTop (nhds (scalarGaussianCumulant variance order)) := by
  apply cumulantLimits_of_newmanFourthControl _ variance
    (criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl
      d (by omega) a hF) hvariance
  exact PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero
    d hd a ha0 ha1

end CriticalFiniteBoxes

end

end StatMech.FrontierA
