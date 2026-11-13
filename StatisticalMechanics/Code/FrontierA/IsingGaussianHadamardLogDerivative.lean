/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Code.FrontierA.IsingGaussianNewmanRootControl
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn









open scoped BigOperators

namespace StatMech.FrontierA

noncomputable section


def hadamardRootFactor (roots : Nat → Real) (n : Nat) (z : Complex) : Complex :=
  1 + (roots n : Complex) * z ^ 2


def hadamardRootProduct (roots : Nat → Real) (z : Complex) : Complex :=
  ∏' n, hadamardRootFactor roots n z

theorem multipliableLocallyUniformlyOn_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    MultipliableLocallyUniformlyOn (hadamardRootFactor roots) Set.univ := by
  unfold hadamardRootFactor
  refine ⟨fun z => ∏' n, (1 + (roots n : Complex) * z ^ 2), ?_⟩
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using
      tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let u : Nat → Real := fun n => roots n * ‖z₀‖ ^ 2
    have hu : Summable u := hsum.mul_right _
    exact hu.hasProdUniformlyOn_nat_one_add hcompact
      (.of_forall fun n z hz => by
        dsimp [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hroots n), norm_pow]
        exact mul_le_mul_of_nonneg_left (hmax z hz) (hroots n))
      (fun _ => by fun_prop)


def hadamardRootNeighborhood (roots : Nat → Real) : Set Complex :=
  {z | ‖z‖ ^ 2 * (∑' n, roots n) < 1}

theorem isOpen_hadamardRootNeighborhood (roots : Nat → Real) :
    IsOpen (hadamardRootNeighborhood roots) := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem zero_mem_hadamardRootNeighborhood
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n) :
    (0 : Complex) ∈ hadamardRootNeighborhood roots := by
  have htotal : 0 ≤ ∑' n, roots n := tsum_nonneg hroots
  simp [hadamardRootNeighborhood]

private theorem root_le_tsum
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (n : Nat) :
    roots n ≤ ∑' k, roots k := by
  exact hsum.le_tsum n fun k _ => hroots k

theorem hadamardRootFactor_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) (n : Nat) :
    hadamardRootFactor roots n z ≠ 0 := by
  have hterm : ‖(roots n : Complex) * z ^ 2‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hroots n), norm_pow]
    calc
      roots n * ‖z‖ ^ 2 ≤ (∑' k, roots k) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (root_le_tsum hroots hsum n) (sq_nonneg ‖z‖)
      _ = ‖z‖ ^ 2 * (∑' k, roots k) := mul_comm _ _
      _ < 1 := hz
  intro hzero
  have hone : (1 : Complex) = -((roots n : Complex) * z ^ 2) :=
    eq_neg_of_add_eq_zero_left hzero
  have hnorm : (1 : Real) = ‖(roots n : Complex) * z ^ 2‖ := by
    calc
      (1 : Real) = ‖(1 : Complex)‖ := by simp
      _ = ‖-((roots n : Complex) * z ^ 2)‖ := congrArg norm hone
      _ = ‖(roots n : Complex) * z ^ 2‖ := norm_neg _
  linarith

theorem summable_norm_hadamardRootFactor_sub_one
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    Summable fun n => ‖(roots n : Complex) * z ^ 2‖ := by
  have h := hsum.mul_right (‖z‖ ^ 2)
  apply h.congr
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hroots n), norm_pow]

theorem logDeriv_hadamardRootFactor
    (roots : Nat → Real) (n : Nat) (z : Complex) :
    logDeriv (hadamardRootFactor roots n) z =
      2 * (roots n : Complex) * z /
        (1 + (roots n : Complex) * z ^ 2) := by
  unfold hadamardRootFactor
  rw [logDeriv_apply]
  have hp := (hasDerivAt_id z).pow 2
  have hc := hp.const_mul (roots n : Complex)
  have h := hc.const_add 1
  have h' : HasDerivAt
      (fun w : Complex => 1 + (roots n : Complex) * w ^ 2)
      (2 * (roots n : Complex) * z) z := by
    convert h using 1 <;> simp <;> ring
  rw [h'.deriv]

theorem summable_logDeriv_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    Summable fun n => logDeriv (hadamardRootFactor roots n) z := by
  let total : Real := ∑' n, roots n
  let gap : Real := 1 - ‖z‖ ^ 2 * total
  have hgap : 0 < gap := by
    dsimp [gap, total]
    exact sub_pos.mpr hz
  let bound : Real := 2 * ‖z‖ / gap
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hmajorant : Summable fun n => roots n * bound :=
    hsum.mul_right bound
  apply hmajorant.of_norm_bounded
  intro n
  rw [logDeriv_hadamardRootFactor, norm_div]
  have hterm :
      ‖(roots n : Complex) * z ^ 2‖ ≤ ‖z‖ ^ 2 * total := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hroots n), norm_pow]
    calc
      roots n * ‖z‖ ^ 2 ≤ total * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (root_le_tsum hroots hsum n) (sq_nonneg ‖z‖)
      _ = ‖z‖ ^ 2 * total := mul_comm _ _
  have hden : gap ≤ ‖1 + (roots n : Complex) * z ^ 2‖ := by
    calc
      gap = 1 - ‖z‖ ^ 2 * total := rfl
      _ ≤ 1 - ‖(roots n : Complex) * z ^ 2‖ :=
        sub_le_sub_left hterm 1
      _ = ‖(1 : Complex)‖ - ‖-((roots n : Complex) * z ^ 2)‖ := by simp
      _ ≤ ‖(1 : Complex) - (-((roots n : Complex) * z ^ 2))‖ :=
        norm_sub_norm_le _ _
      _ = ‖1 + (roots n : Complex) * z ^ 2‖ := by ring_nf
  calc
    ‖2 * (roots n : Complex) * z‖ /
        ‖1 + (roots n : Complex) * z ^ 2‖ ≤
        ‖2 * (roots n : Complex) * z‖ / gap :=
      div_le_div_of_nonneg_left (norm_nonneg _) hgap hden
    _ = roots n * bound := by
      dsimp [bound]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hroots n)]
      norm_num
      field_simp

theorem hadamardRootProduct_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    hadamardRootProduct roots z ≠ 0 := by
  unfold hadamardRootProduct hadamardRootFactor
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    exact hadamardRootFactor_ne_zero hroots hsum hz n
  · exact summable_norm_hadamardRootFactor_sub_one hroots hsum z



theorem logDeriv_hadamardRootProduct_eq_tsum
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    logDeriv (hadamardRootProduct roots) z =
      ∑' n, 2 * (roots n : Complex) * z /
        (1 + (roots n : Complex) * z ^ 2) := by
  unfold hadamardRootProduct
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    (fun n => hadamardRootFactor_ne_zero hroots hsum hz n)
    (fun _ => by unfold hadamardRootFactor; fun_prop)
    (summable_logDeriv_hadamardRootFactor hroots hsum hz)
    (multipliableLocallyUniformlyOn_hadamardRootFactor hroots hsum)
    (hadamardRootProduct_ne_zero hroots hsum hz)]
  apply tsum_congr
  intro n
  exact logDeriv_hadamardRootFactor roots n z



structure EvenHadamardFactorization (F : Complex → Complex) where
  roots : Nat → Real
  roots_nonneg : ∀ n, 0 ≤ roots n
  roots_summable : Summable roots
  value_zero_ne : F 0 ≠ 0
  normalized_eq : ∀ z,
    F z / F 0 = hadamardRootProduct roots z



def EvenHadamardFactorization.scaleArgument
    {F : Complex -> Complex} (hF : EvenHadamardFactorization F)
    (c : Real) :
    EvenHadamardFactorization (fun z => F ((c : Complex) * z)) where
  roots := fun n => c ^ 2 * hF.roots n
  roots_nonneg := fun n => mul_nonneg (sq_nonneg c) (hF.roots_nonneg n)
  roots_summable := Summable.mul_left (c ^ 2) hF.roots_summable
  value_zero_ne := by simpa using hF.value_zero_ne
  normalized_eq := fun z => by
    simp only [mul_zero]
    rw [hF.normalized_eq ((c : Complex) * z)]
    unfold hadamardRootProduct hadamardRootFactor
    apply tprod_congr
    intro n
    push_cast
    ring



theorem EvenHadamardFactorization.logDeriv_eq_tsum
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    {z : Complex} (hz : z ∈ hadamardRootNeighborhood hF.roots) :
    logDeriv F z =
      ∑' n, 2 * (hF.roots n : Complex) * z /
        (1 + (hF.roots n : Complex) * z ^ 2) := by
  have hfun : (fun w => F w / F 0) = hadamardRootProduct hF.roots := by
    funext w
    exact hF.normalized_eq w
  have hlog := congrArg (fun f : Complex → Complex => logDeriv f z) hfun
  have hconst : (F 0)⁻¹ ≠ 0 := inv_ne_zero hF.value_zero_ne
  rw [show (fun w => F w / F 0) = (fun w => F w * (F 0)⁻¹) by
      funext w; simp [div_eq_mul_inv]] at hlog
  change logDeriv (fun w => F w * (F 0)⁻¹) z =
    logDeriv (hadamardRootProduct hF.roots) z at hlog
  rw [logDeriv_mul_const z (F 0)⁻¹ hconst] at hlog
  rw [hlog]
  exact logDeriv_hadamardRootProduct_eq_tsum
    hF.roots_nonneg hF.roots_summable hz

section FiniteIsing

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



abbrev FiniteIsingWeightedHadamardFactorization
    (beta : Real) (a : V → Real) : Type :=
  EvenHadamardFactorization (finiteIsingWeightedFieldPartition G beta a)

theorem finiteIsingWeightedFieldPartition_logDeriv_eq_tsum
    (beta : Real) (a : V → Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    {z : Complex} (hz : z ∈ hadamardRootNeighborhood hF.roots) :
    logDeriv (finiteIsingWeightedFieldPartition G beta a) z =
      ∑' n, 2 * (hF.roots n : Complex) * z /
        (1 + (hF.roots n : Complex) * z ^ 2) :=
  hF.logDeriv_eq_tsum hz

end FiniteIsing

end

end StatMech.FrontierA
