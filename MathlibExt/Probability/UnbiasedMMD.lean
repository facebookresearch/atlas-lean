/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KernelMeanEmbedding
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

/-!
# The unbiased estimate of the squared MMD

For i.i.d. samples `x₁, …, x_m ~ P` and `y₁, …, y_n ~ Q`, the statistic

  `MMD_u² = 1/(m(m-1)) ∑_{i ≠ j} k(xᵢ, xⱼ) + 1/(n(n-1)) ∑_{i ≠ j} k(yᵢ, yⱼ)
      - 2/(mn) ∑_{i,j} k(xᵢ, yⱼ)`

(`mmdUnbiasedSq`, Gretton et al. 2012, equation (3)) is a sum of two U-statistics and a sample
average, and it is an unbiased estimate of the squared population MMD (`integral_mmdUnbiasedSq`,
Lemma 6). The proof computes the expectation of each kernel term from the two-dimensional
marginals of the product of the sample laws.

## References

* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, "A kernel two-sample
  test", *J. Mach. Learn. Res.* **13** (2012), 723–773, Lemma 6 and equation (3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.KernelMeanEmbedding

namespace MathlibExt.Probability.UnbiasedMMD

variable {X : Type*} [MeasurableSpace X]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [RKHS ℝ H X ℝ]

/-- **Unbiased empirical estimate of the squared MMD** (Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), Lemma 6, equation (3)). For samples `x₁, …, x_m` and `y₁, …, y_n` of
sizes `m, n ≥ 2`,
`MMD_u² = 1/(m(m-1)) ∑_{i ≠ j} k(xᵢ, xⱼ) + 1/(n(n-1)) ∑_{i ≠ j} k(yᵢ, yⱼ)
- 2/(mn) ∑_{i,j} k(xᵢ, yⱼ)`. For a sample of size `0` or `1`, which is excluded, there is no pair
`i ≠ j` and its U-statistic would be `0` (`0 / 0`), so the value would not be an estimate. -/
noncomputable def mmdUnbiasedSq {m n : ℕ} (_hm : 2 ≤ m) (_hn : 2 ≤ n) (x : Fin m → X)
    (y : Fin n → X) : ℝ :=
  ((m : ℝ) * (m - 1))⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (x i) (x j) +
    ((n : ℝ) * (n - 1))⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (y i) (y j) -
    2 * ((m : ℝ) * n)⁻¹ * ∑ i, ∑ j, kernelValue H (x i) (y j)

variable {H}

/-- **Two coordinates of an i.i.d. sample are independent copies.** For `i ≠ j`, the pair
`(xᵢ, xⱼ)` of an i.i.d. sample from `P` has law `P ⊗ P` (the independent copies `x, x'` of
Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Lemma 6). -/
theorem measurePreserving_pair_pi {m : ℕ} (μ : Measure X) [IsProbabilityMeasure μ] {i j : Fin m}
    (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin m → X => (x i, x j)) (Measure.pi fun _ : Fin m => μ)
      (μ.prod μ) := by
  have hind : iIndepFun (fun (k : Fin m) (ω : Fin m → X) => ω k)
      (Measure.pi fun _ : Fin m => μ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => measurable_id.aemeasurable
  have h2 : IndepFun (fun ω : Fin m → X => ω i) (fun ω => ω j) (Measure.pi fun _ : Fin m => μ) :=
    hind.indepFun hij
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 h2]
  rw [(measurePreserving_eval (fun _ => μ) i).map_eq,
    (measurePreserving_eval (fun _ => μ) j).map_eq]

variable {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem integral_kernel_comp {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    {ρ' : Measure X} {ρ'' : Measure X} [SFinite ρ'] [SFinite ρ'']
    (hρ' : Integrable (featureMap H) ρ') (hρ'' : Integrable (featureMap H) ρ'')
    {f : α → X × X} (hf : MeasurePreserving f ρ (ρ'.prod ρ'')) :
    Integrable (fun a => kernelValue H (f a).1 (f a).2) ρ ∧
      ∫ a, kernelValue H (f a).1 (f a).2 ∂ρ = ∫ z, kernelValue H z.1 z.2 ∂(ρ'.prod ρ'') := by
  have hint := integrable_kernelValue_prod hρ' hρ''
  refine ⟨(hf.integrable_comp hint.1).2 hint, ?_⟩
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable (by rw [hf.map_eq]; exact hint.1)]

/-- **The unbiased MMD statistic is unbiased** (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), Lemma 6). Let `P` and `Q` be probability measures with Bochner integrable feature
maps, and let `x₁, …, x_m` be i.i.d. from `P` and `y₁, …, y_n` i.i.d. from `Q`, independent,
with `m, n ≥ 2`. Then `E[MMD_u²] = MMD(P, Q)²`. -/
theorem integral_mmdUnbiasedSq {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hμ : Integrable (featureMap H) μ) (hν : Integrable (featureMap H) ν) :
    ∫ z, mmdUnbiasedSq H hm hn z.1 z.2 ∂((Measure.pi fun _ : Fin m => μ).prod
      (Measure.pi fun _ : Fin n => ν)) = mmd H μ ν ^ 2 := by
  set Pm := Measure.pi fun _ : Fin m => μ
  set Pn := Measure.pi fun _ : Fin n => ν
  set R := Pm.prod Pn
  have hfst : MeasurePreserving (Prod.fst : (Fin m → X) × (Fin n → X) → _) R Pm :=
    measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : (Fin m → X) × (Fin n → X) → _) R Pn :=
    measurePreserving_snd
  -- the three kinds of kernel terms
  have hxx : ∀ i j : Fin m, i ≠ j →
      Integrable (fun z : (Fin m → X) × (Fin n → X) => kernelValue H (z.1 i) (z.1 j)) R ∧
      ∫ z, kernelValue H (z.1 i) (z.1 j) ∂R = ∫ z, kernelValue H z.1 z.2 ∂(μ.prod μ) :=
    fun i j hij => integral_kernel_comp hμ hμ ((measurePreserving_pair_pi μ hij).comp hfst)
  have hyy : ∀ i j : Fin n, i ≠ j →
      Integrable (fun z : (Fin m → X) × (Fin n → X) => kernelValue H (z.2 i) (z.2 j)) R ∧
      ∫ z, kernelValue H (z.2 i) (z.2 j) ∂R = ∫ z, kernelValue H z.1 z.2 ∂(ν.prod ν) :=
    fun i j hij => integral_kernel_comp hν hν ((measurePreserving_pair_pi ν hij).comp hsnd)
  have hxy : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun z : (Fin m → X) × (Fin n → X) => kernelValue H (z.1 i) (z.2 j)) R ∧
      ∫ z, kernelValue H (z.1 i) (z.2 j) ∂R = ∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν) := by
    intro i j
    have hp : MeasurePreserving (fun z : (Fin m → X) × (Fin n → X) => (z.1 i, z.2 j)) R
        (μ.prod ν) :=
      ((measurePreserving_eval (fun _ => μ) i).prod (measurePreserving_eval (fun _ => ν) j))
    exact integral_kernel_comp hμ hν hp
  set a := ∫ z, kernelValue H z.1 z.2 ∂(μ.prod μ)
  set b := ∫ z, kernelValue H z.1 z.2 ∂(ν.prod ν)
  set c := ∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν)
  -- integrability of the double sums
  have ixx : Integrable (fun z : (Fin m → X) × (Fin n → X) =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.1 i) (z.1 j)) R :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      (hxx i j (Finset.ne_of_mem_erase hj).symm).1
  have iyy : Integrable (fun z : (Fin m → X) × (Fin n → X) =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.2 i) (z.2 j)) R :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      (hyy i j (Finset.ne_of_mem_erase hj).symm).1
  have ixy : Integrable (fun z : (Fin m → X) × (Fin n → X) =>
      ∑ i, ∑ j, kernelValue H (z.1 i) (z.2 j)) R :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hxy i j).1
  have Ixx : ∫ z, ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.1 i) (z.1 j) ∂R =
      (m : ℝ) * (m - 1) * a := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      (hxx i j (Finset.ne_of_mem_erase hj).symm).1]
    simp_rw [integral_finsetSum _ fun j hj => (hxx _ j (Finset.ne_of_mem_erase hj).symm).1]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      (hxx i j (Finset.ne_of_mem_erase hj).symm).2]
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have Iyy : ∫ z, ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.2 i) (z.2 j) ∂R =
      (n : ℝ) * (n - 1) * b := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      (hyy i j (Finset.ne_of_mem_erase hj).symm).1]
    simp_rw [integral_finsetSum _ fun j hj => (hyy _ j (Finset.ne_of_mem_erase hj).symm).1]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      (hyy i j (Finset.ne_of_mem_erase hj).symm).2]
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have Ixy : ∫ z, ∑ i, ∑ j, kernelValue H (z.1 i) (z.2 j) ∂R = (m : ℝ) * n * c := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hxy i j).1]
    simp_rw [integral_finsetSum _ fun j _ => (hxy _ j).1]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hxy i j).2]
    simp
    ring
  have hm' : (m : ℝ) * (m - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hn' : (n : ℝ) * (n - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hmn : (m : ℝ) * n ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have e1 : Integrable (fun z : (Fin m → X) × (Fin n → X) =>
      ((m : ℝ) * (m - 1))⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.1 i) (z.1 j) +
        ((n : ℝ) * (n - 1))⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, kernelValue H (z.2 i) (z.2 j)) R :=
    (ixx.const_mul _).add (iyy.const_mul _)
  simp only [mmdUnbiasedSq]
  rw [integral_sub e1 (ixy.const_mul _),
    integral_add (ixx.const_mul _) (iyy.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, Ixx, Iyy, Ixy, mmd_sq_eq hμ hν]
  change _ = a - 2 * c + b
  rw [inv_mul_cancel_left₀ hm', inv_mul_cancel_left₀ hn', mul_assoc 2,
    inv_mul_cancel_left₀ hmn]
  ring

end MathlibExt.Probability.UnbiasedMMD
