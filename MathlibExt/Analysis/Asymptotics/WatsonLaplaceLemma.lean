/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MetaMathlibExt

private theorem watson_aux_integrable (m : ℝ) (hm : 0 < m) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-m * s)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := m)
    hs one_pos hm
  simp only [Real.rpow_one] at h
  apply h.congr
  filter_upwards with s
  rw [Real.rpow_natCast]

private theorem watson_aux_value (m : ℝ) (hm : 0 < m) (n : ℕ) :
    (∫ s in Set.Ioi 0, s ^ n * Real.exp (-m * s)) = (n.factorial : ℝ) / m ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := m)
    (by positivity) hm
  rw [Real.Gamma_nat_eq_factorial] at h
  have e1 : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
  have e3 : ((n : ℝ) + 1) = (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hfun : (fun t : ℝ => t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(m * t)))
      = (fun s : ℝ => s ^ n * Real.exp (-m * s)) := by
    funext s
    rw [e1, Real.rpow_natCast]
    have he : (-(m * s)) = (-m * s) := by ring
    rw [he]
  rw [hfun] at h
  have hRHS : (1 / m) ^ ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ)
      = ((n.factorial : ℕ) : ℝ) / m ^ (n + 1) := by
    rw [e3, Real.rpow_natCast, div_pow, one_pow]
    ring
  rw [hRHS] at h
  exact h

/-- **Watson's lemma for Laplace integrals.** Let $g : \mathbb{R} \to \mathbb{R}$ and let
$(c_k)_{k \ge 1}$ be real numbers such that for every $N \ge 0$,
$g(s) - \sum_{k=1}^{N} c_k s^k = O(s^{N+1})$ as $s \to 0^+$. Suppose there is $m_0 \in \mathbb{R}$
such that $s \mapsto g(s) e^{-ms}$ is integrable on $(0, \infty)$ for every $m \ge m_0$. Then
for every $N \ge 0$,
$\int_0^\infty g(s) e^{-ms} \, ds - \sum_{k=1}^{N} k! \, c_k / m^{k+1} = O(1 / m^{N+2})$ as
$m \to \infty$.

The case $N = 0$ of the hypothesis says $g(s) = O(s)$ as $s \to 0^+$: the expansion of $g$ has no
constant term.

Grounded record: `jis_grounded_f44808e9542400b9602c4bfc`
Concept: `jis_dep_4b8d33719e173348274b207f`
Source: `https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex`, lines 142-151
File SHA-256: `4420f4c929622a46f0e5623054b7cc4a699802cfb111b4dce5d1922af1e4c1d7`
Span SHA-256: `30a175909268f0c6c372ad6dba97f6edb373a35cf7eb26ecb5a0c0212eec8ee6`
Counts: 2 mentions / 1 paper / 1 proof use.
Proves `Wanted` entry `watson_laplace_integral_asymptotic`.
-/
theorem watson_laplace_integral_asymptotic
  (g : ℝ → ℝ) (c : ℕ → ℝ)
  (hlocal : ∀ N : ℕ, Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
    (fun s : ℝ => g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)))
    (fun s : ℝ => s ^ (N + 1)))
  (hconv : ∃ m₀ : ℝ, ∀ m ≥ m₀, MeasureTheory.IntegrableOn
    (fun s : ℝ => g s * Real.exp (-m * s)) (Set.Ioi 0)) :
  ∀ N : ℕ, Asymptotics.IsBigO Filter.atTop
    (fun m : ℝ => (∫ s in Set.Ioi 0, g s * Real.exp (-m * s)) -
      (∑ k ∈ Finset.range N,
        ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2)))
    (fun m : ℝ => 1 / m ^ (N + 2)) := by
  intro N
  obtain ⟨m₀, hconv⟩ := hconv
  have hloc := hlocal N
  rw [Asymptotics.isBigO_iff] at hloc
  obtain ⟨C, hC⟩ := hloc
  rw [eventually_nhdsWithin_iff, Filter.eventually_iff] at hC
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hC
  set δ : ℝ := ε / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    linarith
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  set M : ℝ := max m₀ 1 with hM
  have hm₀le : m₀ ≤ M := by
    rw [hM]
    exact le_max_left _ _
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  set C' : ℝ := max C 0 with hC'
  have hC'nn : 0 ≤ C' := by
    rw [hC']
    exact le_max_right _ _
  have hCle : C ≤ C' := by
    rw [hC']
    exact le_max_left _ _
  set K₁ : ℝ := Real.exp (M * δ / 2) *
    (∫ s in Set.Ioi δ, ‖g s * Real.exp (-M * s)‖) with hK₁
  set K₂ : ℝ := Real.exp (M * δ / 2) *
    (∫ s in Set.Ioi δ, ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) *
        Real.exp (-M * s)‖) with hK₂
  set Cexp : ℝ := (2 * ((N : ℝ) + 2) / δ) ^ (N + 2) with hCexp
  have hmem : ∀ s : ℝ, s ∈ Set.Ioc 0 δ →
      ‖g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ ≤ C * ‖s ^ (N + 1)‖ := by
    intro s hs
    have hsIoc := Set.mem_Ioc.mp hs
    have hball : s ∈ Metric.ball (0 : ℝ) ε := by
      have hlt : dist s (0 : ℝ) < ε := by
        rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hsIoc.1]
        linarith
      rwa [Metric.mem_ball]
    exact hεsub hball hsIoc.1
  have hdisj : Disjoint (Set.Ioc 0 δ) (Set.Ioi δ) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxle⟩ hxlt
    exact absurd (lt_of_le_of_lt hxle hxlt) (lt_irrefl _)
  have hunion : Set.Ioc 0 δ ∪ Set.Ioi δ = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi hδpos.le
  have hIoc_sub : Set.Ioc 0 δ ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  have hIoi_sub : Set.Ioi δ ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi hδpos.le
  have hsplit_gen : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn f (Set.Ioi 0) →
      (∫ s in Set.Ioi 0, f s) = (∫ s in Set.Ioc 0 δ, f s) + ∫ s in Set.Ioi δ, f s := by
    intro f hf
    have h := MeasureTheory.setIntegral_union₀ hdisj.aedisjoint
      measurableSet_Ioi.nullMeasurableSet
      (hf.mono_set hIoc_sub) (hf.mono_set hIoi_sub)
    rw [hunion] at h
    exact h
  have setInt_le : ∀ f : ℝ → ℝ, (∀ s ∈ Set.Ioi 0, 0 ≤ f s) →
      MeasureTheory.IntegrableOn f (Set.Ioi 0) →
      (∫ s in Set.Ioc 0 δ, f s) ≤ ∫ s in Set.Ioi 0, f s := by
    intro f hf0 hint
    have hsplit := hsplit_gen f hint
    have hnn : 0 ≤ ∫ s in Set.Ioi δ, f s := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact hf0 s (Set.Ioi_subset_Ioi hδpos.le hs)
    linarith
  have hPint : ∀ m : ℝ, 0 < m → MeasureTheory.IntegrableOn
      (fun s : ℝ => (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
      (Set.Ioi 0) := by
    intro m hm
    have hterm : ∀ k ∈ Finset.range N, MeasureTheory.IntegrableOn
        (fun s : ℝ => (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s)) (Set.Ioi 0) := by
      intro k _
      have h2 : (fun s : ℝ => (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
          = fun s : ℝ => c (k + 1) * (s ^ (k + 1) * Real.exp (-m * s)) := by
        ext s
        ring
      rw [h2]
      exact MeasureTheory.Integrable.const_mul
        (watson_aux_integrable m hm (k + 1)) (c (k + 1))
    have hfun : (fun s : ℝ => (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
        = (fun s : ℝ => ∑ k ∈ Finset.range N, ((c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))) := by
      funext s
      rw [Finset.sum_mul]
    rw [hfun]
    exact MeasureTheory.integrable_finsetSum _ (fun k hk => hterm k hk)
  have hPval : ∀ m : ℝ, 0 < m →
      (∫ s in Set.Ioi 0, (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
      = ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2) := by
    intro m hm
    have hterm : ∀ k ∈ Finset.range N, MeasureTheory.IntegrableOn
        (fun s : ℝ => (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s)) (Set.Ioi 0) := by
      intro k _
      have h2 : (fun s : ℝ => (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
          = fun s : ℝ => c (k + 1) * (s ^ (k + 1) * Real.exp (-m * s)) := by
        ext s
        ring
      rw [h2]
      exact MeasureTheory.Integrable.const_mul
        (watson_aux_integrable m hm (k + 1)) (c (k + 1))
    have hfun : (fun s : ℝ => (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
        = (fun s : ℝ => ∑ k ∈ Finset.range N, ((c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))) := by
      funext s
      rw [Finset.sum_mul]
    rw [hfun, MeasureTheory.integral_finsetSum _ (fun k hk => hterm k hk)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hcm : (∫ s in Set.Ioi 0, (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
        = c (k + 1) * (∫ s in Set.Ioi 0, s ^ (k + 1) * Real.exp (-m * s)) := by
      have h2 : (fun s : ℝ => (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
          = fun s : ℝ => c (k + 1) * (s ^ (k + 1) * Real.exp (-m * s)) := by
        ext s
        ring
      rw [h2]
      exact MeasureTheory.integral_const_mul _ _
    have hval := watson_aux_value m hm (k + 1)
    calc (∫ s in Set.Ioi 0, (c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s))
        = c (k + 1) * (∫ s in Set.Ioi 0, s ^ (k + 1) * Real.exp (-m * s)) := hcm
      _ = c (k + 1) * (((k + 1).factorial : ℝ) / m ^ (k + 1 + 1)) := by rw [hval]
      _ = ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2) := by
          have hexp : k + 1 + 1 = k + 2 := by omega
          rw [hexp]
          ring
  have hRint : ∀ m : ℝ, M ≤ m → MeasureTheory.IntegrableOn
      (fun s : ℝ => (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s))
      (Set.Ioi 0) := by
    intro m hm
    have hg := hconv m (le_trans hm₀le hm)
    have hp := hPint m (lt_of_lt_of_le hMpos hm)
    have hfun : (fun s : ℝ => (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s))
        = (fun s : ℝ => g s * Real.exp (-m * s)) -
            (fun s : ℝ => (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) * Real.exp (-m * s)) := by
      funext s
      exact sub_mul _ _ _
    rw [hfun]
    exact MeasureTheory.IntegrableOn.sub hg hp
  have hRsplit : ∀ m : ℝ, m₀ ≤ m → 0 < m →
      (∫ s in Set.Ioi 0, g s * Real.exp (-m * s))
      = (∫ s in Set.Ioi 0, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
          Real.exp (-m * s))
      + (∫ s in Set.Ioi 0, (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) *
          Real.exp (-m * s)) := by
    intro m hm0 hmpos
    have hg := hconv m hm0
    have hp := hPint m hmpos
    have hRcongr : (fun s : ℝ => (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s))
        = fun s : ℝ => (fun s : ℝ => g s * Real.exp (-m * s)) s -
            (fun s : ℝ => (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) *
            Real.exp (-m * s)) s := by
      funext s
      exact sub_mul _ _ _
    have hsub_eq := MeasureTheory.integral_sub hg hp
    rw [hRcongr, hsub_eq, sub_add_cancel]
  have hK1eq : (fun s : ℝ => ‖g s‖ * Real.exp (-M * (s - δ / 2)))
      = (fun s : ℝ => Real.exp (M * δ / 2) * ‖g s * Real.exp (-M * s)‖) := by
    funext s
    have hexp0 : ‖Real.exp (-M * s)‖ = Real.exp (-M * s) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-M * (s - δ / 2)) = Real.exp (M * δ / 2) * Real.exp (-M * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [norm_mul, hexp0, he]
    ring
  have hK1int : MeasureTheory.IntegrableOn
      (fun s : ℝ => ‖g s‖ * Real.exp (-M * (s - δ / 2))) (Set.Ioi δ) := by
    rw [hK1eq]
    exact MeasureTheory.IntegrableOn.mono_set
      (MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.norm (hconv M hm₀le))
          (Real.exp (M * δ / 2)))
      (Set.Ioi_subset_Ioi hδpos.le)
  have hK2eq : (fun s : ℝ => ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ *
      Real.exp (-M * (s - δ / 2)))
      = (fun s : ℝ => Real.exp (M * δ / 2) * ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1)) *
          Real.exp (-M * s)‖) := by
    funext s
    have hexp0 : ‖Real.exp (-M * s)‖ = Real.exp (-M * s) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-M * (s - δ / 2)) = Real.exp (M * δ / 2) * Real.exp (-M * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [norm_mul, hexp0, he]
    ring
  have hK2int : MeasureTheory.IntegrableOn
      (fun s : ℝ => ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2)))
      (Set.Ioi δ) := by
    rw [hK2eq]
    exact MeasureTheory.IntegrableOn.mono_set
      (MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.norm (hPint M hMpos))
          (Real.exp (M * δ / 2)))
      (Set.Ioi_subset_Ioi hδpos.le)
  have hJG : (∫ s in Set.Ioi δ, ‖g s‖ * Real.exp (-M * (s - δ / 2))) = K₁ := by
    rw [hK1eq, MeasureTheory.integral_const_mul, hK₁]
  have hJP : (∫ s in Set.Ioi δ, ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ *
      Real.exp (-M * (s - δ / 2))) = K₂ := by
    rw [hK2eq, MeasureTheory.integral_const_mul, hK₂]
  have hK₁nn : 0 ≤ K₁ := by
    rw [hK₁]
    refine mul_nonneg (Real.exp_pos _).le ?_
    apply MeasureTheory.integral_nonneg_of_ae
    apply Filter.Eventually.of_forall
    intro s
    exact norm_nonneg _
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂]
    refine mul_nonneg (Real.exp_pos _).le ?_
    apply MeasureTheory.integral_nonneg_of_ae
    apply Filter.Eventually.of_forall
    intro s
    exact norm_nonneg _
  have hNN : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hKne : (2 : ℝ) * ((N : ℝ) + 2) ≠ 0 := ne_of_gt (by positivity)
  have hexp : ∀ m : ℝ, M ≤ m → Real.exp (-m * δ / 2) ≤ Cexp / m ^ (N + 2) := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le hMpos hm
    have hmN : (0 : ℝ) < m ^ (N + 2) := pow_pos hmpos _
    set u : ℝ := m * δ / (2 * ((N : ℝ) + 2)) with hu
    have hu0 : 0 ≤ u := by
      rw [hu]
      exact div_nonneg (mul_nonneg hmpos.le hδpos.le) (mul_nonneg (by positivity) hNN.le)
    have hue : u ≤ Real.exp u := by
      have h := Real.add_one_le_exp u
      linarith
    have huK : u * (2 * ((N : ℝ) + 2) / δ) = m := by
      rw [hu]
      field_simp
    have hexpu : (Real.exp u) ^ (N + 2) = Real.exp (m * δ / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hu]
      push_cast
      field_simp
    have hCexp_nn : (0 : ℝ) ≤ Cexp := by
      rw [hCexp]
      apply pow_nonneg
      apply div_nonneg (mul_nonneg (by positivity) hNN.le) hδpos.le
    have hmain : Real.exp (-m * δ / 2) * m ^ (N + 2) ≤ Cexp := by
      have h1 : u ^ (N + 2) ≤ (Real.exp u) ^ (N + 2) := pow_le_pow_left₀ hu0 hue (N + 2)
      have h2 : Real.exp (-m * δ / 2) * (Real.exp u) ^ (N + 2) = 1 := by
        rw [hexpu, ← Real.exp_add]
        have h3 : -m * δ / 2 + m * δ / 2 = (0 : ℝ) := by ring
        rw [h3, Real.exp_zero]
      have hmK : m ^ (N + 2) = Cexp * u ^ (N + 2) := by
        rw [hCexp, ← huK, mul_pow]
        ring
      calc Real.exp (-m * δ / 2) * m ^ (N + 2)
          = Cexp * (Real.exp (-m * δ / 2) * u ^ (N + 2)) := by rw [hmK]; ring
        _ ≤ Cexp * (Real.exp (-m * δ / 2) * (Real.exp u) ^ (N + 2)) := by
            apply mul_le_mul_of_nonneg_left _ hCexp_nn
            apply mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Cexp := by rw [h2, mul_one]
    rw [le_div_iff₀ hmN]
    exact hmain
  have hnear : ∀ m : ℝ, M ≤ m →
      ‖∫ s in Set.Ioc 0 δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
          Real.exp (-m * s)‖
      ≤ C' * ((N + 1).factorial : ℝ) / m ^ (N + 2) := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le hMpos hm
    have hRsub := (hRint m hm).mono_set hIoc_sub
    have hnorm : MeasureTheory.Integrable
        (fun s : ℝ => ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s)‖)
        (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) :=
      MeasureTheory.Integrable.norm hRsub
    have hmono : MeasureTheory.Integrable
        (fun s : ℝ => C' * (s ^ (N + 1) * Real.exp (-m * s)))
        (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) :=
      MeasureTheory.IntegrableOn.mono_set
        (MeasureTheory.Integrable.const_mul (watson_aux_integrable m hmpos (N + 1)) C')
        hIoc_sub
    have hle : (∫ s in Set.Ioc 0 δ, ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s)‖)
        ≤ ∫ s in Set.Ioc 0 δ, C' * (s ^ (N + 1) * Real.exp (-m * s)) := by
      apply MeasureTheory.integral_mono_ae hnorm hmono
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hsIoc := Set.mem_Ioc.mp hs
      have hRs := hmem s hs
      have hexp0 : ‖Real.exp (-m * s)‖ = Real.exp (-m * s) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hspow : ‖s ^ (N + 1)‖ = s ^ (N + 1) := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_pos hsIoc.1]
      have hspow_nn : (0 : ℝ) ≤ s ^ (N + 1) := by
        rw [← hspow]
        exact norm_nonneg _
      calc ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s)‖
          = ‖g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-m * s) := by
            rw [norm_mul, hexp0]
        _ ≤ (C' * s ^ (N + 1)) * Real.exp (-m * s) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            calc ‖g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ ≤ C * ‖s ^ (N + 1)‖ := hRs
              _ = C * s ^ (N + 1) := by rw [hspow]
              _ ≤ C' * s ^ (N + 1) := mul_le_mul_of_nonneg_right hCle hspow_nn
        _ = C' * (s ^ (N + 1) * Real.exp (-m * s)) := by ring
    have hsub : (∫ s in Set.Ioc 0 δ, C' * (s ^ (N + 1) * Real.exp (-m * s)))
        ≤ ∫ s in Set.Ioi 0, C' * (s ^ (N + 1) * Real.exp (-m * s)) :=
      setInt_le (fun s : ℝ => C' * (s ^ (N + 1) * Real.exp (-m * s)))
        (fun s hs => by
          have hsI : (0 : ℝ) < s := hs
          exact mul_nonneg hC'nn (mul_nonneg (pow_nonneg hsI.le _) (Real.exp_pos _).le))
        (MeasureTheory.Integrable.const_mul (watson_aux_integrable m hmpos (N + 1)) C')
    have hval : (∫ s in Set.Ioi 0, C' * (s ^ (N + 1) * Real.exp (-m * s)))
        = C' * ((N + 1).factorial : ℝ) / m ^ (N + 2) := by
      have h1 := watson_aux_value m hmpos (N + 1)
      have hexpN : N + 1 + 1 = N + 2 := by omega
      rw [hexpN] at h1
      calc (∫ s in Set.Ioi 0, C' * (s ^ (N + 1) * Real.exp (-m * s)))
          = C' * ∫ s in Set.Ioi 0, s ^ (N + 1) * Real.exp (-m * s) :=
            MeasureTheory.integral_const_mul _ _
        _ = C' * (((N + 1).factorial : ℝ) / m ^ (N + 2)) := by rw [h1]
        _ = C' * ((N + 1).factorial : ℝ) / m ^ (N + 2) := by ring
    calc ‖∫ s in Set.Ioc 0 δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s)‖
        ≤ ∫ s in Set.Ioc 0 δ, ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
            Real.exp (-m * s)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ s in Set.Ioc 0 δ, C' * (s ^ (N + 1) * Real.exp (-m * s)) := hle
      _ ≤ ∫ s in Set.Ioi 0, C' * (s ^ (N + 1) * Real.exp (-m * s)) := hsub
      _ = C' * ((N + 1).factorial : ℝ) / m ^ (N + 2) := hval
  have hfar_pt : ∀ m : ℝ, M ≤ m → ∀ s : ℝ, s ∈ Set.Ioi δ →
      ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s)‖
      ≤ Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
        + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))) := by
    intro m hm s hs
    have hsI : δ < s := hs
    have hs2 : (0 : ℝ) < s - δ / 2 := by linarith
    have hexp_le : Real.exp (-m * (s - δ / 2)) ≤ Real.exp (-M * (s - δ / 2)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hs2.le
      linarith
    have hexp_split : Real.exp (-m * s) = Real.exp (-m * δ / 2) * Real.exp (-m * (s - δ / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp0 : ‖Real.exp (-m * s)‖ = Real.exp (-m * s) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s)‖
        = ‖g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-m * s) := by
          rw [norm_mul, hexp0]
      _ ≤ (‖g s‖ + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖) * Real.exp (-m * s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact norm_sub_le _ _
      _ = Real.exp (-m * δ / 2) *
          ((‖g s‖ + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖) *
          Real.exp (-m * (s - δ / 2))) := by
          rw [hexp_split]
          ring
      _ ≤ Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
          + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [add_mul]
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
  have hfar : ∀ m : ℝ, M ≤ m →
      ‖∫ s in Set.Ioi δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
          Real.exp (-m * s)‖
      ≤ (K₁ + K₂) * (Cexp / m ^ (N + 2)) := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le hMpos hm
    have hnorm : MeasureTheory.Integrable
        (fun s : ℝ => ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) * Real.exp (-m * s)‖)
        (MeasureTheory.volume.restrict (Set.Ioi δ)) :=
      MeasureTheory.Integrable.norm ((hRint m hm).mono_set hIoi_sub)
    have hK1e : MeasureTheory.Integrable (fun s : ℝ => ‖g s‖ * Real.exp (-M * (s - δ / 2)))
        (MeasureTheory.volume.restrict (Set.Ioi δ)) := hK1int
    have hK2e : MeasureTheory.Integrable
        (fun s : ℝ => ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ *
            Real.exp (-M * (s - δ / 2)))
        (MeasureTheory.volume.restrict (Set.Ioi δ)) := hK2int
    have hbound : MeasureTheory.Integrable
        (fun s : ℝ => Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
          + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))))
        (MeasureTheory.volume.restrict (Set.Ioi δ)) :=
      MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.add hK1int hK2int) _
    have hae : (fun s : ℝ => ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s)‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi δ)]
        (fun s : ℝ => Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
          + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2)))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact hfar_pt m hm s hs
    have hle := MeasureTheory.integral_mono_ae hnorm hbound hae
    have hval : (∫ s in Set.Ioi δ, Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
        + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))))
        = Real.exp (-m * δ / 2) * (K₁ + K₂) := by
      calc (∫ s in Set.Ioi δ, Real.exp (-m * δ / 2) * (‖g s‖ * Real.exp (-M * (s - δ / 2))
            + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))))
          = Real.exp (-m * δ / 2) * ∫ s in Set.Ioi δ, (‖g s‖ * Real.exp (-M * (s - δ / 2))
            + ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ * Real.exp (-M * (s - δ / 2))) :=
            MeasureTheory.integral_const_mul _ _
        _ = Real.exp (-m * δ / 2) * ((∫ s in Set.Ioi δ, ‖g s‖ * Real.exp (-M * (s - δ / 2)))
            + (∫ s in Set.Ioi δ, ‖(∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))‖ *
                Real.exp (-M * (s - δ / 2)))) := by
            congr 1
            exact MeasureTheory.integral_add hK1e hK2e
        _ = Real.exp (-m * δ / 2) * (K₁ + K₂) := by rw [hJG, hJP]
    have hE := hexp m hm
    have hKnn : (0 : ℝ) ≤ K₁ + K₂ := add_nonneg hK₁nn hK₂nn
    calc ‖∫ s in Set.Ioi δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s)‖
        ≤ ∫ s in Set.Ioi δ, ‖(g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
            Real.exp (-m * s)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ Real.exp (-m * δ / 2) * (K₁ + K₂) := by rw [← hval]; exact hle
      _ ≤ (Cexp / m ^ (N + 2)) * (K₁ + K₂) := mul_le_mul_of_nonneg_right hE hKnn
      _ = (K₁ + K₂) * (Cexp / m ^ (N + 2)) := by ring
  apply Asymptotics.IsBigO.of_bound (C' * ((N + 1).factorial : ℝ) + (K₁ + K₂) * Cexp)
  rw [Filter.eventually_atTop]
  refine ⟨M, fun m hm => ?_⟩
  show ‖(∫ s in Set.Ioi 0, g s * Real.exp (-m * s)) -
      (∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2))‖
    ≤ (C' * ((N + 1).factorial : ℝ) + (K₁ + K₂) * Cexp) * ‖1 / m ^ (N + 2)‖
  have hmpos : 0 < m := lt_of_lt_of_le hMpos hm
  have hDm : (∫ s in Set.Ioi 0, g s * Real.exp (-m * s))
      - (∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℕ) : ℝ) * c (k + 1) / m ^ (k + 2))
      = ∫ s in Set.Ioi 0, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
          Real.exp (-m * s) := by
    rw [hRsplit m (le_trans hm₀le hm) hmpos, hPval m hmpos, add_sub_cancel_right]
  rw [hDm]
  have hsplitR := hsplit_gen _ (hRint m hm)
  have hnorm1 : ‖1 / (m : ℝ) ^ (N + 2)‖ = 1 / m ^ (N + 2) := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (pow_pos hmpos _))]
  calc ‖∫ s in Set.Ioi 0, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
      Real.exp (-m * s)‖
      = ‖(∫ s in Set.Ioc 0 δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
          Real.exp (-m * s))
        + (∫ s in Set.Ioi δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
            Real.exp (-m * s))‖ := by
        rw [hsplitR]
    _ ≤ ‖∫ s in Set.Ioc 0 δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
        Real.exp (-m * s)‖
        + ‖∫ s in Set.Ioi δ, (g s - (∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1))) *
            Real.exp (-m * s)‖ :=
        norm_add_le _ _
    _ ≤ (C' * ((N + 1).factorial : ℝ) / m ^ (N + 2)) + ((K₁ + K₂) * (Cexp / m ^ (N + 2))) :=
        add_le_add (hnear m hm) (hfar m hm)
    _ = (C' * ((N + 1).factorial : ℝ) + (K₁ + K₂) * Cexp) * (1 / m ^ (N + 2)) := by ring
    _ = (C' * ((N + 1).factorial : ℝ) + (K₁ + K₂) * Cexp) * ‖1 / m ^ (N + 2)‖ := by rw [hnorm1]

end MetaMathlibExt
