/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The GPY–Maynard sieve: positivity reduction and the variational quantity `M_k`

The Goldston–Pintz–Yıldırım method detects many primes among `n + h₁, …, n + h_k` by showing
that `S(N, ρ) = ∑_{N ≤ n < 2N} (∑ᵢ 1_ℙ(n + hᵢ) - ρ) w_n` is positive for non-negative weights
`w_n`. This module proves the purely combinatorial and limiting part of the method: positivity
forces some `n` with more than `ρ` of the `n + hᵢ` prime, and Maynard's asymptotics for the two
sums `S₁`, `S₂` (taken as hypotheses) force infinitely many such `n` once `ρ < θ M_k / 2`.
It also defines Maynard's functionals `I_k`, `J_k^{(m)}` and the quantity `M_k`.

Source: J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383-413;
numbering of arXiv:1311.4600v3: Section 2, display (2.1); Section 4, Propositions 4.1 and 4.2
and the proof of Proposition 4.2, display (4.4).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.GPYMaynard

open Filter Topology MeasureTheory

/-- **Number of prime translates.** For a finite set `H` of natural numbers and `n : ℕ`, the
number of `h ∈ H` with `n + h` prime, i.e. `∑_{h ∈ H} 1_ℙ(n + h)` (Maynard, *Small gaps between
primes*, arXiv:1311.4600v3, the inner sum of (2.1)). -/
def primeShiftCount (H : Finset ℕ) (n : ℕ) : ℕ :=
  (H.filter fun h => (n + h).Prime).card

/-- **GPY detection principle, finite form.** Let `w ≥ 0` on a finite set `s` of natural
numbers, `H` a finite set of shifts and `ρ` real. If
`∑_{n ∈ s} (∑_{h ∈ H} 1_ℙ(n + h) - ρ) w_n > 0`, then some `n ∈ s` has more than `ρ` of the
`n + h` prime, that is at least `⌊ρ + 1⌋` of them (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Section 2, the paragraph after (2.1)). -/
theorem exists_lt_primeShiftCount_of_sum_pos (H : Finset ℕ) (s : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) (ρ : ℝ)
    (hpos : 0 < ∑ n ∈ s, ((primeShiftCount H n : ℝ) - ρ) * w n) :
    ∃ n ∈ s, ρ < primeShiftCount H n := by
  by_contra hcon
  push Not at hcon
  have hle : ∑ n ∈ s, ((primeShiftCount H n : ℝ) - ρ) * w n ≤ 0 :=
    Finset.sum_nonpos fun n hn =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hcon n hn)) (hw n hn)
  linarith

/-- **GPY detection principle over dyadic ranges.** If `w_N ≥ 0` for every `N` and
`∑_{N ≤ n < 2N} (∑_{h ∈ H} 1_ℙ(n + h) - ρ) w_N(n) > 0` for all sufficiently large `N`, then
infinitely many `n` have more than `ρ` of the `n + h` prime (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Section 2: "Thus if `S(N, ρ) > 0` for all large `N`, there are infinitely many
integers `n` for which at least `⌊ρ + 1⌋` of the `n + hᵢ` are prime"). -/
theorem infinite_lt_primeShiftCount_of_eventually_sum_pos (H : Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ N n, 0 ≤ w N n) (ρ : ℝ)
    (hpos : ∀ᶠ N in atTop,
      0 < ∑ n ∈ Finset.Ico N (2 * N), ((primeShiftCount H n : ℝ) - ρ) * w N n) :
    {n : ℕ | ρ < primeShiftCount H n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨N, hN, hNa⟩ := (hpos.and (eventually_gt_atTop a)).exists
  obtain ⟨n, hn, hρ⟩ :=
    exists_lt_primeShiftCount_of_sum_pos H _ (w N) (fun n _ => hw N n) ρ hN |>.imp
      fun n h => h
  exact ⟨n, hρ, lt_of_lt_of_le hNa (Finset.mem_Ico.mp hn).1⟩

/-- **From the asymptotics of `S₁` and `S₂` to infinitely many prime-rich translates.** Let
`w_N ≥ 0`, `S₁(N) = ∑_{N ≤ n < 2N} w_N(n)` and
`S₂(N) = ∑_{N ≤ n < 2N} (∑_{h ∈ H} 1_ℙ(n + h)) w_N(n)`. If `S₁(N) / B(N) → I` and
`S₂(N) / B(N) → J` for a normalisation `B(N) > 0` (eventually), and `ρ I < J`, then infinitely
many `n` have more than `ρ` of the `n + h` prime. This is the limiting step
`S = S₂ - ρ S₁ > 0` of the proof of Maynard's Proposition 4.2 (*Small gaps between primes*,
arXiv:1311.4600v3, display (4.4)). -/
theorem infinite_lt_primeShiftCount_of_tendsto (H : Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ N n, 0 ≤ w N n) (B : ℕ → ℝ) (hB : ∀ᶠ N in atTop, 0 < B N) (I J ρ : ℝ)
    (hS₁ : Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop (𝓝 I))
    (hS₂ : Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
      (primeShiftCount H n : ℝ) * w N n) / B N) atTop (𝓝 J))
    (hρ : ρ * I < J) :
    {n : ℕ | ρ < primeShiftCount H n}.Infinite := by
  refine infinite_lt_primeShiftCount_of_eventually_sum_pos H w hw ρ ?_
  have hlim := hS₂.sub (hS₁.const_mul ρ)
  have hev : ∀ᶠ N in atTop,
      0 < (∑ n ∈ Finset.Ico N (2 * N), (primeShiftCount H n : ℝ) * w N n) / B N -
        ρ * ((∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev, hB] with N hN hBN
  have hsum : ∑ n ∈ Finset.Ico N (2 * N), ((primeShiftCount H n : ℝ) - ρ) * w N n =
      ∑ n ∈ Finset.Ico N (2 * N), (primeShiftCount H n : ℝ) * w N n -
        ρ * ∑ n ∈ Finset.Ico N (2 * N), w N n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsum]
  rw [mul_div_assoc', div_sub_div_same, div_pos_iff_of_pos_right hBN] at hN
  exact hN

/-- **Prime-rich translates give short gaps between the `n`-th and `(n+m)`-th primes.** Let `H` be
a finite set of shifts with `b ≤ a + D` for all `a, b ∈ H`. If infinitely many `n` have more than
`m` of the `n + h`, `h ∈ H`, prime, then `p_{j+m} - p_j ≤ D` for infinitely many `j`, where
`p_j = Nat.nth Nat.Prime j` is the `j`-th prime counted from `p_0 = 2`. This is the step
"In particular, `lim inf_n (p_{n+r_k-1} - p_n) ≤ max_{i,j} (h_i - h_j)`" of Maynard,
*Small gaps between primes*, arXiv:1311.4600v3, Proposition 4.2, with `r_k - 1 = m`. -/
theorem frequently_nth_prime_add_sub_le_of_infinite (H : Finset ℕ) (m D : ℕ)
    (hD : ∀ a ∈ H, ∀ b ∈ H, b ≤ a + D)
    (hinf : {n : ℕ | (m : ℝ) < primeShiftCount H n}.Infinite) :
    ∃ᶠ j in atTop, Nat.nth Nat.Prime (j + m) - Nat.nth Nat.Prime j ≤ D := by
  refine Filter.frequently_atTop.mpr fun J₀ => ?_
  obtain ⟨n, hn, hnJ⟩ := hinf.exists_gt (Nat.nth Nat.Prime J₀)
  have hcount : m < primeShiftCount H n := by exact_mod_cast hn
  set S := H.filter fun h => (n + h).Prime with hS
  have hSne : S.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le m) hcount)
  set a := S.min' hSne with ha
  have haS : a ∈ S := Finset.min'_mem S hSne
  have haH : a ∈ H := (Finset.mem_filter.mp haS).1
  have hqa : (n + a).Prime := (Finset.mem_filter.mp haS).2
  set j := Nat.count Nat.Prime (n + a) with hj
  have hnthj : Nat.nth Nat.Prime j = n + a := Nat.nth_count hqa
  -- The shifted primes `n + h`, `h ∈ S`, all lie in `[n + a, n + a + D]`.
  have hsub : S.image (fun h => h - a) ⊆
      (Finset.range (D + 1)).filter fun k => (n + a + k).Prime := by
    intro k hk
    obtain ⟨h, hhS, rfl⟩ := Finset.mem_image.mp hk
    have hah : a ≤ h := Finset.min'_le S h hhS
    have hhH : h ∈ H := (Finset.mem_filter.mp hhS).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have := hD a haH h hhH
      omega
    · have hp := (Finset.mem_filter.mp hhS).2
      have : n + a + (h - a) = n + h := by omega
      rwa [this]
  have hinj : Set.InjOn (fun h => h - a) S := by
    intro x hx y hy hxy
    have hx' : a ≤ x := Finset.min'_le S x hx
    have hy' : a ≤ y := Finset.min'_le S y hy
    simp only at hxy
    omega
  have hcardS : S.card ≤ Nat.count (fun k => (n + a + k).Prime) (D + 1) := by
    rw [Nat.count_eq_card_filter_range, ← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hlt : j + m < Nat.count Nat.Prime (n + a + (D + 1)) := by
    rw [Nat.count_add]
    have : primeShiftCount H n = S.card := rfl
    omega
  have hnth : Nat.nth Nat.Prime (j + m) < n + a + (D + 1) := Nat.nth_lt_of_lt_count hlt
  refine ⟨j, ?_, ?_⟩
  · have hmono := Nat.count_monotone Nat.Prime (show Nat.nth Nat.Prime J₀ ≤ n + a by omega)
    rwa [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hmono
  · rw [hnthj]
    omega

/-- **Maynard's reduction for one weight profile.** Let `θ, ρ` be real, `I > 0` and `J` real
with `ρ < (θ / 2) (J / I)`. Suppose that for every small `δ > 0` there are weights `w_N ≥ 0` and
a normalisation `B(N) > 0` with `S₁(N) / B(N) → I` and `S₂(N) / B(N) → (θ / 2 - δ) J`, as
Maynard's Proposition 4.1 provides for `R = N^{θ/2 - δ}`, `I = I_k(F)` and `J = ∑_m J_k^{(m)}(F)`
when the primes have level of distribution `θ`. Then infinitely many `n` have more than `ρ` of
the `n + h` prime (Maynard, *Small gaps between primes*, arXiv:1311.4600v3, proof of
Proposition 4.2, display (4.4)). The asymptotics are hypotheses here; nothing about the
distribution of primes is proved. -/
theorem infinite_lt_primeShiftCount_of_maynard_asymptotics (H : Finset ℕ) (θ ρ I J : ℝ)
    (hI : 0 < I) (hρ : ρ < θ / 2 * (J / I)) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hasym : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ (w : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
      (∀ N n, 0 ≤ w N n) ∧ (∀ᶠ N in atTop, 0 < B N) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop (𝓝 I) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
        (primeShiftCount H n : ℝ) * w N n) / B N) atTop (𝓝 ((θ / 2 - δ) * J))) :
    {n : ℕ | ρ < primeShiftCount H n}.Infinite := by
  have hgap : 0 < θ / 2 * J - ρ * I := by
    have h1 : θ / 2 * (J / I) = (θ / 2 * J) / I := by ring
    rw [h1, lt_div_iff₀ hI] at hρ
    linarith
  set δ := min ((θ / 2 * J - ρ * I) / (2 * (|J| + 1))) (δ₀ / 2) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by linarith)
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨w, B, hw, hB, hS₁, hS₂⟩ := hasym δ hδpos hδlt
  refine infinite_lt_primeShiftCount_of_tendsto H w hw B hB I _ ρ hS₁ hS₂ ?_
  have hδle : δ * (2 * (|J| + 1)) ≤ θ / 2 * J - ρ * I := by
    have h1 : δ ≤ (θ / 2 * J - ρ * I) / (2 * (|J| + 1)) := min_le_left _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  have hJ : δ * J ≤ δ * |J| := mul_le_mul_of_nonneg_left (le_abs_self J) hδpos.le
  nlinarith [abs_nonneg J]

/-- **Maynard's simplex.** `R_k = {x ∈ [0, ∞)^k : x₁ + ⋯ + x_k ≤ 1}`, the support allowed for the
profile `F` (Maynard, *Small gaps between primes*, arXiv:1311.4600v3, Proposition 4.1). -/
def maynardSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- **Maynard's functional `I_k`.** `I_k(F) = ∫_{[0,1]^k} F(t)² dt` (Maynard, *Small gaps between
primes*, arXiv:1311.4600v3, Proposition 4.1). -/
noncomputable def maynardI (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : Fin k → ℝ) 1, F x ^ 2

/-- **Maynard's functional `J_k^{(m)}`.**
`J_k^{(m)}(F) = ∫_{[0,1]^{k-1}} (∫_0^1 F(t) dt_m)² dt₁ ⋯ dt_{m-1} dt_{m+1} ⋯ dt_k`, written as an
integral over the whole cube `[0,1]^k` of a function that does not depend on the `m`-th
coordinate (Maynard, *Small gaps between primes*, arXiv:1311.4600v3, Proposition 4.1). -/
noncomputable def maynardJ (k : ℕ) (m : Fin k) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : Fin k → ℝ) 1, (∫ t in (0 : ℝ)..1, F (Function.update x m t)) ^ 2

/-- **Admissible profiles for `M_k`.** `F : ℝ^k → ℝ` is measurable and bounded, vanishes off
Maynard's simplex `R_k`, and has `I_k(F) ≠ 0` and `J_k^{(m)}(F) ≠ 0` for every `m`. Maynard takes
Riemann-integrable `F` (*Small gaps between primes*, arXiv:1311.4600v3, Proposition 4.2). A
Riemann-integrable profile is bounded and agrees almost everywhere with a Borel-measurable one,
which has the same `I_k` and `J_k^{(m)}`; so this class contains an a.e.-equivalent of each of
Maynard's profiles. -/
def IsMaynardProfile (k : ℕ) (F : (Fin k → ℝ) → ℝ) : Prop :=
  Measurable F ∧ (∃ C : ℝ, ∀ x, |F x| ≤ C) ∧ (∀ x ∉ maynardSimplex k, F x = 0) ∧
    maynardI k F ≠ 0 ∧ ∀ m, maynardJ k m F ≠ 0

/-- **Maynard's ratio.** `(∑_{m=1}^{k} J_k^{(m)}(F)) / I_k(F)` (Maynard, *Small gaps between
primes*, arXiv:1311.4600v3, Proposition 4.2). -/
noncomputable def maynardRatio (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  (∑ m, maynardJ k m F) / maynardI k F

/-- **Maynard's variational quantity `M_k`.** The supremum of
`(∑_m J_k^{(m)}(F)) / I_k(F)` over admissible profiles `F` (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Proposition 4.2). It is a real supremum, so it carries Mathlib's junk value
`0` if the set of ratios is empty or unbounded above. -/
noncomputable def maynardM (k : ℕ) : ℝ :=
  sSup (maynardRatio k '' {F | IsMaynardProfile k F})

/-- **`I_k` of an admissible profile is positive.** -/
theorem maynardI_pos {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hF : IsMaynardProfile k F) :
    0 < maynardI k F :=
  lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg (F x)) (Ne.symm hF.2.2.2.1)

/-- **Admissible profiles exist.** For every `k` the indicator of the box `[0, 1/(k+1)]^k`, which
lies inside Maynard's simplex, is an admissible profile: it is bounded and measurable, and
`I_k` and every `J_k^{(m)}` are positive on it. Hence the set of ratios defining `M_k` is
nonempty. -/
theorem exists_isMaynardProfile (k : ℕ) : ∃ F, IsMaynardProfile k F := by
  set c : ℝ := 1 / (k + 1) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set box : Set (Fin k → ℝ) := Set.Icc 0 (fun _ => c) with hbox
  have hmem : ∀ x : Fin k → ℝ, x ∈ box ↔ ∀ i, 0 ≤ x i ∧ x i ≤ c := by
    intro x
    simp only [hbox, Set.mem_Icc, Pi.le_def, Pi.zero_apply]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have hboxcube : box ⊆ Set.Icc (0 : Fin k → ℝ) 1 := Set.Icc_subset_Icc le_rfl (fun _ => hc1)
  have hboxpos : 0 < volume box := by
    rw [hbox, Real.volume_Icc_pi]
    exact CanonicallyOrderedAdd.prod_pos.mpr fun i _ => by simp [hc0]
  have hcubefin : volume (Set.Icc (0 : Fin k → ℝ) 1) < ⊤ := isCompact_Icc.measure_lt_top
  refine ⟨box.indicator 1, measurable_one.indicator measurableSet_Icc, ⟨1, fun x => ?_⟩, ?_, ?_, ?_⟩
  · by_cases hx : x ∈ box <;> simp [hx]
  · intro x hx
    apply Set.indicator_of_notMem
    intro hxb
    rw [hmem] at hxb
    apply hx
    refine ⟨fun i => (hxb i).1, ?_⟩
    calc ∑ i, x i ≤ ∑ _i : Fin k, c := Finset.sum_le_sum fun i _ => (hxb i).2
      _ = k * c := by simp
      _ ≤ 1 := by
        rw [hc, mul_one_div, div_le_one (by positivity)]
        linarith
  · unfold maynardI
    have hsq : ∀ x, (box.indicator (1 : (Fin k → ℝ) → ℝ) x) ^ 2 = box.indicator 1 x := by
      intro x
      by_cases hx : x ∈ box <;> simp [hx]
    simp_rw [hsq]
    rw [integral_indicator measurableSet_Icc]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hboxcube]
    exact (ENNReal.toReal_pos hboxpos.ne' (lt_of_le_of_lt (measure_mono hboxcube) hcubefin).ne).ne'
  · intro m
    unfold maynardJ
    set S : Set (Fin k → ℝ) := Set.univ.pi fun i => if i = m then Set.univ else Set.Icc 0 c with hS
    have hSmeas : MeasurableSet S :=
      MeasurableSet.univ_pi fun i => by split_ifs <;> simp [measurableSet_Icc]
    have hinner : ∀ x, (∫ t in (0 : ℝ)..1, box.indicator 1 (Function.update x m t)) =
        S.indicator (fun _ => c) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        have hpt : ∀ t, box.indicator (1 : (Fin k → ℝ) → ℝ) (Function.update x m t) =
            (Set.Icc 0 c).indicator 1 t := by
          intro t
          have hiff : Function.update x m t ∈ box ↔ t ∈ Set.Icc 0 c := by
            rw [hmem, Set.mem_Icc]
            constructor
            · intro h
              simpa using h m
            · intro ht i
              by_cases him : i = m
              · subst him
                simpa using ht
              · rw [Function.update_of_ne him]
                have := hx i (Set.mem_univ i)
                simp only [him, ite_false] at this
                exact this
          by_cases ht : t ∈ Set.Icc 0 c
          · rw [Set.indicator_of_mem (hiff.mpr ht), Set.indicator_of_mem ht]
            rfl
          · rw [Set.indicator_of_notMem (fun h => ht (hiff.mp h)), Set.indicator_of_notMem ht]
        simp_rw [hpt]
        rw [intervalIntegral.integral_of_le zero_le_one, integral_indicator measurableSet_Icc]
        simp only [Pi.one_apply]
        rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          Measure.restrict_apply measurableSet_Icc]
        have hset : Set.Icc 0 c ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 c := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
          constructor
          · rintro ⟨⟨_, h2⟩, h3, _⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1.le, h2⟩, h1, h2.trans hc1⟩
        rw [hset, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hc0.le]
      · rw [Set.indicator_of_notMem hx]
        have hzero : ∀ t, box.indicator (1 : (Fin k → ℝ) → ℝ) (Function.update x m t) = 0 := by
          intro t
          apply Set.indicator_of_notMem
          intro hb
          apply hx
          intro i _
          rw [hmem] at hb
          by_cases him : i = m
          · simp [him]
          · have := hb i
            rw [Function.update_of_ne him] at this
            simpa [him] using this
        simp [hzero]
    simp_rw [hinner]
    have hsq : ∀ x, (S.indicator (fun _ => c) x) ^ 2 = S.indicator (fun _ => c ^ 2) x := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    simp_rw [hsq]
    rw [integral_indicator_const _ hSmeas, smul_eq_mul, measureReal_def,
      Measure.restrict_apply hSmeas]
    have hboxS : box ⊆ S ∩ Set.Icc 0 1 := by
      intro x hx
      refine ⟨fun i _ => ?_, hboxcube hx⟩
      rw [hmem] at hx
      change x i ∈ (if i = m then Set.univ else Set.Icc 0 c)
      split_ifs
      · exact Set.mem_univ _
      · exact ⟨(hx i).1, (hx i).2⟩
    have hpos : 0 < (volume (S ∩ Set.Icc (0 : Fin k → ℝ) 1)).toReal :=
      ENNReal.toReal_pos (lt_of_lt_of_le hboxpos (measure_mono hboxS)).ne'
        (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hcubefin).ne
    exact (mul_pos hpos (pow_pos hc0 2)).ne'

/-- **Maynard's Proposition 4.2, reduction to the asymptotics of Proposition 4.1.** Let `θ > 0`.
If `ρ < θ M_k / 2`, and for every admissible profile `F` and every small `δ > 0` there are
weights `w_N ≥ 0` with
`S₁(N) / B(N) → I_k(F)` and `S₂(N) / B(N) → (θ / 2 - δ) ∑_m J_k^{(m)}(F)` for a normalisation
`B(N) > 0`, then infinitely many `n` have more than `ρ` of the `n + h` prime, `h ∈ H`. With
`ρ = m` this gives `m + 1` primes; with `θ = 1 - ε` the condition reads `M_k > 2m / (1 - ε)`.
The weights are unconstrained: the hypothesis asks only for some non-negative weights with these
limits, which abstracts Maynard's Proposition 4.1 (proved there for smooth `F` with his sieve
weights). It is satisfiable for every admissible profile when `H` is admissible with `#H = k`,
`θ` is a level of distribution and `δ₀ ≤ θ / 2`: reweighting a translate with more than `c`
primes against one with none achieves any limit `c < θ M_k / 2` (Maynard, *Small gaps between
primes*, arXiv:1311.4600v3, Proposition 4.2 and its proof). -/
theorem infinite_lt_primeShiftCount_of_lt_maynardM (H : Finset ℕ) (k : ℕ) (θ ρ : ℝ)
    (hθ : 0 < θ)
    (hρ : ρ < θ * maynardM k / 2) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hasym : ∀ F, IsMaynardProfile k F → ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ (w : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
      (∀ N n, 0 ≤ w N n) ∧ (∀ᶠ N in atTop, 0 < B N) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop
        (𝓝 (maynardI k F)) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
        (primeShiftCount H n : ℝ) * w N n) / B N) atTop
        (𝓝 ((θ / 2 - δ) * ∑ m, maynardJ k m F))) :
    {n : ℕ | ρ < primeShiftCount H n}.Infinite := by
  have hlt : 2 * ρ / θ < maynardM k := by
    rw [div_lt_iff₀ hθ]
    linarith
  obtain ⟨F₀, hF₀⟩ := exists_isMaynardProfile k
  have hne : (maynardRatio k '' {F | IsMaynardProfile k F}).Nonempty :=
    ⟨_, F₀, hF₀, rfl⟩
  obtain ⟨r, ⟨F, hF, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne hlt
  refine infinite_lt_primeShiftCount_of_maynard_asymptotics H θ ρ (maynardI k F)
    (∑ m, maynardJ k m F) (maynardI_pos hF) ?_ δ₀ hδ₀ (hasym F hF)
  have hr' : 2 * ρ < maynardRatio k F * θ := (div_lt_iff₀ hθ).mp hr
  unfold maynardRatio at hr'
  nlinarith

end MathlibExt.NumberTheory.GPYMaynard
