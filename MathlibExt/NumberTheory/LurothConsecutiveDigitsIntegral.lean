/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothBorelBernstein
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Integral zero-one law for functions of consecutive Lüroth digits

Summability or divergence of superlevel integrals controls the measure of the set on which a
function of consecutive digits meets or exceeds its threshold infinitely often.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Function

namespace MetaMathlibExt

namespace volume_lurothConsecutiveDigits_zero_one_integral

private noncomputable abbrev μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

private instance instIsProbabilityMeasureRestrictedVolume : IsProbabilityMeasure μ :=
  ⟨by simp [μ]⟩

private noncomputable def digitBlock {m : ℕ} (n : ℕ) (x : ℝ) (i : Fin m) : ℕ :=
  lurothDigitSeq x (n + i)

private theorem measurable_block {m : ℕ} {ν : Measure ℕ}
    (h : MeasurePreserving lurothDigitSeq μ (Measure.infinitePi fun _ : ℕ => ν)) (n : ℕ) :
    Measurable (digitBlock (m := m) n) :=
  (measurable_pi_iff.2 fun i : Fin m => measurable_pi_apply (n + (i : ℕ))).comp h.measurable

private theorem map_blocks {m : ℕ} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (h : MeasurePreserving lurothDigitSeq μ (Measure.infinitePi fun _ : ℕ => ν)) (r : ℕ) :
    μ.map (fun x k => digitBlock (m := m) (r + k * (m + 1)) x) =
      Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin m => ν) := by
  let f (p : ℕ × Fin m) := r + (p.1 * (m + 1) + p.2)
  have hf : Function.Injective f := by
    intro p q hpq
    have hpair : (p.1, p.2.castSucc) = (q.1, q.2.castSucc) :=
      (Nat.divModEquiv (m + 1)).symm.injective (Nat.add_left_cancel hpq)
    exact Prod.ext (congrArg (Prod.fst : ℕ × Fin (m + 1) → ℕ) hpair)
      (Fin.ext (congrArg (fun u : ℕ × Fin (m + 1) => (u.2 : ℕ)) hpair))
  let project (d : ℕ → ℕ) (p : ℕ × Fin m) := d (f p)
  let curry := MeasurableEquiv.curry ℕ (Fin m) ℕ
  have hproject : Measurable project := measurable_pi_iff.2 fun i => measurable_pi_apply (f i)
  have hcomp : (fun x k => digitBlock (m := m) (r + k * (m + 1)) x) =
      curry ∘ project ∘ lurothDigitSeq := by
    ext x k i
    simp [curry, project, f, digitBlock, Nat.add_assoc]
  rw [hcomp, ← Measure.map_map curry.measurable (hproject.comp h.measurable),
    ← Measure.map_map hproject h.measurable, h.map_eq,
    Measure.map_infinitePi_infinitePi_of_inj (f := f) hf]
  rw [show curry = MeasurableEquiv.curry ℕ (Fin m) ℕ from rfl,
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin m) => ν)]
  simp only [Measure.infinitePi_eq_pi]

private theorem map_block {m : ℕ} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (h : MeasurePreserving lurothDigitSeq μ (Measure.infinitePi fun _ : ℕ => ν)) (r : ℕ) :
    μ.map (digitBlock (m := m) r) = Measure.pi fun _ : Fin m => ν := by
  have he : digitBlock (m := m) r =
      (fun d : ℕ → Fin m → ℕ => d 0) ∘ (fun x k => digitBlock (r + k * (m + 1)) x) := by
    simp [Function.comp_def]
  rw [he, ← Measure.map_map (measurable_pi_apply 0)
    (measurable_pi_iff.2 fun k => measurable_block h (r + k * (m + 1))), map_blocks h,
    Measure.infinitePi_map_eval]

private def box {m : ℕ} (d : Fin m → ℕ) : Set (Fin m → ℝ) :=
  univ.pi fun i => Ico (d i : ℝ) ((d i : ℝ) + 1)

private theorem measurableSet_box {m : ℕ} (d : Fin m → ℕ) : MeasurableSet (box d) :=
  .univ_pi fun _ => measurableSet_Ico

private theorem floor_eq_of_mem_box {m : ℕ} {d : Fin m → ℕ} {x : Fin m → ℝ}
    (hx : x ∈ box d) : (fun i => ⌊x i⌋₊) = d := by
  funext i
  exact (Nat.floor_eq_iff (by
    exact (Nat.cast_nonneg (d i)).trans (mem_univ_pi.1 hx i).1)).2 (mem_univ_pi.1 hx i)

private theorem disjoint_box {m : ℕ} : Pairwise (Disjoint on (box (m := m))) := by
  intro d e h
  refine disjoint_left.2 fun x hx hy => h ?_
  exact (floor_eq_of_mem_box hx).symm.trans (floor_eq_of_mem_box hy)

private theorem volume_box {m : ℕ} (d : Fin m → ℕ) : volume (box d) = 1 := by
  simp [box, Real.volume_pi_Ico]

private noncomputable def density {m : ℕ} (x : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i, 1 / x i ^ 2)

private noncomputable def weight (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ((d : ℝ) * ((d : ℝ) - 1)))

private theorem density_eq_prod {m : ℕ} (x : Fin m → ℝ) :
    density x = ∏ i, ENNReal.ofReal (1 / x i ^ 2) := by
  unfold density
  exact ENNReal.ofReal_prod_of_nonneg fun _ _ => by positivity

private theorem measurable_density {m : ℕ} : Measurable (density (m := m)) := by
  change Measurable (fun x : Fin m → ℝ => density x)
  simp only [density_eq_prod]
  exact Finset.measurable_prod _ fun _ _ => by fun_prop

-- The integrand on a unit box is comparable to the mass of its digit tuple.
private theorem box_bounds {m : ℕ} (d : Fin m → ℕ) (hd : ∀ i, 2 ≤ d i) :
    (∫⁻ x in box d, density x) ≤ ∏ i, weight (d i) ∧
      (∏ i, weight (d i)) ≤ 6 ^ m * ∫⁻ x in box d, density x := by
  have hpoint (x : Fin m → ℝ) (hx : x ∈ box d) (i : Fin m) :
      ENNReal.ofReal (1 / x i ^ 2) ≤ weight (d i) ∧
        weight (d i) ≤ 6 * ENNReal.ofReal (1 / x i ^ 2) := by
    have hdi : (2 : ℝ) ≤ d i := by exact_mod_cast hd i
    obtain ⟨hl, hu⟩ := mem_univ_pi.1 hx i
    have hpos : 0 < (d i : ℝ) * ((d i : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have hxpos : 0 < x i := by linarith
    constructor
    · apply ENNReal.ofReal_le_ofReal
      apply one_div_le_one_div_of_le hpos
      rw [pow_two]
      exact mul_le_mul hl (by linarith) (by linarith) hxpos.le
    · have hx₂ : x i ≤ 2 * (d i : ℝ) := by linarith
      have hx₃ : x i ≤ 3 * ((d i : ℝ) - 1) := by linarith
      have hsq : x i ^ 2 ≤ 6 * ((d i : ℝ) * ((d i : ℝ) - 1)) := by
        rw [pow_two]
        calc
          x i * x i ≤ (2 * (d i : ℝ)) * (3 * ((d i : ℝ) - 1)) :=
            mul_le_mul hx₂ hx₃ hxpos.le (by linarith)
          _ = _ := by ring
      rw [weight, ← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_one_div]
      exact (div_le_div_iff₀ hpos (pow_pos hxpos 2)).2 (by simpa using hsq)
  constructor
  · calc
      (∫⁻ x in box d, density x) ≤ ∫⁻ _ in box d, ∏ i, weight (d i) := by
        apply setLIntegral_mono' (measurableSet_box d)
        intro x hx
        rw [density_eq_prod]
        exact Finset.prod_le_prod fun i _ => (hpoint x hx i).1
      _ = _ := by simp [lintegral_const, volume_box]
  · rw [← lintegral_const_mul _ measurable_density]
    calc
      (∏ i, weight (d i)) = ∫⁻ _ in box d, ∏ i, weight (d i) := by
        simp [lintegral_const, volume_box]
      _ ≤ _ := by
        apply setLIntegral_mono' (measurableSet_box d)
        intro x hx
        rw [density_eq_prod, ← show (∏ _ : Fin m, (6 : ℝ≥0∞)) = 6 ^ m by simp,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod fun i _ => (hpoint x hx i).2

private def eligible {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) : Set (Fin m → ℕ) :=
  {d | (∀ i, 2 ≤ d i) ∧ y ≤ F (fun i => (d i : ℝ))}

private theorem prob_superlevel {m : ℕ} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (hν : ∀ d : ℕ, ν {d} = if 2 ≤ d then weight d else 0)
    (F : (Fin m → ℝ) → ℝ) (y : ℝ) :
    (Measure.pi fun _ : Fin m => ν) {d | y ≤ F (fun i => (d i : ℝ))} =
      ∑' d : eligible F y, ∏ i, weight (d.val i) := by
  classical
  rw [← Measure.tsum_indicator_apply_singleton _ _ .of_discrete,
    tsum_subtype (eligible F y) (fun d => ∏ i, weight (d i))]
  apply tsum_congr
  intro d
  by_cases hy : y ≤ F (fun i => (d i : ℝ))
  · by_cases hd : ∀ i, 2 ≤ d i
    · simp [eligible, hy, hd, Measure.pi_singleton, hν]
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      have hz : ∏ j, ν {d j} = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hν, hi])
      simp [eligible, hy, hd, hz]
  · simp [eligible, hy]

private def superlevel {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 2 ≤ x i) ∧ y ≤ F x}

private theorem measurableSet_superlevel {m : ℕ} {F : (Fin m → ℝ) → ℝ}
    (hFm : Measurable F) (y : ℝ) : MeasurableSet (superlevel F y) := by
  have he : superlevel F y =
      (⋂ i : Fin m, (fun x : Fin m → ℝ => x i) ⁻¹' Ici (2 : ℝ)) ∩ F ⁻¹' Ici y := by
    ext x
    simp [superlevel]
  rw [he]
  exact (MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ici).inter
    (hFm measurableSet_Ici)

private theorem integral_bounds {m : ℕ} (F : (Fin m → ℝ) → ℝ) (hFm : Measurable F)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (M : ℝ) (hMp : 0 < M)
    (hM : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → F x ≤ M * F (fun i => (⌊x i⌋₊ : ℝ))) (y : ℝ) :
    (∫⁻ x in superlevel F (M * y), density x) ≤ (∑' d : eligible F y, ∏ i, weight (d.val i)) ∧
      (∑' d : eligible F y, ∏ i, weight (d.val i)) ≤
        6 ^ m * ∫⁻ x in superlevel F y, density x := by
  let B := ⋃ d : eligible F y, box d.val
  have hB : MeasurableSet B := .iUnion fun d => measurableSet_box d.val
  have hsum : (∫⁻ x in B, density x) = ∑' d : eligible F y, ∫⁻ x in box d.val, density x :=
    lintegral_iUnion (fun d => measurableSet_box d.val)
      (fun _ _ h => disjoint_box (Subtype.val_injective.ne h)) _
  have hlower : superlevel F (M * y) ⊆ B := by
    rintro x ⟨hx, hy⟩
    let d (i : Fin m) := ⌊x i⌋₊
    have hd (i : Fin m) : 2 ≤ d i := Nat.le_floor (by simpa using hx i)
    have hd' : y ≤ F (fun i => (d i : ℝ)) :=
      (mul_le_mul_iff_right₀ hMp).1 (by
        simpa only [mul_comm M] using hy.trans (hM x hx))
    refine mem_iUnion.2 ⟨⟨d, hd, hd'⟩, mem_univ_pi.2 fun i => ?_⟩
    exact ⟨Nat.floor_le (by linarith [hx i]), Nat.lt_floor_add_one _⟩
  have hupper : B ⊆ superlevel F y := by
    intro x hx
    obtain ⟨d, hd⟩ := mem_iUnion.1 hx
    have hdi (i : Fin m) : (2 : ℝ) ≤ (d.val i : ℝ) := by exact_mod_cast d.property.1 i
    have hle (i : Fin m) : (d.val i : ℝ) ≤ x i := (mem_univ_pi.1 hd i).1
    have hx' (i : Fin m) : 2 ≤ x i := (hdi i).trans (hle i)
    exact ⟨hx', d.property.2.trans (hmono hdi hx' hle)⟩
  constructor
  · calc
      (∫⁻ x in superlevel F (M * y), density x) ≤ ∫⁻ x in B, density x := by
        rw [← lintegral_indicator (measurableSet_superlevel hFm _), ← lintegral_indicator hB]
        exact lintegral_mono (indicator_le_indicator_of_subset hlower (fun _ => zero_le))
      _ = _ := hsum
      _ ≤ _ := tsum_le_tsum fun d => (box_bounds d.val d.property.1).1
  · calc
      (∑' d : eligible F y, ∏ i, weight (d.val i)) ≤
          ∑' d : eligible F y, 6 ^ m * ∫⁻ x in box d.val, density x :=
        tsum_le_tsum fun d => (box_bounds d.val d.property.1).2
      _ = 6 ^ m * ∫⁻ x in B, density x := by rw [hsum, ENNReal.tsum_mul_left]
      _ ≤ _ := by gcongr

-- A divergent series has a divergent residue class. Blocks in that class are disjoint.
private theorem limsup_blocks_eq_one {m : ℕ} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (h : MeasurePreserving lurothDigitSeq μ (Measure.infinitePi fun _ : ℕ => ν))
    (S : ℕ → Set (Fin m → ℕ)) (hdiv : ∑' n, μ (digitBlock n ⁻¹' S n) = ∞) :
    μ (limsup (fun n => digitBlock n ⁻¹' S n) atTop) = 1 := by
  let A (n : ℕ) := digitBlock n ⁻¹' S n
  have hsum : (∑' n, μ (A n)) =
      ∑ r : Fin (m + 1), ∑' k : ℕ, μ (A (r + k * (m + 1))) := by
    rw [← (Nat.divModEquiv (m + 1)).symm.tsum_eq (fun n => μ (A n)), tsum_prod',
      tsum_comm, tsum_fintype]
    simp only [Nat.divModEquiv_symm_apply, Nat.add_comm]
  obtain ⟨r, hr⟩ : ∃ r : Fin (m + 1), (∑' k : ℕ, μ (A (r + k * (m + 1)))) = ∞ := by
    have ht : (∑ r : Fin (m + 1), ∑' k : ℕ, μ (A (r + k * (m + 1)))) = ∞ :=
      hsum.symm.trans hdiv
    simpa only [ENNReal.sum_eq_top, Finset.mem_univ, true_and] using ht
  let index (k : ℕ) : ℕ := r + k * (m + 1)
  have h_indep : iIndepFun (fun k => digitBlock (m := m) (index k)) μ := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_block h (index k))).2
    rw [show (fun x k => digitBlock (m := m) (index k) x) =
        (fun x k => digitBlock (r + k * (m + 1)) x) from rfl, map_blocks h]
    simp_rw [map_block h]
  have h_meas (k : ℕ) : MeasurableSet (A (index k)) :=
    measurable_block h (index k) .of_discrete
  have h_indepSet : iIndepSet (A ∘ index) μ := by
    apply (iIndepSet_iff_meas_biInter h_meas).2
    intro s
    exact h_indep.measure_inter_preimage_eq_mul s (sets := S ∘ index) fun _ _ => .of_discrete
  have hfull := measure_limsup_eq_one h_meas h_indepSet hr
  have hsub : limsup (A ∘ index) atTop ⊆ limsup A atTop := by
    intro x
    simp only [mem_limsup_iff_frequently_mem, frequently_atTop, Function.comp_apply]
    intro hx n
    obtain ⟨k, hk, hxk⟩ := hx n
    have hk' : k ≤ k * (m + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos m)
    exact ⟨index k, by dsimp [index]; omega, hxk⟩
  have hle : μ (limsup A atTop) ≤ μ univ := measure_mono (subset_univ _)
  exact le_antisymm (by simpa only [measure_univ] using hle) (hfull ▸ measure_mono hsub)

end volume_lurothConsecutiveDigits_zero_one_integral

open volume_lurothConsecutiveDigits_zero_one_integral

/-- **Integral zero-one law for functions of consecutive Lüroth digits.** Let $m \in \mathbb{N}$
and let $F : \mathbb{R}^m \to \mathbb{R}$ be a measurable function that is positive on
$[2, \infty)^m$ and non-decreasing there for the coordinatewise order. Let $M \in \mathbb{R}$
satisfy $F(x) \le M F(\lfloor x_1 \rfloor, \dots, \lfloor x_m \rfloor)$ for every
$x \in [2, \infty)^m$, and for $y \in \mathbb{R}$ put
$$G(y) = \int_{\{x \in [2, \infty)^m : F(x) \ge y\}} \prod_{i=1}^{m} \frac{1}{x_i^2} \, dx.$$
Let $(\Psi(n))_{n \ge 0}$ be a real sequence, write $d_k(x)$ for the $k$-th Lüroth digit of
$x$, and let $E$ be the set of $x \in (0, 1]$ such that
$F(d_{n+1}(x), \dots, d_{n+m}(x)) \ge \Psi(n)$ for infinitely many $n$. If
$\sum_{n \ge 0} G(\Psi(n)) < \infty$ then $E$ has Lebesgue measure $0$, and if
$\sum_{n \ge 0} G(M \Psi(n)) = \infty$ then $E$ has Lebesgue measure $1$.

Here $M$ is any constant with this property (the paper takes the supremum; a larger $M$ only
weakens the divergence condition). Unlike the paper, $\Psi$ need not be positive.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 4, with (6)
and `G` from (7) (`integers-2024-A67-thm-4`). -/
public theorem volume_lurothConsecutiveDigits_zero_one_integral {m : ℕ}
    (F : (Fin m → ℝ) → ℝ) (hFm : Measurable F)
    (hpos : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → 0 < F x)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (M : ℝ)
    (hM : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → F x ≤ M * F (fun i => (⌊x i⌋₊ : ℝ)))
    (Ψ : ℕ → ℝ) :
    let G : ℝ → ℝ≥0∞ := fun y =>
      ∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x}, ENNReal.ofReal (∏ i, 1 / x i ^ 2)
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ F (fun i => (lurothDigitSeq x (n + i) : ℝ))}
    (∑' n, G (Ψ n) < ∞ → volume E = 0) ∧ (∑' n, G (M * Ψ n) = ∞ → volume E = 1) := by
  classical
  obtain ⟨ν, hprob, hν, hseq⟩ := measurePreserving_digitSeq
  let S (n : ℕ) : Set (Fin m → ℕ) := {d | Ψ n ≤ F (fun i => (d i : ℝ))}
  let A (n : ℕ) := digitBlock n ⁻¹' S n
  have hMp : 0 < M := by
    let a : Fin m → ℝ := fun _ => 2
    have ha : ∀ i, 2 ≤ a i := fun _ => le_rfl
    have hf := hM a ha
    have hfloor : (fun i => (⌊a i⌋₊ : ℝ)) = a := by
      funext i
      norm_num [a]
    rw [hfloor] at hf
    exact pos_of_mul_pos_left ((hpos a ha).trans_le hf) (hpos a ha).le
  let G (y : ℝ) := ∫⁻ x in superlevel F y, density x
  have hb (n : ℕ) : G (M * Ψ n) ≤ μ (A n) ∧ μ (A n) ≤ 6 ^ m * G (Ψ n) := by
    have he : μ (A n) = (Measure.pi fun _ : Fin m => ν) (S n) := by
      rw [show A n = digitBlock n ⁻¹' S n from rfl,
        ← Measure.map_apply (measurable_block hseq n) .of_discrete, map_block hseq]
    rw [he, show S n = _ from rfl, prob_superlevel hν]
    exact integral_bounds F hFm hmono M hMp hM (Ψ n)
  have he : volume {x ∈ Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ F (fun i => (lurothDigitSeq x (n + i) : ℝ))} =
      μ (limsup A atTop) := by
    rw [Measure.restrict_apply' measurableSet_Ioc]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_limsup_iff_frequently_mem, A, S, digitBlock, mem_preimage,
      mem_ofPred_eq]
    exact and_comm
  change (∑' n, G (Ψ n) < ∞ → _ = 0) ∧ (∑' n, G (M * Ψ n) = ∞ → _ = 1)
  rw [he]
  constructor
  · intro hc
    apply measure_limsup_atTop_eq_zero
    have hfinite : (6 : ℝ≥0∞) ^ m * (∑' n, G (Ψ n)) < ∞ :=
      ENNReal.mul_lt_top (ENNReal.pow_lt_top (by norm_num)) hc
    rw [← ENNReal.tsum_mul_left] at hfinite
    exact ((tsum_le_tsum fun n => (hb n).2).trans_lt hfinite).ne
  · intro hd
    apply limsup_blocks_eq_one hseq S
    exact top_unique (hd ▸ tsum_le_tsum fun n => (hb n).1)

end MetaMathlibExt
