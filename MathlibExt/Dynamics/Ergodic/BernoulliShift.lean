/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.Mixing
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Tactic.Linarith

/-!
# Bernoulli shifts are mixing

The Bernoulli scheme with distribution `p` is the one-sided left shift `x ↦ (n ↦ x (n + 1))` on
`ℕ → S` with the product measure `p^ℕ = Measure.infinitePi (fun _ ↦ p)`: the dynamical form of a
sequence of independent identically distributed trials. It is mixing, whence ergodic.

The proof follows the textbook one. A cylinder event `A` constrains finitely many coordinates,
all `< n` for `n` large, while `σ⁻ⁿ B` only depends on the coordinates `≥ n`; the coordinates
are independent under the product measure, so `μ (A ∩ σ⁻ⁿ B) = μ A * μ B` exactly. A general
measurable `A` is approximated in measure by cylinders, which form a ring of sets generating the
product σ-algebra.

## Main results

* `shift`, `twoSidedShift`: Mathlib's full shift by `1` on `ℕ → S` and on `ℤ → S`.
* `measurePreserving_shift`: the shift preserves `p^ℕ`.
* `measure_cylinder_inter_preimage_iterate`: exact independence of a cylinder and `σ⁻ⁿ B` for
  large `n`.
* `isMixing_shift`: Bernoulli shifts are mixing (O. Sarig, *Lecture Notes on Ergodic Theory*,
  Proposition 1.7, stated there for finite alphabets; the proof here works for any probability
  space `(S, p)`).

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, §1.5.3 and Proposition 1.7,
  https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.BernoulliShift

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.Mixing
open scoped ENNReal symmDiff

variable {S : Type*} [MeasurableSpace S]

/-- **The one-sided left shift.** `shift x = (x 1, x 2, x 3, …)` for a sequence
`x = (x 0, x 1, x 2, …)` in `ℕ → S`. It is Mathlib's full shift by `1` on configurations
indexed by `ℕ`, `SymbolicDynamics.FullShift.shift 1`, under a short name. -/
def shift : (ℕ → S) → ℕ → S := SymbolicDynamics.FullShift.shift (1 : ℕ)

/-- **The two-sided left shift.** `twoSidedShift x = (n ↦ x (1 + n))` on bi-infinite sequences
`x : ℤ → S`, Mathlib's full shift by `1` on configurations indexed by `ℤ`; it is invertible, the
setting of invertible Bernoulli schemes. -/
def twoSidedShift : (ℤ → S) → ℤ → S := SymbolicDynamics.FullShift.shift (1 : ℤ)

omit [MeasurableSpace S] in
/-- **The shift reads the next symbol.** `shift x n = x (n + 1)`. -/
theorem shift_apply (x : ℕ → S) (n : ℕ) : shift x n = x (n + 1) := by
  simp only [shift, SymbolicDynamics.FullShift.shift_apply, Nat.add_comm]

omit [MeasurableSpace S] in
/-- **Iterates of the shift.** `(shift^[n] x) k = x (k + n)`. -/
theorem shift_iterate_apply (n : ℕ) (x : ℕ → S) (k : ℕ) : shift^[n] x k = x (k + n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, shift_apply]
    congr 1

/-- **The shift is measurable** for the product σ-algebra. -/
theorem measurable_shift : Measurable (shift (S := S)) :=
  Measurable.of_eval fun n => measurable_pi_apply (1 + n)

/-- **The shift preserves the product measure** `p^ℕ` (Sarig, *Lecture Notes on Ergodic
Theory*, §1.5.3). -/
theorem measurePreserving_shift (p : Measure S) [IsProbabilityMeasure p] :
    MeasurePreserving shift (Measure.infinitePi fun _ : ℕ => p)
      (Measure.infinitePi fun _ : ℕ => p) :=
  ⟨measurable_shift,
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => p) (f := fun i => 1 + i)
      (add_right_injective 1)⟩

/-- **A cylinder event is independent of the far future.** If the cylinder `cylinder s T` only
constrains coordinates `< n`, then for every measurable `B`,
`μ (cylinder s T ∩ σ⁻ⁿ B) = μ (cylinder s T) * μ B` under the product measure `μ = p^ℕ`: the
cylinder is measurable for the coordinates in `s`, `σ⁻ⁿ B` for the coordinates `≥ n`, and
coordinates are independent. -/
theorem measure_cylinder_inter_preimage_iterate (p : Measure S) [IsProbabilityMeasure p]
    {s : Finset ℕ} {T : Set (s → S)} (hT : MeasurableSet T) {B : Set (ℕ → S)}
    (hB : MeasurableSet B) {n : ℕ} (hn : ∀ i ∈ s, i < n) :
    (Measure.infinitePi fun _ : ℕ => p) (cylinder s T ∩ shift^[n] ⁻¹' B) =
      (Measure.infinitePi fun _ : ℕ => p) (cylinder s T) *
        (Measure.infinitePi fun _ : ℕ => p) B := by
  set μ := Measure.infinitePi fun _ : ℕ => p
  set m : ℕ → MeasurableSpace (ℕ → S) := fun i => MeasurableSpace.comap (fun ω => ω i) ‹_›
  have hind : iIndep m μ :=
    (iIndepFun_iff_iIndep _ _ _).1
      (iIndepFun_infinitePi (P := fun _ : ℕ => p) (X := fun _ (x : S) => x)
        fun _ => measurable_id)
  have hle : ∀ i, m i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hdisj : Disjoint (s : Set ℕ) {i | n ≤ i} :=
    Set.disjoint_left.2 fun i hi hi' => absurd (hn i hi) (not_lt.2 hi')
  have hI := indep_iSup_of_disjoint hle hind hdisj
  have hA : MeasurableSet[⨆ i ∈ (s : Set ℕ), m i] (cylinder s T) := by
    have hmeas : Measurable[⨆ i ∈ (s : Set ℕ), m i] (fun (ω : ℕ → S) (i : s) => ω i) := by
      refine @Measurable.of_eval _ _ _ (⨆ i ∈ (s : Set ℕ), m i) _ _ fun i => ?_
      exact measurable_iff_comap_le.2 (le_iSup₂_of_le (f := fun j (_ : j ∈ (s : Set ℕ)) => m j)
        (i : ℕ) (Finset.mem_coe.2 i.2) le_rfl)
    exact hmeas hT
  have hC : MeasurableSet[⨆ i ∈ {i | n ≤ i}, m i] (shift^[n] ⁻¹' B) := by
    have hmeas : Measurable[⨆ i ∈ {i | n ≤ i}, m i] (shift^[n] : (ℕ → S) → ℕ → S) := by
      refine @Measurable.of_eval _ _ _ (⨆ i ∈ {i | n ≤ i}, m i) _ _ fun k => ?_
      have hk : (fun ω : ℕ → S => shift^[n] ω k) = fun ω => ω (k + n) :=
        funext fun ω => shift_iterate_apply n ω k
      rw [hk]
      exact measurable_iff_comap_le.2 (le_iSup₂_of_le (f := fun j (_ : j ∈ {i | n ≤ i}) => m j)
        (k + n) (by simp) le_rfl)
    exact hmeas hB
  rw [(Indep_iff _ _ _).1 hI _ _ hA hC,
    ((measurePreserving_shift p).iterate n).measure_preimage hB.nullMeasurableSet]

/-- **Bernoulli shifts are mixing.** For every probability space `(S, p)`, the one-sided left
shift on `ℕ → S` with the product measure `p^ℕ` is mixing, whence ergodic (O. Sarig, *Lecture
Notes on Ergodic Theory*, Proposition 1.7, for finite alphabets `S`). -/
theorem isMixing_shift (p : Measure S) [IsProbabilityMeasure p] :
    IsMixing shift (Measure.infinitePi fun _ : ℕ => p) where
  measurePreserving := measurePreserving_shift p
  tendsto_measure_inter_preimage A B hA hB := by
    set μ := Measure.infinitePi fun _ : ℕ => p
    rw [← ENNReal.tendsto_toReal_iff (fun n => measure_ne_top μ _)
      (ENNReal.mul_ne_top (measure_ne_top μ A) (measure_ne_top μ B))]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε3 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨A', hA'C, hA'⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
      isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        Set.singleton_subset_iff.2 (univ_mem_measurableCylinders _), by simp⟩
      generateFrom_measurableCylinders.symm hA hε3
    obtain ⟨s, T, hT, rfl⟩ := (mem_measurableCylinders _).1 hA'C
    refine ⟨s.sup id + 1, fun n hn => ?_⟩
    have hn' : ∀ i ∈ s, i < n := fun i hi =>
      lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)) hn
    have key : μ (cylinder s T ∩ shift^[n] ⁻¹' B) = μ (cylinder s T) * μ B :=
      measure_cylinder_inter_preimage_iterate p hT hB hn'
    have hA'm : MeasurableSet (cylinder s T) := MeasurableSet.cylinder (α := fun _ : ℕ => S) s hT
    have hCm : MeasurableSet (shift^[n] ⁻¹' B) := hB.preimage (measurable_shift.iterate n)
    have hd : μ.real (cylinder s T ∆ A) < ε / 3 := by
      have := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hA'
      rwa [ENNReal.toReal_ofReal (by linarith)] at this
    have h1 : |μ.real (cylinder s T ∩ shift^[n] ⁻¹' B) - μ.real (A ∩ shift^[n] ⁻¹' B)|
        ≤ μ.real (cylinder s T ∆ A) := by
      refine (abs_measureReal_sub_le_measureReal_symmDiff (hA'm.inter hCm).nullMeasurableSet
        (hA.inter hCm).nullMeasurableSet).trans (measureReal_mono ?_)
      rw [← Set.inter_symmDiff_distrib_right]
      exact Set.inter_subset_left
    have h2 : |μ.real (cylinder s T) - μ.real A| ≤ μ.real (cylinder s T ∆ A) :=
      abs_measureReal_sub_le_measureReal_symmDiff hA'm.nullMeasurableSet hA.nullMeasurableSet
    have hkey : μ.real (cylinder s T ∩ shift^[n] ⁻¹' B) = μ.real (cylinder s T) * μ.real B := by
      simp only [measureReal_def, key, ENNReal.toReal_mul]
    have hB1 : μ.real B ≤ 1 := measureReal_le_one
    have hB0 : 0 ≤ μ.real B := measureReal_nonneg
    rw [Real.dist_eq, ENNReal.toReal_mul]
    change |μ.real (A ∩ shift^[n] ⁻¹' B) - μ.real A * μ.real B| < ε
    have h3 : |μ.real (cylinder s T) * μ.real B - μ.real A * μ.real B|
        ≤ μ.real (cylinder s T ∆ A) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hB0]
      calc |μ.real (cylinder s T) - μ.real A| * μ.real B
          ≤ |μ.real (cylinder s T) - μ.real A| * 1 :=
            mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
        _ ≤ μ.real (cylinder s T ∆ A) := by rw [mul_one]; exact h2
    rw [hkey] at h1
    calc |μ.real (A ∩ shift^[n] ⁻¹' B) - μ.real A * μ.real B|
        ≤ |μ.real (A ∩ shift^[n] ⁻¹' B) - μ.real (cylinder s T) * μ.real B|
          + |μ.real (cylinder s T) * μ.real B - μ.real A * μ.real B| := abs_sub_le _ _ _
      _ ≤ μ.real (cylinder s T ∆ A) + μ.real (cylinder s T ∆ A) := by
          rw [abs_sub_comm] at h1
          exact add_le_add h1 h3
      _ < ε := by linarith

/-- **Bernoulli shifts are ergodic**, as mixing transformations of a probability space. -/
theorem ergodic_shift (p : Measure S) [IsProbabilityMeasure p] :
    Ergodic shift (Measure.infinitePi fun _ : ℕ => p) :=
  (isMixing_shift p).ergodic

end MathlibExt.Dynamics.Ergodic.BernoulliShift
