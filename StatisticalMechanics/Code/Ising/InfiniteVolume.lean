/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Ising.Gibbs
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoundaryConditions
import Code.Foundations.WeakConvergence
import Code.Foundations.Prokhorov

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}




instance instDecidableMemBox (d n : ℕ) (x : Site d) :
    Decidable (x ∈ box d n) := by
  rw [mem_box]; infer_instance


instance instDecidableAdj (d : ℕ) (x y : Site d) :
    Decidable ((hypercubicLattice d).Adj x y) := by
  rw [hypercubicLattice_adj]; infer_instance


noncomputable def boxFinset (d n : ℕ) : Finset (Site d) :=
  (box_finite d n).toFinset

@[simp] lemma mem_boxFinset {d n : ℕ} {x : Site d} :
    x ∈ boxFinset d n ↔ x ∈ box d n := by
  rw [boxFinset, Set.Finite.mem_toFinset]


noncomputable instance instFintypeBox (d n : ℕ) : Fintype {x // x ∈ box d n} :=
  (box_finite d n).fintype


noncomputable instance instFintypeBoxAssign (d n : ℕ) :
    Fintype ({x // x ∈ box d n} → Bool) := inferInstance






noncomputable def bondPairsTouch (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d (n + 1)) ×ˢ (boxFinset d (n + 1))).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ box d n ∨ p.2 ∈ box d n))


noncomputable def bondPairsInternal (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2)


noncomputable def bondFinsetTouch (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsTouch d n).image (fun p => s(p.1, p.2))


noncomputable def bondFinsetInternal (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (bondPairsInternal d n).image (fun p => s(p.1, p.2))





noncomputable def glue (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) : ConfigSpace (Site d) :=
  fun x => if h : x ∈ box d n then τ ⟨x, h⟩ else η x

@[simp] lemma glue_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∈ box d n) :
    glue η τ x = τ ⟨x, hx⟩ := by
  simp [glue, hx]

@[simp] lemma glue_not_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∉ box d n) :
    glue η τ x = η x := by
  simp [glue, hx]










noncomputable def fvEnergy (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  - (∑ e ∈ B, bond (glue η τ) e) - h * ∑ x ∈ boxFinset d n, spin (glue η τ) x


noncomputable def fvWeight (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  Real.exp (-β * fvEnergy η n B h τ)

lemma fvWeight_pos (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 < fvWeight η n B β h τ := Real.exp_pos _

lemma fvWeight_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 ≤ fvWeight η n B β h τ := (fvWeight_pos η n B β h τ).le



noncomputable def fvZ (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β h τ

lemma fvZ_pos (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : 0 < fvZ η n B β h := by
  unfold fvZ
  apply Finset.sum_pos
  · intro τ _; exact fvWeight_pos η n B β h τ
  · exact Finset.univ_nonempty

lemma fvZ_ne_zero (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : fvZ η n B β h ≠ 0 :=
  (fvZ_pos η n B β h).ne'


noncomputable def fvProb (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  fvWeight η n B β h τ / fvZ η n B β h

lemma fvProb_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 ≤ fvProb η n B β h τ :=
  div_nonneg (fvWeight_nonneg η n B β h τ) (fvZ_pos η n B β h).le

lemma fvProb_sum_eq_one (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ = 1 := by
  unfold fvProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (fvZ_ne_zero η n B β h)]
  rfl







noncomputable def fvMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Measure (ConfigSpace (Site d)) :=
  ∑ τ : {x // x ∈ box d n} → Bool,
    ENNReal.ofReal (fvProb η n B β h τ) • Measure.dirac (glue η τ)


lemma fvMeasure_univ (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    (fvMeasure η n B β h) Set.univ = 1 := by
  unfold fvMeasure
  rw [Measure.finsetSum_apply _ _ _]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun τ _ => fvProb_nonneg η n B β h τ),
    fvProb_sum_eq_one η n B β h, ENNReal.ofReal_one]

instance fvMeasure_isProbabilityMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    IsProbabilityMeasure (fvMeasure η n B β h) :=
  ⟨fvMeasure_univ η n B β h⟩


noncomputable def fvProbabilityMeasure (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  ⟨fvMeasure η n B β h, fvMeasure_isProbabilityMeasure η n B β h⟩




def plusField (d : ℕ) : ConfigSpace (Site d) := fun _ => true


def minusField (d : ℕ) : ConfigSpace (Site d) := fun _ => false



noncomputable def plusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (plusField d) n (bondFinsetTouch d n) β h



noncomputable def minusMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetTouch d n) β h




noncomputable def freeMeasure (d n : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (minusField d) n (bondFinsetInternal d n) β h







def InfiniteVolumeState (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (μ : ProbabilityMeasure (ConfigSpace (Site d))) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakConvergesTo (ρ ∘ φ) μ





theorem exists_infiniteVolumeState
    (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    ∃ μ : ProbabilityMeasure (ConfigSpace (Site d)), InfiniteVolumeState ρ μ := by
  obtain ⟨ν, φ, hφ, htends⟩ := prokhorov_seq_compact ρ
  exact ⟨ν, φ, hφ, htends⟩



noncomputable def limitState (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (exists_infiniteVolumeState ρ).choose


theorem limitState_isInfiniteVolumeState
    (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    InfiniteVolumeState ρ (limitState ρ) :=
  (exists_infiniteVolumeState ρ).choose_spec



noncomputable def plusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => plusMeasure d n β h)



noncomputable def minusState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => minusMeasure d n β h)



noncomputable def freeState (d : ℕ) (β h : ℝ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => freeMeasure d n β h)



theorem plusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => plusMeasure d n β h) (plusState d β h) :=
  limitState_isInfiniteVolumeState _



theorem minusState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => minusMeasure d n β h) (minusState d β h) :=
  limitState_isInfiniteVolumeState _



theorem freeState_isInfiniteVolumeState (d : ℕ) (β h : ℝ) :
    InfiniteVolumeState (fun n => freeMeasure d n β h) (freeState d β h) :=
  limitState_isInfiniteVolumeState _

end Ising

end StatMech
