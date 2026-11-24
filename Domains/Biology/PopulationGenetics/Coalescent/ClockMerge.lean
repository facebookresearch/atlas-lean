/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.MutationPairwise
public import Domains.Biology.PopulationGenetics.Coalescent.Kingman
public import Domains.Biology.PopulationGenetics.Coalescent.Topology

/-!
# Clock/merge decomposition on the concrete genealogy

The coalescent decomposes into independent exponential epoch lengths and an
independent random-joining topology (Kingman 1982; Wakeley 2009, sections 3.1-3.2).
On the concrete genealogy space this becomes statements about
`kingmanGenealogyMeasure n = (piMeasure n).prod (randomJoining n)` on
`(Icc 2 n → ℝ) × RankedHistory n`, where `piMeasure n` is the product of
`expMeasure (k.choose 2)` and `randomJoining n` is the product over steps of
uniform pair choice.

For `n = 0` and `n = 1` the epoch index `Icc 2 n` is empty; the statements below
remain true as stated (the `hasLaw` obligations are vacuous and the independence
is over an empty index).

## Main results

* `KingmanTimes.ofGenealogy`: the time coordinate projections form a
  `KingmanTimes (kingmanGenealogyMeasure n) n` (Clause 1).
* `measurePreserving_fst_genealogy`, `measurePreserving_snd_genealogy`: the
  marginals are `piMeasure n` and `randomJoining n` (Clause 2).
* `indep_history_times_genealogy`: the history coordinate is independent of the
  full time coordinate, as `Indep` of the two comap σ-algebras, in the shape
  consumed by the site frequency spectrum theorems (Clause 3).
* `hasLaw_step_randomJoining`: each step coordinate under `randomJoining n` has
  law `uniformOn Set.univ` (Clause 4).

## What this does NOT do

This realizes the decomposition on the concrete product space. Deriving the same
decomposition from the continuous-time partition path (`partitionRate` CTMC path)
is a separate identification theorem, not claimed here.

## References

* J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982), 235–248.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009), sections 3.1–3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

private theorem measurePreserving_fst_genealogy_aux (n : ℕ) :
    MeasurePreserving Prod.fst (kingmanGenealogyMeasure n) (piMeasure n) := by
  unfold kingmanGenealogyMeasure
  exact measurePreserving_fst

/-- Clause 1: the time coordinate projections of the concrete genealogy form a
`KingmanTimes`. For `n = 0, 1` the index is empty and the fields hold vacuously. -/
def KingmanTimes.ofGenealogy (n : ℕ) : KingmanTimes (kingmanGenealogyMeasure n) n where
  T k g := if h : k ∈ Icc 2 n then g.1 ⟨k, h⟩ else 0
  hasLaw k hk := by
    exact ((KingmanTimes.ofPi n).hasLaw k hk).comp
      (measurePreserving_fst_genealogy_aux n).hasLaw
  indep := by
    exact iIndepFun_comp_of_measurePreserving (measurePreserving_fst_genealogy_aux n)
      (fun k => by
        simp only [KingmanTimes.ofPi, k.2, ↓reduceDIte]
        exact measurable_pi_apply _)
      (KingmanTimes.ofPi n).indep

namespace ClockMerge

/-- Clause 2 (fst): `Prod.fst` is measure-preserving from the genealogy to `piMeasure`. -/
theorem measurePreserving_fst_genealogy (n : ℕ) :
    MeasurePreserving Prod.fst (kingmanGenealogyMeasure n) (piMeasure n) := by
  unfold kingmanGenealogyMeasure
  exact measurePreserving_fst

/-- Clause 2 (snd): `Prod.snd` is measure-preserving from the genealogy to `randomJoining`. -/
theorem measurePreserving_snd_genealogy (n : ℕ) :
    MeasurePreserving Prod.snd (kingmanGenealogyMeasure n) (randomJoining n) := by
  unfold kingmanGenealogyMeasure
  exact measurePreserving_snd

/-- Clause 3: the history coordinate is independent of the full time coordinate,
as `Indep` of the two comap σ-algebras, mirroring the shape of
`SiteFrequencySpectrum.integral_sfs`. -/
theorem indep_history_times_genealogy (n : ℕ) :
    Indep (MeasurableSpace.comap (Prod.snd : (Icc 2 n → ℝ) × RankedHistory n → RankedHistory n) ⊤)
      (MeasurableSpace.comap (Prod.fst : (Icc 2 n → ℝ) × RankedHistory n → (Icc 2 n → ℝ))
        MeasurableSpace.pi)
      (kingmanGenealogyMeasure n) := by
  have htop : (inferInstance : MeasurableSpace (RankedHistory n)) = ⊤ :=
    MeasurableSpace.ext fun s =>
      ⟨fun _ => MeasurableSpace.measurableSet_top, fun _ => MeasurableSet.of_discrete⟩
  unfold kingmanGenealogyMeasure
  rw [← htop, ← IndepFun_iff_Indep]
  exact (indepFun_prod measurable_id measurable_id).symm

/-- Clause 4: each step coordinate under `randomJoining` is uniform over pairs. -/
theorem hasLaw_step_randomJoining (n : ℕ) (i : Fin (n - 1)) :
    HasLaw (fun h : RankedHistory n => h i)
      (ProbabilityTheory.uniformOn (Set.univ : Set (LineagePair (n - i))))
      (randomJoining n) := by
  have h := (measurePreserving_eval
    (fun i : Fin (n - 1) =>
      ProbabilityTheory.uniformOn (Set.univ : Set (LineagePair (n - i)))) i).hasLaw
  unfold randomJoining at h ⊢
  exact h

end ClockMerge

end MathlibExt.Biology.PopulationGenetics.Coalescent
