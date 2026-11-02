/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SubcriticalDecay
public import MathlibExt.Probability.Percolation.Exploration
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import MathlibExt.Probability.Configuration.Ergodicity
public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# Translation invariance and crossings from a shifted origin

The Bernoulli product measure on edges of `ℤ^d` is invariant under lattice translations, so the
probability that a site `y ∈ Λ_L` is connected to distance `n` is at most the probability that the
origin is connected to distance `n - L`. Measurability of the crossing events is also proved here.

## Main definitions

* `StatMech.Percolation.crossingEventFrom`: the event that `y` is connected to a site outside
  `Λ_{n-1}`.

## Main results

* `StatMech.Percolation.bernoulli_translationInvariant`: the product measure is translation
  invariant.
* `StatMech.Percolation.crossProbFrom_le`: `ℙ_p(y ↔ ℤ^d \ Λ_{n-1}) ≤ crossProb d p m` for `y ∈ Λ_L`,
  `m + L ≤ n`.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

section TranslationInvariance

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]

theorem shift_eq_piCongrLeft (g : G) :
    (shift g : ConfigSpace E → ConfigSpace E)
      = ⇑(Equiv.piCongrLeft (fun _ : E => Bool) (MulAction.toPerm g)) := by
  funext ω b
  set e₁ := MulAction.toPerm (β := E) g with he₁
  conv_rhs => rw [show b = e₁ (e₁.symm b) from (e₁.apply_symm_apply b).symm,
    Equiv.piCongrLeft_apply_apply (a := e₁.symm b)]
  rw [shift_apply, he₁, MulAction.toPerm_symm_apply]

/-- The Bernoulli product measure on `{0, 1}^E` is invariant under the shift action of `G`. -/
theorem bernoulli_translationInvariant (p : ℝ≥0) (hp : p ≤ 1) [Countable E] :
    IsTranslationInvariant (G := G) (bernoulliProductMeasure (E := E) p hp) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [shift_eq_piCongrLeft]
  have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : E => bernoulliMeasure p hp)
    (MulAction.toPerm (β := E) g)
  simpa only [bernoulliProductMeasure, MeasurableEquiv.coe_piCongrLeft] using h

end TranslationInvariance

variable {d : ℕ}

/-- The event that `y` is joined by an open path to a site outside `Λ_{n-1}`. -/
def crossingEventFrom (d : ℕ) (y : Site d) (n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ v, Connected d ω y v ∧ v ∉ box d (n - 1)}

@[simp]
theorem mem_crossingEventFrom {y : Site d} {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ crossingEventFrom d y n ↔ ∃ v, Connected d ω y v ∧ v ∉ box d (n - 1) :=
  Iff.rfl

theorem crossingEventFrom_origin (n : ℕ) :
    crossingEventFrom d (origin d) n = crossingEvent d n := rfl

theorem measurableSet_crossingEventFrom (y : Site d) (n : ℕ) :
    MeasurableSet (crossingEventFrom d y n) := by
  have hrw : crossingEventFrom d y n
      = ⋃ v ∈ (box d (n - 1))ᶜ,
          {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω y v} := by
    ext ω
    simp only [mem_crossingEventFrom, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun v _ => measurableSet_connected y v)

theorem crossingEventFrom_eq_preimage (y : Site d) (n : ℕ) :
    crossingEventFrom d y n
      = (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹'
          {ω | ∃ v, Connected d ω (origin d) v ∧ (v + y) ∉ box d (n - 1)} := by
  ext ω
  simp only [mem_crossingEventFrom, Set.mem_ofPred_eq, Set.mem_preimage]
  set g := Multiplicative.ofAdd (-y) with hg
  have hgy : g • y = origin d := by funext i; change -y i + y i = (0 : ℤ); ring
  constructor
  · rintro ⟨v, hc, hv⟩
    refine ⟨g • v, ?_, ?_⟩
    · have hkey := (connected_shift g ω y v).mpr hc
      rwa [hgy] at hkey
    · have hvy : g • v + y = v := by funext i; change (-y i + v i) + y i = v i; ring
      rwa [hvy]
  · rintro ⟨w, hc, hw⟩
    refine ⟨g⁻¹ • w, ?_, ?_⟩
    · have hkey := (connected_shift g ω y (g⁻¹ • w)).mp ?_
      · exact hkey
      · rw [hgy, smul_inv_smul]; exact hc
    · have hgi : g⁻¹ • w = w + y := by
        funext i
        rw [smul_site_apply]
        simp only [hg, ← ofAdd_neg, toAdd_ofAdd, neg_neg, Pi.add_apply]
        ring
      rwa [hgi]

theorem box_shift_mem {y v : Site d} {L m n : ℕ}
    (hy : y ∈ box d L) (hv : v ∈ box d (m - 1)) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (v + y) ∈ box d (n - 1) := by
  intro i
  have hvi : (v i).natAbs ≤ m - 1 := hv i
  have hyi : (y i).natAbs ≤ L := hy i
  have hle : ((v + y) i).natAbs ≤ (v i).natAbs + (y i).natAbs := by
    rw [Pi.add_apply]; exact Int.natAbs_add_le _ _
  omega

theorem crossProbFrom_le (p : ℝ≥0) (hp : p ≤ 1) (y : Site d) {L m n : ℕ}
    (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEventFrom d y n)
      ≤ crossProb d p hp m := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  set g := Multiplicative.ofAdd (-y) with hg
  set B := {ω : ConfigSpace (Sym2 (Site d)) |
      ∃ v, Connected d ω (origin d) v ∧ (v + y) ∉ box d (n - 1)} with hB
  have hBmeas : MeasurableSet B := by
    have hrw : B = ⋃ v ∈ {v : Site d | (v + y) ∉ box d (n - 1)},
        {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω (origin d) v} := by
      ext ω; simp only [hB, Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩⟩
    rw [hrw]
    exact MeasurableSet.biUnion (Set.to_countable _)
      (fun v _ => measurableSet_connected (origin d) v)
  have hpres := (bernoulli_translationInvariant (E := Sym2 (Site d))
    (G := Multiplicative (Site d)) p hp) g
  have hstep1 : μ.real (crossingEventFrom d y n) = μ.real B := by
    rw [crossingEventFrom_eq_preimage]
    exact hpres.measureReal_preimage hBmeas.nullMeasurableSet
  rw [hstep1]
  have hsub : B ⊆ crossingEvent d m := by
    rintro ω ⟨v, hc, hv⟩
    exact ⟨v, hc, fun hvm => hv (box_shift_mem hy hvm hmLn hm)⟩
  calc μ.real B ≤ μ.real (crossingEvent d m) := measureReal_mono hsub
    _ = crossProb d p hp m := rfl

end Percolation

end StatMech
