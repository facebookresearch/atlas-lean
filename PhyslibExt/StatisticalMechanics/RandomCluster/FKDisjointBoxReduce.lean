/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxDomainMarkov
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKTwoBoxDecoupling
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties

/-!
# Ergodicity of the wired `q = 2` measure from conditional product caps in boxes

A box-level conditional product cap for pairs of multi-open events implies the finite-box disjoint
product domination of `FKTwoBoxDecoupling`, hence ergodicity of the wired `q = 2` infinite-volume
measure.

## i. Overview

Masses of box events under the wired finite-volume measure are sums of `bcProb` with the wired
boundary graph. `fdb_BoxConditionalProductCap` asks, for each pair of multi-open events and far
translation, for a decomposition `O_T ∩ g⁻¹O_{T'} = A ∩ B` in a large box with `A` increasing, `B`
depending only on edges outside a set `F`, and bounds on the conditional masses of `A` and the mass
of `B`. The product bound of `FKDisjointBoxDomainMarkov` then gives
`ftb_FiniteBoxDisjointProductDom`. `fdb_boxConditionalProductCap_nonvacuous` exhibits the required
data for the trivial pair `T = T' = ∅`.

## ii. Key results

- `fdb_boxMass_eq_bcProb_sum` : wired box masses as sums of `bcProb`.
- `fdb_finiteBoxDisjointProductDom_of_boxCap` : the cap implies finite-box product domination.
- `fdb_wiredIV_isErgodic_of_boxCap` : ergodicity of the wired `q = 2` measure under the cap.

## iii. Table of contents

- A. Box masses
- B. The conditional product cap
- C. Ergodicity

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.19.
-/

@[expose] public section

open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}

/-! ## A. Box masses -/

lemma fdb_boxMass_eq_bcProb_sum (m : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d m)))) (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω := by
  rw [wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 S hmeas]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [bcProb_clique_eq_wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω]

/-! ## B. The conditional product cap -/

/-- For every finite family of finite edge sets and box index `N`, some translation `g` satisfies,
for
all large `m`: each `O_T ∩ g⁻¹O_{T'}` is `A ∩ B` on `Λ_m` with `A` increasing and `B` depending
only
on edges outside some `F`, the conditional masses of `A` on the fibres of `F` (with a boundary
graph
containing the wired one) are at most `μ_N(O_T)`, and the mass of `B` is at most `μ_N(O_{T'})`.
-/
def fdb_BoxConditionalProductCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      ∃ (F : Finset (Sym2 (boxVerts d m)))
        (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d m))))
        (C' : SimpleGraph (boxVerts d m)) (_ : DecidableRel C'.Adj),
        (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') = boxRestrict d m ⁻¹' (S_A ∩ S_B) ∧
        MeasurableSet (boxRestrict d m ⁻¹' (S_A ∩ S_B)) ∧
        MeasurableSet (boxRestrict d m ⁻¹' S_B) ∧
        IsIncreasing S_A ∧
        DependsOnOutside F S_B ∧
        boundaryCliqueGraph (boxBoundary d m) ≤ C' ∧
        (0 ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, S_A.indicator (fun _ => (1 : ℝ)) ρ * condBcProb (boxGraph d m) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) ∧
        ((wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S_B)
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))

lemma fdb_finiteBoxDisjointProductDom_of_boxCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
    ftb_FiniteBoxDisjointProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) := by
  intro P N
  obtain ⟨g, hg⟩ := hcap P N
  refine ⟨g, hg.mono fun m hm => ?_⟩
  intro T hT T' hT'
  obtain ⟨F, S_A, S_B, C', hC'dec, hcross, hmeasAB, hmeasB, hSAinc, hSBout, hCC', hαnn,
    hαcap, hBcap⟩ := hm T hT T' hT'
  set α := (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) with hαdef
  have hcrossmass : (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          (S_A ∩ S_B).indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω := by
    rw [hcross, fdb_boxMass_eq_bcProb_sum m hp hp1 (S_A ∩ S_B) hmeasAB]
  have hBmass : (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S_B)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S_B.indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω :=
    fdb_boxMass_eq_bcProb_sum m hp hp1 S_B hmeasB
  have hdecouple :
      (∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          (S_A ∩ S_B).indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω)
        ≤ α * (∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
            S_B.indicator (fun _ => (1 : ℝ)) ω
              * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω) :=
    bcProb_disjoint_product_dom_wired (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) C' hCC' hSAinc hSBout hαnn hαcap
  rw [hcrossmass]
  calc (∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          (S_A ∩ S_B).indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω)
      ≤ α * (∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
            S_B.indicator (fun _ => (1 : ℝ)) ω
              * bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ω) := hdecouple
    _ = α * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S_B) := by
          rw [hBmass]
    _ ≤ α * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') :=
          mul_le_mul_of_nonneg_left hBcap hαnn

lemma fmu_multiOpen_empty : fmu_multiOpen (∅ : Finset (Sym2 (Site d))) = Set.univ := by
  ext ω; simp [fmu_multiOpen]

lemma fdb_wiredMeasure_real_univ (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real Set.univ = 1 := by
  rw [Measure.real, measure_univ]; simp

lemma fdb_boxConditionalProductCap_nonvacuous {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ _g : Multiplicative (Site d), ∀ᶠ m in atTop,
      ∃ (F : Finset (Sym2 (boxVerts d m)))
        (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d m))))
        (C' : SimpleGraph (boxVerts d m)) (_ : DecidableRel C'.Adj),
        (fmu_multiOpen (∅ : Finset (Sym2 (Site d))) ∩
          (shift (1 : Multiplicative (Site d))
            : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen (∅ : Finset (Sym2 (Site d))))
            = boxRestrict d m ⁻¹' (S_A ∩ S_B) ∧
        MeasurableSet (boxRestrict d m ⁻¹' (S_A ∩ S_B)) ∧
        MeasurableSet (boxRestrict d m ⁻¹' S_B) ∧
        IsIncreasing S_A ∧
        DependsOnOutside F S_B ∧
        boundaryCliqueGraph (boxBoundary d m) ≤ C' ∧
        (0 ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d m)))).indicator (fun _ => (1 : ℝ)) ρ
              * condBcProb (boxGraph d m) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧
        ((wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S_B)
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
  refine ⟨1, Filter.Eventually.of_forall (fun m => ?_)⟩
  refine ⟨∅, Set.univ, Set.univ, boundaryCliqueGraph (boxBoundary d m), inferInstance, ?_, ?_, ?_,
    ?_, ?_, le_refl _, ?_, ?_, ?_⟩
  · rw [fmu_multiOpen_empty, Set.preimage_univ, Set.inter_univ, Set.inter_univ,
      Set.preimage_univ]
  · rw [Set.inter_univ, Set.preimage_univ]; exact MeasurableSet.univ
  · rw [Set.preimage_univ]; exact MeasurableSet.univ
  · exact fun _ _ _ ha => ha
  · exact fun _ _ _ => Iff.rfl
  · rw [fmu_multiOpen_empty, fdb_wiredMeasure_real_univ]; norm_num
  · intro ψ _
    rw [fmu_multiOpen_empty, fdb_wiredMeasure_real_univ]
    have : (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d m)))).indicator (fun _ => (1 : ℝ)) ρ
        * condBcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ∅ ψ ρ)
        = ∑ ρ, condBcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p 2 ∅ ψ ρ := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Set.indicator_of_mem (Set.mem_univ ρ), one_mul]
    rw [this, condBcProb_sum_eq_one (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m))
      hp hp1 (by norm_num) ∅ ψ]
  · rw [Set.preimage_univ, fmu_multiOpen_empty, fdb_wiredMeasure_real_univ,
      fdb_wiredMeasure_real_univ]

/-! ## C. Ergodicity -/

lemma fdb_wiredIV_isErgodic_of_boxCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ftb_wiredIV_isErgodic_of_finiteBoxDisjointProductDom hp hp1
    (fdb_finiteBoxDisjointProductDom_of_boxCap hp hp1 hcap)

end FK

end StatMech
