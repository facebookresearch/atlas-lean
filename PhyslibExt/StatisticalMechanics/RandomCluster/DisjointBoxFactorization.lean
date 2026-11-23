/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxReduce
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKWiredDomainMonotone
public import PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvarianceFromHomogeneity

/-!
# Factorization of multi-open events in disjoint boxes

When a multi-open event `O_T` and a translated event `g⁻¹O_{T'}` sit in a common box with the edges
of the translate outside a set `F`, conditional bounds on fibres of `F` give the wired disjoint-box
factorization bound and hence ergodicity of the wired `q = 2` measure.

## i. Overview

Multi-open box events whose edges avoid `F` depend only on edges outside `F`. Under the analytic cap
`dgf_DisjointBoxAnalyticCap` (realizations of `T` and `g⁻¹T'` in `Λ_{N+r}` with `g⁻¹T'` outside `F`,
and conditional and marginal bounds by the box masses at scale `N`), the product bound of
`FKDisjointBoxDomainMarkov` yields `fwm_WiredDisjointBoxFactorise` and ergodicity.
`dgf_disjointBoxAnalyticCap_nonvacuous` exhibits the required data for the trivial pair.

## ii. Key results

- `dgf_boxMultiOpen_dependsOnOutside` : multi-open events avoiding `F` depend only on edges outside
  `F`.
- `dgf_factorise_pair` : the factorization bound for one pair.
- `dgf_wiredDisjointBoxFactorise_of_conditionalCap` : the factorization bound for all pairs.
- `dgf_wiredIV_isErgodic_of_conditionalCap` : ergodicity under the cap.

## iii. Table of contents

- A. Events outside a set of edges
- B. The analytic cap and factorization
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

variable {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
  [DecidableRel G.Adj] [DecidableRel C.Adj]

/-! ## A. Events outside a set of edges -/

lemma dgf_disjoint_product_dom_doubleCap {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : DependsOnOutside F B)
    {α β : ℝ} (hα : 0 ≤ α)
    (hAcap : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α)
    (hBcap : (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ * bcProb G C p q ρ) ≤ β) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ * bcProb G C p q ρ) ≤ α * β := by
  have hAB := bcProb_disjoint_product_dom_wired G C hp hp1 hq C' hCC' hA hB hα hAcap
  exact hAB.trans (mul_le_mul_of_nonneg_left hBcap hα)

lemma dgf_boxMultiOpen_dependsOnOutside (M : ℕ) (F : Finset (Sym2 (boxVerts d M)))
    (t : Finset (Sym2 (boxVerts d M))) (hdisj : ∀ e ∈ t, e ∉ F) :
    DependsOnOutside F (cdc_boxMultiOpenEvent M t) := by
  intro ψ ρ hagree
  constructor
  · intro hψ eb heb; rw [hagree eb (hdisj eb heb)]; exact hψ eb heb
  · intro hρ eb heb; rw [← hagree eb (hdisj eb heb)]; exact hρ eb heb

lemma dgf_cross_eq_boxRestrict_inter (M : ℕ) (g : Multiplicative (Site d))
    (T T' : Finset (Sym2 (Site d)))
    (tT tT' : Finset (Sym2 (boxVerts d M)))
    (hT : T = tT.image (edgeIncl d M))
    (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d M)) :
    (fmu_multiOpen T ∩
        (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
          ⁻¹' fmu_multiOpen T')
      = boxRestrict d M ⁻¹' (cdc_boxMultiOpenEvent M tT ∩ cdc_boxMultiOpenEvent M tT') := by
  rw [fmu_shift_multiOpen g T', hT', hT,
    ftb_fmu_eq_cdc_multiOpen, ftb_fmu_eq_cdc_multiOpen,
    cdc_multiOpenEvent_image_eq_boxRestrict, cdc_multiOpenEvent_image_eq_boxRestrict,
    Set.preimage_inter]

/-! ## B. The analytic cap and factorization -/

/-- For every finite family of finite edge sets and scale `N`, some translation `g` and margin `r`
realize each pair `T`, `g⁻¹T'` in `Λ_{N+r}` with `g⁻¹T'` outside a set `F`, such that the
conditional masses of `O_T` on fibres of `F` (with a boundary graph containing the wired one)
are at
most `μ_N(O_T)` and the box mass of `g⁻¹O_{T'}` is at most `μ_N(O_{T'})`.
-/
def dgf_DisjointBoxAnalyticCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    ∃ (g : Multiplicative (Site d)) (r : ℕ), ∀ T ∈ P, ∀ T' ∈ P,
      ∃ (F tT tT' : Finset (Sym2 (boxVerts d (N + r))))
        (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj),
        T = tT.image (edgeIncl d (N + r)) ∧
        T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d (N + r)) ∧
        (∀ e ∈ tT', e ∉ F) ∧
        boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1 : ℝ)) ρ
              * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) ∧
        ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT'))
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))

lemma dgf_factorise_pair {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {N r : ℕ} {g : Multiplicative (Site d)} {T T' : Finset (Sym2 (Site d))}
    {F tT tT' : Finset (Sym2 (boxVerts d (N + r)))}
    {C' : SimpleGraph (boxVerts d (N + r))} (hC'dec : DecidableRel C'.Adj)
    (hT : T = tT.image (edgeIncl d (N + r)))
    (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d (N + r)))
    (hdisj : ∀ e ∈ tT', e ∉ F)
    (hCC' : boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C')
    (hαcap : ∀ ψ ∈ fibreReps F,
      (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1 : ℝ)) ρ
          * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))
    (hBcap : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT'))
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) :
    (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
  classical
  set S_A := cdc_boxMultiOpenEvent (N + r) tT with hSA
  set S_B := cdc_boxMultiOpenEvent (N + r) tT' with hSB
  have hSAinc : IsIncreasing S_A := cdc_boxMultiOpenEvent_isIncreasing (N + r) tT
  have hSBout : DependsOnOutside F S_B := dgf_boxMultiOpen_dependsOnOutside (N + r) F tT' hdisj
  have hcross : (fmu_multiOpen T ∩
      (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
        ⁻¹' fmu_multiOpen T') = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B) :=
    dgf_cross_eq_boxRestrict_inter (N + r) g T T' tT tT' hT hT'
  have hmeasA : MeasurableSet (boxRestrict d (N + r) ⁻¹' S_A) := by
    rw [hSA, ← cdc_multiOpenEvent_image_eq_boxRestrict, ← ftb_fmu_eq_cdc_multiOpen]
    exact fmu_multiOpen_measurable _
  have hmeasB : MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B) := by
    rw [hSB, ← cdc_multiOpenEvent_image_eq_boxRestrict, ← ftb_fmu_eq_cdc_multiOpen]
    exact fmu_multiOpen_measurable _
  have hmeasAB : MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)) := by
    rw [Set.preimage_inter]; exact hmeasA.inter hmeasB
  have hαnn : 0 ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) := measureReal_nonneg
  have hcrossmass : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
          (S_A ∩ S_B).indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω := by
    rw [hcross, fdb_boxMass_eq_bcProb_sum (N + r) hp hp1 (S_A ∩ S_B) hmeasAB]
  have hBmass : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
          S_B.indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω :=
    fdb_boxMass_eq_bcProb_sum (N + r) hp hp1 S_B hmeasB
  have hBcap' : (∑ ω : ConfigSpace (Sym2 (boxVerts d (N + r))),
        S_B.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (boxGraph d (N + r)) (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 ω)
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
    rw [← hBmass]; exact hBcap
  rw [hcrossmass]
  exact dgf_disjoint_product_dom_doubleCap (boxGraph d (N + r))
    (boundaryCliqueGraph (boxBoundary d (N + r)))
    hp hp1 (by norm_num : (1 : ℝ) ≤ 2) C' hCC' hSAinc hSBout hαnn hαcap hBcap'

lemma dgf_cross_support_realised {M : ℕ} {g : Multiplicative (Site d)}
    {T T' : Finset (Sym2 (Site d))} {tT tT' : Finset (Sym2 (boxVerts d M))}
    (hT : T = tT.image (edgeIncl d M))
    (hT' : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d M)) :
    T ∪ T'.image (fun e => g⁻¹ • e) = (tT ∪ tT').image (edgeIncl d M) := by
  rw [hT, hT', Finset.image_union]

lemma dgf_wiredDisjointBoxFactorise_of_conditionalCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : dgf_DisjointBoxAnalyticCap (d := d) hp hp1) :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) := by
  intro P N hreal
  obtain ⟨g, r, hg⟩ := hcap P N
  refine ⟨g, r, fun T hT T' hT' => ?_⟩
  obtain ⟨F, tT, tT', C', hC'dec, hTreal, hT'real, hdisj, hCC', hαcap, hBcap⟩ := hg T hT T' hT'
  refine ⟨⟨tT ∪ tT', dgf_cross_support_realised hTreal hT'real⟩, ?_⟩
  exact dgf_factorise_pair hp hp1 hC'dec hTreal hT'real hdisj hCC' hαcap hBcap

lemma dgf_disjointBoxAnalyticCap_nonvacuous {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ (_g : Multiplicative (Site d)) (r : ℕ),
      ∃ (F tT tT' : Finset (Sym2 (boxVerts d (N + r))))
        (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj),
        (∅ : Finset (Sym2 (Site d))) = tT.image (edgeIncl d (N + r)) ∧
        (∅ : Finset (Sym2 (Site d))).image (fun e => (1 : Multiplicative (Site d))⁻¹ • e)
          = tT'.image (edgeIncl d (N + r)) ∧
        (∀ e ∈ tT', e ∉ F) ∧
        boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1 : ℝ)) ρ
              * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) ∧
        ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT'))
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (fmu_multiOpen (∅ : Finset (Sym2 (Site d))))) := by
  classical
  refine ⟨1, 0, ∅, ∅, ∅, boundaryCliqueGraph (boxBoundary d (N + 0)), inferInstance,
    by simp, by simp, by simp, le_refl _, ?_, ?_⟩
  · intro ψ _
    rw [fmu_multiOpen_empty, fdb_wiredMeasure_real_univ]
    have hev : cdc_boxMultiOpenEvent (N + 0) (∅ : Finset (Sym2 (boxVerts d (N + 0))))
        = (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + 0))))) := by
      ext ρ; simp [cdc_boxMultiOpenEvent]
    rw [hev]
    have : (∑ ρ, (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + 0))))).indicator
        (fun _ => (1 : ℝ)) ρ
        * condBcProb (boxGraph d (N + 0)) (boundaryCliqueGraph (boxBoundary d (N + 0))) p 2 ∅ ψ ρ)
        = ∑ ρ, condBcProb (boxGraph d (N + 0)) (boundaryCliqueGraph (boxBoundary d (N + 0))) p 2
            ∅ ψ ρ := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Set.indicator_of_mem (Set.mem_univ ρ), one_mul]
    rw [this, condBcProb_sum_eq_one (boxGraph d (N + 0))
        (boundaryCliqueGraph (boxBoundary d (N + 0)))
      hp hp1 (by norm_num) ∅ ψ]
  · have hev : cdc_boxMultiOpenEvent (N + 0) (∅ : Finset (Sym2 (boxVerts d (N + 0))))
        = (Set.univ : Set (ConfigSpace (Sym2 (boxVerts d (N + 0))))) := by
      ext ρ; simp [cdc_boxMultiOpenEvent]
    rw [hev, Set.preimage_univ, fmu_multiOpen_empty, fdb_wiredMeasure_real_univ,
      fdb_wiredMeasure_real_univ]

/-! ## C. Ergodicity -/

lemma dgf_wiredIV_isErgodic_of_conditionalCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : dgf_DisjointBoxAnalyticCap (d := d) hp hp1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fwm_wiredIV_isErgodic_of_factorise hp hp1
    (dgf_wiredDisjointBoxFactorise_of_conditionalCap hp hp1 hcap)

end FK

end StatMech
