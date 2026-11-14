/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib.Probability.Independence.Basic

/-!
# CDIS Probabilités IV: consequences of the independence of a sequence

* id 66: subsequences, vectors built from disjoint blocks, and Borel functions of an independent
  sequence are independent.

Items (1) and (3) are `iIndepFun.precomp` and `iIndepFun.comp`. Item (2) is not in Mathlib,
which only splits a family into two blocks (`iIndepFun.indepFun_finset`):
`iIndep_biSup_of_pairwise_disjoint` groups independent σ-algebras into any family of pairwise
disjoint blocks, by the π-system argument of `iIndepSets.iIndep` applied to the finite
intersections `piiUnionInter` of each block.
-/

open MeasureTheory ProbabilityTheory Set MeasurableSpace Function

namespace CDIS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grouping independent σ-algebras into disjoint blocks keeps them independent. -/
theorem iIndep_biSup_of_pairwise_disjoint {ι κ : Type*} {m : ι → MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h : iIndep m P) {S : κ → Set ι} (hS : Pairwise (Disjoint on S)) :
    iIndep (fun k ↦ ⨆ i ∈ S k, m i) P := by
  classical
  refine iIndepSets.iIndep (m := fun k ↦ ⨆ i ∈ S k, m i) (fun k ↦ iSup₂_le fun i _ ↦ h_le i)
    (fun k ↦ piiUnionInter (fun i ↦ {s | MeasurableSet[m i] s}) (S k))
    (fun k ↦ isPiSystem_piiUnionInter _
      (fun i ↦ @MeasurableSpace.isPiSystem_measurableSet Ω (m i)) _)
    (fun k ↦ (generateFrom_piiUnionInter_measurableSet m (S k)).symm) ?_
  rw [iIndepSets_iff]
  intro s f hf
  rcases s.eq_empty_or_nonempty with rfl | ⟨k₀, -⟩
  · simp
  have : Nonempty κ := ⟨k₀⟩
  choose T hTS g hg hfg using hf
  -- the finite index sets of the blocks are disjoint, and their union indexes one intersection
  set T' : κ → Finset ι := fun k ↦ if hk : k ∈ s then T k hk else ∅ with hT'
  have hT'S : ∀ k, (T' k : Set ι) ⊆ S k := fun k ↦ by
    by_cases hk : k ∈ s <;> simp [T', hk, hTS]
  have hdisj : (s : Set κ).PairwiseDisjoint T' := fun k _ l _ hkl ↦
    Finset.disjoint_coe.1 ((hS hkl).mono (hT'S k) (hT'S l))
  set g' : κ → ι → Set Ω := fun k ↦ if hk : k ∈ s then g k hk else fun _ ↦ univ
  have hfg' : ∀ k ∈ s, f k = ⋂ i ∈ T' k, g' k i := fun k hk ↦ by simp [T', g', hk, hfg k hk]
  have hg' : ∀ k ∈ s, ∀ i ∈ T' k, MeasurableSet[m i] (g' k i) := fun k hk i hi ↦ by
    simp only [T', g', hk, dite_true] at hi ⊢
    exact hg k hk i hi
  -- the block containing an index of the union
  have hunique : ∀ i ∈ s.biUnion T', ∃ k ∈ s, i ∈ T' k := fun i hi ↦ by
    simpa using hi
  choose! blk hblk hiblk using hunique
  have hblk_eq : ∀ k ∈ s, ∀ i ∈ T' k, blk i = k := fun k hk i hi ↦ by
    have hi' : i ∈ s.biUnion T' := Finset.mem_biUnion.2 ⟨k, hk, hi⟩
    by_contra hne
    exact Finset.disjoint_left.1 (hdisj (hblk i hi') hk hne) (hiblk i hi') hi
  set G : ι → Set Ω := fun i ↦ g' (blk i) i
  have hGm : ∀ i ∈ s.biUnion T', MeasurableSet[m i] (G i) := fun i hi ↦
    hg' _ (hblk i hi) i (hiblk i hi)
  have hinter : ⋂ k ∈ s, f k = ⋂ i ∈ s.biUnion T', G i := by
    ext ω
    simp only [mem_iInter, Finset.mem_biUnion]
    constructor
    · rintro h i ⟨k, hk, hi⟩
      have := (hfg' k hk ▸ h k hk : ω ∈ ⋂ i ∈ T' k, g' k i)
      simp only [mem_iInter] at this
      simpa [G, hblk_eq k hk i hi] using this i hi
    · intro h k hk
      rw [hfg' k hk]
      simp only [mem_iInter]
      intro i hi
      simpa [G, hblk_eq k hk i hi] using h i ⟨k, hk, hi⟩
  rw [hinter, h.meas_biInter hGm, Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [hfg' k hk, h.meas_biInter (hg' k hk)]
  exact Finset.prod_congr rfl fun i hi ↦ by simp [G, hblk_eq k hk i hi]

/-- CDIS P.IV, id 66: if the sequence `(X_n)` is independent, so are (1) every subsequence
`(X_{φ k})`, (2) every sequence of vectors `((X_i)_{i ∈ S k})_k` built from pairwise disjoint
finite blocks `S k`, and (3) every sequence `(f_n(X_n))` with Borel functions `f_n`. -/
theorem iIndepFun_consequences {β : ℕ → Type*} [∀ n, MeasurableSpace (β n)]
    {X : ∀ n, Ω → β n} (hX : ∀ n, Measurable (X n)) (h : iIndepFun X P)
    {γ : ℕ → Type*} [∀ n, MeasurableSpace (γ n)] {f : ∀ n, β n → γ n}
    (hf : ∀ n, Measurable (f n)) :
    (∀ φ : ℕ → ℕ, StrictMono φ → iIndepFun (fun k ↦ X (φ k)) P) ∧
      (∀ S : ℕ → Finset ℕ, Pairwise (Disjoint on S) →
        iIndepFun (fun k ω (i : S k) ↦ X i ω) P) ∧
      iIndepFun (fun n ω ↦ f n (X n ω)) P := by
  refine ⟨fun φ hφ ↦ h.precomp hφ.injective, fun S hS ↦ ?_, h.comp f hf⟩
  rw [iIndepFun_iff_iIndep] at h ⊢
  have hblock : ∀ k, MeasurableSpace.comap (fun ω (i : S k) ↦ X i ω) MeasurableSpace.pi =
      ⨆ i ∈ (S k : Set ℕ), MeasurableSpace.comap (X i) inferInstance := by
    intro k
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup_subtype' (p := fun i ↦ i ∈ (S k : Set ℕ))
      (f := fun i _ ↦ MeasurableSpace.comap (X i) inferInstance) |>.symm
  simp_rw [hblock]
  exact iIndep_biSup_of_pairwise_disjoint (fun i ↦ (hX i).comap_le) h
    fun k l hkl ↦ Finset.disjoint_coe.2 (hS hkl)

end CDIS
