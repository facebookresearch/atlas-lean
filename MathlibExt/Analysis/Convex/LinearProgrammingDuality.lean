/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Strong linear programming duality

A feasible bounded-above primal `max { c ⬝ᵥ x | x ≥ 0, A *ᵥ x ≤ b }` attains
its supremum, and there is a dual-feasible `y ≥ 0` with `c ≤ Aᵀ *ᵥ y` and
equal objective value `c ⬝ᵥ x = b ⬝ᵥ y`.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.LPDuality

open scoped Topology Matrix
open Finset Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
/-- Elimination step: a relation kills one generator. -/
private lemma hull_elim {S : Finset E} {c : E →₀ ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsupp : c.support ⊆ ↑S) {d : E →₀ ℝ} (hd : d ≠ 0)
    (hdsupp : d.support ⊆ ↑S)
    (hrel : Finsupp.linearCombination ℝ id d = 0)
    {y : E} (hy : Finsupp.linearCombination ℝ id c = y) :
    ∃ j ∈ S, y ∈ PointedCone.hull ℝ (↑(S.erase j) : Set E) := by
  have step : ∀ {d : E →₀ ℝ}, d.support ⊆ ↑S →
      Finsupp.linearCombination ℝ id d = 0 →
      (S.filter (fun i => 0 < d i)).Nonempty →
      ∃ j ∈ S, y ∈ PointedCone.hull ℝ (↑(S.erase j) : Set E) := by
    intro d hdsupp hrel ⟨j, hjP⟩
    obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image
      (S.filter (fun i => 0 < d i)) (fun i => c i / d i) ⟨j, hjP⟩
    rw [Finset.mem_filter] at hjP
    obtain ⟨hjS, hdj⟩ := hjP
    set t := c j / d j with ht
    have hdj' : d j ≠ 0 := ne_of_gt hdj
    have htnonneg : 0 ≤ t := div_nonneg (hc j) hdj.le
    -- new weights
    set c' : E →₀ ℝ := c - t • d with hc'def
    have hci : ∀ i, c' i = c i - t * d i := fun i => by
      simp [hc'def, Finsupp.sub_apply, Finsupp.smul_apply]
    have hc' : ∀ i, 0 ≤ c' i := by
      intro i
      rw [hci]
      by_cases hSi : i ∈ S
      · by_cases hdi : 0 < d i
        · have hmem : i ∈ S.filter (fun i => 0 < d i) :=
            Finset.mem_filter.mpr ⟨hSi, hdi⟩
          have hle : t ≤ c i / d i := hjmin i hmem
          have h := (le_div_iff₀ hdi).mp hle
          linarith
        · push Not at hdi
          have h := mul_nonpos_of_nonneg_of_nonpos htnonneg hdi
          have := hc i
          linarith
      · have hcz : c i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hsupp h))
        have hdz : d i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hdsupp h))
        rw [hcz, hdz, mul_zero, sub_zero]
    have hsupp' : c'.support ⊆ ↑(S.erase j) := by
      intro i hi
      rw [Finset.mem_erase]
      have hne : c' i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hiS : i ∈ S := by
        by_contra hSi
        have hcz : c i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hsupp h))
        have hdz : d i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hdsupp h))
        rw [hci, hcz, hdz, mul_zero, sub_zero] at hne
        exact hne rfl
      refine ⟨?_, hiS⟩
      intro hij
      apply hne
      rw [hci, hij, ht, div_mul_cancel₀ _ hdj', sub_self]
    have hcomb' : Finsupp.linearCombination ℝ id c' = y := by
      rw [hc'def, map_sub, map_smul, hrel, smul_zero, sub_zero]
      exact hy
    refine ⟨j, hjS, PointedCone.mem_hull_set.mpr ⟨c', hsupp', hc', ?_⟩⟩
    simpa [Finsupp.linearCombination_apply] using hcomb'
  -- sign choice
  obtain ⟨i, hiS, hdi⟩ : ∃ i ∈ S, d i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hd
    ext i
    by_cases hiS : i ∈ S
    · simp [hcon i hiS]
    · have h : i ∉ d.support :=
        fun hm => hiS (hdsupp hm)
      rw [Finsupp.notMem_support_iff.mp h]
      rfl
  by_cases hpos : 0 < d i
  · exact step hdsupp hrel ⟨i, Finset.mem_filter.mpr ⟨hiS, hpos⟩⟩
  · push Not at hpos
    have hneg : 0 < (-d) i := by
      rw [Finsupp.neg_apply]
      have : d i < 0 := lt_of_le_of_ne hpos hdi
      linarith
    have hdsupp' : (-d).support ⊆ ↑S := by
      rw [Finsupp.support_neg]
      exact hdsupp
    have hrel' : Finsupp.linearCombination ℝ id (-d) = 0 := by
      rw [map_neg, hrel, neg_zero]
    exact step hdsupp' hrel' ⟨i, Finset.mem_filter.mpr ⟨hiS, hneg⟩⟩

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Every cone element has a representation over an independent subset. -/
private lemma hull_indep_repr {S : Finset E} {y : E}
    (hy : y ∈ PointedCone.hull ℝ (↑S : Set E)) :
    ∃ T : Finset E, T ⊆ S ∧ LinearIndependent ℝ ((↑) : T → E) ∧
      y ∈ PointedCone.hull ℝ (↑T : Set E) := by
  classical
  induction S using Finset.strongInduction with
  | H S IH =>
    by_cases hindep : LinearIndependent ℝ ((↑) : S → E)
    · exact ⟨S, Finset.Subset.rfl, hindep, hy⟩
    · rw [linearIndependent_iff] at hindep
      push Not at hindep
      obtain ⟨l, hl0, hln⟩ := hindep
      set e : ↥S ↪ E := Function.Embedding.subtype (· ∈ S)
      set d : E →₀ ℝ := l.embDomain e with hddef
      have hdsupp : d.support ⊆ ↑S := by
        intro i hi
        rw [hddef, Finsupp.support_embDomain] at hi
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
        exact a.property
      have hd : d ≠ 0 := by
        rw [hddef, Ne, Finsupp.embDomain_eq_zero]
        exact hln
      have hrel : Finsupp.linearCombination ℝ id d = 0 := by
        rw [hddef, Finsupp.linearCombination_embDomain]
        have : (id ∘ e : ↥S → E) = ((↑) : ↥S → E) := rfl
        rw [this]
        exact hl0
      obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp hy
      have hcomb' : Finsupp.linearCombination ℝ id c = y := by
        simpa [Finsupp.linearCombination_apply] using hcomb
      obtain ⟨j, hjS, hy'⟩ := hull_elim hc hsupp hd hdsupp hrel hcomb'
      obtain ⟨T, hTS, hindepT, hyT⟩ :=
        IH (S.erase j) (Finset.erase_ssubset hjS) hy'
      exact ⟨T, hTS.trans (Finset.erase_subset _ _), hindepT, hyT⟩

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Finitely generated cones are closed. -/
private lemma isClosed_hull_finset (S : Finset E) :
    IsClosed (PointedCone.hull ℝ (↑S : Set E) : Set E) := by
  classical
  apply IsSeqClosed.isClosed
  intro f x hfs hf
  have hrep : ∀ n, ∃ T : Finset E, T ⊆ S ∧
      LinearIndependent ℝ ((↑) : T → E) ∧
        f n ∈ PointedCone.hull ℝ (↑T : Set E) :=
    fun n => hull_indep_repr (hfs n)
  choose T hTS hindep hmemT using hrep
  set g : ℕ → ↥(S.powerset) :=
    fun n => ⟨T n, Finset.mem_powerset.mpr (hTS n)⟩ with hgdef
  obtain ⟨T₀, hfib⟩ := Finite.exists_infinite_fiber g
  have hfib' : {n : ℕ | T n = (T₀ : Finset E)}.Infinite := by
    have heq : g ⁻¹' {T₀} = {n : ℕ | T n = (T₀ : Finset E)} := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rw [Subtype.ext_iff]
    rw [← heq]
    exact Set.infinite_coe_iff.mp hfib
  set e := @Infinite.natEmbedding _ hfib'.to_subtype with hedef
  set φ : ℕ → ℕ :=
    fun n => ((e n : ↥{n : ℕ | T n = (T₀ : Finset E)}) : ℕ) with hφdef
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp e.injective
  have hφtop : Tendsto φ atTop atTop := hφinj.nat_tendsto_atTop
  have hφmem : ∀ n, T (φ n) = (T₀ : Finset E) := fun n => (e n).property
  have hflim : Tendsto (f ∘ φ) atTop (𝓝 x) := hf.comp hφtop
  have hmemφ : ∀ n, (f ∘ φ) n ∈
      PointedCone.hull ℝ (↑(T₀ : Finset E) : Set E) := by
    intro n
    rw [← hφmem n]
    exact hmemT (φ n)
  have hT0indep : LinearIndependent ℝ ((↑) : ↥(T₀ : Finset E) → E) := by
    have h := hindep (φ 0)
    rwa [hφmem 0] at h
  set G : (↥(T₀ : Finset E) → ℝ) →ₗ[ℝ] E :=
    ∑ i : ↥(T₀ : Finset E), (LinearMap.proj i).smulRight (i : E) with hGdef
  have hGapply : ∀ r : ↥(T₀ : Finset E) → ℝ,
      G r = ∑ i : ↥(T₀ : Finset E), r i • (i : E) := by
    intro r
    simp [hGdef, LinearMap.sum_apply]
  have hGker : ∀ r : ↥(T₀ : Finset E) → ℝ, G r = 0 → r = 0 := by
    intro r hr
    have hsum : (∑ i : ↥(T₀ : Finset E), r i • ((i : ↥(T₀ : Finset E)) : E)) = 0 := by
      rw [← hGapply]
      exact hr
    have h0 := (linearIndependent_iff.mp hT0indep)
      (Finsupp.onFinset Finset.univ r (fun a _ => Finset.mem_univ a))
      (by rw [Finsupp.linearCombination_onFinset]; exact hsum)
    funext i
    have hci := congr_fun (congr_arg DFunLike.coe h0) i
    simpa using hci
  have hGinj : Function.Injective G := by
    intro r₁ r₂ h
    have h0 : r₁ - r₂ = 0 := hGker _ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp h0
  have hcrep : ∀ n, ∃ r : ↥(T₀ : Finset E) → ℝ,
      (∀ i, 0 ≤ r i) ∧ G r = (f ∘ φ) n := by
    intro n
    obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp (hmemφ n)
    refine ⟨fun i => c (i : E), fun i => hc _, ?_⟩
    have hsum : Finsupp.linearCombination ℝ id c =
        ∑ i : ↥(T₀ : Finset E), c (i : E) • ((i : ↥(T₀ : Finset E)) : E) := by
      have hfin : Finsupp.linearCombination ℝ id c =
          ∑ i ∈ (T₀ : Finset E), c i • (i : E) := by
        rw [Finsupp.linearCombination_apply]
        exact Finsupp.sum_of_support_subset c hsupp _ (fun i _ => by simp)
      rw [hfin, ← Finset.sum_attach]
      rfl
    rw [hGapply]
    rw [← hsum]
    simpa [Finsupp.linearCombination_apply] using hcomb
  choose r hrnonneg hrG using hcrep
  set RG := LinearMap.range G with hRGdef
  have hRGclosed : IsClosed (↑RG : Set E) :=
    Submodule.closed_of_finiteDimensional RG
  have hmemRG : ∀ n, (f ∘ φ) n ∈ RG := fun n => ⟨r n, hrG n⟩
  have hyRG : x ∈ RG :=
    hRGclosed.mem_of_tendsto hflim (Filter.Eventually.of_forall hmemRG)
  have hyRGmem := hyRG
  obtain ⟨rstar, hrstar⟩ := hyRG
  have hHcont : Continuous
      ((LinearEquiv.ofInjective G hGinj).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  have hsub : Tendsto (fun n => (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) atTop
      (𝓝 ⟨x, hyRGmem⟩) :=
    tendsto_subtype_rng.mpr hflim
  have hrlim : Tendsto r atTop (𝓝 rstar) := by
    have h1 : Tendsto
        (fun n => (LinearEquiv.ofInjective G hGinj).symm.toLinearMap
          (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) atTop
        (𝓝 ((LinearEquiv.ofInjective G hGinj).symm.toLinearMap ⟨x, hyRGmem⟩)) :=
      (hHcont.tendsto _).comp hsub
    have h2 : (fun n => (LinearEquiv.ofInjective G hGinj).symm.toLinearMap
        (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) = r := by
      funext n
      have hmem : (⟨(f ∘ φ) n, hmemRG n⟩ : RG)
          = (LinearEquiv.ofInjective G hGinj) (r n) :=
        Subtype.ext (hrG n).symm
      rw [hmem]
      change (LinearEquiv.ofInjective G hGinj).symm
        ((LinearEquiv.ofInjective G hGinj) (r n)) = r n
      exact LinearEquiv.symm_apply_apply _ _
    have h3 : (LinearEquiv.ofInjective G hGinj).symm.toLinearMap ⟨x, hyRGmem⟩
        = rstar := by
      have hmem : (⟨x, hyRGmem⟩ : RG)
          = (LinearEquiv.ofInjective G hGinj) rstar :=
        Subtype.ext hrstar.symm
      rw [hmem]
      change (LinearEquiv.ofInjective G hGinj).symm
        ((LinearEquiv.ofInjective G hGinj) rstar) = rstar
      exact LinearEquiv.symm_apply_apply _ _
    rw [h2, h3] at h1
    exact h1
  have hrstar_nonneg : ∀ i, 0 ≤ rstar i := by
    intro i
    apply ge_of_tendsto (tendsto_pi_nhds.mp hrlim i)
    filter_upwards with n
    exact hrnonneg n i
  have hxG : G rstar = x := by
    have h1 : Tendsto (G ∘ r) atTop (𝓝 (G rstar)) :=
      ((LinearMap.continuous_of_finiteDimensional G).tendsto _).comp hrlim
    have h2 : (G ∘ r) = (f ∘ φ) := funext (fun n => hrG n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hflim
  have hxrep : x ∈ PointedCone.hull ℝ (↑(T₀ : Finset E) : Set E) := by
    apply PointedCone.mem_hull_set.mpr
    refine ⟨∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i), ?_, ?_, ?_⟩
    · intro j hj
      have hne : (∑ i : ↥(T₀ : Finset E),
          Finsupp.single (i : E) (rstar i)) j ≠ 0 :=
        Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      by_contra hjS
      have hzero : ∀ i : ↥(T₀ : Finset E),
          (Finsupp.single (i : E) (rstar i)) j = 0 := by
        intro i
        apply Finsupp.single_eq_of_ne
        intro hcon
        exact hjS (hcon ▸ i.property)
      have : (∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i)) j = 0 := by
        rw [Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero (fun i _ => hzero i)
      exact hne this
    · intro j
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_nonneg
      intro i _
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h
        exact hrstar_nonneg i
      · exact le_rfl
    · change Finsupp.linearCombination ℝ id
          (∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i)) = x
      rw [map_sum]
      simp only [Finsupp.linearCombination_single]
      change (∑ x : ↥(T₀ : Finset E), rstar x • ((x : ↥(T₀ : Finset E)) : E)) = x
      rw [← hGapply, hxG]
  exact Submodule.span_mono
    (Finset.coe_subset.mpr (Finset.mem_powerset.mp T₀.property)) hxrep

section Farkas

variable {p q : ℕ}

/-- LP cone generators: scaled columns, slacks, and the value direction. -/
private noncomputable def lpConeGens (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    Finset ((Fin p → ℝ) × ℝ) :=
  (Finset.univ.image (fun i : Fin q => ((fun j => M j i), e i))) ∪
  (Finset.univ.image
    (fun j : Fin p => (Pi.single (M := fun _ => ℝ) j 1, 0))) ∪
  {((0 : Fin p → ℝ), -1)}

/-- The LP cone: image points above achievable values. -/
private def lpCone (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    Set ((Fin p → ℝ) × ℝ) :=
  {zw | ∃ x : Fin q → ℝ, (∀ i, 0 ≤ x i) ∧ ∃ s : Fin p → ℝ, (∀ j, 0 ≤ s j) ∧
    ∃ r : ℝ, 0 ≤ r ∧ zw.1 = M.mulVec x + s ∧ zw.2 = e ⬝ᵥ x - r}

/-- Column generators lie in the cone. -/
private lemma lpCone_gen_col (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (i : Fin q) : ((fun j => M j i), e i) ∈ lpCone M e := by
  refine ⟨Pi.single (M := fun _ => ℝ) i 1, fun k => ?_, 0, fun j => by simp,
    0, le_rfl, ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs with h
    · exact zero_le_one
    · exact le_rfl
  · change (fun j => M j i) = M.mulVec (Pi.single (M := fun _ => ℝ) i 1) + 0
    rw [add_zero]
    funext j
    change M j i = (∑ k, M j k * Pi.single (M := fun _ => ℝ) i 1 k)
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      have h0 : Pi.single (M := fun _ => ℝ) i 1 b = 0 := by
        rw [Pi.single_apply, ite_eq_right hb]
      rw [h0, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · change e i = e ⬝ᵥ Pi.single (M := fun _ => ℝ) i 1 - 0
    rw [sub_zero]
    exact (dotProduct_single_one e i).symm

/-- Slack generators lie in the cone. -/
private lemma lpCone_gen_slack (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (j : Fin p) : (Pi.single (M := fun _ => ℝ) j 1, 0) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = 0 := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, Pi.single (M := fun _ => ℝ) j 1, fun k => ?_,
    0, le_rfl, ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs with h
    · exact zero_le_one
    · exact le_rfl
  · change Pi.single (M := fun _ => ℝ) j 1
      = M.mulVec (0 : Fin q → ℝ) + Pi.single (M := fun _ => ℝ) j 1
    rw [hM0, zero_add]
  · change (0 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 0
    rw [hd0, sub_zero]

/-- The value-direction generator lies in the cone. -/
private lemma lpCone_gen_val (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    ((0 : Fin p → ℝ), -1) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = (0 : Fin p → ℝ) := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, 0, fun j => by simp, 1, zero_le_one, ?_, ?_⟩
  · change (0 : Fin p → ℝ) = M.mulVec (0 : Fin q → ℝ) + 0
    rw [hM0, add_zero]
  · change (-1 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 1
    rw [hd0]
    exact (zero_sub 1).symm

/-- The cone contains the origin. -/
private lemma lpCone_zero (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    ((0 : Fin p → ℝ), 0) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = (0 : Fin p → ℝ) := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, 0, fun j => by simp, 0, le_rfl, ?_, ?_⟩
  · change (0 : Fin p → ℝ) = M.mulVec (0 : Fin q → ℝ) + 0
    rw [hM0, add_zero]
  · change (0 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 0
    rw [hd0, sub_zero]

/-- The cone is closed under addition. -/
private lemma lpCone_add (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (a b : (Fin p → ℝ) × ℝ) :
    a ∈ lpCone M e → b ∈ lpCone M e → a + b ∈ lpCone M e := by
  rintro ⟨x₁, hx₁, s₁, hs₁, r₁, hr₁, h1a, h1b⟩
    ⟨x₂, hx₂, s₂, hs₂, r₂, hr₂, h2a, h2b⟩
  refine ⟨x₁ + x₂, fun i => add_nonneg (hx₁ i) (hx₂ i),
    s₁ + s₂, fun j => add_nonneg (hs₁ j) (hs₂ j),
    r₁ + r₂, add_nonneg hr₁ hr₂, ?_, ?_⟩
  · change a.1 + b.1 = M.mulVec (x₁ + x₂) + (s₁ + s₂)
    have e1 : M.mulVec (x₁ + x₂) = M.mulVec x₁ + M.mulVec x₂ :=
      map_add (Matrix.mulVecLin M) x₁ x₂
    rw [e1, h1a, h2a]
    abel
  · change a.2 + b.2 = e ⬝ᵥ (x₁ + x₂) - (r₁ + r₂)
    have e2 : e ⬝ᵥ (x₁ + x₂) = e ⬝ᵥ x₁ + e ⬝ᵥ x₂ :=
      dotProduct_add _ _ _
    rw [e2, h1b, h2b]
    ring

/-- The cone is closed under nonnegative scaling. -/
private lemma lpCone_smul (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (y : (Fin p → ℝ) × ℝ) :
    y ∈ lpCone M e → a • y ∈ lpCone M e := by
  rintro ⟨x, hx, s, hs, r, hr, h1, h2⟩
  refine ⟨a • x, fun i => smul_nonneg ha (hx i),
    a • s, fun j => smul_nonneg ha (hs j),
    a * r, mul_nonneg ha hr, ?_, ?_⟩
  · change a • y.1 = M.mulVec (a • x) + a • s
    have e1 : M.mulVec (a • x) = a • M.mulVec x :=
      map_smul (Matrix.mulVecLin M) a x
    rw [e1, h1, smul_add]
  · change a • y.2 = e ⬝ᵥ (a • x) - a * r
    have e2 : e ⬝ᵥ (a • x) = a • (e ⬝ᵥ x) :=
      dotProduct_smul _ _ _
    rw [e2, h2]
    simp only [smul_eq_mul]
    ring

/-- Generated cone points lie in the cone. -/
private lemma hull_subset_lpCone (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    (PointedCone.hull ℝ (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :
      Set ((Fin p → ℝ) × ℝ)) ⊆ lpCone M e := by
  intro y hy
  obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp hy
  have hterm : ∀ v ∈ c.support, c v • v ∈ lpCone M e := by
    intro v hv
    have hmem : v ∈ lpConeGens M e := hsupp hv
    unfold lpConeGens at hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    obtain (h1 | h2) | hk := hmem
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
      rw [← hi]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_col M e i)
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
      rw [← hj]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_slack M e j)
    · rw [Finset.mem_singleton] at hk
      rw [hk]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_val M e)
  have hsum : (∑ v ∈ c.support, c v • v) ∈ lpCone M e :=
    Finset.sum_induction _ _ (lpCone_add M e) (lpCone_zero M e) hterm
  have hyeq : y = ∑ v ∈ c.support, c v • v := by
    rw [← hcomb]
    change c.sum (fun v a => a • v) = ∑ v ∈ c.support, c v • v
    rfl
  rw [hyeq]
  exact hsum

/-- The LP cone as a proper cone. -/
private noncomputable def lpProperCone (M : Matrix (Fin p) (Fin q) ℝ)
    (e : Fin q → ℝ) : ProperCone ℝ ((Fin p → ℝ) × ℝ) where
  carrier := PointedCone.hull ℝ (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))
  add_mem' := (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).add_mem
  zero_mem' := (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).zero_mem
  smul_mem' := fun c _ hx => (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).smul_mem c.property hx
  isClosed' := isClosed_hull_finset _

/-- A point outside the cone separates. -/
private lemma lpCone_separate (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (d : Fin p → ℝ) (t : ℝ) (h : (d, t) ∉ lpCone M e) :
    ∃ f : StrongDual ℝ ((Fin p → ℝ) × ℝ),
      (∀ x ∈ PointedCone.hull ℝ
        (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)), 0 ≤ f x) ∧ f (d, t) < 0 := by
  have hnotin : (d, t) ∉ PointedCone.hull ℝ
      (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :=
    fun hm => h (hull_subset_lpCone M e hm)
  obtain ⟨f, hfC, hflt⟩ :=
    (lpProperCone M e).hyperplane_separation_point (by simpa [lpProperCone] using hnotin)
  exact ⟨f, hfC, hflt⟩

/-- Cone membership unfolds to a feasible point dominating the value. -/
private lemma mem_lpCone_iff (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (d : Fin p → ℝ) (t : ℝ) :
    (d, t) ∈ lpCone M e ↔ ∃ x : Fin q → ℝ, (∀ i, 0 ≤ x i) ∧
      (∀ j, (M.mulVec x) j ≤ d j) ∧ t ≤ e ⬝ᵥ x := by
  constructor
  · rintro ⟨x, hx, s, hs, r, hr, h1, h2⟩
    have h1' : d = M.mulVec x + s := h1
    have h2' : t = e ⬝ᵥ x - r := h2
    refine ⟨x, hx, fun j => ?_, ?_⟩
    · rw [h1', Pi.add_apply]
      exact le_add_of_nonneg_right (hs j)
    · rw [h2']
      exact sub_le_self _ hr
  · rintro ⟨x, hx, hAx, htx⟩
    refine ⟨x, hx, d - M.mulVec x, fun j => ?_, e ⬝ᵥ x - t, ?_, ?_, ?_⟩
    · rw [Pi.sub_apply]
      exact sub_nonneg.mpr (hAx j)
    · exact sub_nonneg.mpr htx
    · change d = M.mulVec x + (d - M.mulVec x)
      exact (add_sub_cancel _ _).symm
    · change t = e ⬝ᵥ x - (e ⬝ᵥ x - t)
      exact (sub_sub_cancel _ _).symm

/-- Column generators belong to the generator set. -/
private lemma lpConeGens_col_mem (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (i : Fin q) : ((fun j => M j i), e i) ∈ lpConeGens M e := by
  unfold lpConeGens
  rw [Finset.mem_union, Finset.mem_union]
  exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

/-- Slack generators belong to the generator set. -/
private lemma lpConeGens_slack_mem (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (j : Fin p) :
    (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ)) ∈ lpConeGens M e := by
  unfold lpConeGens
  rw [Finset.mem_union, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))

/-- The value generator belongs to the generator set. -/
private lemma lpConeGens_val_mem (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    ((0 : Fin p → ℝ), -1) ∈ lpConeGens M e := by
  unfold lpConeGens
  rw [Finset.mem_union, Finset.mem_union]
  exact Or.inr (Finset.mem_singleton.mpr rfl)

/-- The LP cone is exactly the cone generated by its generators. -/
private lemma lpCone_eq (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    lpCone M e = PointedCone.hull ℝ
      (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) := by
  refine Set.eq_of_subset_of_subset ?_ (hull_subset_lpCone M e)
  rintro zw ⟨x, hx, s, hs, r, hr, h1, h2⟩
  set c : ((Fin p → ℝ) × ℝ) →₀ ℝ :=
    (∑ i : Fin q, x i • Finsupp.single ((fun j => M j i), e i) 1) +
    (∑ j : Fin p, s j • Finsupp.single (Pi.single (M := fun _ => ℝ) j 1, 0) 1) +
    r • Finsupp.single ((0 : Fin p → ℝ), -1) 1 with hcdef
  apply PointedCone.mem_hull_set.mpr
  refine ⟨c, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ c.support := Finset.mem_coe.mp hv
    rw [Finsupp.mem_support_iff] at hv'
    by_contra hcon
    apply hv'
    have g1 : ∀ i : Fin q,
        (Finsupp.single ((fun j => M j i), e i) (1 : ℝ)) v = 0 := by
      intro i
      apply Finsupp.single_eq_of_ne
      intro hgi
      apply hcon
      rw [hgi]
      exact lpConeGens_col_mem M e i
    have g2 : ∀ j : Fin p,
        (Finsupp.single (Pi.single (M := fun _ => ℝ) j 1, 0) (1 : ℝ)) v = 0 := by
      intro j
      apply Finsupp.single_eq_of_ne
      intro hgj
      apply hcon
      rw [hgj]
      exact lpConeGens_slack_mem M e j
    have g3 : (Finsupp.single ((0 : Fin p → ℝ), -1) (1 : ℝ)) v = 0 := by
      apply Finsupp.single_eq_of_ne
      intro hg3
      apply hcon
      rw [hg3]
      exact lpConeGens_val_mem M e
    simp only [hcdef, Finsupp.add_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    have e1 : (∑ i : Fin q,
        x i * (Finsupp.single ((fun j => M j i), e i) (1 : ℝ)) v) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [g1 i, mul_zero]
    have e2 : (∑ j : Fin p,
        s j * (Finsupp.single (Pi.single (M := fun _ => ℝ) j 1, 0) (1 : ℝ)) v) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [g2 j, mul_zero]
    have e3 : r * (Finsupp.single ((0 : Fin p → ℝ), -1) (1 : ℝ)) v = 0 := by
      rw [g3, mul_zero]
    rw [e1, e2, e3, add_zero, add_zero]
  · intro v
    simp only [hcdef, Finsupp.add_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact sum_nonneg fun i _ => mul_nonneg (hx i)
        (by rw [Finsupp.single_apply]; split_ifs <;> positivity)
    · exact sum_nonneg fun j _ => mul_nonneg (hs j)
        (by rw [Finsupp.single_apply]; split_ifs <;> positivity)
    · exact mul_nonneg hr
        (by rw [Finsupp.single_apply]; split_ifs <;> positivity)
  · change Finsupp.linearCombination ℝ id c = zw
    have padd : ∀ a b : (Fin p → ℝ) × ℝ, (a + b).1 = a.1 + b.1 :=
      fun a b => rfl
    have psmul : ∀ (t : ℝ) (v : (Fin p → ℝ) × ℝ), (t • v).1 = t • v.1 :=
      fun t v => rfl
    have psnd_add : ∀ a b : (Fin p → ℝ) × ℝ, (a + b).2 = a.2 + b.2 :=
      fun a b => rfl
    have psnd_smul : ∀ (t : ℝ) (v : (Fin p → ℝ) × ℝ), (t • v).2 = t • v.2 :=
      fun t v => rfl
    have hLc : Finsupp.linearCombination ℝ id c
          = (∑ i : Fin q, x i • ((fun j => M j i), e i))
          + (∑ j : Fin p, s j • (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ)))
          + r • ((0 : Fin p → ℝ), -1) := by
      simp only [hcdef, map_add, map_sum, map_smul,
        Finsupp.linearCombination_single, one_smul, id_eq]
    rw [hLc]
    apply Prod.ext
    · rw [h1]
      simp only [padd, psmul, Prod.fst_sum]
      change (∑ i : Fin q, x i • (fun j => M j i))
        + (∑ j : Fin p, s j • Pi.single (M := fun _ => ℝ) j 1)
        + r • (0 : Fin p → ℝ) = M.mulVec x + s
      rw [smul_zero, add_zero]
      funext k
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hMx : (M.mulVec x) k = ∑ i, M k i * x i := by
        simp only [Matrix.mulVec, dotProduct]
      have hslack : (∑ j : Fin p, s j * Pi.single (M := fun _ => ℝ) j 1 k)
          = s k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      rw [hMx, hslack]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · rw [h2]
      simp only [psnd_add, psnd_smul, Prod.snd_sum]
      change (∑ i : Fin q, x i • e i) + (∑ j : Fin p, s j • (0 : ℝ))
        + r • (-1) = e ⬝ᵥ x - r
      simp only [smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
      have hdot : e ⬝ᵥ x = ∑ i, e i * x i := rfl
      rw [hdot]
      have hsum : (∑ i : Fin q, x i * e i) = ∑ i : Fin q, e i * x i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have hr1 : r * (-1 : ℝ) = -r := by ring
      rw [hsum, hr1, sub_eq_add_neg]

/-- The LP cone is closed. -/
private lemma isClosed_lpCone (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    IsClosed (lpCone M e) := by
  rw [lpCone_eq]
  exact isClosed_hull_finset _

/-- Farkas alternative: a point outside the LP cone yields a separating
certificate `(y, α)` with `y ≥ 0`, `α ≤ 0`, `Mᵀy + αe ≥ 0` and
strict negativity at the point. -/
private lemma farkas_alternative (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (d : Fin p → ℝ) (t : ℝ) (h : (d, t) ∉ lpCone M e) :
    ∃ y : Fin p → ℝ, ∃ α : ℝ, (∀ j, 0 ≤ y j) ∧ α ≤ 0 ∧
      (∀ i, 0 ≤ (Mᵀ.mulVec y) i + α * e i) ∧ d ⬝ᵥ y + t * α < 0 := by
  obtain ⟨f, hfC, hflt⟩ := lpCone_separate M e d t h
  have hsupp_id : ∀ z : Fin p → ℝ,
      z = ∑ j : Fin p, z j • Pi.single (M := fun _ => ℝ) j 1 := by
    intro z
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hexpand : ∀ z : Fin p → ℝ, ∀ u : ℝ,
      f (z, u) = z ⬝ᵥ (fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0))
        + u * f ((0 : Fin p → ℝ), 1) := by
    intro z u
    have hpair : (z, u) = (z, (0 : ℝ)) + ((0 : Fin p → ℝ), u) := by
      apply Prod.ext
      · simp
      · simp
    have hz : (z, (0 : ℝ))
        = ∑ j : Fin p, z j • (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ)) := by
      apply Prod.ext
      · have e1 : (∑ j : Fin p,
            z j • (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ))).1
            = ∑ j : Fin p, z j • Pi.single (M := fun _ => ℝ) j 1 := by
          rw [Prod.fst_sum]
          exact Finset.sum_congr rfl fun j _ => rfl
        rw [e1]
        change z = ∑ j : Fin p, z j • Pi.single (M := fun _ => ℝ) j 1
        exact hsupp_id z
      · have e2 : (∑ j : Fin p,
            z j • (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ))).2
            = ∑ j : Fin p, z j • (0 : ℝ) := by
          rw [Prod.snd_sum]
          exact Finset.sum_congr rfl fun j _ => rfl
        rw [e2]
        change (0 : ℝ) = ∑ j : Fin p, z j • (0 : ℝ)
        simp
    have hu : ((0 : Fin p → ℝ), u) = u • ((0 : Fin p → ℝ), (1 : ℝ)) := by
      apply Prod.ext
      · simp
      · simp
    rw [hpair, map_add, hz, hu, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hdot : (∑ j : Fin p,
        z j * f (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ)))
        = z ⬝ᵥ (fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0)) := rfl
    rw [hdot]
  have hmcol : ∀ i : Fin q,
      ((fun j => M j i), e i) ∈ PointedCone.hull ℝ
        (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :=
    fun i => PointedCone.subset_hull (Finset.mem_coe.mpr (lpConeGens_col_mem M e i))
  have hmslack : ∀ j : Fin p,
      (Pi.single (M := fun _ => ℝ) j 1, (0 : ℝ)) ∈ PointedCone.hull ℝ
        (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :=
    fun j => PointedCone.subset_hull (Finset.mem_coe.mpr (lpConeGens_slack_mem M e j))
  have hmval : ((0 : Fin p → ℝ), -1) ∈ PointedCone.hull ℝ
      (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :=
    PointedCone.subset_hull (Finset.mem_coe.mpr (lpConeGens_val_mem M e))
  refine ⟨fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0),
    f ((0 : Fin p → ℝ), 1), ?_, ?_, ?_, ?_⟩
  · intro j
    have h := hfC _ (hmslack j)
    rw [hexpand] at h
    simpa [dotProduct_single_one] using h
  · have h := hfC _ hmval
    rw [hexpand] at h
    have hz : (0 : Fin p → ℝ) ⬝ᵥ
        (fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0)) = 0 := by
      change (∑ j, (0 : Fin p → ℝ) j * f (Pi.single (M := fun _ => ℝ) j 1, 0))
        = 0
      simp
    rw [hz, zero_add, neg_one_mul] at h
    linarith
  · intro i
    have h := hfC _ (hmcol i)
    rw [hexpand] at h
    have hcol : (Mᵀ.mulVec (fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0))) i
        = (fun j => M j i) ⬝ᵥ (fun j => f (Pi.single (M := fun _ => ℝ) j 1, 0)) :=
      rfl
    rw [hcol]
    have hcomm : f ((0 : Fin p → ℝ), 1) * e i = e i * f ((0 : Fin p → ℝ), 1) :=
      mul_comm _ _
    rw [hcomm]
    exact h
  · have h := hflt
    rwa [hexpand] at h

end Farkas

section AttainDuality

variable {m n : ℕ}

/-- A feasible bounded-above LP attains its supremum. -/
private lemma lp_max_attains (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (e : Fin n → ℝ) (x₀ : Fin n → ℝ) (hx₀ : ∀ i, 0 ≤ x₀ i)
    (hAx₀ : ∀ j, (M.mulVec x₀) j ≤ b j) (Mbd : ℝ)
    (hbd : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, (M.mulVec x) j ≤ b j) → e ⬝ᵥ x ≤ Mbd) :
    ∃ xopt : Fin n → ℝ, (∀ i, 0 ≤ xopt i) ∧ (∀ j, (M.mulVec xopt) j ≤ b j) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
        (∀ j, (M.mulVec x) j ≤ b j) → e ⬝ᵥ x ≤ e ⬝ᵥ xopt := by
  set F : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∀ j, (M.mulVec x) j ≤ b j}
  set S : Set ℝ := {v | ∃ x ∈ F, e ⬝ᵥ x = v}
  have hF0 : x₀ ∈ F := ⟨hx₀, hAx₀⟩
  have hSne : S.Nonempty := ⟨e ⬝ᵥ x₀, x₀, hF0, rfl⟩
  have hSbdd : BddAbove S := ⟨Mbd, by
    rintro v ⟨x, hxF, rfl⟩
    exact hbd x hxF.1 hxF.2⟩
  have hseq : ∀ k : ℕ, ∃ x ∈ F, sSup S - 1 / ((k : ℝ) + 1) < e ⬝ᵥ x := by
    intro k
    have hlt : sSup S - 1 / ((k : ℝ) + 1) < sSup S := by
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨w, hwS, hltw⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
    obtain ⟨x, hxF, rfl⟩ := hwS
    exact ⟨x, hxF, hltw⟩
  choose xk hxkF hxklt using hseq
  have hlim : Tendsto (fun k : ℕ => e ⬝ᵥ (xk k)) atTop (nhds (sSup S)) := by
    have h1 : Tendsto (fun k : ℕ => sSup S - e ⬝ᵥ (xk k)) atTop (nhds 0) := by
      refine squeeze_zero (fun k => sub_nonneg.mpr
        (le_csSup hSbdd ⟨xk k, hxkF k, rfl⟩)) (fun k => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hkk := hxklt k
      linarith
    have h2 : Tendsto (fun k : ℕ => sSup S - (sSup S - e ⬝ᵥ (xk k))) atTop
        (nhds (sSup S - 0)) :=
      tendsto_const_nhds.sub h1
    rw [sub_zero] at h2
    have heq : (fun k : ℕ => sSup S - (sSup S - e ⬝ᵥ (xk k)))
        = (fun k : ℕ => e ⬝ᵥ (xk k)) :=
      funext fun k => sub_sub_cancel _ _
    rw [heq] at h2
    exact h2
  have hmem_each : ∀ k : ℕ, ((b : Fin m → ℝ), e ⬝ᵥ (xk k)) ∈ lpCone M e := by
    intro k
    rw [mem_lpCone_iff]
    exact ⟨xk k, (hxkF k).1, (hxkF k).2, le_rfl⟩
  have htend : Tendsto (fun k : ℕ => ((b : Fin m → ℝ), e ⬝ᵥ (xk k))) atTop
      (nhds (b, sSup S)) :=
    tendsto_const_nhds.prodMk_nhds hlim
  have hclosed : IsClosed (lpCone M e) := isClosed_lpCone M e
  have hlim_mem : (b, sSup S) ∈ lpCone M e :=
    hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hmem_each)
  obtain ⟨xopt, hxopt1, hxopt2, hle⟩ := (mem_lpCone_iff M e b (sSup S)).mp hlim_mem
  have hval : e ⬝ᵥ xopt = sSup S :=
    le_antisymm (le_csSup hSbdd ⟨xopt, ⟨hxopt1, hxopt2⟩, rfl⟩) hle
  refine ⟨xopt, hxopt1, hxopt2, fun x hx1 hx2 => ?_⟩
  rw [hval]
  exact le_csSup hSbdd ⟨x, ⟨hx1, hx2⟩, rfl⟩

/-- Transpose unfolding for the dual certificate. -/
private lemma transpose_mulVec_apply (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin m → ℝ) (i : Fin n) :
    (Aᵀ.mulVec w) i = ((fun j => A j i) ⬝ᵥ w) := rfl

/-- Dual feasibility in negated form. -/
private lemma dualNegFeas (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (h : ∀ i, c i ≤ (Aᵀ.mulVec y) i) :
    ∀ i, (((-Aᵀ).mulVec y) i ≤ (-c) i) := by
  intro i
  have h1 : (((-Aᵀ).mulVec y)) i = -((Aᵀ.mulVec y) i) := by
    rw [Matrix.neg_mulVec, Pi.neg_apply]
  have h3 : (-c) i = -(c i) := rfl
  rw [h1, h3]
  exact neg_le_neg_iff.mpr (h i)

/-- Dual feasibility in positive form. -/
private lemma dualPosFeas (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (h : ∀ i, (((-Aᵀ).mulVec y) i ≤ (-c) i)) :
    ∀ i, c i ≤ (Aᵀ.mulVec y) i := by
  intro i
  have h2 := h i
  have h1 : (((-Aᵀ).mulVec y)) i = -((Aᵀ.mulVec y) i) := by
    rw [Matrix.neg_mulVec, Pi.neg_apply]
  have h3 : (-c) i = -(c i) := rfl
  rw [h1, h3] at h2
  exact neg_le_neg_iff.mp h2

/-- Above every suboptimal value sits a dual-feasible point. -/
private lemma dual_value_approach (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xopt : Fin n → ℝ) (hxopt : ∀ i, 0 ≤ xopt i)
    (hAxopt : ∀ j, (A.mulVec xopt) j ≤ b j)
    (hmax : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, (A.mulVec x) j ≤ b j) → c ⬝ᵥ x ≤ c ⬝ᵥ xopt)
    (t : ℝ) (ht : c ⬝ᵥ xopt < t) :
    ∃ y : Fin m → ℝ, (∀ j, 0 ≤ y j) ∧
      (∀ i, c i ≤ (Aᵀ.mulVec y) i) ∧ b ⬝ᵥ y < t := by
  have hnotin : (b, t) ∉ lpCone A c := by
    intro hmem
    obtain ⟨x, hx1, hx2, htx⟩ := (mem_lpCone_iff A c b t).mp hmem
    exact absurd (hmax x hx1 hx2) (not_le.mpr (lt_of_lt_of_le ht htx))
  obtain ⟨y, α, hy, hα, hcol, hstrict⟩ := farkas_alternative A c b t hnotin
  have hαneg : α < 0 := by
    by_contra hcon
    push Not at hcon
    have hα0 : α = 0 := le_antisymm hα hcon
    have h1 : (Aᵀ.mulVec y) ⬝ᵥ xopt ≤ b ⬝ᵥ y := by
      calc
        (Aᵀ.mulVec y) ⬝ᵥ xopt = xopt ⬝ᵥ Aᵀ.mulVec y := dotProduct_comm _ _
        _ = y ⬝ᵥ A.mulVec xopt := Matrix.dotProduct_transpose_mulVec A xopt y
        _ ≤ b ⬝ᵥ y := sum_le_sum fun j _ => (mul_comm (y j) _).le.trans
          (mul_le_mul_of_nonneg_right (hAxopt j) (hy j))
    have h2 : (0 : ℝ) ≤ (Aᵀ.mulVec y) ⬝ᵥ xopt := by
      change (0 : ℝ) ≤ ∑ i, (Aᵀ.mulVec y) i * xopt i
      apply sum_nonneg
      intro i _
      have hci := hcol i
      rw [hα0, zero_mul, add_zero] at hci
      exact mul_nonneg hci (hxopt i)
    have h3 : b ⬝ᵥ y < 0 := by
      have hs := hstrict
      rwa [hα0, mul_zero, add_zero] at hs
    linarith
  have hpos : (0 : ℝ) < -α := neg_pos.mpr hαneg
  refine ⟨(-α)⁻¹ • y, fun j => smul_nonneg (inv_nonneg.mpr hpos.le) (hy j),
    ?_, ?_⟩
  · intro i
    have hAT : (Aᵀ.mulVec ((-α)⁻¹ • y)) i = (-α)⁻¹ * ((Aᵀ.mulVec y) i) := by
      simp only [transpose_mulVec_apply, dotProduct_smul, smul_eq_mul]
    rw [hAT, inv_mul_eq_div, le_div_iff₀ hpos]
    have hle : c i * -α ≤ (Aᵀ.mulVec y) i := by
      have hci := hcol i
      have e2 : c i * -α = -(α * c i) := by ring
      rw [e2]
      linarith
    exact hle
  · have hdp : b ⬝ᵥ ((-α)⁻¹ • y) = (-α)⁻¹ * (b ⬝ᵥ y) := by
      rw [dotProduct_smul, smul_eq_mul]
    rw [hdp, inv_mul_eq_div, div_lt_iff₀ hpos]
    have e1 : t * -α = -(t * α) := by ring
    rw [e1]
    linarith [hstrict]

/-- **Strong linear programming duality.** Let $A$ be a real $m \times n$ matrix, and let
$b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$; inequalities between vectors are componentwise.
Suppose some $x \in \mathbb{R}^n$ satisfies $x \ge 0$ and $Ax \le b$, and that $c \cdot x$ is
bounded above over all such $x$. Then there exist $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$
with $x \ge 0$, $Ax \le b$, $y \ge 0$, $A^{\mathsf{T}} y \ge c$ and $c \cdot x = b \cdot y$.

By weak duality, such $x$ and $y$ are optimal solutions of the primal problem of maximizing
$c \cdot x$ subject to $x \ge 0$, $Ax \le b$ and of the dual problem of minimizing $b \cdot y$
subject to $y \ge 0$, $A^{\mathsf{T}} y \ge c$.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem. -/
theorem strong_linear_programming_duality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ ∀ j, (A.mulVec x) j ≤ b j)
    (hbdd : ∃ M : ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (∀ j, (A.mulVec x) j ≤ b j) → c ⬝ᵥ x ≤ M) :
    ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ,
      (∀ i, 0 ≤ x i) ∧ (∀ j, (A.mulVec x) j ≤ b j) ∧
      (∀ j, 0 ≤ y j) ∧ (∀ i, c i ≤ (A.transpose.mulVec y) i) ∧
      c ⬝ᵥ x = b ⬝ᵥ y := by
  obtain ⟨x₀, hx₀, hAx₀⟩ := hfeas
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨xopt, hxopt, hAxopt, hmax⟩ := lp_max_attains A b c x₀ hx₀ hAx₀ M hM
  have hweak : ∀ y : Fin m → ℝ, (∀ j, 0 ≤ y j) →
      (∀ i, c i ≤ (Aᵀ.mulVec y) i) → c ⬝ᵥ xopt ≤ b ⬝ᵥ y := by
    intro y hy hAty
    calc c ⬝ᵥ xopt ≤ (Aᵀ.mulVec y) ⬝ᵥ xopt :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hAty i) (hxopt i)
      _ = xopt ⬝ᵥ (Aᵀ.mulVec y) := dotProduct_comm _ _
      _ = y ⬝ᵥ (A.mulVec xopt) := Matrix.dotProduct_transpose_mulVec A xopt y
      _ ≤ y ⬝ᵥ b :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hAxopt j) (hy j)
      _ = b ⬝ᵥ y := dotProduct_comm _ _
  have hseq : ∀ k : ℕ, ∃ y : Fin m → ℝ, (∀ j, 0 ≤ y j) ∧
      (∀ i, c i ≤ (Aᵀ.mulVec y) i) ∧
      b ⬝ᵥ y < c ⬝ᵥ xopt + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have ht : c ⬝ᵥ xopt < c ⬝ᵥ xopt + 1 / ((k : ℝ) + 1) := by linarith
    exact dual_value_approach A b c xopt hxopt hAxopt hmax _ ht
  obtain ⟨y₀, hy₀, hAty₀, _⟩ := hseq 0
  obtain ⟨yopt, hyopt, hAyopt, hmin⟩ :=
    lp_max_attains (-Aᵀ) (-c) (-b) y₀ hy₀ (dualNegFeas A c y₀ hAty₀)
      (-(c ⬝ᵥ xopt)) (fun y hy hAy => by
        have hle := hweak y hy (dualPosFeas A c y hAy)
        rw [neg_dotProduct]
        exact neg_le_neg_iff.mpr hle)
  have hAtyopt : ∀ i, c i ≤ (Aᵀ.mulVec yopt) i := dualPosFeas A c yopt hAyopt
  have hle1 : c ⬝ᵥ xopt ≤ b ⬝ᵥ yopt := hweak yopt hyopt hAtyopt
  have hle2 : b ⬝ᵥ yopt ≤ c ⬝ᵥ xopt := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨y, hy, hAy, hby⟩ := hseq k
    have hminy := hmin y hy (dualNegFeas A c y hAy)
    rw [neg_dotProduct, neg_dotProduct] at hminy
    have hle : b ⬝ᵥ yopt ≤ b ⬝ᵥ y := neg_le_neg_iff.mp hminy
    have hlt : b ⬝ᵥ y < c ⬝ᵥ xopt + ε :=
      lt_of_lt_of_le hby (by linarith)
    exact lt_of_le_of_lt hle hlt
  exact ⟨xopt, yopt, hxopt, hAxopt, hyopt, hAtyopt, le_antisymm hle1 hle2⟩

end AttainDuality

end MathlibExt.Analysis.Convex.LPDuality
