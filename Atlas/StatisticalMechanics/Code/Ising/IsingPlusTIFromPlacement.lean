/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Ising.IsingTranslatedBoxClose
import Code.Ising.FVConsistencyProve
import Code.Ising.IsingFKGLayer
import Code.Ising.GibbsExtreme
import Code.Lattice.ContourCountInjection
import Code.FK.InducedBC
import Code.Percolation.BurtonKeane

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace
open StatMech.FK
open StatMech.Percolation

variable {d : ℕ}









def gvUnit (d : ℕ) (i : Fin d) : Site d := fun j => if j = i then 1 else 0


noncomputable def gvBall (x : Site d) : Finset (Site d) :=
  insert x ((Finset.univ : Finset (Fin d)).biUnion
    (fun i => {x + gvUnit d i, x - gvUnit d i}))


noncomputable def gvCand (S : Finset (Site d)) : Finset (Site d) := S.biUnion gvBall


noncomputable def gvBondTouch (S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (((gvCand S) ×ˢ (gvCand S)).filter
    (fun p => (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ S ∨ p.2 ∈ S))).image (fun p => s(p.1, p.2))


theorem gv_self_mem_ball (x : Site d) : x ∈ gvBall x := Finset.mem_insert_self _ _



theorem gv_nbr_mem_ball {x y : Site d} (hadj : (hypercubicLattice d).Adj x y) :
    y ∈ gvBall x := by
  rw [hypercubicLattice_adj] at hadj
  
  obtain ⟨i, hi1, hi0⟩ : ∃ i, (x i - y i).natAbs = 1 ∧ ∀ j, j ≠ i → x j = y j := by
    rcases Finset.exists_ne_zero_of_sum_ne_zero (by rw [hadj]; norm_num :
        (∑ i, (x i - y i).natAbs) ≠ 0) with ⟨i, _, hine⟩
    have hi1 : (x i - y i).natAbs = 1 := by
      by_contra hc
      have hge : 2 ≤ (x i - y i).natAbs := by omega
      have : 2 ≤ ∑ j, (x j - y j).natAbs :=
        le_trans hge (Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      omega
    refine ⟨i, hi1, fun j hj => ?_⟩
    by_contra hjne
    have hjpos : 1 ≤ (x j - y j).natAbs := by
      have : x j - y j ≠ 0 := sub_ne_zero.mpr hjne
      omega
    have hsum2 : (x i - y i).natAbs + (x j - y j).natAbs ≤ ∑ k, (x k - y k).natAbs := by
      have := Finset.sum_le_sum_of_subset (s := ({i, j} : Finset (Fin d)))
        (t := (Finset.univ : Finset (Fin d))) (f := fun k => (x k - y k).natAbs)
        (Finset.subset_univ _)
      rwa [Finset.sum_pair (Ne.symm hj)] at this
    omega
  
  rw [gvBall]
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
  have hxy : x i - y i = 1 ∨ x i - y i = -1 := by
    rcases Int.natAbs_eq_iff.mp hi1 with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  rcases hxy with h | h
  · 
    refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
    funext j
    by_cases hji : j = i
    · subst hji; simp only [Pi.sub_apply, gvUnit, if_true]; omega
    · simp only [Pi.sub_apply, gvUnit, if_neg hji, sub_zero]; exact (hi0 j hji).symm
  · 
    have hyeq : y = x + gvUnit d i := by
      funext j
      by_cases hji : j = i
      · subst hji; simp only [Pi.add_apply, gvUnit, if_true]; omega
      · simp only [Pi.add_apply, gvUnit, if_neg hji, add_zero]; exact (hi0 j hji).symm
    rw [hyeq]; exact Finset.mem_insert_self _ _


theorem gv_mk_mem_bondTouch {S : Finset (Site d)} {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (htouch : x ∈ S ∨ y ∈ S) :
    s(x, y) ∈ gvBondTouch S := by
  rw [gvBondTouch, Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj, htouch⟩
  · rw [gvCand, Finset.mem_biUnion]
    rcases htouch with h | h
    · exact ⟨x, h, gv_self_mem_ball x⟩
    · exact ⟨y, h, gv_nbr_mem_ball hadj.symm⟩
  · rw [gvCand, Finset.mem_biUnion]
    rcases htouch with h | h
    · exact ⟨x, h, gv_nbr_mem_ball hadj⟩
    · exact ⟨y, h, gv_self_mem_ball y⟩


theorem gv_bondTouch_subset_edgeSet (S : Finset (Site d)) :
    ∀ e ∈ gvBondTouch S, e ∈ (hypercubicLattice d).edgeSet := by
  intro e he
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter] at hp
  rw [SimpleGraph.mem_edgeSet]
  exact hp.2.1



theorem gv_bondTouch_subset {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    gvBondTouch Sin ⊆ gvBondTouch Sout := by
  intro e he
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, htouch⟩ := hp
  refine gv_mk_mem_bondTouch hadj ?_
  rcases htouch with h | h
  · exact Or.inl (hsub h)
  · exact Or.inr (hsub h)


noncomputable def gvGlue (η : ConfigSpace (Site d)) (S : Finset (Site d))
    (τ : {x // x ∈ S} → Bool) : ConfigSpace (Site d) :=
  fun x => if h : x ∈ S then τ ⟨x, h⟩ else η x

@[simp] lemma gvGlue_mem (η : ConfigSpace (Site d)) (S : Finset (Site d))
    (τ : {x // x ∈ S} → Bool) {x : Site d} (hx : x ∈ S) :
    gvGlue η S τ x = τ ⟨x, hx⟩ := by simp [gvGlue, hx]

@[simp] lemma gvGlue_not_mem (η : ConfigSpace (Site d)) (S : Finset (Site d))
    (τ : {x // x ∈ S} → Bool) {x : Site d} (hx : x ∉ S) :
    gvGlue η S τ x = η x := by simp [gvGlue, hx]


noncomputable def gvEnergy (η : ConfigSpace (Site d)) (S : Finset (Site d)) (h : ℝ)
    (τ : {x // x ∈ S} → Bool) : ℝ :=
  - (∑ e ∈ gvBondTouch S, bond (gvGlue η S τ) e) - h * ∑ x ∈ S, spin (gvGlue η S τ) x


noncomputable def gvWeight (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : ℝ :=
  Real.exp (-β * gvEnergy η S h τ)

lemma gvWeight_pos (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : 0 < gvWeight η S β h τ := Real.exp_pos _


noncomputable def gvZ (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ S} → Bool, gvWeight η S β h τ

lemma gvZ_pos (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    0 < gvZ η S β h := by
  unfold gvZ
  exact Finset.sum_pos (fun τ _ => gvWeight_pos η S β h τ) Finset.univ_nonempty

lemma gvZ_ne_zero (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    gvZ η S β h ≠ 0 := (gvZ_pos η S β h).ne'


noncomputable def gvProb (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : ℝ :=
  gvWeight η S β h τ / gvZ η S β h

lemma gvProb_nonneg (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : 0 ≤ gvProb η S β h τ :=
  div_nonneg (gvWeight_pos η S β h τ).le (gvZ_pos η S β h).le

lemma gvProb_sum_eq_one (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    ∑ τ : {x // x ∈ S} → Bool, gvProb η S β h τ = 1 := by
  unfold gvProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (gvZ_ne_zero η S β h)]; rfl


noncomputable def gvMeasure (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    Measure (ConfigSpace (Site d)) :=
  ∑ τ : {x // x ∈ S} → Bool,
    ENNReal.ofReal (gvProb η S β h τ) • Measure.dirac (gvGlue η S τ)

lemma gvMeasure_univ (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    (gvMeasure η S β h) Set.univ = 1 := by
  unfold gvMeasure
  rw [Measure.finsetSum_apply _ _ _]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun τ _ => gvProb_nonneg η S β h τ),
    gvProb_sum_eq_one η S β h, ENNReal.ofReal_one]

instance gvMeasure_isProbabilityMeasure (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    IsProbabilityMeasure (gvMeasure η S β h) := ⟨gvMeasure_univ η S β h⟩


noncomputable def gvPlusMeasure (S : Finset (Site d)) (β h : ℝ) : Measure (ConfigSpace (Site d)) :=
  gvMeasure (plusField d) S β h

instance gvPlusMeasure_isProbabilityMeasure (S : Finset (Site d)) (β h : ℝ) :
    IsProbabilityMeasure (gvPlusMeasure S β h) := gvMeasure_isProbabilityMeasure _ S β h


theorem gvMeasure_real_eq (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) :
    (gvMeasure η S β h).real A
      = ∑ τ : {x // x ∈ S} → Bool,
          gvProb η S β h τ * (Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η S τ)) := by
  unfold Measure.real
  rw [show (gvMeasure η S β h) A
        = ∑ τ : {x // x ∈ S} → Bool,
            (ENNReal.ofReal (gvProb η S β h τ) • Measure.dirac (gvGlue η S τ)) A from
      Measure.finsetSum_apply Finset.univ _ A]
  rw [ENNReal.toReal_sum (fun τ _ => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (gvProb_nonneg η S β h τ)]
  congr 1
  by_cases hmem : gvGlue η S τ ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; simp
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; simp









theorem gvGlue_mono_interior (η : ConfigSpace (Site d)) (S : Finset (Site d))
    (τ τ' : {x // x ∈ S} → Bool) (h : τ ≤ τ') : gvGlue η S τ ≤ gvGlue η S τ' := by
  intro x
  by_cases hx : x ∈ S
  · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]; exact h ⟨x, hx⟩
  · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]


theorem gvGlue_mono_boundary (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (τ : {x // x ∈ S} → Bool) : gvGlue η S τ ≤ gvGlue η' S τ := by
  intro x
  by_cases hx : x ∈ S
  · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]
  · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]; exact hle x


theorem gv_spin_glue_inf (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η S (a ⊓ b)) x = min (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
  by_cases hx : x ∈ S
  · simp only [spin, gvGlue_mem _ _ _ hx, Pi.inf_apply]; exact spinB_inf _ _
  · simp only [spin, gvGlue_not_mem _ _ _ hx]
    conv_lhs => rw [show η x = η x ⊓ η' x from (inf_eq_left.mpr (hle x)).symm]
    exact spinB_inf _ _


theorem gv_spin_glue_sup (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η' S (a ⊔ b)) x = max (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
  by_cases hx : x ∈ S
  · simp only [spin, gvGlue_mem _ _ _ hx, Pi.sup_apply]; exact spinB_sup _ _
  · simp only [spin, gvGlue_not_mem _ _ _ hx]
    conv_lhs => rw [show η' x = η x ⊔ η' x from (sup_eq_right.mpr (hle x)).symm]
    exact spinB_sup _ _


theorem gv_bond_glue_supermod (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (e : Sym2 (Site d)) :
    bond (gvGlue η S a) e + bond (gvGlue η' S b) e
      ≤ bond (gvGlue η S (a ⊓ b)) e + bond (gvGlue η' S (a ⊔ b)) e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [bond_mk]
    rw [gv_spin_glue_inf S η η' hle a b x, gv_spin_glue_inf S η η' hle a b y,
        gv_spin_glue_sup S η η' hle a b x, gv_spin_glue_sup S η η' hle a b y]
    exact prod_supermod _ _ _ _


theorem gv_spin_glue_add (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η S a) x + spin (gvGlue η' S b) x
      = spin (gvGlue η S (a ⊓ b)) x + spin (gvGlue η' S (a ⊔ b)) x := by
  rw [gv_spin_glue_inf S η η' hle a b x, gv_spin_glue_sup S η η' hle a b x]
  rcases le_total (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]; ring


theorem gv_fvEnergy_supermod (S : Finset (Site d)) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvEnergy η S h (a ⊓ b) + gvEnergy η' S h (a ⊔ b)
      ≤ gvEnergy η S h a + gvEnergy η' S h b := by
  unfold gvEnergy
  have hbond : ∑ e ∈ gvBondTouch S, bond (gvGlue η S a) e
        + ∑ e ∈ gvBondTouch S, bond (gvGlue η' S b) e
      ≤ ∑ e ∈ gvBondTouch S, bond (gvGlue η S (a ⊓ b)) e
        + ∑ e ∈ gvBondTouch S, bond (gvGlue η' S (a ⊔ b)) e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => gv_bond_glue_supermod S η η' hle a b e)
  have hfield : ∑ x ∈ S, spin (gvGlue η S a) x + ∑ x ∈ S, spin (gvGlue η' S b) x
      = ∑ x ∈ S, spin (gvGlue η S (a ⊓ b)) x + ∑ x ∈ S, spin (gvGlue η' S (a ⊔ b)) x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => gv_spin_glue_add S η η' hle a b x)
  have hfieldh : h * (∑ x ∈ S, spin (gvGlue η S a) x) + h * (∑ x ∈ S, spin (gvGlue η' S b) x)
      = h * (∑ x ∈ S, spin (gvGlue η S (a ⊓ b)) x)
        + h * (∑ x ∈ S, spin (gvGlue η' S (a ⊔ b)) x) := by rw [← mul_add, ← mul_add, hfield]
  linarith [hbond, hfieldh]


theorem gv_fvWeight_cross (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvWeight η S β h a * gvWeight η' S β h b
      ≤ gvWeight η S β h (a ⊓ b) * gvWeight η' S β h (a ⊔ b) := by
  unfold gvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := gv_fvEnergy_supermod S h hh η η' hle a b
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]


theorem gv_fvProb_cross (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvProb η S β h a * gvProb η' S β h b
      ≤ gvProb η S β h (a ⊓ b) * gvProb η' S β h (a ⊔ b) := by
  have hZ1 : 0 < gvZ η S β h := gvZ_pos _ _ _ _
  have hZ2 : 0 < gvZ η' S β h := gvZ_pos _ _ _ _
  simp only [gvProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)).mpr
    (gv_fvWeight_cross S hβ h hh η η' hle a b)


theorem gv_fvProb_dominates (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    {A : Set (ConfigSpace {x // x ∈ S})} (hA : IsIncreasing A) :
    ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η S β h τ
      ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ :=
  holley_dominates (fun τ => gvProb_nonneg η S β h τ) (fun τ => gvProb_nonneg η' S β h τ)
    (by rw [gvProb_sum_eq_one, gvProb_sum_eq_one])
    (fun a b => gv_fvProb_cross S hβ h hh η η' hle a b) hA



theorem gvMeasure_dominated (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    (gvMeasure η S β h).real A ≤ (gvMeasure η' S β h).real A := by
  rw [gvMeasure_real_eq η S β h hA, gvMeasure_real_eq η' S β h hA]
  set A₁ : Set (ConfigSpace {x // x ∈ S}) := (fun τ => gvGlue η S τ) ⁻¹' A with hA1
  set A₂ : Set (ConfigSpace {x // x ∈ S}) := (fun τ => gvGlue η' S τ) ⁻¹' A with hA2
  have hreη : ∀ τ, Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η S τ)
      = Set.indicator A₁ (fun _ => (1 : ℝ)) τ := by
    intro τ; by_cases hmem : gvGlue η S τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₁ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₁ from hmem)]
  have hreη' : ∀ τ, Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η' S τ)
      = Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
    intro τ; by_cases hmem : gvGlue η' S τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₂ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₂ from hmem)]
  simp_rw [hreη, hreη']
  have hA1inc : IsIncreasing A₁ := fun τ τ' hτ hmem => hAinc (gvGlue_mono_interior η S τ τ' hτ) hmem
  have hsub : A₁ ⊆ A₂ := fun τ hmem => hAinc (gvGlue_mono_boundary S η η' hle τ) hmem
  calc ∑ τ, gvProb η S β h τ * Set.indicator A₁ (fun _ => (1 : ℝ)) τ
      = ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * gvProb η S β h τ := by
        apply Finset.sum_congr rfl; intro τ _; ring
    _ ≤ ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ :=
        gv_fvProb_dominates S hβ h hh η η' hle hA1inc
    _ ≤ ∑ τ, Set.indicator A₂ (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ := by
        apply Finset.sum_le_sum; intro τ _
        apply mul_le_mul_of_nonneg_right _ (gvProb_nonneg η' S β h τ)
        by_cases h1 : τ ∈ A₁
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hsub h1)]
        · rw [Set.indicator_of_notMem h1]
          by_cases h2 : τ ∈ A₂
          · rw [Set.indicator_of_mem h2]; norm_num
          · rw [Set.indicator_of_notMem h2]
    _ = ∑ τ, gvProb η' S β h τ * Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
        apply Finset.sum_congr rfl; intro τ _; ring


theorem gv_le_plusField (η : ConfigSpace (Site d)) : η ≤ plusField d := by
  intro x; simp [plusField]


theorem gvMeasure_le_plusField (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (η : ConfigSpace (Site d)) {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A)
    (hAinc : IsIncreasing A) :
    (gvMeasure η S β h).real A ≤ (gvMeasure (plusField d) S β h).real A :=
  gvMeasure_dominated S hβ hh η (plusField d) (gv_le_plusField η) hA hAinc









noncomputable def gvOvr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) : {x // x ∈ Sout} → Bool :=
  fun x => if hn : (x : Site d) ∈ Sin then τ ⟨x, hn⟩ else σ x


noncomputable def gvRes {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) : {x // x ∈ Sin} → Bool :=
  fun x => σ ⟨x, hsub x.2⟩

theorem gvRes_gvOvr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvRes hsub (gvOvr hsub σ τ) = τ := by
  funext x; simp only [gvRes, gvOvr]; rw [dif_pos x.2]

theorem gvOvr_gvOvr_gvRes {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvOvr hsub (gvOvr hsub σ τ) (gvRes hsub σ) = σ := by
  funext x; simp only [gvOvr, gvRes]
  by_cases hn : (x : Site d) ∈ Sin
  · rw [dif_pos hn]
  · rw [dif_neg hn, dif_neg hn]


theorem gvGlue_gvGlue_eq_gvGlue_ovr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvGlue (gvGlue η Sout σ) Sin τ = gvGlue η Sout (gvOvr hsub σ τ) := by
  funext x
  by_cases hn : x ∈ Sin
  · have hm : x ∈ Sout := hsub hn
    rw [gvGlue_mem _ _ _ hn, gvGlue_mem _ _ _ hm]; simp only [gvOvr, dif_pos hn]
  · by_cases hm : x ∈ Sout
    · rw [gvGlue_not_mem _ _ _ hn, gvGlue_mem _ _ _ hm, gvGlue_mem _ _ _ hm]
      simp only [gvOvr, dif_neg hn]
    · rw [gvGlue_not_mem _ _ _ hn, gvGlue_not_mem _ _ _ hm, gvGlue_not_mem _ _ _ hm]


theorem gvGlue_ovr_eq_off {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool)
    {x : Site d} (hx : x ∉ Sin) :
    gvGlue η Sout (gvOvr hsub σ τ) x = gvGlue η Sout σ x := by
  by_cases hm : x ∈ Sout
  · rw [gvGlue_mem _ _ _ hm, gvGlue_mem _ _ _ hm]; simp only [gvOvr, dif_neg hx]
  · rw [gvGlue_not_mem _ _ _ hm, gvGlue_not_mem _ _ _ hm]


theorem gv_bond_glue_ovr_eq_of_notMem {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool)
    {e : Sym2 (Site d)} (heE : e ∈ (hypercubicLattice d).edgeSet) (heB : e ∉ gvBondTouch Sin) :
    bond (gvGlue η Sout (gvOvr hsub σ τ)) e = bond (gvGlue η Sout σ) e := by
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at heE
    rw [bond_mk, bond_mk]
    have ha : a ∉ Sin := fun h => heB (gv_mk_mem_bondTouch heE (Or.inl h))
    have hb : b ∉ Sin := fun h => heB (gv_mk_mem_bondTouch heE (Or.inr h))
    rw [show spin (gvGlue η Sout (gvOvr hsub σ τ)) a = spin (gvGlue η Sout σ) a from by
          unfold spin; rw [gvGlue_ovr_eq_off hsub η σ τ ha],
        show spin (gvGlue η Sout (gvOvr hsub σ τ)) b = spin (gvGlue η Sout σ) b from by
          unfold spin; rw [gvGlue_ovr_eq_off hsub η σ τ hb]]


theorem gv_bond_sum_diff_eq {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout (gvOvr hsub σ τ)) e)
        - (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout σ) e)
      = (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout (gvOvr hsub σ τ)) e)
        - (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout σ) e) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (gv_bondTouch_subset hsub) (fun e heM heN => ?_)).symm
  have heE : e ∈ (hypercubicLattice d).edgeSet := gv_bondTouch_subset_edgeSet Sout e heM
  rw [gv_bond_glue_ovr_eq_of_notMem hsub η σ τ heE heN, sub_self]


theorem gv_spin_sum_diff_eq {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    (∑ x ∈ Sout, spin (gvGlue η Sout (gvOvr hsub σ τ)) x)
        - (∑ x ∈ Sout, spin (gvGlue η Sout σ) x)
      = (∑ x ∈ Sin, spin (gvGlue η Sout (gvOvr hsub σ τ)) x)
        - (∑ x ∈ Sin, spin (gvGlue η Sout σ) x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset hsub (fun x hxM hxN => ?_)).symm
  unfold spin
  rw [gvGlue_ovr_eq_off hsub η σ τ hxN, sub_self]


theorem gv_energy_decomp {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (h : ℝ) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvEnergy η Sout h σ + gvEnergy (gvGlue η Sout σ) Sin h τ
      = gvEnergy η Sout h (gvOvr hsub σ τ)
        + gvEnergy (gvGlue η Sout (gvOvr hsub σ τ)) Sin h (gvRes hsub σ) := by
  unfold gvEnergy
  rw [gvGlue_gvGlue_eq_gvGlue_ovr hsub η σ τ,
      gvGlue_gvGlue_eq_gvGlue_ovr hsub η (gvOvr hsub σ τ) (gvRes hsub σ),
      gvOvr_gvOvr_gvRes hsub σ τ]
  have hb := gv_bond_sum_diff_eq hsub η σ τ
  have hs := gv_spin_sum_diff_eq hsub η σ τ
  linear_combination hb + h * hs


theorem gv_weight_spec_symm {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (β h : ℝ) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvWeight η Sout β h σ * gvWeight (gvGlue η Sout σ) Sin β h τ
      = gvWeight η Sout β h (gvOvr hsub σ τ)
        * gvWeight (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ) := by
  unfold gvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hE := gv_energy_decomp hsub η h σ τ
  ring_nf
  linear_combination (-β) * hE


theorem gv_fvWeight_eq_of_agree_off {Sin : Finset (Site d)} (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x)
    (τ : {x // x ∈ Sin} → Bool) :
    gvWeight ζ₁ Sin β h τ = gvWeight ζ₂ Sin β h τ := by
  unfold gvWeight gvEnergy
  have hglue : gvGlue ζ₁ Sin τ = gvGlue ζ₂ Sin τ := by
    funext x
    by_cases hx : x ∈ Sin
    · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]
    · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]; exact hagree x hx
  rw [hglue]

theorem gv_fvZ_eq_of_agree_off {Sin : Finset (Site d)} (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x) :
    gvZ ζ₁ Sin β h = gvZ ζ₂ Sin β h := by
  unfold gvZ
  exact Finset.sum_congr rfl (fun τ _ => gv_fvWeight_eq_of_agree_off β h hagree τ)


noncomputable def gvSwapPair {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool))
      → (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool)) :=
  fun p => (gvOvr hsub p.1 p.2, gvRes hsub p.1)

theorem gvSwapPair_involutive {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    Function.Involutive (gvSwapPair (d := d) hsub) := by
  rintro ⟨σ, τ⟩
  simp only [gvSwapPair]
  rw [gvOvr_gvOvr_gvRes hsub σ τ, gvRes_gvOvr hsub σ τ]

theorem gvSwapPair_bijective {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    Function.Bijective (gvSwapPair (d := d) hsub) := (gvSwapPair_involutive hsub).bijective


theorem gv_consistency_double_sum {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (β h : ℝ) (g : ConfigSpace (Site d) → ℝ) :
    (∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue (gvGlue η Sout σ) Sin τ))
      = ∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ * g (gvGlue η Sout σ) := by
  set F : (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool)) → ℝ :=
    fun p => gvProb η Sout β h p.1
        * (gvProb (gvGlue η Sout p.1) Sin β h p.2 * g (gvGlue (gvGlue η Sout p.1) Sin p.2))
    with hF
  have hLHS : (∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue (gvGlue η Sout σ) Sin τ))
      = ∑ p, F p := by
    rw [Fintype.sum_prod_type (f := F)]
    refine Finset.sum_congr rfl (fun σ _ => ?_); rw [Finset.mul_sum]
  rw [hLHS, ← Function.Bijective.sum_comp (gvSwapPair_bijective hsub) F]
  have hpoint : ∀ p : (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool)),
      F (gvSwapPair hsub p)
        = gvProb η Sout β h p.1
            * (gvProb (gvGlue η Sout p.1) Sin β h p.2 * g (gvGlue η Sout p.1)) := by
    rintro ⟨σ, τ⟩
    simp only [hF, gvSwapPair]
    have harg : gvGlue (gvGlue η Sout (gvOvr hsub σ τ)) Sin (gvRes hsub σ) = gvGlue η Sout σ := by
      rw [gvGlue_gvGlue_eq_gvGlue_ovr hsub η (gvOvr hsub σ τ) (gvRes hsub σ),
        gvOvr_gvOvr_gvRes hsub σ τ]
    rw [harg]
    have hprob : gvProb η Sout β h (gvOvr hsub σ τ)
          * gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ)
        = gvProb η Sout β h σ * gvProb (gvGlue η Sout σ) Sin β h τ := by
      unfold gvProb
      have hagree : ∀ x ∉ Sin, gvGlue η Sout (gvOvr hsub σ τ) x = gvGlue η Sout σ x :=
        fun x hx => gvGlue_ovr_eq_off hsub η σ τ hx
      rw [gv_fvZ_eq_of_agree_off β h hagree]
      have hw := gv_weight_spec_symm hsub η β h σ τ
      rw [div_mul_div_comm, div_mul_div_comm, hw]
    calc gvProb η Sout β h (gvOvr hsub σ τ)
            * (gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ) * g (gvGlue η Sout σ))
        = (gvProb η Sout β h (gvOvr hsub σ τ)
              * gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ))
            * g (gvGlue η Sout σ) := by ring
      _ = (gvProb η Sout β h σ * gvProb (gvGlue η Sout σ) Sin β h τ) * g (gvGlue η Sout σ) := by
            rw [hprob]
      _ = gvProb η Sout β h σ * (gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue η Sout σ)) := by ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hcollapse : (∑ τ : {x // x ∈ Sin} → Bool,
        gvProb η Sout β h σ * (gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue η Sout σ)))
      = gvProb η Sout β h σ * g (gvGlue η Sout σ)
          * (∑ τ : {x // x ∈ Sin} → Bool, gvProb (gvGlue η Sout σ) Sin β h τ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun τ _ => ?_); ring
  rw [hcollapse, gvProb_sum_eq_one (gvGlue η Sout σ) Sin β h, mul_one]











theorem iptp_gv_crossbox_dom {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    (gvPlusMeasure Sout β h).real A ≤ (gvPlusMeasure Sin β h).real A := by
  set g0 : ConfigSpace (Site d) → ℝ := A.indicator (fun _ => (1:ℝ)) with hg0
  have hcds := gv_consistency_double_sum hsub (plusField d) β h g0
  have hpm : (gvPlusMeasure Sout β h).real A
      = ∑ σ : {x // x ∈ Sout} → Bool, gvProb (plusField d) Sout β h σ * g0 (gvGlue (plusField d) Sout σ) := by
    rw [gvPlusMeasure, gvMeasure_real_eq (plusField d) Sout β h hAmeas]
  rw [hpm, ← hcds]
  have hterm : ∀ σ : {x // x ∈ Sout} → Bool,
      gvProb (plusField d) Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
              * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ)
      ≤ gvProb (plusField d) Sout β h σ * (gvPlusMeasure Sin β h).real A := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (gvProb_nonneg _ _ _ _ _)
    have hinner : (∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
              * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ))
        = (gvMeasure (gvGlue (plusField d) Sout σ) Sin β h).real A :=
      (gvMeasure_real_eq (gvGlue (plusField d) Sout σ) Sin β h hAmeas).symm
    rw [hinner]
    exact gvMeasure_le_plusField Sin hβ hh (gvGlue (plusField d) Sout σ) hAmeas hAinc
  calc ∑ σ : {x // x ∈ Sout} → Bool,
          gvProb (plusField d) Sout β h σ
            * ∑ τ : {x // x ∈ Sin} → Bool,
                gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
                  * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ)
      ≤ ∑ σ : {x // x ∈ Sout} → Bool,
          gvProb (plusField d) Sout β h σ * (gvPlusMeasure Sin β h).real A :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (gvPlusMeasure Sin β h).real A := by
        rw [← Finset.sum_mul, gvProb_sum_eq_one (plusField d) Sout β h, one_mul]








noncomputable def iptp_boxEquiv (d n : ℕ) :
    {x : Site d // x ∈ box d n} ≃ {x : Site d // x ∈ boxFinset d n} :=
  Equiv.subtypeEquivProp (by ext x; rw [mem_boxFinset])


theorem iptp_gvBondTouch_boxFinset (n : ℕ) :
    gvBondTouch (boxFinset d n) = bondFinsetTouch d n := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [gvBondTouch, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    refine StatMech.Lattice.mk_mem_bondFinsetTouch hadj ?_
    rcases htouch with h | h
    · exact Or.inl (mem_boxFinset.mp h)
    · exact Or.inr (mem_boxFinset.mp h)
  · intro e he
    rw [bondFinsetTouch, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [bondPairsTouch, Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    refine gv_mk_mem_bondTouch hadj ?_
    rcases htouch with h | h
    · exact Or.inl (mem_boxFinset.mpr h)
    · exact Or.inr (mem_boxFinset.mpr h)

theorem iptp_gvGlue_box (n : ℕ) (η : ConfigSpace (Site d)) (τ : {x // x ∈ box d n} → Bool) :
    gvGlue η (boxFinset d n) (fun y => τ ((iptp_boxEquiv d n).symm y)) = glue η τ := by
  funext x
  by_cases hx : x ∈ box d n
  · rw [gvGlue_mem _ _ _ (mem_boxFinset.mpr hx), glue_mem _ _ hx]; congr 1
  · rw [gvGlue_not_mem _ _ _ (fun h => hx (mem_boxFinset.mp h)), glue_not_mem _ _ hx]

theorem iptp_gvEnergy_box (n : ℕ) (η : ConfigSpace (Site d)) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvEnergy η (boxFinset d n) h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvEnergy η n (bondFinsetTouch d n) h τ := by
  unfold gvEnergy fvEnergy
  rw [iptp_gvBondTouch_boxFinset, iptp_gvGlue_box]

theorem iptp_gvWeight_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvWeight η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvWeight η n (bondFinsetTouch d n) β h τ := by
  unfold gvWeight fvWeight; rw [iptp_gvEnergy_box]

theorem iptp_gvZ_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ) :
    gvZ η (boxFinset d n) β h = fvZ η n (bondFinsetTouch d n) β h := by
  unfold gvZ fvZ
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool))
    (fun τ => gvWeight η (boxFinset d n) β h τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← iptp_gvWeight_box n η β h τ]; rfl

theorem iptp_gvProb_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvProb η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvProb η n (bondFinsetTouch d n) β h τ := by
  unfold gvProb fvProb; rw [iptp_gvWeight_box, iptp_gvZ_box]


theorem iptp_gvMeasure_eq_fvMeasure (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ) :
    gvMeasure η (boxFinset d n) β h = fvMeasure η n (bondFinsetTouch d n) β h := by
  unfold gvMeasure fvMeasure
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool))
    (fun τ => ENNReal.ofReal (gvProb η (boxFinset d n) β h τ)
      • Measure.dirac (gvGlue η (boxFinset d n) τ))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show gvProb η (boxFinset d n) β h ((Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool)) τ)
        = fvProb η n (bondFinsetTouch d n) β h τ from iptp_gvProb_box n η β h τ,
    show gvGlue η (boxFinset d n) ((Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool)) τ)
        = glue η τ from iptp_gvGlue_box n η τ]


theorem iptp_gvPlusMeasure_eq_plusMeasure (n : ℕ) (β h : ℝ) :
    gvPlusMeasure (boxFinset d n) β h = (plusMeasure d n β h : Measure (ConfigSpace (Site d))) := by
  rw [gvPlusMeasure, iptp_gvMeasure_eq_fvMeasure, plusMeasure_coe]










noncomputable def iptp_transInteriorEquiv (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    {x : Site d // x ∈ S} ≃ {x : Site d // x ∈ S.image (fun x => g • x)} where
  toFun x := ⟨g • (x : Site d), Finset.mem_image_of_mem _ x.2⟩
  invFun y := ⟨g⁻¹ • (y : Site d), by
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp y.2
    rw [← hzeq, inv_smul_smul]; exact hz⟩
  left_inv x := by ext; simp [inv_smul_smul]
  right_inv y := by ext; simp [smul_inv_smul]


theorem iptp_gvBondTouch_image_subset (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    (gvBondTouch S).image (fun e => g • e) ⊆ gvBondTouch (S.image (fun x => g • x)) := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rw [gvBondTouch, Finset.mem_image] at he0
  obtain ⟨p, hp, rfl⟩ := he0
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, htouch⟩ := hp
  rw [smul_sym2_mk]
  refine gv_mk_mem_bondTouch ((hyper_adj_smul g p.1 p.2).mpr hadj) ?_
  rcases htouch with h | h
  · exact Or.inl (Finset.mem_image_of_mem _ h)
  · exact Or.inr (Finset.mem_image_of_mem _ h)


theorem iptp_gvBondTouch_image (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    gvBondTouch (S.image (fun x => g • x)) = (gvBondTouch S).image (fun e => g • e) := by
  apply Finset.Subset.antisymm _ (iptp_gvBondTouch_image_subset g S)
  have hfwd := iptp_gvBondTouch_image_subset g⁻¹ (S.image (fun x => g • x))
  intro e he
  have hmem : (g⁻¹ • e) ∈ gvBondTouch ((S.image (fun x => g • x)).image (fun x => g⁻¹ • x)) :=
    hfwd (Finset.mem_image_of_mem _ he)
  rw [Finset.image_image] at hmem
  have hcomp : ((fun x : Site d => g⁻¹ • x) ∘ fun x : Site d => g • x) = id := by
    funext x; exact inv_smul_smul g x
  rw [hcomp, Finset.image_id] at hmem
  rw [Finset.mem_image]
  exact ⟨g⁻¹ • e, hmem, by rw [smul_inv_smul]⟩


theorem iptp_gvGlue_shift (g : Multiplicative (Site d)) (S : Finset (Site d))
    (τ : {x // x ∈ S} → Bool) :
    ConfigSpace.shift g (gvGlue (plusField d) S τ)
      = gvGlue (plusField d) (S.image (fun x => g • x))
          (fun y => τ ((iptp_transInteriorEquiv g S).symm y)) := by
  funext x
  rw [ConfigSpace.shift_apply]
  by_cases hx : x ∈ S.image (fun x => g • x)
  · have hinv : g⁻¹ • x ∈ S := by
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hx; rw [← hzeq, inv_smul_smul]; exact hz
    rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hinv]; congr 1
  · have hinv : g⁻¹ • x ∉ S := by
      intro hc; exact hx (by rw [← smul_inv_smul g x]; exact Finset.mem_image_of_mem _ hc)
    rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hinv]; simp [plusField]


theorem iptp_spin_shift (g : Multiplicative (Site d)) (c : ConfigSpace (Site d)) (x : Site d) :
    spin (ConfigSpace.shift g c) (g • x) = spin c x := by
  unfold spin; rw [ConfigSpace.shift_apply, inv_smul_smul]


theorem iptp_bond_shift (g : Multiplicative (Site d)) (c : ConfigSpace (Site d)) (e : Sym2 (Site d)) :
    bond (ConfigSpace.shift g c) (g • e) = bond c e := by
  induction e with
  | h x y => rw [smul_sym2_mk, bond_mk, bond_mk, iptp_spin_shift, iptp_spin_shift]


theorem iptp_gvEnergy_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvEnergy (plusField d) (S.image (fun x => g • x)) h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvEnergy (plusField d) S h τ := by
  unfold gvEnergy
  rw [← iptp_gvGlue_shift g S τ]
  congr 1
  · rw [iptp_gvBondTouch_image,
      Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => iptp_bond_shift g (gvGlue (plusField d) S τ) e)
  · congr 1
    rw [Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    exact Finset.sum_congr rfl (fun x _ => iptp_spin_shift g (gvGlue (plusField d) S τ) x)

theorem iptp_gvWeight_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvWeight (plusField d) (S.image (fun x => g • x)) β h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvWeight (plusField d) S β h τ := by
  unfold gvWeight; rw [iptp_gvEnergy_shift]

theorem iptp_gvZ_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    gvZ (plusField d) (S.image (fun x => g • x)) β h = gvZ (plusField d) S β h := by
  unfold gvZ
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun τ => gvWeight (plusField d) (S.image (fun x => g • x)) β h τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← iptp_gvWeight_shift g S β h τ]; rfl

theorem iptp_gvProb_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) :
    gvProb (plusField d) (S.image (fun x => g • x)) β h
        (fun y => τ ((iptp_transInteriorEquiv g S).symm y))
      = gvProb (plusField d) S β h τ := by
  unfold gvProb; rw [iptp_gvWeight_shift, iptp_gvZ_shift]

theorem iptp_map_sum_aux {ι : Type*} [Fintype ι] (f : ConfigSpace (Site d) → ConfigSpace (Site d))
    (hf : Measurable f) (μ : ι → Measure (ConfigSpace (Site d))) :
    Measure.map f (∑ i, μ i) = ∑ i, Measure.map f (μ i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]


theorem iptp_gvMeasure_map_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    Measure.map (ConfigSpace.shift g) (gvMeasure (plusField d) S β h)
      = gvMeasure (plusField d) (S.image (fun x => g • x)) β h := by
  unfold gvMeasure
  rw [iptp_map_sum_aux _ (ConfigSpace.measurable_shift g)]
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun τ => ENNReal.ofReal (gvProb (plusField d) (S.image (fun x => g • x)) β h τ)
      • Measure.dirac (gvGlue (plusField d) (S.image (fun x => g • x)) τ))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.map_smul, Measure.map_dirac (gvGlue (plusField d) S τ)]
  rw [show gvProb (plusField d) (S.image (fun x => g • x)) β h
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool)) τ)
        = gvProb (plusField d) S β h τ from iptp_gvProb_shift g S β h τ,
    show gvGlue (plusField d) (S.image (fun x => g • x))
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool)) τ)
        = ConfigSpace.shift g (gvGlue (plusField d) S τ) from (iptp_gvGlue_shift g S τ).symm]


theorem iptp_gvPlus_real_shift (g : Multiplicative (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (T : Finset (Site d)) :
    (gvPlusMeasure (S.image (fun x => g • x)) β h).real (fmu_multiOpen T)
      = (gvPlusMeasure S β h).real (fmu_multiOpen (T.image (fun e => g⁻¹ • e))) := by
  rw [gvPlusMeasure, gvPlusMeasure, ← iptp_gvMeasure_map_shift g S β h, Measure.real,
    Measure.map_apply (ConfigSpace.measurable_shift g) (fmu_multiOpen_measurable T),
    ← fmu_shift_multiOpen g T]
  rfl








theorem iptp_inv_smul_coord (g : Multiplicative (Site d)) (y : Site d) (i : Fin d) :
    (g⁻¹ • y) i = y i - Multiplicative.toAdd g i := by
  rw [smul_site_apply, show Multiplicative.toAdd g⁻¹ = - Multiplicative.toAdd g from rfl]
  simp; ring


theorem iptp_box_subset_transBox (g : Multiplicative (Site d)) {a m : ℕ}
    (hcm : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
    boxFinset d a ⊆ (boxFinset d m).image (fun x => g • x) := by
  intro y hy
  rw [Finset.mem_image]
  refine ⟨g⁻¹ • y, mem_boxFinset.mpr ?_, by rw [smul_inv_smul]⟩
  intro i
  have hyi : (y i).natAbs ≤ a := mem_boxFinset.mp hy i
  have hvi : (Multiplicative.toAdd g i).natAbs ≤ flc_vrad (Multiplicative.toAdd g) := flc_vrad_le _ i
  rw [iptp_inv_smul_coord g y i]
  calc (y i - Multiplicative.toAdd g i).natAbs
        ≤ (y i).natAbs + (Multiplicative.toAdd g i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ a + flc_vrad (Multiplicative.toAdd g) := Nat.add_le_add hyi hvi
    _ ≤ m := hcm


theorem iptp_transBox_subset_box (g : Multiplicative (Site d)) (m : ℕ) :
    (boxFinset d m).image (fun x => g • x) ⊆ boxFinset d (m + flc_vrad (Multiplicative.toAdd g)) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_boxFinset]
  intro i
  have hzi : (z i).natAbs ≤ m := mem_boxFinset.mp hz i
  have hvi : (Multiplicative.toAdd g i).natAbs ≤ flc_vrad (Multiplicative.toAdd g) := flc_vrad_le _ i
  have hgz : (g • z) i = Multiplicative.toAdd g i + z i := smul_site_apply g z i
  rw [hgz]
  calc (Multiplicative.toAdd g i + z i).natAbs
        ≤ (Multiplicative.toAdd g i).natAbs + (z i).natAbs := Int.natAbs_add_le _ _
    _ ≤ flc_vrad (Multiplicative.toAdd g) + m := Nat.add_le_add hvi hzi
    _ = m + flc_vrad (Multiplicative.toAdd g) := by omega



















theorem iptp_squeeze_lower {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) (m : ℕ) :
    (plusMeasure d (m + flc_vrad (Multiplicative.toAdd g)) β h
        : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
      ≤ (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) := by
  
  rw [← iptp_gvPlusMeasure_eq_plusMeasure m β h, ← iptp_gvPlus_real_shift g (boxFinset d m) β h T,
    ← iptp_gvPlusMeasure_eq_plusMeasure (m + flc_vrad (Multiplicative.toAdd g)) β h]
  
  exact iptp_gv_crossbox_dom (iptp_transBox_subset_box g m) hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T)) (fmu_multiOpen_isIncreasing T)


theorem iptp_squeeze_upper {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) {a m : ℕ}
    (hcond : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))
      ≤ (plusMeasure d a β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T) := by
  rw [← iptp_gvPlusMeasure_eq_plusMeasure m β h, ← iptp_gvPlusMeasure_eq_plusMeasure a β h,
    ← iptp_gvPlus_real_shift g (boxFinset d m) β h T]
  exact iptp_gv_crossbox_dom (iptp_box_subset_transBox g hcond) hβ hh
    (IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T)) (fmu_multiOpen_isIncreasing T)





theorem iptp_plusMultiHomogeneous {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) : iti_PlusMultiHomogeneous β h g := by
  intro T
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  set c := flc_vrad (Multiplicative.toAdd g) with hc
  set IV_T := (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)
    with hivt
  set IV_T' := (plusState d β h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) with hivt'
  
  have hmid : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) atTop (𝓝 IV_T') :=
    itb_plus_multiOpen_full_tendsto hβ hh (T.image (fun x => g⁻¹ • x)) hφ hconv
  
  have hfull : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) :=
    itb_plus_multiOpen_full_tendsto hβ hh T hφ hconv
  
  have hup : Tendsto (fun m => (plusMeasure d (m + c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) := hfull.comp (tendsto_add_atTop_nat c)
  have hlow : Tendsto (fun m => (plusMeasure d (m - c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) := hfull.comp (tendsto_sub_atTop_nat c)
  
  have hle1 : IV_T ≤ IV_T' :=
    le_of_tendsto_of_tendsto hup hmid
      (Filter.Eventually.of_forall (fun m => iptp_squeeze_lower hβ hh g T m))
  
  have hle2 : IV_T' ≤ IV_T := by
    refine le_of_tendsto_of_tendsto hmid hlow ?_
    filter_upwards [Filter.eventually_ge_atTop c] with m hm
    exact iptp_squeeze_upper hβ hh g T (by omega : (m - c) + c ≤ m)
  exact le_antisymm hle1 hle2







theorem iptp_plusState_isTranslationInvariant {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  iti_plusState_isTranslationInvariant_of_homogeneous β h
    (fun g => iptp_plusMultiHomogeneous hβ hh g)






theorem ising_plus_extreme (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isInvariantExtremePoint hd hβ hh (iptp_plusState_isTranslationInvariant hβ hh)


theorem iptp_plusState_isErgodic (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isErgodic hd hβ hh (iptp_plusState_isTranslationInvariant hβ hh)

end Ising

end StatMech
