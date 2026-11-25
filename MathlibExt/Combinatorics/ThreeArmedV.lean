/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Plane regions cut by three-armed V's

We define the number of connected components left by a set of cuts in the plane and prove the
maximum for finitely many three-armed V's. For the upper bound, an arm can increase the region
count by at most one per earlier ray, with a shared tip accounting for at most one extra region
on each arm after the first. For attainment, upward rays give two regions per tip and one per
pairwise crossing between arms from distinct tips, together with the region below the tips.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of regions cut out of the plane.** For a set $K \subseteq \mathbb{R}^2$ of cuts, the
number of regions into which $K$ divides the plane is the number of connected components of the
complement $\mathbb{R}^2 \setminus K$, or $0$ if there are infinitely many components.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1. -/
public noncomputable def planeRegionCount (K : Set (ℝ × ℝ)) : ℕ :=
  Set.ncard {C : Set (ℝ × ℝ) | ∃ x ∈ Kᶜ, C = connectedComponentIn Kᶜ x}

/-- **No cuts, one region.** The empty set of cuts divides the plane into exactly one region.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Section 1 (`n = 0`). -/
public theorem planeRegionCount_empty : planeRegionCount ∅ = 1 := by
  have h : {C : Set (ℝ × ℝ) | ∃ x ∈ (∅ : Set (ℝ × ℝ))ᶜ,
      C = connectedComponentIn (∅ : Set (ℝ × ℝ))ᶜ x} = {Set.univ} := by
    ext C
    simp [Set.compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  rw [planeRegionCount, h, Set.ncard_singleton]

end

open Set

namespace isGreatest_planeRegionCount_threeArmedV

private def regions {X : Type*} [TopologicalSpace X] (U : Set X) : Set (Set X) :=
  { C | ∃ x ∈ U, C = connectedComponentIn U x }

private theorem region_at {X : Type*} [TopologicalSpace X] {U : Set X} {x : X} (hx : x ∈ U) :
    connectedComponentIn U x ∈ regions U := ⟨x, hx, rfl⟩

private theorem region_relClosed {X : Type*} [TopologicalSpace X] {V : Set X}
    {x : X} (hx : x ∈ V) :
    closure (connectedComponentIn V x) ∩ V ⊆ connectedComponentIn V x := by
  rw [connectedComponentIn_eq_image hx]
  rintro y ⟨hy, hyV⟩
  refine ⟨⟨y, hyV⟩, ?_, rfl⟩
  rw [← isClosed_connectedComponent.closure_eq,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  exact hy

private theorem region_eq_of_disjoint {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {V B : Set X} (hV : IsOpen V) (hB : IsOpen B) {x : X}
    (hx : x ∈ V) (hCB : Disjoint (connectedComponentIn V x) B) :
    connectedComponentIn (V ∪ B) x = connectedComponentIn V x := by
  refine subset_antisymm ?_ (connectedComponentIn_mono x subset_union_left)
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (hV.connectedComponentIn) ⟨x, mem_connectedComponentIn (Or.inl hx),
      mem_connectedComponentIn hx⟩
  rintro y ⟨hy, hyU⟩
  rcases connectedComponentIn_subset _ _ hyU with hyV | hyB
  · exact region_relClosed hx ⟨hy, hyV⟩
  · exact False.elim <| Set.disjoint_left.1 (hCB.closure_left hB) hy hyB

private theorem regions_cut_le {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {V B : Set X} (hV : IsOpen V) (hB : IsOpen B)
    {b : X} (E : Set (Set X))
    (hE : ∀ x ∈ B ∩ V, connectedComponentIn V x = connectedComponentIn V b ∨
      connectedComponentIn V x ∈ E) :
    (regions V).encard ≤ (regions (V ∪ B)).encard + E.encard := by
  classical
  let T := regions V \ E
  have hex : ∀ C ∈ T, ∃ x ∈ V, C = connectedComponentIn V x := fun _ hC => hC.1
  choose x hx hCx using hex
  let p (C : Set X) (hC : C ∈ T) := connectedComponentIn (V ∪ B) (x C hC)
  have hp (C : Set X) (hC : C ∈ T) : p C hC ∈ regions (V ∪ B) :=
    region_at (Or.inl (hx C hC))
  have hsub (C : Set X) (hC : C ∈ T) : C ⊆ p C hC := by
    change C ⊆ connectedComponentIn (V ∪ B) (x C hC)
    exact (hCx C hC).le.trans (connectedComponentIn_mono _ subset_union_left)
  have hhit (C : Set X) (hC : C ∈ T) (h : (C ∩ B).Nonempty) :
      C = connectedComponentIn V b := by
    obtain ⟨y, hy, hyB⟩ := h
    have hyV : y ∈ V := connectedComponentIn_subset V _ (hCx C hC ▸ hy)
    have he : C = connectedComponentIn V y :=
      (hCx C hC).trans (connectedComponentIn_eq (hCx C hC ▸ hy))
    exact he.trans ((hE y ⟨hyB, hyV⟩).resolve_right (by simpa [← he] using hC.2))
  have hparent (C : Set X) (hC : C ∈ T) (h : Disjoint C B) : p C hC = C := by
    exact (region_eq_of_disjoint hV hB (hx C hC) (hCx C hC ▸ h)).trans (hCx C hC).symm
  have heq (C : Set X) (hC : C ∈ T) (D : Set X) (hD : D ∈ T) (h : D ⊆ C) : C = D := by
    have hxD : x D hD ∈ D := (hCx D hD).ge (mem_connectedComponentIn (hx D hD))
    exact (hCx C hC).trans <| (connectedComponentIn_eq
      ((hCx C hC).le (h hxD))).trans (hCx D hD).symm
  have hinj : Function.Injective (fun C : T => (⟨p C C.2, hp C C.2⟩ : regions (V ∪ B))) := by
    intro ⟨C, hC⟩ ⟨D, hD⟩ he
    have he' : p C hC = p D hD := congrArg Subtype.val he
    apply Subtype.ext
    by_cases hCB : Disjoint C B
    · have hDC : D ⊆ C := he' ▸ hsub D hD |>.trans (hparent C hC hCB).le
      exact heq C hC D hD hDC
    · by_cases hDB : Disjoint D B
      · have hCD : C ⊆ D := (hsub C hC).trans (he'.trans (hparent D hD hDB)).le
        exact (heq D hD C hC hCD).symm
      · exact (hhit C hC (not_disjoint_iff_nonempty_inter.1 hCB)).trans
          (hhit D hD (not_disjoint_iff_nonempty_inter.1 hDB)).symm
  have hT : T.encard ≤ (regions (V ∪ B)).encard := by
    rw [Set.encard, Set.encard]
    exact ENat.card_le_card_of_injective hinj
  refine (encard_mono (show regions V ⊆ T ∪ E from ?_)).trans
    ((encard_union_le T E).trans (add_le_add_left hT _))
  exact fun C hC => or_iff_not_imp_right.mpr fun h => ⟨hC, h⟩

/-! ## Cutting along the horizontal axis -/

private def axis (x : ℝ) : ℝ × ℝ := (x, 0)

private def axisCut (J : Set ℝ) : Set (ℝ × ℝ) :=
  Prod.fst ⁻¹' (J ∩ Ici 0) ∩ Prod.snd ⁻¹' {0}

private theorem closed_axisCut {J : Set ℝ} (hJ : IsClosed J) : IsClosed (axisCut J) :=
  ((hJ.inter isClosed_Ici).preimage continuous_fst).inter
    (isClosed_singleton.preimage continuous_snd)

open Classical in
private theorem axis_cut_region_bound {U : Set (ℝ × ℝ)} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hJc : IsPreconnected J) (hne : J.Nonempty)
    (hJU : J ⊆ axis ⁻¹' U) (hcl : closure J ∩ axis ⁻¹' U ⊆ J) :
    (regions (U \ axisCut (closure J))).encard ≤
      (regions U).encard + (if (J ∩ Iio 0).Nonempty then 0 else 1) := by
  classical
  open Metric in
  have htube : ∃ r : ℝ → ℝ, Continuous r ∧
      (∀ x ∈ J, 0 < r x) ∧ (∀ x ∈ J, ∀ y, |y| < r x → (x, y) ∈ U) := by
    by_cases hu : U = univ
    · exact ⟨fun _ => 1, continuous_const, by simp, by simp [hu]⟩
    have hUc : Uᶜ.Nonempty := Set.nonempty_compl.2 hu
    refine ⟨fun x => infDist (axis x) Uᶜ,
      (continuous_infDist_pt _).comp (continuous_id.prodMk continuous_const), ?_, ?_⟩
    · intro x hx
      exact (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (by simpa using hJU hx)
    · intro x hx y hy
      by_contra h
      have hle := infDist_le_dist_of_mem (x := axis x) (show (x, y) ∈ Uᶜ from h)
      rw [axis, dist_prod_same_left, Real.dist_eq, zero_sub, abs_neg] at hle
      exact hy.not_ge hle
  obtain ⟨r, hr, hrpos, hrU⟩ := htube
  let B : Set (ℝ × ℝ) := Prod.fst ⁻¹' J ∩ {p | |p.2| < r p.1}
  let V : Set (ℝ × ℝ) := U \ axisCut (closure J)
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, r p.1 * p.2)
  let D : Set (ℝ × ℝ) := J ×ˢ Ioo (-1) 1
  have hB : IsOpen B := (hJ.preimage continuous_fst).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) (hr.comp continuous_fst))
  have hV : IsOpen V := hU.sdiff (closed_axisCut isClosed_closure)
  have hUeq : V ∪ B = U := by
    apply subset_antisymm
    · exact union_subset sdiff_subset (by rintro ⟨x,y⟩ ⟨hx, hy⟩; exact hrU x hx y hy)
    · rintro ⟨x, y⟩ hp
      by_cases hcut : (x, y) ∈ axisCut (closure J)
      · have hy : y = 0 := hcut.2
        subst y
        have hx : x ∈ J := hcl ⟨hcut.1.1, hp⟩
        exact Or.inr ⟨hx, by simpa using hrpos x hx⟩
      · exact Or.inl ⟨hp, hcut⟩
  have hF : Continuous F := continuous_fst.prodMk ((hr.comp continuous_fst).mul continuous_snd)
  have hFmem (p : ℝ × ℝ) (hp : p ∈ D) : F p ∈ B := by
    refine ⟨hp.1, ?_⟩
    change |r p.1 * p.2| < r p.1
    rw [abs_mul, abs_of_pos (hrpos _ hp.1)]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (abs_lt.2 hp.2) (hrpos _ hp.1)
  have hcut (p : ℝ × ℝ) (hp : p ∈ D) :
      F p ∈ axisCut (closure J) ↔ 0 ≤ p.1 ∧ p.2 = 0 := by
    change (p.1 ∈ closure J ∧ 0 ≤ p.1) ∧ r p.1 * p.2 = 0 ↔ _
    have h := subset_closure hp.1
    simp [h, (hrpos _ hp.1).ne']
  let D' : Set (ℝ × ℝ) := D \ {p | 0 ≤ p.1 ∧ p.2 = 0}
  have hFimage : F '' D' = B ∩ V := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqB := hFmem q hq.1
      exact ⟨hqB, hUeq ▸ Or.inr hqB, fun h => hq.2 ((hcut q hq.1).1 h)⟩
    · rintro ⟨hpB, hpV⟩
      have hpJ : p.1 ∈ J := hpB.1
      have hpr := hrpos _ hpJ
      let q : ℝ × ℝ := (p.1, p.2 / r p.1)
      have he : F q = p := by simp [F, q, mul_div_cancel₀, hpr.ne']
      have hq : q ∈ D := by
        refine ⟨hpJ, abs_lt.1 ?_⟩
        change |p.2 / r p.1| < 1
        rw [abs_div, abs_of_pos hpr, div_lt_iff₀ hpr, one_mul]
        exact hpB.2
      exact ⟨q, ⟨hq, fun hc => hpV.2 (he ▸ (hcut q hq).2 hc)⟩, he⟩
  let P : Set (ℝ × ℝ) := J ×ˢ Ioo 0 1
  let M : Set (ℝ × ℝ) := J ×ˢ Ioo (-1) 0
  have hP : IsPreconnected P := hJc.prod isPreconnected_Ioo
  have hM : IsPreconnected M := hJc.prod isPreconnected_Ioo
  have hPD : P ⊆ D' := by
    rintro ⟨x, y⟩ ⟨hx, hy₀, hy₁⟩
    exact ⟨⟨hx, by constructor <;> linarith [hy₀, hy₁]⟩, fun h => hy₀.ne' h.2⟩
  have hMD : M ⊆ D' := by
    rintro ⟨x, y⟩ ⟨hx, hy₀, hy₁⟩
    exact ⟨⟨hx, by constructor <;> linarith [hy₀, hy₁]⟩, fun h => hy₁.ne h.2⟩
  obtain ⟨x, hx⟩ := hne
  have hbP : (x, (1 / 2 : ℝ)) ∈ P := ⟨hx, by constructor <;> norm_num⟩
  have hbM : (x, (-1 / 2 : ℝ)) ∈ M := ⟨hx, by constructor <;> norm_num⟩
  let b := F (x, 1 / 2)
  let c := F (x, -1 / 2)
  have hb : b ∈ B ∩ V := hFimage ▸ mem_image_of_mem F (hPD hbP)
  change (regions V).encard ≤ (regions U).encard + _
  rw [← hUeq]
  split_ifs with hneg
  · let N : Set (ℝ × ℝ) := (J ∩ Iio 0) ×ˢ Ioo (-1) 1
    have hN : IsPreconnected N :=
      (hJc.ordConnected.inter ordConnected_Iio).isPreconnected.prod isPreconnected_Ioo
    obtain ⟨w, hwJ, hw⟩ := hneg
    have hNp : (P ∩ N).Nonempty :=
      ⟨(w, 1 / 2), ⟨hwJ, by constructor <;> norm_num⟩,
        ⟨⟨hwJ, hw⟩, by constructor <;> norm_num⟩⟩
    have hNm : (M ∩ (P ∪ N)).Nonempty :=
      ⟨(w, -1 / 2), ⟨hwJ, by constructor <;> norm_num⟩,
        Or.inr ⟨⟨hwJ, hw⟩, by constructor <;> norm_num⟩⟩
    have hDeq : D' = M ∪ (P ∪ N) := by
      ext p
      rcases p with ⟨a, d⟩
      change (a ∈ J ∧ (-1 < d ∧ d < 1)) ∧ ¬ (0 ≤ a ∧ d = 0) ↔
        (a ∈ J ∧ (-1 < d ∧ d < 0)) ∨
        (a ∈ J ∧ (0 < d ∧ d < 1)) ∨ (a ∈ J ∧ a < 0) ∧ (-1 < d ∧ d < 1)
      constructor
      · rintro ⟨⟨ha, h₁, h₂⟩, hn⟩
        rcases lt_trichotomy d 0 with hd | rfl | hd
        · exact Or.inl ⟨ha, h₁, hd⟩
        · exact Or.inr (Or.inr ⟨⟨ha, lt_of_not_ge (fun haf => hn ⟨haf, rfl⟩)⟩, h₁, h₂⟩)
        · exact Or.inr (Or.inl ⟨ha, hd, h₂⟩)
      · rintro (⟨ha, h₁, hd⟩ | ⟨ha, hd, h₂⟩ | ⟨⟨ha, hneg⟩, h₁, h₂⟩)
        · exact ⟨⟨ha, h₁, hd.trans (by norm_num)⟩, fun h => hd.ne h.2⟩
        · exact ⟨⟨ha, (by norm_num : (-1 : ℝ) < 0).trans hd, h₂⟩, fun h => hd.ne' h.2⟩
        · exact ⟨⟨ha, h₁, h₂⟩, fun h => hneg.not_ge h.1⟩
    have hBV : IsPreconnected (B ∩ V) := hFimage ▸
      (hDeq.symm ▸ hM.union' hNm (hP.union' hNp hN)).image F hF.continuousOn
    simpa using regions_cut_le hV hB (b := b) ∅ (fun y hy => Or.inl
      (connectedComponentIn_eq
        (hBV.subset_connectedComponentIn hb inter_subset_right hy)).symm)
  · have hDeq : D' = P ∪ M := by
      ext p
      rcases p with ⟨a, d⟩
      change (a ∈ J ∧ (-1 < d ∧ d < 1)) ∧ ¬ (0 ≤ a ∧ d = 0) ↔
        (a ∈ J ∧ (0 < d ∧ d < 1)) ∨ (a ∈ J ∧ (-1 < d ∧ d < 0))
      have hn : a ∈ J → 0 ≤ a := fun ha => le_of_not_gt (fun hh => hneg ⟨a, ha, hh⟩)
      constructor
      · rintro ⟨⟨ha, h₁, h₂⟩, hn'⟩
        rcases lt_or_gt_of_ne (fun he => hn' ⟨hn ha, he⟩) with hd | hd
        · exact Or.inr ⟨ha, h₁, hd⟩
        · exact Or.inl ⟨ha, hd, h₂⟩
      · rintro (⟨ha, hd, h₂⟩ | ⟨ha, h₁, hd⟩)
        · exact ⟨⟨ha, (by norm_num : (-1 : ℝ) < 0).trans hd, h₂⟩, fun h => hd.ne' h.2⟩
        · exact ⟨⟨ha, h₁, hd.trans (by norm_num)⟩, fun h => hd.ne h.2⟩
    have hpSub : F '' P ⊆ V := (image_mono hPD).trans (hFimage ▸ inter_subset_right)
    have hmSub : F '' M ⊆ V := (image_mono hMD).trans (hFimage ▸ inter_subset_right)
    have hcover (y : ℝ × ℝ) (hy : y ∈ B ∩ V) : y ∈ F '' P ∨ y ∈ F '' M := by
      rwa [← mem_union, ← image_union, ← hDeq, hFimage]
    simpa using regions_cut_le hV hB (b := b) {connectedComponentIn V c} (fun y hy => by
      rcases hcover y hy with h | h
      · have hh := (hP.image F hF.continuousOn).subset_connectedComponentIn
          (mem_image_of_mem F hbP) hpSub h
        exact Or.inl (connectedComponentIn_eq hh).symm
      · exact Or.inr (mem_singleton_iff.2 (connectedComponentIn_eq
          ((hM.image F hF.continuousOn).subset_connectedComponentIn
            (mem_image_of_mem F hbM) hmSub h)).symm))

private theorem regions_eq_of_inter {X : Type*} [TopologicalSpace X] {U C D : Set X}
    (hC : C ∈ regions U) (hD : D ∈ regions U) (h : (C ∩ D).Nonempty) : C = D := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, rfl⟩ := hD
  obtain ⟨z, hzC, hzD⟩ := h
  exact (connectedComponentIn_eq hzC).trans (connectedComponentIn_eq hzD).symm

-- Charge each interval that can split a region to a blocked interval on its left.
-- An interval that contains the tip has a path around the tip and costs zero.
private theorem axis_union_bound {ι : Type*} [Fintype ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (T : ι → Set ℝ) (hT : ∀ i, (T i).OrdConnected)
    (hTeq : (axis ⁻¹' U)ᶜ = ⋃ i, T i) :
    (regions (U \ axisCut univ)).encard ≤ (regions U).encard + Fintype.card ι := by
  classical
  let A := axis ⁻¹' U
  have haxis : Continuous axis := continuous_id.prodMk continuous_const
  have hA : IsOpen A := hU.preimage haxis
  let Q : Set (Set ℝ) := {J | J ∈ regions A ∧ (J ∩ Ici 0).Nonempty}
  let P : Set (Set ℝ) := {J ∈ Q | ¬ (J ∩ Iio 0).Nonempty}
  have hsets {J : Set ℝ} (hJ : J ∈ Q) :
      IsOpen J ∧ IsPreconnected J ∧ J.Nonempty ∧ J ⊆ A ∧ closure J ∩ A ⊆ J := by
    obtain ⟨t, ht, rfl⟩ := hJ.1
    exact ⟨hA.connectedComponentIn, isPreconnected_connectedComponentIn,
      ⟨t, mem_connectedComponentIn ht⟩, connectedComponentIn_subset _ _, region_relClosed ht⟩
  have hbb (J : P) : BddBelow (J : Set ℝ) :=
    ⟨0, fun x hx => le_of_not_gt (fun h => J.2.2 ⟨x, hx, h⟩)⟩
  have hstrict (J : P) {x : ℝ} (hx : x ∈ (J : Set ℝ)) : sInf (J : Set ℝ) < x := by
    apply lt_of_le_of_ne (csInf_le (hbb J) hx)
    intro h
    subst x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hsets J.2.1).1 _ hx
    let x := sInf (J : Set ℝ) - ε / 2
    have hmem : x ∈ Metric.ball (sInf (J : Set ℝ)) ε := by
      change dist x (sInf (J : Set ℝ)) < ε
      rw [Real.dist_eq, abs_lt]
      dsimp [x]
      constructor <;> linarith
    have hle := csInf_le (hbb J) (hball hmem)
    dsimp [x] at hle
    linarith
  have hJinf (J : P) : sInf (J : Set ℝ) ∈ Aᶜ :=
    fun hx => (hstrict J ((hsets J.2.1).2.2.2.2
      ⟨csInf_mem_closure (hsets J.2.1).2.2.1 (hbb J), hx⟩)).false
  have hex (J : P) : ∃ i, sInf (J : Set ℝ) ∈ T i := mem_iUnion.1 (hTeq ▸ hJinf J)
  choose pick hpick using hex
  have hcontr (C D : P) (h : pick C = pick D)
      (hlt : sInf (C : Set ℝ) < sInf (D : Set ℝ)) : False := by
    obtain ⟨x, hxC, hxd⟩ := exists_lt_of_csInf_lt (hsets C.2.1).2.2.1 hlt
    have hxT := (hT (pick C)).out (hpick C) (h ▸ hpick D)
      (show x ∈ Icc (sInf (C : Set ℝ)) (sInf (D : Set ℝ)) from
        ⟨csInf_le (hbb C) hxC, hxd.le⟩)
    exact ((hTeq ▸ mem_iUnion_of_mem (pick C) hxT : x ∈ Aᶜ)) ((hsets C.2.1).2.2.2.1 hxC)
  have hinf (C D : P) (h : sInf (C : Set ℝ) = sInf (D : Set ℝ)) : C = D := by
    have hone (C D : P) (h : sInf (C : Set ℝ) = sInf (D : Set ℝ))
        {x y : ℝ} (hx : x ∈ (C : Set ℝ)) (hy : y ∈ (D : Set ℝ)) (hxy : x ≤ y) : C = D := by
      have hx' : sInf (D : Set ℝ) < x := h ▸ hstrict C hx
      obtain ⟨w, hwD, hwx⟩ := exists_lt_of_csInf_lt (hsets D.2.1).2.2.1 hx'
      have hxD := (hsets D.2.1).2.1.ordConnected.out hwD hy
        (show x ∈ Icc w y from ⟨hwx.le, hxy⟩)
      exact Subtype.ext (regions_eq_of_inter C.2.1.1 D.2.1.1 ⟨x, hx, hxD⟩)
    obtain ⟨x, hx⟩ := (hsets C.2.1).2.2.1
    obtain ⟨y, hy⟩ := (hsets D.2.1).2.2.1
    rcases le_total x y with hxy | hyx
    · exact hone C D h hx hy hxy
    · exact (hone D C h.symm hy hx hyx).symm
  have hpi : Function.Injective pick := by
    intro C D h
    apply hinf
    exact le_antisymm (le_of_not_gt (hcontr D C h.symm)) (le_of_not_gt (hcontr C D h))
  have hPenc : P.encard ≤ Fintype.card ι := by
    change ENat.card P ≤ _
    rw [← ENat.card_eq_coe_fintype_card]
    exact ENat.card_le_card_of_injective hpi
  have hPfin : P.Finite := encard_lt_top_iff.1 (hPenc.trans_lt (by simp))
  have hQfin : Q.Finite := by
    refine (hPfin.insert (connectedComponentIn A 0)).subset ?_
    intro J hJ
    by_cases hneg : (J ∩ Iio 0).Nonempty
    · obtain ⟨x, hxJ, hx⟩ := hneg
      obtain ⟨y, hyJ, hy⟩ := hJ.2
      have h0 : 0 ∈ J := (hsets hJ).2.1.ordConnected.out hxJ hyJ
        (show 0 ∈ Icc x y from ⟨hx.le, hy⟩)
      obtain ⟨t, ht, rfl⟩ := hJ.1
      exact Or.inl (connectedComponentIn_eq h0)
    · exact Or.inr ⟨hJ, hneg⟩
  let f := hQfin.toFinset
  let cut (s : Finset (Set ℝ)) := U \ ⋃ J ∈ s, axisCut (closure J)
  have hcut_op (s : Finset (Set ℝ)) : IsOpen (cut s) :=
    hU.sdiff (isClosed_biUnion_finset (fun _ _ => closed_axisCut isClosed_closure))
  have hfQ {J : Set ℝ} : J ∈ f ↔ J ∈ Q := hQfin.mem_toFinset
  have hfull : cut f = U \ axisCut univ := by
    ext p
    constructor
    · rintro ⟨hpU, hp⟩
      refine ⟨hpU, fun h => hp ?_⟩
      have hy : p.2 = 0 := h.2
      have haxisP : axis p.1 = p := Prod.ext rfl hy.symm
      have hx : p.1 ∈ A := haxisP ▸ hpU
      let J := connectedComponentIn A p.1
      have hpJ : p.1 ∈ J := mem_connectedComponentIn hx
      have hJ : J ∈ f := hfQ.2 ⟨region_at hx, ⟨p.1, hpJ, h.1.2⟩⟩
      exact mem_iUnion₂_of_mem hJ ⟨⟨subset_closure hpJ, h.1.2⟩, hy⟩
    · rintro ⟨hpU, hp⟩
      refine ⟨hpU, ?_⟩
      intro h
      obtain ⟨J, hJ, hmem⟩ := mem_iUnion₂.1 h
      exact hp ⟨⟨mem_univ _, hmem.1.2⟩, hmem.2⟩
  have hcount (s : Finset (Set ℝ)) (hs : ∀ J ∈ s, J ∈ Q) :
      (regions (cut s)).encard ≤ (regions U).encard + ((s.filter (· ∈ P)).card : ℕ∞) := by
    induction s using Finset.induction_on with
    | empty => simp [cut]
    | @insert J s hnot ih =>
      have hJ := hs J (Finset.mem_insert_self _ _)
      have hs' (D : Set ℝ) (hD : D ∈ s) : D ∈ Q := hs D (Finset.mem_insert_of_mem hD)
      obtain ⟨hJop, hJc, hJne, hJA, hJcl⟩ := hsets hJ
      have hJsub : J ⊆ axis ⁻¹' cut s := by
        intro x hx
        refine ⟨hJA hx, ?_⟩
        intro h
        obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.1 h
        have hmemD : x ∈ D := (hsets (hs' D hD)).2.2.2.2 ⟨hxD.1.1, hJA hx⟩
        exact hnot ((regions_eq_of_inter hJ.1 (hs' D hD).1 ⟨x, hx, hmemD⟩).symm ▸ hD)
      have hJcl' : closure J ∩ axis ⁻¹' cut s ⊆ J :=
        fun x hx => hJcl ⟨hx.1, hx.2.1⟩
      have heq : cut (insert J s) = cut s \ axisCut (closure J) := by
        ext x
        simp only [cut, Finset.set_biUnion_insert, mem_sdiff, mem_union]
        tauto
      rw [heq]
      have hc := axis_cut_region_bound (hcut_op s) hJop hJc hJne hJsub hJcl'
      refine hc.trans ((add_le_add_left (ih hs') _).trans ?_)
      by_cases hP : J ∈ P
      · have h : ¬ (J ∩ Iio 0).Nonempty := hP.2
        simp [Finset.filter_insert, hP, h, hnot, add_assoc]
      · have h : (J ∩ Iio 0).Nonempty := by simpa [P, hJ] using hP
        simp [Finset.filter_insert, hP, h]
  rw [← hfull]
  have hcard : ((f.filter (· ∈ P)).card : ℕ∞) ≤ Fintype.card ι := by
    rw [← encard_coe_eq_coe_finsetCard]
    exact (encard_mono (fun _ hx => (Finset.mem_filter.1 hx).2)).trans hPenc
  exact (hcount f (fun _ => hfQ.1)).trans (add_le_add_right hcard _)

/-! ## The upper bound for arbitrary rays -/

private theorem regions_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (U : Set X) :
    regions (e '' U) = (fun C : Set X => e '' C) '' regions U := by
  ext D
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, region_at hx, e.image_connectedComponentIn hx⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, mem_image_of_mem e hx, e.image_connectedComponentIn hx⟩

private theorem regions_encard_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (U : Set X) : (regions (e '' U)).encard = (regions U).encard := by
  rw [regions_image, e.injective.image_injective.encard_image]

private def ray (c u : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun s : ℝ => c + s • u) '' Ici 0

private theorem tip_mem_ray (c u : ℝ × ℝ) : c ∈ ray c u :=
  ⟨0, mem_Ici.2 le_rfl, by simp⟩

private theorem coe_ray_lineMap (c u : ℝ × ℝ) :
    ⇑(AffineMap.lineMap (k := ℝ) c (u + c)) = fun s : ℝ => c + s • u := by
  funext t
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, add_comm]

private theorem ray_convex (c u : ℝ × ℝ) : Convex ℝ (ray c u) := by
  have h := (convex_Ici (0 : ℝ)).affine_image (AffineMap.lineMap c (u + c))
  rwa [coe_ray_lineMap] at h

private theorem exists_ray_homeomorph (c u : ℝ × ℝ) (hu : u ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : ℝ, e (axis t) = c + t • u := by
  let d := u.1 ^ 2 + u.2 ^ 2
  have hd : d ≠ 0 := by
    intro h
    have h₁ : u.1 = 0 := by dsimp [d] at h; nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h₂ : u.2 = 0 := by dsimp [d] at h; nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    exact hu (Prod.ext h₁ h₂)
  let f (p : ℝ × ℝ) := (c.1 + p.1 * u.1 - p.2 * u.2, c.2 + p.1 * u.2 + p.2 * u.1)
  let g (p : ℝ × ℝ) := (((p.1 - c.1) * u.1 + (p.2 - c.2) * u.2) / d,
    ((p.2 - c.2) * u.1 - (p.1 - c.1) * u.2) / d)
  let e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := f
    invFun := g
    left_inv p := by
      apply Prod.ext <;> dsimp [f, g] <;> field_simp [hd] <;> dsimp [d] <;> ring
    right_inv p := by
      apply Prod.ext <;> dsimp [f, g] <;> field_simp [hd] <;> dsimp [d] <;> ring
    continuous_toFun := by dsimp [f]; fun_prop
    continuous_invFun := by dsimp [g]; fun_prop }
  refine ⟨e, fun t => ?_⟩
  change f (t, 0) = c + t • u
  apply Prod.ext <;> simp [f]

private theorem ray_image_axisCut (c u : ℝ × ℝ) (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (he : ∀ t : ℝ, e (axis t) = c + t • u) :
    e '' axisCut univ = ray c u := by
  have h : axisCut univ = axis '' Ici 0 := by
    ext p
    constructor
    · intro hp
      exact ⟨p.1, hp.1.2, Prod.ext rfl hp.2.symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨mem_univ _, hx⟩, rfl⟩
  rw [h, image_image]
  simp only [ray, he]

private theorem ray_closed (c u : ℝ × ℝ) (hu : u ≠ 0) : IsClosed (ray c u) := by
  obtain ⟨e, he⟩ := exists_ray_homeomorph c u hu
  rw [← ray_image_axisCut c u e he]
  exact e.isClosedMap _ (closed_axisCut isClosed_univ)

private theorem ray_trace_ordConnected (c u p v : ℝ × ℝ) :
    ((fun t : ℝ => c + t • u) ⁻¹' ray p v).OrdConnected := by
  have h := (ray_convex p v).affine_preimage (AffineMap.lineMap c (u + c))
  rw [← convex_iff_ordConnected]
  rwa [coe_ray_lineMap] at h

private theorem ray_union_bound {ι : Type*} [Fintype ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (c u : ℝ × ℝ) (hu : u ≠ 0) (B : ι → Set (ℝ × ℝ))
    (hB : ∀ i, ((fun t : ℝ => c + t • u) ⁻¹' B i).OrdConnected)
    (hBeq : Uᶜ = ⋃ i, B i) :
    (regions (U \ ray c u)).encard ≤ (regions U).encard + Fintype.card ι := by
  obtain ⟨e, he⟩ := exists_ray_homeomorph c u hu
  let W := e ⁻¹' U
  have hW : IsOpen W := hU.preimage e.continuous
  let T (i : ι) := (fun t : ℝ => c + t • u) ⁻¹' B i
  have hTeq : (axis ⁻¹' W)ᶜ = ⋃ i, T i := by
    rw [show axis ⁻¹' W = (fun t : ℝ => c + t • u) ⁻¹' U from by
      ext t; simp [W, he], ← preimage_compl, hBeq, preimage_iUnion]
  have h := axis_union_bound hW T hB hTeq
  have hWimage : e '' W = U := e.surjective.image_preimage _
  have hcut : e '' (W \ axisCut univ) = U \ ray c u := by
    rw [image_sdiff e.injective, hWimage, ray_image_axisCut c u e he]
  rw [← hcut, ← hWimage, regions_encard_image, regions_encard_image]
  exact h

private theorem tip_pair_trace (c u v w : ℝ × ℝ) :
    ((fun t : ℝ => c + t • u) ⁻¹' (ray c v ∪ ray c w)).OrdConnected := by
  rw [preimage_union, ← isPreconnected_iff_ordConnected]
  apply (ray_trace_ordConnected c u c v).isPreconnected.union (0 : ℝ)
  · simpa using tip_mem_ray c v
  · simpa using tip_mem_ray c w
  · exact (ray_trace_ordConnected c u c w).isPreconnected

private theorem added_fan_bound {ι : Type*} [Fintype ι] {p v : ι → ℝ × ℝ}
    (hv : ∀ a, v a ≠ 0) (c : ℝ × ℝ) (u : Fin 3 → ℝ × ℝ) (hu : ∀ j, u j ≠ 0) :
    (regions ((⋃ a, ray (p a) (v a)) ∪ ⋃ j, ray c (u j))ᶜ).encard ≤
      (regions (⋃ a, ray (p a) (v a))ᶜ).encard + (3 * Fintype.card ι + 2 : ℕ) := by
  let B (a : ι) := ray (p a) (v a)
  let K := ⋃ a, B a
  let B₀ : Option ι → Set (ℝ × ℝ) := fun a => a.elim (ray c (u 0)) B
  let B₁ : Option ι → Set (ℝ × ℝ) := fun a => a.elim (ray c (u 0) ∪ ray c (u 1)) B
  have hc : IsClosed K := isClosed_iUnion_of_finite (fun a => ray_closed (p a) (v a) (hv a))
  have hc₀ : IsClosed (K ∪ ray c (u 0)) := hc.union (ray_closed c (u 0) (hu 0))
  have hc₁ : IsClosed (K ∪ (ray c (u 0) ∪ ray c (u 1))) :=
    hc.union ((ray_closed c (u 0) (hu 0)).union (ray_closed c (u 1) (hu 1)))
  have hb₀ : (K ∪ ray c (u 0))ᶜᶜ = ⋃ a, B₀ a := by
    rw [compl_compl, iUnion_option]
    exact union_comm _ _
  have hb₁ : (K ∪ (ray c (u 0) ∪ ray c (u 1)))ᶜᶜ = ⋃ a, B₁ a := by
    rw [compl_compl, iUnion_option]
    exact union_comm _ _
  have h₀ := ray_union_bound hc.isOpen_compl c (u 0) (hu 0) B
    (fun a => ray_trace_ordConnected c (u 0) (p a) (v a)) (compl_compl K)
  have h₁ := ray_union_bound hc₀.isOpen_compl c (u 1) (hu 1) B₀ (by
    rintro (_ | a)
    · exact ray_trace_ordConnected c (u 1) c (u 0)
    · exact ray_trace_ordConnected c (u 1) (p a) (v a)) hb₀
  have h₂ := ray_union_bound hc₁.isOpen_compl c (u 2) (hu 2) B₁ (by
    rintro (_ | a)
    · exact tip_pair_trace c (u 2) (u 0) (u 1)
    · exact ray_trace_ordConnected c (u 2) (p a) (v a)) hb₁
  have hcEq (X Y : Set (ℝ × ℝ)) : Xᶜ \ Y = (X ∪ Y)ᶜ := by
    ext x
    simp
  rw [hcEq] at h₀ h₁ h₂
  rw [union_assoc] at h₁ h₂
  change (regions (K ∪ ⋃ j, ray c (u j))ᶜ).encard ≤ _
  have heq : (⋃ j, ray c (u j)) = ray c (u 0) ∪ (ray c (u 1) ∪ ray c (u 2)) := by
    ext z
    constructor
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.1 h
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr hj)
    · rintro (h | h | h)
      · exact mem_iUnion_of_mem 0 h
      · exact mem_iUnion_of_mem 1 h
      · exact mem_iUnion_of_mem 2 h
  rw [heq, ← union_assoc (ray c (u 0))]
  have h := h₂.trans ((add_le_add_left h₁ _).trans (add_le_add_left
    (add_le_add_left h₀ _) _))
  refine h.trans_eq ?_
  simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem max_count_nat (n : ℕ) : 1 + 2 * n + 9 * n.choose 2 =
    (9 * n ^ 2 - 5 * n + 2) / 2 := by
  have h : 2 * n.choose 2 + n = n ^ 2 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
      nlinarith
  have h₁ : 5 * n ≤ 9 * n ^ 2 := by omega
  have h₂ : 2 * (1 + 2 * n + 9 * n.choose 2) = 9 * n ^ 2 - 5 * n + 2 := by omega
  omega

private theorem all_fans_bound {n : ℕ} (c : Fin n → ℝ × ℝ)
    (u : Fin n → Fin 3 → ℝ × ℝ) (hu : ∀ i j, u i j ≠ 0) :
    (regions (⋃ i, ⋃ j, ray (c i) (u i j))ᶜ).encard ≤ (1 + 2 * n + 9 * n.choose 2 : ℕ) := by
  classical
  let K (s : Finset (Fin n)) := ⋃ i ∈ s, ⋃ j, ray (c i) (u i j)
  have hbase : regions (univ : Set (ℝ × ℝ)) = {univ} := by
    ext x
    simp [regions, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  have h (s : Finset (Fin n)) :
      (regions (K s)ᶜ).encard ≤ (1 + 2 * s.card + 9 * s.card.choose 2 : ℕ) := by
    induction s using Finset.induction_on with
    | empty => simp [K, hbase]
    | @insert i s his ih =>
      let p (a : s × Fin 3) := c a.1
      let v (a : s × Fin 3) := u a.1 a.2
      have heq : (⋃ a, ray (p a) (v a)) = K s := by
        ext z
        simp only [p, v, K, mem_iUnion]
        exact ⟨fun ⟨⟨a, j⟩, ha⟩ => ⟨a, a.2, j, ha⟩,
          fun ⟨a, ha, j, hz⟩ => ⟨(⟨a, ha⟩, j), hz⟩⟩
      have hKi : K (insert i s) = K s ∪ ⋃ j, ray (c i) (u i j) := by
        change (⋃ a ∈ insert i s, ⋃ j, ray (c a) (u a j)) =
          (⋃ a ∈ s, ⋃ j, ray (c a) (u a j)) ∪ ⋃ j, ray (c i) (u i j)
        rw [Finset.set_biUnion_insert, union_comm]
      have hi := added_fan_bound (p := p) (v := v) (fun a => hu a.1 a.2) (c i) (u i) (hu i)
      rw [heq, ← hKi, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hi
      refine hi.trans ((add_le_add_left ih _).trans ?_)
      rw [← Nat.cast_add, Finset.card_insert_of_notMem his, Nat.choose_succ_succ' _ 1,
        Nat.choose_one_right, Nat.cast_le]
      simp only [show 1 + 1 = 2 from rfl]
      omega
  simpa [K] using h Finset.univ

/-! ## Regions between upward rays -/

private def lineAt {α : Type*} (b m : α → ℝ) (a : α) (t : ℝ) : ℝ :=
  b a + t * m a

private def upwardRay {α : Type*} (b m : α → ℝ) (a : α) : Set (ℝ × ℝ) :=
  ray (b a, 0) (m a, 1)

private theorem mem_upwardRay {α : Type*} (b m : α → ℝ) (a : α) (p : ℝ × ℝ) :
    p ∈ upwardRay b m a ↔ 0 ≤ p.2 ∧ p.1 = lineAt b m a p.2 := by
  rcases p with ⟨x, y⟩
  simp only [upwardRay, ray, mem_image, mem_Ici, Prod.smul_mk, smul_eq_mul, mul_one,
    Prod.mk_add_mk, zero_add, Prod.mk.injEq, lineAt]
  exact ⟨fun ⟨t, ht, hx, hy⟩ => ⟨hy ▸ ht, hy ▸ hx.symm⟩, fun ⟨hy, hx⟩ =>
    ⟨y, hy, hx.symm, rfl⟩⟩

private def gap {α : Type*} (b m : α → ℝ) (l r : α) : Set (ℝ × ℝ) :=
  {p | lineAt b m l p.2 < p.1 ∧ p.1 < lineAt b m r p.2}

private def weakGap {α : Type*} (b m : α → ℝ) (l r : α) : Set (ℝ × ℝ) :=
  {p | lineAt b m l p.2 ≤ p.1 ∧ p.1 ≤ lineAt b m r p.2}

private theorem lineAt_continuous {α : Type*} (b m : α → ℝ) (a : α) :
    Continuous (lineAt b m a) := by
  unfold lineAt
  fun_prop

private theorem gap_open {α : Type*} (b m : α → ℝ) (l r : α) :
    IsOpen (gap b m l r) :=
  (isOpen_lt ((lineAt_continuous b m l).comp continuous_snd) continuous_fst).inter
    (isOpen_lt continuous_fst ((lineAt_continuous b m r).comp continuous_snd))

private theorem weakGap_closed {α : Type*} (b m : α → ℝ) (l r : α) :
    IsClosed (weakGap b m l r) :=
  (isClosed_le ((lineAt_continuous b m l).comp continuous_snd) continuous_fst).inter
    (isClosed_le continuous_fst ((lineAt_continuous b m r).comp continuous_snd))

private theorem gap_subset_weakGap {α : Type*} (b m : α → ℝ) (l r : α) :
    gap b m l r ⊆ weakGap b m l r :=
  fun _ hp => ⟨hp.1.le, hp.2.le⟩

private theorem weakGap_height {α : Type*} {b m : α → ℝ} {l r : α} {t : ℝ}
    (hm : m l < m r) (ht : lineAt b m l t = lineAt b m r t) {p : ℝ × ℝ}
    (hp : p ∈ weakGap b m l r) : t ≤ p.2 := by
  by_contra! h
  have hneg := mul_neg_of_neg_of_pos (sub_neg.2 h) (sub_pos.2 hm)
  have hle := hp.1.trans hp.2
  dsimp [lineAt] at ht hle
  nlinarith

private theorem gap_lt_height {α : Type*} {b m : α → ℝ} {l r : α} {t : ℝ}
    (hm : m l < m r) (ht : lineAt b m l t = lineAt b m r t) {p : ℝ × ℝ}
    (hp : p ∈ gap b m l r) : t < p.2 := by
  refine lt_of_le_of_ne (weakGap_height hm ht (gap_subset_weakGap b m l r hp)) ?_
  intro he
  have h := hp.1.trans hp.2
  rw [← he, ht] at h
  exact (lt_irrefl _ h)

-- A short path up the middle of the gap lies in one region with the apex in its closure.
-- The two rays bound this region, so its closure cannot approach a lower height.
private theorem exists_gap_region {α : Type*} [Finite α] (b m : α → ℝ) (l r : α)
    (hm : m l < m r) (x t : ℝ) (ht : 0 ≤ t)
    (hl : lineAt b m l t = x) (hr : lineAt b m r t = x)
    (hadj : ∀ a, lineAt b m a t = x → m a ≤ m l ∨ m r ≤ m a) :
    ∃ C ∈ regions (⋃ a, upwardRay b m a)ᶜ,
      (x, t) ∈ closure C ∧ C ⊆ gap b m l r := by
  let U := (⋃ a, upwardRay b m a)ᶜ
  let S := ⋃ a : {a // lineAt b m a t ≠ x}, upwardRay b m a.1
  have hSc : IsClosed S := isClosed_iUnion_of_finite (fun a =>
    ray_closed _ _ (fun h => one_ne_zero (congrArg Prod.snd h)))
  have hxSc : (x, t) ∈ Sᶜ := by
    intro h
    obtain ⟨a, ha⟩ := mem_iUnion.1 h
    exact a.2 ((mem_upwardRay b m a.1 (x, t)).1 ha).2.symm
  let avg := (m l + m r) / 2
  have havl : m l < avg := by dsimp [avg]; linarith
  have havr : avg < m r := by dsimp [avg]; linarith
  let f (s : ℝ) := (x + s * avg, t + s)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf₀ : f 0 = (x, t) := by simp [f]
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (hSc.isOpen_compl.preimage hf) 0
    (show f 0 ∈ Sᶜ from hf₀.symm ▸ hxSc)
  let I : Set ℝ := Ioo 0 ε
  have hIU : f '' I ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    intro hu
    obtain ⟨a, ha⟩ := mem_iUnion.1 hu
    by_cases he : lineAt b m a t = x
    · have h := ((mem_upwardRay b m a (f s)).1 ha).2
      change x + s * avg = lineAt b m a (t + s) at h
      have hzero : s * (avg - m a) = 0 := by
        dsimp [lineAt] at he h
        nlinarith
      have ha' := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hs.1.ne')
      rcases hadj a he with ha₁ | ha₂
      · exact havl.not_ge (ha' ▸ ha₁)
      · exact havr.not_ge (ha' ▸ ha₂)
    · have hfs : f s ∈ Sᶜ := hεsub (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact hs.2)
      exact hfs (mem_iUnion_of_mem ⟨a, he⟩ ha)
  have hIgap : f '' I ⊆ gap b m l r := by
    rintro _ ⟨s, hs, rfl⟩
    change lineAt b m l (t + s) < x + s * avg ∧ x + s * avg < lineAt b m r (t + s)
    dsimp [lineAt] at hl hr ⊢
    constructor
    · nlinarith [mul_pos hs.1 (sub_pos.2 havl)]
    · nlinarith [mul_pos hs.1 (sub_pos.2 havr)]
  let p := f (ε / 2)
  have hp : p ∈ f '' I := ⟨ε / 2, by constructor <;> linarith, rfl⟩
  have hpU : p ∈ U := hIU hp
  refine ⟨connectedComponentIn U p, region_at hpU, ?_, ?_⟩
  · have hcl : (x, t) ∈ closure (f '' I) := by
      rw [← hf₀]
      apply mem_closure_image hf.continuousAt
      change (0 : ℝ) ∈ closure (Ioo 0 ε)
      rw [closure_Ioo (ne_of_lt hε)]
      exact ⟨le_rfl, hε.le⟩
    have hI : IsPreconnected I := isPreconnected_Ioo
    have himage := hI.image f hf.continuousOn
    exact closure_mono (himage.subset_connectedComponentIn hp hIU) hcl
  · refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      (gap_open b m l r) ⟨p, mem_connectedComponentIn hpU, hIgap hp⟩ ?_
    intro q hq
    have hqg := closure_minimal (gap_subset_weakGap b m l r) (weakGap_closed b m l r) hq.1
    have hqU := connectedComponentIn_subset _ _ hq.2
    have hqt := ht.trans (weakGap_height hm (hl.trans hr.symm) hqg)
    refine ⟨lt_of_le_of_ne hqg.1 ?_, lt_of_le_of_ne hqg.2 ?_⟩
    · intro he
      exact hqU (mem_iUnion_of_mem l ((mem_upwardRay b m l q).2 ⟨hqt, he.symm⟩))
    · intro he
      exact hqU (mem_iUnion_of_mem r ((mem_upwardRay b m r q).2 ⟨hqt, he⟩))


private theorem gaps_lower_bound {α β : Type*} [Finite α] [Fintype β]
    (b m : α → ℝ) (hm : Function.Injective m)
    (pair : β → α × α) (hpair : Function.Injective pair) (apex : β → ℝ × ℝ)
    (hsl : ∀ e, m (pair e).1 < m (pair e).2)
    (ht : ∀ e, 0 ≤ (apex e).2)
    (hl : ∀ e, lineAt b m (pair e).1 (apex e).2 = (apex e).1)
    (hr : ∀ e, lineAt b m (pair e).2 (apex e).2 = (apex e).1)
    (hadj : ∀ e a, lineAt b m a (apex e).2 = (apex e).1 →
      m a ≤ m (pair e).1 ∨ m (pair e).2 ≤ m a) :
    (Fintype.card (Option β) : ℕ∞) ≤ (regions (⋃ a, upwardRay b m a)ᶜ).encard := by
  let U := (⋃ a, upwardRay b m a)ᶜ
  let L (e : β) := (pair e).1
  let R (e : β) := (pair e).2
  have heq (e : β) : lineAt b m (L e) (apex e).2 = lineAt b m (R e) (apex e).2 :=
    (hl e).trans (hr e).symm
  have hex (e : β) : ∃ C ∈ regions U, apex e ∈ closure C ∧ C ⊆ gap b m (L e) (R e) :=
    exists_gap_region b m (L e) (R e) (hsl e) (apex e).1 (apex e).2 (ht e)
      (hl e) (hr e) (hadj e)
  choose C hC hA hG using hex
  have hweak (e : β) : closure (C e) ⊆ weakGap b m (L e) (R e) :=
    closure_minimal ((hG e).trans (gap_subset_weakGap b m (L e) (R e)))
      (weakGap_closed b m (L e) (R e))
  have hheight (e d : β) (h : C e = C d) : (apex d).2 ≤ (apex e).2 :=
    weakGap_height (hsl d) (heq d) (hweak d (h ▸ hA e))
  have hsame (e d : β) (h : C e = C d) : apex e = apex d := by
    have hy := le_antisymm (hheight d e h.symm) (hheight e d h)
    have ha := hweak d (h ▸ hA e)
    change lineAt b m (L d) (apex e).2 ≤ (apex e).1 ∧
      (apex e).1 ≤ lineAt b m (R d) (apex e).2 at ha
    rw [hy, hl d, hr d] at ha
    exact Prod.ext (le_antisymm ha.2 ha.1) hy
  have hle (e d : β) (h : C e = C d) :
      m (L d) ≤ m (L e) ∧ m (R e) ≤ m (R d) := by
    have ha := hsame e d h
    obtain ⟨q, hq⟩ : (C e).Nonempty := by
      obtain ⟨p, hp, he⟩ := hC e
      exact ⟨p, he.ge (mem_connectedComponentIn hp)⟩
    have hqe := hG e hq
    have hqd := hG d (h ▸ hq)
    have htq := gap_lt_height (hsl e) (heq e) hqe
    have hcmp (a d' : α) (ha' : lineAt b m a (apex e).2 = (apex e).1)
        (hd' : lineAt b m d' (apex e).2 = (apex e).1)
        (hline : lineAt b m a q.2 < lineAt b m d' q.2) : m a < m d' := by
      by_contra! hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 htq.le) (sub_nonpos.2 hn)
      dsimp [lineAt] at ha' hd' hline
      nlinarith
    have hld : lineAt b m (L d) (apex e).2 = (apex e).1 := by rw [ha, hl d]
    have hrd : lineAt b m (R d) (apex e).2 = (apex e).1 := by rw [ha, hr d]
    exact ⟨(hadj e (L d) hld).resolve_right
      (hcmp (L d) (R e) hld (hr e) (hqd.1.trans hqe.2)).not_ge,
      (hadj e (R d) hrd).resolve_left
        (hcmp (L e) (R d) (hl e) hrd (hqe.1.trans hqd.2)).not_ge⟩
  have hCi : Function.Injective C := by
    intro e d he
    have h₁ := hle e d he
    have h₂ := hle d e he.symm
    exact hpair (Prod.ext (hm (le_antisymm h₂.1 h₁.1)) (hm (le_antisymm h₁.2 h₂.2)))
  let q₀ : ℝ × ℝ := (0, -1)
  have hq₀ : q₀ ∈ U := by
    intro h
    obtain ⟨a, ha⟩ := mem_iUnion.1 h
    exact (by norm_num : ¬ 0 ≤ (-1 : ℝ)) ((mem_upwardRay b m a q₀).1 ha).1
  let C₀ := connectedComponentIn U q₀
  have hC₀ (e : β) : C₀ ≠ C e := by
    intro he
    have hmem : q₀ ∈ C₀ := mem_connectedComponentIn hq₀
    have hq := hG e (he ▸ hmem)
    have hlt := (ht e).trans_lt (gap_lt_height (hsl e) (heq e) hq)
    exact (by norm_num : ¬ 0 < (-1 : ℝ)) hlt
  let f : Option β → regions U :=
    fun e => e.elim ⟨C₀, region_at hq₀⟩ (fun a => ⟨C a, hC a⟩)
  have hf : Function.Injective f := by
    intro a d h
    have he := congrArg Subtype.val h
    rcases a with (_ | a) <;> rcases d with (_ | d)
    · rfl
    · exact (hC₀ d he).elim
    · exact (hC₀ a he.symm).elim
    · exact congrArg some (hCi he)
  rw [← ENat.card_eq_coe_fintype_card]
  exact ENat.card_le_card_of_injective hf


/-! ## An arrangement attaining the bound -/

private abbrev Arm (n : ℕ) := Fin n × Fin 3

private def armKey {n : ℕ} (a : Arm n) : ℕ := 3 * a.1.val + a.2.val

-- Slopes decrease along the ordered arms. The factor between slopes from different tips
-- rules out a third ray at a crossing, since the entire row of tips has length less than n.
private def armPower {n : ℕ} (a : Arm n) : ℝ := ((n : ℝ) + 1) ^ armKey a

private def armSlope {n : ℕ} (a : Arm n) : ℝ := -armPower a

private def armIntercept {n : ℕ} (a : Arm n) : ℝ := a.1.val

private theorem armKey_injective {n : ℕ} : Function.Injective (@armKey n) := by
  intro a b hab
  have ha := a.2.isLt
  have hb := b.2.isLt
  dsimp [armKey] at hab
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem armKey_lt_of_tip_lt {n : ℕ} {a b : Arm n} (hab : a.1 < b.1) :
    armKey a < armKey b := by
  have ha := a.2.isLt
  have hb := b.2.isLt
  change a.1.val < b.1.val at hab
  dsimp [armKey]
  omega

private theorem armBase_gt_one {n : ℕ} (a : Arm n) : 1 < (n : ℝ) + 1 := by
  have hn : 0 < n := (Nat.zero_le _).trans_lt a.1.isLt
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem armPower_pos {n : ℕ} (a : Arm n) : 0 < armPower a :=
  pow_pos ((by norm_num : (0 : ℝ) < 1).trans (armBase_gt_one a)) _

private theorem armSlope_injective {n : ℕ} : Function.Injective (@armSlope n) := by
  intro a b hab
  apply armKey_injective
  exact (pow_right_strictMono₀ (armBase_gt_one a)).injective (neg_injective hab)

private theorem armSlope_lt {n : ℕ} {a b : Arm n} (hab : armKey a < armKey b) :
    armSlope b < armSlope a :=
  neg_lt_neg (pow_lt_pow_right₀ (armBase_gt_one a) hab)

private theorem armSlope_le {n : ℕ} {a b : Arm n} (hab : armKey a ≤ armKey b) :
    armSlope b ≤ armSlope a :=
  neg_le_neg (pow_le_pow_right₀ (armBase_gt_one a).le hab)

private theorem armPower_domination {n : ℕ} {a b : Arm n} (hab : a.1 < b.1) :
    ((n : ℝ) + 1) * armPower a ≤ armPower b := by
  change ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ armKey a) ≤ ((n : ℝ) + 1) ^ armKey b
  rw [mul_comm, ← pow_succ]
  exact pow_le_pow_right₀ (armBase_gt_one a).le (armKey_lt_of_tip_lt hab)

private theorem no_three_tips_concurrent {n : ℕ} {a b c : Arm n}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) {t : ℝ} (ht : 0 < t)
    (h₁ : lineAt armIntercept armSlope a t = lineAt armIntercept armSlope b t)
    (h₂ : lineAt armIntercept armSlope b t = lineAt armIntercept armSlope c t) : False := by
  have hj : a.1.val + 1 ≤ b.1.val := hab
  have hj' : (a.1.val : ℝ) + 1 ≤ (b.1.val : ℝ) := by exact_mod_cast hj
  have hkn : (c.1.val : ℝ) < (n : ℝ) := by exact_mod_cast c.1.isLt
  have hi : (0 : ℝ) ≤ (b.1.val : ℝ) := Nat.cast_nonneg _
  dsimp [lineAt, armIntercept, armSlope] at h₁ h₂
  have hbt : 1 ≤ t * armPower b := by
    have hpos := mul_pos ht (armPower_pos a)
    linarith
  have hdom := armPower_domination hbc
  have hdiff : (n : ℝ) * armPower b ≤ armPower c - armPower b := by linarith
  have hbound : (n : ℝ) ≤ (c.1.val : ℝ) - (b.1.val : ℝ) := calc
    (n : ℝ) = (n : ℝ) * 1 := by ring
    _ ≤ (n : ℝ) * (t * armPower b) := mul_le_mul_of_nonneg_left hbt (Nat.cast_nonneg _)
    _ = t * ((n : ℝ) * armPower b) := by ring
    _ ≤ t * (armPower c - armPower b) := mul_le_mul_of_nonneg_left hdiff ht.le
    _ = (c.1.val : ℝ) - (b.1.val : ℝ) := by linarith
  linarith

private theorem eq_arm_of_same_tip_hit {n : ℕ} {a b : Arm n} (hab : a.1 = b.1)
    {t : ℝ} (ht : 0 < t)
    (h : lineAt armIntercept armSlope a t = lineAt armIntercept armSlope b t) : a = b := by
  have he : armIntercept a = armIntercept b := by simp only [armIntercept, hab]
  have hmul : t * armSlope a = t * armSlope b := by
    dsimp [lineAt] at h
    rw [he] at h
    exact add_left_cancel h
  exact armSlope_injective ((mul_left_cancel₀ ht.ne') hmul)

private theorem crossing_only_two_arms {n : ℕ} {a b d : Arm n}
    (hab : a.1 < b.1) {x t : ℝ} (ht : 0 < t)
    (ha : lineAt armIntercept armSlope a t = x)
    (hb : lineAt armIntercept armSlope b t = x)
    (hd : lineAt armIntercept armSlope d t = x) : d = a ∨ d = b := by
  rcases lt_trichotomy d.1 a.1 with hda | hda | had
  · exact (no_three_tips_concurrent hda hab ht (hd.trans ha.symm) (ha.trans hb.symm)).elim
  · exact Or.inl (eq_arm_of_same_tip_hit hda ht (hd.trans ha.symm))
  · rcases lt_trichotomy d.1 b.1 with hdb | hdb | hbd
    · exact (no_three_tips_concurrent had hdb ht (ha.trans hd.symm) (hd.trans hb.symm)).elim
    · exact Or.inr (eq_arm_of_same_tip_hit hdb ht (hd.trans hb.symm))
    · exact (no_three_tips_concurrent hab hbd ht (ha.trans hb.symm) (hb.trans hd.symm)).elim

private abbrev GapIndex (n : ℕ) :=
  (Fin n × Fin 2) ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Fin 3 × Fin 3)

private def gapPair {n : ℕ} : GapIndex n → Arm n × Arm n
  | .inl (i, j) => ((i, j.succ), (i, j.castSucc))
  | .inr (p, j, k) => ((p.val.2, k), (p.val.1, j))

private theorem gapPair_injective {n : ℕ} : Function.Injective (@gapPair n) := by
  rintro (⟨i, j⟩ | ⟨p, j, k⟩) (⟨i', j'⟩ | ⟨p', j', k'⟩) he
  · have hi : i = i' := congrArg (fun a : Arm n × Arm n => a.1.1) he
    have hj : j = j' := Fin.ext (congrArg (fun a : Arm n × Arm n => a.2.2.val) he)
    cases hi
    cases hj
    rfl
  · have hi : i = p'.val.2 := congrArg (fun a : Arm n × Arm n => a.1.1) he
    have hi' : i = p'.val.1 := congrArg (fun a : Arm n × Arm n => a.2.1) he
    exact (ne_of_lt p'.2 (hi'.symm.trans hi)).elim
  · have hi : p.val.2 = i' := congrArg (fun a : Arm n × Arm n => a.1.1) he
    have hi' : p.val.1 = i' := congrArg (fun a : Arm n × Arm n => a.2.1) he
    exact (ne_of_lt p.2 (hi'.trans hi.symm)).elim
  · have hp : p = p' := Subtype.ext (Prod.ext
      (congrArg (fun a : Arm n × Arm n => a.2.1) he)
      (congrArg (fun a : Arm n × Arm n => a.1.1) he))
    have hj : j = j' := congrArg (fun a : Arm n × Arm n => a.2.2) he
    have hk : k = k' := congrArg (fun a : Arm n × Arm n => a.1.2) he
    cases hp
    cases hj
    cases hk
    rfl

private theorem gapPair_geometry {n : ℕ} (e : GapIndex n) :
    ∃ p : ℝ × ℝ, armSlope (gapPair e).1 < armSlope (gapPair e).2 ∧ 0 ≤ p.2 ∧
      lineAt armIntercept armSlope (gapPair e).1 p.2 = p.1 ∧
      lineAt armIntercept armSlope (gapPair e).2 p.2 = p.1 ∧
      ∀ d : Arm n, lineAt armIntercept armSlope d p.2 = p.1 →
        armSlope d ≤ armSlope (gapPair e).1 ∨ armSlope (gapPair e).2 ≤ armSlope d := by
  rcases e with (⟨i, j⟩ | ⟨p, j, k⟩)
  · have hkey : armKey (i, j.castSucc) < armKey (i, j.succ) := by
      simp [armKey]
    refine ⟨(i.val, 0), armSlope_lt hkey, le_rfl, ?_, ?_, ?_⟩
    · simp [gapPair, lineAt, armIntercept]
    · simp [gapPair, lineAt, armIntercept]
    · rintro ⟨d, l⟩ hd
      have hdi : d = i := by
        change lineAt armIntercept armSlope (d, l) 0 = (i.val : ℝ) at hd
        simp only [lineAt, armIntercept, zero_mul, add_zero] at hd
        exact Fin.ext (by exact_mod_cast hd)
      subst d
      have h : j.val + 1 ≤ l.val ∨ l.val ≤ j.val := by omega
      rcases h with h | h
      · exact Or.inl (armSlope_le (show armKey (i, j.succ) ≤ armKey (i, l) by
          simpa [armKey] using h))
      · exact Or.inr (armSlope_le (show armKey (i, l) ≤ armKey (i, j.castSucc) by
          simpa [armKey] using h))
  · let a : Arm n := (p.val.1, j)
    let b : Arm n := (p.val.2, k)
    have hab : a.1 < b.1 := p.2
    have hm : armSlope b < armSlope a := armSlope_lt (armKey_lt_of_tip_lt hab)
    have hb : armIntercept a < armIntercept b := by
      change (a.1.val : ℝ) < (b.1.val : ℝ)
      exact_mod_cast hab
    let t := (armIntercept b - armIntercept a) / (armSlope a - armSlope b)
    have ht : 0 < t := div_pos (sub_pos.2 hb) (sub_pos.2 hm)
    let x := lineAt armIntercept armSlope a t
    have hx : lineAt armIntercept armSlope b t = x := by
      have he : t * (armSlope a - armSlope b) = armIntercept b - armIntercept a :=
        div_mul_cancel₀ _ (sub_pos.2 hm).ne'
      dsimp [x, lineAt]
      nlinarith
    refine ⟨(x, t), hm, ht.le, hx, rfl, ?_⟩
    intro d hd
    rcases crossing_only_two_arms hab ht rfl hx hd with rfl | rfl
    · exact Or.inr le_rfl
    · exact Or.inl le_rfl

private theorem upward_fans_bound {n : ℕ} :
    (↑(1 + 2 * n + 9 * n.choose 2 : ℕ) : ℕ∞) ≤
      (regions (⋃ a : Arm n, upwardRay armIntercept armSlope a)ᶜ).encard := by
  classical
  choose apex hm ht hl hr hadj using (fun e : GapIndex n => gapPair_geometry e)
  have h := gaps_lower_bound armIntercept armSlope armSlope_injective gapPair gapPair_injective
    apex hm ht hl hr hadj
  refine le_trans ?_ h
  rw [Nat.cast_le]
  have hpair : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hpair]
  omega

end isGreatest_planeRegionCount_threeArmedV

open isGreatest_planeRegionCount_threeArmedV in
/-- **Maximum region count for three-armed V's.** A long-legged three-armed V is the union of
three rays $\{c + s u_j : s \ge 0\}$, $j = 1, 2, 3$, from a common tip $c \in \mathbb{R}^2$, with
nonzero direction vectors $u_1, u_2, u_3 \in \mathbb{R}^2$ in arbitrary directions. For every
natural number $n$, the largest number of regions into which the union of $n$ long-legged
three-armed V's can divide the plane is $(9n^2 - 5n + 2)/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-armed V*. -/
public theorem isGreatest_planeRegionCount_threeArmedV (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (c : Fin n → ℝ × ℝ) (u : Fin n → Fin 3 → ℝ × ℝ),
      (∀ i j, u i j ≠ 0) ∧
        N = planeRegionCount (⋃ i, ⋃ j, (fun s : ℝ => c i + s • u i j) '' Set.Ici 0)}
      ((9 * n ^ 2 - 5 * n + 2) / 2) := by
  rw [← max_count_nat]
  constructor
  · let c (i : Fin n) : ℝ × ℝ := (i.val, 0)
    let u (i : Fin n) (j : Fin 3) : ℝ × ℝ := (armSlope (i, j), 1)
    have hu (i j) : u i j ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    refine ⟨c, u, hu, ?_⟩
    have hupper := all_fans_bound c u hu
    have hlower : (↑(1 + 2 * n + 9 * n.choose 2 : ℕ) : ℕ∞) ≤
        (regions (⋃ i, ⋃ j, ray (c i) (u i j))ᶜ).encard := by
      simpa only [iUnion_prod', upwardRay, armIntercept, c, u] using (upward_fans_bound (n := n))
    simpa only [planeRegionCount, regions, ray, Set.ncard, ENat.toNat_natCast] using
      congrArg ENat.toNat (le_antisymm hlower hupper)
  · rintro N ⟨c, u, hu, rfl⟩
    have h := all_fans_bound c u hu
    have htop : (↑(1 + 2 * n + 9 * n.choose 2 : ℕ) : ℕ∞) < ⊤ := ENat.natCast_lt_top _
    have hf := encard_lt_top_iff.1 (h.trans_lt htop)
    rw [← hf.cast_ncard_eq, Nat.cast_le] at h
    exact h

end MetaMathlibExt
