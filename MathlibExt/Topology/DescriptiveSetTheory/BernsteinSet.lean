/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Bernstein set existence
-/

noncomputable section

open Set Topology
open Cardinal

namespace MathlibExt.Topology.DescriptiveSetTheory.BernsteinSet

private theorem card_uncountable_isClosed (F : Set ℝ) (hF : IsClosed F) (hc : ¬F.Countable) :
    #(↥F) = Cardinal.continuum := by
  have hstep : #(ℕ → Bool) = (2 : Cardinal) ^ ℵ₀ := by rw [← power_def, mk_bool, mk_nat]
  have hcont : #(ℕ → Bool) = Cardinal.continuum := by
    rwa [show (2 : Cardinal) ^ ℵ₀ = Cardinal.continuum from rfl] at hstep
  obtain ⟨f, hfR, _, hfinj⟩ := hF.exists_nat_bool_injection_of_not_countable hc
  have hle1 : #(ℕ → Bool) ≤ #(↥F) := by
    apply mk_le_of_injective (f := fun x : (ℕ → Bool) => (⟨f x, hfR (Set.mem_range_self x)⟩ : ↥F))
    intro a b hab
    have := congrArg Subtype.val hab
    exact hfinj this
  have hle2 : #(↥F) ≤ #(ℝ) := by
    apply mk_le_of_injective (f := fun x : ↥F => (x.val : ℝ))
    intro a b hab
    exact Subtype.ext hab
  rw [mk_real] at hle2
  rw [← hcont] at hle2 ⊢
  exact le_antisymm hle2 hle1

private theorem card_closed_uncountable_le :
    #(↥{F : Set ℝ | IsClosed F ∧ ¬F.Countable}) ≤ Cardinal.continuum := by
  classical
  let B := TopologicalSpace.countableBasis ℝ
  have hBasis := TopologicalSpace.isBasis_countableBasis ℝ
  have hBcount := TopologicalSpace.countable_countableBasis ℝ
  have hdecode : ∀ (U : Set ℝ), IsOpen U → U = ⋃₀ {v ∈ B | v ⊆ U} := by
    intro U hU
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨v, hvB, hxv, hvU⟩ := hBasis.exists_subset_of_mem_open hx hU
      exact mem_sUnion.mpr ⟨v, ⟨hvB, hvU⟩, hxv⟩
    · rw [sUnion_subset_iff]
      intro t ht
      exact ht.2
  let code : ↥{F : Set ℝ | IsClosed F ∧ ¬F.Countable} → Set ↥B :=
    fun F => {b : ↥B | (b.val : Set ℝ) ⊆ (F.val)ᶜ}
  have hcode_inj : Function.Injective code := by
    intro F G hFG
    have hFcompl : (F.val)ᶜ = ⋃₀ ((fun b : ↥B => (b.val : Set ℝ)) '' code F) := by
      have hU := hdecode (F.val)ᶜ (by have h := F.property.1; exact IsClosed.isOpen_compl)
      rw [hU]
      congr 1
      ext v
      constructor
      · rintro ⟨hvB, hvU⟩
        exact ⟨⟨v, hvB⟩, hvU, rfl⟩
      · rintro ⟨⟨w, hwB⟩, hwU, rfl⟩
        exact ⟨hwB, hwU⟩
    have hGcompl : (G.val)ᶜ = ⋃₀ ((fun b : ↥B => (b.val : Set ℝ)) '' code G) := by
      have hU := hdecode (G.val)ᶜ (by have h := G.property.1; exact IsClosed.isOpen_compl)
      rw [hU]
      congr 1
      ext v
      constructor
      · rintro ⟨hvB, hvU⟩
        exact ⟨⟨v, hvB⟩, hvU, rfl⟩
      · rintro ⟨⟨w, hwB⟩, hwU, rfl⟩
        exact ⟨hwB, hwU⟩
    rw [hFG] at hFcompl
    have hval : F.val = G.val := by
      have this : (F.val)ᶜ = (G.val)ᶜ := hFcompl.trans hGcompl.symm
      have e1 : F.val = (F.val)ᶜᶜ := (compl_compl _).symm
      have e2 : G.val = (G.val)ᶜᶜ := (compl_compl _).symm
      rw [e1, e2, this]
    exact Subtype.ext hval
  have hle : #(↥{F : Set ℝ | IsClosed F ∧ ¬F.Countable}) ≤ #(Set ↥B) :=
    mk_le_of_injective hcode_inj
  have hbase : #(↥B) ≤ ℵ₀ :=
    mk_le_aleph0_iff.mpr (countable_coe_iff.mpr hBcount)
  have hset : #(Set ↥B) = 2 ^ #(↥B) := mk_set
  have hpow : (2 : Cardinal) ^ #(↥B) ≤ 2 ^ ℵ₀ :=
    power_le_power_left (by norm_num) hbase
  have hfin : (2 : Cardinal) ^ ℵ₀ = Cardinal.continuum := rfl
  calc #(↥{F : Set ℝ | IsClosed F ∧ ¬F.Countable})
      ≤ #(Set ↥B) := hle
    _ = 2 ^ #(↥B) := hset
    _ ≤ 2 ^ ℵ₀ := hpow
    _ = Cardinal.continuum := hfin

-- fresh point outside a small set
private theorem exists_fresh (S F : Set ℝ) (h : #↥S < #↥F) : ∃ x, x ∈ F ∧ x ∉ S := by
  by_contra hc
  have hsub : F ⊆ S := by
    intro x hx
    by_contra hxS
    exact hc ⟨x, hx, hxS⟩
  have hle : #↥F ≤ #↥S := by
    apply mk_le_of_injective (f := fun z : ↥F => (⟨z.val, hsub z.property⟩ : ↥S))
    intro a b hab
    have h2 := congrArg Subtype.val hab
    exact Subtype.ext h2
  exact lt_irrefl _ (lt_of_le_of_lt hle h)

/--
**Existence of a Bernstein set.** There is a set $B \subseteq \mathbb{R}$ such that every closed,
uncountable set $F \subseteq \mathbb{R}$ meets both $B$ and its complement $\mathbb{R} \setminus B$.

Source: F. Bernstein (construction); J. C. Oxtoby, Measure and Category, 2nd ed. (1980); A. S.
Kechris, Classical Descriptive Set Theory, Thm 8.24 (1995).
Proves `Wanted` entry `bernstein_set_exists`.
-/
theorem bernstein_set_exists :
    ∃ (B : Set ℝ), ∀ (F : Set ℝ), IsClosed F → ¬F.Countable →
      (B ∩ F).Nonempty ∧ (Set.compl B ∩ F).Nonempty := by
  classical
  set I : Type := ↥{F : Set ℝ | IsClosed F ∧ ¬F.Countable} with hI
  set κ : Cardinal := #I with hκ
  have hκle : κ ≤ Cardinal.continuum := card_closed_uncountable_le
  -- index type: initial ordinal of κ, as a small type
  set idx : Type := κ.ord.ToType with hidx
  have hTo : #idx = κ := mk_ord_toType κ
  obtain ⟨e⟩ := Cardinal.eq.mp (rfl.trans hTo.symm : #I = #idx)
  have htype : (#idx).ord = Ordinal.type (fun x1 x2 : idx => x1 < x2) := by
    rw [hTo]
    exact (Ordinal.type_toType _).symm
  have hseg : ∀ (b : idx), #(↥(Set.Iio b)) < κ := by
    intro b
    have h := mk_Iio_lt b htype
    rwa [hTo] at h
  -- the closed set indexed by b
  let F_of : idx → Set ℝ := fun b => (e.symm b).val
  have hFc : ∀ b, IsClosed (F_of b) := fun b => (e.symm b).property.1
  have hFu : ∀ b, ¬(F_of b).Countable := fun b => (e.symm b).property.2
  have hFcard : ∀ b, #(↥(F_of b)) = Cardinal.continuum :=
    fun b => card_uncountable_isClosed _ (hFc b) (hFu b)
  -- previous picks at stage b
  have hSbound : ∀ (b : idx) (p : ∀ a, a < b → ℝ × ℝ),
      #↥(Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).1) ∪
        Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).2)) <
        Cardinal.continuum := by
    intro b p
    have hD : #(↥(Set.Iio b)) < Cardinal.continuum :=
      lt_of_lt_of_le (hseg b) hκle
    have h1 : #↥(Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).1))
        ≤ #(↥(Set.Iio b)) := mk_range_le
    have h2 : #↥(Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).2))
        ≤ #(↥(Set.Iio b)) := mk_range_le
    have hunion : #↥(Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).1) ∪
          Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).2))
        ≤ #(↥(Set.Iio b)) + #(↥(Set.Iio b)) :=
      le_trans (mk_union_le _ _) (add_le_add h1 h2)
    exact lt_of_le_of_lt hunion (add_lt_of_lt aleph0_le_continuum hD hD)
  let S : ∀ (b : idx), (∀ a, a < b → ℝ × ℝ) → Set ℝ :=
    fun b p => Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).1) ∪
      Set.range (fun d : ↥(Set.Iio b) => (p d.val (Set.mem_Iio.mp d.property)).2)
  have hfresh : ∀ (b : idx) (p : ∀ a, a < b → ℝ × ℝ),
      Nonempty {q : ℝ × ℝ // q.1 ∈ F_of b ∧ q.2 ∈ F_of b ∧ q.1 ≠ q.2 ∧ q.1 ∉ S b p ∧
        q.2 ∉ insert q.1 (S b p)} := by
    intro b p
    have hSb : #↥(S b p) < #↥(F_of b) := by
      rw [hFcard b]
      exact hSbound b p
    obtain ⟨x, hxF, hxS⟩ := exists_fresh (S b p) (F_of b) hSb
    have hS'x : #↥(insert x (S b p)) < #↥(F_of b) := by
      rw [hFcard b]
      have h2 : #↥(insert x (S b p)) = #↥(S b p) + 1 := mk_insert hxS
      rw [h2]
      have h1lt : (1 : Cardinal) < Cardinal.continuum := by
        exact_mod_cast nat_lt_continuum 1
      exact add_lt_of_lt aleph0_le_continuum (hSbound b p) h1lt
    obtain ⟨y, hyF, hyS⟩ := exists_fresh (insert x (S b p)) (F_of b) hS'x
    have hxy : x ≠ y := by
      rintro rfl
      exact hyS (Set.mem_insert _ _)
    exact ⟨⟨(x, y), hxF, hyF, hxy, hxS, hyS⟩⟩
  have hwf : WellFounded (fun a b : idx => a < b) := wellFounded_lt
  let step : ∀ (b : idx), (∀ a, a < b → ℝ × ℝ) → ℝ × ℝ :=
    fun b p => (Classical.choice (hfresh b p)).val
  have step_def : ∀ (b : idx) (p : ∀ a, a < b → ℝ × ℝ),
      step b p = (Classical.choice (hfresh b p)).val := fun b p => rfl
  have good : ∀ b, (hwf.fix step b).1 ∈ F_of b ∧ (hwf.fix step b).2 ∈ F_of b ∧
      (hwf.fix step b).1 ≠ (hwf.fix step b).2 ∧
      (hwf.fix step b).1 ∉ S b (fun a _ => hwf.fix step a) ∧
      (hwf.fix step b).2 ∉ insert (hwf.fix step b).1 (S b (fun a _ => hwf.fix step a)) := by
    intro b
    rw [WellFounded.fix_eq hwf step b]
    simp only [step_def]
    exact (Classical.choice (hfresh b (fun a _ => hwf.fix step a))).property
  -- the Bernstein set: first coordinates of all picks
  let Bset : Set ℝ := Set.range (fun b : idx => (hwf.fix step b).1)
  refine ⟨Bset, ?_⟩
  intro F hF hc
  set b0 : idx := e ⟨F, hF, hc⟩ with hb0
  have hFb : F_of b0 = F := by
    change (e.symm (e (⟨F, hF, hc⟩ : I))).val = F
    rw [Equiv.symm_apply_apply]
  obtain ⟨hx_mem, hy_mem, hxy, hxbS, hybS⟩ := good b0
  have hxB : (hwf.fix step b0).1 ∈ Bset := ⟨b0, rfl⟩
  have hxF' : (hwf.fix step b0).1 ∈ F := by
    rw [← hFb]
    exact hx_mem
  have hyF' : (hwf.fix step b0).2 ∈ F := by
    rw [← hFb]
    exact hy_mem
  have hyB : (hwf.fix step b0).2 ∈ Bsetᶜ := by
    rw [mem_compl_iff]
    rintro ⟨c, hc⟩
    change (hwf.fix step c).1 = (hwf.fix step b0).2 at hc
    rcases lt_trichotomy c b0 with hcb | rfl | hbc
    · have hmem1 : (hwf.fix step b0).2 ∈ S b0 (fun a _ => hwf.fix step a) := by
        apply Or.inl
        exact ⟨⟨c, hcb⟩, hc⟩
      exact hybS (mem_insert_iff.mpr (Or.inr hmem1))
    · exact hxy hc
    · obtain ⟨_, _, _, hxcS, _⟩ := good c
      rw [hc] at hxcS
      have hmem2 : (hwf.fix step b0).2 ∈ S c (fun a _ => hwf.fix step a) := by
        apply Or.inr
        exact ⟨⟨b0, hbc⟩, rfl⟩
      exact hxcS hmem2
  exact ⟨⟨_, hxB, hxF'⟩, ⟨_, hyB, hyF'⟩⟩
end MathlibExt.Topology.DescriptiveSetTheory.BernsteinSet
