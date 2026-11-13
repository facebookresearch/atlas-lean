/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.Order
public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions

@[expose] public section

namespace MetaMathlibExt.CameronOrderGroupWanted

private noncomputable def transPerm (c : ℚ) : Equiv.Perm ℚ where
  toFun x := x + c
  invFun x := x - c
  left_inv x := by simp
  right_inv x := by simp

private theorem transPerm_mem (c : ℚ) : transPerm c ∈ MetaMathlibExt.orderAutSubgroup ℚ := by
  intro a b
  simp [transPerm]

private noncomputable def scaleFun (M c x : ℚ) : ℚ :=
  if x ≤ M then x else M + (x - M) * c

private noncomputable def scaleInvFun (M c x : ℚ) : ℚ :=
  if x ≤ M then x else M + (x - M) / c

private theorem scale_left_inv (M c : ℚ) (hc : 0 < c) (x : ℚ) :
    scaleInvFun M c (scaleFun M c x) = x := by
  by_cases h : x ≤ M
  · simp [scaleFun, scaleInvFun, h]
  · have hne : c ≠ 0 := ne_of_gt hc
    have hxM : M < x := lt_of_not_ge h
    have hMlt : M < M + (x - M) * c := by
      have hpos : 0 < (x - M) * c := mul_pos (by linarith) hc
      linarith
    have hle : ¬ (M + (x - M) * c ≤ M) := by linarith
    simp [scaleFun, scaleInvFun, h, hle]
    field_simp
    ring

private theorem scale_right_inv (M c : ℚ) (hc : 0 < c) (x : ℚ) :
    scaleFun M c (scaleInvFun M c x) = x := by
  by_cases h : x ≤ M
  · simp [scaleFun, scaleInvFun, h]
  · have hne : c ≠ 0 := ne_of_gt hc
    have hxM : M < x := lt_of_not_ge h
    have hMlt : M < M + (x - M) / c := by
      have hpos : 0 < (x - M) / c := by positivity
      linarith
    have hle : ¬ (M + (x - M) / c ≤ M) := by linarith
    simp [scaleFun, scaleInvFun, h, hle]
    field_simp
    ring

private theorem scale_strictMono (M c : ℚ) (hc : 0 < c) : StrictMono (scaleFun M c) := by
  intro a b hab
  by_cases ha : a ≤ M
  · by_cases hb : b ≤ M
    · simp [scaleFun, ha, hb, hab]
    · have hbM : M < b := lt_of_not_ge hb
      have ha_eq : scaleFun M c a = a := by simp [scaleFun, ha]
      have hb_eq : scaleFun M c b = M + (b - M) * c := by simp [scaleFun, hb]
      rw [ha_eq, hb_eq]
      have hpos : 0 < (b - M) * c := mul_pos (by linarith) hc
      linarith
  · by_cases hb : b ≤ M
    · exfalso
      exact ha (le_trans (le_of_lt hab) hb)
    · simp only [scaleFun, ha, ↓reduceIte, hb, add_lt_add_iff_left]
      have h1 : (a - M) * c < (b - M) * c := by
        apply mul_lt_mul_of_pos_right _ hc
        linarith
      linarith

private noncomputable def scalePerm (M c : ℚ) (hc : 0 < c) : Equiv.Perm ℚ where
  toFun := scaleFun M c
  invFun := scaleInvFun M c
  left_inv := scale_left_inv M c hc
  right_inv := scale_right_inv M c hc

private theorem scalePerm_mem (M c : ℚ) (hc : 0 < c) : scalePerm M c hc ∈
    MetaMathlibExt.orderAutSubgroup ℚ := by
  intro a b
  constructor
  · intro h
    exact scale_strictMono M c hc h
  · intro h
    have h' : scaleFun M c a < scaleFun M c b := h
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hlt' : scaleFun M c b < scaleFun M c a :=
        scale_strictMono M c hc hlt
      linarith
    · have heq' : scaleFun M c b = scaleFun M c a := by rw [heq]
      linarith

private theorem scalePerm_fix_of_le (M c : ℚ) (hc : 0 < c) (x : ℚ) (h : x ≤ M) :
    scalePerm M c hc x = x := by
  simp [scalePerm, scaleFun, h]

private theorem scalePerm_of_gt (M c : ℚ) (hc : 0 < c) (x : ℚ) (h : ¬ x ≤ M) :
    scalePerm M c hc x = M + (x - M) * c := by
  simp [scalePerm, scaleFun, h]

private theorem exists_perm_image_eq : ∀ (n : ℕ) (sx sy : Finset ℚ),
    sx.card = n → sy.card = n →
    ∃ σ ∈ MetaMathlibExt.orderAutSubgroup ℚ, sx.image (⇑σ) = sy := by
  intro n
  induction n with
  | zero =>
    intro sx sy hsx hsy
    have hsx' : sx = ∅ := Finset.card_eq_zero.mp hsx
    have hsy' : sy = ∅ := Finset.card_eq_zero.mp hsy
    exact ⟨1, (MetaMathlibExt.orderAutSubgroup ℚ).one_mem, by simp [hsx', hsy']⟩
  | succ n ih =>
    intro sx sy hsx hsy
    have hsx_ne : sx.Nonempty := by
      rw [← Finset.card_pos]
      omega
    have hsy_ne : sy.Nonempty := by
      rw [← Finset.card_pos]
      omega
    set smax := sx.max' hsx_ne with hsmax_def
    set tmax := sy.max' hsy_ne with htmax_def
    have hsmax_mem : smax ∈ sx := Finset.max'_mem sx hsx_ne
    have htmax_mem : tmax ∈ sy := Finset.max'_mem sy hsy_ne
    set sx' := sx.erase smax with hsx'_def
    set sy' := sy.erase tmax with hsy'_def
    have hsx'_card : sx'.card = n := by
      rw [hsx'_def, Finset.card_erase_of_mem hsmax_mem, hsx]
      omega
    have hsy'_card : sy'.card = n := by
      rw [hsy'_def, Finset.card_erase_of_mem htmax_mem, hsy]
      omega
    obtain ⟨τ, hτmem, hτmap⟩ := ih sx' sy' hsx'_card hsy'_card
    set s' := τ smax with hs'_def
    have hτmono : ∀ a b : ℚ, a < b ↔ τ a < τ b := hτmem
    have hsy'_lt_s' : ∀ y ∈ sy', y < s' := by
      intro y hy
      have hmem : y ∈ sy' := hy
      rw [← hτmap] at hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨s, hs_mem, hs_eq⟩ := hmem
      have hs_in_sx : s ∈ sx := by
        have h : s ∈ sx' := hs_mem
        simp only [hsx'_def, Finset.mem_erase, ne_eq] at h
        exact h.2
      have hle : s ≤ smax := Finset.le_max' sx s hs_in_sx
      have hne : s ≠ smax := by
        intro hcon
        have h : s ∈ sx' := hs_mem
        simp [hsx'_def, Finset.mem_erase, hcon] at h
      have hs_lt : s < smax := lt_of_le_of_ne hle hne
      have hlt : τ s < τ smax := (hτmono s smax).mp hs_lt
      rw [← hs_eq]
      exact hlt
    have hsy'_lt_tmax : ∀ y ∈ sy', y < tmax := by
      intro y hy
      have hy_in_sy : y ∈ sy := by
        have h : y ∈ sy' := hy
        simp only [hsy'_def, Finset.mem_erase, ne_eq] at h
        exact h.2
      have hle : y ≤ tmax := Finset.le_max' sy y hy_in_sy
      have hne : y ≠ tmax := by
        intro hcon
        have h : y ∈ sy' := hy
        simp [hsy'_def, Finset.mem_erase, hcon] at h
      exact lt_of_le_of_ne hle hne
    by_cases hn : n = 0
    · subst hn
      have hsx'_empty : sx' = ∅ := Finset.card_eq_zero.mp hsx'_card
      have hsy'_empty : sy' = ∅ := Finset.card_eq_zero.mp hsy'_card
      have hsx_eq : sx = {smax} := by
        have h : insert smax sx' = sx := Finset.insert_erase hsmax_mem
        rw [hsx'_empty] at h
        simpa using h.symm
      have hsy_eq : sy = {tmax} := by
        have h : insert tmax sy' = sy := Finset.insert_erase htmax_mem
        rw [hsy'_empty] at h
        simpa using h.symm
      refine ⟨transPerm (tmax - smax), transPerm_mem _, ?_⟩
      rw [hsx_eq, hsy_eq, Finset.image_singleton]
      congr 1
      show transPerm (tmax - smax) smax = tmax
      simp [transPerm]
    · have hsy'_ne : sy'.Nonempty := by
        rw [← Finset.card_pos]
        omega
      set M := sy'.max' hsy'_ne with hM_def
      have hM_mem : M ∈ sy' := Finset.max'_mem sy' hsy'_ne
      have hM_lt_s' : M < s' := hsy'_lt_s' M hM_mem
      have hM_lt_tmax : M < tmax := hsy'_lt_tmax M hM_mem
      set c := (tmax - M) / (s' - M) with hc_def
      have hc_pos : 0 < c := div_pos (by linarith) (by linarith)
      set ρ := scalePerm M c hc_pos with hρ_def
      have hρmem : ρ ∈ MetaMathlibExt.orderAutSubgroup ℚ := scalePerm_mem M c hc_pos
      have hρ_fix : ∀ y ∈ sy', ρ y = y := by
        intro y hy
        apply scalePerm_fix_of_le
        exact Finset.le_max' sy' y hy
      have hs'M : s' - M ≠ 0 := ne_of_gt (by linarith)
      have hρ_s' : ρ s' = tmax := by
        have hnotle : ¬ s' ≤ M := by linarith
        rw [scalePerm_of_gt M c hc_pos s' hnotle, hc_def]
        field_simp
        ring
      refine ⟨ρ * τ, (MetaMathlibExt.orderAutSubgroup ℚ).mul_mem hρmem hτmem, ?_⟩
      have hsx_eq : insert smax sx' = sx := Finset.insert_erase hsmax_mem
      have hsy_eq : insert tmax sy' = sy := Finset.insert_erase htmax_mem
      have hσ_smax : (ρ * τ) smax = tmax := by
        rw [Equiv.Perm.mul_apply, ← hs'_def]
        exact hρ_s'
      have hmap_sx' : sx'.image (⇑(ρ * τ)) = sy' := by
        have h1 : sx'.image (⇑(ρ * τ)) = sx'.image (⇑τ) := by
          apply Finset.ext
          intro z
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨s, hs, hse⟩
            have hτs_mem : τ s ∈ sy' := by
              have hmem : τ s ∈ sx'.image (⇑τ) := by
                rw [Finset.mem_image]
                exact ⟨s, hs, rfl⟩
              rw [hτmap] at hmem
              exact hmem
            have hσs_eq : (ρ * τ) s = τ s := by
              rw [Equiv.Perm.mul_apply]
              exact hρ_fix (τ s) hτs_mem
            exact ⟨s, hs, by rw [← hse, hσs_eq]⟩
          · rintro ⟨s, hs, hse⟩
            have hτs_mem : τ s ∈ sy' := by
              have hmem : τ s ∈ sx'.image (⇑τ) := by
                rw [Finset.mem_image]
                exact ⟨s, hs, rfl⟩
              rw [hτmap] at hmem
              exact hmem
            have hσs_eq : (ρ * τ) s = τ s := by
              rw [Equiv.Perm.mul_apply]
              exact hρ_fix (τ s) hτs_mem
            exact ⟨s, hs, by rw [hσs_eq, hse]⟩
        rw [h1, hτmap]
      calc sx.image (⇑(ρ * τ))
          = (insert smax sx').image (⇑(ρ * τ)) := by rw [hsx_eq]
        _ = insert ((ρ * τ) smax) (sx'.image (⇑(ρ * τ))) := by
            rw [Finset.image_insert]
        _ = insert tmax sy' := by rw [hσ_smax, hmap_sx']
        _ = sy := hsy_eq

open scoped Pointwise in
private theorem orderAut_isHighlyHomogeneous :
    MetaMathlibExt.IsHighlyHomogeneous (MetaMathlibExt.orderAutSubgroup ℚ) := by
  intro k
  constructor
  intro x y
  have hx : (x.val : Finset ℚ).card = k := x.prop
  have hy : (y.val : Finset ℚ).card = k := y.prop
  obtain ⟨σ, hσmem, hσmap⟩ := exists_perm_image_eq k x.val y.val hx hy
  refine ⟨⟨σ, hσmem⟩, ?_⟩
  apply Subtype.ext
  change (⟨σ, hσmem⟩ : ↥(MetaMathlibExt.orderAutSubgroup ℚ)) • (x.val : Finset ℚ) = y.val
  rw [Finset.smul_finset_def]
  have hrfl : (x.val.image fun a => (⟨σ, hσmem⟩ : ↥(MetaMathlibExt.orderAutSubgroup ℚ)) • a) =
      x.val.image (⇑σ) := rfl
  rw [hrfl, hσmap]

/--
**The order-automorphism group of the rationals is closed and highly homogeneous.** The group of
order automorphisms of $\mathbb{Q}$, that is, of the permutations $\sigma$ of $\mathbb{Q}$ such
that $a < b$ if and only if $\sigma(a) < \sigma(b)$ for all $a, b \in \mathbb{Q}$, is closed in
the topology of pointwise convergence on the permutations of $\mathbb{Q}$, where $\mathbb{Q}$
carries the discrete topology, and it is highly homogeneous: for every natural number $k$ it has
a single orbit on the $k$-element subsets of $\mathbb{Q}$.

Source: Daniele A. Gewurz and Francesca Merola, "Sequences realized as Parker vectors of
oligomorphic permutation groups," JIS 6,
https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex, lines 331-359,
source SHA-256 aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21,
cited-span SHA-256 81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4.
Primary source, cited there: Peter J. Cameron, "Transitivity of permutation groups on unordered
sets," *Mathematische Zeitschrift* 148(2) (1976), 127--139, DOI 10.1007/BF01214702.

Proves `Wanted` entry `orderAutSubgroup_isClosed_and_highlyHomogeneous`.
-/
theorem orderAutSubgroup_isClosed_and_highlyHomogeneous :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
      ↑(MetaMathlibExt.orderAutSubgroup ℚ) ∧
      MetaMathlibExt.IsHighlyHomogeneous (MetaMathlibExt.orderAutSubgroup ℚ) := by
  constructor
  · -- closedness in the pointwise topology
    let : TopologicalSpace ℚ := ⊥
    have : DiscreteTopology ℚ := ⟨rfl⟩
    unfold Equiv.Perm.pointwiseTopology
    rw [isClosed_induced_iff]
    refine ⟨{f : ℚ → ℚ | ∀ a b, a < b ↔ f a < f b}, ?_, ?_⟩
    · have hclosed : ∀ a b : ℚ, IsClosed {f : ℚ → ℚ | (a < b ↔ f a < f b)} := by
        intro a b
        by_cases h : a < b
        · have heq : {f : ℚ → ℚ | (a < b ↔ f a < f b)} =
              (fun f : ℚ → ℚ => (f a, f b)) ⁻¹' {p : ℚ × ℚ | p.1 < p.2} := by
            ext f
            simp [h]
          rw [heq]
          apply IsClosed.preimage _ (isClosed_discrete _)
          exact (continuous_apply a).prodMk (continuous_apply b)
        · have heq : {f : ℚ → ℚ | (a < b ↔ f a < f b)} =
              (fun f : ℚ → ℚ => (f a, f b)) ⁻¹' {p : ℚ × ℚ | ¬ p.1 < p.2} := by
            ext f
            simp [h]
          rw [heq]
          apply IsClosed.preimage _ (isClosed_discrete _)
          exact (continuous_apply a).prodMk (continuous_apply b)
      have hinter : {f : ℚ → ℚ | ∀ a b, a < b ↔ f a < f b} =
          ⋂ a, ⋂ b, {f : ℚ → ℚ | (a < b ↔ f a < f b)} := by
        ext f
        simp [Set.mem_iInter]
      rw [hinter]
      exact isClosed_iInter fun a => isClosed_iInter fun b => hclosed a b
    · ext σ
      simp only [Set.mem_preimage]
      rfl
  · exact orderAut_isHighlyHomogeneous

end MetaMathlibExt.CameronOrderGroupWanted
