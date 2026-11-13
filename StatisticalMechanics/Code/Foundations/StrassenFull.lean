/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Code.Foundations.Strassen

open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace StatMech

namespace Transport







open Filter Topology



theorem isClosed_nonneg_smul_of_compact {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (K : Set H) (hK : IsCompact K) (h0 : (0 : H) ∉ K) :
    IsClosed {z : H | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ K, z = t • x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro zn z hzn hlim
  choose t ht x hx hz using hzn
  obtain ⟨x0, hx0K, ψ, hψmono, hψlim⟩ := hK.tendsto_subseq hx
  have hx0pos : 0 < ‖x0‖ := by
    rw [norm_pos_iff]; rintro rfl; exact h0 hx0K
  have hzlim : Tendsto (fun n => zn (ψ n)) atTop (𝓝 z) := hlim.comp hψmono.tendsto_atTop
  have hnormx : Tendsto (fun n => ‖x (ψ n)‖) atTop (𝓝 ‖x0‖) :=
    (continuous_norm.tendsto x0).comp hψlim
  have heqt : ∀ n, t (ψ n) = ‖zn (ψ n)‖ / ‖x (ψ n)‖ := by
    intro n
    rcases eq_or_ne (x (ψ n)) 0 with hx0 | hx0
    · exact absurd (hx0 ▸ hx (ψ n)) h0
    · have hnz : ‖zn (ψ n)‖ = t (ψ n) * ‖x (ψ n)‖ := by
        rw [hz (ψ n), norm_smul, Real.norm_of_nonneg (ht (ψ n))]
      rw [hnz, mul_div_assoc, div_self (by rwa [norm_ne_zero_iff]), mul_one]
  have htlim : Tendsto (fun n => t (ψ n)) atTop (𝓝 (‖z‖ / ‖x0‖)) := by
    simp_rw [heqt]
    exact ((continuous_norm.tendsto z).comp hzlim).div hnormx (ne_of_gt hx0pos)
  refine ⟨‖z‖ / ‖x0‖, div_nonneg (norm_nonneg _) (norm_nonneg _), x0, hx0K, ?_⟩
  have hconv : Tendsto (fun n => zn (ψ n)) atTop (𝓝 ((‖z‖ / ‖x0‖) • x0)) := by
    have := htlim.smul hψlim; simpa [hz] using this
  exact tendsto_nhds_unique hzlim hconv



variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


def IsDown (D : Finset P) : Prop := ∀ x y, x ≤ y → y ∈ D → x ∈ D








theorem layer_cake [Nonempty P] (g : P → ℝ) (h : P → ℝ) (hanti : Antitone h)
    (hpos : ∀ x, 0 ≤ h x) (hg : ∀ D : Finset P, IsDown D → 0 ≤ ∑ x ∈ D, g x) :
    0 ≤ ∑ x, g x * h x := by
  generalize hk : (univ.image h).card = k
  induction k using Nat.strong_induction_on generalizing h with
  | _ k IH =>
    by_cases hconst : ∃ c, ∀ x, h x = c
    · obtain ⟨c, hc⟩ := hconst
      have hcpos : 0 ≤ c := by rw [← hc (Classical.arbitrary P)]; exact hpos _
      calc 0 ≤ c * ∑ x, g x := by
              apply mul_nonneg hcpos
              simpa using hg univ (fun x y _ _ => mem_univ x)
        _ = ∑ x, g x * h x := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun x _ => by rw [hc x]; ring)
    · have himg_ne : (univ.image h).Nonempty := univ_nonempty.image h
      set M := (univ.image h).max' himg_ne with hMdef
      have hMmem : M ∈ univ.image h := Finset.max'_mem _ _
      have hMmax : ∀ x, h x ≤ M := fun x =>
        Finset.le_max' _ (h x) (mem_image_of_mem h (mem_univ x))
      set below := (univ.image h).filter (· < M) with hbelowdef
      have hbelow_ne : below.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hconst
        refine ⟨M, fun x => le_antisymm (hMmax x) ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        have hmem' : h x ∈ below := by
          rw [hbelowdef]; simp only [mem_filter, mem_image, mem_univ, true_and]
          exact ⟨⟨x, rfl⟩, hlt⟩
        rw [hempty] at hmem'; exact absurd hmem' (Finset.notMem_empty _)
      set mp := below.max' hbelow_ne with hmpdef
      have hmp_below : mp ∈ below := Finset.max'_mem _ _
      have hmpM : mp < M := by
        have := hmp_below; rw [hbelowdef] at this
        simp only [mem_filter] at this; exact this.2
      have hmpimg : mp ∈ univ.image h := by
        have := hmp_below; rw [hbelowdef] at this
        simp only [mem_filter] at this; exact this.1
      have hbelowle : ∀ x, h x < M → h x ≤ mp := by
        intro x hx
        apply Finset.le_max'
        rw [hbelowdef]; simp only [mem_filter, mem_image, mem_univ, true_and]
        exact ⟨⟨x, rfl⟩, hx⟩
      have hsplit : ∀ x, h x = M ∨ h x ≤ mp := by
        intro x; rcases eq_or_lt_of_le (hMmax x) with he | hl
        · exact Or.inl he
        · exact Or.inr (hbelowle x hl)
      set h' := fun x => min (h x) mp with hh'def
      have hh'anti : Antitone h' := fun x y hxy => min_le_min (hanti hxy) (le_refl mp)
      have hmppos : 0 ≤ mp := by
        obtain ⟨x, hx⟩ : ∃ x, h x = mp := by simpa using hmpimg
        rw [← hx]; exact hpos x
      have hh'pos : ∀ x, 0 ≤ h' x := fun x => le_min (hpos x) hmppos
      set D := univ.filter (fun x => M ≤ h x) with hDdef
      have hDdown : IsDown D := by
        intro x y hxy hy
        rw [hDdef] at *; simp only [mem_filter, mem_univ, true_and] at *
        exact le_trans hy (hanti hxy)
      have hdecomp : ∑ x, g x * h x = (∑ x, g x * h' x) + (M - mp) * ∑ x ∈ D, g x := by
        have ptwise : ∀ x, g x * h x = g x * h' x + (if M ≤ h x then (M - mp) * g x else 0) := by
          intro x
          rcases hsplit x with hx | hx
          · simp only [hh'def, hx]; simp only [le_refl, if_pos]
            rw [min_eq_right (le_of_lt hmpM)]; ring
          · rw [hh'def]; simp only; rw [min_eq_left hx]
            by_cases hMx : M ≤ h x
            · have hxM : h x = M := le_antisymm (le_trans hx (le_of_lt hmpM)) hMx
              have hmpeqM : mp = M := le_antisymm (le_of_lt hmpM) (hxM ▸ hx)
              rw [if_pos hMx, hmpeqM]; ring
            · rw [if_neg hMx]; ring
        rw [Finset.sum_congr rfl (fun x _ => ptwise x), Finset.sum_add_distrib]
        congr 1
        rw [hDdef, Finset.mul_sum, ← Finset.sum_filter]
      rw [hdecomp]
      apply add_nonneg
      · apply IH ((univ.image h').card) ?_ h' hh'anti hh'pos rfl
        rw [← hk]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨M, hMmem, ?_⟩
          simp only [mem_image, not_exists, mem_univ, true_and, hh'def]
          intro x hcontra
          have hle : min (h x) mp ≤ mp := min_le_right _ _
          rw [hcontra] at hle; linarith
        · intro v hv
          simp only [mem_image, mem_univ, true_and, hh'def] at hv ⊢
          obtain ⟨x, rfl⟩ := hv
          rcases le_or_gt (h x) mp with hle | hlt
          · exact ⟨x, by rw [min_eq_left hle]⟩
          · rw [min_eq_right (le_of_lt hlt)]; simpa using hmpimg
      · exact mul_nonneg (by linarith) (hg D hDdown)



variable [DecidableRel ((· ≤ ·) : P → P → Prop)]






theorem dual_feasibility [Nonempty P] (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x)
    (φ ψ : P → ℝ) (hfeas : ∀ x y, x ≤ y → 0 ≤ φ x + ψ y) :
    0 ≤ (∑ x, μ x * φ x) + ∑ y, ν y * ψ y := by
  have hne : ∀ x : P, (univ.filter (x ≤ ·)).Nonempty := fun x => ⟨x, by simp⟩
  set h : P → ℝ := fun x => (univ.filter (x ≤ ·)).sup' (hne x) (fun y => -ψ y) with hhdef
  have hge : ∀ x, -ψ x ≤ h x := fun x => Finset.le_sup' (f := fun y => -ψ y) (by simp)
  have hφh : ∀ x, h x ≤ φ x := by
    intro x; apply Finset.sup'_le
    intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    linarith [hfeas x y hy]
  have hanti : Antitone h := by
    intro x x' hxx'
    apply Finset.sup'_le
    intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    exact Finset.le_sup' (f := fun y => -ψ y) (by
      simp only [mem_filter, mem_univ, true_and]; exact le_trans hxx' hy)
  set c : ℝ := - (univ.inf' univ_nonempty h) with hcdef
  have hshiftpos : ∀ x, 0 ≤ h x + c := by
    intro x; rw [hcdef]
    have : univ.inf' univ_nonempty h ≤ h x := Finset.inf'_le _ (mem_univ x)
    linarith
  have hshiftanti : Antitone (fun x => h x + c) := fun x y hxy => by
    simp only; have := hanti hxy; linarith
  have key : 0 ≤ ∑ x, (μ x - ν x) * (h x + c) := by
    apply layer_cake (fun x => μ x - ν x) (fun x => h x + c) hshiftanti hshiftpos
    intro D hD
    rw [Finset.sum_sub_distrib]
    linarith [hDOM D hD]
  have hsum0 : ∑ x, (μ x - ν x) = 0 := by rw [Finset.sum_sub_distrib, hTOT, sub_self]
  have expand : ∑ x, (μ x - ν x) * (h x + c) = ∑ x, (μ x - ν x) * h x := by
    have hpt : ∀ x, (μ x - ν x) * (h x + c) = (μ x - ν x) * h x + c * (μ x - ν x) :=
      fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum0, mul_zero, add_zero]
  rw [expand] at key
  have step1 : (∑ x, (μ x - ν x) * h x) ≤ (∑ x, μ x * φ x) + ∑ y, ν y * ψ y := by
    rw [show (∑ x, (μ x - ν x) * h x) = (∑ x, μ x * h x) - ∑ x, ν x * h x by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)]
    have hA : (∑ x, μ x * h x) ≤ ∑ x, μ x * φ x :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hφh x) (hμpos x))
    have hB : -(∑ x, ν x * h x) ≤ ∑ y, ν y * ψ y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum; intro x _
      have hrw : -(ν x * h x) = ν x * (-h x) := by ring
      rw [hrw]; exact mul_le_mul_of_nonneg_left (by linarith [hge x]) (hνpos x)
    linarith
  linarith




abbrev OrderPairs (P : Type*) [PartialOrder P] := {p : P × P // p.1 ≤ p.2}

instance : Fintype (OrderPairs P) := Subtype.fintype _
instance : DecidableEq (OrderPairs P) := Subtype.instDecidableEq



def pmargL : (OrderPairs P → ℝ) →ₗ[ℝ] (P ⊕ P → ℝ) where
  toFun c := fun s => match s with
    | Sum.inl x => ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0
    | Sum.inr y => ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0
  map_add' c d := by
    funext s; cases s <;>
    · simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
  map_smul' r c := by
    funext s; cases s <;>
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)


noncomputable def margL :
    EuclideanSpace ℝ (OrderPairs P) →ₗ[ℝ] EuclideanSpace ℝ (P ⊕ P) :=
  (WithLp.linearEquiv 2 ℝ (P ⊕ P → ℝ)).symm.toLinearMap ∘ₗ pmargL ∘ₗ
    (WithLp.linearEquiv 2 ℝ (OrderPairs P → ℝ)).toLinearMap


noncomputable def margCLM :
    EuclideanSpace ℝ (OrderPairs P) →L[ℝ] EuclideanSpace ℝ (P ⊕ P) :=
  LinearMap.toContinuousLinearMap margL

theorem margCLM_inl (c : EuclideanSpace ℝ (OrderPairs P)) (x : P) :
    margCLM c (Sum.inl x) = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := rfl

theorem margCLM_inr (c : EuclideanSpace ℝ (OrderPairs P)) (y : P) :
    margCLM c (Sum.inr y) = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := rfl



theorem marg_inner (c : EuclideanSpace ℝ (OrderPairs P)) (w : EuclideanSpace ℝ (P ⊕ P)) :
    (inner ℝ (margCLM c) w : ℝ)
      = ∑ q : OrderPairs P, c q * (w (Sum.inl (q : P × P).1) + w (Sum.inr (q : P × P).2)) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [RCLike.inner_apply, conj_trivial]
  have e1 : ∀ x : P, (margCLM c) (Sum.inl x)
      = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := fun x => margCLM_inl c x
  have e2 : ∀ y : P, (margCLM c) (Sum.inr y)
      = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := fun y => margCLM_inr c y
  simp only [e1, e2]
  have hL : (∑ x, w (Sum.inl x) * ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0)
      = ∑ q : OrderPairs P, c q * w (Sum.inl (q : P × P).1) := by
    have hstep : ∀ x : P, w (Sum.inl x) * ∑ q : OrderPairs P, (if (q : P × P).1 = x then c q else 0)
        = ∑ q : OrderPairs P, (if (q : P × P).1 = x then c q * w (Sum.inl x) else 0) := by
      intro x; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ (q : P × P).1 (fun x => c q * w (Sum.inl x))]
    simp
  have hR : (∑ y, w (Sum.inr y) * ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0)
      = ∑ q : OrderPairs P, c q * w (Sum.inr (q : P × P).2) := by
    have hstep : ∀ y : P, w (Sum.inr y) * ∑ q : OrderPairs P, (if (q : P × P).2 = y then c q else 0)
        = ∑ q : OrderPairs P, (if (q : P × P).2 = y then c q * w (Sum.inr y) else 0) := by
      intro y; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
    rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ (q : P × P).2 (fun y => c q * w (Sum.inr y))]
    simp
  rw [hL, hR, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => by ring)

open ProperCone Set



noncomputable def orthant (P : Type*) [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] : ProperCone ℝ (EuclideanSpace ℝ (OrderPairs P)) :=
  innerDual (Set.range (fun q => (EuclideanSpace.single q 1 : EuclideanSpace ℝ (OrderPairs P))))

theorem mem_orthant (y : EuclideanSpace ℝ (OrderPairs P)) :
    y ∈ orthant P ↔ ∀ q, 0 ≤ y q := by
  simp only [orthant, mem_innerDual]
  constructor
  · intro h q
    simpa [EuclideanSpace.inner_single_left] using h (Set.mem_range_self q)
  · rintro h x ⟨q, rfl⟩
    simpa [EuclideanSpace.inner_single_left] using h q

theorem inner_eq_sum (x y : EuclideanSpace ℝ (OrderPairs P)) :
    (inner ℝ x y : ℝ) = ∑ q, x q * y q := by
  rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]


theorem orthant_selfdual :
    innerDual ((orthant P : Set (EuclideanSpace ℝ (OrderPairs P)))) = orthant P := by
  apply le_antisymm
  · intro y hy
    rw [mem_orthant]; intro q; rw [mem_innerDual] at hy
    have hpos : (0 : ℝ) ≤ (inner ℝ (EuclideanSpace.single q (1 : ℝ)) y : ℝ) := by
      apply hy; rw [SetLike.mem_coe, mem_orthant]; intro j
      rcases eq_or_ne q j with rfl | hne
      · simp
      · simp [hne, eq_comm]
    simpa [EuclideanSpace.inner_single_left] using hpos
  · intro y hy; rw [mem_innerDual]; intro x hx
    rw [SetLike.mem_coe, mem_orthant] at hx; rw [mem_orthant] at hy
    rw [inner_eq_sum]
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (hx q) (hy q))








theorem exists_coupling_vec [Nonempty P] (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x) :
    ∃ c : OrderPairs P → ℝ, (∀ q, 0 ≤ c q) ∧
      (∀ x, (∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0) = μ x) ∧
      (∀ y, (∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0) = ν y) := by
  classical
  set b : EuclideanSpace ℝ (P ⊕ P) := (WithLp.equiv 2 _).symm
    (fun s => match s with | Sum.inl x => μ x | Sum.inr y => ν y) with hbdef
  have hbinl : ∀ x, b (Sum.inl x) = μ x := fun x => rfl
  have hbinr : ∀ y, b (Sum.inr y) = ν y := fun y => rfl
  
  have hmem : b ∈ ProperCone.map margCLM (orthant P) := by
    rw [ProperCone.relative_hyperplane_separation]
    intro w hw
    rw [orthant_selfdual, mem_orthant] at hw
    have hfeas : ∀ x y : P, x ≤ y → 0 ≤ w (Sum.inl x) + w (Sum.inr y) := by
      intro x y hxy
      have hwq := hw ⟨(x, y), hxy⟩
      have key : (ContinuousLinearMap.adjoint margCLM w) (⟨(x, y), hxy⟩ : OrderPairs P)
          = w (Sum.inl x) + w (Sum.inr y) := by
        have h1 : (inner ℝ (EuclideanSpace.single (⟨(x, y), hxy⟩ : OrderPairs P) (1 : ℝ))
              (ContinuousLinearMap.adjoint margCLM w) : ℝ)
            = (ContinuousLinearMap.adjoint margCLM w) (⟨(x, y), hxy⟩ : OrderPairs P) := by
          rw [EuclideanSpace.inner_single_left]; simp
        rw [← h1, ContinuousLinearMap.adjoint_inner_right, marg_inner]
        simp only [PiLp.single_apply]
        rw [Finset.sum_eq_single (⟨(x, y), hxy⟩ : OrderPairs P)]
        · simp
        · intro q _ hqne; simp [hqne]
        · intro hc; exact absurd (Finset.mem_univ _) hc
      rw [key] at hwq; exact hwq
    rw [show (inner ℝ b w : ℝ)
          = (∑ x, b (Sum.inl x) * w (Sum.inl x)) + ∑ y, b (Sum.inr y) * w (Sum.inr y) by
      rw [PiLp.inner_apply, Fintype.sum_sum_type]
      simp only [RCLike.inner_apply, conj_trivial]
      congr 1 <;> exact Finset.sum_congr rfl (fun x _ => by ring)]
    simp only [hbinl, hbinr]
    exact dual_feasibility μ ν hμpos hνpos hTOT hDOM
      (fun x => w (Sum.inl x)) (fun y => w (Sum.inr y)) hfeas
  
  
  set base : Set (EuclideanSpace ℝ (P ⊕ P)) :=
    margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | (∀ q, 0 ≤ c q) ∧ ∑ q, c q = 1} with hbasedef
  have hsimplex_compact : IsCompact
      {c : EuclideanSpace ℝ (OrderPairs P) | (∀ q, 0 ≤ c q) ∧ ∑ q, c q = 1} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · 
      have h1 : IsClosed {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
        rw [show {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q}
            = ⋂ q, {c : EuclideanSpace ℝ (OrderPairs P) | 0 ≤ c q} by ext c; simp]
        exact isClosed_iInter (fun q =>
          isClosed_le continuous_const ((EuclideanSpace.proj q).continuous))
      have h2 : IsClosed {c : EuclideanSpace ℝ (OrderPairs P) | ∑ q, c q = 1} := by
        have hcont : Continuous (fun c : EuclideanSpace ℝ (OrderPairs P) => ∑ q, c q) :=
          continuous_finsetSum _ (fun q _ => (EuclideanSpace.proj q).continuous)
        exact isClosed_eq hcont continuous_const
      exact h1.inter h2
    · 
      apply Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (OrderPairs P)) |>.2
      refine ⟨Real.sqrt (Fintype.card (OrderPairs P)), fun c hc => ?_⟩
      simp only [Set.mem_setOf_eq] at hc
      obtain ⟨hcpos, hcsum⟩ := hc
      rw [Metric.mem_closedBall, dist_zero_right]
      have hbd : ∀ q, c q ≤ 1 := by
        intro q
        calc c q ≤ ∑ q', c q' := Finset.single_le_sum (fun q' _ => hcpos q') (Finset.mem_univ q)
          _ = 1 := hcsum
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ q, ‖c q‖ ^ 2 ≤ ∑ q : OrderPairs P, (1:ℝ) := by
            apply Finset.sum_le_sum; intro q _
            rw [Real.norm_eq_abs, abs_of_nonneg (hcpos q), sq_le_one_iff_abs_le_one,
              abs_of_nonneg (hcpos q)]
            exact hbd q
        _ = Fintype.card (OrderPairs P) := by simp
  have hbase_compact : IsCompact base := hsimplex_compact.image margCLM.continuous
  have hbase_no0 : (0 : EuclideanSpace ℝ (P ⊕ P)) ∉ base := by
    rintro ⟨c, ⟨hcpos, hcsum⟩, hc0⟩
    
    have hrow : ∑ x : P, (margCLM c) (Sum.inl x) = 1 := by
      simp only [margCLM_inl]
      rw [Finset.sum_comm]
      rw [show (∑ q : OrderPairs P, ∑ x : P, if (q : P × P).1 = x then c q else 0)
          = ∑ q : OrderPairs P, c q from
        Finset.sum_congr rfl (fun q _ => by
          rw [Finset.sum_ite_eq Finset.univ (q : P × P).1 (fun _ => c q)]; simp)]
      exact hcsum
    rw [hc0] at hrow; simp at hrow
  have hbase_ne : base.Nonempty := by
    have hq0 : Nonempty (OrderPairs P) := ⟨⟨(Classical.arbitrary P, Classical.arbitrary P), le_refl _⟩⟩
    obtain ⟨q0⟩ := hq0
    refine ⟨margCLM (EuclideanSpace.single q0 1), EuclideanSpace.single q0 1, ⟨?_, ?_⟩, rfl⟩
    · intro q; rcases eq_or_ne q0 q with rfl | hne
      · simp
      · simp [hne]
    · rw [show (∑ q, (EuclideanSpace.single q0 (1:ℝ)) q) = ∑ q, (if q = q0 then (1:ℝ) else 0) from
        Finset.sum_congr rfl (fun q _ => by rw [PiLp.single_apply])]
      simp
  have himg_closed : IsClosed {z : EuclideanSpace ℝ (P ⊕ P) |
      ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ base, z = t • x} :=
    isClosed_nonneg_smul_of_compact base hbase_compact hbase_no0
  
  have himg_eq : (margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q})
      = {z : EuclideanSpace ℝ (P ⊕ P) | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ base, z = t • x} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      by_cases hz : ∑ q, c q = 0
      · 
        have hc0 : ∀ q, c q = 0 := fun q =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hc q)).1 hz q (Finset.mem_univ q)
        obtain ⟨x0, hx0⟩ := hbase_ne
        refine ⟨0, le_refl 0, x0, hx0, ?_⟩
        rw [zero_smul]
        rw [show c = 0 from PiLp.ext (fun q => by simpa using hc0 q), map_zero]
      · refine ⟨∑ q, c q, Finset.sum_nonneg (fun q _ => hc q), (∑ q, c q)⁻¹ • (margCLM c), ?_, ?_⟩
        · refine ⟨(∑ q, c q)⁻¹ • c, ⟨fun q => ?_, ?_⟩, by rw [map_smul]⟩
          · exact smul_nonneg (inv_nonneg.2 (Finset.sum_nonneg (fun q _ => hc q))) (hc q)
          · simp only [PiLp.smul_apply, smul_eq_mul]
            rw [← Finset.mul_sum, inv_mul_cancel₀ hz]
        · rw [smul_inv_smul₀ hz]
    · rintro ⟨t, ht, x, hx, rfl⟩
      obtain ⟨c, ⟨hcpos, _⟩, rfl⟩ := hx
      exact ⟨t • c, fun q => smul_nonneg ht (hcpos q), by rw [map_smul]⟩
  have hset : ((orthant P).toPointedCone : Set (EuclideanSpace ℝ (OrderPairs P)))
      = {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    ext c; rw [SetLike.mem_coe, ProperCone.mem_toPointedCone, mem_orthant]; rfl
  
  have hcoe : (((orthant P).toPointedCone.map
        ((margCLM : EuclideanSpace ℝ (OrderPairs P) →L[ℝ] EuclideanSpace ℝ (P ⊕ P)) :
          EuclideanSpace ℝ (OrderPairs P) →ₗ[ℝ] EuclideanSpace ℝ (P ⊕ P))) : Set _)
      = margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    rw [PointedCone.coe_map, hset]; rfl
  
  have hb_img : b ∈ margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    rw [ProperCone.mem_map, PointedCone.mem_closure] at hmem
    rw [hcoe] at hmem
    have hclo : closure (margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q})
        = margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
      rw [himg_eq]; exact himg_closed.closure_eq
    rwa [hclo] at hmem
  
  obtain ⟨c, hc, hceq⟩ := hb_img
  simp only [Set.mem_setOf_eq] at hc
  refine ⟨fun q => c q, hc, ?_, ?_⟩
  · intro x
    have hxapp := congrArg (fun (v : EuclideanSpace ℝ (P ⊕ P)) => v (Sum.inl x)) hceq
    simp only at hxapp
    rw [margCLM_inl] at hxapp
    rw [hxapp, hbinl]
  · intro y
    have hyapp := congrArg (fun (v : EuclideanSpace ℝ (P ⊕ P)) => v (Sum.inr y)) hceq
    simp only at hyapp
    rw [margCLM_inr] at hyapp
    rw [hyapp, hbinr]

end Transport








section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


instance : DecidableRel ((· ≤ ·) : ConfigSpace E → ConfigSpace E → Prop) :=
  fun _ _ => Fintype.decidableForallFintype


private noncomputable def mass (μ : Measure (ConfigSpace E)) (ω : ConfigSpace E) : ℝ :=
  (μ {ω}).toReal

private theorem mass_nonneg (μ : Measure (ConfigSpace E)) (ω : ConfigSpace E) :
    0 ≤ mass μ ω := ENNReal.toReal_nonneg


private theorem measureReal_finset_eq_sum_mass (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (A : Finset (ConfigSpace E)) :
    μ.real (A : Set (ConfigSpace E)) = ∑ ω ∈ A, mass μ ω := by
  simp only [mass, measureReal_def]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  congr 1
  rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
        (fun ω _ => measurableSet_singleton ω)]
  congr 1; ext ω; simp


private theorem sum_mass_eq_one (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] :
    ∑ ω : ConfigSpace E, mass μ ω = 1 := by
  simp only [mass]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  rw [show (∑ ω : ConfigSpace E, μ {ω}) = μ Set.univ by
    rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
          (fun ω _ => measurableSet_singleton ω)]
    congr 1; ext ω; simp]
  simp


private theorem measure_singleton_eq_ofReal_mass (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (ω : ConfigSpace E) : μ {ω} = ENNReal.ofReal (mass μ ω) := by
  rw [mass, ENNReal.ofReal_toReal (measure_ne_top μ _)]



private theorem mass_down_dom (μ ν : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hdom : μ ≼ ν)
    (D : Finset (ConfigSpace E)) (hD : Transport.IsDown D) :
    ∑ ω ∈ D, mass ν ω ≤ ∑ ω ∈ D, mass μ ω := by
  have hDc_inc : IsIncreasing ((↑D)ᶜ : Set (ConfigSpace E)) := by
    apply IsLowerSet.compl
    intro a b hab hb
    simp only [Finset.mem_coe] at *
    exact hD b a hab hb
  have hmeas : MeasurableSet ((↑D)ᶜ : Set (ConfigSpace E)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hle := hdom _ hmeas hDc_inc
  have hsplit : ∀ (ρ : Measure (ConfigSpace E)) [IsProbabilityMeasure ρ],
      ρ.real ((↑D)ᶜ : Set (ConfigSpace E)) = 1 - ∑ ω ∈ D, mass ρ ω := by
    intro ρ _
    have h1 := probReal_add_probReal_compl (μ := ρ) (s := (↑D : Set (ConfigSpace E)))
        (DiscreteMeasurableSpace.forall_measurableSet _)
    rw [measureReal_finset_eq_sum_mass ρ D] at h1
    linarith
  rw [hsplit μ, hsplit ν] at hle
  linarith



private noncomputable def kappaOfVec
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    Measure (ConfigSpace E × ConfigSpace E) :=
  ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
    (ENNReal.ofReal (c q)) • Measure.dirac (q : ConfigSpace E × ConfigSpace E)

open scoped Classical in
private theorem kappaOfVec_apply
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ)
    (A : Set (ConfigSpace E × ConfigSpace E)) :
    kappaOfVec c A
      = ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
          if (q : ConfigSpace E × ConfigSpace E) ∈ A then ENNReal.ofReal (c q) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold kappaOfVec
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hq : (q : ConfigSpace E × ConfigSpace E) ∈ A <;> simp [hq]

instance (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    IsFiniteMeasure (kappaOfVec c) := by
  refine ⟨?_⟩
  rw [kappaOfVec_apply]
  simp only [Set.mem_univ, if_true]
  exact ENNReal.sum_lt_top.2 (fun q _ => ENNReal.ofReal_lt_top)










theorem exists_monotoneCoupling_of_stochasticallyDominated
    (μ ν : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : μ ≼ ν) :
    ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
      IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ := by
  classical
  
  obtain ⟨c, hcpos, hrow, hcol⟩ :=
    Transport.exists_coupling_vec (P := ConfigSpace E) (mass μ) (mass ν)
      (mass_nonneg μ) (mass_nonneg ν)
      (by rw [sum_mass_eq_one μ, sum_mass_eq_one ν])
      (fun D hD => mass_down_dom μ ν hdom D hD)
  
  refine ⟨kappaOfVec c, inferInstance, ?_, ?_, ?_⟩
  · 
    apply Measure.ext_of_singleton
    intro ω
    rw [Measure.fst_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass μ ω, ← hrow ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).1 = ω
    · rw [if_pos (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.fst ⁻¹' {ω} from hq),
        if_pos hq]
    · rw [if_neg (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.fst ⁻¹' {ω} from hq),
        if_neg hq, ENNReal.ofReal_zero]
  · 
    apply Measure.ext_of_singleton
    intro ω
    rw [Measure.snd_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass ν ω, ← hcol ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).2 = ω
    · rw [if_pos (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.snd ⁻¹' {ω} from hq),
        if_pos hq]
    · rw [if_neg (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.snd ⁻¹' {ω} from hq),
        if_neg hq, ENNReal.ofReal_zero]
  · 
    rw [kappaOfVec_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro hmem
    
    exact hmem q.2

end ConfigSpace

end StatMech
