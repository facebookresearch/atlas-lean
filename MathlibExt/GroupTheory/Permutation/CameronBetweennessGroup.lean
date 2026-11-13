/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.Betweenness
public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions

@[expose] public section

/-!
# Cameron betweenness group

The rational-order betweenness automorphism group is closed in the pointwise topology
and highly homogeneous.
-/

namespace MetaMathlibExt.CameronBetweennessGroupWanted

private lemma continuous_eval (a : ℚ) :
    @Continuous (Equiv.Perm ℚ) ℚ (Equiv.Perm.pointwiseTopology (α := ℚ)) ⊥
      (fun σ : Equiv.Perm ℚ => σ a) := by
  let : TopologicalSpace (Equiv.Perm ℚ) := Equiv.Perm.pointwiseTopology (α := ℚ)
  let : TopologicalSpace ℚ := ⊥
  change @Continuous _ _ (TopologicalSpace.induced (fun σ : Equiv.Perm ℚ => ⇑σ) inferInstance)
    inferInstance (fun σ : Equiv.Perm ℚ => σ a)
  exact (continuous_apply a).comp continuous_induced_dom

private lemma isClosed_cond (a b c : ℚ) :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
      { σ | isBetween ℚ a b c ↔ isBetween ℚ (σ a) (σ b) (σ c) } := by
  let : TopologicalSpace (Equiv.Perm ℚ) := Equiv.Perm.pointwiseTopology (α := ℚ)
  let : TopologicalSpace ℚ := ⊥
  have := discreteTopology_bot ℚ
  have hcont : Continuous (fun σ : Equiv.Perm ℚ => ((σ a, (σ b, σ c)) : ℚ × (ℚ × ℚ))) := by
    have ha : Continuous (fun σ : Equiv.Perm ℚ => σ a) := continuous_eval a
    have hb : Continuous (fun σ : Equiv.Perm ℚ => σ b) := continuous_eval b
    have hc : Continuous (fun σ : Equiv.Perm ℚ => σ c) := continuous_eval c
    exact ha.prodMk (hb.prodMk hc)
  have hset : { σ : Equiv.Perm ℚ | isBetween ℚ a b c ↔ isBetween ℚ (σ a) (σ b) (σ c) } =
      (fun σ : Equiv.Perm ℚ => ((σ a, (σ b, σ c)) : ℚ × (ℚ × ℚ))) ⁻¹'
        { p : ℚ × (ℚ × ℚ) | isBetween ℚ a b c ↔ isBetween ℚ p.1 p.2.1 p.2.2 } := rfl
  rw [hset]
  exact IsClosed.preimage hcont (isClosed_discrete _)

private lemma closed_carrier :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
      ↑(betweennessAutSubgroup ℚ) := by
  let : TopologicalSpace (Equiv.Perm ℚ) := Equiv.Perm.pointwiseTopology (α := ℚ)
  have hcar : (↑(betweennessAutSubgroup ℚ) : Set (Equiv.Perm ℚ)) =
      ⋂ a, ⋂ b, ⋂ c, { σ : Equiv.Perm ℚ | isBetween ℚ a b c ↔ isBetween ℚ (σ a) (σ b) (σ c) } := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred]
    rfl
  rw [hcar]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
    isClosed_cond a b c

private noncomputable def tailFix (a u v : ℚ) : ℚ → ℚ := fun x =>
  if x ≤ a then x
  else if x ≤ u then a + (x - a) * ((v - a) / (u - a))
  else v + (x - u)

private lemma tailFix_fix (a u v x : ℚ) (h : x ≤ a) : tailFix a u v x = x := by
  simp [tailFix, h]

private lemma tailFix_u (a u v : ℚ) (h : a < u) : tailFix a u v u = v := by
  have hua : u - a ≠ 0 := by
    have : (0:ℚ) < u - a := by linarith
    exact ne_of_gt this
  have h1 : ¬ (u ≤ a) := by linarith
  simp [tailFix, h1]
  field_simp
  ring

private lemma tailFix_strictMono (a u v : ℚ) (hu : a < u) (hv : a < v) :
    StrictMono (tailFix a u v) := by
  have hua : (0:ℚ) < u - a := by linarith
  have hva : (0:ℚ) < v - a := by linarith
  have hm : (0:ℚ) < (v - a) / (u - a) := div_pos hva hua
  intro x y hxy
  by_cases hx1 : x ≤ a
  · by_cases hy1 : y ≤ a
    · rw [tailFix_fix a u v x hx1, tailFix_fix a u v y hy1]; exact hxy
    · by_cases hy2 : y ≤ u
      · simp only [tailFix, hx1, ↓reduceIte, hy1, hy2]
        have hpos : (0:ℚ) < (y - a) * ((v - a) / (u - a)) :=
          mul_pos (by linarith) hm
        linarith
      · simp [tailFix, hx1, hy1, hy2]
        have : (0:ℚ) < y - u := by
          have : a < y := lt_of_not_ge hy1
          linarith [hu]
        linarith
  · by_cases hy1 : y ≤ a
    · linarith
    · by_cases hx2 : x ≤ u
      · by_cases hy2 : y ≤ u
        · simp [tailFix, hx1, hx2, hy1, hy2]
          have h := mul_lt_mul_of_pos_right (sub_lt_sub_right hxy a) hm
          linarith
        · simp only [tailFix, hx1, ↓reduceIte, hx2, hy1, hy2]
          have hle : (x - a) * ((v - a) / (u - a)) ≤ (v - a) := by
            have h1 : x - a ≤ u - a := by linarith
            have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hm)
            rwa [mul_div_cancel₀ _ (ne_of_gt hua)] at h2
          have hlt : (0:ℚ) < y - u := by linarith
          linarith
      · by_cases hy2 : y ≤ u
        · linarith
        · simp [tailFix, hx1, hx2, hy1, hy2]
          linarith

private lemma tailFix_surjective (a u v : ℚ) (hu : a < u) (hv : a < v) :
    Function.Surjective (tailFix a u v) := by
  have hua : (0:ℚ) < u - a := by linarith
  have hva : (0:ℚ) < v - a := by linarith
  have hva' : v - a ≠ 0 := ne_of_gt hva
  have hmi : (0:ℚ) < (u - a) / (v - a) := div_pos hua hva
  intro y
  by_cases hy1 : y ≤ a
  · exact ⟨y, by simp [tailFix, hy1]⟩
  · by_cases hy2 : y ≤ v
    · refine ⟨a + (y - a) * ((u - a) / (v - a)), ?_⟩
      have hya : (0:ℚ) < y - a := by linarith [lt_of_not_ge hy1]
      have hxgt : a < a + (y - a) * ((u - a) / (v - a)) := by
        have : (0:ℚ) < (y - a) * ((u - a) / (v - a)) := mul_pos hya hmi
        linarith
      have hxle : a + (y - a) * ((u - a) / (v - a)) ≤ u := by
        have h1 : (y - a) * ((u - a) / (v - a)) ≤ (u - a) := by
          have hle : y - a ≤ v - a := by linarith
          have h2 := mul_le_mul_of_nonneg_right hle (le_of_lt hmi)
          rwa [mul_div_cancel₀ _ hva'] at h2
        linarith
      have hx1 : ¬ (a + (y - a) * ((u - a) / (v - a)) ≤ a) := by linarith
      have hcancel : ((u - a) / (v - a)) * ((v - a) / (u - a)) = 1 := by
        field_simp
      have hmain : (a + (y - a) * ((u - a) / (v - a)) - a) * ((v - a) / (u - a)) = (y - a) := by
        have hsub : a + (y - a) * ((u - a) / (v - a)) - a = (y - a) * ((u - a) / (v - a)) := by ring
        rw [hsub, mul_assoc, hcancel, mul_one]
      simp [tailFix, hx1, hxle]
      linarith
    · refine ⟨u + (y - v), ?_⟩
      have hyv : (0:ℚ) < y - v := by linarith [lt_of_not_ge hy2]
      have hx1 : ¬ (u + (y - v) ≤ a) := by linarith
      have hx2 : ¬ (u + (y - v) ≤ u) := by linarith
      simp [tailFix, hx1, hx2]

private lemma tailFix_bijective (a u v : ℚ) (hu : a < u) (hv : a < v) :
    Function.Bijective (tailFix a u v) :=
  ⟨(tailFix_strictMono a u v hu hv).injective, tailFix_surjective a u v hu hv⟩

private lemma mem_betweenness_of_strictMono_bijective (f : ℚ → ℚ)
    (hm : StrictMono f) (hb : Function.Bijective f) :
    Equiv.ofBijective f hb ∈ betweennessAutSubgroup ℚ := by
  have hlt : ∀ x y : ℚ, x < y ↔ f x < f y := by
    intro x y
    constructor
    · intro h
      exact hm h
    · intro h
      by_contra hcon
      exact (not_le_of_gt h) (hm.monotone (le_of_not_gt hcon))
  intro a b c
  have e1 := hlt a b
  have e2 := hlt b c
  have e3 := hlt c b
  have e4 := hlt b a
  simp only [Equiv.ofBijective_apply]
  change isBetween ℚ a b c ↔ isBetween ℚ (f a) (f b) (f c)
  unfold isBetween
  rw [e1, e2, e3, e4]

private lemma exists_strictMono_map (s t : Finset ℚ) (n : ℕ) (hs : s.card = n) (ht : t.card = n) :
    ∃ g : ℚ → ℚ, StrictMono g ∧ Function.Bijective g ∧
      ∀ j : Fin n, g (s.orderEmbOfFin hs j) = t.orderEmbOfFin ht j := by
  have hesM : StrictMono (s.orderEmbOfFin hs) := (s.orderEmbOfFin hs).strictMono
  have hetM : StrictMono (t.orderEmbOfFin ht) := (t.orderEmbOfFin ht).strictMono
  have hetMon : Monotone (t.orderEmbOfFin ht) := hetM.monotone
  have key : ∀ i : ℕ, ∃ g : ℚ → ℚ, StrictMono g ∧ Function.Bijective g ∧
      ∀ j : Fin n, j.val < i → g (s.orderEmbOfFin hs j) = t.orderEmbOfFin ht j := by
    intro i
    induction i with
    | zero =>
      exact ⟨id, strictMono_id, Function.bijective_id,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ i ih =>
      obtain ⟨g, hmg, hbg, hcorr⟩ := ih
      by_cases hi : i < n
      · by_cases hi0 : i = 0
        · subst hi0
          have htrans_mono : StrictMono
              (fun x : ℚ => x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩))) := by
            intro x y hxy
            change x + _ < y + _
            linarith
          have htrans_bij : Function.Bijective
              (fun x : ℚ => x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩))) := by
            constructor
            · intro x y h
              have h2 : x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩)) =
                  y + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩)) := h
              linarith
            · intro y
              exact ⟨y - (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩)), by ring⟩
          have huv : (fun x : ℚ =>
              x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩)))
              (g (s.orderEmbOfFin hs ⟨0, hi⟩)) = t.orderEmbOfFin ht ⟨0, hi⟩ := by
            change g _ + (_ - g _) = _
            ring
          refine ⟨(fun x : ℚ =>
              x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩))) ∘ g,
            htrans_mono.comp hmg, htrans_bij.comp hbg, ?_⟩
          intro j hj
          have hjeq : j = ⟨0, hi⟩ := Fin.ext (show j.val = 0 by omega)
          rw [hjeq]
          change ((fun x : ℚ => x + _) ∘ g) (s.orderEmbOfFin hs ⟨0, hi⟩) = _
          change (fun x : ℚ => x + (t.orderEmbOfFin ht ⟨0, hi⟩ - g (s.orderEmbOfFin hs ⟨0, hi⟩)))
            (g (s.orderEmbOfFin hs ⟨0, hi⟩)) = _
          exact huv
        · have h1 : i - 1 < n := by omega
          have hcorr1 : g (s.orderEmbOfFin hs ⟨i - 1, h1⟩) = t.orderEmbOfFin ht ⟨i - 1, h1⟩ :=
            hcorr _ (show i - 1 < i by omega)
          have hfin1 : (⟨i - 1, h1⟩ : Fin n) < ⟨i, hi⟩ := Fin.mk_lt_mk.mpr (by omega)
          have hau : t.orderEmbOfFin ht ⟨i - 1, h1⟩ < g (s.orderEmbOfFin hs ⟨i, hi⟩) := by
            have h1' : g (s.orderEmbOfFin hs ⟨i - 1, h1⟩) < g (s.orderEmbOfFin hs ⟨i, hi⟩) :=
              hmg (hesM hfin1)
            rw [hcorr1] at h1'
            exact h1'
          have hav : t.orderEmbOfFin ht ⟨i - 1, h1⟩ < t.orderEmbOfFin ht ⟨i, hi⟩ :=
            hetM hfin1
          set A := t.orderEmbOfFin ht ⟨i - 1, h1⟩ with hA
          set U := g (s.orderEmbOfFin hs ⟨i, hi⟩) with hU
          set V := t.orderEmbOfFin ht ⟨i, hi⟩ with hV
          have hhM := tailFix_strictMono A U V hau hav
          have hhB := tailFix_bijective A U V hau hav
          refine ⟨tailFix A U V ∘ g, hhM.comp hmg, hhB.comp hbg, ?_⟩
          intro j hj
          by_cases hji : j.val < i
          · have hgj : g (s.orderEmbOfFin hs j) = t.orderEmbOfFin ht j := hcorr j hji
            have hfin : j ≤ (⟨i - 1, h1⟩ : Fin n) :=
              Fin.le_def.mpr (show j.val ≤ i - 1 by omega)
            have hle : t.orderEmbOfFin ht j ≤ A := hetMon hfin
            have hfix : tailFix A U V (t.orderEmbOfFin ht j) = t.orderEmbOfFin ht j :=
              tailFix_fix A U V _ hle
            change tailFix A U V (g (s.orderEmbOfFin hs j)) = _
            rw [hgj, hfix]
          · have hjeq : j = ⟨i, hi⟩ := Fin.ext (show j.val = i by omega)
            rw [hjeq]
            change (tailFix A U V ∘ g) (s.orderEmbOfFin hs ⟨i, hi⟩) = _
            change tailFix A U V (g (s.orderEmbOfFin hs ⟨i, hi⟩)) = _
            exact tailFix_u A U V hau
      · refine ⟨g, hmg, hbg, fun j hj => ?_⟩
        have : j.val < i := by omega
        exact hcorr j this
  obtain ⟨g, hmg, hbg, hcorr⟩ := key n
  exact ⟨g, hmg, hbg, fun j => hcorr j j.isLt⟩

open scoped Pointwise in
private lemma smul_eq_of_map (k : ℕ) (x y : ↥(Set.powersetCard ℚ k))
    (g : ℚ → ℚ) (hbg : Function.Bijective g)
    (hs : x.val.card = k) (ht : y.val.card = k)
    (hmap : ∀ j : Fin k, g (x.val.orderEmbOfFin hs j) = y.val.orderEmbOfFin ht j)
    (hmem : Equiv.ofBijective g hbg ∈ betweennessAutSubgroup ℚ) :
    (⟨Equiv.ofBijective g hbg, hmem⟩ : betweennessAutSubgroup ℚ) • x = y := by
  apply Subtype.ext
  change ((((Equiv.ofBijective g hbg • x : ↥(Set.powersetCard ℚ k)))) : Finset ℚ) = y.val
  rw [Set.powersetCard.coe_smul]
  apply Finset.ext
  intro z
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨w, hw, hzw⟩
    have hw' : w ∈ x.val := hw
    have hwr : w ∈ (↑(x.val) : Set ℚ) := Finset.mem_coe.mpr hw'
    rw [← Finset.range_orderEmbOfFin x.val hs] at hwr
    obtain ⟨j, hj⟩ := hwr
    have hzw2 : Equiv.ofBijective g hbg w = z := hzw
    rw [← hj, Equiv.ofBijective_apply, hmap j] at hzw2
    rw [← hzw2]
    exact Finset.orderEmbOfFin_mem y.val ht j
  · intro hz
    have hzr : z ∈ (↑(y.val) : Set ℚ) := Finset.mem_coe.mpr hz
    rw [← Finset.range_orderEmbOfFin y.val ht] at hzr
    obtain ⟨j, hj⟩ := hzr
    refine ⟨x.val.orderEmbOfFin hs j, Finset.orderEmbOfFin_mem x.val hs j, ?_⟩
    change Equiv.ofBijective g hbg (x.val.orderEmbOfFin hs j) = z
    rw [Equiv.ofBijective_apply, hmap j]
    exact hj

/-- **The betweenness group of the rationals is closed and highly homogeneous.** Let $G$ be the
group of permutations $\sigma$ of $\mathbb{Q}$ preserving strict betweenness in both directions:
for all $a, b, c \in \mathbb{Q}$, $b$ lies strictly between $a$ and $c$ (that is, $a < b < c$ or
$c < b < a$) if and only if $\sigma(b)$ lies strictly between $\sigma(a)$ and $\sigma(c)$. Then
$G$ is closed in the topology of pointwise convergence on the permutations of $\mathbb{Q}$, where
$\mathbb{Q}$ carries the discrete topology, and $G$ is highly homogeneous: for every natural
number $k$ it has a single orbit on the $k$-element subsets of $\mathbb{Q}$.

Source: Daniele A. Gewurz and Francesca Merola, "Sequences realized as Parker vectors
of oligomorphic permutation groups," Journal of Integer Sequences 6,
`https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex`, lines 331–359. Live
and bundled source-file SHA-256 `aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21`;
exact lines 331–359 SHA-256 under LF joining without a terminal LF
`81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4`. The source
identifies `B` (also `∂C*`) as the rational-order permutations preserving or reversing
order and calls Cameron's five representatives closed and highly homogeneous, glossed
as one orbit on `k`-sets for all `k`. The source cites Peter J. Cameron, "Transitivity
of permutation groups on unordered sets," Math. Z. 148 (1976), 127–139. Interpretation
boundary: only the `B` representative is asserted, not exhaustive classification,
uniqueness, or conjugacy.

Proves `Wanted` entry `betweennessAutSubgroup_isClosed_and_highlyHomogeneous`.
-/
theorem betweennessAutSubgroup_isClosed_and_highlyHomogeneous :
    @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
      ↑(betweennessAutSubgroup ℚ) ∧
    IsHighlyHomogeneous (betweennessAutSubgroup ℚ) := by
  constructor
  · exact closed_carrier
  · intro k
    refine MulAction.IsPretransitive.mk fun x y => ?_
    have hs : x.val.card = k := by simp
    have ht : y.val.card = k := by simp
    obtain ⟨g, hmg, hbg, hmap⟩ := exists_strictMono_map x.val y.val k hs ht
    have hmem : Equiv.ofBijective g hbg ∈ betweennessAutSubgroup ℚ :=
      mem_betweenness_of_strictMono_bijective g hmg hbg
    exact ⟨⟨Equiv.ofBijective g hbg, hmem⟩, smul_eq_of_map k x y g hbg hs ht hmap hmem⟩

end MetaMathlibExt.CameronBetweennessGroupWanted
