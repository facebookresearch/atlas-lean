/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finset.Sort
import MathlibExt.Combinatorics.LittlewoodOfford

/-!
# Concentration of subset sums

`subsetSumCountBound_holds` proves the Sárközy–Szemerédi bound by toggling one of the smaller
elements of the set. The change in sum recovers the toggled element. The resulting sums lie in
two intervals of length equal to the least large element. Within either half-open interval,
fixing the small elements leaves an antichain of subsets of the large elements. Sperner's
theorem bounds its size by the middle binomial coefficient.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362Wanted

/-- **Erdős Problem 362: subsets with a given sum.** There is a real constant $C$ such that for
every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and every $t \in \mathbb{N}$,
the number of subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is at most
$C \cdot 2^N / N^{3/2}$. -/
def subsetSumCountBound : Prop :=
  ∃ C : ℝ, ∀ (A : Finset ℕ) (t : ℕ), A.Nonempty →
    ((A.powerset.filter fun S => ∑ n ∈ S, n = t).card : ℝ) ≤
      C * 2 ^ A.card / (A.card : ℝ) ^ (3 / 2 : ℝ)

open Finset

-- On 2k + 1 unit weights, a subset of size k has signed sum -1.
private lemma middle_layer_bound :
    ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      (n.choose (n / 2) : ℝ) * Real.sqrt n ≤ K * 2 ^ n := by
  classical
  obtain ⟨C, hC, h⟩ := ScottishBook179Wanted.littlewoodOffordSharpBound
  refine ⟨2 * C, ?_⟩
  intro n hn
  let k := n / 2
  let m := 2 * k + 1
  have hnm : n ≤ m := by dsimp [m, k]; omega
  have hmn : m ≤ n + 1 := by dsimp [m, k]; omega
  let encode (s : Finset (Fin m)) (i : Fin m) := decide (i ∈ s)
  have hinj : Function.Injective encode := by
    intro s t he
    ext i
    simpa [encode] using congrFun he i
  have hcard := card_le_card_of_injOn (s := univ.powersetCard k)
    (t := univ.filter (fun ε : Fin m → Bool =>
      |(1 : ℝ) + ∑ i, (if ε i then (1 : ℝ) else -1) * 1| < 1)) encode (by
      intro s hs
      have hsk := (mem_powersetCard.mp hs).2
      have hsum : (∑ i : Fin m, (if encode s i then (1 : ℝ) else -1) * 1) =
          2 * s.card - m := by
        simp only [encode, Bool.decide_iff, mul_one]
        simp_rw [show ∀ i : Fin m, (if i ∈ s then (1 : ℝ) else -1) =
          (if i ∈ s then 1 else 0) * 2 - 1 by intro i; split <;> norm_num]
        simp [sum_sub_distrib, mul_comm]
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [hsum, hsk]
      simp [m]) hinj.injOn
  rw [card_powersetCard, card_univ, Fintype.card_fin] at hcard
  have hOff := h m (by dsimp [m]; omega) (fun _ => 1) (by simp)
  have hchoose : (n.choose k : ℝ) ≤ C * 2 ^ m / Real.sqrt m :=
    (Nat.cast_le.mpr ((Nat.choose_le_choose k hnm).trans hcard)).trans hOff
  have hm : 0 < (m : ℝ) := by exact_mod_cast hn.trans_le hnm
  calc
    (n.choose k : ℝ) * Real.sqrt n ≤ (n.choose k : ℝ) * Real.sqrt m := by gcongr
    _ ≤ C * 2 ^ m := (le_div_iff₀ (Real.sqrt_pos.mpr hm)).mp hchoose
    _ ≤ C * 2 ^ (n + 1) := by gcongr; norm_num
    _ = 2 * C * 2 ^ n := by rw [pow_succ]; ring

private def intervalFamily (A : Finset ℕ) (u p : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun S => u ≤ ∑ a ∈ S, a ∧ (∑ a ∈ S, a) < u + p

-- Fix the small elements. Adding any large element increases the sum by at least p.
private lemma interval_card (A L B : Finset ℕ) (hA : L ∪ B = A) (u p : ℕ)
    (hB : ∀ b ∈ B, p ≤ b) :
    (intervalFamily A u p).card ≤ 2 ^ L.card * B.card.choose (B.card / 2) := by
  classical
  let layer (s : Finset ℕ) := univ.filter (fun v : Finset B =>
    let z := (∑ i ∈ s, i) + ∑ i ∈ v, (i : ℕ)
    u ≤ z ∧ z < u + p)
  have hlayer (s : Finset ℕ) : (layer s).card ≤ B.card.choose (B.card / 2) := by
    have hanti : IsAntichain (· ⊆ ·) (layer s : Set (Finset B)) := by
      intro v hv w hw hne hvw
      have hv' := (mem_filter.mp hv).2.1
      have hw' := (mem_filter.mp hw).2.2
      obtain ⟨i, hi⟩ := sdiff_nonempty.mpr (fun hwv => hne (Subset.antisymm hvw hwv))
      have hgap : p ≤ ∑ j ∈ w \ v, (j : ℕ) :=
        (hB i i.property).trans (single_le_sum (fun _ _ => Nat.zero_le _) hi)
      have hsum := sum_sdiff hvw (f := fun i : B => (i : ℕ))
      omega
    simpa using hanti.sperner
  let join (x : Σ _ : Finset ℕ, Finset B) := x.1 ∪ x.2.map (Function.Embedding.subtype _)
  have hsub : intervalFamily A u p ⊆ (L.powerset.sigma layer).image join := by
    intro s hs
    obtain ⟨hsA, hsI⟩ := mem_filter.mp hs
    have hsAB : s ⊆ L ∪ B := hA ▸ mem_powerset.mp hsA
    have hsmall : s \ B ⊆ L := by
      intro a ha
      obtain ⟨haS, haB⟩ := mem_sdiff.mp ha
      exact (mem_union.mp (hsAB haS)).resolve_right haB
    let v := s.subtype (· ∈ B)
    have hsplit : (∑ i ∈ s \ B, i) + (∑ i ∈ v, (i : ℕ)) = ∑ i ∈ s, i := by
      rw [show (∑ i ∈ v, (i : ℕ)) = ∑ i ∈ s ∩ B, i by
        simpa only [v, filter_mem_eq_inter] using
          (sum_subtype_eq_sum_filter (s := s) (p := (· ∈ B)) (fun i => i))]
      rw [← sum_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
    refine mem_image.mpr ⟨⟨s \ B, v⟩, mem_sigma.mpr ⟨mem_powerset.mpr hsmall,
      mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩
    · simpa only [hsplit] using hsI
    · simp only [join, v, subtype_map, filter_mem_eq_inter, sdiff_union_inter]
  calc
    _ ≤ ((L.powerset.sigma layer).image join).card := card_le_card hsub
    _ ≤ (L.powerset.sigma layer).card := card_image_le
    _ = ∑ s ∈ L.powerset, (layer s).card := card_sigma _ _
    _ ≤ ∑ _s ∈ L.powerset, B.card.choose (B.card / 2) := sum_le_sum (fun s _ => hlayer s)
    _ = _ := by simp

private def toggle (s : Finset ℕ) (a : ℕ) : Finset ℕ :=
  if a ∈ s then s.erase a else insert a s

private lemma toggle_twice (s : Finset ℕ) (a : ℕ) : toggle (toggle s a) a = s := by
  by_cases h : a ∈ s <;> simp [toggle, h]

private lemma toggle_sum (s : Finset ℕ) (a : ℕ) :
    (∑ i ∈ toggle s a, i) + a = (∑ i ∈ s, i) ∨
    (∑ i ∈ toggle s a, i) = a + ∑ i ∈ s, i := by
  by_cases h : a ∈ s
  · exact Or.inl (by simpa [toggle, h] using sum_erase_add _ (fun i => i) h)
  · exact Or.inr (by simp [toggle, h])

-- Each change has magnitude exactly the toggled element, including when that element is zero.
private lemma toggle_count (A L : Finset ℕ) (t p : ℕ) (hL : L ⊆ A) (hp : ∀ a ∈ L, a < p) :
    (A.powerset.filter fun s => ∑ i ∈ s, i = t).card * L.card ≤
      (intervalFamily A (t + 1 - p) p).card + (intervalFamily A t p).card := by
  classical
  let F := A.powerset.filter fun s => ∑ i ∈ s, i = t
  let f (x : Finset ℕ × ℕ) := toggle x.1 x.2
  have hinj : ((F ×ˢ L : Finset _) : Set _).InjOn f := by
    rintro ⟨s, a⟩ hs ⟨v, b⟩ hv he
    have hst : (∑ i ∈ s, i) = t := (mem_filter.mp (mem_product.mp hs).1).2
    have hvt : (∑ i ∈ v, i) = t := (mem_filter.mp (mem_product.mp hv).1).2
    change toggle s a = toggle v b at he
    have ha := toggle_sum s a
    have hb := toggle_sum v b
    rw [he] at ha
    have hab : a = b := by omega
    subst b
    have hsv := congrArg (toggle · a) he
    simpa [toggle_twice] using hsv
  have hmap : Set.MapsTo f (F ×ˢ L : Finset _)
      (intervalFamily A (t + 1 - p) p ∪ intervalFamily A t p : Finset _) := by
    rintro ⟨s, a⟩ hs
    obtain ⟨hsF, ha⟩ := mem_product.mp hs
    obtain ⟨hsA, hst⟩ := mem_filter.mp hsF
    change (∑ i ∈ s, i) = t at hst
    have hsA' := mem_powerset.mp hsA
    have hsub : toggle s a ⊆ A := by
      unfold toggle
      split
      · exact (erase_subset _ _).trans hsA'
      · exact insert_subset (hL ha) hsA'
    have ha' := hp a ha
    apply mem_union.mpr
    rcases toggle_sum s a with h | h
    · left
      exact mem_filter.mpr ⟨mem_powerset.mpr hsub, by dsimp [f]; omega⟩
    · right
      exact mem_filter.mpr ⟨mem_powerset.mpr hsub, by dsimp [f]; omega⟩
  simpa only [card_product, F] using
    (card_le_card_of_injOn f hmap hinj).trans (card_union_le _ _)

private lemma split_count (A : Finset ℕ) (t : ℕ) (hn : 2 ≤ A.card) :
    let l := A.card / 2
    let b := A.card - l
    (A.powerset.filter fun s => ∑ i ∈ s, i = t).card * l ≤
      2 * 2 ^ l * b.choose (b / 2) := by
  classical
  let e := A.orderEmbOfFin rfl
  let i : Fin A.card := ⟨A.card / 2, by omega⟩
  let L := (Iio i).map e.toEmbedding
  let B := A \ L
  have hL : L ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl j
  have hlo : ∀ a ∈ L, a < e i := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_map.mp ha
    exact e.strictMono (mem_Iio.mp hj)
  have hhi : ∀ a ∈ B, e i ≤ a := by
    intro a ha
    obtain ⟨haA, haL⟩ := mem_sdiff.mp ha
    obtain ⟨j, rfl⟩ := (show a ∈ Set.range e by
      rwa [A.range_orderEmbOfFin rfl])
    apply e.monotone
    by_contra! hj
    exact haL (mem_map.mpr ⟨j, mem_Iio.mpr hj, rfl⟩)
  have hsize : L.card = A.card / 2 := by simp [L, i]
  have hrest : B.card = A.card - A.card / 2 := by
    simp only [B, card_sdiff_of_subset hL, hsize]
  have hinterval := interval_card A L B (union_sdiff_of_subset hL) (p := e i)
  have h := (toggle_count A L t (e i) hL hlo).trans
    (Nat.add_le_add (hinterval _ hhi) (hinterval _ hhi))
  simpa only [hsize, hrest, ← two_mul, mul_assoc] using h

/--
**Sárközy–Szemerédi bound on subsets with a given sum.** There is a real constant $C$ such that for
every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and every $t \in \mathbb{N}$,
the number of subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is at most
$C \cdot 2^N / N^{3/2}$.

Sárközy and Szemerédi removed the factor $(\log N)^{3/2}$ from the Erdős–Moser bound; Stanley later
found the extremal sets.

Source: T. F. Bloom, Erdős Problems,
Problem #362, https://www.erdosproblems.com/362 (status PROVED (LEAN)); resolution: A. Sárközy and
E. Szemerédi, Über ein Problem von Erdős und Moser, Acta Arith. (1965), 205-208; G. Halász,
Estimates for the concentration function of combinatorial number theory and probability, Period.
Math. Hungar. (1977), 197-211, erdosproblems.com/362: the first question answered by Sárközy and
Szemerédi, the second by Halász as a consequence of a multi-dimensional result.
-/
theorem subsetSumCountBound_holds : subsetSumCountBound := by
  obtain ⟨K, hmiddle⟩ := middle_layer_bound
  refine ⟨max 1 (12 * K), ?_⟩
  intro A t hA
  let N := A.card
  let l := N / 2
  let b := N - l
  let count := (A.powerset.filter fun s => ∑ i ∈ s, i = t).card
  have hN : 0 < N := card_pos.mpr hA
  change (count : ℝ) ≤ max 1 (12 * K) * 2 ^ N / (N : ℝ) ^ (3 / 2 : ℝ)
  by_cases hsmall : N = 1
  · have htriv : count ≤ 2 ^ N :=
      (card_filter_le _ _).trans_eq (card_powerset _)
    calc
      (count : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast htriv
      _ ≤ _ := by simp [hsmall]
  have hb : 0 < b := by dsimp [b, l]; omega
  have hsplit : l + b = N := by dsimp [b, l]; omega
  have h₁ : (N : ℝ) ≤ 3 * l := by exact_mod_cast (show N ≤ 3 * l by dsimp [l]; omega)
  have h₂ : Real.sqrt N ≤ 2 * Real.sqrt b := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
    exact_mod_cast (show N ≤ 4 * b by dsimp [b, l]; omega)
  have hcount : (count : ℝ) * l ≤ 2 * (2 : ℝ) ^ l * (b.choose (b / 2) : ℝ) := by
    exact_mod_cast split_count A t (show 2 ≤ N by omega)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)).mpr
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (Nat.cast_pos.mpr hN), Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc
    (count : ℝ) * (N * Real.sqrt N) ≤ count * ((3 * l) * (2 * Real.sqrt b)) := by gcongr
    _ = 6 * ((count : ℝ) * l) * Real.sqrt b := by ring
    _ ≤ 6 * (2 * (2 : ℝ) ^ l * (b.choose (b / 2) : ℝ)) * Real.sqrt b := by gcongr
    _ = 12 * (2 : ℝ) ^ l * ((b.choose (b / 2) : ℝ) * Real.sqrt b) := by ring
    _ ≤ 12 * (2 : ℝ) ^ l * (K * 2 ^ b) :=
      mul_le_mul_of_nonneg_left (hmiddle b hb) (by positivity)
    _ = 12 * K * 2 ^ N := by rw [← hsplit, pow_add]; ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

end MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362Wanted
