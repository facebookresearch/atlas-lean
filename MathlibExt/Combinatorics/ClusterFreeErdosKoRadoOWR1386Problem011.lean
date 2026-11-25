/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.KatonaCircle
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Exact Erdős-Ko-Rado bound for K(d)-families (Oberwolfach Reports 48/2006)

Oberwolfach workshop Combinatorics, Probability and Computing (2006), Conjecture 3 (D. Mubayi): for
`k ≥ d ≥ 3` and `n ≥ d k/(d - 1)`, every `K(d)`-family `G` of `k`-subsets of `[n]` has `|G| ≤ C(n -
1, k - 1)`, with equality only when all members of `G` share a point.

The theorem `kdFamilyErdosKoRado_holds` proves the sharp bound and its common-point
equality case. The proof uses Currier's weighted induction for `2 * k ≤ n` and
a cyclic-interval argument for `n < 2 * k`.

Source: D. Mubayi, in Combinatorics, Probability and Computing, Oberwolfach Reports 3 (2006), no.
48, p. 2922, Conjecture 3, DOI 10.4171/OWR/2006/48. UnsolvedMath record UM-30000604
(`OWR-1386-011`), dataset ulamai/UnsolvedMath v1.8.0.

A `K(d)`-family (source's definition): any `d` distinct members with union of size at most `2k` have
a common element. `[n]` is `Fin n`; `d` distinct members are an injective map from `Fin d`.
-/

namespace MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011Wanted

@[expose] public section

/-- **$K(d)$-families.** Let $n$, $k$ and $d$ be natural numbers and let
$[n] = \{0, 1, \dots, n - 1\}$. A family $G$ of subsets of $[n]$ is a $K(d)$-family of
$k$-subsets when every member of $G$ has exactly $k$ elements and any $d$ distinct members
$A_1, \dots, A_d$ of $G$ with $|A_1 \cup \dots \cup A_d| \le 2k$ have a common element. -/
def IsKdFamily (n k d : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ G, A.card = k) ∧
    ∀ A : Fin d → Finset (Fin n), Function.Injective A → (∀ i, A i ∈ G) →
      (Finset.univ.biUnion A).card ≤ 2 * k → ∃ x, ∀ i, x ∈ A i

/-- **Mubayi's Erdős–Ko–Rado conjecture for $K(d)$-families.** For all natural numbers $n$, $k$
and $d$ with $3 \le d \le k$ and $n \ge dk/(d - 1)$, every $K(d)$-family $G$ of $k$-subsets of
$[n] = \{0, 1, \dots, n - 1\}$ satisfies $|G| \le \binom{n-1}{k-1}$, and if
$|G| = \binom{n-1}{k-1}$ then some element of $[n]$ lies in every member of $G$.

Source: D. Mubayi, Oberwolfach Report 48/2006, Conjecture 3. -/
def kdFamilyErdosKoRado : Prop :=
  ∀ n k d : ℕ, 3 ≤ d → d ≤ k → (d : ℝ) * k / (d - 1) ≤ n →
    ∀ G : Finset (Finset (Fin n)), IsKdFamily n k d G →
      G.card ≤ (n - 1).choose (k - 1) ∧
        (G.card = (n - 1).choose (k - 1) → ∃ x, ∀ A ∈ G, x ∈ A)

end

open Finset
open scoped FinsetFamily

-- In Currier's weighted induction the marked subfamily contains every member of
-- every cluster. Taking it empty recovers the cluster-free statement.
private def ClustersCovered {α : Type*} [DecidableEq α]
    (k d : ℕ) (G H : Finset (Finset α)) : Prop :=
  ∀ C : Finset (Finset α), C ⊆ G → C.card = d → (C.biUnion id).card ≤ 2 * k →
    (¬ ∃ x, ∀ A ∈ C, x ∈ A) → C ⊆ H

private theorem clustersCovered_empty {n k d : ℕ}
    {G : Finset (Finset (Fin n))} (hG : IsKdFamily n k d G) :
    ClustersCovered k d G ∅ := by
  intro C hCG hCd hCU hCI
  exfalso
  let e : Fin d ≃ C :=
    (Fintype.equivFinOfCardEq (by simpa using hCd : Fintype.card C = d)).symm
  let A : Fin d → Finset (Fin n) := fun i ↦ e i
  have hA : Function.Injective A := fun _ _ h ↦ e.injective (Subtype.ext h)
  have hmem : ∀ i, A i ∈ G := fun i ↦ hCG (e i).property
  have hU : univ.biUnion A = C.biUnion id := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and, id_eq]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨A i, (e i).property, hi⟩,
      fun ⟨S, hS, hxS⟩ ↦ ⟨e.symm ⟨S, hS⟩, by simpa [A] using hxS⟩⟩
  obtain ⟨x, hx⟩ := hG.2 A hA hmem (hU ▸ hCU)
  apply hCI
  exact ⟨x, fun S hS ↦ by simpa [A] using hx (e.symm ⟨S, hS⟩)⟩

private theorem real_threshold_iff {n k d : ℕ} (hd : 1 < d) :
    (d : ℝ) * k / (d - 1) ≤ n ↔ d * k ≤ (d - 1) * n := by
  have hp : 0 < (d : ℝ) - 1 := by exact sub_pos.mpr (by exact_mod_cast hd)
  rw [div_le_iff₀ hp, mul_comm (n : ℝ)]
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [← hcast]
  norm_cast

private theorem lt_ground_of_threshold {n k d : ℕ}
    (hd : 1 < d) (hdk : d ≤ k) (hn : (d : ℝ) * k / (d - 1) ≤ n) :
    k < n := by
  have hl := (real_threshold_iff hd).mp hn
  have he : d * k = (d - 1) * k + k := by
    calc
      d * k = (d - 1 + 1) * k := by congr 1; omega
      _ = _ := by rw [add_mul, one_mul]
  rw [he] at hl
  by_contra! hnk
  have hmul := Nat.mul_le_mul_left (d - 1) hnk
  omega

/-! ### Weighted induction on point links -/

section Links

variable {α : Type*} [DecidableEq α]

private def link (G : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (G.filter fun A ↦ x ∈ A).image (fun A ↦ A.erase x)

private theorem mem_link {G : Finset (Finset α)} {x : α} {D : Finset α} :
    D ∈ link G x ↔ x ∉ D ∧ insert x D ∈ G := by
  simp only [link, mem_image, mem_filter]
  constructor
  · rintro ⟨A, ⟨hA, hx⟩, rfl⟩
    simpa [insert_erase hx] using hA
  · rintro ⟨hx, hA⟩
    exact ⟨insert x D, ⟨hA, mem_insert_self _ _⟩, erase_insert hx⟩

private theorem card_of_mem_link {k : ℕ} {G : Finset (Finset α)} {x : α}
    (hG : ∀ A ∈ G, A.card = k) {D : Finset α} (hD : D ∈ link G x) :
    D.card + 1 = k := by
  obtain ⟨hx, hD⟩ := mem_link.mp hD
  simpa [card_insert_of_notMem hx] using hG _ hD

private def UniqueExtension (G : Finset (Finset α)) (D : Finset α) : Prop :=
  ∃! A, A ∈ G ∧ D ⊆ A

private noncomputable def markedLink
    (G H : Finset (Finset α)) (x : α) : Finset (Finset α) := by
  classical
  exact (link G x).filter fun D ↦ UniqueExtension G D ∨ D ∈ link H x

private theorem mem_markedLink {G H : Finset (Finset α)} {x : α} {D : Finset α} :
    D ∈ markedLink G H x ↔ D ∈ link G x ∧ (UniqueExtension G D ∨ D ∈ link H x) := by
  classical
  exact mem_filter

private theorem clustersCovered_markedLink {k d : ℕ} (hd : 3 ≤ d)
    {G H : Finset (Finset α)} (hG : ∀ A ∈ G, A.card = k)
    (hcover : ClustersCovered k d G H) (x : α) :
    ClustersCovered (k - 1) (d - 1) (link G x) (markedLink G H x) := by
  classical
  intro C hCL hCd hCU hCI D hD
  have hDL := hCL hD
  rw [mem_markedLink]
  refine ⟨hDL, ?_⟩
  by_contra! hnot
  obtain ⟨hxD, hDG⟩ := mem_link.mp hDL
  have hDcard := card_of_mem_link hG hDL
  have hnoH : insert x D ∉ H := fun hH ↦ hnot.2 (mem_link.mpr ⟨hxD, hH⟩)
  have hsecond : ∃ A ∈ G, D ⊆ A ∧ A ≠ insert x D := by
    by_contra! he
    exact hnot.1 ⟨insert x D, ⟨hDG, subset_insert _ _⟩,
      fun A hA ↦ he A hA.1 hA.2⟩
  obtain ⟨A, hAG, hDA, hAne⟩ := hsecond
  have hxA : x ∉ A := by
    intro hxA
    exact hAne (eq_of_subset_of_card_le (insert_subset hxA hDA) (by
      rw [hG A hAG, hG _ hDG])).symm
  have hAinsert : ∃ y, y ∉ D ∧ insert y D = A :=
    exists_eq_insert_iff.2 ⟨hDA, by rw [hG _ hAG, hDcard]⟩
  obtain ⟨y, _, rfl⟩ := hAinsert
  let B := C.image (insert x)
  have hB : ∀ E ∈ B, x ∈ E := by
    intro E hE
    obtain ⟨F, _, rfl⟩ := mem_image.mp hE
    exact mem_insert_self _ _
  have hnew : insert y D ∉ B := fun hy ↦ hxA (hB _ hy)
  have hBinj : Set.InjOn (insert x) (C : Set (Finset α)) := by
    intro E hE F hF he
    have hEx := (mem_link.mp (hCL hE)).1
    have hFx := (mem_link.mp (hCL hF)).1
    simpa only [erase_insert hEx, erase_insert hFx] using congrArg (fun S ↦ S.erase x) he
  let C' := insert (insert y D) B
  have hC'G : C' ⊆ G := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact hAG
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hE
    exact (mem_link.mp (hCL hF)).2
  have hC'd : C'.card = d := by
    change (insert (insert y D) B).card = d
    rw [card_insert_of_notMem hnew, card_image_of_injOn hBinj, hCd]
    omega
  have hC'U : (C'.biUnion id).card ≤ 2 * k := by
    have hsub : C'.biUnion id ⊆ insert x (insert y (C.biUnion id)) := by
      intro z hz
      obtain ⟨E, hE, hzE⟩ := mem_biUnion.mp hz
      rcases mem_insert.mp hE with rfl | hE
      · exact mem_insert_of_mem (mem_insert.mpr ((mem_insert.mp hzE).imp_right
          fun hzD ↦ mem_biUnion.mpr ⟨D, hD, hzD⟩))
      obtain ⟨F, hF, rfl⟩ := mem_image.mp hE
      exact mem_insert.mpr ((mem_insert.mp hzE).imp_right fun hzF ↦
        mem_insert_of_mem (mem_biUnion.mpr ⟨F, hF, hzF⟩))
    exact (card_le_card hsub).trans (by
      have h₁ := card_insert_le x (insert y (C.biUnion id))
      have h₂ := card_insert_le y (C.biUnion id)
      omega)
  have hC'I : ¬ ∃ z, ∀ E ∈ C', z ∈ E := by
    rintro ⟨z, hz⟩
    have hzx : z ≠ x := by
      rintro rfl
      exact hxA (hz _ (mem_insert_self _ _))
    exact hCI ⟨z, fun E hE ↦ mem_of_mem_insert_of_ne
      (hz _ (mem_insert_of_mem (mem_image_of_mem _ hE))) hzx⟩
  exact hnoH (hcover C' hC'G hC'd hC'U hC'I
    (mem_insert_of_mem (mem_image_of_mem _ hD)))

private theorem link_subset_layer {k : ℕ} {U : Finset α} {G : Finset (Finset α)}
    (hG : G ⊆ U.powersetCard k) (x : α) :
    link G x ⊆ (U.erase x).powersetCard (k - 1) := by
  intro D hD
  obtain ⟨hx, hGx⟩ := mem_link.mp hD
  obtain ⟨hsub, hsize⟩ := mem_powersetCard.mp (hG hGx)
  refine mem_powersetCard.mpr ⟨fun y hy ↦ ?_, ?_⟩
  · exact mem_erase.mpr ⟨fun h ↦ hx (h ▸ hy), hsub (mem_insert_of_mem hy)⟩
  · rw [card_insert_of_notMem hx] at hsize
    omega

private theorem card_link (G : Finset (Finset α)) (x : α) :
    (link G x).card = (G.filter fun A ↦ x ∈ A).card := by
  apply card_image_of_injOn
  intro A hA B hB h
  have ha : x ∈ A := (mem_filter.mp hA).2
  have hb : x ∈ B := (mem_filter.mp hB).2
  change A.erase x = B.erase x at h
  rw [← insert_erase ha, ← insert_erase hb, h]

private theorem sum_card_link {k : ℕ} {U : Finset α} {G : Finset (Finset α)}
    (hG : G ⊆ U.powersetCard k) :
    ∑ x ∈ U, (link G x).card = k * G.card := by
  let rel := fun (A : Finset α) (x : α) ↦ x ∈ A
  have count := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow rel (s := G) (t := U)
  have hA (A : Finset α) (hA : A ∈ G) : U.bipartiteAbove rel A = A := by
    ext x
    simp only [mem_bipartiteAbove, rel]
    exact and_iff_right_of_imp (fun hx ↦ (mem_powersetCard.mp (hG hA)).1 hx)
  calc
    _ = ∑ x ∈ U, (G.bipartiteBelow rel x).card := sum_congr rfl fun x _ ↦ card_link G x
    _ = ∑ a ∈ G, (U.bipartiteAbove rel a).card := count.symm
    _ = ∑ _a ∈ G, k := sum_congr rfl fun A hAG ↦
      (congrArg card (hA A hAG)).trans (mem_powersetCard.mp (hG hAG)).2
    _ = _ := by simp [mul_comm]

private noncomputable def uniqueFaces (G : Finset (Finset α)) (U : Finset α) (k : ℕ) :
    Finset (Finset α) := by
  classical
  exact (U.powersetCard (k - 1)).filter (UniqueExtension G)

private theorem unique_degree {k : ℕ} (hk : 0 < k) {U : Finset α} {G : Finset (Finset α)}
    (hG : G ⊆ U.powersetCard k) {D : Finset α} (hD : D ∈ uniqueFaces G U k) :
    ∃! x, x ∈ U ∧ x ∉ D ∧ insert x D ∈ G := by
  classical
  have hD' : D ∈ U.powersetCard (k - 1) ∧ UniqueExtension G D :=
    mem_filter.mp (show D ∈ (U.powersetCard (k - 1)).filter (UniqueExtension G) from hD)
  obtain ⟨A, ⟨hA, hDA⟩, hu⟩ := hD'.2
  have hAc := (mem_powersetCard.mp (hG hA)).2
  have hDc := (mem_powersetCard.mp hD'.1).2
  obtain ⟨x, hxD, rfl⟩ := exists_eq_insert_iff.mpr ⟨hDA, by omega⟩
  refine ⟨x, ⟨(mem_powersetCard.mp (hG hA)).1 (mem_insert_self _ _), hxD, hA⟩, ?_⟩
  intro y hy
  have he := hu (insert y D) ⟨hy.2.2, subset_insert _ _⟩
  exact (mem_insert.mp (he ▸ mem_insert_self y D)).resolve_right hy.2.1

open scoped Classical in
private theorem sum_card_unique_link {k : ℕ} (hk : 0 < k) {U : Finset α}
    {G : Finset (Finset α)} (hG : G ⊆ U.powersetCard k) :
    ∑ x ∈ U, ((link G x).filter (fun D ↦ UniqueExtension G D)).card =
      (uniqueFaces G U k).card := by
  classical
  let rel := fun (x : α) (D : Finset α) ↦ x ∉ D ∧ insert x D ∈ G
  have he (x : α) :
      (uniqueFaces G U k).bipartiteAbove rel x =
      (link G x).filter (UniqueExtension G) := by
    ext D
    simp only [mem_bipartiteAbove, uniqueFaces, mem_filter, rel, mem_link]
    exact ⟨fun ⟨⟨_, hU⟩, hL⟩ ↦ ⟨hL, hU⟩,
      fun ⟨hL, hU⟩ ↦ ⟨⟨powersetCard_mono (erase_subset _ _) (link_subset_layer hG x
        (mem_link.mpr hL)), hU⟩, hL⟩⟩
  rw [← sum_congr rfl (fun x _ ↦ congrArg card (he x)),
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have hb (D : Finset α) (hD : D ∈ uniqueFaces G U k) :
      (U.bipartiteBelow rel D).card = 1 := by
    obtain ⟨x, hx, hu⟩ := unique_degree hk hG hD
    exact card_eq_one.mpr ⟨x, by ext y; exact ⟨fun hy ↦ mem_singleton.mpr
      (hu y ((mem_bipartiteBelow rel).mp hy)), fun hy ↦
      (mem_singleton.mp hy).symm ▸ (mem_bipartiteBelow rel).mpr hx⟩⟩
  rw [sum_congr rfl hb]
  simp

private theorem markedLink_card_sum {k : ℕ} (hk : 0 < k) {U : Finset α}
    {G H : Finset (Finset α)} (hG : G ⊆ U.powersetCard k) (hHG : H ⊆ G) :
    ∑ x ∈ U, (markedLink G H x).card ≤ (uniqueFaces G U k).card + k * H.card := by
  classical
  rw [← sum_card_unique_link hk hG, ← sum_card_link (hHG.trans hG), ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  refine (card_le_card (t := ((link G x).filter (UniqueExtension G)) ∪ link H x) ?_).trans
    (card_union_le _ _)
  intro D hD
  rw [mem_markedLink] at hD
  exact mem_union.mpr (hD.2.imp_left fun h ↦ mem_filter.mpr ⟨hD.1, h⟩)

omit [DecidableEq α] in
private theorem uniqueFaces_card_mul {k : ℕ} (hk : 0 < k) {U : Finset α}
    (hkU : k ≤ U.card) {G : Finset (Finset α)} (hG : G ⊆ U.powersetCard k) :
    (uniqueFaces G U k).card * (U.card - k) ≤ ((U.powersetCard k).card - G.card) * k := by
  classical
  let M := U.powersetCard k \ G
  let F := uniqueFaces G U k
  let rel := fun (D A : Finset α) ↦ D ⊆ A
  rw [← card_sdiff_of_subset hG]
  change F.card * (U.card - k) ≤ M.card * k
  apply card_mul_le_card_mul rel
  · intro D hD
    have hD' : D ∈ U.powersetCard (k - 1) ∧ UniqueExtension G D :=
      mem_filter.mp (show D ∈ (U.powersetCard (k - 1)).filter (UniqueExtension G) from hD)
    obtain ⟨A, hA, hu⟩ := hD'.2
    have hGunique : (G.filter fun B ↦ D ⊆ B).card = 1 := by
      refine card_eq_one.mpr ⟨A, ?_⟩
      ext B
      exact ⟨fun h ↦ mem_singleton.mpr (hu B (mem_filter.mp h)), fun h ↦
        (mem_singleton.mp h).symm ▸ mem_filter.mpr hA⟩
    have hfilt : M.bipartiteAbove rel D =
        ((U.powersetCard k).filter fun B ↦ D ⊆ B) \ (G.filter fun B ↦ D ⊆ B) := by
      ext B
      simp only [M, rel, mem_bipartiteAbove, mem_sdiff, mem_filter]
      tauto
    rw [hfilt, card_sdiff_of_subset (filter_subset_filter _ hG), hGunique,
      card_filter_powersetCard_subset D U k (mem_powersetCard.mp hD'.1).1
        (by rw [(mem_powersetCard.mp hD'.1).2]; omega),
      (mem_powersetCard.mp hD'.1).2, show k - (k - 1) = 1 by omega, Nat.choose_one_right]
    omega
  · intro A hA
    have hAc := (mem_powersetCard.mp (mem_sdiff.mp hA).1).2
    refine (card_le_card (t := A.powersetCard (k - 1)) ?_).trans ?_
    · intro D hDA
      obtain ⟨hDU, hDA⟩ := (mem_bipartiteBelow rel).mp hDA
      exact mem_powersetCard.mpr ⟨hDA, (mem_powersetCard.mp (mem_filter.mp hDU).1).2⟩
    · rw [card_powersetCard, hAc]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp [Nat.choose_succ_self_right]

private theorem choose_mul_rank (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    n * (n - 1).choose (k - 1) = k * n.choose k := by
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_add_cancel (by omega : 1 ≤ k),
    Nat.mul_comm (n.choose k)] using h

private def weight (n k g h : ℕ) : ℝ :=
  (n : ℝ) * g - ((n : ℝ) - k) * h

private theorem sum_weights_le {k : ℕ} (hk : 0 < k) {U : Finset α}
    (hkU : k ≤ U.card) {G H : Finset (Finset α)} (hG : G ⊆ U.powersetCard k)
    (hHG : H ⊆ G) :
    (k : ℝ) * (weight U.card k G.card H.card - U.card.choose k) ≤
      ∑ x ∈ U, weight (U.card - 1) (k - 1) (link G x).card (markedLink G H x).card := by
  have hU : 1 ≤ U.card := by omega
  have hsum := markedLink_card_sum hk hG hHG
  have huniq := uniqueFaces_card_mul hk hkU hG
  rw [card_powersetCard] at huniq
  have hGcard : G.card ≤ U.card.choose k := by simpa using card_le_card hG
  have hreal₁ : (∑ x ∈ U, ((markedLink G H x).card : ℝ)) ≤
      (uniqueFaces G U k).card + (k : ℝ) * H.card := by exact_mod_cast hsum
  have hreal₂ : (uniqueFaces G U k).card * ((U.card : ℝ) - k) ≤
      ((U.card.choose k : ℝ) - G.card) * k := by
    exact_mod_cast (show (uniqueFaces G U k).card * (U.card - k) ≤
      (U.card.choose k - G.card) * k from huniq)
  have hcast₁ : ((U.card - 1 : ℕ) : ℝ) = (U.card : ℝ) - 1 := by
    rw [Nat.cast_sub hU, Nat.cast_one]
  have hcast₂ : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  simp only [weight, hcast₁, hcast₂, sum_sub_distrib, ← mul_sum,
    ← Nat.cast_sum, sum_card_link hG, Nat.cast_mul]
  have hmul := mul_le_mul_of_nonneg_right hreal₁
    (sub_nonneg.mpr (by exact_mod_cast hkU : (k : ℝ) ≤ U.card))
  have hsumcast : ((∑ x ∈ U, (markedLink G H x).card : ℕ) : ℝ) =
      ∑ x ∈ U, ((markedLink G H x).card : ℝ) := Nat.cast_sum _ _
  rw [hsumcast]
  linear_combination hmul + hreal₂

private theorem weighted_induction_step {k d : ℕ} (hd : 3 ≤ d) (hdk : d ≤ k)
    {U : Finset α} (hU : 2 * k ≤ U.card) {G H : Finset (Finset α)}
    (hG : G ⊆ U.powersetCard k) (hHG : H ⊆ G) (hcover : ClustersCovered k d G H)
    (ih : ∀ {V : Finset α} {A B : Finset (Finset α)}, 2 * (k - 1) ≤ V.card →
      A ⊆ V.powersetCard (k - 1) → B ⊆ A → ClustersCovered (k - 1) (d - 1) A B →
      weight V.card (k - 1) A.card B.card ≤ (k - 1 : ℕ) * V.card.choose (k - 1)) :
    weight U.card k G.card H.card ≤ (k : ℝ) * U.card.choose k ∧
      (weight U.card k G.card H.card = (k : ℝ) * U.card.choose k →
        ∀ x ∈ U, weight (U.card - 1) (k - 1) (link G x).card (markedLink G H x).card =
          (k - 1 : ℕ) * (U.card - 1).choose (k - 1)) := by
  have hk : 0 < k := by omega
  have hlocal (x : α) (hx : x ∈ U) :
      weight (U.card - 1) (k - 1) (link G x).card (markedLink G H x).card ≤
        (k - 1 : ℕ) * (U.card - 1).choose (k - 1) := by
    have hcard : (U.erase x).card = U.card - 1 := card_erase_of_mem hx
    simpa only [hcard] using ih (by rw [hcard]; omega) (link_subset_layer hG x)
      (fun _ h ↦ (mem_markedLink.mp h).1)
      (clustersCovered_markedLink hd (fun A hA ↦ (mem_powersetCard.mp (hG hA)).2) hcover x)
  have hlow := sum_weights_le hk (by omega : k ≤ U.card) hG hHG
  have hup := sum_le_sum hlocal
  have hs : (∑ _x ∈ U, ((k - 1 : ℕ) : ℝ) * ((U.card - 1).choose (k - 1) : ℝ)) =
      ((k : ℝ) - 1) * ((k : ℝ) * (U.card.choose k : ℝ)) := by
    have hc : (U.card : ℝ) * ↑((U.card - 1).choose (k - 1)) =
        (k : ℝ) * ↑(U.card.choose k) := by
      exact_mod_cast choose_mul_rank U.card k (by omega : 0 < U.card) hk
    rw [sum_const, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    linear_combination ((k : ℝ) - 1) * hc
  have hup' : (∑ x ∈ U,
      weight (U.card - 1) (k - 1) (link G x).card (markedLink G H x).card) ≤ _ := hup
  rw [hs] at hup'
  have hp : 0 < (k : ℝ) := by exact_mod_cast hk
  refine ⟨(mul_le_mul_iff_right₀ hp).mp ?_, ?_⟩
  · have h := hlow.trans hup'
    linear_combination h
  · intro he x hx
    by_contra! hne
    have hstrict := sum_lt_sum hlocal ⟨x, hx, lt_of_le_of_ne (hlocal x hx) hne⟩
    change (∑ x ∈ U, weight (U.card - 1) (k - 1) (link G x).card
      (markedLink G H x).card) <
        ∑ _x ∈ U, ((k - 1 : ℕ) : ℝ) * ((U.card - 1).choose (k - 1) : ℝ) at hstrict
    rw [hs] at hstrict
    rw [he] at hlow
    linarith

end Links

/-! ### Rigidity when a point link is full -/

section FullLink

variable {α : Type*} [DecidableEq α]

private theorem paired_cluster_of_full_link {k d : ℕ} (hd : 3 ≤ d) (hdk : d ≤ k)
    {U : Finset α} (hU : 2 * k ≤ U.card) {G : Finset (Finset α)} (hG : G ⊆ U.powersetCard k)
    {x : α} (hfull : link G x = (U.erase x).powersetCard (k - 1))
    {A B : Finset α} (hA : A ∈ G) (hB : B ∈ G) (hxA : x ∈ A) (hxB : x ∉ B) :
    ∃ C : Finset (Finset α), C ⊆ G ∧ C.card = d ∧ (C.biUnion id).card ≤ 2 * k ∧
      (¬ ∃ y, ∀ D ∈ C, y ∈ D) ∧ A ∈ C ∧ B ∈ C := by
  have hA' := mem_powersetCard.mp (hG hA)
  have hB' := mem_powersetCard.mp (hG hB)
  obtain ⟨Z, hZ, hZU, hZc⟩ := exists_subsuperset_card_eq (union_subset hA'.1 hB'.1)
    ((card_union_le A B).trans (by rw [hA'.2, hB'.2, two_mul])) hU
  have hxZ : x ∈ Z := hZ (mem_union_left B hxA)
  have hAB : A ∩ B ⊆ Z.erase x := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := mem_inter.mp hy
    exact mem_erase.mpr ⟨fun he ↦ hxB (he ▸ hyB), hZ (mem_union_left _ hyA)⟩
  have hABc : (A ∩ B).card < k := by
    rw [← hA'.2]
    apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, fun he ↦
      hxB (mem_inter.mp (he.symm ▸ hxA)).2⟩
  let P := (Z.erase x) \ (A ∩ B)
  have hPc : k ≤ P.card := by
    rw [card_sdiff_of_subset hAB, card_erase_of_mem hxZ, hZc]
    omega
  let D₀ := (P.powersetCard (k - 1)).image (insert x)
  have hD₀c : k ≤ D₀.card := by
    have hinj : Set.InjOn (insert x) ((P.powersetCard (k - 1) : Finset (Finset α)) :
        Set (Finset α)) := by
      intro S hS T hT he
      have hs : x ∉ S := fun h ↦ (notMem_erase _ _) (sdiff_subset ((mem_powersetCard.mp hS).1 h))
      have ht : x ∉ T := fun h ↦ (notMem_erase _ _) (sdiff_subset ((mem_powersetCard.mp hT).1 h))
      simpa only [erase_insert hs, erase_insert ht] using congrArg (fun R ↦ R.erase x) he
    rw [show D₀.card = _ from card_image_of_injOn hinj, card_powersetCard]
    have hk : k.choose (k - 1) = k := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [Nat.choose_succ_self_right]
    exact hk.ge.trans (Nat.choose_le_choose _ hPc)
  obtain ⟨K, hK, hKc⟩ := exists_subset_card_eq (s := D₀.erase A) (n := d - 2)
    (by
      by_cases ha : A ∈ D₀
      · have := card_erase_add_one ha
        omega
      · rw [erase_eq_of_notMem ha]
        omega)
  have hKprop (D : Finset α) (hD : D ∈ K) :
      x ∈ D ∧ D ∈ G ∧ D ⊆ Z ∧ Disjoint D (A ∩ B) := by
    obtain ⟨S, hS, rfl⟩ := mem_image.mp (mem_erase.mp (hK hD)).2
    obtain ⟨hSP, hSc⟩ := mem_powersetCard.mp hS
    have hSU : S ⊆ U.erase x := by
      intro y hy
      have h := mem_erase.mp (sdiff_subset (hSP hy))
      exact mem_erase.mpr ⟨h.1, hZU h.2⟩
    have hSlink : S ∈ link G x := hfull.symm ▸ mem_powersetCard.mpr ⟨hSU, hSc⟩
    refine ⟨mem_insert_self _ _, (mem_link.mp hSlink).2,
      insert_subset hxZ (hSP.trans (sdiff_subset.trans (erase_subset _ _))), ?_⟩
    rw [disjoint_left]
    intro y hy hyAB
    rcases mem_insert.mp hy with rfl | hy
    · exact hxB (mem_inter.mp hyAB).2
    · exact (mem_sdiff.mp (hSP hy)).2 hyAB
  let C := insert B (insert A K)
  have hAK : A ∉ K := fun h ↦ (notMem_erase _ _) (hK h)
  have hB'not : B ∉ insert A K := by
    intro h
    rcases mem_insert.mp h with he | he
    · exact hxB (he.symm ▸ hxA)
    · exact hxB (hKprop _ he).1
  have hCcard : C.card = d := by
    change (insert B (insert A K)).card = d
    rw [card_insert_of_notMem hB'not, card_insert_of_notMem hAK, hKc]
    omega
  have hAC : A ∈ C := mem_insert_of_mem (mem_insert_self _ _)
  have hBC : B ∈ C := mem_insert_self _ _
  have hCsubG : C ⊆ G := insert_subset hB (insert_subset hA fun D hD ↦ (hKprop D hD).2.1)
  have hCU : C.biUnion id ⊆ Z := by
    intro y hy
    obtain ⟨D, hD, hyD⟩ := mem_biUnion.mp hy
    rcases mem_insert.mp hD with rfl | hD
    · exact hZ (mem_union_right _ hyD)
    rcases mem_insert.mp hD with rfl | hD
    · exact hZ (mem_union_left _ hyD)
    exact (hKprop D hD).2.2.1 hyD
  refine ⟨C, hCsubG, hCcard, (card_le_card hCU).trans hZc.le, ?_, hAC, hBC⟩
  rintro ⟨y, hy⟩
  obtain ⟨D, hD⟩ := card_pos.mp (by rw [hKc]; omega : 0 < K.card)
  exact disjoint_left.mp (hKprop D hD).2.2.2
    (hy D (mem_insert_of_mem (mem_insert_of_mem hD))) (mem_inter.mpr ⟨hy A hAC, hy B hBC⟩)

private theorem eq_of_full_link_of_nonstar {k d : ℕ} (hd : 3 ≤ d) (hdk : d ≤ k)
    {U : Finset α} (hU : 2 * k ≤ U.card) {G H : Finset (Finset α)} (hG : G ⊆ U.powersetCard k)
    (hHG : H ⊆ G) (hcover : ClustersCovered k d G H)
    {x : α} (hxU : x ∈ U) (hfull : link G x = (U.erase x).powersetCard (k - 1))
    {B : Finset α} (hB : B ∈ G) (hxB : x ∉ B) :
    G = H := by
  have hL : (link G x).Nonempty := by
    rw [hfull, powersetCard_nonempty]
    rw [card_erase_of_mem hxU]
    omega
  obtain ⟨D, hD⟩ := hL
  have hA₀ := (mem_link.mp hD).2
  have hx₀ := mem_insert_self x D
  refine subset_antisymm (fun A hA ↦ ?_) hHG
  by_cases hxA : x ∈ A
  · obtain ⟨C, hCG, hCd, hCU, hCI, hAC, _⟩ :=
      paired_cluster_of_full_link hd hdk hU hG hfull hA hB hxA hxB
    exact hcover C hCG hCd hCU hCI hAC
  · obtain ⟨C, hCG, hCd, hCU, hCI, _, hAC⟩ :=
      paired_cluster_of_full_link hd hdk hU hG hfull hA₀ hA hx₀ hxA
    exact hcover C hCG hCd hCU hCI hAC

end FullLink

/-! ### Pairwise base case and the sparse range -/

section WeightedBase

open Finset.Colex

private theorem exists_initial_segment {n r m : ℕ} (t : Fin n)
    (hm : m ≤ t.val.choose r) :
    ∃ C : Finset (Finset (Fin n)), IsInitSeg C r ∧ C ⊆ (Iio t).powersetCard r ∧ C.card = m := by
  classical
  let Q := ((Iio t).powersetCard r).image toColex
  have hQ : Q.card = t.val.choose r := by
    rw [card_image_of_injective _ toColex.injective, card_powersetCard, Fin.card_Iio]
  let e := (Q.orderEmbOfFin rfl)
  let f := ((Fin.castLEEmb (hQ.symm ▸ hm)).trans e.toEmbedding).trans ofColex.toEmbedding
  let C := (univ : Finset (Fin m)).map f
  have hf (j : Fin m) : f j ∈ (Iio t).powersetCard r := by
    have h := Q.orderEmbOfFin_mem rfl (Fin.castLEEmb (hQ.symm ▸ hm) j)
    obtain ⟨S, hS, he⟩ := mem_image.mp h
    have he' : S = f j := by
      change S = ofColex (Q.orderEmbOfFin rfl (Fin.castLEEmb (hQ.symm ▸ hm) j))
      simpa only [ofColex_toColex] using congrArg ofColex he
    exact he' ▸ hS
  have hC : C ⊆ (Iio t).powersetCard r := by
    intro A hA
    obtain ⟨j, _, rfl⟩ := mem_map.mp hA
    exact hf j
  refine ⟨C, ⟨fun A hA ↦ (mem_powersetCard.mp (hC hA)).2, ?_⟩, hC, by simp [C]⟩
  intro A B hA hBA
  obtain ⟨j, _, rfl⟩ := mem_map.mp hA
  have hBin : B ∈ (Iio t).powersetCard r := mem_powersetCard.mpr
    ⟨fun i hi ↦ mem_Iio.mpr (forall_lt_mono hBA.1.le
      (fun a ha ↦ mem_Iio.mp ((mem_powersetCard.mp (hf j)).1 ha)) i hi), hBA.2⟩
  have hBQ : toColex B ∈ Q := mem_image_of_mem _ hBin
  let i := (Q.orderIsoOfFin rfl).symm ⟨toColex B, hBQ⟩
  have hi : e i = toColex B := congrArg Subtype.val ((Q.orderIsoOfFin rfl).apply_symm_apply _)
  have hij : i < Fin.castLEEmb (hQ.symm ▸ hm) j := by
    apply e.lt_iff_lt.mp
    rw [hi]
    simpa [f] using hBA.1
  have him : i.val < m := lt_trans hij j.isLt
  exact mem_map.mpr ⟨⟨i.val, him⟩, mem_univ _, by simpa [f] using congrArg ofColex hi⟩

private theorem shadow_rank_mem {α : Type*} [DecidableEq α] {r k : ℕ}
    {U : Finset α} {G : Finset (Finset α)} (hk : k ≤ r) (hG : G ⊆ U.powersetCard r)
    {D : Finset α} :
    D ∈ ∂^[r - k] G ↔ D.card = k ∧ ∃ A ∈ G, D ⊆ A := by
  rw [mem_shadow_iterate_iff_exists_mem_card_add]
  constructor
  · rintro ⟨A, hA, hDA, he⟩
    exact ⟨by have h := (mem_powersetCard.mp (hG hA)).2; omega, A, hA, hDA⟩
  · rintro ⟨hd, A, hA, hDA⟩
    exact ⟨A, hA, hDA, by
      rw [hd, (mem_powersetCard.mp (hG hA)).2]
      omega⟩

private theorem initial_segment_boundary {n r : ℕ} {t : Fin n}
    {C : Finset (Finset (Fin n))} (hC : IsInitSeg C r)
    (hCU : C ⊆ (Iio t).powersetCard r) (hc : C.Nonempty)
    (hproper : C.card < t.val.choose r) :
    ∃ A ∈ C, ∃ B ∈ (Iio t).powersetCard r \ C, (A ∩ B).card = r - 1 := by
  classical
  have hM : (((Iio t).powersetCard r) \ C).Nonempty := by
    apply card_pos.mp
    rwa [card_sdiff_of_subset hCU, card_powersetCard, Fin.card_Iio, Nat.sub_pos_iff_lt]
  obtain ⟨B, hB, hmin⟩ := exists_min_image _ toColex hM
  obtain ⟨T, hT⟩ := hc
  have hBT : toColex T < toColex B := by
    have hnot := (mem_sdiff.mp hB).2
    rcases lt_trichotomy (toColex T) (toColex B) with h | h | h
    · exact h
    · exact (hnot (toColex.injective h ▸ hT)).elim
    · exact (hnot (hC.2 hT ⟨h, (mem_powersetCard.mp (mem_sdiff.mp hB).1).2⟩)).elim
  have hBc := (mem_powersetCard.mp (mem_sdiff.mp hB).1).2
  have hTc := hC.1 hT
  obtain ⟨y, hy, _, hTy⟩ := toColex_lt_toColex_iff_exists_forall_lt.mp hBT
  have hxE : (T \ B).Nonempty := by
    by_contra! he
    have hsub : T ⊆ B := sdiff_eq_empty_iff_subset.mp he
    exact (ne_of_lt hBT) (congrArg toColex (eq_of_subset_of_card_le hsub (by rw [hBc, hTc])))
  obtain ⟨x, hx⟩ := hxE
  have hxB : x ∉ B := (mem_sdiff.mp hx).2
  have hyB : y ∈ B := hy
  let A := insert x (B.erase y)
  have hAB : toColex A < toColex B := by
    rw [← insert_erase hyB]
    exact (insert_lt_insert (notMem_mono (erase_subset _ _) hxB) (notMem_erase _ _)).mpr
      (hTy x (mem_sdiff.mp hx).1 hxB)
  have hAc : A.card = r := by
    rw [card_insert_of_notMem (notMem_mono (erase_subset _ _) hxB), card_erase_add_one hyB, hBc]
  have hAU : A ∈ (Iio t).powersetCard r := mem_powersetCard.mpr
    ⟨insert_subset ((mem_powersetCard.mp (hCU hT)).1 (mem_sdiff.mp hx).1)
      ((erase_subset _ _).trans (mem_powersetCard.mp (mem_sdiff.mp hB).1).1), hAc⟩
  have hA : A ∈ C := by
    by_contra hA
    exact (not_le_of_gt hAB) (hmin A (mem_sdiff.mpr ⟨hAU, hA⟩))
  refine ⟨A, hA, B, hB, ?_⟩
  have he : A ∩ B = B.erase y := by
    ext z
    simp only [A, mem_inter, mem_insert, mem_erase]
    aesop
  rw [he, card_erase_of_mem hyB, hBc]

private theorem shadow_incidence {α : Type*} [DecidableEq α] {k r : ℕ}
    {U : Finset α} (hkr : k ≤ r) {C : Finset (Finset α)} (hC : C ⊆ U.powersetCard r) :
    C.card * r.choose k ≤
      (∂^[r - k] C).card * (U.card - k).choose (r - k) ∧
    ((∃ A ∈ C, ∃ B ∈ U.powersetCard r \ C, k ≤ (A ∩ B).card) →
      C.card * r.choose k < (∂^[r - k] C).card * (U.card - k).choose (r - k)) := by
  classical
  let S := ∂^[r - k] C
  let rel := fun (A D : Finset α) ↦ D ⊆ A
  have hA (A : Finset α) (hA : A ∈ C) : S.bipartiteAbove rel A = A.powersetCard k := by
    ext D
    simp only [mem_bipartiteAbove, S, shadow_rank_mem hkr hC, rel, mem_powersetCard]
    exact ⟨fun h ↦ ⟨h.2, h.1.1⟩, fun h ↦ ⟨⟨h.2, A, hA, h.1⟩, h.1⟩⟩
  have hD (D : Finset α) (hD : D ∈ S) :
      (C.bipartiteBelow rel D).card ≤ (U.card - k).choose (r - k) := by
    obtain ⟨hDc, A, hA, hDA⟩ := (shadow_rank_mem hkr hC).mp hD
    have hDU := hDA.trans (mem_powersetCard.mp (hC hA)).1
    have hble : C.bipartiteBelow rel D ⊆ (U.powersetCard r).filter (fun B ↦ D ⊆ B) :=
      filter_subset_filter _ hC
    simpa only [card_filter_powersetCard_subset D U r hDU (hDc ▸ hkr), hDc] using
      card_le_card hble
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow rel (s := C) (t := S)
  have hcard : C.card * r.choose k = ∑ D ∈ S, (C.bipartiteBelow rel D).card := by
    rw [← hsum, sum_congr rfl (fun A hAC ↦ congrArg card (hA A hAC)),
      sum_congr rfl (fun A hAC ↦ by rw [card_powersetCard, (mem_powersetCard.mp (hC hAC)).2]),
      sum_const, nsmul_eq_mul]
    simp
  change C.card * r.choose k ≤ S.card * _ ∧ _
  rw [hcard, ← show ∑ _D ∈ S, (U.card - k).choose (r - k) = S.card * _ by simp]
  refine ⟨sum_le_sum hD, ?_⟩
  rintro ⟨A, hAC, B, hB, hAB⟩
  obtain ⟨D, hDAB, hDc⟩ := exists_subset_card_eq hAB
  have hDsubA := hDAB.trans inter_subset_left
  have hDS : D ∈ S := (shadow_rank_mem hkr hC).mpr ⟨hDc, A, hAC, hDsubA⟩
  have hDU := hDsubA.trans (mem_powersetCard.mp (hC hAC)).1
  refine sum_lt_sum hD ⟨D, hDS, ?_⟩
  have hlt : C.bipartiteBelow rel D ⊂ (U.powersetCard r).filter (fun B ↦ D ⊆ B) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset_filter _ hC, fun he ↦ ?_⟩
    have hBF := mem_filter.mpr ⟨(mem_sdiff.mp hB).1, hDAB.trans inter_subset_right⟩
    exact (mem_sdiff.mp hB).2 ((mem_bipartiteBelow rel).mp (he ▸ hBF)).1
  simpa only [card_filter_powersetCard_subset D U r hDU (hDc ▸ hkr), hDc] using
    card_lt_card hlt

-- The shadow of a colex initial segment gives a strict incidence bound as soon as
-- the segment meets the last point of the containing layer.
private theorem shadow_comparison {n k : ℕ} {U : Finset (Fin n)} (hk : 0 < k)
    (hU : 2 * k < U.card) {F : Finset (Finset (Fin n))}
    (hF : F ⊆ U.powersetCard (U.card - k)) (hFc : F.card ≤ (U.card - 1).choose (k - 1)) :
    F.card * (U.card - k) ≤ (∂^[U.card - k - k] F).card * k ∧
      (0 < F.card → F.card < (U.card - 1).choose (k - 1) →
        F.card * (U.card - k) < (∂^[U.card - k - k] F).card * k) := by
  let N := U.card
  let r := N - k
  let q := N - 1
  have hrk : k < r := by omega
  have hrq : r ≤ q := by omega
  have ht : q < n := by
    have hc : U.card ≤ n := by simpa using U.card_le_univ
    omega
  let t : Fin n := ⟨q, ht⟩
  have hsym : q.choose r = q.choose (k - 1) := by
    rw [show r = q - (k - 1) by omega, Nat.choose_symm (by omega)]
  obtain ⟨C, hCinit, hCU, hCc⟩ :=
    exists_initial_segment (r := r) t (by change F.card ≤ q.choose r; rwa [hsym])
  have hkk : (∂^[r - k] C).card ≤ (∂^[r - k] F).card :=
    iterated_kk (fun A hA ↦ (mem_powersetCard.mp (hF hA)).2) hCc.le hCinit
  have hinc := shadow_incidence hrk.le hCU
  simp only [Fin.card_Iio] at hinc
  change C.card * r.choose k ≤ (∂^[r - k] C).card * (q - k).choose (r - k) ∧ _ at hinc
  have hbin : r.choose k * k = (q - k).choose (r - k) * r := by
    have h₁ : q.choose r * r.choose k = q.choose k * (q - k).choose (r - k) :=
      Nat.choose_mul hrk.le
    have h₂ : q.choose k * k = q.choose (k - 1) * r := by
      have := Nat.choose_succ_right_eq q (k - 1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ k), show q - (k - 1) = r by omega] at this
    apply Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hrq)
    calc
      q.choose r * (r.choose k * k) = (q.choose r * r.choose k) * k := by ring
      _ = (q.choose k * k) * (q - k).choose (r - k) := by rw [h₁]; ring
      _ = q.choose r * ((q - k).choose (r - k) * r) := by rw [h₂, hsym]; ring
  let e := (q - k).choose (r - k)
  have he : 0 < e := Nat.choose_pos (by omega)
  constructor
  · apply Nat.le_of_mul_le_mul_right _ he
    have h := Nat.mul_le_mul_right k (hinc.1.trans (Nat.mul_le_mul_right e hkk))
    rw [hCc, mul_assoc, hbin] at h
    simpa only [e, mul_assoc, mul_left_comm, mul_comm] using h
  · intro hF₀ hFl
    have hCb := initial_segment_boundary hCinit hCU (card_pos.mp (hCc.symm ▸ hF₀))
      (by change C.card < q.choose r; rwa [hCc, hsym])
    obtain ⟨A, hAC, B, hB, hab⟩ := hCb
    have h := hinc.2 ⟨A, hAC, B, hB, by omega⟩
    have h' := Nat.mul_lt_mul_of_pos_right (h.trans_le (Nat.mul_le_mul_right e hkk)) hk
    have heq : F.card * r * e < (∂^[r - k] F).card * k * e := by
      rw [hCc, mul_assoc, hbin] at h'
      simpa only [e, mul_assoc, mul_left_comm, mul_comm] using h'
    exact Nat.lt_of_mul_lt_mul_right heq

private theorem pascal_pred {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := by
  have h := Nat.choose_succ_succ (n - 1) (k - 1)
  have hn' : (n - 1).succ = n := by omega
  have hk' : (k - 1).succ = k := by omega
  rwa [hn', hk'] at h

private theorem weighted_pair_base {n k : ℕ} {U : Finset (Fin n)} (hk : 2 ≤ k)
    (hU : 2 * k ≤ U.card) {G H : Finset (Finset (Fin n))}
    (hG : G ⊆ U.powersetCard k) (hHG : H ⊆ G)
    (hcover : ClustersCovered k 2 G H) :
    weight U.card k G.card H.card ≤ (k : ℝ) * U.card.choose k ∧
      (2 * k < U.card → weight U.card k G.card H.card = (k : ℝ) * U.card.choose k →
        G.card = U.card.choose k ∨ G.card = (U.card - 1).choose (k - 1)) := by
  classical
  let N := U.card
  let r := N - k
  let L := U.powersetCard k
  let M := L \ G
  let S := G \ H
  let F := S.image (fun A ↦ U \ A)
  have hAcard (A : Finset (Fin n)) (hA : A ∈ G) : A.card = k :=
    (mem_powersetCard.mp (hG hA)).2
  have hAsub (A : Finset (Fin n)) (hA : A ∈ G) : A ⊆ U :=
    (mem_powersetCard.mp (hG hA)).1
  have hF : F ⊆ U.powersetCard r := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hD
    have ha := (mem_sdiff.mp hA).1
    exact mem_powersetCard.mpr
      ⟨sdiff_subset, by rw [card_sdiff_of_subset (hAsub A ha), hAcard A ha]⟩
  have hFc : F.card = S.card := by
    apply card_image_of_injOn
    intro A hA B hB he
    change U \ A = U \ B at he
    have ha := hAsub A (mem_sdiff.mp hA).1
    have hb := hAsub B (mem_sdiff.mp hB).1
    have hd (X : Finset (Fin n)) (hX : X ⊆ U) : U \ (U \ X) = X := by
      ext x
      simp only [mem_sdiff]
      exact ⟨fun h ↦ by tauto, fun h ↦ ⟨hX h, by tauto⟩⟩
    simpa only [hd A ha, hd B hb] using congrArg (fun C ↦ U \ C) he
  have hN : N ≤ n := by simpa [N] using U.card_le_univ
  have hadd : r + k = N := by omega
  have hkr : k ≤ r := by omega
  have hr : r ≤ N - 1 := by omega
  let Y := ∂^[r - k] F
  have hdisj (A B : Finset (Fin n)) (hA : A ∈ G) (hB : B ∈ S) : ¬ Disjoint A B := by
    intro hab
    have hBG := (mem_sdiff.mp hB).1
    have hne : A ≠ B := by
      intro he
      subst B
      have h := disjoint_self.mp hab
      have := hAcard A hA
      simp [h] at this
      omega
    have hpair : ({A, B} : Finset (Finset (Fin n))) ⊆ G :=
      insert_subset hA (singleton_subset_iff.mpr hBG)
    have hcard : ({A, B} : Finset (Finset (Fin n))).card = 2 := by simp [hne]
    have hu : (({A, B} : Finset (Finset (Fin n))).biUnion id).card ≤ 2 * k := by
      simpa [biUnion_insert, hAcard A hA, hAcard B hBG, two_mul] using card_union_le A B
    have hi : ¬ ∃ x, ∀ C ∈ ({A, B} : Finset (Finset (Fin n))), x ∈ C := by
      rintro ⟨x, hx⟩
      exact disjoint_left.mp hab (hx A (by simp)) (hx B (by simp))
    exact (mem_sdiff.mp hB).2 (hcover _ hpair hcard hu hi (by simp))
  have hY : Y ⊆ M := by
    intro D hD
    obtain ⟨hDc, E, hE, hDE⟩ := (shadow_rank_mem hkr hF).mp hD
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hE
    refine mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨hDE.trans sdiff_subset, hDc⟩, fun hDG ↦ ?_⟩
    exact hdisj D B hDG hB (disjoint_of_subset_left hDE disjoint_sdiff_self_left)
  have hMc : M.card = N.choose k - G.card := by rw [card_sdiff_of_subset hG, card_powersetCard]
  have hGle : G.card ≤ N.choose k := by simpa [N] using card_le_card hG
  have hSc : S.card = G.card - H.card := card_sdiff_of_subset hHG
  have hSle : S.card ≤ G.card := card_le_card sdiff_subset
  have hFbound : F.card ≤ (N - 1).choose (k - 1) := by
    by_contra! h
    have hsym : (N - 1).choose r = (N - 1).choose (k - 1) := by
      rw [show r = N - 1 - (k - 1) by omega, Nat.choose_symm (by omega)]
    have hKK := kruskal_katona_lovasz_form (i := r - k) (r := r) (k := N - 1)
      (by omega) hr (by omega)
      (fun B hB ↦ (mem_powersetCard.mp (hF hB)).2) (hsym ▸ h.le)
    rw [show r - (r - k) = k by omega] at hKK
    have hc := hKK.trans (card_le_card hY)
    have hpas := pascal_pred (n := N) (k := k) (by omega) (by omega)
    rw [hMc] at hc
    rw [hFc] at h
    omega
  have hcomp : F.card * r ≤ M.card * k := by
    by_cases he : 2 * k = N
    · have he' : r = k := by omega
      simpa [Y, he'] using Nat.mul_le_mul_right k (card_le_card hY)
    · exact (shadow_comparison (by omega) (by omega) hF hFbound).1.trans
        (Nat.mul_le_mul_right k (card_le_card hY))
  have hKN : k ≤ N := by omega
  have hcmpcast : (S.card : ℝ) * ((N : ℝ) - k) ≤ ((N.choose k : ℝ) - G.card) * k := by
    rw [hFc, hMc] at hcomp
    rw [← Nat.cast_sub hKN, ← Nat.cast_sub hGle]
    exact_mod_cast (show S.card * (N - k) ≤ (N.choose k - G.card) * k from hcomp)
  have hScast : (S.card : ℝ) = (G.card : ℝ) - H.card := by
    rw [hSc, Nat.cast_sub (card_le_card hHG)]
  rw [hScast] at hcmpcast
  refine ⟨by unfold weight; change (N : ℝ) * _ - ((N : ℝ) - k) * _ ≤ _; linarith, ?_⟩
  intro hstrict he
  by_cases h0 : F.card = 0
  · left
    have hHC : H.card = G.card := by
      rw [hFc, hSc] at h0
      have := card_le_card hHG
      omega
    rw [weight, hHC] at he
    have hk' : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have heq : (G.card : ℝ) = (N.choose k : ℝ) := by
      apply mul_left_cancel₀ hk'.ne'
      linarith
    exact_mod_cast heq
  right
  have hmax : F.card = (N - 1).choose (k - 1) := by
    by_contra h
    have hh := (shadow_comparison (by omega) hstrict hF hFbound).2
      (Nat.pos_of_ne_zero h0) (lt_of_le_of_ne hFbound h)
    have hlt := hh.trans_le (Nat.mul_le_mul_right k (card_le_card hY))
    rw [hFc, hMc] at hlt
    have hreal : (S.card : ℝ) * ((N : ℝ) - k) < ((N.choose k : ℝ) - G.card) * k := by
      rw [← Nat.cast_sub hKN, ← Nat.cast_sub hGle]
      exact_mod_cast (show S.card * (N - k) < (N.choose k - G.card) * k from hlt)
    rw [hScast] at hreal
    unfold weight at he
    change (N : ℝ) * _ - ((N : ℝ) - k) * _ = _ at he
    linarith
  have hstar : (N : ℝ) * ((N - 1).choose (k - 1) : ℝ) = (k : ℝ) * N.choose k := by
    exact_mod_cast choose_mul_rank N k (by omega : 0 < N) (by omega : 0 < k)
  rw [hFc] at hmax
  have hS : ((N - 1).choose (k - 1) : ℝ) = (G.card : ℝ) - H.card := by
    exact (congrArg (fun m : ℕ ↦ (m : ℝ)) hmax).symm.trans hScast
  rw [hS] at hstar
  unfold weight at he
  change (N : ℝ) * _ - ((N : ℝ) - k) * _ = _ at he
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hz : (H.card : ℝ) = 0 := by
    apply mul_left_cancel₀ hk'.ne'
    linarith
  have hHC : H.card = 0 := by exact_mod_cast hz
  simpa [hSc, hHC] using hmax

-- Currier's weighted theorem is proved by induction on the cluster size.
private theorem weighted_clusters {n k d : ℕ} (hd : 2 ≤ d) (hdk : d ≤ k)
    {U : Finset (Fin n)} (hU : 2 * k ≤ U.card)
    {G H : Finset (Finset (Fin n))} (hG : G ⊆ U.powersetCard k) (hHG : H ⊆ G)
    (hcov : ClustersCovered k d G H) :
    weight U.card k G.card H.card ≤ (k : ℝ) * U.card.choose k ∧
      (2 * k < U.card ∨ 3 ≤ d →
        weight U.card k G.card H.card = (k : ℝ) * U.card.choose k →
        (G.card = U.card.choose k ∨ G.card = (U.card - 1).choose (k - 1)) ∧
          (H = ∅ → 3 ≤ d → ∃ x, ∀ A ∈ G, x ∈ A)) := by
  induction d using Nat.strong_induction_on generalizing k U G H with
  | ind d ih =>
    by_cases hd₂ : d = 2
    · subst d
      obtain ⟨hle, heq⟩ := weighted_pair_base hdk hU hG hHG hcov
      exact ⟨hle, fun h he ↦ ⟨heq (h.resolve_right (by omega)) he, fun _ hh ↦ by omega⟩⟩
    have hd₃ : 3 ≤ d := by omega
    have hk : 0 < k := by omega
    have hcard (x : Fin n) (hx : x ∈ U) : (U.erase x).card = U.card - 1 :=
      card_erase_of_mem hx
    have hrecur {V : Finset (Fin n)} {A B : Finset (Finset (Fin n))}
        (hV : 2 * (k - 1) ≤ V.card) (hVA : A ⊆ V.powersetCard (k - 1)) (hAB : B ⊆ A)
        (hcover : ClustersCovered (k - 1) (d - 1) A B) :=
      ih (d - 1) (by omega) (by omega) (by omega) hV hVA hAB hcover
    obtain ⟨hbound, hstep⟩ := weighted_induction_step hd₃ hdk hU hG hHG hcov
      (fun h₁ h₂ h₃ h₄ ↦ (hrecur h₁ h₂ h₃ h₄).1)
    refine ⟨hbound, fun _ he ↦ ?_⟩
    have hcpos : 0 < U.card := by omega
    have hchoose := choose_mul_rank U.card k hcpos hk
    have hsreal : (U.card : ℝ) * ((U.card - 1).choose (k - 1) : ℝ) =
        (k : ℝ) * U.card.choose k := by exact_mod_cast hchoose
    have hNpos : 0 < (U.card : ℝ) := by exact_mod_cast hcpos
    have hGe : (U.card - 1).choose (k - 1) ≤ G.card := by
      have hnon : 0 ≤ ((U.card : ℝ) - k) * H.card :=
        mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (show k ≤ U.card by omega))) (by positivity)
      have hle : (U.card : ℝ) * ((U.card - 1).choose (k - 1) : ℝ) ≤
          (U.card : ℝ) * G.card := by
        unfold weight at he
        linarith
      have hcancel := (mul_le_mul_iff_right₀ hNpos).mp hle
      exact_mod_cast hcancel
    have hfull : ∃ x ∈ U, (link G x).card = (U.card - 1).choose (k - 1) := by
      by_contra! hn
      have hsmall (x : Fin n) (hx : x ∈ U) :
          (link G x).card = (U.card - 2).choose (k - 2) := by
        have hV : 2 * (k - 1) < (U.erase x).card := by rw [hcard x hx]; omega
        have hrec := (hrecur hV.le (link_subset_layer hG x)
          (fun _ h ↦ (mem_markedLink.mp h).1)
          (clustersCovered_markedLink hd₃ (fun A hA ↦ (mem_powersetCard.mp (hG hA)).2) hcov x)).2
          (Or.inl hV)
        have hloc : weight (U.erase x).card (k - 1) (link G x).card (markedLink G H x).card =
            (k - 1 : ℕ) * (U.erase x).card.choose (k - 1) := by
          rw [hcard x hx]
          exact hstep he x hx
        have hsize := (hrec hloc).1
        rw [hcard x hx] at hsize
        rcases hsize with h | h
        · exact (hn x hx h).elim
        · simpa only [show U.card - 1 - 1 = U.card - 2 by omega,
            show k - 1 - 1 = k - 2 by omega] using h
      have hsum : k * G.card = U.card * (U.card - 2).choose (k - 2) := by
        rw [← sum_card_link hG, sum_congr rfl hsmall, sum_const, nsmul_eq_mul]
        simp
      have hc : (U.card - 1) * (U.card - 2).choose (k - 2) =
          (k - 1) * (U.card - 1).choose (k - 1) := by
        simpa only [show U.card - 1 - 1 = U.card - 2 by omega, show k - 1 - 1 = k - 2 by omega]
          using choose_mul_rank (U.card - 1) (k - 1) (by omega) (by omega)
      have hlt : U.card * (U.card - 2).choose (k - 2) <
          k * (U.card - 1).choose (k - 1) := by
        have hbasic : U.card * (k - 1) < k * (U.card - 1) := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, mul_one, mul_one,
            mul_comm U.card k]
          have hm : 1 * U.card ≤ k * U.card := Nat.mul_le_mul_right U.card (show 1 ≤ k by omega)
          rw [one_mul] at hm
          omega
        have harr := Nat.mul_lt_mul_of_pos_right hbasic
          (Nat.choose_pos (by omega : k - 1 ≤ U.card - 1))
        apply Nat.lt_of_mul_lt_mul_right
        calc
          (U.card * (U.card - 2).choose (k - 2)) * (U.card - 1) =
              (U.card * (k - 1)) * (U.card - 1).choose (k - 1) := by
            rw [mul_assoc, mul_comm ((U.card - 2).choose (k - 2)) (U.card - 1), hc, ← mul_assoc]
          _ < _ := by simpa only [mul_assoc, mul_comm (U.card - 1)] using harr
      exact (not_le_of_gt hlt) (hsum ▸ Nat.mul_le_mul_left k hGe)
    obtain ⟨x, hx, hxC⟩ := hfull
    have hxL : link G x = (U.erase x).powersetCard (k - 1) := by
      apply eq_of_subset_of_card_le (link_subset_layer hG x)
      rw [card_powersetCard, hcard x hx, hxC]
    by_cases hstar : ∀ A ∈ G, x ∈ A
    · have hGcard : G.card = (U.card - 1).choose (k - 1) := by
        simpa [card_link, filter_eq_self.mpr hstar] using hxC
      exact ⟨Or.inr hGcard, fun _ _ ↦ ⟨x, hstar⟩⟩
    push Not at hstar
    obtain ⟨B, hB, hBx⟩ := hstar
    have hGH := eq_of_full_link_of_nonstar hd₃ hdk hU hG hHG hcov hx hxL hB hBx
    rw [weight, ← hGH] at he
    have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
    have heq : (G.card : ℝ) = (U.card.choose k : ℝ) := by
      apply mul_left_cancel₀ hkp.ne'
      linarith
    have hGcz : G.card = U.card.choose k := by exact_mod_cast heq
    refine ⟨Or.inl hGcz, fun hempty _ ↦ ?_⟩
    have hGempty := hGH.trans hempty
    exact False.elim ((Nat.choose_pos (by omega : k ≤ U.card)).ne'
      (by simpa [hGempty] using hGcz.symm))

private theorem kd_in_sparse_range {n k d : ℕ} (hd : 3 ≤ d) (hdk : d ≤ k) (hU : 2 * k ≤ n)
    {G : Finset (Finset (Fin n))} (hG : IsKdFamily n k d G) :
    G.card ≤ (n - 1).choose (k - 1) ∧
      (G.card = (n - 1).choose (k - 1) → ∃ x, ∀ A ∈ G, x ∈ A) := by
  have hk : 0 < k := by omega
  have hn : 0 < n := by omega
  have hsub : G ⊆ (univ : Finset (Fin n)).powersetCard k :=
    fun A hA ↦ mem_powersetCard.mpr ⟨subset_univ _, hG.1 A hA⟩
  have hW := weighted_clusters (by omega : 2 ≤ d) hdk
    (by simpa using hU : 2 * k ≤ (univ : Finset (Fin n)).card) hsub
    (empty_subset _) (clustersCovered_empty hG)
  rw [card_univ, Fintype.card_fin] at hW
  have hchoose : (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = (k : ℝ) * n.choose k :=
    by exact_mod_cast choose_mul_rank n k hn hk
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← hchoose] at hW
  have hle : (n : ℝ) * G.card ≤ (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) := by
    simpa [weight] using hW.1
  refine ⟨?_, ?_⟩
  · have h := (mul_le_mul_iff_right₀ hnp).mp hle
    exact_mod_cast h
  · intro he
    exact ((hW.2 (Or.inr hd) (by simp [weight, he])).2 rfl hd)

end WeightedBase

/-! ### Cyclic intervals for the dense range -/

section Circle

variable {n : ℕ} [NeZero n]

private def arc (r : ℕ) (a : Fin n) : Finset (Fin n) :=
  univ.image fun j : Fin r ↦ a + Fin.ofNat n j.val

private theorem mem_arc {r : ℕ} {a x : Fin n} :
    x ∈ arc r a ↔ ∃ j : ℕ, j < r ∧ a + Fin.ofNat n j = x := by
  simp only [arc, mem_image, mem_univ, true_and]
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨j, j.isLt, hj⟩, fun ⟨j, hr, hj⟩ ↦ ⟨⟨j, hr⟩, hj⟩⟩

private theorem card_arc {r : ℕ} (hr : r ≤ n) (a : Fin n) : (arc r a).card = r := by
  rw [arc, card_image_of_injective]
  · simp
  intro i j hij
  have h := congrArg Fin.val (add_left_cancel hij)
  change i.val % n = j.val % n at h
  rw [Nat.mod_eq_of_lt (i.isLt.trans_le hr),
    Nat.mod_eq_of_lt (j.isLt.trans_le hr)] at h
  exact Fin.ext h

private theorem mem_arc_of_nat {r a x j : ℕ} (ha : a < n) (hx : x < n)
    (hj : j < r) (h : a + j = x ∨ a + j = x + n) :
    (⟨x, hx⟩ : Fin n) ∈ arc r ⟨a, ha⟩ := by
  refine mem_arc.mpr ⟨j, hj, Fin.ext ?_⟩
  change (a + j % n) % n = x
  rw [Nat.add_mod_mod]
  rcases h with h | h
  · rw [h, Nat.mod_eq_of_lt hx]
  · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

-- In an order rotated to a selected start at zero, every residue class of the
-- shifted starts must miss a selected interval. A complete class would cover the circle.
private theorem missing_residues_surj {r d : ℕ} (hr : 0 < r)
    (hd : 0 < d) (hn : n ≤ d * r) (S : Finset (Fin n)) (h0 : 0 ∈ S)
    (hno : ∀ C : Finset (Fin n), C ⊆ S → C.card ≤ d → C.biUnion (arc r) ≠ univ) :
    Set.SurjOn (fun i : Fin n ↦ (i.val - 1) % r)
      (Sᶜ : Finset (Fin n)) (range r : Set ℕ) := by
  classical
  intro i hi
  have hir := mem_range.mp hi
  let a := i + 1
  have hap : 0 < a := by omega
  have har : a ≤ r := by omega
  change ∃ z : Fin n, z ∈ Sᶜ ∧ (z.val - 1) % r = i
  by_contra! he
  have hin {j : ℕ} (hj : a + j * r < n) : (⟨a + j * r, hj⟩ : Fin n) ∈ S := by
    by_contra hh
    apply he ⟨a + j * r, hj⟩ (mem_compl.mpr hh)
    change (a + j * r - 1) % r = i
    rw [show a + j * r - 1 = i + r * j by rw [Nat.mul_comm j r]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hir]
  let valid (m : ℕ) := (range m).filter (fun j ↦ a + j * r < n)
  have valid_spec {m j : ℕ} (h : j ∈ valid m) : j < m ∧ a + j * r < n := by
    simpa [valid] using h
  let starts (m : ℕ) := (valid m).attach.image
    fun j ↦ (⟨a + j.val * r, (valid_spec j.property).2⟩ : Fin n)
  have starts_mem {m j : ℕ} (hm : j < m) (hj : a + j * r < n) :
      (⟨a + j * r, hj⟩ : Fin n) ∈ starts m := by
    apply mem_image.mpr
    exact ⟨⟨j, mem_filter.mpr ⟨mem_range.mpr hm, hj⟩⟩, by simp, rfl⟩
  have starts_sub (m : ℕ) : starts m ⊆ S := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact hin (valid_spec j.property).2
  have starts_card (m : ℕ) : (starts m).card ≤ m :=
    (card_image_le.trans (by rw [card_attach]; exact card_filter_le _ _)).trans_eq (card_range m)
  have hdform : d * r = (d - 1) * r + r := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hd]
  have back (u : ℕ) (hu : a ≤ u) :
      a + ((u - a) / r) * r + ((u - a) % r) = u := by
    have := Nat.mod_add_div (u - a) r
    rw [Nat.mul_comm r] at this
    omega
  by_cases hcase : n ≤ a + (d - 1) * r
  · apply hno (insert 0 (starts (d - 1))) (insert_subset h0 (starts_sub _))
    · have := card_insert_le (0 : Fin n) (starts (d - 1))
      have := starts_card (d - 1)
      omega
    apply eq_univ_of_forall
    intro u
    by_cases hu : u.val < a
    · exact mem_biUnion.mpr ⟨0, mem_insert_self _ _,
        mem_arc.mpr ⟨u.val, by omega, by
          simp only [zero_add]
          exact Fin.ext (Nat.mod_eq_of_lt u.isLt)⟩⟩
    have hu' : a ≤ u.val := by omega
    have hj := back u.val hu'
    have hv : a + (u.val - a) / r * r < n := by have := u.isLt; omega
    have hjm : (u.val - a) / r < d - 1 := by
      apply (Nat.div_lt_iff_lt_mul hr).mpr
      omega
    exact mem_biUnion.mpr ⟨_, mem_insert_of_mem (starts_mem hjm hv),
      mem_arc_of_nat hv u.isLt (Nat.mod_lt _ hr) (Or.inl hj)⟩
  · apply hno (starts d) (starts_sub _) (starts_card _)
    apply eq_univ_of_forall
    intro u
    by_cases hu : u.val < a
    · have hv : a + (d - 1) * r < n := by omega
      have hj : u.val + n - (a + (d - 1) * r) < r := by omega
      refine mem_biUnion.mpr ⟨_, starts_mem (by omega) hv,
        mem_arc_of_nat hv u.isLt hj (Or.inr (by omega))⟩
    have hu' : a ≤ u.val := by omega
    have hj := back u.val hu'
    have hv : a + (u.val - a) / r * r < n := by have := u.isLt; omega
    have hjm : (u.val - a) / r < d := by
      apply (Nat.div_lt_iff_lt_mul hr).mpr
      have := u.isLt
      omega
    exact mem_biUnion.mpr ⟨_, starts_mem hjm hv,
      mem_arc_of_nat hv u.isLt (Nat.mod_lt _ hr) (Or.inl hj)⟩
private theorem selected_compl_card_le {r d : ℕ} (hr : 0 < r) (hrn : r < n)
    (hd : 0 < d) (hn : n ≤ d * r) (S : Finset (Fin n)) (h0 : 0 ∈ S)
    (hno : ∀ C : Finset (Fin n), C ⊆ S → C.card ≤ d → C.biUnion (arc r) ≠ univ) :
    S.card ≤ n - r := by
  classical
  have hres := missing_residues_surj hr hd hn S h0 hno
  have hc := card_le_card_of_surjOn _ hres
  simp only [card_range, card_compl, Fintype.card_fin] at hc
  omega

private theorem mem_arc_iff {r : ℕ} (hr : r ≤ n) {a x : Fin n} :
    x ∈ arc r a ↔ (x - a).val < r := by
  rw [mem_arc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have he : a + Fin.ofNat n j - a = Fin.ofNat n j := by abel
    rwa [he, show (Fin.ofNat n j).val = j from Nat.mod_eq_of_lt (hj.trans_le hr)]
  · intro h
    refine ⟨(x - a).val, h, ?_⟩
    have he : Fin.ofNat n (x - a).val = x - a :=
      Fin.ext (Nat.mod_eq_of_lt (x - a).isLt)
    rw [he, add_sub_cancel]

private def orderedArc (r : ℕ) (p : Equiv.Perm (Fin n)) (a : Fin n) : Finset (Fin n) :=
  (arc r a).map p.toEmbedding

private theorem mem_orderedArc {r : ℕ} (hr : r ≤ n) {p : Equiv.Perm (Fin n)} {a x : Fin n} :
    x ∈ orderedArc r p a ↔ (p.symm x - a).val < r := by
  rw [← mem_arc_iff hr, orderedArc, mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro hx
    exact ⟨p.symm x, hx, p.apply_symm_apply x⟩

private noncomputable def selected
    (r : ℕ) (G : Finset (Finset (Fin n))) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter fun a ↦ orderedArc r p a ∈ G

private theorem mem_selected {r : ℕ} {F : Finset (Finset (Fin n))}
    {p : Equiv.Perm (Fin n)} {a : Fin n} :
    a ∈ selected r F p ↔ orderedArc r p a ∈ F := by
  exact mem_filter.trans ⟨And.right, fun h ↦ ⟨mem_univ _, h⟩⟩

private theorem count_orderedArc {r : ℕ} (hr : r ≤ n) (a : Fin n) {A : Finset (Fin n)}
    (hA : A.card = r) :
    ((univ : Finset (Equiv.Perm (Fin n))).filter (fun p ↦ orderedArc r p a = A)).card =
      r.factorial * (n - r).factorial := by
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin n).symm
  let e : Equiv.Perm (Fin n) ≃ Numbering (Fin n) :=
    { toFun := fun p ↦ (p.symm.trans (Equiv.addRight (-a))).trans c
      invFun := fun f ↦ (((f.trans c.symm).trans (Equiv.addRight a))).symm
      left_inv := by intro p; ext x; simp [c]
      right_inv := by intro f; ext x; simp [c] }
  have he (p : Equiv.Perm (Fin n)) :
      orderedArc r p a = A ↔ (e p).IsPrefix A := by
    have hpe (x : Fin n) : ((e p) x).val = (p.symm x - a).val := by
      simp [e, c, sub_eq_add_neg]
    simp only [Numbering.IsPrefix, hpe, hA, ← mem_orderedArc hr]
    exact ⟨fun h x ↦ h ▸ Iff.rfl, fun h ↦ Finset.ext fun x ↦ (h x).symm⟩
  let P := (univ : Finset (Equiv.Perm (Fin n))).filter fun p ↦ orderedArc r p a = A
  let e' : P ≃ (Numbering.prefixed A) :=
    e.subtypeEquiv fun p ↦ by simpa only [P, mem_filter, mem_univ, true_and,
      Numbering.mem_prefixed] using he p
  simpa only [Fintype.card_coe, Numbering.card_prefixed, Fintype.card_fin, hA] using
    Fintype.card_congr e'

private theorem sum_selected_card {r : ℕ} (hr : r ≤ n) (G : Finset (Finset (Fin n)))
    (hG : ∀ A ∈ G, A.card = r) :
    ∑ p : Equiv.Perm (Fin n), (selected r G p).card =
      n * (G.card * (r.factorial * (n - r).factorial)) := by
  classical
  let rel := fun (p : Equiv.Perm (Fin n)) (a : Fin n) ↦ orderedArc r p a ∈ G
  change (∑ p ∈ (univ : Finset (Equiv.Perm (Fin n))),
    ((univ : Finset (Fin n)).bipartiteAbove rel p).card) = _
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have hfixed (a : Fin n) : ((univ : Finset (Equiv.Perm (Fin n))).bipartiteBelow rel a).card =
      G.card * (r.factorial * (n - r).factorial) := by
    let ord := fun p : Equiv.Perm (Fin n) ↦ orderedArc r p a
    have h := card_eq_sum_card_fiberwise
      (s := (univ : Finset (Equiv.Perm (Fin n))).bipartiteBelow rel a) (t := G) (f := ord)
      (fun p hp ↦ (mem_bipartiteBelow rel).mp hp |>.2)
    rw [h]
    trans ∑ _x ∈ G, r.factorial * (n - r).factorial
    · apply sum_congr rfl
      intro A hA
      have heq :
          (((univ : Finset (Equiv.Perm (Fin n))).bipartiteBelow rel a).filter
            (fun p ↦ ord p = A)) =
          (univ : Finset (Equiv.Perm (Fin n))).filter (fun p ↦ ord p = A) := by
        ext p
        simp only [mem_filter, mem_bipartiteBelow, mem_univ, true_and, rel, ord]
        exact and_iff_right_of_imp fun h ↦ h.symm ▸ hA
      rw [heq]
      exact count_orderedArc hr a (hG A hA)
    · simp
  simp [hfixed]

private theorem arc_rotate {r : ℕ} (hr : r ≤ n) (a b : Fin n) :
    (arc r a).map (Equiv.addRight b).toEmbedding = arc r (a + b) := by
  ext x
  simp only [mem_map, mem_arc_iff hr, Equiv.toEmbedding_apply]
  refine ⟨?_, fun h ↦ ⟨x - b, ?_, sub_add_cancel _ _⟩⟩
  · rintro ⟨j, hj, rfl⟩
    change (j + b - (a + b)).val < r
    rwa [show j + b - (a + b) = j - a by abel]
  · rwa [show x - b - a = x - (a + b) by abel]

private theorem card_le_of_no_arc_cover {r d : ℕ} (hr : 0 < r) (hrn : r < n)
    (hd : 0 < d) (hn : n ≤ d * r) (S : Finset (Fin n))
    (hno : ∀ C : Finset (Fin n), C ⊆ S → C.card ≤ d → C.biUnion (arc r) ≠ univ) :
    S.card ≤ n - r := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  let e := Equiv.addRight (-a)
  let T := S.map e.toEmbedding
  have h0 : 0 ∈ T := mem_map.mpr ⟨a, ha, by simp [e]⟩
  have hT : ∀ C : Finset (Fin n), C ⊆ T → C.card ≤ d → C.biUnion (arc r) ≠ univ := by
    intro C hCS hCd hU
    let e' := Equiv.addRight a
    have hmap : C.map e'.toEmbedding ⊆ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := mem_map.mp (hCS hy)
      simpa [e, e'] using hz
    refine hno _ hmap (by simpa using hCd) (eq_univ_of_forall fun x ↦ ?_)
    have hx : x - a ∈ C.biUnion (arc r) := hU.symm ▸ mem_univ _
    obtain ⟨y, hy, hx⟩ := mem_biUnion.mp hx
    refine mem_biUnion.mpr ⟨y + a, mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [← arc_rotate hrn.le]
    exact mem_map.mpr ⟨x - a, hx, sub_add_cancel _ _⟩
  simpa [T] using selected_compl_card_le hr hrn hd hn T h0 hT

private theorem card_le_of_max_selected {r m : ℕ} (hr : r ≤ n)
    {G : Finset (Finset (Fin n))} (hG : ∀ A ∈ G, A.card = r)
    (hmax : ∀ p, (selected r G p).card ≤ m) :
    n * G.card ≤ m * n.choose r := by
  have hsum : (∑ p : Equiv.Perm (Fin n), (selected r G p).card) ≤
      ∑ _p : Equiv.Perm (Fin n), m := sum_le_sum fun p _ ↦ hmax p
  rw [sum_selected_card hr G hG] at hsum
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hfact := Nat.choose_mul_factorial_mul_factorial hr
  have hpos : 0 < r.factorial * (n - r).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.le_of_mul_le_mul_right _ hpos
  have hrhs : m * n.choose r * (r.factorial * (n - r).factorial) = n.factorial * m := by
    calc
      _ = m * (n.choose r * r.factorial * (n - r).factorial) := by ring
      _ = _ := by rw [hfact, mul_comm]
  rw [hrhs]
  simpa only [mul_assoc, Nat.cast_id] using hsum

private theorem card_eq_of_card_eq_weight {r m : ℕ} (hr : r ≤ n)
    {G : Finset (Finset (Fin n))} (hG : ∀ A ∈ G, A.card = r)
    (hmax : ∀ p, (selected r G p).card ≤ m)
    (he : n * G.card = m * n.choose r) (p : Equiv.Perm (Fin n)) :
    (selected r G p).card = m := by
  by_contra hne
  have hsum : (∑ p : Equiv.Perm (Fin n), (selected r G p).card) <
      ∑ _p : Equiv.Perm (Fin n), m :=
    sum_lt_sum (fun q _ ↦ hmax q) ⟨p, mem_univ _, lt_of_le_of_ne (hmax p) hne⟩
  rw [sum_selected_card hr G hG, ← mul_assoc, he] at hsum
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id] at hsum
  have hf := Nat.choose_mul_factorial_mul_factorial hr
  have hfalse : m * (n.choose r * r.factorial * (n - r).factorial) < m * n.factorial := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [hf] at hfalse
  exact (lt_irrefl _) hfalse

private theorem no_arc_cover_of_no_cover {r d : ℕ} (G : Finset (Finset (Fin n)))
    (hno : ∀ C : Finset (Finset (Fin n)), C ⊆ G → C.card ≤ d → C.biUnion id ≠ univ)
    (p : Equiv.Perm (Fin n)) :
    ∀ C : Finset (Fin n), C ⊆ selected r G p → C.card ≤ d → C.biUnion (arc r) ≠ univ := by
  intro C hC hcard hU
  refine hno (C.image (orderedArc r p)) ?_ (card_image_le.trans hcard) ?_
  · rw [image_subset_iff]
    exact fun a ha ↦ (mem_filter.mp (hC ha)).2
  · apply eq_univ_of_forall
    intro x
    have hmem : p.symm x ∈ C.biUnion (arc r) := hU.symm ▸ mem_univ _
    obtain ⟨a, ha, hx⟩ := mem_biUnion.mp hmem
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ ha,
      mem_map.mpr ⟨p.symm x, hx, p.apply_symm_apply x⟩⟩

private theorem selected_card_of_no_cover {r d : ℕ} (hr : 0 < r) (hrn : r < n)
    (hd : 0 < d) (hn : n ≤ d * r) (G : Finset (Finset (Fin n)))
    (hno : ∀ C : Finset (Finset (Fin n)), C ⊆ G → C.card ≤ d → C.biUnion id ≠ univ)
    (p : Equiv.Perm (Fin n)) : (selected r G p).card ≤ n - r :=
  card_le_of_no_arc_cover hr hrn hd hn _ (no_arc_cover_of_no_cover G hno p)

omit [NeZero n] in
private theorem val_sub_ite (x a : Fin n) :
    (x - a).val = if a ≤ x then x.val - a.val else n + x.val - a.val := by
  have h := Fin.intCast_val_sub_eq_sub_add_ite x a
  by_cases ha : a ≤ x
  · simp only [ite_eq_left ha] at h ⊢
    have := a.isLt
    change a.val ≤ x.val at ha
    omega
  · simp only [ite_eq_right ha] at h ⊢
    have := a.isLt
    change ¬ a.val ≤ x.val at ha
    omega

private theorem arc_disjoint_iff {r : ℕ} (hr : 0 < r) (hrn : 2 * r ≤ n)
    (a b : Fin n) :
    Disjoint (arc r a) (arc r b) ↔ r ≤ (b - a).val ∧ (b - a).val ≤ n - r := by
  have hle : r ≤ n := by omega
  have h : Disjoint (arc r a) (arc r b) ↔ Disjoint (arc r 0) (arc r (b - a)) := by
    have h₁ : (arc r a).map (Equiv.addRight (-a)).toEmbedding = arc r 0 := by
      rw [arc_rotate hle, add_neg_cancel]
    have h₂ : (arc r b).map (Equiv.addRight (-a)).toEmbedding = arc r (b - a) := by
      rw [arc_rotate hle, sub_eq_add_neg]
    rw [← h₁, ← h₂, disjoint_map]
  rw [h]
  set c := b - a
  constructor
  · intro h
    constructor
    · by_contra! hc
      exact disjoint_left.mp h (mem_arc_iff hle |>.mpr (by simpa using hc))
        (mem_arc_iff hle |>.mpr (by simpa using hr))
    · by_contra! hc
      have hc0 : c ≠ 0 := by
        rintro he
        rw [he] at hc
        simp at hc
      have hpos : 0 < c.val := Nat.pos_of_ne_zero (fun he ↦ hc0 (Fin.ext (by simpa using he)))
      have hzc : ¬c ≤ (0 : Fin n) := by
        intro hz
        change c.val ≤ 0 at hz
        omega
      exact disjoint_left.mp h ((mem_arc_iff hle (a := 0) (x := 0)).mpr (by simpa using hr))
        ((mem_arc_iff hle).mpr (by
          rw [val_sub_ite, ite_eq_right hzc]
          simp only [Fin.val_zero, add_zero]
          omega))
  · rintro ⟨hc, hcn⟩
    rw [disjoint_left]
    intro x hx hx'
    have hxr : x.val < r := by simpa using (mem_arc_iff hle).mp hx
    have hnot : ¬ c ≤ x := by change ¬ c.val ≤ x.val; omega
    have hj := (mem_arc_iff hle).mp hx'
    rw [val_sub_ite, ite_eq_right hnot] at hj
    omega

omit [NeZero n] in
private theorem perm_map_pair {A B C D : Finset (Fin n)}
    (hab : Disjoint A B) (hcd : Disjoint C D) (hAC : A.card = C.card)
    (hBD : B.card = D.card) :
    ∃ p : Equiv.Perm (Fin n), A.map p.toEmbedding = C ∧ B.map p.toEmbedding = D := by
  let f : (A ⊕ B) → Fin n := Sum.elim Subtype.val Subtype.val
  let g : (A ⊕ B) → Fin n :=
    Sum.elim (fun x ↦ (A.equivOfCardEq hAC x : C).val) (fun x ↦ (B.equivOfCardEq hBD x : D).val)
  have hf : Function.Injective f := by
    intro a b he
    cases a <;> cases b
    · exact congrArg Sum.inl (Subtype.ext he)
    · rename_i a b
      change a.val = b.val at he
      exact False.elim (disjoint_left.mp hab a.property (he.symm ▸ b.property))
    · rename_i b a
      change b.val = a.val at he
      exact False.elim (disjoint_left.mp hab a.property (he ▸ b.property))
    · exact congrArg Sum.inr (Subtype.ext he)
  have hg : Function.Injective g := by
    intro a b he
    cases a <;> cases b
    · exact congrArg Sum.inl ((A.equivOfCardEq hAC).injective (Subtype.ext he))
    · rename_i a b
      change (A.equivOfCardEq hAC a).val = (B.equivOfCardEq hBD b).val at he
      exact False.elim (disjoint_left.mp hcd (A.equivOfCardEq hAC a).property
        (he.symm ▸ (B.equivOfCardEq hBD b).property))
    · rename_i b a
      change (B.equivOfCardEq hBD b).val = (A.equivOfCardEq hAC a).val at he
      exact False.elim (disjoint_left.mp hcd (A.equivOfCardEq hAC a).property
        (he ▸ (B.equivOfCardEq hBD b).property))
    · exact congrArg Sum.inr ((B.equivOfCardEq hBD).injective (Subtype.ext he))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨p, ?_, ?_⟩
  · apply eq_of_subset_of_card_le _ (by simpa using hAC.ge)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (hp (Sum.inl ⟨y, hy⟩)).symm ▸ (A.equivOfCardEq hAC ⟨y, hy⟩).property
  · apply eq_of_subset_of_card_le _ (by simpa using hBD.ge)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (hp (Sum.inr ⟨y, hy⟩)).symm ▸ (B.equivOfCardEq hBD ⟨y, hy⟩).property

private theorem orderedArc_precompose_rotate {r : ℕ} (hrn : r ≤ n)
    (p : Equiv.Perm (Fin n)) (a u : Fin n) :
    orderedArc r ((Equiv.addRight a).trans p) u = orderedArc r p (u + a) := by
  rw [orderedArc, orderedArc, ← arc_rotate hrn, map_map]
  rfl

-- At equality the missing starts have distinct residues. Positioning disjoint
-- missing intervals consecutively forces their residues to agree after a rotation.
private theorem disjoint_forbidden_impossible {r d : ℕ} (hr : 0 < r) (hrn : 2 * r < n)
    (hd : 0 < d) (hn : n ≤ d * r) (G : Finset (Finset (Fin n)))
    (hno : ∀ C : Finset (Finset (Fin n)), C ⊆ G → C.card ≤ d → C.biUnion id ≠ univ)
    (heq : ∀ p, (selected r G p).card = n - r)
    {A B : Finset (Fin n)} (hAc : A.card = r) (hBc : B.card = r)
    (hAG : A ∉ G) (hBG : B ∉ G) :
    ¬ Disjoint A B := by
  intro hAB
  let t : Fin n := ⟨r, by omega⟩
  have hdis : Disjoint (arc r 0) (arc r t) := by
    rw [arc_disjoint_iff hr hrn.le]
    simp only [sub_zero, t]
    omega
  obtain ⟨p, hpA, hpB⟩ := perm_map_pair hdis hAB
    ((card_arc (by omega) _).trans hAc.symm) ((card_arc (by omega) _).trans hBc.symm)
  let S := selected r G p
  have hSc : S.card = n - r := heq p
  have h0S : 0 ∉ S := fun h ↦ hAG (hpA ▸ (mem_filter.mp h).2)
  have htS : t ∉ S := fun h ↦ hBG (hpB ▸ (mem_filter.mp h).2)
  have ha : ∃ a ∈ S, r < a.val := by
    by_contra! hb
    have hsub : S ⊆ Iio t := by
      intro a ha
      apply mem_Iio.mpr
      have hap : a ≠ t := fun e ↦ htS (e ▸ ha)
      have hal := hb a ha
      have hne : a.val ≠ r := fun e ↦ hap (Fin.ext e)
      change a.val < r
      omega
    have hle := card_le_card hsub
    rw [Fin.card_Iio, hSc] at hle
    change n - r ≤ r at hle
    omega
  obtain ⟨a, ha, har⟩ := ha
  let q := (Equiv.addRight a).trans p
  let T := selected r G q
  have htrans (u : Fin n) : u ∈ T ↔ u + a ∈ S := by
    simp only [T, S, selected, mem_filter, mem_univ, true_and, q,
      orderedArc_precompose_rotate (by omega : r ≤ n)]
  have hzero : 0 ∈ T := (htrans 0).mpr (by simpa using ha)
  let f : Fin n → ℕ := fun i ↦ (i.val - 1) % r
  have hsurj : Set.SurjOn f (Tᶜ : Finset (Fin n)) (range r : Set ℕ) :=
    missing_residues_surj hr hd hn T hzero (no_arc_cover_of_no_cover G hno q)
  have hf : Set.MapsTo f (Tᶜ : Finset (Fin n)) (range r : Set ℕ) :=
    fun x _ ↦ mem_range.mpr (Nat.mod_lt _ hr)
  have hcard : (Tᶜ : Finset (Fin n)).card = r := by
    rw [card_compl, Fintype.card_fin, heq]
    omega
  have hfim : (Tᶜ : Finset (Fin n)).image f = range r := by
    ext x
    exact ⟨fun h ↦ by obtain ⟨y, hy, rfl⟩ := mem_image.mp h; exact hf hy, fun h ↦ by
      obtain ⟨y, hy, he⟩ := hsurj h
      exact mem_image.mpr ⟨y, hy, he⟩⟩
  have hinj : Set.InjOn f (Tᶜ : Finset (Fin n)) :=
    injOn_of_card_image_eq (by rw [hfim, card_range, hcard])
  have hz : 0 - a ∈ (Tᶜ : Finset (Fin n)) := mem_compl.mpr
    (fun h ↦ h0S (by simpa using (htrans (0 - a)).mp h))
  have ht : t - a ∈ (Tᶜ : Finset (Fin n)) := mem_compl.mpr
    (fun h ↦ htS (by simpa using (htrans (t - a)).mp h))
  have hab : (0 - a).val = n - a.val := by
    rw [val_sub_ite, ite_eq_right (by change ¬ a.val ≤ 0; omega)]
    simp
  have htval : (t - a).val = n + r - a.val := by
    rw [val_sub_ite, ite_eq_right (by change ¬ a.val ≤ r; omega)]
  have hmod : f (0 - a) = f (t - a) := by
    change ((0 - a).val - 1)%r = ((t - a).val - 1)%r
    have hshift : n + r - a.val - 1 = (n - a.val - 1) + r := by
      have := a.isLt
      omega
    rw [hab, htval, hshift, Nat.add_mod_right]
  have hh := hinj hz ht hmod
  have hh' : t = 0 := (sub_left_injective hh).symm
  have := congrArg Fin.val hh'
  change r = 0 at this
  omega

private theorem common_point_of_max_arcs_zero {r : ℕ} (hr : 0 < r) (hrn : 2 * r < n)
    (S : Finset (Fin n)) (hS : S.card = r) (h0 : 0 ∈ S)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, ¬ Disjoint (arc r a) (arc r b)) :
    ∃ z, ∀ a ∈ S, z ∈ arc r a := by
  classical
  let f := fun a : Fin n ↦ if a.val < r then a.val else a.val + r - n
  have htype (a : Fin n) (ha : a ∈ S) : a.val < r ∨ n - r < a.val := by
    have h := hpair 0 h0 a ha
    rw [arc_disjoint_iff hr hrn.le, sub_zero] at h
    omega
  have hf (a : Fin n) (ha : a ∈ S) : f a ∈ range r := by
    rw [mem_range]
    rcases htype a ha with h | h
    · simp [f, h]
    · have := a.isLt
      simp only [f, ite_eq_right (by omega : ¬ a.val < r)]
      omega
  have hmixed {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) (hla : a.val < r)
      (hlb : ¬ b.val < r) (he : f a = f b) : False := by
    have hb' := (htype b hb).resolve_left hlb
    have hab : a ≤ b := by change a.val ≤ b.val; omega
    simp only [f, ite_eq_left hla, ite_eq_right hlb] at he
    apply hpair a ha b hb
    rw [arc_disjoint_iff hr hrn.le, val_sub_ite, ite_eq_left hab]
    omega
  have hi : Set.InjOn f (S : Set (Fin n)) := by
    intro a ha b hb he
    change a ∈ S at ha
    change b ∈ S at hb
    by_cases hla : a.val < r <;> by_cases hlb : b.val < r
    · exact Fin.ext (by simpa [f, hla, hlb] using he)
    · exact False.elim (hmixed ha hb hla hlb he)
    · exact False.elim (hmixed hb ha hlb hla he.symm)
    · apply Fin.ext
      have ha' := (htype a ha).resolve_left hla
      have hb' := (htype b hb).resolve_left hlb
      simp only [f, ite_eq_right hla, ite_eq_right hlb] at he
      omega
  have himage : S.image f = range r := by
    apply eq_of_subset_of_card_le
    · rw [image_subset_iff]
      exact hf
    · rw [card_image_of_injOn hi, hS, card_range]
  let T := (S.filter fun a ↦ a.val < r).image Fin.val
  have hT : T.Nonempty := by exact ⟨0, mem_image.mpr ⟨0, mem_filter.mpr ⟨h0, by simpa⟩, rfl⟩⟩
  let t := T.max' hT
  obtain ⟨u, hu, hval⟩ := mem_image.mp (max'_mem T hT)
  have huS : u ∈ S := (mem_filter.mp hu).1
  have hur : u.val < r := (mem_filter.mp hu).2
  have hdown (j : ℕ) (hj : j ≤ t) : ∃ a ∈ S, a.val = j := by
    induction hjq : t - j using Nat.strong_induction_on generalizing j with
    | ind q ih =>
      by_cases h : j = t
      · exact ⟨u, huS, hval.trans h.symm⟩
      obtain ⟨a, ha, hav⟩ := ih (t - (j + 1)) (by omega) (j + 1) (by omega) rfl
      have hjr : j < r := by omega
      have hJ : j ∈ S.image f := himage.symm ▸ mem_range.mpr hjr
      obtain ⟨b, hb, hbv⟩ := mem_image.mp hJ
      by_cases hbpos : b.val < r
      · exact ⟨b, hb, by simpa [f, hbpos] using hbv⟩
      have hbn := (htype b hb).resolve_left hbpos
      have hba : a ≤ b := by change a.val ≤ b.val; omega
      simp only [f, ite_eq_right hbpos] at hbv
      exfalso
      apply hpair a ha b hb
      rw [arc_disjoint_iff hr hrn.le, val_sub_ite, ite_eq_left hba]
      omega
  refine ⟨u, fun a ha ↦ ?_⟩
  have hle : r ≤ n := by omega
  apply (mem_arc_iff hle).mpr
  rcases htype a ha with h | h
  · have hat : a.val ≤ t := le_max' T _ (mem_image.mpr ⟨a, mem_filter.mpr ⟨ha,h⟩, rfl⟩)
    have hau : a ≤ u := by change a.val ≤ u.val; omega
    rw [val_sub_ite, ite_eq_left hau]
    omega
  · have hapos : ¬ a.val < r := by omega
    have hfgt : t < f a := by
      by_contra! hle
      obtain ⟨b, hb, hbe⟩ := hdown (f a) hle
      have hblt : b.val < r := by omega
      exact hmixed hb ha hblt hapos (by simpa [f,hblt] using hbe)
    have hau : ¬ a ≤ u := by change ¬ a.val ≤ u.val; omega
    simp only [f, ite_eq_right hapos] at hfgt
    rw [val_sub_ite, ite_eq_right hau]
    omega

private theorem common_point_of_max_arcs {r : ℕ} (hr : 0 < r) (hrn : 2 * r < n)
    (S : Finset (Fin n)) (hS : S.card = r)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, ¬ Disjoint (arc r a) (arc r b)) :
    ∃ z, ∀ a ∈ S, z ∈ arc r a := by
  obtain ⟨a, ha⟩ := card_pos.mp (hS.symm ▸ hr)
  let e := Equiv.addRight (-a)
  let T := S.map e.toEmbedding
  have hTc : T.card = r := by simpa [T] using hS
  have h0 : 0 ∈ T := mem_map.mpr ⟨a, ha, by simp [e]⟩
  have hrle : r ≤ n := by omega
  have hpairT (u : Fin n) (hu : u ∈ T) (v : Fin n) (hv : v ∈ T) :
      ¬ Disjoint (arc r u) (arc r v) := by
    obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := mem_map.mp hv
    change ¬ Disjoint (arc r (u' + -a)) (arc r (v' + -a))
    simpa only [← arc_rotate hrle, disjoint_map] using hpair u' hu' v' hv'
  obtain ⟨z, hz⟩ := common_point_of_max_arcs_zero hr hrn T hTc h0 hpairT
  refine ⟨z + a, fun u hu ↦ ?_⟩
  have h := hz (u + -a) (mem_map.mpr ⟨u, hu, rfl⟩)
  rw [← arc_rotate hrle] at h
  obtain ⟨w, hw, he⟩ := mem_map.mp h
  have hwz : w = z + a := by
    change w + -a = z at he
    rw [← he]
    abel
  exact hwz ▸ hw

private def startsThrough (r : ℕ) (v : Fin n) : Finset (Fin n) :=
  univ.filter fun a ↦ v ∈ arc r a

private theorem mem_startsThrough {r : ℕ} (hr : r ≤ n) {v a : Fin n} :
    a ∈ startsThrough r v ↔ (v - a).val < r := by
  simp [startsThrough, mem_arc_iff hr]

private theorem card_startsThrough {r : ℕ} (hr : r ≤ n) (v : Fin n) :
    (startsThrough r v).card = r := by
  have he : startsThrough r v = (arc r 0).map (Equiv.subLeft v).toEmbedding := by
    ext a
    rw [mem_startsThrough hr, mem_map]
    constructor
    · intro h
      exact ⟨v - a, (mem_arc_iff hr).mpr (by simpa using h), by change v - (v - a) = a; abel⟩
    · rintro ⟨a', ha', rfl⟩
      change (v - (v - a')).val < r
      simpa using (mem_arc_iff hr (a := 0)).mp ha'
  rw [he, card_map, card_arc hr]

private theorem arc_transpose_unchanged {r : ℕ} (hR : r < n) {a j : Fin n}
    (ha : a ≠ j) (hb : a ≠ j - Fin.ofNat n r) :
    (arc r a).map (Equiv.swap (j - 1) j).toEmbedding = arc r a := by
  have h₁ : ¬ j - a = 0 := fun h ↦ ha (sub_eq_zero.mp h).symm
  have h₂ : (j - a).val ≠ r := fun h ↦ hb (by
    have he : j - a = Fin.ofNat n r := Fin.ext (h.trans (Nat.mod_eq_of_lt hR).symm)
    rw [← he]
    abel)
  have hmem : j - 1 ∈ arc r a ↔ j ∈ arc r a := by
    rw [mem_arc_iff hR.le, mem_arc_iff hR.le, show j - 1 - a = (j - a) - 1 by abel,
      Fin.val_sub_one_of_ne_zero h₁]
    omega
  ext z
  simp only [mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Equiv.swap_apply_def]
    split_ifs with h h'
    · exact hmem.mp (h ▸ hu)
    · exact hmem.mpr (h' ▸ hu)
    · exact hu
  · intro hz
    refine ⟨Equiv.swap (j - 1) j z, ?_, Equiv.swap_apply_self _ _ _⟩
    rw [Equiv.swap_apply_def]
    split_ifs with h h'
    · exact hmem.mp (h ▸ hz)
    · exact hmem.mpr (h' ▸ hz)
    · exact hz

-- Swapping adjacent positions away from the center changes at most two intervals.
-- The unchanged boundary starts of the interval star pin down its center.
private theorem preserves_center_zero {r : ℕ} (hr : 2 ≤ r) (hR : 2 * r < n)
    (F : Finset (Finset (Fin n))) (p : Equiv.Perm (Fin n)) {j : Fin n} (hj : 2 ≤ j.val)
    (hp : selected r F p = startsThrough r 0)
    (hQ : ∃ v, selected r F ((Equiv.swap (j - 1) j).trans p) = startsThrough r v) :
    selected r F ((Equiv.swap (j - 1) j).trans p) = startsThrough r 0 := by
  let L := j - Fin.ofNat n r
  let T := selected r F ((Equiv.swap (j - 1) j).trans p)
  have hrn : r < n := by omega
  obtain ⟨v, hv⟩ := hQ
  change T = startsThrough r v at hv
  have hs (a : Fin n) (ha : a ≠ j) (hb : a ≠ L) :
      a ∈ T ↔ a ∈ startsThrough r 0 := by
    rw [← hp]
    change a ∈ selected r F _ ↔ a ∈ selected r F _
    rw [mem_selected, mem_selected]
    unfold orderedArc
    change ((arc r a).map ((Equiv.swap (j - 1) j).toEmbedding.trans p.toEmbedding) ∈ F) ↔ _
    rw [← map_map, arc_transpose_unchanged hrn ha hb]
  have hz (a : Fin n) : a ∈ startsThrough r (0 : Fin n) ↔ a.val = 0 ∨ n - r < a.val := by
    rw [mem_startsThrough hrn.le, val_sub_ite]
    by_cases h : a.val = 0
    · simp [Fin.ext (show a.val = (0 : Fin n).val from h)]
      omega
    · have hx : ¬ a ≤ (0 : Fin n) := by change ¬ a.val ≤ 0; omega
      simp only [ite_eq_right hx, Fin.val_zero, add_zero]
      have := a.isLt
      omega
  have h01 (h0 : (0 : Fin n) ∈ T) (h1 : (1 : Fin n) ∉ T) : v = 0 := by
    rw [hv, mem_startsThrough hrn.le, sub_zero] at h0
    rw [hv, mem_startsThrough hrn.le] at h1
    apply Fin.ext
    change v.val = 0
    by_contra h
    have h1v : (1 : Fin n) ≤ v := by
      have hone : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
      change (1 : Fin n).val ≤ v.val
      rw [hone]
      exact Nat.pos_of_ne_zero h
    rw [val_sub_ite, ite_eq_left h1v] at h1
    omega
  have hLv : L.val = if r ≤ j.val then j.val - r else n + j.val - r := by
    have hRval : (Fin.ofNat n r).val = r := Nat.mod_eq_of_lt hrn
    unfold L
    rw [val_sub_ite]
    change (if (Fin.ofNat n r).val ≤ j.val then j.val - (Fin.ofNat n r).val
      else n + j.val - (Fin.ofNat n r).val) = _
    rw [hRval]
  have hj0 : (0 : Fin n) ≠ j := fun e ↦ by have := congrArg Fin.val e; simp at this; omega
  have hone : (1 : Fin n).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hj1 : (1 : Fin n) ≠ j := fun e ↦ by have := congrArg Fin.val e; omega
  by_cases hL0 : L = 0
  · have hLzero : L.val = 0 := congrArg Fin.val hL0
    have hjr : j.val = r := by split at hLv <;> omega
    let a : Fin n := ⟨n - r, by omega⟩
    let b : Fin n := ⟨n - r + 1, by omega⟩
    have haT : a ∉ T := fun h ↦ by
      have hnot := (hz a).mp ((hs a (fun h ↦ by
        have he := congrArg Fin.val h; change n - r = j.val at he; omega)
        (fun h ↦ by have he := congrArg Fin.val h; change n - r = L.val at he; omega)).mp h)
      change n - r = 0 ∨ n - r<n - r at hnot
      omega
    have hbT : b ∈ T := (hs b (fun h ↦ by
        have he := congrArg Fin.val h; change n - r + 1 = j.val at he; omega)
        (fun h ↦ by have he := congrArg Fin.val h; change n - r + 1 = L.val at he; omega)).mpr
      ((hz b).mpr (Or.inr (by change n - r<n - r + 1; omega)))
    rw [hv, mem_startsThrough hrn.le] at haT hbT
    rw [val_sub_ite] at haT hbT
    apply hv.trans (congrArg (startsThrough r) (show v = 0 by
      apply Fin.ext
      change v.val = 0
      change ¬ ((if n - r ≤ v.val then v.val - (n - r) else n + v.val - (n - r)) < r) at haT
      change (if n - r + 1 ≤ v.val then v.val - (n - r + 1) else n + v.val - (n - r + 1)) < r at hbT
      have := v.isLt
      split at haT <;> split at hbT <;> omega))
  by_cases hL1 : L = 1
  · have hLone : L.val = 1 := (congrArg Fin.val hL1).trans hone
    have hjr : j.val = r + 1 := by split at hLv <;> omega
    have hnJ : j ∉ startsThrough r (0 : Fin n) := fun h ↦ by
      have := (hz j).mp h
      omega
    have hnL : L ∉ startsThrough r (0 : Fin n) := fun h ↦ by
      have := (hz L).mp h
      omega
    have he : startsThrough r (0 : Fin n) ⊆ T := fun a ha ↦
      (hs a (fun h ↦ hnJ (h ▸ ha)) (fun h ↦ hnL (h ▸ ha))).mpr ha
    exact (eq_of_subset_of_card_le he (by rw [hv, card_startsThrough hrn.le,
      card_startsThrough hrn.le])).symm
  have h0 : (0 : Fin n) ∈ T := (hs 0 hj0 (Ne.symm hL0)).mpr ((hz 0).mpr (Or.inl rfl))
  have h1 : (1 : Fin n) ∉ T := fun h ↦ by
    have h := (hz 1).mp ((hs 1 hj1 (Ne.symm hL1)).mp h)
    omega
  exact hv.trans (congrArg (startsThrough r) (h01 h0 h1))

private theorem all_perms_preserve_property_of_adjacent_swaps {m : ℕ}
    (P : Equiv.Perm (Fin (m + 2)) → Prop)
    (hstep : ∀ (p : Equiv.Perm (Fin (m + 2))) (j : Fin (m + 2)), 2 ≤ j.val →
      P p → P ((Equiv.swap (j - 1) j).trans p))
    (p q : Equiv.Perm (Fin (m + 2))) (hpq : q 0 = p 0) (hp : P p) :
    P q := by
  let φ : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm (Fin (m + 2)) :=
    { toFun := fun e ↦ Equiv.Perm.decomposeFin.symm (0, e)
      map_one' := by simpa using (Equiv.Perm.one_def (α := Fin (m + 2))).symm
      map_mul' := by
        intro e f
        ext x
        refine Fin.cases ?_ (fun i ↦ ?_) x
        · simp
        · simp [Equiv.Perm.mul_apply] }
  let K : Submonoid (Equiv.Perm (Fin (m + 1))) :=
    { carrier := {e | ∀ p, P p → P ((φ e).trans p)}
      one_mem' := by
        intro w hw
        change P ((φ 1).trans w)
        rwa [map_one, Equiv.Perm.one_def, Equiv.refl_trans]
      mul_mem' := by
        intro a b ha hb p hp
        change P ((φ (a * b)).trans p)
        rw [map_mul]
        exact hb _ (ha _ hp) }
  have hgen : (Set.range fun i : Fin m ↦ Equiv.swap i.castSucc i.succ) ⊆ (K : Set _) := by
    rintro e ⟨i, rfl⟩
    intro p hp
    let j := i.succ.succ
    have hji : j - 1 = i.castSucc.succ := by
      apply Fin.ext
      rw [Fin.val_sub_one_of_ne_zero (Fin.succ_ne_zero _)]
      rfl
    have he : φ (Equiv.swap i.castSucc i.succ) = Equiv.swap (j - 1) j := by
      rw [hji]
      ext x
      refine Fin.cases ?_ (fun a ↦ ?_) x
      · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.succ_ne_zero _))
          (Ne.symm (Fin.succ_ne_zero _))]
        simp [φ]
      · simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.decomposeFin_symm_apply_succ,
          Equiv.swap_self, Equiv.refl_apply]
        exact congrArg Fin.val
          (Function.Injective.map_swap (Fin.succ_injective _) i.castSucc i.succ a)
    rw [he]
    exact hstep p j (by simp [j]) hp
  have htop : K = ⊤ := top_unique (by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ m]
    exact Submonoid.closure_le.mpr hgen)
  let e := q.trans p.symm
  have he0 : e 0 = 0 := by simp [e, hpq]
  obtain ⟨a, f, haf⟩ : ∃ a f, Equiv.Perm.decomposeFin e = (a, f) :=
    ⟨(Equiv.Perm.decomposeFin e).1, (Equiv.Perm.decomposeFin e).2, rfl⟩
  have he : Equiv.Perm.decomposeFin.symm (a, f) = e := by
    rw [← haf, Equiv.symm_apply_apply]
  have ha0 : a = 0 := by
    have h := congrArg (fun w : Equiv.Perm (Fin (m + 2)) ↦ w 0) he
    simpa [he0] using h
  subst a
  have hmem : f ∈ K := by simp [htop]
  have h := hmem p hp
  change P ((φ f).trans p) at h
  rw [show φ f = e from he] at h
  simpa [e, Equiv.trans_assoc] using h

-- Changing the order while fixing the point in position zero preserves the center.
-- Every set through that point can be made an interval in such an order.
private theorem global_star_of_circles {r : ℕ} (hr : 2 ≤ r) (hR : 2 * r < n)
    (F : Finset (Finset (Fin n)))
    (hfull : ∀ p, ∃ v, selected r F p = startsThrough r v) :
    ∃ x, ∀ A : Finset (Fin n), A.card = r → x ∈ A → A ∈ F := by
  have hrn : r ≤ n := by omega
  obtain ⟨v, hv⟩ := hfull (Equiv.refl (Fin n))
  let p : Equiv.Perm (Fin n) := (Equiv.addRight v).trans (Equiv.refl _)
  have hp : selected r F p = startsThrough r 0 := by
    ext a
    change a ∈ selected r F ((Equiv.addRight v).trans (Equiv.refl _)) ↔ _
    rw [mem_selected, orderedArc_precompose_rotate hrn, ← mem_selected, hv,
      mem_startsThrough hrn, mem_startsThrough hrn, show v - (a + v) = 0 - a by abel]
  refine ⟨p 0, fun A hAc hx ↦ ?_⟩
  have ha0 : (0 : Fin n) ∈ arc r (0 : Fin n) := by
    exact mem_arc.mpr ⟨0, by omega, by simp⟩
  obtain ⟨q, hq₁, hq₂⟩ := perm_map_pair
    (disjoint_left.mpr (fun x hx hy ↦ (notMem_erase _ _) ((mem_singleton.mp hy) ▸ hx)))
    (disjoint_left.mpr (fun x hx hy ↦ (notMem_erase _ _) ((mem_singleton.mp hy) ▸ hx)))
    (show ((arc r (0 : Fin n)).erase 0).card = (A.erase (p 0)).card by
      rw [card_erase_of_mem ha0, card_erase_of_mem hx, card_arc hrn, hAc])
    (show ({0} : Finset (Fin n)).card = ({p 0} : Finset (Fin n)).card by simp)
  have hqp : q 0 = p 0 := by simpa using hq₂
  have hq : selected r F q = startsThrough r 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact all_perms_preserve_property_of_adjacent_swaps
      (fun w ↦ selected r F w = startsThrough r 0)
      (fun w j hj hw ↦ preserves_center_zero hr hR F w hj hw (hfull _)) p q hqp hp
  have h0S : (0 : Fin n) ∈ selected r F q := hq.symm ▸ mem_filter.mpr ⟨mem_univ _, ha0⟩
  have h0 := mem_selected.mp h0S
  rw [orderedArc, ← insert_erase ha0, map_insert, hq₁] at h0
  change insert (q 0) (A.erase (p 0)) ∈ F at h0
  rw [hqp, insert_erase hx] at h0
  exact h0

end Circle

/-! ### From the cyclic interval argument to the dense equality case -/

private theorem no_complement_cover {n k d : ℕ} {G : Finset (Finset (Fin n))}
    (hd : 0 < d) (hG : IsKdFamily n k d G) (hsmall : n ≤ 2 * k)
    (hdG : d ≤ G.card) :
    ∀ C : Finset (Finset (Fin n)), C ⊆ G.compls → C.card ≤ d → C.biUnion id ≠ univ := by
  intro C hC hCd hCU
  obtain ⟨B, hCB, hBG, hBd⟩ := exists_subsuperset_card_eq hC hCd (by rwa [card_compls])
  have hB : B.compls ⊆ G := by
    simpa using (compls_subset_compls.mpr hBG)
  have hBcard : B.compls.card = d := by simpa using hBd
  have hBU : (B.compls.biUnion id).card ≤ 2 * k := by
    exact (by simpa using (B.compls.biUnion id).card_le_univ :
      (B.compls.biUnion id).card ≤ n).trans hsmall
  have hBI : ¬ ∃ x, ∀ A ∈ B.compls, x ∈ A := by
    rintro ⟨x, hx⟩
    have h : x ∈ C.biUnion id := hCU.symm ▸ mem_univ _
    obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp h
    exact (mem_compl.mp (hx Aᶜ (mem_compls.mpr (by simpa using hCB hA)))) hxA
  have hempty : B.compls = ∅ := subset_empty.mp
    (clustersCovered_empty hG _ hB hBcard hBU hBI)
  simpa [hempty] using (show 0 < B.compls.card by omega)

private theorem ground_le_mul_corank {n k d : ℕ} (hd : 1 < d)
    (hn : (d : ℝ) * k / (d - 1) ≤ n) : n ≤ d * (n - k) := by
  have ht := (real_threshold_iff hd).mp hn
  have h₁ := Nat.mul_sub (n := d) (m := n) (k := k)
  have h₂ : d * n = (d - 1) * n + n := by
    have h := Nat.add_one_mul (d - 1) n
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ d)] at h
  omega

private theorem complements_uniform {n k d : ℕ} {G : Finset (Finset (Fin n))}
    (hG : IsKdFamily n k d G) : ∀ A ∈ G.compls, A.card = n - k := by
  intro A hA
  have h := hG.1 _ (mem_compls.mp hA)
  rw [card_compl, Fintype.card_fin] at h
  have h' : A.card ≤ n := by simpa using A.card_le_univ
  omega

private theorem rank_le_star_card {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    k ≤ (n - 1).choose (k - 1) := by
  calc
    k = k.choose (k - 1) := by
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp [Nat.choose_succ_self_right]
    _ ≤ _ := Nat.choose_le_choose _ (by omega)

private theorem kd_card_le_in_dense_range {n k d : ℕ} {G : Finset (Finset (Fin n))}
    (hd : 3 ≤ d) (hdk : d ≤ k) (hn : (d : ℝ) * k / (d - 1) ≤ n)
    (hsmall : n ≤ 2 * k) (hG : IsKdFamily n k d G) :
    G.card ≤ (n - 1).choose (k - 1) := by
  have hkn := lt_ground_of_threshold (by omega : 1 < d) hdk hn
  have hk : 0 < k := by omega
  have : NeZero n := ⟨by omega⟩
  by_cases hdG : d ≤ G.card
  · have hnr := ground_le_mul_corank (by omega) hn
    have hG' := complements_uniform hG
    have hbound := card_le_of_max_selected (r := n - k) (m := n - (n - k)) (by omega) hG'
      (selected_card_of_no_cover (by omega) (by omega) (by omega) hnr G.compls
        (no_complement_cover (by omega) hG hsmall hdG))
    rw [card_compls, Nat.sub_sub_self hkn.le, Nat.choose_symm hkn.le] at hbound
    rw [← choose_mul_rank n k (by omega) hk] at hbound
    exact Nat.le_of_mul_le_mul_left hbound (by omega)
  · exact (show G.card ≤ k by omega).trans (rank_le_star_card hk hkn)

private theorem kd_eq_in_dense_range {n k d : ℕ} {G : Finset (Finset (Fin n))}
    (hd : 3 ≤ d) (hdk : d ≤ k) (hn : (d : ℝ) * k / (d - 1) ≤ n)
    (hsmall : n < 2 * k) (hG : IsKdFamily n k d G)
    (he : G.card = (n - 1).choose (k - 1)) :
    ∃ x, ∀ A ∈ G, x ∈ A := by
  let r := n - k
  have hkn := lt_ground_of_threshold (by omega : 1 < d) hdk hn
  have hR : 2 * r < n := by omega
  have : NeZero n := ⟨by omega⟩
  have hdG : d ≤ G.card := hdk.trans (he.symm ▸ rank_le_star_card (by omega) hkn)
  have hnr : n ≤ d * r := ground_le_mul_corank (by omega) hn
  have hr : 2 ≤ r := by
    by_contra! h
    have hdr : d * r ≤ d := by simpa using Nat.mul_le_mul_left d (show r ≤ 1 by omega)
    omega
  let S := G.compls
  have hsized : ∀ A ∈ S, A.card = r := complements_uniform hG
  have hno := no_complement_cover (by omega) hG hsmall.le hdG
  have hmax := selected_card_of_no_cover (by omega : 0 < r) (by omega) (by omega) hnr S hno
  have hweight : n * S.card = (n - r) * n.choose r := by
    rw [show S.card = G.card from card_compls _, he, show n - r = k by omega]
    change n * (n - 1).choose (k - 1) = k * n.choose (n - k)
    rw [Nat.choose_symm hkn.le]
    exact choose_mul_rank n k (by omega) (by omega)
  have heq := card_eq_of_card_eq_weight (by omega : r ≤ n) hsized hmax hweight
  let F := (univ.powersetCard r) \ S
  have hFsel (p) : selected r F p = (selected r S p)ᶜ := by
    ext a
    rw [mem_selected, mem_compl, mem_selected]
    have hcard : (orderedArc r p a).card = r := by
      rw [orderedArc, card_map, card_arc (by omega)]
    exact mem_sdiff.trans
      ⟨And.right, fun h ↦ ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, h⟩⟩
  have hFcard (p) : (selected r F p).card = r := by
    rw [hFsel, card_compl, Fintype.card_fin, heq]
    omega
  have hpair (p) a (ha : a ∈ selected r F p) b (hb : b ∈ selected r F p) :
      ¬ Disjoint (arc r a) (arc r b) := by
    rw [hFsel, mem_compl, mem_selected] at ha hb
    have hc (c : Fin n) : (orderedArc r p c).card = r := by
      rw [orderedArc, card_map, card_arc (by omega)]
    intro hdab
    refine disjoint_forbidden_impossible (by omega) hR (by omega) hnr S hno heq
      (hc a) (hc b) ha hb ?_
    rw [orderedArc, orderedArc, disjoint_left]
    intro y hya hyb
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hya
    obtain ⟨v, hv, he⟩ := mem_map.mp hyb
    exact disjoint_left.mp hdab hu (p.injective he ▸ hv)
  have hfull (p) : ∃ v, selected r F p = startsThrough r v := by
    obtain ⟨v, hv⟩ := common_point_of_max_arcs (by omega) hR _ (hFcard p) (hpair p)
    refine ⟨v, eq_of_subset_of_card_le (fun a ha ↦ mem_filter.mpr ⟨mem_univ _, hv a ha⟩) ?_⟩
    rw [card_startsThrough (by omega), hFcard]
  obtain ⟨x, hx⟩ := global_star_of_circles hr hR F hfull
  refine ⟨x, fun A hA ↦ ?_⟩
  by_contra hxA
  have ha : Aᶜ ∈ S := mem_compls.mpr (by simpa using hA)
  exact (mem_sdiff.mp (hx _ (hsized _ ha) (mem_compl.mpr hxA))).2 ha

/--
**Mubayi's Erdős–Ko–Rado conjecture for $K(d)$-families holds.** For all natural numbers $n$, $k$
and $d$ with $3 \le d \le k$ and $n \ge dk/(d - 1)$, every $K(d)$-family $G$ of $k$-subsets of
$[n] = \{0, 1, \dots, n - 1\}$ satisfies $|G| \le \binom{n-1}{k-1}$, and if
$|G| = \binom{n-1}{k-1}$ then some element of $[n]$ lies in every member of $G$.

Currier proved the bound for $2 \le d \le k$, with the equality case for $d \ge 3$.

Source: D. Mubayi, in Combinatorics, Probability and Computing, Oberwolfach Reports 3
(2006), no. 48, p. 2922, Conjecture 3, DOI 10.4171/OWR/2006/48; resolution: G. Currier, On the
d-cluster generalization of Erdős-Ko-Rado, J. Combin. Theory Ser. A 182 (2021), 105464,
arXiv:1812.11153, abstract and Theorem 2: for 2 ≤ d ≤ k and n ≥ dk/(d - 1), a family of k-subsets of
[n] with no d-cluster (d members with empty intersection and union of size at most 2k) has at most
C(n - 1, k - 1) members, with equality only for a full star (d ≥ 3); this resolves Mubayi's
conjecture, https://arxiv.org/abs/1812.11153.
-/
public theorem kdFamilyErdosKoRado_holds : kdFamilyErdosKoRado := by
  intro n k d hd hdk hn G hG
  by_cases hlarge : 2 * k ≤ n
  · exact kd_in_sparse_range hd hdk hlarge hG
  · exact ⟨kd_card_le_in_dense_range hd hdk hn (by omega) hG,
      kd_eq_in_dense_range hd hdk hn (by omega) hG⟩

end MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011Wanted
