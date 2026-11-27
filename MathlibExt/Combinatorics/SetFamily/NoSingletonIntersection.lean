/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform families with no singleton intersection (Erdős Problem 702)

Frankl's theorem bounds the size of a uniform family avoiding singleton intersections.
To prove it, consider sets of two or three points that no member meets in exactly one point.
If every point has high degree, such sets cover the ground set. A protected triple containing
a protected pair forces a common pair at high degree. Otherwise the small protected sets through
each point have bounded union. Double counting one-point extensions then forces every point into
a protected pair, which gives too few extensions for high degree. Deleting a low-degree point
increases the excess over the claimed bound by Pascal's identity.

Source: T. F. Bloom, Erdős Problems, Problem #702, https://www.erdosproblems.com/702 (status
PROVED). UnsolvedMath record UM-30006985 (`EP-702`), dataset ulamai/UnsolvedMath v1.8.0.

Frankl's theorem is for `n` sufficiently large in terms of `k`, and the target keeps that
hypothesis: for all `n` the statement is false (for `k = 4`, `n = 5` the five `4`-subsets of a
`5`-set pairwise meet in `3` points and `5 > C(3, 2)`). Compared with the formal-conjectures
statement `ErdosProblems/702.lean` (formal-conjectures also proves `erdos_702.variants.all_n_false`
for k = 4, n = 5; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.NoSingletonIntersectionErdosProblem702Wanted

/-- **Erdős Problem 702 on singleton intersections.** For every $k \ge 4$ and every sufficiently
large $n$ (depending on $k$), every family of more than $\binom{n-2}{k-2}$ subsets of
$\{1, \dots, n\}$, each with exactly $k$ elements, contains two sets $A$ and $B$ with
$|A \cap B| = 1$.

This is Frankl's form of the problem of Erdős and Sós; without the hypothesis that $n$ is large
the statement fails, for instance for $k = 4$ and $n = 5$. -/
def noSingletonIntersectionBound : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (∀ A ∈ F, A.card = k) → (n - 2).choose (k - 2) < F.card →
      ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1

open Finset

variable {α : Type*} [DecidableEq α] {V : Finset α} {F : Finset (Finset α)} {k : ℕ}

-- Members containing a prescribed set.
private def star (F : Finset (Finset α)) (S : Finset α) := F.filter (S ⊆ ·)

private lemma mem_star {A S : Finset α} : A ∈ star F S ↔ A ∈ F ∧ S ⊆ A := mem_filter

-- Every member that hits S contains a second point of S.
private def Protected (F : Finset (Finset α)) (S : Finset α) : Prop :=
  ∀ A ∈ F, ∀ x ∈ S, x ∈ A → ∃ y ∈ S, y ≠ x ∧ y ∈ A

private lemma protected_of_inter {S : Finset α} (h : ∀ A ∈ F, (A ∩ S).card ≠ 1) :
    Protected F S := by
  intro A ha x hx hxa
  by_contra! hn
  have he : A ∩ S = {x} := by
    ext y
    simp only [mem_inter, mem_singleton]
    exact ⟨fun hy ↦ by_contra fun hne ↦ hn y hy.2 hne hy.1, fun e ↦ e ▸ ⟨hxa, hx⟩⟩
  exact h A ha (by simp [he])

private lemma full_star_card {S : Finset α} (hs : S ⊆ V) (hk : S.card ≤ k) :
    (star (V.powersetCard k) S).card = (V.card - S.card).choose (k - S.card) :=
  card_filter_powersetCard_subset S V k hs hk

private lemma star_card_le (hF : F ⊆ V.powersetCard k) {S : Finset α} (hs : S ⊆ V)
    (hk : S.card ≤ k) : (star F S).card ≤ (V.card - S.card).choose (k - S.card) := by
  rw [← full_star_card hs hk]
  exact card_le_card (filter_subset_filter _ hF)

-- Count a family covered by at most |I| subfamilies of size at most b.
omit [DecidableEq α] in
private lemma cover_bound {β : Type*} (I : Finset β) (G : Finset (Finset α))
    (H : β → Finset (Finset α)) (b : ℕ) (hc : ∀ A ∈ G, ∃ i ∈ I, A ∈ H i)
    (hb : ∀ i ∈ I, (H i).card ≤ b) : G.card ≤ I.card * b := by
  classical
  calc G.card ≤ (I.biUnion H).card := card_le_card fun _ ha ↦ mem_biUnion.mpr (hc _ ha)
    _ ≤ ∑ i ∈ I, (H i).card := card_biUnion_le
    _ ≤ _ := sum_le_card_nsmul _ _ _ hb

-- If S is unprotected, a member hitting it once supplies at most k ways to extend S.
private lemma extend_bound (hF : F ⊆ V.powersetCard k) (hP : ∀ E ∈ F, Protected F E)
    {S : Finset α} (hn : ¬ Protected F S) {b : ℕ}
    (hb : ∀ y ∈ V, y ∉ S → (star F (insert y S)).card ≤ b) :
    (star F S).card ≤ k * b := by
  unfold Protected at hn
  push Not at hn
  obtain ⟨E, he, x, hx, hxe, huniq⟩ := hn
  have hEV := mem_powersetCard.mp (hF he)
  calc (star F S).card ≤ (E \ S).card * b := by
          apply cover_bound _ _ (fun y ↦ star F (insert y S))
          · intro A ha
            obtain ⟨haf, hsa⟩ := mem_star.mp ha
            obtain ⟨y, hye, hyx, hya⟩ := hP E he A haf x hxe (hsa hx)
            exact ⟨y, mem_sdiff.mpr ⟨hye, fun hys ↦ huniq y hys hyx hye⟩,
              mem_star.mpr ⟨haf, insert_subset hya hsa⟩⟩
          · intro y hy
            exact hb y (hEV.1 (mem_sdiff.mp hy).1) (mem_sdiff.mp hy).2
    _ ≤ k * b := Nat.mul_le_mul_right _ (hEV.2 ▸ card_le_card sdiff_subset)

-- Double-count extensions of S and their subsets of size k - 1 containing S.
private lemma count_extensions (hF : F ⊆ V.powersetCard k) {S : Finset α} (hs : S ⊆ V)
    (hk : S.card < k) {b : ℕ}
    (hb : ∀ U ∈ V.powersetCard (k - 1), S ⊆ U → (star F U).card ≤ b) :
    (star F S).card * (k - S.card) ≤ (V.card - S.card).choose (k - 1 - S.card) * b := by
  rw [← full_star_card hs (show S.card ≤ k - 1 by omega)]
  apply card_mul_le_card_mul (fun A U ↦ U ⊆ A)
  · intro A ha
    obtain ⟨haf, hsa⟩ := mem_star.mp ha
    obtain ⟨hav, hak⟩ := mem_powersetCard.mp (hF haf)
    have hi : Set.InjOn (fun x ↦ A.erase x) ↑(A \ S) :=
      A.erase_injOn.mono (by exact_mod_cast (sdiff_subset : A \ S ⊆ A))
    rw [← hak, ← card_sdiff_of_subset hsa, ← card_image_of_injOn hi]
    apply card_le_card
    intro U hu
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    obtain ⟨hxa, hxs⟩ := mem_sdiff.mp hx
    exact mem_filter.mpr ⟨mem_star.mpr ⟨mem_powersetCard.mpr
      ⟨(erase_subset ..).trans hav, by rw [card_erase_of_mem hxa, hak]⟩,
      fun y hy ↦ mem_erase.mpr ⟨fun e ↦ hxs (e ▸ hy), hsa hy⟩⟩, erase_subset ..⟩
  · intro U hu
    obtain ⟨huv, hsu⟩ := mem_star.mp hu
    exact (card_le_card fun A ha ↦ mem_star.mpr
      ⟨(mem_star.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩).trans
      (hb U huv hsu)

private lemma protected_pair {x y : α} (hne : x ≠ y) :
    Protected F {x, y} ↔ ∀ A ∈ F, (x ∈ A ↔ y ∈ A) := by
  simp only [Protected, mem_insert, mem_singleton]
  grind

-- High degree forces each point into a protected pair or triple. At each failed
-- extension step there are at most k choices for the next point.
private lemma small_protected (hF : F ⊆ V.powersetCard k) (hP : ∀ E ∈ F, Protected F E)
    (hk : 4 ≤ k) {x : α} (hx : x ∈ V)
    (hd : k * (k * (k * (V.card - 3).choose (k - 4))) < (star F {x}).card) :
    ∃ S ⊆ V, x ∈ S ∧ S.card ≤ 3 ∧ Protected F S := by
  by_contra! hn
  have step {S : Finset α} {b : ℕ} (hs : S ⊆ V) (hxS : x ∈ S) (hc : S.card ≤ 3) :=
    extend_bound hF hP (hn S hs hxS hc) (b := b)
  apply hd.not_ge
  apply step (singleton_subset_iff.mpr hx) (mem_singleton_self _) (by simp)
  intro y hy hyx
  have hxy := insert_subset hy (singleton_subset_iff.mpr hx)
  have hc₂ : (insert y {x} : Finset α).card = 2 := by rw [card_insert_of_notMem hyx]; simp
  apply step hxy (mem_insert_of_mem (mem_singleton_self _)) (by omega)
  intro z hz hz'
  have hxyz := insert_subset hz hxy
  have hc₃ : (insert z (insert y {x}) : Finset α).card = 3 := by rw [card_insert_of_notMem hz', hc₂]
  apply step hxyz (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))) (by omega)
  intro w hw hw'
  have hc₄ : (insert w (insert z (insert y {x})) : Finset α).card = 4 := by
    rw [card_insert_of_notMem hw', hc₃]
  have h := star_card_le hF (insert_subset hw hxyz) (hc₄ ▸ hk)
  rw [hc₄] at h
  exact h.trans (Nat.choose_le_choose _ (by omega))

-- A protected triple containing a protected pair forces its third point to occur only
-- with that pair. At the full triple degree, every extension occurs.
private lemma nested_protected (hF : F ⊆ V.powersetCard k) (hP : ∀ E ∈ F, Protected F E)
    (hk : 4 ≤ k) (hn : 2 * k ≤ V.card) {p q z : α} (hpq : p ≠ q) (hzp : z ≠ p)
    (hzq : z ≠ q) (hV : ({z, p, q} : Finset α) ⊆ V) (hp : Protected F {p, q})
    (ht : Protected F {z, p, q})
    (hd : (V.card - 3).choose (k - 3) ≤ (star F {z}).card) :
    F.card ≤ (V.card - 2).choose (k - 2) := by
  let T : Finset α := {z, p, q}
  have hc : T.card = 3 := by simp [T, hzp, hzq, hpq]
  have hpair := (protected_pair hpq).mp hp
  have hforced (A) (ha : A ∈ F) (hz : z ∈ A) : T ⊆ A := by
    obtain ⟨y, hy, hyz, hya⟩ := ht A ha z (by simp) hz
    simp only [mem_insert, mem_singleton] at hy
    have h : p ∈ A ∨ q ∈ A := by grind
    exact insert_subset hz (insert_subset (h.elim id (hpair A ha).mpr)
      (singleton_subset_iff.mpr (h.elim (hpair A ha).mp id)))
  have he : star F {z} = star (V.powersetCard k) T := by
    apply eq_of_subset_of_card_le
    · intro A ha
      obtain ⟨haf, hza⟩ := mem_star.mp ha
      exact mem_star.mpr ⟨hF haf, hforced A haf (singleton_subset_iff.mp hza)⟩
    · rwa [full_star_card hV (by omega : T.card ≤ k), hc]
  have hall (E) (heF : E ∈ F) : p ∈ E := by
    by_contra hnp
    have hnq : q ∉ E := fun h ↦ hnp ((hpair E heF).mpr h)
    have hnz : z ∉ E := fun h ↦ hnp (hforced E heF h (by simp [T]))
    obtain ⟨hev, hek⟩ := mem_powersetCard.mp (hF heF)
    obtain ⟨w, hw⟩ := card_pos.mp (show 0 < E.card by omega)
    have hTV : T ⊆ V \ E := by
      intro a ha
      exact mem_sdiff.mpr ⟨hV ha, by
        simp only [T, mem_insert, mem_singleton] at ha
        grind⟩
    have hsmall : (insert w T).card ≤ k := (card_insert_le ..).trans (by omega)
    have hlarge : k ≤ (insert w (V \ E)).card := by
      have := card_le_card (subset_insert w (V \ E))
      rw [card_sdiff_of_subset hev, hek] at this
      omega
    obtain ⟨A, hA, hAV, hAk⟩ := exists_subsuperset_card_eq (insert_subset_insert w hTV)
      hsmall hlarge
    have hAT := (subset_insert w T).trans hA
    have ha : A ∈ star (V.powersetCard k) T := mem_star.mpr
      ⟨mem_powersetCard.mpr ⟨hAV.trans (insert_subset (hev hw) sdiff_subset), hAk⟩, hAT⟩
    rw [← he] at ha
    obtain ⟨y, hyE, hyw, hyA⟩ := hP E heF A (mem_star.mp ha).1 w hw (hA (mem_insert_self ..))
    exact (mem_sdiff.mp ((mem_insert.mp (hAV hyA)).resolve_left hyw)).2 hyE
  have hpV : ({p, q} : Finset α) ⊆ V := (subset_insert z _).trans hV
  have hc₂ : ({p, q} : Finset α).card = 2 := by simp [hpq]
  calc F.card ≤ (star (V.powersetCard k) {p, q}).card := by
         apply card_le_card
         intro E he
         exact mem_star.mpr ⟨hF he, insert_subset (hall E he)
           (singleton_subset_iff.mpr ((hpair E he).mp (hall E he)))⟩
    _ = _ := by rw [full_star_card hpV (by omega), hc₂]

-- If S is not protected, one member meets it only at x.
omit [DecidableEq α] in
private lemma witness_of_unprotected {S : Finset α} (h : ¬ Protected F S) :
    ∃ E ∈ F, ∃ x ∈ S, x ∈ E ∧ ∀ y ∈ S, y ∈ E → y = x := by
  unfold Protected at h
  push Not at h
  obtain ⟨E, he, x, hx, hxe, hu⟩ := h
  exact ⟨E, he, x, hx, hxe, fun y hy hyE ↦ by_contra fun hne ↦ hu y hy hne hyE⟩

-- Bound the number of points sharing a small protected set with p. Fix a member E
-- through p. A protected triple {p,q,z} with z outside E has q in E. A witness
-- separating p and q must then contain z.
private lemma neighbors (hF : F ⊆ V.powersetCard k) {p : α} {E : Finset α} (he : E ∈ F)
    (hpe : p ∈ E)
    (hnest : ∀ q z, p ≠ q → z ≠ p → z ≠ q → ({z, p, q} : Finset α) ⊆ V →
      Protected F {p, q} → ¬ Protected F {z, p, q}) :
    ∃ N : Finset α, N.card ≤ k + k * k ∧ ∀ S ⊆ V, S.card ≤ 3 → Protected F S →
      p ∈ S → S ⊆ N := by
  classical
  have hex (q : α) : ∃ B : Finset α, B.card ≤ k ∧
      (¬ Protected F {p, q} → ∃ a ∈ ({p, q} : Finset α), a ∈ B ∧
        B ∈ F ∧ ∀ b ∈ ({p, q} : Finset α), b ∈ B → b = a) := by
    by_cases h : Protected F {p, q}
    · exact ⟨∅, by simp, by simp [h]⟩
    obtain ⟨B, hb, a, ha, hab, hu⟩ := witness_of_unprotected h
    exact ⟨B, (mem_powersetCard.mp (hF hb)).2.le, fun _ ↦ ⟨a, ha, hab, hb, hu⟩⟩
  choose B hBk hB using hex
  have hEk := (mem_powersetCard.mp (hF he)).2
  refine ⟨E ∪ E.biUnion B, ?_, ?_⟩
  · calc _ ≤ E.card + (E.biUnion B).card := card_union_le _ _
         _ ≤ E.card + E.card * k := Nat.add_le_add_left
           (card_biUnion_le.trans (sum_le_card_nsmul _ _ _ (fun q _ ↦ hBk q))) _
         _ = _ := by rw [hEk]
  · intro S hSV hc hs hps z hzs
    by_cases hze : z ∈ E
    · exact mem_union_left _ hze
    obtain ⟨q, hqs, hqp, hqe⟩ := hs E he p hps hpe
    have hzp : z ≠ p := fun e ↦ hze (e ▸ hpe)
    have hzq : z ≠ q := fun e ↦ hze (e ▸ hqe)
    have hsub : ({z, p, q} : Finset α) ⊆ S := insert_subset hzs
      (insert_subset hps (singleton_subset_iff.mpr hqs))
    have heq : ({z, p, q} : Finset α) = S := eq_of_subset_of_card_le hsub (by
      simpa [hzp, hzq, hqp.symm] using hc)
    have ht : Protected F {z, p, q} := heq ▸ hs
    have hnp : ¬ Protected F {p, q} := fun h ↦ hnest q z hqp.symm hzp hzq (hsub.trans hSV) h ht
    obtain ⟨a, ha, haB, hbF, hu⟩ := hB q hnp
    obtain ⟨b, hb, hba, hbB⟩ := ht _ hbF a (mem_insert_of_mem ha) haB
    have hbz := (mem_insert.mp hb).resolve_right (fun hb' ↦ hba (hu b hb' hbB))
    exact mem_union_right E (mem_biUnion.mpr ⟨q, hqe, hbz ▸ hbB⟩)

private lemma bounded_extensions (hF : F ⊆ V.powersetCard k) (hk : 0 < k)
    (hsmall : ∀ x ∈ V, ∃ S ⊆ V, x ∈ S ∧ S.card ≤ 3 ∧ Protected F S)
    (N : α → Finset α) (hN : ∀ x ∈ V, (N x).card ≤ k + k * k ∧
      ∀ S ⊆ V, S.card ≤ 3 → Protected F S → x ∈ S → S ⊆ N x)
    {U : Finset α} (hu : U ∈ V.powersetCard (k - 1)) :
    (star F U).card ≤ k * (k + k * k) := by
  obtain ⟨huv, huk⟩ := mem_powersetCard.mp hu
  have hsub : star F U ⊆ (U.biUnion N).image (fun x ↦ insert x U) := by
    intro A ha
    obtain ⟨haf, hua⟩ := mem_star.mp ha
    obtain ⟨hav, hak⟩ := mem_powersetCard.mp (hF haf)
    obtain ⟨x, hxU, he⟩ := exists_eq_insert_iff.mpr ⟨hua, by omega⟩
    have hx : x ∈ A := he ▸ mem_insert_self ..
    obtain ⟨S, hsv, hxs, hc, hs⟩ := hsmall x (hav hx)
    obtain ⟨y, hys, hyx, hya⟩ := hs A haf x hxs hx
    rw [← he] at hya
    have hyU := (mem_insert.mp hya).resolve_left hyx
    have hxN := (hN y (huv hyU)).2 S hsv hc hs hys hxs
    exact mem_image.mpr ⟨x, mem_biUnion.mpr ⟨y, hyU, hxN⟩, he⟩
  calc _ ≤ (U.biUnion N).card := (card_le_card hsub).trans card_image_le
       _ ≤ U.card * (k + k * k) := card_biUnion_le.trans
         (sum_le_card_nsmul _ _ _ fun y hy ↦ (hN y (huv hy)).1)
       _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

-- Once every point belongs to a protected pair, a (k-1)-set has at most one extension.
private lemma unique_extension (hF : F ⊆ V.powersetCard k) (hk : 0 < k)
    (hp : ∀ x ∈ V, ∃ y, x ≠ y ∧ Protected F {x, y})
    {U : Finset α} (hu : U ∈ V.powersetCard (k - 1)) : (star F U).card ≤ 1 := by
  apply card_le_one.mpr
  intro A ha B hb
  obtain ⟨haf, hua⟩ := mem_star.mp ha
  obtain ⟨hbf, hub⟩ := mem_star.mp hb
  have hak := mem_powersetCard.mp (hF haf)
  have hbk := mem_powersetCard.mp (hF hbf)
  have huk := (mem_powersetCard.mp hu).2
  obtain ⟨x, hxU, he⟩ := exists_eq_insert_iff.mpr ⟨hua, by omega⟩
  have hx : x ∈ A := he ▸ mem_insert_self ..
  obtain ⟨y, hxy, hp⟩ := hp x (hak.1 hx)
  have ht := (protected_pair hxy).mp hp
  have hya := (ht A haf).mp hx
  rw [← he] at hya
  have hxb := (ht B hbf).mpr (hub ((mem_insert.mp hya).resolve_left hxy.symm))
  exact eq_of_subset_of_card_le (he ▸ insert_subset hxb hub) (by omega)

-- The ratio of adjacent binomial coefficients eventually exceeds any fixed constant.
private lemma choose_gap (r c n : ℕ) (hn : r + c * (r + 1) < n) :
    c * n.choose r < n.choose (r + 1) := by
  have hp : 0 < n.choose r := Nat.choose_pos (by omega)
  have he := Nat.choose_succ_right_eq n r
  have hlt := Nat.mul_lt_mul_of_pos_left (show c * (r + 1) < n - r by omega) hp
  nlinarith only [he, hlt]

-- A counterexample on a large ground set has a point of degree strictly below the
-- increment in the extremal bound.
private lemma low_degree (hF : F ⊆ V.powersetCard k) (hP : ∀ E ∈ F, Protected F E)
    (hk : 4 ≤ k) (hn : 2 * k ≤ V.card)
    (hgap : k * (k * (k * (k + k * k))) * (V.card - 3).choose (k - 4) <
      (V.card - 3).choose (k - 3))
    (hbig : (V.card - 2).choose (k - 2) < F.card) :
    ∃ x ∈ V, (star F {x}).card < (V.card - 3).choose (k - 3) := by
  classical
  by_contra! hd
  let b := (V.card - 3).choose (k - 4)
  let d := (V.card - 3).choose (k - 3)
  have hratio : k * (k * (k * (k + k * k) * b)) < d := by
    simpa only [b, d, Nat.mul_assoc] using hgap
  have hpos : 0 < d := (Nat.zero_le _).trans_lt hratio
  have hsmall (x) (hx : x ∈ V) : ∃ S ⊆ V, x ∈ S ∧ S.card ≤ 3 ∧ Protected F S := by
    apply small_protected hF hP hk hx
    apply lt_of_lt_of_le _ (hd x hx)
    apply lt_of_le_of_lt _ hratio
    dsimp [b]
    gcongr
    nlinarith
  have hN (p : α) : ∃ N : Finset α, p ∈ V → N.card ≤ k + k * k ∧
      ∀ S ⊆ V, S.card ≤ 3 → Protected F S → p ∈ S → S ⊆ N := by
    by_cases hp : p ∈ V
    · obtain ⟨E, he⟩ := card_pos.mp (hpos.trans_le (hd p hp))
      obtain ⟨hef, hpE⟩ := mem_star.mp he
      obtain ⟨N, hN⟩ := neighbors hF hef (singleton_subset_iff.mp hpE)
        (fun q z hpq hzp hzq hv hpair ht ↦ hbig.not_ge
          (nested_protected hF hP hk hn hpq hzp hzq hv hpair ht (hd z (hv (mem_insert_self ..)))))
      exact ⟨N, fun _ ↦ hN⟩
    · exact ⟨∅, fun h ↦ (hp h).elim⟩
  choose N hN using hN
  have hext {U : Finset α} := bounded_extensions hF (by omega) hsmall N hN (U := U)
  -- Without a protected pair through x, two extension steps suffice to bound its degree.
  have hpair (x) (hx : x ∈ V) : ∃ y, x ≠ y ∧ Protected F {x, y} := by
    by_contra! hno
    have hnot : ¬ Protected F {x} := by
      obtain ⟨E, he⟩ := card_pos.mp (hpos.trans_le (hd x hx))
      obtain ⟨hef, hes⟩ := mem_star.mp he
      intro h
      simpa using h E hef x (by simp) (singleton_subset_iff.mp hes)
    apply hratio.not_ge
    apply le_trans (hd x hx)
    apply extend_bound hF hP hnot
    intro y hy hyx
    have hxy : x ≠ y := (by simpa using hyx : y ≠ x).symm
    apply extend_bound hF hP (S := {y, x})
      (by simpa only [pair_comm y x] using hno y hxy)
    intro z hz hz'
    let S : Finset α := {z, y, x}
    have hc : S.card = 3 := by
      change (insert z {y, x} : Finset α).card = 3
      rw [card_insert_of_notMem hz']; simp [hxy.symm]
    have hsv : S ⊆ V := insert_subset hz (insert_subset hy (singleton_subset_iff.mpr hx))
    have h := count_extensions hF hsv (by omega : S.card < k) (fun U hu _ ↦ hext hu)
    have hle := Nat.le_mul_of_pos_right (star F S).card (show 0 < k - S.card by omega)
    rw [hc, show k - 1 - 3 = k - 4 by omega, Nat.mul_comm _ (k * _)] at h
    rw [hc] at hle
    exact hle.trans h
  -- Every point now has a partner, so the last double count has multiplicity one.
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < V.card by omega)
  obtain ⟨y, hxy, ht⟩ := hpair x hx
  obtain ⟨A, ha⟩ := card_pos.mp (hpos.trans_le (hd x hx))
  obtain ⟨haf, hxa⟩ := mem_star.mp ha
  have hy := (mem_powersetCard.mp (hF haf)).1
    (((protected_pair hxy).mp ht A haf).mp (singleton_subset_iff.mp hxa))
  have hs : ({x, y} : Finset α) ⊆ V := insert_subset hx (singleton_subset_iff.mpr hy)
  have hc : ({x, y} : Finset α).card = 2 := by simp [hxy]
  have heq : star F {x} = star F {x, y} := by
    ext E
    simp only [mem_star, singleton_subset_iff, insert_subset_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2, ((protected_pair hxy).mp ht E h.1).mp h.2⟩,
      fun h ↦ ⟨h.1, h.2.1⟩⟩
  have hcoun := count_extensions hF hs (by omega : ({x, y} : Finset α).card < k)
    (fun U hu _ ↦ unique_extension hF (by omega) hpair hu)
  rw [hc, mul_one, ← heq, show k - 1 - 2 = k - 3 by omega] at hcoun
  have hpas : (V.card - 2).choose (k - 3) = d + b := by
    rw [show V.card - 2 = (V.card - 3) + 1 by omega,
      show k - 3 = (k - 4) + 1 by omega, Nat.choose_succ_succ]
    dsimp [d, b]
    rw [show k - 4 + 1 = k - 3 by omega, Nat.add_comm]
  rw [hpas] at hcoun
  have hbd : b < d := lt_of_le_of_lt (Nat.le_mul_of_pos_left b (by positivity)) hgap
  have h₂ := (Nat.mul_le_mul (hd x hx) (show 2 ≤ k - 2 by omega))
  change d * 2 ≤ _ at h₂
  omega

-- Each deletion increases the excess of the family size over the binomial bound.
-- At ground size m that excess is at most 2^m, so a counterexample cannot persist
-- through 2^m deletions.
omit [DecidableEq α] in
private lemma deletion_bound {m : ℕ} (hk : 4 ≤ k) (hm : 2 * k ≤ m)
    (hgap : ∀ n ≥ m, k * (k * (k * (k + k * k))) * (n - 3).choose (k - 4) <
      (n - 3).choose (k - 3)) (t : ℕ) (hn : V.card = m + t) (hF : F ⊆ V.powersetCard k)
    (hP : ∀ E ∈ F, Protected F E) (hbig : (V.card - 2).choose (k - 2) < F.card) :
    F.card + t ≤ (V.card - 2).choose (k - 2) + 2 ^ m := by
  classical
  induction t generalizing V F with
  | zero =>
    have h := card_le_card ((show F ⊆ V.powerset from fun A ha ↦ mem_powerset.mpr
      (mem_powersetCard.mp (hF ha)).1))
    rw [card_powerset, hn, Nat.add_zero] at h
    omega
  | succ t ih =>
    obtain ⟨x, hx, hd⟩ := low_degree hF hP hk (by omega) (hgap _ (by omega)) hbig
    let G := F.filter (x ∉ ·)
    let W := V.erase x
    have hW : W.card = m + t := by dsimp [W]; rw [card_erase_of_mem hx, hn]; omega
    have hpart : G.card + (star F {x}).card = F.card := by
      simp only [G, star, singleton_subset_iff]
      simpa using F.card_filter_add_card_filter_not (fun A ↦ x ∉ A)
    have hG : G ⊆ W.powersetCard k := by
      intro A ha
      obtain ⟨haf, hxa⟩ := mem_filter.mp ha
      obtain ⟨hav, hak⟩ := mem_powersetCard.mp (hF haf)
      exact mem_powersetCard.mpr
        ⟨fun a ha ↦ mem_erase.mpr ⟨fun e ↦ hxa (e ▸ ha), hav ha⟩, hak⟩
    have hPG : ∀ E ∈ G, Protected G E :=
      fun E he A ha ↦ hP E (mem_filter.mp he).1 A (mem_filter.mp ha).1
    have hpas : (V.card - 2).choose (k - 2) =
        (W.card - 2).choose (k - 2) + (V.card - 3).choose (k - 3) := by
      rw [show V.card - 2 = (V.card - 3) + 1 by omega,
        show k - 2 = (k - 3) + 1 by omega, Nat.choose_succ_succ,
        show W.card - 2 = V.card - 3 by omega, Nat.add_comm]
    have := ih hW hG hPG (by omega)
    omega

/--
**Frankl's theorem on families with no singleton intersection.** For every $k \ge 4$ and every
sufficiently large $n$ (depending on $k$), every family of more than $\binom{n-2}{k-2}$ subsets of
$\{1, \dots, n\}$, each with exactly $k$ elements, contains two sets $A$ and $B$ with
$|A \cap B| = 1$.

This resolves Erdős Problem 702 of Erdős and Sós; Katona had the case $k = 4$. The hypothesis that
$n$ is large is needed ($k = 4$, $n = 5$).

Source: T. F. Bloom, Erdős Problems, Problem
#702, https://www.erdosproblems.com/702 (status PROVED); resolution: P. Frankl, On families of
finite sets no two of which intersect in a singleton, Bull. Austral. Math. Soc. 17 (1977), 125-134,
P. Keevash, D. Mubayi and R. M. Wilson, Set systems with no singleton intersection, abstract:
'Frankl showed that |F| ≤ C(n-2, k-2) for k ≥ 4 and n sufficiently large, confirming a conjecture of
Erdős and Sós'; erdosproblems.com/702: Frankl proved this for all k ≥ 4,
https://www.math.cmu.edu/users/mubayi/papers/no-singleton.pdf.
-/
theorem noSingletonIntersectionBound_holds : noSingletonIntersectionBound := by
  classical
  intro k hk
  let c := k * (k * (k * (k + k * k)))
  let m := 2 * k + (k - 4) + c * (k - 4 + 1) + 4
  have hm : 2 * k ≤ m := by dsimp [m]; omega
  have hgap (n : ℕ) (hn : m ≤ n) :
      c * (n - 3).choose (k - 4) < (n - 3).choose (k - 3) := by
    rw [show k - 3 = (k - 4) + 1 by omega]
    apply choose_gap
    dsimp [m] at hn
    omega
  filter_upwards [Filter.eventually_ge_atTop (m + 2 ^ m)] with n hn
  intro F hu hbig
  by_contra! hno
  let V : Finset (Fin n) := univ
  have hV : V.card = n := by simp [V]
  have hF : F ⊆ V.powersetCard k := fun A ha ↦
    mem_powersetCard.mpr ⟨subset_univ _, hu A ha⟩
  have hP (E) (he : E ∈ F) : Protected F E :=
    protected_of_inter fun A ha ↦ hno A ha E he
  change m + 2 ^ m ≤ n at hn
  have hnm : m ≤ n := (Nat.le_add_right ..).trans hn
  have hsize : V.card = m + (n - m) := by rw [hV, Nat.add_sub_of_le hnm]
  have hle := deletion_bound hk hm hgap (n - m) hsize hF hP (by rwa [hV])
  rw [hV] at hle
  omega

end MathlibExt.Combinatorics.NoSingletonIntersectionErdosProblem702Wanted
