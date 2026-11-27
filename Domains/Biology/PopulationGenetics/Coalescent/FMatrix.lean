/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Fintype

/-!
# F-matrix encoding and metrics on ranked tree shapes

A *ranked tree shape* is a rooted binary tree without leaf labels whose change points
(coalescences and, for heterochronous samples, sampling events) are totally ordered in time.
Kim, Rosenberg and Palacios (2020) encode a ranked tree shape with `n` leaves and `m` sampling
events by its *F matrix*, a lower-triangular `(n + m - 2) × (n + m - 2)` matrix of lineage
counts, and compare ranked tree shapes, and ranked genealogies with branch lengths, by entrywise
distances between these matrices.

We record a labeled ranked history by its lineages between consecutive change points, each
lineage given by its set of sampled descendant leaves (`LabeledRankedHistory`); a ranked tree
shape is such a history up to relabelling of the leaves (`RankedTreeShape`). Entry `(i, j)` of
the F matrix, for `j ≤ i`, is the number of lineages common to the intervals `j` and `i`
(counted from the root); such a lineage persists, without bifurcating or ending at a sampling
event, through every interval in between (`LabeledRankedHistory.mem_lineages_of_mem_of_mem`).
A ranked labeled history of `n` genes (`RankedHistory`) is a labeled ranked history with one
sampling event, whose lineages are its ancestral partitions.

The unique encoding is proved by extending a relabelling of the leaves one change point at a
time, from the most recent: the F matrix fixes the type of each change point, the number of
leaves sampled there, and, for a coalescence, the intervals in which the two merging lineages
were born, which determines them up to swapping single leaves born together.

Indices follow Lean's convention: row and column `i` of the F matrix is the interval `i + 1` of
the source, and `F_{i,i} = i + 1` there reads `T.fMatrix i i = i + 2` here.

## Main definitions

* `LabeledRankedHistory n m`, `RankedTreeShape n m`: labeled ranked histories and ranked tree
  shapes with `n` leaves and `m` sampling events.
* `RankedTreeShape.fMatrix`, `RankedHistory.fMatrix`: the F matrix.
* `RankedTreeShape.d₁`, `RankedTreeShape.d₂`: the `L¹` and `L²` distances (Eqs. 1–2).
* `RankedGenealogy n m`, `RankedGenealogy.weightMatrix`, `RankedGenealogy.dw₁`,
  `RankedGenealogy.dw₂`: ranked genealogies, their weight matrices and the weighted distances
  (Eqs. 3–4).
* `l2MedoidSet`, `meanSquaredDistance`: the `L²`-medoid set of a sample and the dispersion
  around a point (Eqs. 5–7).

## Main results

* `LabeledRankedHistory.card_coalescences_and_samplings`: a labeled ranked history with `n`
  leaves and `m` sampling events has `n - 1` coalescences and `m` sampling events.
* `RankedTreeShape.fMatrix_injective`: the F matrix determines the ranked tree shape
  (Theorem 1), and `RankedHistory.fMatrix_eq_fMatrix_iff` for ranked labeled histories.
* `RankedTreeShape.fMatrix_diag_of_isochronous`: the diagonal of an isochronous F matrix.
* `RankedTreeShape.d₁_isMetric`, `RankedTreeShape.d₂_isMetric`: `d₁` and `d₂` are metrics.
* `RankedGenealogy.dw₁_pseudometric`, `RankedGenealogy.dw₂_pseudometric`: the weighted distances
  are pseudometrics, and `RankedGenealogy.eq_of_dw₁_eq_zero_of_isochronous`,
  `RankedGenealogy.eq_of_dw₂_eq_zero_of_isochronous`: they are metrics on isochronous ranked
  genealogies (Proposition 2 for `m = 1`). `RankedGenealogy.eq_of_weighted_eq` reduces the
  heterochronous case to the diagonals of the F matrices.
* `l2MedoidSet_nonempty`: a nonempty sample has an `L²`-medoid.

## References

* J. Kim, N. A. Rosenberg and J. A. Palacios, *Distance metrics for ranked evolutionary trees*,
  Proc. Natl. Acad. Sci. USA 117 (2020), 28876–28886, Theorem 1, Eqs. 1–7 and Proposition 2.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Lineage sets and relabelling of leaves -/

section Lineages

variable {α : Type*}

private theorem map_mul_toEmbedding (σ τ : Equiv.Perm α) (B : Finset α) :
    B.map (σ * τ).toEmbedding = (B.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

private theorem map_eq_self_of_forall {σ : Equiv.Perm α} {B : Finset α} (h : ∀ y ∈ B, σ y = y) :
    B.map σ.toEmbedding = B := by
  ext y
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [h z hz]
  · exact fun hy => ⟨y, hy, h y hy⟩

variable [DecidableEq α]

/-- Relabel the leaves of a set of lineages, each lineage given by its set of leaves, by a
permutation `σ` of the leaves. -/
def relabelLineages (σ : Equiv.Perm α) (S : Finset (Finset α)) : Finset (Finset α) :=
  S.image (Finset.map σ.toEmbedding)

theorem relabelLineages_one (S : Finset (Finset α)) : relabelLineages 1 S = S := by
  have h : ∀ B : Finset α, B.map (1 : Equiv.Perm α).toEmbedding = B :=
    fun _ => map_eq_self_of_forall fun _ _ => rfl
  rw [relabelLineages, Finset.image_congr (g := id) fun B _ => h B, Finset.image_id]

theorem relabelLineages_mul (σ τ : Equiv.Perm α) (S : Finset (Finset α)) :
    relabelLineages (σ * τ) S = relabelLineages σ (relabelLineages τ S) := by
  simp only [relabelLineages, Finset.image_image]
  exact Finset.image_congr fun B _ => map_mul_toEmbedding σ τ B

theorem map_mem_relabelLineages_iff (σ : Equiv.Perm α) (S : Finset (Finset α)) (B : Finset α) :
    B.map σ.toEmbedding ∈ relabelLineages σ S ↔ B ∈ S :=
  (Finset.map_injective _).mem_finset_image

theorem card_relabelLineages (σ : Equiv.Perm α) (S : Finset (Finset α)) :
    (relabelLineages σ S).card = S.card :=
  Finset.card_image_of_injective _ (Finset.map_injective _)

theorem relabelLineages_inter (σ : Equiv.Perm α) (S T : Finset (Finset α)) :
    relabelLineages σ (S ∩ T) = relabelLineages σ S ∩ relabelLineages σ T :=
  Finset.image_inter _ _ (Finset.map_injective _)

theorem relabelLineages_union (σ : Equiv.Perm α) (S T : Finset (Finset α)) :
    relabelLineages σ (S ∪ T) = relabelLineages σ S ∪ relabelLineages σ T :=
  Finset.image_union _ _

theorem relabelLineages_coalescence (σ : Equiv.Perm α) (S : Finset (Finset α)) (X Y : Finset α) :
    relabelLineages σ (insert (X ∪ Y) ((S.erase X).erase Y)) =
      insert (X.map σ.toEmbedding ∪ Y.map σ.toEmbedding)
        (((relabelLineages σ S).erase (X.map σ.toEmbedding)).erase (Y.map σ.toEmbedding)) := by
  rw [relabelLineages, Finset.image_insert, Finset.image_erase (Finset.map_injective _),
    Finset.image_erase (Finset.map_injective _), Finset.map_union]
  rfl

theorem relabelLineages_image_singleton (σ : Equiv.Perm α) (A : Finset α) :
    relabelLineages σ (A.image ({·})) = (A.map σ.toEmbedding).image ({·}) := by
  ext B
  simp only [relabelLineages, Finset.image_image, Finset.mem_image, Finset.mem_map,
    Function.comp_apply, Finset.map_singleton, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨σ a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem relabelLineages_eq_self {σ : Equiv.Perm α} {S : Finset (Finset α)}
    (h : ∀ B ∈ S, B.map σ.toEmbedding ∈ S) : relabelLineages σ S = S := by
  refine Finset.eq_of_subset_of_card_le (fun B hB => ?_) (card_relabelLineages σ S).ge
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hB
  exact h C hC

private theorem map_swap_eq_self {x x' : α} {B : Finset α} (hx : x ∉ B) (hx' : x' ∉ B) :
    B.map (Equiv.swap x x').toEmbedding = B :=
  map_eq_self_of_forall fun _ hy =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ hy)) (fun h => hx' (h ▸ hy))

/-- `S'` arises from `S` by a **coalescence**: two distinct lineages `X, Y` of `S` merge into
the lineage `X ∪ Y`. -/
def IsCoalescence (S S' : Finset (Finset α)) : Prop :=
  ∃ X ∈ S, ∃ Y ∈ S, X ≠ Y ∧ S' = insert (X ∪ Y) ((S.erase X).erase Y)

/-- `S'` arises from `S` by a **sampling event**: the leaves of a nonempty set `A`, none of
which lies in a lineage of `S`, join as single-leaf lineages. -/
def IsSampling (S S' : Finset (Finset α)) : Prop :=
  ∃ A : Finset α, A.Nonempty ∧ (∀ B ∈ S, Disjoint A B) ∧ S' = S ∪ A.image ({·})

end Lineages

/-! ### Chains of lineage sets

A chain `S 0, …, S K` starts with single-leaf lineages and changes at each step by a
coalescence or a sampling event. The lemmas below are the invariants that the unique-encoding
theorem uses: lineages stay nonempty and pairwise disjoint, every lineage lies in a lineage of
each later set, and a lineage is present at an interval of steps. -/

section Chains

variable {α : Type*} [DecidableEq α]

/-- `S 0, …, S K` is a chain of lineage sets: `S 0` consists of single-leaf lineages, and each
step is a coalescence or a sampling event. -/
private structure IsChain (S : ℕ → Finset (Finset α)) (K : ℕ) : Prop where
  initial : ∃ A : Finset α, S 0 = A.image ({·})
  step : ∀ t < K, IsCoalescence (S t) (S (t + 1)) ∨ IsSampling (S t) (S (t + 1))

omit [DecidableEq α] in
/-- The lineages of `T` are nonempty and pairwise disjoint. -/
private def Separated (T : Finset (Finset α)) : Prop :=
  (∀ B ∈ T, B.Nonempty) ∧ ∀ B ∈ T, ∀ C ∈ T, B ≠ C → Disjoint B C

private theorem separated_image_singleton (A : Finset α) : Separated (A.image ({·})) := by
  refine ⟨fun B hB => ?_, fun B hB C hC hBC => ?_⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hB
    exact Finset.singleton_nonempty a
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hC
    exact Finset.disjoint_singleton.2 fun h => hBC (h ▸ rfl)

omit [DecidableEq α] in
private theorem Separated.eq_of_subset {T : Finset (Finset α)} (hT : Separated T)
    {B Z : Finset α} (hB : B ∈ T) (hZ : Z ∈ T) (hBZ : B ⊆ Z) : B = Z := by
  by_contra hne
  obtain ⟨x, hx⟩ := hT.1 B hB
  exact Finset.disjoint_left.1 (hT.2 B hB Z hZ hne) hx (hBZ hx)

private theorem union_notMem {T : Finset (Finset α)} (hT : Separated T) {X Y : Finset α}
    (hX : X ∈ T) (hY : Y ∈ T) (hXY : X ≠ Y) : X ∪ Y ∉ T := by
  intro h
  have hXU : X ∪ Y ≠ X := by
    intro heq
    obtain ⟨y, hy⟩ := hT.1 Y hY
    have hyX : y ∈ X := heq ▸ Finset.mem_union_right X hy
    exact Finset.disjoint_left.1 (hT.2 X hX Y hY hXY) hyX hy
  obtain ⟨x, hx⟩ := hT.1 X hX
  exact Finset.disjoint_left.1 (hT.2 _ h X hX hXU) (Finset.mem_union_left Y hx) hx

private theorem mem_coalescence_iff {T : Finset (Finset α)} {X Y B : Finset α} :
    B ∈ insert (X ∪ Y) ((T.erase X).erase Y) ↔ B = X ∪ Y ∨ (B ≠ Y ∧ B ≠ X ∧ B ∈ T) := by
  simp [Finset.mem_insert, Finset.mem_erase]

private theorem separated_coalescence {T : Finset (Finset α)} (hT : Separated T)
    {X Y : Finset α} (hX : X ∈ T) (hY : Y ∈ T) :
    Separated (insert (X ∪ Y) ((T.erase X).erase Y)) := by
  refine ⟨fun B hB => ?_, fun B hB C hC hBC => ?_⟩
  · rcases mem_coalescence_iff.1 hB with rfl | ⟨-, -, hB⟩
    · exact (hT.1 X hX).mono Finset.subset_union_left
    · exact hT.1 B hB
  · rcases mem_coalescence_iff.1 hB with rfl | ⟨hBY, hBX, hB⟩ <;>
      rcases mem_coalescence_iff.1 hC with rfl | ⟨hCY, hCX, hC⟩
    · exact absurd rfl hBC
    · exact Finset.disjoint_union_left.2
        ⟨hT.2 X hX C hC (Ne.symm hCX), hT.2 Y hY C hC (Ne.symm hCY)⟩
    · exact Finset.disjoint_union_right.2 ⟨hT.2 B hB X hX hBX, hT.2 B hB Y hY hBY⟩
    · exact hT.2 B hB C hC hBC

private theorem separated_sampling {T : Finset (Finset α)} (hT : Separated T) {A : Finset α}
    (hA : ∀ B ∈ T, Disjoint A B) : Separated (T ∪ A.image ({·})) := by
  have hsg := separated_image_singleton A
  refine ⟨fun B hB => ?_, fun B hB C hC hBC => ?_⟩
  · rcases Finset.mem_union.1 hB with hB | hB
    · exact hT.1 B hB
    · exact hsg.1 B hB
  · rcases Finset.mem_union.1 hB with hB | hB <;> rcases Finset.mem_union.1 hC with hC | hC
    · exact hT.2 B hB C hC hBC
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
      exact Finset.disjoint_singleton_right.2 fun h => Finset.disjoint_left.1 (hA B hB) ha h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
      exact Finset.disjoint_singleton_left.2 fun h => Finset.disjoint_left.1 (hA C hC) ha h
    · exact hsg.2 B hB C hC hBC

private theorem card_coalescence {T : Finset (Finset α)} (hT : Separated T) {X Y : Finset α}
    (hX : X ∈ T) (hY : Y ∈ T) (hXY : X ≠ Y) :
    (insert (X ∪ Y) ((T.erase X).erase Y)).card + 1 = T.card := by
  have hn : X ∪ Y ∉ (T.erase X).erase Y := fun h =>
    union_notMem hT hX hY hXY (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have h2 : 1 < T.card := Finset.one_lt_card.2 ⟨X, hX, Y, hY, hXY⟩
  rw [Finset.card_insert_of_notMem hn,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hXY, hY⟩), Finset.card_erase_of_mem hX]
  omega

private theorem card_sampling {T : Finset (Finset α)} {A : Finset α}
    (hA : ∀ B ∈ T, Disjoint A B) : (T ∪ A.image ({·})).card = T.card + A.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Finset.singleton_injective]
  rw [Finset.disjoint_left]
  intro B hB hB'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB'
  exact Finset.disjoint_left.1 (hA _ hB) ha (Finset.mem_singleton_self a)

variable {S : ℕ → Finset (Finset α)} {K : ℕ}

private theorem IsChain.separated (hS : IsChain S K) {t : ℕ} (ht : t ≤ K) : Separated (S t) := by
  induction t with
  | zero =>
    obtain ⟨A, hA⟩ := hS.initial
    rw [hA]
    exact separated_image_singleton A
  | succ t ih =>
    rcases hS.step t (by omega) with ⟨X, hX, Y, hY, hXY, h⟩ | ⟨A, -, hA, h⟩
    · rw [h]
      exact separated_coalescence (ih (by omega)) hX hY
    · rw [h]
      exact separated_sampling (ih (by omega)) hA

private theorem IsChain.exists_superset_succ (hS : IsChain S K) {t : ℕ} (ht : t < K)
    {B : Finset α} (hB : B ∈ S t) : ∃ Z ∈ S (t + 1), B ⊆ Z := by
  rcases hS.step t ht with ⟨X, hX, Y, hY, hXY, h⟩ | ⟨A, -, hA, h⟩
  · rw [h]
    by_cases hBX : B = X
    · refine ⟨X ∪ Y, Finset.mem_insert_self _ _, ?_⟩
      rw [hBX]
      exact Finset.subset_union_left
    by_cases hBY : B = Y
    · refine ⟨X ∪ Y, Finset.mem_insert_self _ _, ?_⟩
      rw [hBY]
      exact Finset.subset_union_right
    · exact ⟨B, mem_coalescence_iff.2 (Or.inr ⟨hBY, hBX, hB⟩), subset_rfl⟩
  · rw [h]
    exact ⟨B, Finset.mem_union_left _ hB, subset_rfl⟩

private theorem IsChain.exists_superset (hS : IsChain S K) {s k : ℕ} (hsk : s ≤ k) (hk : k ≤ K)
    {B : Finset α} (hB : B ∈ S s) : ∃ Z ∈ S k, B ⊆ Z := by
  induction k, hsk using Nat.le_induction with
  | base => exact ⟨B, hB, subset_rfl⟩
  | succ k _ ih =>
    obtain ⟨Z, hZ, hBZ⟩ := ih (by omega)
    obtain ⟨Z', hZ', hZZ'⟩ := hS.exists_superset_succ (by omega) hZ
    exact ⟨Z', hZ', hBZ.trans hZZ'⟩

private theorem IsChain.biUnion_mono (hS : IsChain S K) {s k : ℕ} (hsk : s ≤ k) (hk : k ≤ K) :
    (S s).biUnion id ⊆ (S k).biUnion id := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨Z, hZ, hBZ⟩ := hS.exists_superset hsk hk hB
  exact Finset.mem_biUnion.2 ⟨Z, hZ, hBZ hxB⟩

/-- A merged lineage `X ∪ Y` of step `k` is not a lineage of any earlier set. -/
private theorem IsChain.union_notMem_of_le (hS : IsChain S K) {s k : ℕ} (hsk : s ≤ k)
    (hk : k ≤ K) {X Y : Finset α} (hX : X ∈ S k) (hY : Y ∈ S k) (hXY : X ≠ Y) :
    X ∪ Y ∉ S s := by
  intro h
  have hsep := hS.separated hk
  obtain ⟨Z, hZ, hUZ⟩ := hS.exists_superset hsk hk h
  have hXZ : X = Z := hsep.eq_of_subset hX hZ (Finset.subset_union_left.trans hUZ)
  obtain ⟨y, hy⟩ := hsep.1 Y hY
  have hyX : y ∈ X := hXZ ▸ hUZ (Finset.mem_union_right X hy)
  exact Finset.disjoint_left.1 (hsep.2 X hX Y hY hXY) hyX hy

/-- A lineage that leaves the chain never returns. -/
private theorem IsChain.notMem_of_notMem_succ (hS : IsChain S K) {j k : ℕ} {B : Finset α}
    (hj : B ∈ S j) (hj' : B ∉ S (j + 1)) (hjk : j + 1 ≤ k) (hk : k ≤ K) : B ∉ S k := by
  intro hBk
  rcases hS.step j (by omega) with ⟨X, hX, Y, hY, hXY, h⟩ | ⟨A, -, -, h⟩
  · have hsep := hS.separated (t := j) (by omega)
    have hBXY : B = X ∨ B = Y := by
      by_contra hcon
      simp only [not_or] at hcon
      exact hj' (h ▸ mem_coalescence_iff.2 (Or.inr ⟨hcon.2, hcon.1, hj⟩))
    obtain ⟨Z, hZ, hUZ⟩ := hS.exists_superset (s := j + 1) hjk hk (B := X ∪ Y)
      (by rw [h]; exact Finset.mem_insert_self _ _)
    rcases hBXY with hBX | hBY
    · have hBZ : B = Z := (hS.separated hk).eq_of_subset hBk hZ
        (hBX ▸ Finset.subset_union_left.trans hUZ)
      obtain ⟨y, hy⟩ := hsep.1 Y hY
      have hyB : y ∈ B := hBZ ▸ hUZ (Finset.mem_union_right X hy)
      exact Finset.disjoint_left.1 (hsep.2 X hX Y hY hXY) (hBX ▸ hyB) hy
    · have hBZ : B = Z := (hS.separated hk).eq_of_subset hBk hZ
        (hBY ▸ Finset.subset_union_right.trans hUZ)
      obtain ⟨x, hx⟩ := hsep.1 X hX
      have hxB : x ∈ B := hBZ ▸ hUZ (Finset.mem_union_left Y hx)
      exact Finset.disjoint_left.1 (hsep.2 X hX Y hY hXY) hx (hBY ▸ hxB)
  · exact hj' (h ▸ Finset.mem_union_left _ hj)

/-- A lineage present at steps `s ≤ k` is present at every step in between. -/
private theorem IsChain.mem_of_mem_of_mem (hS : IsChain S K) {s r k : ℕ} {B : Finset α}
    (hsr : s ≤ r) (hrk : r ≤ k) (hk : k ≤ K) (hs : B ∈ S s) (hk' : B ∈ S k) : B ∈ S r := by
  induction r, hsr using Nat.le_induction with
  | base => exact hs
  | succ r _ ih =>
    by_contra hn
    exact hS.notMem_of_notMem_succ (ih (by omega)) hn hrk hk hk'

/-- The steps at which a lineage of `S k` is present, up to `k`, are those from its birth. -/
private theorem IsChain.exists_birth (hS : IsChain S K) {k : ℕ} (hk : k ≤ K) {B : Finset α}
    (hB : B ∈ S k) : ∃ β ≤ k, ∀ s ≤ k, (B ∈ S s ↔ β ≤ s) := by
  have hex : ∃ s, B ∈ S s := ⟨k, hB⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hB, fun s hs => ⟨fun h => Nat.find_min' hex h,
    fun h => ?_⟩⟩
  exact hS.mem_of_mem_of_mem h hs hk (Nat.find_spec hex) hB

/-- Two distinct lineages born at the same step are single leaves, sampled at that step, that
no earlier lineage contains. -/
private theorem IsChain.new_singletons (hS : IsChain S K) {b : ℕ} (hb : b < K) {B B' : Finset α}
    (hB : B ∈ S (b + 1)) (hB' : B' ∈ S (b + 1)) (hBn : B ∉ S b) (hB'n : B' ∉ S b)
    (hne : B ≠ B') : ∃ x x', B = {x} ∧ B' = {x'} ∧ x ∉ (S b).biUnion id ∧
      x' ∉ (S b).biUnion id := by
  rcases hS.step b hb with ⟨X, hX, Y, hY, hXY, h⟩ | ⟨A, -, hA, h⟩
  · have key : ∀ C ∈ S (b + 1), C ∉ S b → C = X ∪ Y := by
      intro C hC hCn
      rw [h] at hC
      rcases mem_coalescence_iff.1 hC with h1 | ⟨-, -, h1⟩
      · exact h1
      · exact absurd h1 hCn
    exact absurd ((key B hB hBn).trans (key B' hB' hB'n).symm) hne
  · have key : ∀ C ∈ S (b + 1), C ∉ S b → ∃ x, C = {x} ∧ x ∉ (S b).biUnion id := by
      intro C hC hCn
      rw [h] at hC
      rcases Finset.mem_union.1 hC with h1 | h1
      · exact absurd h1 hCn
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
        refine ⟨a, rfl, fun hmem => ?_⟩
        obtain ⟨D, hD, haD⟩ := Finset.mem_biUnion.1 hmem
        exact Finset.disjoint_left.1 (hA D hD) ha haD
    obtain ⟨x, rfl, hx⟩ := key B hB hBn
    obtain ⟨x', rfl, hx'⟩ := key B' hB' hB'n
    exact ⟨x, x', rfl, rfl, hx, hx'⟩

/-- Swapping two leaves that are both outside every lineage, or both single-leaf lineages,
fixes a separated lineage set. -/
private theorem relabelLineages_swap_eq {T : Finset (Finset α)} (hT : Separated T) {x x' : α}
    (h : (x ∉ T.biUnion id ∧ x' ∉ T.biUnion id) ∨ ({x} ∈ T ∧ {x'} ∈ T)) :
    relabelLineages (Equiv.swap x x') T = T := by
  apply relabelLineages_eq_self
  intro C hC
  rcases h with ⟨hx, hx'⟩ | ⟨hx, hx'⟩
  · rw [map_swap_eq_self (B := C) (fun h => hx (Finset.mem_biUnion.2 ⟨C, hC, h⟩))
      (fun h => hx' (Finset.mem_biUnion.2 ⟨C, hC, h⟩))]
    exact hC
  · by_cases hCx : C = {x}
    · subst hCx
      simpa using hx'
    by_cases hCx' : C = {x'}
    · subst hCx'
      simpa using hx
    have h1 : x ∉ C := fun h =>
      Finset.disjoint_left.1 (hT.2 _ hx C hC (Ne.symm hCx)) (Finset.mem_singleton_self x) h
    have h2 : x' ∉ C := fun h =>
      Finset.disjoint_left.1 (hT.2 _ hx' C hC (Ne.symm hCx')) (Finset.mem_singleton_self x') h
    rw [map_swap_eq_self h1 h2]
    exact hC

/-- Two distinct lineages of `S k` present at the same steps are single leaves whose swap
fixes `S 0, …, S k`. -/
private theorem IsChain.exists_swap (hS : IsChain S K) {k : ℕ} (hk : k ≤ K) {B B' : Finset α}
    (hB : B ∈ S k) (hB' : B' ∈ S k) (hne : B ≠ B') (hpres : ∀ s ≤ k, B ∈ S s ↔ B' ∈ S s) :
    ∃ x x', B = {x} ∧ B' = {x'} ∧ ∀ t ≤ k, relabelLineages (Equiv.swap x x') (S t) = S t := by
  obtain ⟨β, hβk, hβ⟩ := hS.exists_birth hk hB
  have hβ' : ∀ s ≤ k, B' ∈ S s ↔ β ≤ s := fun s hs => (hpres s hs).symm.trans (hβ s hs)
  have main : ∃ x x', B = {x} ∧ B' = {x'} ∧
      ∀ t < β, x ∉ (S t).biUnion id ∧ x' ∉ (S t).biUnion id := by
    rcases Nat.eq_zero_or_pos β with h0 | hpos
    · obtain ⟨A, hA⟩ := hS.initial
      have hB0 : B ∈ S 0 := (hβ 0 (Nat.zero_le _)).2 h0.le
      have hB'0 : B' ∈ S 0 := (hβ' 0 (Nat.zero_le _)).2 h0.le
      rw [hA] at hB0 hB'0
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hB0
      obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hB'0
      exact ⟨x, x', rfl, rfl, fun t ht => absurd ht (by omega)⟩
    · obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
      have h1 : B ∈ S (b + 1) := (hβ _ hβk).2 le_rfl
      have h2 : B' ∈ S (b + 1) := (hβ' _ hβk).2 le_rfl
      have h3 : B ∉ S b := fun h => by have := (hβ b (by omega)).1 h; omega
      have h4 : B' ∉ S b := fun h => by have := (hβ' b (by omega)).1 h; omega
      obtain ⟨x, x', rfl, rfl, hx, hx'⟩ := hS.new_singletons (by omega) h1 h2 h3 h4 hne
      exact ⟨x, x', rfl, rfl, fun t ht =>
        ⟨fun h => hx (hS.biUnion_mono (by omega) (by omega) h),
          fun h => hx' (hS.biUnion_mono (by omega) (by omega) h)⟩⟩
  obtain ⟨x, x', rfl, rfl, hout⟩ := main
  refine ⟨x, x', rfl, rfl, fun t ht => relabelLineages_swap_eq (hS.separated (by omega)) ?_⟩
  by_cases htβ : t < β
  · exact Or.inl (hout t htβ)
  · exact Or.inr ⟨(hβ t ht).2 (by omega), (hβ' t ht).2 (by omega)⟩

omit [DecidableEq α] in
/-- Any two equal-size sets of leaves are related by a permutation. -/
private theorem exists_perm_map_eq [Finite α] {A₁ A₂ : Finset α} (h : A₁.card = A₂.card) :
    ∃ σ : Equiv.Perm α, A₁.map σ.toEmbedding = A₂ := by
  classical
  let e : {x // x ∈ A₁} ≃ {x // x ∈ A₂} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, Finset.eq_of_subset_of_card_le (fun y hy => ?_)
    (by rw [Finset.card_map, h])⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  rw [Equiv.toEmbedding_apply, Equiv.extendSubtype_apply_of_mem e x hx]
  exact (e ⟨x, hx⟩).2

omit [DecidableEq α] in
/-- Two equal-size sets of leaves outside `C` are related by a permutation fixing `C`
pointwise. -/
private theorem exists_perm_fix_map_eq [Finite α] (C : Finset α) {D₁ D₂ : Finset α}
    (h₁ : Disjoint D₁ C) (h₂ : Disjoint D₂ C) (h : D₁.card = D₂.card) :
    ∃ ρ : Equiv.Perm α, (∀ x ∈ C, ρ x = x) ∧ D₁.map ρ.toEmbedding = D₂ := by
  classical
  have hc : (D₁.subtype (· ∉ C)).card = (D₂.subtype (· ∉ C)).card := by
    rw [Finset.card_subtype, Finset.card_subtype,
      Finset.filter_true_of_mem fun x hx => Finset.disjoint_left.1 h₁ hx,
      Finset.filter_true_of_mem fun x hx => Finset.disjoint_left.1 h₂ hx, h]
  obtain ⟨π, hπ⟩ := exists_perm_map_eq hc
  refine ⟨Equiv.Perm.ofSubtype π,
    fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem π (not_not.2 hx),
    Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map, h])⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  have hxC : x ∉ C := Finset.disjoint_left.1 h₁ hx
  rw [Equiv.toEmbedding_apply, Equiv.Perm.ofSubtype_apply_of_mem π hxC]
  have hmem : π ⟨x, hxC⟩ ∈ D₂.subtype (· ∉ C) :=
    hπ ▸ Finset.mem_map_of_mem _ (Finset.mem_subtype.2 hx)
  exact Finset.mem_subtype.1 hmem

private theorem card_inter_pair (T : Finset (Finset α)) {X Y : Finset α} (hXY : X ≠ Y) :
    (T ∩ {X, Y}).card = (if X ∈ T then 1 else 0) + (if Y ∈ T then 1 else 0) := by
  rw [Finset.inter_comm]
  by_cases hX : X ∈ T <;> by_cases hY : Y ∈ T
  · rw [Finset.insert_inter_of_mem hX, Finset.singleton_inter_of_mem hY,
      Finset.card_pair hXY]
    simp [hX, hY]
  · rw [Finset.insert_inter_of_mem hX, Finset.singleton_inter_of_notMem hY]
    simp [hX, hY]
  · rw [Finset.insert_inter_of_notMem hX, Finset.singleton_inter_of_mem hY]
    simp [hX, hY]
  · rw [Finset.insert_inter_of_notMem hX, Finset.singleton_inter_of_notMem hY]
    simp [hX, hY]

/-- Across a coalescence of `X` and `Y`, a lineage set `T` that lacks `X ∪ Y` loses exactly
its lineages among `X, Y`. -/
private theorem card_inter_coalescence {T U : Finset (Finset α)} {X Y : Finset α}
    (hX : X ∈ U) (hY : Y ∈ U) (hU : X ∪ Y ∉ T) :
    (T ∩ U).card = (T ∩ insert (X ∪ Y) ((U.erase X).erase Y)).card + (T ∩ {X, Y}).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext B
    simp only [Finset.mem_inter, Finset.mem_union, mem_coalescence_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hBT, hBU⟩
      by_cases hBX : B = X
      · exact Or.inr ⟨hBT, Or.inl hBX⟩
      by_cases hBY : B = Y
      · exact Or.inr ⟨hBT, Or.inr hBY⟩
      exact Or.inl ⟨hBT, Or.inr ⟨hBY, hBX, hBU⟩⟩
    · rintro (⟨hBT, rfl | ⟨-, -, hBU⟩⟩ | ⟨hBT, rfl | rfl⟩)
      · exact absurd hBT hU
      · exact ⟨hBT, hBU⟩
      · exact ⟨hBT, hX⟩
      · exact ⟨hBT, hY⟩
  · rw [Finset.disjoint_left]
    intro B hB hB'
    simp only [Finset.mem_inter, mem_coalescence_iff] at hB hB'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB'
    rcases hB with ⟨hBT, rfl | ⟨hBY, hBX, -⟩⟩
    · exact hU hBT
    · rcases hB'.2 with h | h
      · exact hBX h
      · exact hBY h

/-- The births of two pairs of lineages that are present at the same number of steps agree up
to order. -/
private theorem pair_match {b₁ b₂ c₁ c₂ k : ℕ}
    (h : ∀ s ≤ k, (if b₁ ≤ s then 1 else 0) + (if b₂ ≤ s then 1 else 0) =
      (if c₁ ≤ s then 1 else 0) + (if c₂ ≤ s then (1 : ℕ) else 0))
    (hb₁ : b₁ ≤ k) (hb₂ : b₂ ≤ k) (hc₁ : c₁ ≤ k) (hc₂ : c₂ ≤ k) :
    (b₁ = c₁ ∧ b₂ = c₂) ∨ (b₁ = c₂ ∧ b₂ = c₁) := by
  have hmin : min b₁ b₂ = min c₁ c₂ := by
    rcases lt_trichotomy (min b₁ b₂) (min c₁ c₂) with hlt | heq | hgt
    · have := h (min b₁ b₂) (by omega)
      split_ifs at this <;> omega
    · exact heq
    · have := h (min c₁ c₂) (by omega)
      split_ifs at this <;> omega
  have hmax : max b₁ b₂ = max c₁ c₂ := by
    rcases lt_trichotomy (max b₁ b₂) (max c₁ c₂) with hlt | heq | hgt
    · have := h (max b₁ b₂) (by omega)
      split_ifs at this <;> omega
    · exact heq
    · have := h (max c₁ c₂) (by omega)
      split_ifs at this <;> omega
  omega

variable {S : ℕ → Finset (Finset α)} {K : ℕ}

/-- Two pairs of lineages of `S k`, matched by the steps at which they are present, are related
by a permutation that fixes `S 0, …, S k`. -/
private theorem IsChain.exists_aut_pair (hS : IsChain S K) {k : ℕ} (hk : k ≤ K)
    {X' Y' X₂ Y₂ : Finset α} (hX' : X' ∈ S k) (hY' : Y' ∈ S k) (hXY' : X' ≠ Y')
    (hX₂ : X₂ ∈ S k) (hY₂ : Y₂ ∈ S k) (hXY₂ : X₂ ≠ Y₂)
    (hpX : ∀ s ≤ k, X' ∈ S s ↔ X₂ ∈ S s) (hpY : ∀ s ≤ k, Y' ∈ S s ↔ Y₂ ∈ S s) :
    ∃ τ : Equiv.Perm α, (∀ t ≤ k, relabelLineages τ (S t) = S t) ∧
      X'.map τ.toEmbedding = X₂ ∧ Y'.map τ.toEmbedding = Y₂ := by
  obtain ⟨τ₁, haut₁, hτ₁⟩ : ∃ τ₁ : Equiv.Perm α, (∀ t ≤ k, relabelLineages τ₁ (S t) = S t) ∧
      X'.map τ₁.toEmbedding = X₂ := by
    by_cases h : X' = X₂
    · refine ⟨1, fun t _ => relabelLineages_one _, ?_⟩
      rw [h]
      exact map_eq_self_of_forall fun _ _ => rfl
    · obtain ⟨x, x₂, rfl, rfl, haut⟩ := hS.exists_swap hk hX' hX₂ h hpX
      exact ⟨Equiv.swap x x₂, haut, by simp⟩
  have hmem : ∀ s ≤ k, ∀ B, B.map τ₁.toEmbedding ∈ S s ↔ B ∈ S s := fun s hs B => by
    conv_lhs => rw [← haut₁ s hs]
    exact map_mem_relabelLineages_iff _ _ _
  set Y'' := Y'.map τ₁.toEmbedding with hY''def
  have hY'' : Y'' ∈ S k := (hmem k le_rfl Y').2 hY'
  have hpY'' : ∀ s ≤ k, Y'' ∈ S s ↔ Y₂ ∈ S s := fun s hs => (hmem s hs Y').trans (hpY s hs)
  have hne'' : Y'' ≠ X₂ := by
    rw [← hτ₁]
    exact fun h => hXY' (Finset.map_injective _ h).symm
  obtain ⟨τ₂, haut₂, hτ₂Y, hτ₂X⟩ : ∃ τ₂ : Equiv.Perm α,
      (∀ t ≤ k, relabelLineages τ₂ (S t) = S t) ∧ Y''.map τ₂.toEmbedding = Y₂ ∧
        X₂.map τ₂.toEmbedding = X₂ := by
    by_cases h : Y'' = Y₂
    · refine ⟨1, fun t _ => relabelLineages_one _, ?_, map_eq_self_of_forall fun _ _ => rfl⟩
      rw [h]
      exact map_eq_self_of_forall fun _ _ => rfl
    · obtain ⟨y, y₂, hy, hy₂, haut⟩ := hS.exists_swap hk hY'' hY₂ h hpY''
      have hsep := hS.separated hk
      have h1 : y ∉ X₂ := fun hyX => Finset.disjoint_left.1 (hsep.2 _ hY'' _ hX₂ hne'')
        (by rw [hy]; exact Finset.mem_singleton_self y) hyX
      have h2 : y₂ ∉ X₂ := fun hyX => Finset.disjoint_left.1
        (hsep.2 _ hY₂ _ hX₂ (Ne.symm hXY₂)) (by rw [hy₂]; exact Finset.mem_singleton_self y₂) hyX
      exact ⟨Equiv.swap y y₂, haut, by rw [hy, hy₂]; simp, map_swap_eq_self h1 h2⟩
  refine ⟨τ₂ * τ₁, fun t ht => by rw [relabelLineages_mul, haut₁ t ht, haut₂ t ht], ?_, ?_⟩
  · rw [map_mul_toEmbedding, hτ₁, hτ₂X]
  · rw [map_mul_toEmbedding, ← hY''def, hτ₂Y]

/-- **Core of the unique encoding.** Two chains whose lineage sets meet in the same numbers of
lineages, pairwise, are related by a relabelling of the leaves. -/
private theorem IsChain.exists_relabel [Finite α] {S₁ S₂ : ℕ → Finset (Finset α)}
    (h₁ : IsChain S₁ K) (h₂ : IsChain S₂ K)
    (hF : ∀ a ≤ K, ∀ b ≤ K, (S₁ a ∩ S₁ b).card = (S₂ a ∩ S₂ b).card) :
    ∃ σ : Equiv.Perm α, ∀ t ≤ K, relabelLineages σ (S₁ t) = S₂ t := by
  suffices H : ∀ k ≤ K, ∃ σ : Equiv.Perm α, ∀ t ≤ k, relabelLineages σ (S₁ t) = S₂ t from
    H K le_rfl
  intro k hk
  induction k with
  | zero =>
    obtain ⟨A₁, hA₁⟩ := h₁.initial
    obtain ⟨A₂, hA₂⟩ := h₂.initial
    have hc : A₁.card = A₂.card := by
      have := hF 0 (Nat.zero_le _) 0 (Nat.zero_le _)
      rwa [Finset.inter_self, Finset.inter_self, hA₁, hA₂,
        Finset.card_image_of_injective _ Finset.singleton_injective,
        Finset.card_image_of_injective _ Finset.singleton_injective] at this
    obtain ⟨σ, hσ⟩ := exists_perm_map_eq hc
    refine ⟨σ, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    rw [hA₁, hA₂, relabelLineages_image_singleton, hσ]
  | succ k ih =>
    obtain ⟨σ, hσ⟩ := ih (by omega)
    have hkK : k < K := by omega
    have hs₁ := h₁.separated hkK.le
    have hs₂ := h₂.separated hkK.le
    have hck : (S₁ k).card = (S₂ k).card := by simpa using hF k hkK.le k hkK.le
    have hck' : (S₁ (k + 1)).card = (S₂ (k + 1)).card := by simpa using hF (k + 1) hk (k + 1) hk
    have hmemσ : ∀ s ≤ k, ∀ B, B.map σ.toEmbedding ∈ S₂ s ↔ B ∈ S₁ s := fun s hs B => by
      rw [← hσ s hs]
      exact map_mem_relabelLineages_iff _ _ _
    rcases h₁.step k hkK with ⟨X₁, hX₁, Y₁, hY₁, hXY₁, e₁⟩ | ⟨A₁, hA₁ne, hA₁, e₁⟩ <;>
      rcases h₂.step k hkK with ⟨X₂, hX₂, Y₂, hY₂, hXY₂, e₂⟩ | ⟨A₂, hA₂ne, hA₂, e₂⟩
    · -- two coalescences
      set X' := X₁.map σ.toEmbedding with hX'def
      set Y' := Y₁.map σ.toEmbedding with hY'def
      have hX' : X' ∈ S₂ k := (hmemσ k le_rfl X₁).2 hX₁
      have hY' : Y' ∈ S₂ k := (hmemσ k le_rfl Y₁).2 hY₁
      have hXY' : X' ≠ Y' := fun h => hXY₁ (Finset.map_injective _ h)
      have hpair : ∀ s ≤ k, (S₂ s ∩ {X', Y'}).card = (S₂ s ∩ {X₂, Y₂}).card := by
        intro s hs
        have a1 := card_inter_coalescence (T := S₁ s) hX₁ hY₁
          (h₁.union_notMem_of_le hs hkK.le hX₁ hY₁ hXY₁)
        have a2 := card_inter_coalescence (T := S₂ s) hX₂ hY₂
          (h₂.union_notMem_of_le hs hkK.le hX₂ hY₂ hXY₂)
        rw [← e₁] at a1
        rw [← e₂] at a2
        have f1 := hF s (by omega) k hkK.le
        have f2 := hF s (by omega) (k + 1) hk
        have r : (S₂ s ∩ {X', Y'}).card = (S₁ s ∩ {X₁, Y₁}).card := by
          rw [← hσ s hs, show ({X', Y'} : Finset (Finset α)) = relabelLineages σ {X₁, Y₁} by
            simp [relabelLineages, X', Y'], ← relabelLineages_inter, card_relabelLineages]
        omega
      obtain ⟨βX', hβX'k, hβX'⟩ := h₂.exists_birth hkK.le hX'
      obtain ⟨βY', hβY'k, hβY'⟩ := h₂.exists_birth hkK.le hY'
      obtain ⟨βX₂, hβX₂k, hβX₂⟩ := h₂.exists_birth hkK.le hX₂
      obtain ⟨βY₂, hβY₂k, hβY₂⟩ := h₂.exists_birth hkK.le hY₂
      have hm := pair_match (k := k) (b₁ := βX') (b₂ := βY') (c₁ := βX₂) (c₂ := βY₂)
        (fun s hs => by
          have := hpair s hs
          rw [card_inter_pair _ hXY', card_inter_pair _ hXY₂] at this
          simpa only [hβX' s hs, hβY' s hs, hβX₂ s hs, hβY₂ s hs] using this)
        hβX'k hβY'k hβX₂k hβY₂k
      have finish : ∀ {P Q : Finset α}, P ∈ S₂ k → Q ∈ S₂ k → P ≠ Q →
          S₂ (k + 1) = insert (P ∪ Q) (((S₂ k).erase P).erase Q) →
          (∀ s ≤ k, X' ∈ S₂ s ↔ P ∈ S₂ s) → (∀ s ≤ k, Y' ∈ S₂ s ↔ Q ∈ S₂ s) →
          ∃ σ' : Equiv.Perm α, ∀ t ≤ k + 1, relabelLineages σ' (S₁ t) = S₂ t := by
        intro P Q hP hQ hPQ eP hpP hpQ
        obtain ⟨τ, haut, hτX, hτY⟩ := h₂.exists_aut_pair hkK.le hX' hY' hXY' hP hQ hPQ hpP hpQ
        refine ⟨τ * σ, fun t ht => ?_⟩
        rcases Nat.lt_or_ge t (k + 1) with htk | htk
        · rw [relabelLineages_mul, hσ t (by omega), haut t (by omega)]
        · obtain rfl : t = k + 1 := by omega
          rw [e₁, eP, relabelLineages_coalescence, relabelLineages_mul, hσ k le_rfl,
            haut k le_rfl, map_mul_toEmbedding, map_mul_toEmbedding, ← hX'def, ← hY'def,
            hτX, hτY]
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact finish hX₂ hY₂ hXY₂ e₂
          (fun s hs => by rw [hβX' s hs, hβX₂ s hs, e1])
          (fun s hs => by rw [hβY' s hs, hβY₂ s hs, e2])
      · refine finish hY₂ hX₂ (Ne.symm hXY₂) ?_
          (fun s hs => by rw [hβX' s hs, hβY₂ s hs, e1])
          (fun s hs => by rw [hβY' s hs, hβX₂ s hs, e2])
        rw [e₂, Finset.union_comm, Finset.erase_right_comm]
    · -- a coalescence against a sampling event
      have c₁ := card_coalescence hs₁ hX₁ hY₁ hXY₁
      have c₂ := card_sampling (T := S₂ k) hA₂
      rw [← e₁] at c₁
      rw [← e₂] at c₂
      have := hA₂ne.card_pos
      omega
    · -- a sampling event against a coalescence
      have c₁ := card_sampling (T := S₁ k) hA₁
      have c₂ := card_coalescence hs₂ hX₂ hY₂ hXY₂
      rw [← e₁] at c₁
      rw [← e₂] at c₂
      have := hA₁ne.card_pos
      omega
    · -- two sampling events
      have c₁ := card_sampling (T := S₁ k) hA₁
      have c₂ := card_sampling (T := S₂ k) hA₂
      rw [← e₁] at c₁
      rw [← e₂] at c₂
      have hcA : A₁.card = A₂.card := by omega
      have hd₁ : Disjoint (A₁.map σ.toEmbedding) ((S₂ k).biUnion id) := by
        rw [Finset.disjoint_left]
        intro y hy hyC
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨B₂, hB₂, haB₂⟩ := Finset.mem_biUnion.1 hyC
        rw [← hσ k le_rfl] at hB₂
        obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.1 hB₂
        exact Finset.disjoint_left.1 (hA₁ B₁ hB₁) ha ((Finset.mem_map' _).1 haB₂)
      have hd₂ : Disjoint A₂ ((S₂ k).biUnion id) := by
        rw [Finset.disjoint_left]
        intro y hy hyC
        obtain ⟨B₂, hB₂, hyB₂⟩ := Finset.mem_biUnion.1 hyC
        exact Finset.disjoint_left.1 (hA₂ B₂ hB₂) hy hyB₂
      obtain ⟨ρ, hρC, hρ⟩ := exists_perm_fix_map_eq _ hd₁ hd₂ (by rw [Finset.card_map, hcA])
      have fixρ : ∀ t ≤ k, relabelLineages ρ (S₂ t) = S₂ t := by
        intro t ht
        refine relabelLineages_eq_self fun B hB => ?_
        rw [map_eq_self_of_forall (B := B) fun y hy => hρC y
          (h₂.biUnion_mono ht hkK.le (Finset.mem_biUnion.2 ⟨B, hB, hy⟩))]
        exact hB
      refine ⟨ρ * σ, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (k + 1) with htk | htk
      · rw [relabelLineages_mul, hσ t (by omega), fixρ t (by omega)]
      · obtain rfl : t = k + 1 := by omega
        rw [e₁, e₂, relabelLineages_mul, relabelLineages_union, relabelLineages_union,
          hσ k le_rfl, fixρ k le_rfl, relabelLineages_image_singleton,
          relabelLineages_image_singleton, hρ]

private theorem coalescence_step {T T' : Finset (Finset α)} (hT : Separated T)
    (h : IsCoalescence T T') : T'.biUnion id = T.biUnion id ∧ T'.card + 1 = T.card := by
  obtain ⟨X, hX, Y, hY, hXY, rfl⟩ := h
  refine ⟨?_, card_coalescence hT hX hY hXY⟩
  ext x
  simp only [Finset.mem_biUnion, id, mem_coalescence_iff]
  constructor
  · rintro ⟨B, rfl | ⟨-, -, hB⟩, hxB⟩
    · rcases Finset.mem_union.1 hxB with hx | hx
      exacts [⟨X, hX, hx⟩, ⟨Y, hY, hx⟩]
    · exact ⟨B, hB, hxB⟩
  · rintro ⟨B, hB, hxB⟩
    by_cases hBX : B = X
    · exact ⟨X ∪ Y, Or.inl rfl, Finset.mem_union_left _ (hBX ▸ hxB)⟩
    by_cases hBY : B = Y
    · exact ⟨X ∪ Y, Or.inl rfl, Finset.mem_union_right _ (hBY ▸ hxB)⟩
    exact ⟨B, Or.inr ⟨hBY, hBX, hB⟩, hxB⟩

private theorem sampling_step {T T' : Finset (Finset α)} (h : IsSampling T T') :
    (T.biUnion id).card < (T'.biUnion id).card ∧
      (T'.biUnion id).card + T.card = (T.biUnion id).card + T'.card := by
  obtain ⟨A, hAne, hA, rfl⟩ := h
  have hsupp : (T ∪ A.image ({·})).biUnion id = T.biUnion id ∪ A := by
    rw [Finset.union_biUnion]
    congr 1
    ext x
    simp
  have hdisj : Disjoint (T.biUnion id) A := by
    rw [Finset.disjoint_left]
    intro x hx hxA
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.1 hx
    exact Finset.disjoint_left.1 (hA B hB) hxA hxB
  have hc := card_sampling hA
  have hcs : ((T ∪ A.image ({·})).biUnion id).card = (T.biUnion id).card + A.card := by
    rw [hsupp, Finset.card_union_of_disjoint hdisj]
  have := hAne.card_pos
  exact ⟨by omega, by omega⟩

/-- In a chain, the number of leaves is at most the number of lineages plus the number of
steps, with equality only if every step so far was a coalescence. -/
private theorem IsChain.leaves_le (hS : IsChain S K) {t : ℕ} (ht : t ≤ K) :
    ((S t).biUnion id).card ≤ (S t).card + t ∧
      (((S t).biUnion id).card = (S t).card + t →
        ∀ u < t, IsCoalescence (S u) (S (u + 1))) := by
  induction t with
  | zero =>
    obtain ⟨A, hA⟩ := hS.initial
    have : ((S 0).biUnion id).card = (S 0).card := by
      rw [hA, Finset.card_image_of_injective _ Finset.singleton_injective]
      congr 1
      ext x
      simp
    exact ⟨this.le, fun _ u hu => absurd hu (Nat.not_lt_zero u)⟩
  | succ t ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rcases hS.step t (by omega) with hcoal | hsamp
    · obtain ⟨hs, hc⟩ := coalescence_step (hS.separated (t := t) (by omega)) hcoal
      refine ⟨by rw [hs]; omega, fun heq u hu => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact ih₂ (by rw [hs] at heq; omega) u hu
      · exact hcoal
    · obtain ⟨hs, hc⟩ := sampling_step hsamp
      exact ⟨by omega, fun heq => by omega⟩

end Chains


/-! ### The F matrix of a sequence of lineage sets -/

section FMatrix

variable {α : Type*} [DecidableEq α]

/-- The **F matrix** of size `r` of a list `L` of lineage sets, listed from the most recent
interval (`L[0]`) towards the root: on and below the diagonal (`j ≤ i`), the number of
lineages common to `L[r - 1 - i]` and `L[r - 1 - j]`; zero above it. Rows and columns are
indexed from the root, from `0`: index `i` is the source's interval `i + 1`. -/
def lineageFMatrix (L : List (Finset (Finset α))) (r : ℕ) : Matrix (Fin r) (Fin r) ℕ :=
  Matrix.of fun i j => if j ≤ i then (L.getD (r - 1 - i) ∅ ∩ L.getD (r - 1 - j) ∅).card else 0

theorem lineageFMatrix_apply (L : List (Finset (Finset α))) (r : ℕ) (i j : Fin r) :
    lineageFMatrix L r i j =
      if j ≤ i then (L.getD (r - 1 - i) ∅ ∩ L.getD (r - 1 - j) ∅).card else 0 :=
  rfl

theorem relabelLineages_empty (σ : Equiv.Perm α) : relabelLineages σ ∅ = ∅ :=
  Finset.image_empty _

theorem getD_map_relabelLineages (σ : Equiv.Perm α) (L : List (Finset (Finset α))) (t : ℕ) :
    (L.map (relabelLineages σ)).getD t ∅ = relabelLineages σ (L.getD t ∅) := by
  rw [← List.getD_map L ∅ (relabelLineages σ), relabelLineages_empty]

/- Relabelling the leaves does not change the F matrix. -/
theorem lineageFMatrix_map_relabelLineages (σ : Equiv.Perm α) (L : List (Finset (Finset α)))
    (r : ℕ) : lineageFMatrix (L.map (relabelLineages σ)) r = lineageFMatrix L r := by
  ext i j
  simp only [lineageFMatrix_apply, getD_map_relabelLineages, ← relabelLineages_inter,
    card_relabelLineages]

private theorem card_inter_eq_of_lineageFMatrix_eq {L₁ L₂ : List (Finset (Finset α))} {r : ℕ}
    (h : lineageFMatrix L₁ r = lineageFMatrix L₂ r) {a b : ℕ} (ha : a < r) (hb : b < r) :
    (L₁.getD a ∅ ∩ L₁.getD b ∅).card = (L₂.getD a ∅ ∩ L₂.getD b ∅).card := by
  wlog hab : a ≤ b generalizing a b
  · rw [Finset.inter_comm, this hb ha (by omega), Finset.inter_comm]
  have := congrFun (congrFun h ⟨r - 1 - a, by omega⟩) ⟨r - 1 - b, by omega⟩
  have hle : r - 1 - b ≤ r - 1 - a := by omega
  simp only [lineageFMatrix_apply, Fin.mk_le_mk, hle, ↓reduceIte] at this
  rw [show r - 1 - (r - 1 - a) = a by omega,
    show r - 1 - (r - 1 - b) = b by omega] at this
  exact this

end FMatrix

/-! ### Labeled ranked histories and ranked tree shapes -/

/-- A **labeled ranked history** with `n` leaves `0, …, n - 1` and `m` sampling events: a rooted
binary genealogy of labeled leaves, sampled at `m` distinct times, with its `n + m - 1` change
points (`n - 1` coalescences and `m` sampling events, one event at each change point) totally
ordered in time but without branch lengths.

It is recorded by its lineages: `lineages[t]` is the set of lineages extant in the interval just
rootward of the change point `t`, each lineage given by the set of sampled leaves descending from
it. Change point `0` is the most recent sampling event, which samples a nonempty set of leaves as
single-leaf lineages; going rootward, each change point either merges two lineages (a
coalescence) or adds a nonempty set of not yet sampled leaves as single-leaf lineages (a sampling
event); the last change point `n + m - 2` is the root, above which one lineage holds all the
leaves. As the type fixes `n + m - 1` change points and the root holds all `n` leaves, `n - 1`
of them are coalescences and `m` are sampling events
(`LabeledRankedHistory.card_coalescences_and_samplings`). -/
@[ext]
structure LabeledRankedHistory (n m : ℕ) where
  /-- `lineages[t]`: the lineages just rootward of the change point `t`, each given by its set
  of sampled descendant leaves. -/
  lineages : List (Finset (Finset (Fin n)))
  length_lineages : lineages.length = n + m - 1
  initial : ∃ A : Finset (Fin n), A.Nonempty ∧ lineages.getD 0 ∅ = A.image ({·})
  step : ∀ t, t + 1 < n + m - 1 →
    IsCoalescence (lineages.getD t ∅) (lineages.getD (t + 1) ∅) ∨
      IsSampling (lineages.getD t ∅) (lineages.getD (t + 1) ∅)
  root : lineages.getD (n + m - 2) ∅ = {univ}

namespace LabeledRankedHistory

variable {n m : ℕ}

private theorem isChain (H : LabeledRankedHistory n m) {K : ℕ} (hK : K ≤ n + m - 2) :
    IsChain (fun t => H.lineages.getD t ∅) K where
  initial := by
    obtain ⟨A, -, hA⟩ := H.initial
    exact ⟨A, hA⟩
  step t ht := H.step t (by omega)

/-- A lineage common to the lineage sets of two intervals is a lineage of every interval in
between. So the entries of the F matrix count the lineages of one interval that persist, without
bifurcating or ending at a sampling event, through every interval up to the other. -/
theorem mem_lineages_of_mem_of_mem (H : LabeledRankedHistory n m) {s r k : ℕ} (hsr : s ≤ r)
    (hrk : r ≤ k) (hk : k < n + m - 1) {B : Finset (Fin n)} (hs : B ∈ H.lineages.getD s ∅)
    (hk' : B ∈ H.lineages.getD k ∅) : B ∈ H.lineages.getD r ∅ :=
  (H.isChain le_rfl).mem_of_mem_of_mem hsr hrk (by omega) hs hk'

/-- Two labeled ranked histories have the **same shape** when a relabelling of the leaves
carries the lineages of one to those of the other. -/
def SameShape (H₁ H₂ : LabeledRankedHistory n m) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), H₁.lineages.map (relabelLineages σ) = H₂.lineages

theorem map_relabelLineages_one (L : List (Finset (Finset (Fin n)))) :
    L.map (relabelLineages 1) = L := by
  rw [show relabelLineages (1 : Equiv.Perm (Fin n)) = id from funext relabelLineages_one,
    List.map_id]

theorem map_relabelLineages_mul (σ τ : Equiv.Perm (Fin n)) (L : List (Finset (Finset (Fin n)))) :
    L.map (relabelLineages (σ * τ)) = (L.map (relabelLineages τ)).map (relabelLineages σ) := by
  rw [List.map_map]
  exact List.map_congr_left fun S _ => relabelLineages_mul σ τ S

/-- Having the same shape is an equivalence relation. -/
instance shapeSetoid (n m : ℕ) : Setoid (LabeledRankedHistory n m) where
  r := SameShape
  iseqv := {
    refl := fun H => ⟨1, map_relabelLineages_one _⟩
    symm := fun {_ _} h => by
      obtain ⟨σ, h⟩ := h
      exact ⟨σ⁻¹, by rw [← h, ← map_relabelLineages_mul, inv_mul_cancel,
        map_relabelLineages_one]⟩
    trans := fun {_ _ _} h h' => by
      obtain ⟨σ, h⟩ := h
      obtain ⟨τ, h'⟩ := h'
      exact ⟨τ * σ, by rw [map_relabelLineages_mul, h, h']⟩ }

/-- The F matrix of a labeled ranked history, of size `n + m - 2`: for `j ≤ i`, entry `(i, j)`
is the number of lineages extant in the interval `j` (counted from the root, from `0`) that
persist, without bifurcating or ending at a sampling event, through the interval `i`; entries
above the diagonal are zero. In the source's notation, indexed from `1`, this entry is
`F_{i+1, j+1}`. -/
def fMatrix (H : LabeledRankedHistory n m) : Matrix (Fin (n + m - 2)) (Fin (n + m - 2)) ℕ :=
  lineageFMatrix H.lineages (n + m - 2)

theorem fMatrix_apply (H : LabeledRankedHistory n m) (i j : Fin (n + m - 2)) :
    H.fMatrix i j = if j ≤ i then
      (H.lineages.getD (n + m - 3 - i) ∅ ∩ H.lineages.getD (n + m - 3 - j) ∅).card else 0 := by
  rw [fMatrix, lineageFMatrix_apply, show n + m - 2 - 1 = n + m - 3 by omega]

theorem fMatrix_eq_of_sameShape {H₁ H₂ : LabeledRankedHistory n m} (h : SameShape H₁ H₂) :
    H₁.fMatrix = H₂.fMatrix := by
  obtain ⟨σ, hσ⟩ := h
  rw [fMatrix, fMatrix, ← hσ, lineageFMatrix_map_relabelLineages]

/- Labeled ranked histories with the same F matrix have the same shape. -/
theorem sameShape_of_fMatrix_eq {H₁ H₂ : LabeledRankedHistory n m}
    (h : H₁.fMatrix = H₂.fMatrix) : SameShape H₁ H₂ := by
  have hroot₁ := H₁.root
  have hroot₂ := H₂.root
  have hF : ∀ a ≤ n + m - 3, ∀ b ≤ n + m - 3,
      (H₁.lineages.getD a ∅ ∩ H₁.lineages.getD b ∅).card =
        (H₂.lineages.getD a ∅ ∩ H₂.lineages.getD b ∅).card := by
    intro a ha b hb
    by_cases hr : n + m - 2 = 0
    · obtain rfl : a = 0 := by omega
      obtain rfl : b = 0 := by omega
      rw [hr] at hroot₁ hroot₂
      rw [hroot₁, hroot₂]
    · exact card_inter_eq_of_lineageFMatrix_eq h (by omega) (by omega)
  obtain ⟨σ, hσ⟩ := IsChain.exists_relabel (H₁.isChain (K := n + m - 3) (by omega))
    (H₂.isChain (K := n + m - 3) (by omega)) hF
  refine ⟨σ, List.ext_getElem (by simp [length_lineages]) fun t ht₁ ht₂ => ?_⟩
  simp only [List.length_map, length_lineages] at ht₁
  rw [List.getElem_map, ← List.getD_eq_getElem _ ∅ ht₂,
    ← List.getD_eq_getElem _ ∅ (by rw [length_lineages]; omega)]
  by_cases ht : t = n + m - 2
  · rw [ht, hroot₁, hroot₂, relabelLineages, Finset.image_singleton, Finset.map_univ_equiv]
  · exact hσ t (by omega)

end LabeledRankedHistory

/-- A **ranked tree shape** with `n` leaves and `m` sampling events: a labeled ranked history
with its leaf labels forgotten, that is, up to relabelling of the leaves. For `m = 1` (all
leaves sampled at the same time) these are the isochronous ranked tree shapes, rooted binary
unlabeled trees with their `n - 1` internal nodes totally ordered in time; for `m ≥ 2` they are
heterochronous. -/
def RankedTreeShape (n m : ℕ) : Type :=
  Quotient (LabeledRankedHistory.shapeSetoid n m)

namespace RankedTreeShape

variable {n m : ℕ}

/-- The **F matrix** of a ranked tree shape (Kim, Rosenberg and Palacios 2020): the
`(n + m - 2) × (n + m - 2)` lower-triangular matrix whose entry `(i, j)`, for `j ≤ i`, is the
number of lineages extant in the interval `j` (counted from the root, from `0`) that persist,
without bifurcating or ending at a sampling event, through the interval `i`
(`LabeledRankedHistory.fMatrix`). -/
def fMatrix : RankedTreeShape n m → Matrix (Fin (n + m - 2)) (Fin (n + m - 2)) ℕ :=
  Quotient.lift LabeledRankedHistory.fMatrix fun _ _ =>
    LabeledRankedHistory.fMatrix_eq_of_sameShape

/-- **Unique encoding of ranked tree shapes** (Kim, Rosenberg and Palacios 2020, Theorem 1): the
F matrix determines the ranked tree shape, isochronous or heterochronous. -/
theorem fMatrix_injective :
    Function.Injective (fMatrix : RankedTreeShape n m → Matrix _ _ ℕ) := by
  intro T₁ T₂ h
  induction T₁ using Quotient.inductionOn
  induction T₂ using Quotient.inductionOn
  exact Quotient.sound (LabeledRankedHistory.sameShape_of_fMatrix_eq h)

end RankedTreeShape

/-! ### Ranked labeled histories as isochronous labeled ranked histories -/

namespace RankedHistory

/-- A ranked labeled history of `n + 1` genes, as a labeled ranked history with one sampling
event: all genes are sampled at the present, and the lineages are the ancestral partitions. -/
def toLabeledRankedHistory {n : ℕ} (h : RankedHistory (n + 1)) :
    LabeledRankedHistory (n + 1) 1 where
  lineages := partitionsOf h
  length_lineages := length_partitionsOf h
  initial := ⟨univ, univ_nonempty, partitionsOf_getD_zero h⟩
  step _ ht := Or.inl (partitionsOf_getD_succ h (by omega))
  root := partitionsOf_getD_pred h (Nat.succ_ne_zero n)

/-- The ranked tree shape of a ranked labeled history: its isochronous ranked tree shape. -/
def rankedTreeShape {n : ℕ} (h : RankedHistory (n + 1)) : RankedTreeShape (n + 1) 1 :=
  ⟦h.toLabeledRankedHistory⟧

/-- Two ranked labeled histories have the same ranked tree shape exactly when a relabelling of
the genes carries the ancestral partitions of one to those of the other. -/
theorem rankedTreeShape_eq_iff {n : ℕ} (h₁ h₂ : RankedHistory (n + 1)) :
    h₁.rankedTreeShape = h₂.rankedTreeShape ↔
      ∃ σ : Equiv.Perm (Fin (n + 1)), (partitionsOf h₁).map (relabelLineages σ) = partitionsOf h₂ :=
  Quotient.eq

/-- The F matrix of a ranked labeled history of `n` genes, of size `n - 1`, from its ancestral
partitions: for `j ≤ i`, entry `(i, j)` is the number of blocks common to the partitions with
`j + 2` and `i + 2` blocks, that is, the number of the `j + 2` lineages of the interval `j`
(counted from the root, from `0`) that do not bifurcate through the interval `i`. -/
def fMatrix {n : ℕ} (h : RankedHistory n) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ :=
  lineageFMatrix (partitionsOf h) (n - 1)

theorem fMatrix_rankedTreeShape {n : ℕ} (h : RankedHistory (n + 1)) :
    h.rankedTreeShape.fMatrix = h.fMatrix :=
  rfl

/-- **Unique encoding for ranked labeled histories**: two ranked labeled histories have the
same F matrix exactly when a relabelling of the genes carries the ancestral partitions of one to
those of the other, that is, exactly when they have the same ranked tree shape. -/
theorem fMatrix_eq_fMatrix_iff {n : ℕ} (h₁ h₂ : RankedHistory n) :
    h₁.fMatrix = h₂.fMatrix ↔
      ∃ σ : Equiv.Perm (Fin n), (partitionsOf h₁).map (relabelLineages σ) = partitionsOf h₂ := by
  constructor
  · intro hF
    rcases n with _ | n
    · refine ⟨1, ?_⟩
      simp [partitionsOf, blocksOf]
    · exact (rankedTreeShape_eq_iff h₁ h₂).1 (RankedTreeShape.fMatrix_injective hF)
  · rintro ⟨σ, hσ⟩
    rw [fMatrix, fMatrix, ← hσ, lineageFMatrix_map_relabelLineages]

end RankedHistory

namespace LabeledRankedHistory

variable {n m : ℕ}

/-- In an isochronous labeled ranked history (one sampling event), every change point after the
first is a coalescence, so the interval just rootward of the change point `t` has `n - t`
lineages. -/
theorem card_lineages_of_isochronous (H : LabeledRankedHistory n 1) {t : ℕ} (ht : t < n) :
    (H.lineages.getD t ∅).card = n - t := by
  have hroot : H.lineages.getD (n - 1) ∅ = {univ} := by
    rw [← H.root]
    congr 1
  have hS := H.isChain (K := n - 1) (by omega)
  have hend : ((H.lineages.getD (n - 1) ∅).biUnion id).card = n := by
    rw [hroot, Finset.singleton_biUnion, id, Finset.card_univ, Fintype.card_fin]
  have hcard : (H.lineages.getD (n - 1) ∅).card = 1 := by
    rw [hroot, Finset.card_singleton]
  have hcoal := (hS.leaves_le (t := n - 1) le_rfl).2 (by omega)
  have key : ∀ u ≤ n - 1, ((H.lineages.getD u ∅).biUnion id).card =
      ((H.lineages.getD 0 ∅).biUnion id).card ∧
      (H.lineages.getD u ∅).card + u = (H.lineages.getD 0 ∅).card := by
    intro u hu
    induction u with
    | zero => exact ⟨rfl, rfl⟩
    | succ u ih =>
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      obtain ⟨hs, hc⟩ := coalescence_step (hS.separated (t := u) (by omega)) (hcoal u (by omega))
      exact ⟨by rw [hs, ih₁], by omega⟩
  obtain ⟨k₁, k₂⟩ := key (n - 1) le_rfl
  have h0 := (hS.leaves_le (t := 0) (Nat.zero_le _)).1
  obtain ⟨-, k₄⟩ := key t (by omega)
  have : ((H.lineages.getD 0 ∅).biUnion id).card ≤ n := by
    simpa using Finset.card_le_univ ((H.lineages.getD 0 ∅).biUnion id)
  omega

private theorem not_isCoalescence_of_isSampling {α : Type*} [DecidableEq α]
    {T T' : Finset (Finset α)} (hT : Separated T) (h : IsSampling T T') :
    ¬ IsCoalescence T T' := by
  rintro hc
  have h1 := (coalescence_step hT hc).2
  obtain ⟨A, hAne, hA, rfl⟩ := h
  have h2 := card_sampling hA
  have := hAne.card_pos
  omega

private theorem natCard_subtype_fin {K : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    Nat.card {t : Fin K // P t} = ((range K).filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun t => if P t then 1 else 0)]

/-- Of the change points after the most recent sampling event (`1, …, n + m - 2`), `n - 1` are
coalescences and `m - 1` are sampling events; with the most recent sampling event, a labeled
ranked history has `n - 1` coalescences and `m` sampling events. -/
theorem card_coalescences_and_samplings (H : LabeledRankedHistory n m) :
    Nat.card {t : Fin (n + m - 2) //
        IsCoalescence (H.lineages.getD t ∅) (H.lineages.getD (t + 1) ∅)} = n - 1 ∧
      Nat.card {t : Fin (n + m - 2) //
        IsSampling (H.lineages.getD t ∅) (H.lineages.getD (t + 1) ∅)} = m - 1 := by
  classical
  have hS := H.isChain (K := n + m - 2) le_rfl
  let C : ℕ → ℕ := fun t => ((range t).filter fun u =>
    IsCoalescence (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅)).card
  have inv : ∀ t ≤ n + m - 2,
      ((H.lineages.getD t ∅).biUnion id).card = (H.lineages.getD t ∅).card + C t := by
    intro t ht
    induction t with
    | zero =>
      obtain ⟨A, -, hA⟩ := H.initial
      simp only [C, Finset.range_zero, Finset.filter_empty, Finset.card_empty, add_zero]
      rw [hA, Finset.card_image_of_injective _ Finset.singleton_injective]
      congr 1
      ext x
      simp
    | succ t ih =>
      have ih := ih (by omega)
      have hsep : Separated (H.lineages.getD t ∅) := hS.separated (t := t) (by omega)
      rcases H.step t (by omega) with hcoal | hsamp
      · have hC : C (t + 1) = C t + 1 := by
          simp only [C, Finset.range_add_one, Finset.filter_insert, hcoal, ↓reduceIte]
          rw [Finset.card_insert_of_notMem (by simp)]
        obtain ⟨hs, hc⟩ := coalescence_step hsep hcoal
        rw [hC, hs]
        omega
      · have hC : C (t + 1) = C t := by
          simp only [C, Finset.range_add_one, Finset.filter_insert,
            not_isCoalescence_of_isSampling hsep hsamp, ↓reduceIte]
        obtain ⟨-, hc⟩ := sampling_step hsamp
        rw [hC]
        omega
  have hend := inv (n + m - 2) le_rfl
  rw [H.root, Finset.singleton_biUnion, id, Finset.card_univ, Fintype.card_fin,
    Finset.card_singleton] at hend
  have hcoal : ((range (n + m - 2)).filter fun u =>
      IsCoalescence (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅)).card = n - 1 := by
    change n = 1 + C (n + m - 2) at hend
    change C (n + m - 2) = n - 1
    omega
  have hsamp : ((range (n + m - 2)).filter fun u =>
      IsSampling (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅)) =
      (range (n + m - 2)).filter fun u =>
        ¬ IsCoalescence (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅) := by
    refine Finset.filter_congr fun u hu => ?_
    have hu : u < n + m - 2 := Finset.mem_range.1 hu
    constructor
    · exact not_isCoalescence_of_isSampling (hS.separated (t := u) (by omega))
    · intro hnc
      exact (H.step u (by omega)).resolve_left hnc
  refine ⟨(natCard_subtype_fin fun u =>
    IsCoalescence (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅)).trans hcoal,
    (natCard_subtype_fin fun u =>
      IsSampling (H.lineages.getD u ∅) (H.lineages.getD (u + 1) ∅)).trans ?_⟩
  rw [hsamp, Finset.filter_not, Finset.card_sdiff_of_subset
    (Finset.filter_subset _ _), Finset.card_range, hcoal]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨A, hA, -⟩ := H.initial
    exact absurd hA (by simp [Finset.eq_empty_of_isEmpty A])
  · omega

end LabeledRankedHistory

namespace RankedTreeShape

variable {n : ℕ}

/-- For isochronous ranked tree shapes the diagonal of the F matrix is fixed: the interval `i`
(counted from the root, from `0`) has `i + 2` lineages, that is, `F_{i,i} = i + 1` in the
source's indexing from `1`. -/
theorem fMatrix_diag_of_isochronous (T : RankedTreeShape n 1) (i : Fin (n + 1 - 2)) :
    T.fMatrix i i = (i : ℕ) + 2 := by
  induction T using Quotient.inductionOn with
  | h H =>
    change H.fMatrix i i = (i : ℕ) + 2
    simp only [LabeledRankedHistory.fMatrix_apply, le_refl, ↓reduceIte, Finset.inter_self]
    rw [LabeledRankedHistory.card_lineages_of_isochronous H (by omega)]
    omega

end RankedTreeShape

/-! ### Entrywise distances between lower-triangular matrices -/

section LowerDistance

variable {r : ℕ}

/-- The entries of `A` on and below the diagonal, as a function of the index pair (zero above
the diagonal). -/
private noncomputable def lowerPart (A : Matrix (Fin r) (Fin r) ℝ) (p : Fin r × Fin r) : ℝ :=
  if p.2 ≤ p.1 then A p.1 p.2 else 0

private theorem sum_lowerPart (A B : Matrix (Fin r) (Fin r) ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ p : Fin r × Fin r, f (lowerPart A p - lowerPart B p) =
      ∑ i, ∑ j ∈ Iic i, f (A i j - B i j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (lowerPart A (i, j) - lowerPart B (i, j)) =
      if j ≤ i then f (A i j - B i j) else 0 := by
    intro j
    simp only [lowerPart]
    split_ifs <;> simp [hf]
  simp only [h]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

private theorem lowerPart_eq_iff {A B : Matrix (Fin r) (Fin r) ℝ} :
    lowerPart A = lowerPart B ↔ ∀ i j, j ≤ i → A i j = B i j := by
  constructor
  · intro h i j hji
    simpa [lowerPart, hji] using congrFun h (i, j)
  · intro h
    funext p
    simp only [lowerPart]
    split_ifs with hp
    exacts [h _ _ hp, rfl]

private theorem lowerL1_eq_dist (A B : Matrix (Fin r) (Fin r) ℝ) :
    ∑ i, ∑ j ∈ Iic i, |A i j - B i j| =
      dist (WithLp.toLp 1 (lowerPart A) : PiLp 1 fun _ : Fin r × Fin r => ℝ)
        (WithLp.toLp 1 (lowerPart B)) := by
  rw [PiLp.dist_eq_of_L1]
  simp only [Real.dist_eq]
  exact (sum_lowerPart A B (|·|) abs_zero).symm

private theorem lowerL2_eq_dist (A B : Matrix (Fin r) (Fin r) ℝ) :
    √(∑ i, ∑ j ∈ Iic i, (A i j - B i j) ^ 2) =
      dist (WithLp.toLp 2 (lowerPart A) : EuclideanSpace ℝ (Fin r × Fin r))
        (WithLp.toLp 2 (lowerPart B)) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Real.dist_eq, sq_abs]
  rw [sum_lowerPart A B (· ^ 2) (by simp)]

/-- A function given by the distance between images in a metric space is a pseudometric, and it
vanishes only where the images agree. -/
private theorem metric_of_eq_dist {X M : Type*} [MetricSpace M] (v : X → M) (d : X → X → ℝ)
    (hd : ∀ x y, d x y = dist (v x) (v y)) :
    (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
      ∀ x y, d x y = 0 → v x = v y :=
  ⟨fun x => by rw [hd, dist_self], fun x y => by rw [hd, hd, dist_comm],
    fun x y z => by rw [hd, hd, hd]; exact dist_triangle _ _ _,
    fun x y h => dist_eq_zero.1 (by rw [← hd]; exact h)⟩

end LowerDistance

/-! ### Metrics on ranked tree shapes -/

namespace RankedTreeShape

variable {n m : ℕ}

theorem fMatrix_eq_zero_of_lt (T : RankedTreeShape n m) {i j : Fin (n + m - 2)} (hij : i < j) :
    T.fMatrix i j = 0 := by
  induction T using Quotient.inductionOn with
  | h H =>
    change H.fMatrix i j = 0
    simp only [LabeledRankedHistory.fMatrix_apply, not_le.2 hij, ↓reduceIte]

/- Two ranked tree shapes whose F matrices agree on and below the diagonal are equal. -/
theorem eq_of_fMatrix_lower_eq {T₁ T₂ : RankedTreeShape n m}
    (h : ∀ i j, j ≤ i → T₁.fMatrix i j = T₂.fMatrix i j) : T₁ = T₂ := by
  refine fMatrix_injective (Matrix.ext fun i j => ?_)
  rcases le_or_gt j i with hji | hij
  · exact h i j hji
  · rw [fMatrix_eq_zero_of_lt T₁ hij, fMatrix_eq_zero_of_lt T₂ hij]

/-- The `L¹` distance `d₁` between ranked tree shapes (Kim, Rosenberg and Palacios 2020, Eq. 1):
the sum, over the entries on and below the diagonal, of the absolute differences of their F
matrices. -/
noncomputable def d₁ (T₁ T₂ : RankedTreeShape n m) : ℝ :=
  ∑ i, ∑ j ∈ Iic i, |(T₁.fMatrix i j : ℝ) - T₂.fMatrix i j|

/-- The `L²` distance `d₂` between ranked tree shapes (Kim, Rosenberg and Palacios 2020, Eq. 2):
the square root of the sum, over the entries on and below the diagonal, of the squared
differences of their F matrices. -/
noncomputable def d₂ (T₁ T₂ : RankedTreeShape n m) : ℝ :=
  √(∑ i, ∑ j ∈ Iic i, ((T₁.fMatrix i j : ℝ) - T₂.fMatrix i j) ^ 2)

private theorem cast_lower_eq {T₁ T₂ : RankedTreeShape n m}
    (h : lowerPart (T₁.fMatrix.map ((↑) : ℕ → ℝ)) = lowerPart (T₂.fMatrix.map ((↑) : ℕ → ℝ))) :
    T₁ = T₂ :=
  eq_of_fMatrix_lower_eq fun i j hji => by
    have := lowerPart_eq_iff.1 h i j hji
    simp only [Matrix.map_apply, Nat.cast_inj] at this
    exact this

/-- `d₁` is a metric on ranked tree shapes with `n` leaves and `m` sampling events. -/
theorem d₁_isMetric :
    (∀ T : RankedTreeShape n m, d₁ T T = 0) ∧ (∀ T₁ T₂ : RankedTreeShape n m, d₁ T₁ T₂ = d₁ T₂ T₁) ∧
      (∀ T₁ T₂ T₃ : RankedTreeShape n m, d₁ T₁ T₃ ≤ d₁ T₁ T₂ + d₁ T₂ T₃) ∧
      ∀ T₁ T₂ : RankedTreeShape n m, d₁ T₁ T₂ = 0 → T₁ = T₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := metric_of_eq_dist
    (fun T : RankedTreeShape n m =>
      (WithLp.toLp 1 (lowerPart (T.fMatrix.map ((↑) : ℕ → ℝ))) :
        PiLp 1 fun _ : Fin (n + m - 2) × Fin (n + m - 2) => ℝ))
    d₁ fun T₁ T₂ => lowerL1_eq_dist _ _
  exact ⟨h1, h2, h3, fun T₁ T₂ h => cast_lower_eq (WithLp.toLp_injective 1 (h4 T₁ T₂ h))⟩

/-- `d₂` is a metric on ranked tree shapes with `n` leaves and `m` sampling events. -/
theorem d₂_isMetric :
    (∀ T : RankedTreeShape n m, d₂ T T = 0) ∧ (∀ T₁ T₂ : RankedTreeShape n m, d₂ T₁ T₂ = d₂ T₂ T₁) ∧
      (∀ T₁ T₂ T₃ : RankedTreeShape n m, d₂ T₁ T₃ ≤ d₂ T₁ T₂ + d₂ T₂ T₃) ∧
      ∀ T₁ T₂ : RankedTreeShape n m, d₂ T₁ T₂ = 0 → T₁ = T₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := metric_of_eq_dist
    (fun T : RankedTreeShape n m =>
      (WithLp.toLp 2 (lowerPart (T.fMatrix.map ((↑) : ℕ → ℝ))) :
        EuclideanSpace ℝ (Fin (n + m - 2) × Fin (n + m - 2))))
    d₂ fun T₁ T₂ => lowerL2_eq_dist _ _
  exact ⟨h1, h2, h3, fun T₁ T₂ h => cast_lower_eq (WithLp.toLp_injective 2 (h4 T₁ T₂ h))⟩

end RankedTreeShape

namespace LabeledRankedHistory

variable {n m : ℕ}

/- Every interval between the most recent sampling event and the root has a lineage. -/
theorem lineages_nonempty (H : LabeledRankedHistory n m) {t : ℕ} (ht : t ≤ n + m - 2) :
    (H.lineages.getD t ∅).Nonempty := by
  induction t with
  | zero =>
    obtain ⟨A, hA, h⟩ := H.initial
    rw [h]
    exact hA.image _
  | succ t ih =>
    rcases H.step t (by omega) with ⟨X, -, Y, -, -, h⟩ | ⟨A, hA, -, h⟩
    · rw [h]
      exact Finset.insert_nonempty _ _
    · rw [h]
      exact (ih (by omega)).mono Finset.subset_union_left

end LabeledRankedHistory

namespace RankedTreeShape

variable {n m : ℕ}

/- The diagonal entries of the F matrix, the numbers of lineages of the intervals, are
positive. -/
theorem fMatrix_diag_pos (T : RankedTreeShape n m) (i : Fin (n + m - 2)) : 0 < T.fMatrix i i := by
  induction T using Quotient.inductionOn with
  | h H =>
    change 0 < H.fMatrix i i
    simp only [LabeledRankedHistory.fMatrix_apply, le_refl, ↓reduceIte, Finset.inter_self]
    exact (H.lineages_nonempty (by omega)).card_pos

end RankedTreeShape

/-! ### Ranked genealogies and weighted distances -/

/-- A **ranked genealogy** with `n` leaves and `m` sampling events: a ranked tree shape together
with the times of its change points, measured into the past from the most recent sampling event.
`time t` is the time of the change point `t` (`t = 0` the most recent sampling event, at time
`0`, and `t = n + m - 2` the root); the times increase strictly towards the root. -/
@[ext]
structure RankedGenealogy (n m : ℕ) where
  /-- The ranked tree shape. -/
  shape : RankedTreeShape n m
  /-- `time t`: the time of the change point `t`, into the past. -/
  time : Fin (n + m - 1) → ℝ
  strictMono_time : StrictMono time
  time_zero : ∀ h : 0 < n + m - 1, time ⟨0, h⟩ = 0

namespace RankedGenealogy

variable {n m : ℕ}

/-- The weight matrix `W` of a ranked genealogy (Kim, Rosenberg and Palacios 2020): for `j ≤ i`,
entry `(i, j)` is the length of the time span from the bottom of the interval `i` to the top of
the interval `j` (intervals counted from the root, from `0`); entries above the diagonal are
zero. In the source's notation, indexed from `1` with change-point times `u_1 > ⋯ > u_{n+m-1}`,
this entry is `W_{i+1,j+1} = u_{j+1} - u_{i+2}`. -/
noncomputable def weightMatrix (g : RankedGenealogy n m) :
    Matrix (Fin (n + m - 2)) (Fin (n + m - 2)) ℝ :=
  Matrix.of fun i j => if j ≤ i then
    g.time ⟨n + m - 2 - j, by have := j.2; omega⟩ - g.time ⟨n + m - 3 - i, by have := i.2; omega⟩
  else 0

theorem weightMatrix_pos (g : RankedGenealogy n m) {i j : Fin (n + m - 2)} (hji : j ≤ i) :
    0 < g.weightMatrix i j := by
  simp only [weightMatrix, Matrix.of_apply, hji, ↓reduceIte, sub_pos]
  apply g.strictMono_time
  rw [Fin.mk_lt_mk]
  have := i.2
  have : (j : ℕ) ≤ i := hji
  omega

private theorem weightMatrix_diag (g : RankedGenealogy n m) {k : ℕ} (hk : k + 1 < n + m - 1) :
    g.weightMatrix ⟨n + m - 3 - k, by omega⟩ ⟨n + m - 3 - k, by omega⟩ =
      g.time ⟨k + 1, hk⟩ - g.time ⟨k, by omega⟩ := by
  simp only [weightMatrix, Matrix.of_apply, le_refl, ↓reduceIte]
  congr 2 <;> rw [Fin.mk.injEq] <;> omega

/-- The weighted `L¹` distance `d₁ʷ` between ranked genealogies (Kim, Rosenberg and Palacios
2020, Eq. 3): `d₁` with each entry `F_{i,j}` of the F matrices replaced by `F_{i,j} W_{i,j}`. -/
noncomputable def dw₁ (g₁ g₂ : RankedGenealogy n m) : ℝ :=
  ∑ i, ∑ j ∈ Iic i, |(g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j -
    g₂.shape.fMatrix i j * g₂.weightMatrix i j|

/-- The weighted `L²` distance `d₂ʷ` between ranked genealogies (Kim, Rosenberg and Palacios
2020, Eq. 4): `d₂` with each entry `F_{i,j}` of the F matrices replaced by `F_{i,j} W_{i,j}`. -/
noncomputable def dw₂ (g₁ g₂ : RankedGenealogy n m) : ℝ :=
  √(∑ i, ∑ j ∈ Iic i, ((g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j -
    g₂.shape.fMatrix i j * g₂.weightMatrix i j) ^ 2)

/-- The entrywise product `F ∘ W` of a ranked genealogy. -/
private noncomputable def weightedF (g : RankedGenealogy n m) :
    Matrix (Fin (n + m - 2)) (Fin (n + m - 2)) ℝ :=
  Matrix.of fun i j => (g.shape.fMatrix i j : ℝ) * g.weightMatrix i j

/-- If the diagonals of the F matrices agree, as they do for isochronous genealogies, the
weighted F matrices determine the ranked genealogy: the diagonal gives the lengths of the
intervals, hence the times and the weights, and dividing by the positive weights gives the F
matrix. -/
theorem eq_of_weighted_eq {g₁ g₂ : RankedGenealogy n m}
    (h : ∀ i j, j ≤ i → (g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j =
      g₂.shape.fMatrix i j * g₂.weightMatrix i j)
    (hdiag : ∀ i, g₁.shape.fMatrix i i = g₂.shape.fMatrix i i) : g₁ = g₂ := by
  have hlen : ∀ i, g₁.weightMatrix i i = g₂.weightMatrix i i := by
    intro i
    have h1 := h i i le_rfl
    rw [hdiag i] at h1
    have hpos : (0 : ℝ) < g₂.shape.fMatrix i i := Nat.cast_pos.2 (g₂.shape.fMatrix_diag_pos i)
    exact mul_left_cancel₀ hpos.ne' h1
  have htime : ∀ k (hk : k < n + m - 1), g₁.time ⟨k, hk⟩ = g₂.time ⟨k, hk⟩ := by
    intro k hk
    induction k with
    | zero => rw [g₁.time_zero, g₂.time_zero]
    | succ k ih =>
      have e₁ := g₁.weightMatrix_diag hk
      have e₂ := g₂.weightMatrix_diag hk
      have e₃ := hlen ⟨n + m - 3 - k, by omega⟩
      have e₄ := ih (by omega)
      linarith
  have htime' : g₁.time = g₂.time := funext fun t => htime t.1 t.2
  have hW : g₁.weightMatrix = g₂.weightMatrix := by
    ext i j
    simp only [weightMatrix, Matrix.of_apply, htime']
  have hshape : g₁.shape = g₂.shape := by
    refine RankedTreeShape.eq_of_fMatrix_lower_eq fun i j hji => ?_
    have h1 := h i j hji
    rw [hW] at h1
    exact_mod_cast mul_right_cancel₀ (g₂.weightMatrix_pos hji).ne' h1
  exact RankedGenealogy.ext hshape htime'

private theorem dw_lower_eq {g₁ g₂ : RankedGenealogy n m}
    (h : lowerPart g₁.weightedF = lowerPart g₂.weightedF) :
    ∀ i j, j ≤ i → (g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j =
      g₂.shape.fMatrix i j * g₂.weightMatrix i j :=
  lowerPart_eq_iff.1 h

/-- `d₁ʷ` is a pseudometric on ranked genealogies: it vanishes on the diagonal, is symmetric
and satisfies the triangle inequality. Two genealogies at distance zero have the same weighted F
matrix on and below the diagonal. -/
theorem dw₁_pseudometric :
    (∀ g : RankedGenealogy n m, dw₁ g g = 0) ∧
      (∀ g₁ g₂ : RankedGenealogy n m, dw₁ g₁ g₂ = dw₁ g₂ g₁) ∧
      (∀ g₁ g₂ g₃ : RankedGenealogy n m, dw₁ g₁ g₃ ≤ dw₁ g₁ g₂ + dw₁ g₂ g₃) ∧
      ∀ g₁ g₂ : RankedGenealogy n m, dw₁ g₁ g₂ = 0 → ∀ i j, j ≤ i →
        (g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j =
          g₂.shape.fMatrix i j * g₂.weightMatrix i j := by
  obtain ⟨h1, h2, h3, h4⟩ := metric_of_eq_dist
    (fun g : RankedGenealogy n m =>
      (WithLp.toLp 1 (lowerPart g.weightedF) :
        PiLp 1 fun _ : Fin (n + m - 2) × Fin (n + m - 2) => ℝ))
    dw₁ fun g₁ g₂ => lowerL1_eq_dist _ _
  exact ⟨h1, h2, h3, fun g₁ g₂ h => dw_lower_eq (WithLp.toLp_injective 1 (h4 g₁ g₂ h))⟩

/-- `d₂ʷ` is a pseudometric on ranked genealogies: it vanishes on the diagonal, is symmetric
and satisfies the triangle inequality. Two genealogies at distance zero have the same weighted F
matrix on and below the diagonal. -/
theorem dw₂_pseudometric :
    (∀ g : RankedGenealogy n m, dw₂ g g = 0) ∧
      (∀ g₁ g₂ : RankedGenealogy n m, dw₂ g₁ g₂ = dw₂ g₂ g₁) ∧
      (∀ g₁ g₂ g₃ : RankedGenealogy n m, dw₂ g₁ g₃ ≤ dw₂ g₁ g₂ + dw₂ g₂ g₃) ∧
      ∀ g₁ g₂ : RankedGenealogy n m, dw₂ g₁ g₂ = 0 → ∀ i j, j ≤ i →
        (g₁.shape.fMatrix i j : ℝ) * g₁.weightMatrix i j =
          g₂.shape.fMatrix i j * g₂.weightMatrix i j := by
  obtain ⟨h1, h2, h3, h4⟩ := metric_of_eq_dist
    (fun g : RankedGenealogy n m =>
      (WithLp.toLp 2 (lowerPart g.weightedF) :
        EuclideanSpace ℝ (Fin (n + m - 2) × Fin (n + m - 2))))
    dw₂ fun g₁ g₂ => lowerL2_eq_dist _ _
  exact ⟨h1, h2, h3, fun g₁ g₂ h => dw_lower_eq (WithLp.toLp_injective 2 (h4 g₁ g₂ h))⟩

/-- **The weighted distances are metrics on isochronous ranked genealogies** (Kim, Rosenberg and
Palacios 2020, Proposition 2, for one sampling event): `d₁ʷ` separates ranked genealogies with
`n` leaves sampled at the same time. -/
theorem eq_of_dw₁_eq_zero_of_isochronous {g₁ g₂ : RankedGenealogy n 1} (h : dw₁ g₁ g₂ = 0) :
    g₁ = g₂ :=
  eq_of_weighted_eq (dw₁_pseudometric.2.2.2 g₁ g₂ h) fun i => by
    rw [RankedTreeShape.fMatrix_diag_of_isochronous, RankedTreeShape.fMatrix_diag_of_isochronous]

/-- **The weighted distances are metrics on isochronous ranked genealogies** (Kim, Rosenberg and
Palacios 2020, Proposition 2, for one sampling event): `d₂ʷ` separates ranked genealogies with
`n` leaves sampled at the same time. -/
theorem eq_of_dw₂_eq_zero_of_isochronous {g₁ g₂ : RankedGenealogy n 1} (h : dw₂ g₁ g₂ = 0) :
    g₁ = g₂ :=
  eq_of_weighted_eq (dw₂_pseudometric.2.2.2 g₁ g₂ h) fun i => by
    rw [RankedTreeShape.fMatrix_diag_of_isochronous, RankedTreeShape.fMatrix_diag_of_isochronous]

end RankedGenealogy

/-! ### Summary statistics -/

section Medoid

variable {X : Type*}

/-- The **`L²`-medoid set** of a finite sample `T 0, …, T (s - 1)`, possibly with repetitions,
for a distance `d` (Kim, Rosenberg and Palacios 2020, Eqs. 5 and 7): the sampled points that
minimise the sum of squared distances to the sample, used as a measure of center. -/
def l2MedoidSet (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) : Set X :=
  {x | (∃ k, T k = x) ∧ ∀ k, ∑ j, d x (T j) ^ 2 ≤ ∑ j, d (T k) (T j) ^ 2}

/-- The mean squared distance from a point `x` to a finite sample, used with an `L²`-medoid `x`
as a measure of dispersion (Kim, Rosenberg and Palacios 2020, Eq. 6). -/
noncomputable def meanSquaredDistance (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) (x : X) : ℝ :=
  (∑ j, d x (T j) ^ 2) / s

/-- A nonempty finite sample has an `L²`-medoid. -/
theorem l2MedoidSet_nonempty (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) (hs : 0 < s) :
    (l2MedoidSet d T).Nonempty := by
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image univ (fun k => ∑ j, d (T k) (T j) ^ 2)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hs⟩⟩)
  exact ⟨T k, ⟨k, rfl⟩, fun k' => hk k' (Finset.mem_univ _)⟩

/- An `L²`-medoid has the least mean squared distance to the sample among the sampled points. -/
theorem meanSquaredDistance_le_of_mem_l2MedoidSet (d : X → X → ℝ) {s : ℕ} (T : Fin s → X)
    {x : X} (hx : x ∈ l2MedoidSet d T) (k : Fin s) :
    meanSquaredDistance d T x ≤ meanSquaredDistance d T (T k) :=
  div_le_div_of_nonneg_right (hx.2 k) (Nat.cast_nonneg s)

end Medoid

end MathlibExt.Biology.PopulationGenetics.Coalescent
