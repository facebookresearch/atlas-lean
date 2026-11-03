/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neighbor joining: Q-criterion and the local star BME length

Neighbor joining (NJ, `NeighborJoining.NJRun`) keeps a set `S` of clusters with a dissimilarity
`D` between them, and joins a pair of distinct clusters minimizing the Q-criterion
`Q(a, b) = (|S| - 2) D a b - ∑_{c ∈ S} D a c - ∑_{c ∈ S} D b c`.

Gascuel and Steel (2006) showed that the selection step is greedy for the balanced
minimum-evolution (BME) length, extended to trees with vertices of any degree. This file
proves only the *local* form of that statement. The extension uses the coefficients of
Semple and Steel (2004), Theorem 4.2: a pair of leaves `i, j` gets coefficient
`∏_v (deg v - 1)⁻¹` over the interior vertices `v` of the path from `i` to `j`, and the
length of the tree for a dissimilarity `D` is `∑_{i<j} coeff(i, j) D(i, j)`.
View the current clusters as the `m = |S|` leaves of a star (one interior vertex of degree `m`).
Joining `a` and `b` gives the tree `T_ab` in which `a` and `b` hang from a new vertex `u` of
degree three, joined to the center, which keeps degree `m - 1`. Its coefficients are `1/2` for
the pair `a, b`; `1/(2(m - 2))` for `a` or `b` with another cluster; and `1/(m - 2)` for two
other clusters (`cherryCoeff`, `cherryLength`).

* `cherryLength_eq`: `L(T_ab) = (∑_{c ≠ c'} D c c' + Q(a, b)) / (2 (m - 2))` for a symmetric `D`
  that vanishes on the diagonal of `S`, with `m ≥ 3`. The first term does not depend on the pair.
* `qCriterion_le_iff_cherryLength_le`, `NJRun.isMin_qCriterion_iff_cherryLength`: so a pair
  minimizes `Q` exactly when joining it gives the smallest `cherryLength`, the BME length of
  `T_ab` on the current clusters for the current cluster dissimilarity `D`. This is a local
  star identity, not the full Gascuel–Steel comparison of partially resolved trees on all taxa.
  At the first step (clusters = taxa, `D = d` on singletons) the two coincide: `cherryLength`
  is then the BME length of the join tree on the taxa for the original dissimilarity.
* `cherryLength_eq_length`: the coefficients are the right ones: if `D` is the path-length
  dissimilarity of `T_ab` with real edge lengths, `cherryLength` is the total edge length.

## Scope

The run-level statement here is relative to the current cluster dissimilarity `D` and the
star on the current clusters. Gascuel and Steel also compare the BME lengths of the partially
resolved trees on all taxa, computed from the original dissimilarity; that comparison is not
formalized here, and no statement in this file should be read as claiming it. In particular
`NJRun.isMin_qCriterion_iff_cherryLength` uses the run hypothesis only to obtain symmetry of
`D` and a zero diagonal; it does not define the run's partial topology on the taxa.

## References

* O. Gascuel and M. Steel, *Neighbor-joining revealed*, Mol. Biol. Evol. 23 (2006), 1997–2000.
* C. Semple and M. Steel, *Cyclic permutations and evolutionary trees*, Adv. in Appl. Math. 32
  (2004), 669–680.
* R. Desper and O. Gascuel, *Fast and accurate phylogeny reconstruction algorithms based on the
  minimum-evolution principle*, J. Comput. Biol. 9 (2002), 687–705.
* N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing
  phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
* J. A. Studier and K. J. Keppler, *A note on the neighbor-joining algorithm of Saitou and
  Nei*, Mol. Biol. Evol. 5 (1988), 729–731.
-/
@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoiningBME

open Finset Cslib.Bioinformatics.Phylogenetics.NeighborJoining

variable {X : Type*} [DecidableEq X]

/-- The generalized Pauplin coefficient of the pair of clusters `u, v` in the tree `T_ab`
obtained from the star on `S` by joining `a` and `b`: `1/2` for `{a, b}`; `1/(2(|S| - 2))` when
one of `u, v` is `a` or `b` and the other is not; `1/(|S| - 2)` when neither is. Values on the
diagonal `u = v` are never used. -/
noncomputable def cherryCoeff (S : Finset (Finset X)) (a b u v : Finset X) : ℝ :=
  if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then 1 / 2
  else if u = a ∨ u = b ∨ v = a ∨ v = b then 1 / (2 * ((S.card : ℝ) - 2))
  else 1 / ((S.card : ℝ) - 2)

/-- The balanced minimum-evolution length of `T_ab` for the dissimilarity `D`:
half the sum over ordered pairs of distinct clusters of `cherryCoeff S a b u v * D u v`, which
is `∑_{u<v} cherryCoeff S a b u v * D u v` when `D` is symmetric. -/
noncomputable def cherryLength (S : Finset (Finset X)) (D : Finset X → Finset X → ℝ)
    (a b : Finset X) : ℝ :=
  (∑ p ∈ S.offDiag, cherryCoeff S a b p.1 p.2 * D p.1 p.2) / 2


omit [DecidableEq X] in
/-- A sum over ordered pairs of distinct elements of `S` is the full double sum when the summand
vanishes on the diagonal. -/
private theorem sum_offDiag_eq {α : Type*} {S : Finset α} (f : α → α → ℝ)
    (hf : ∀ u ∈ S, f u u = 0) :
    ∑ p ∈ S.offDiag, f p.1 p.2 = ∑ u ∈ S, ∑ v ∈ S, f u v := by
  classical
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  rw [Finset.sum_eq_zero (s := S.diag), zero_add]
  intro p hp
  rw [Finset.mem_diag] at hp
  obtain ⟨hp, he⟩ := hp
  rw [← he]
  exact hf _ hp

omit [DecidableEq X] in
/-- Split a sum over `S` at two distinct members `a, b`. -/
private theorem sum_split {α : Type*} [DecidableEq α] {S : Finset α} {a b : α} (ha : a ∈ S)
    (hb : b ∈ S) (hab : a ≠ b) (g : α → ℝ) :
    ∑ u ∈ S, g u = g a + g b + ∑ u ∈ (S.erase a).erase b, g u := by
  rw [← Finset.add_sum_erase S g ha, ← Finset.add_sum_erase (S.erase a) g
    (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]
  ring

/-- **The BME length of a join in terms of the Q-criterion.** For `D` symmetric and zero on the
diagonal of `S`, `|S| ≥ 3` and distinct `a, b ∈ S`:
`cherryLength S D a b = (∑_{u ≠ v ∈ S} D u v + Q(a, b)) / (2 (|S| - 2))`. -/
theorem cherryLength_eq (S : Finset (Finset X)) (D : Finset X → Finset X → ℝ)
    (hsymm : ∀ u ∈ S, ∀ v ∈ S, D u v = D v u) (hdiag : ∀ u ∈ S, D u u = 0)
    (hS : 3 ≤ S.card) {a b : Finset X} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    cherryLength S D a b =
      ((∑ p ∈ S.offDiag, D p.1 p.2) + qCriterion S D a b) / (2 * ((S.card : ℝ) - 2)) := by
  have hk : (0 : ℝ) < (S.card : ℝ) - 2 := by
    have : (3 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  set T := (S.erase a).erase b with hTdef
  have hT : ∀ v ∈ T, v ≠ a ∧ v ≠ b ∧ v ∈ S := by
    intro v hv
    simp only [hTdef, Finset.mem_erase] at hv
    exact ⟨hv.2.1, hv.1, hv.2.2⟩
  unfold cherryLength qCriterion
  rw [sum_offDiag_eq (fun u v => cherryCoeff S a b u v * D u v)
      (fun u hu => by simp [hdiag u hu]),
    sum_offDiag_eq D hdiag]
  simp only [sum_split ha hb hab, Finset.sum_add_distrib]
  have e1 : ∑ v ∈ T, cherryCoeff S a b a v * D a v =
      1 / (2 * ((S.card : ℝ) - 2)) * ∑ v ∈ T, D a v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, -⟩ := hT v hv
    simp [cherryCoeff, hab, hvb]
  have e2 : ∑ v ∈ T, cherryCoeff S a b b v * D b v =
      1 / (2 * ((S.card : ℝ) - 2)) * ∑ v ∈ T, D b v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, -⟩ := hT v hv
    simp [cherryCoeff, hab.symm, hva]
  have e3 : ∑ u ∈ T, cherryCoeff S a b u a * D u a =
      1 / (2 * ((S.card : ℝ) - 2)) * ∑ v ∈ T, D a v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    simp [cherryCoeff, hva, hvb, hsymm v hvS a ha]
  have e4 : ∑ u ∈ T, cherryCoeff S a b u b * D u b =
      1 / (2 * ((S.card : ℝ) - 2)) * ∑ v ∈ T, D b v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    simp [cherryCoeff, hva, hvb, hsymm v hvS b hb]
  have e5 : ∑ u ∈ T, ∑ v ∈ T, cherryCoeff S a b u v * D u v =
      1 / ((S.card : ℝ) - 2) * ∑ u ∈ T, ∑ v ∈ T, D u v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hua, hub, -⟩ := hT u hu
    obtain ⟨hva, hvb, -⟩ := hT v hv
    simp [cherryCoeff, hua, hub, hva, hvb]
  have e6 : ∑ u ∈ T, D u a = ∑ v ∈ T, D a v :=
    Finset.sum_congr rfl fun v hv => hsymm v (hT v hv).2.2 a ha
  have e7 : ∑ u ∈ T, D u b = ∑ v ∈ T, D b v :=
    Finset.sum_congr rfl fun v hv => hsymm v (hT v hv).2.2 b hb
  have cab : cherryCoeff S a b a b = 1 / 2 := by simp [cherryCoeff]
  have cba : cherryCoeff S a b b a = 1 / 2 := by simp [cherryCoeff]
  rw [← hTdef, e1, e2, e3, e4, e5, e6, e7, cab, cba, hdiag a ha, hdiag b hb, hsymm b hb a ha]
  field_simp
  ring

/-- **Minimizing `Q` is minimizing the local star BME length of the join**: the BME length
of `T_ab` on the current clusters for the current cluster dissimilarity `D`. This is the
local star identity; it is not the full Gascuel–Steel comparison on all taxa. -/
theorem qCriterion_le_iff_cherryLength_le (S : Finset (Finset X))
    (D : Finset X → Finset X → ℝ)
    (hsymm : ∀ u ∈ S, ∀ v ∈ S, D u v = D v u) (hdiag : ∀ u ∈ S, D u u = 0)
    (hS : 3 ≤ S.card) {a b a' b' : Finset X} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (ha' : a' ∈ S) (hb' : b' ∈ S) (hab' : a' ≠ b') :
    qCriterion S D a b ≤ qCriterion S D a' b' ↔ cherryLength S D a b ≤ cherryLength S D a' b' := by
  have hk : (0 : ℝ) < 2 * ((S.card : ℝ) - 2) := by
    have : (3 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  rw [cherryLength_eq S D hsymm hdiag hS ha hb hab, cherryLength_eq S D hsymm hdiag hS ha' hb' hab',
    div_le_div_iff_of_pos_right hk, add_le_add_iff_left]

/-- Along a run of neighbor joining on a symmetric `d` with zero diagonal, the cluster
dissimilarity stays symmetric and vanishes on every current cluster. -/
theorem NJRun.symm_diag [Fintype X] {d : X → X → ℝ} (hsymm : ∀ x y, d x y = d y x)
    (hdiag : ∀ x, d x x = 0) {S : Finset (Finset X)} {D : Finset X → Finset X → ℝ}
    {C : Finset (Finset X)} (hrun : NJRun d S D C) :
    (∀ u v, D u v = D v u) ∧ ∀ u ∈ S, D u u = 0 := by
  induction hrun with
  | init =>
    refine ⟨fun u v => ?_, fun u hu => ?_⟩
    · unfold initialDist
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => hsymm x y
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
      simp [initialDist, hdiag]
  | @join S D C a b _ _ _ _ _ _ ih =>
    obtain ⟨ihs, ihd⟩ := ih
    refine ⟨fun u v => ?_, fun u hu => ?_⟩
    · unfold joinDist
      by_cases hu : u = a ∪ b <;> by_cases hv : v = a ∪ b <;> simp [hu, hv, ihs]
    · unfold joinDist
      by_cases hu' : u = a ∪ b
      · simp [hu']
      · simp only [hu', ↓reduceIte]
        rcases Finset.mem_insert.mp hu with h | h
        · exact absurd h hu'
        · exact ihd u (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))

/-- **Q-minimality is cherry-length minimality at a run state.** At every state of a run on a
symmetric dissimilarity with zero diagonal and at least three clusters, a pair of distinct
clusters minimizes the Q-criterion (the pairs NJ may join) if and only if joining it gives
the smallest `cherryLength`, the BME length of the join tree `T_ab` on the current clusters
for the current cluster dissimilarity `D`. This is the local star identity only: it does not
compare partially resolved trees on all taxa under the original dissimilarity `d`. -/
theorem NJRun.isMin_qCriterion_iff_cherryLength [Fintype X] {d : X → X → ℝ} (hsymm : ∀ x y, d x y = d y x)
    (hdiag : ∀ x, d x x = 0) {S : Finset (Finset X)} {D : Finset X → Finset X → ℝ}
    {C : Finset (Finset X)} (hrun : NJRun d S D C) (hS : 3 ≤ S.card) {a b : Finset X}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    (∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → qCriterion S D a b ≤ qCriterion S D a' b') ↔
      ∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → cherryLength S D a b ≤ cherryLength S D a' b' := by
  obtain ⟨hs, hd⟩ := NJRun.symm_diag hsymm hdiag hrun
  exact forall₂_congr fun a' ha' => forall₂_congr fun b' hb' => forall_congr' fun hab' =>
    qCriterion_le_iff_cherryLength_le S D (fun u _ v _ => hs u v) hd hS ha hb hab ha' hb' hab'

/-- **The coefficients give the tree length.** Let `T_ab` carry real edge lengths: `ℓ c` on the
pendant edge of each cluster `c ∈ S` and `m` on the edge between `u` and the center. If `D` is
its path-length dissimilarity (`D a b = ℓ a + ℓ b`, `D x c = ℓ x + m + ℓ c` for `x ∈ {a, b}` and
`c` another cluster, `D c c' = ℓ c + ℓ c'` for two other distinct clusters), then
`cherryLength S D a b = ∑_{c ∈ S} ℓ c + m`. -/
theorem cherryLength_eq_length (S : Finset (Finset X)) (hS : 3 ≤ S.card) {a b : Finset X}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ℓ : Finset X → ℝ) (m : ℝ)
    (D : Finset X → Finset X → ℝ)
    (hD : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → D u v =
      if (u = a ∨ u = b) ∧ (v = a ∨ v = b) then ℓ u + ℓ v
      else if u = a ∨ u = b ∨ v = a ∨ v = b then ℓ u + m + ℓ v
      else ℓ u + ℓ v) :
    cherryLength S D a b = ∑ c ∈ S, ℓ c + m := by
  have hk : (0 : ℝ) < (S.card : ℝ) - 2 := by
    have : (3 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  set T := (S.erase a).erase b with hTdef
  have hT : ∀ v ∈ T, v ≠ a ∧ v ≠ b ∧ v ∈ S := by
    intro v hv
    simp only [hTdef, Finset.mem_erase] at hv
    exact ⟨hv.2.1, hv.1, hv.2.2⟩
  have hcard : (T.card : ℝ) = (S.card : ℝ) - 2 := by
    have h1 := Finset.card_erase_of_mem ha
    have h2 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
    rw [hTdef, h2, h1]
    have : 2 ≤ S.card := by omega
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    norm_num
  -- the summand, extended by `0` on the diagonal
  set g : Finset X → Finset X → ℝ :=
    fun u v => if u = v then 0 else cherryCoeff S a b u v * D u v with hg
  unfold cherryLength
  rw [Finset.sum_congr rfl (g := fun p => g p.1 p.2) (fun p hp => by
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hp
      simp [hg, hne]),
    sum_offDiag_eq g (fun u _ => by simp [hg])]
  simp only [sum_split ha hb hab, Finset.sum_add_distrib]
  have gab : g a b = 1 / 2 * (ℓ a + ℓ b) := by
    simp [hg, hab, cherryCoeff, hD a ha b hb hab]
  have gba : g b a = 1 / 2 * (ℓ b + ℓ a) := by
    simp [hg, Ne.symm hab, cherryCoeff, hD b hb a ha (Ne.symm hab)]
  have gaa : g a a = 0 := by simp [hg]
  have gbb : g b b = 0 := by simp [hg]
  have e1 : ∑ v ∈ T, g a v = 1 / (2 * ((S.card : ℝ) - 2)) *
      (T.card * (ℓ a + m) + ∑ v ∈ T, ℓ v) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    simp [hg, cherryCoeff, hab, hvb, Ne.symm hva, hD a ha v hvS (Ne.symm hva), hva]
  have e2 : ∑ v ∈ T, g b v = 1 / (2 * ((S.card : ℝ) - 2)) *
      (T.card * (ℓ b + m) + ∑ v ∈ T, ℓ v) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    simp [hg, cherryCoeff, Ne.symm hab, hva, Ne.symm hvb, hD b hb v hvS (Ne.symm hvb), hvb]
  have e3 : ∑ u ∈ T, g u a = 1 / (2 * ((S.card : ℝ) - 2)) *
      (T.card * (ℓ a + m) + ∑ v ∈ T, ℓ v) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    have hc : cherryCoeff S a b v a = 1 / (2 * ((S.card : ℝ) - 2)) := by
      simp [cherryCoeff, hva, hvb]
    have hd : D v a = ℓ v + m + ℓ a := by simp [hD v hvS a ha hva, hva, hvb]
    simp only [hg, hva, ↓reduceIte, hc, hd]
    ring
  have e4 : ∑ u ∈ T, g u b = 1 / (2 * ((S.card : ℝ) - 2)) *
      (T.card * (ℓ b + m) + ∑ v ∈ T, ℓ v) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hva, hvb, hvS⟩ := hT v hv
    have hc : cherryCoeff S a b v b = 1 / (2 * ((S.card : ℝ) - 2)) := by
      simp [cherryCoeff, hva, hvb]
    have hd : D v b = ℓ v + m + ℓ b := by simp [hD v hvS b hb hvb, hva, hvb]
    simp only [hg, hvb, ↓reduceIte, hc, hd]
    ring
  have e5 : ∑ u ∈ T, ∑ v ∈ T, g u v =
      1 / ((S.card : ℝ) - 2) * (2 * ((T.card : ℝ) - 1) * ∑ v ∈ T, ℓ v) := by
    have inner : ∀ u ∈ T, ∑ v ∈ T, g u v =
        1 / ((S.card : ℝ) - 2) * ((T.card : ℝ) * ℓ u + ∑ v ∈ T, ℓ v - 2 * ℓ u) := by
      intro u hu
      obtain ⟨hua, hub, huS⟩ := hT u hu
      have : ∀ v ∈ T, g u v = 1 / ((S.card : ℝ) - 2) * (ℓ u + ℓ v) -
          if u = v then 1 / ((S.card : ℝ) - 2) * (ℓ u + ℓ v) else 0 := by
        intro v hv
        obtain ⟨hva, hvb, hvS⟩ := hT v hv
        by_cases huv : u = v
        · simp [hg, huv]
        · simp [hg, huv, cherryCoeff, hua, hub, hva, hvb, hD u huS v hvS huv]
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp only [hu, ↓reduceIte]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl inner, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [← hTdef, gab, gba, gaa, gbb, e1, e2, e3, e4, e5, hcard]
  field_simp
  ring

end Cslib.Bioinformatics.Phylogenetics.NeighborJoiningBME
