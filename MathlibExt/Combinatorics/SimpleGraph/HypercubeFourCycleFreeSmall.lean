/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement is adapted from the known values in `SqueezeBench/Problems/HypercubeC4/README.md`
(leansolving/SqueezeBench, commit e2e19eef093a77882da57f348def029533ec2d5e).
Copyright the SqueezeBench contributors. Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The statement uses ATLAS's hypercube Turán number rather than SqueezeBench's spanning model.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact four-cycle-free hypercube Turán numbers in dimensions one through six

In dimensions two through four we count missing edges in coordinate squares. In dimensions five
and six, each triple of incident edge directions at an even vertex claims a three-face. Two
claims to the same face would give a square, so the total number of faces bounds a sum of
binomial coefficients. In dimension six, the tentative edge count 133 leaves two faces unclaimed.
In each five-dimensional facet the number of unclaimed faces is divisible by three, excluding
this case. Restrictions of a single published six-cube witness give all six lower bounds.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph Finset
open scoped BigOperators

private abbrev Vertex (n : ℕ) := Fin n → Bool

variable {n : ℕ}

private def flip (x : Vertex n) (i : Fin n) : Vertex n :=
  fun j => if j = i then !x j else x j

@[simp] private theorem flip_apply_same (x : Vertex n) (i : Fin n) : flip x i i = !x i := by
  simp [flip]

@[simp] private theorem flip_flip (x : Vertex n) (i : Fin n) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i <;> simp [flip, h]

private theorem flip_comm (x : Vertex n) (i j : Fin n) :
    flip (flip x i) j = flip (flip x j) i := by
  funext k
  simp only [flip]
  split_ifs <;> simp

private theorem flip_ne (x : Vertex n) (i : Fin n) : flip x i ≠ x := by
  intro h
  have hh := congrFun h i
  cases hx : x i <;> simp [hx] at hh

private theorem cube_adj_iff_flip (x y : Vertex n) :
    (hypercubeGraph n).Adj x y ↔ ∃ i, y = flip x i := by
  rw [hypercubeGraph_adj]
  constructor
  · rintro ⟨i, hi, hu⟩
    refine ⟨i, funext fun j => ?_⟩
    by_cases h : j = i
    · subst j
      cases hx : x i <;> cases hy : y i <;> simp_all [flip]
    · have he : x j = y j := by
        by_contra hn
        exact h (hu j hn)
      simp [flip, h, he]
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_, fun j hj => ?_⟩
    · cases hx : x i <;> simp [hx]
    · by_contra h
      exact hj (by simp [flip, h])

private theorem flip_dirs_injective (x : Vertex n) :
    Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  cases hx : x i <;> simp [flip, hij, hx] at hh

private def squareVertex (x : Vertex n) (i j : Fin n) : Fin 4 → Vertex n :=
  ![x, flip x i, flip (flip x i) j, flip x j]

private theorem squareVertex_injective (x : Vertex n) {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (squareVertex x i j) := by
  let signature : Fin 4 → Bool × Bool := ![(false, false), (true, false),
    (true, true), (false, true)]
  have hs : ∀ k, ((squareVertex x i j k i != x i), (squareVertex x i j k j != x j)) =
      signature k := by
    intro k
    fin_cases k <;> cases hx : x i <;> cases hy : x j <;>
      simp [squareVertex, signature, flip, hij, Ne.symm hij, hx, hy]
  have hinj : Function.Injective signature := by decide +kernel
  intro a b h
  apply hinj
  rw [← hs, ← hs, h]

private def HasSquare (G : SimpleGraph (Vertex n)) : Prop :=
  ∃ (x : Vertex n) (i j : Fin n), i ≠ j ∧
    G.Adj x (flip x i) ∧ G.Adj x (flip x j) ∧
    G.Adj (flip x i) (flip (flip x i) j) ∧ G.Adj (flip x j) (flip (flip x i) j)

private theorem square_not_free {G : SimpleGraph (Vertex n)} (h : HasSquare G) :
    ¬ (cycleGraph 4).Free G := by
  obtain ⟨x, i, j, hij, hi, hj, hij₁, hij₂⟩ := h
  intro hfree
  apply hfree
  refine ⟨⟨⟨squareVertex x i j, ?_⟩, squareVertex_injective x hij⟩⟩
  intro a b hab
  fin_cases a <;> fin_cases b <;> first
    | exact hi
    | exact hj
    | exact hij₁
    | exact hij₂
    | exact hi.symm
    | exact hj.symm
    | exact hij₁.symm
    | exact hij₂.symm
    | exact False.elim ((by decide : ¬ (cycleGraph 4).Adj _ _) hab)

private theorem hasSquare_of_copy {G : SimpleGraph (Vertex n)}
    (hle : G ≤ hypercubeGraph n) (h : Nonempty (SimpleGraph.Copy (cycleGraph 4) G)) :
    HasSquare G := by
  obtain ⟨f⟩ := h
  have h01 : G.Adj (f 0) (f 1) := f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 1)
  have h12 : G.Adj (f 1) (f 2) := f.toHom.map_adj (by decide : (cycleGraph 4).Adj 1 2)
  have h03 : G.Adj (f 0) (f 3) := f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 3)
  have h32 : G.Adj (f 3) (f 2) := f.toHom.map_adj (by decide : (cycleGraph 4).Adj 3 2)
  obtain ⟨i, hi⟩ := (cube_adj_iff_flip _ _).mp (hle h01)
  obtain ⟨j, hj⟩ := (cube_adj_iff_flip _ _).mp (hle h12)
  obtain ⟨k, hk⟩ := (cube_adj_iff_flip _ _).mp (hle h03)
  have hij : i ≠ j := by
    rintro rfl
    have he : f 2 = f 0 := by rw [hj, hi, flip_flip]
    exact (by decide : (2 : Fin 4) ≠ 0) (f.injective he)
  have hik : i ≠ k := by
    rintro rfl
    exact (by decide : (1 : Fin 4) ≠ 3) (f.injective (hi.trans hk.symm))
  have hkj : k = j := by
    by_contra hkj
    obtain ⟨l, _, hu⟩ := (hypercubeGraph_adj _ _ _).mp (hle h32)
    rw [hk, hj, hi] at hu
    have hil := hu i (by
      cases hx : f 0 i <;> simp [flip, hx, hik, hij])
    have hjl := hu j (by
      cases hx : f 0 j <;> simp [flip, hx, Ne.symm hkj, Ne.symm hij])
    exact hij (hil.trans hjl.symm)
  subst k
  refine ⟨f 0, i, j, hij, ?_, ?_, ?_, ?_⟩
  · simpa only [hi] using h01
  · simpa only [hk] using h03
  · simpa only [hi, hj] using h12
  · simpa only [hk, hj, hi] using h32

private def changes (x y : Vertex n) : Finset (Fin n) :=
  univ.filter fun i => x i ≠ y i

private def parity (x : Vertex n) : ℕ := (∑ i, (x i).toNat) % 2

private theorem parity_changes (x y : Vertex n) :
    (parity x + parity y) % 2 = (changes x y).card % 2 := by
  have h : (∑ i, ((x i).toNat + (y i).toNat)) =
      ∑ i, ((if x i ≠ y i then 1 else 0) + 2 * (if x i && y i then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> decide
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
    Finset.sum_const, smul_eq_mul, mul_one] at h
  unfold parity changes
  omega

private theorem changes_flip (x : Vertex n) (i : Fin n) : changes x (flip x i) = {i} := by
  ext j
  by_cases h : j = i
  · subst j
    cases hx : x i <;> simp [changes, hx]
  · simp [changes, flip, h]

private theorem parity_flip (x : Vertex n) (i : Fin n) :
    (parity x + parity (flip x i)) % 2 = 1 := by
  simpa [changes_flip] using parity_changes x (flip x i)

private def evenVertices (n : ℕ) : Finset (Vertex n) :=
  univ.filter fun x => parity x = 0

private theorem mem_evenVertices {x : Vertex n} : x ∈ evenVertices n ↔ parity x = 0 := by
  simp [evenVertices]

private theorem mem_evenVertices_flip (x : Vertex n) (i : Fin n) :
    flip x i ∈ evenVertices n ↔ x ∉ evenVertices n := by
  simp only [mem_evenVertices]
  have h := parity_flip x i
  have hx : parity x < 2 := Nat.mod_lt _ (by decide)
  have hy : parity (flip x i) < 2 := Nat.mod_lt _ (by decide)
  omega

private def directions (G : SimpleGraph (Vertex n)) [DecidableRel G.Adj]
    (x : Vertex n) : Finset (Fin n) :=
  univ.filter fun i => G.Adj x (flip x i)

@[simp] private theorem mem_directions {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    {x : Vertex n} {i : Fin n} : i ∈ directions G x ↔ G.Adj x (flip x i) := by
  simp [directions]

private theorem sum_directions_eq_ncard {G : SimpleGraph (Vertex n)}
    [DecidableRel G.Adj] (hle : G ≤ hypercubeGraph n) :
    ∑ x ∈ evenVertices n, (directions G x).card = G.edgeSet.ncard := by
  classical
  have hb : G.IsBipartiteWith (↑(evenVertices n) : Set (Vertex n))
      (↑(evenVertices n) : Set (Vertex n))ᶜ := by
    refine ⟨disjoint_compl_right, fun {x y} hxy => ?_⟩
    obtain ⟨i, rfl⟩ := (cube_adj_iff_flip _ _).mp (hle hxy)
    change x ∈ evenVertices n ∧ flip x i ∉ evenVertices n ∨
      x ∉ evenVertices n ∧ flip x i ∈ evenVertices n
    rw [mem_evenVertices_flip]
    by_cases hx : x ∈ evenVertices n <;> simp [hx]
  have hb' : G.IsBipartiteWith (↑(evenVertices n) : Set (Vertex n))
      (↑((evenVertices n)ᶜ) : Set (Vertex n)) := by
    rw [coe_compl]
    exact hb
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset, ← G.isBipartiteWith_sum_degrees_eq_card_edges hb']
  apply Finset.sum_congr rfl
  intro x _
  rw [← G.card_neighborFinset_eq_degree, ← card_image_of_injective _ (flip_dirs_injective x)]
  congr 1
  ext y
  simp only [mem_image, mem_directions, G.mem_neighborFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hy
    obtain ⟨i, rfl⟩ := (cube_adj_iff_flip _ _).mp (hle hy)
    exact ⟨i, hy, rfl⟩

-- A face is its free-coordinate set and its anchor, with zero on the free coordinates.
private abbrev Face (n : ℕ) := Finset (Fin n) × Vertex n

private def faceOf (x : Vertex n) (s : Finset (Fin n)) : Face n :=
  (s, fun i => if i ∈ s then false else x i)

private def faces (n k : ℕ) : Finset (Face n) :=
  (((univ : Finset (Fin n)).powersetCard k) ×ˢ (univ : Finset (Vertex n))).filter
    fun f => ∀ i ∈ f.1, f.2 i = false

private theorem faceOf_mem (x : Vertex n) {s : Finset (Fin n)} {k : ℕ}
    (h : s.card = k) : faceOf x s ∈ faces n k := by
  refine mem_filter.mpr ⟨by simp [faceOf, h], ?_⟩
  intro i hi
  exact ite_eq_left hi

private theorem face_card {f : Face n} {k : ℕ} (hf : f ∈ faces n k) : f.1.card = k :=
  (mem_powersetCard.mp (mem_product.mp (mem_filter.mp hf).1).1).2

private theorem faceOf_anchor {f : Face n} {k : ℕ} (hf : f ∈ faces n k) :
    faceOf f.2 f.1 = f := by
  refine Prod.ext rfl (funext fun i => ?_)
  have h := (mem_filter.mp hf).2
  by_cases hi : i ∈ f.1 <;> simp [faceOf, hi, h i]

private theorem faceOf_flip (x : Vertex n) {i : Fin n} {s : Finset (Fin n)} (hi : i ∈ s) :
    faceOf (flip x i) s = faceOf x s := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases h : j = i
  · subst j
    simp [faceOf, hi]
  · simp [faceOf, flip, h]

private theorem changes_subset_of_faceOf_eq {x y : Vertex n} {s : Finset (Fin n)}
    (h : faceOf x s = faceOf y s) : changes x y ⊆ s := by
  intro i hi
  by_contra his
  have hxy := congrFun (congrArg Prod.snd h) i
  exact (mem_filter.mp hi).2 (by simpa [faceOf, his] using hxy)

private theorem eq_flip_flip_of_changes {x y : Vertex n} {i j : Fin n}
    (hij : i ≠ j) (hs : changes x y = {i, j}) : y = flip (flip x i) j := by
  funext k
  have hm : x k ≠ y k ↔ k = i ∨ k = j := by
    simpa [changes] using (show k ∈ changes x y ↔ k ∈ ({i, j} : Finset _) by rw [hs])
  by_cases hi : k = i
  · subst k
    have h := hm.mpr (Or.inl rfl)
    cases hx : x i <;> cases hy : y i <;> simp_all [flip]
  · by_cases hj : k = j
    · subst k
      have h := hm.mpr (Or.inr rfl)
      cases hx : x j <;> cases hy : y j <;> simp_all [flip]
    · have he : x k = y k := by simpa [hi, hj] using hm
      simp [flip, hi, hj, he]

private def claims (G : SimpleGraph (Vertex n)) [DecidableRel G.Adj]
    (vertices : Finset (Vertex n)) (allowed : Finset (Fin n)) :
    Finset (Σ _ : Vertex n, Finset (Fin n)) :=
  vertices.sigma fun x => (directions G x ∩ allowed).powersetCard 3

private def claimFace (p : Σ _ : Vertex n, Finset (Fin n)) : Face n := faceOf p.1 p.2

private theorem claimFace_injOn {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (hfree : (cycleGraph 4).Free G) {vertices : Finset (Vertex n)}
    (hv : vertices ⊆ evenVertices n) (allowed : Finset (Fin n)) :
    Set.InjOn (claimFace (n := n))
      (↑(claims G vertices allowed) : Set (Σ _ : Vertex n, Finset (Fin n))) := by
  rintro ⟨x, s⟩ hx ⟨y, t⟩ hy he
  have hst : s = t := congrArg Prod.fst he
  subst t
  change (⟨x, s⟩ : Σ _ : Vertex n, Finset (Fin n)) ∈ claims G vertices allowed at hx
  change (⟨y, s⟩ : Σ _ : Vertex n, Finset (Fin n)) ∈ claims G vertices allowed at hy
  obtain ⟨hxv, hxs⟩ := mem_sigma.mp hx
  obtain ⟨hyv, hys⟩ := mem_sigma.mp hy
  by_cases hxy : x = y
  · subst y
    rfl
  exfalso
  have hsub : changes x y ⊆ s := changes_subset_of_faceOf_eq he
  have hcard := card_le_card hsub
  have hx0 := mem_evenVertices.mp (hv hxv)
  have hy0 := mem_evenVertices.mp (hv hyv)
  have hp := parity_changes x y
  rw [hx0, hy0] at hp
  have hs3 : s.card = 3 := (mem_powersetCard.mp hxs).2
  have hpos : 0 < (changes x y).card := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have htwo : (changes x y).card = 2 := by omega
  obtain ⟨i, j, hij, hd⟩ := card_eq_two.mp htwo
  have hi : i ∈ s := hsub (by simp [hd])
  have hj : j ∈ s := hsub (by simp [hd])
  have hd₁ := fun {k} (hk : k ∈ s) =>
    mem_directions.mp (mem_inter.mp ((mem_powersetCard.mp hxs).1 hk)).1
  have hd₂ := fun {k} (hk : k ∈ s) =>
    mem_directions.mp (mem_inter.mp ((mem_powersetCard.mp hys).1 hk)).1
  have ey := eq_flip_flip_of_changes hij hd
  have ei : flip y i = flip x j := by rw [ey, flip_comm x i j, flip_flip]
  have ej : flip y j = flip x i := by rw [ey, flip_flip]
  have ha := (hd₂ hj).symm
  have hb := (hd₂ hi).symm
  rw [ej, ey] at ha
  rw [ei, ey] at hb
  exact square_not_free ⟨x, i, j, hij, hd₁ hi, hd₁ hj, ha, hb⟩ hfree

private def covered (G : SimpleGraph (Vertex n)) [DecidableRel G.Adj]
    (vertices : Finset (Vertex n)) (allowed : Finset (Fin n)) : Finset (Face n) :=
  (claims G vertices allowed).image claimFace

private theorem covered_subset {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (vertices : Finset (Vertex n)) (allowed : Finset (Fin n)) :
    covered G vertices allowed ⊆ faces n 3 := by
  intro f hf
  obtain ⟨⟨x, s⟩, hs, rfl⟩ := mem_image.mp hf
  exact faceOf_mem x (mem_powersetCard.mp (mem_sigma.mp hs).2).2

private theorem card_covered {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (hfree : (cycleGraph 4).Free G) {vertices : Finset (Vertex n)}
    (hv : vertices ⊆ evenVertices n) (allowed : Finset (Fin n)) :
    (covered G vertices allowed).card =
      ∑ x ∈ vertices, (directions G x ∩ allowed).card.choose 3 := by
  rw [covered, card_image_of_injOn (claimFace_injOn hfree hv allowed), claims, card_sigma]
  simp only [card_powersetCard]

private theorem card_covered_univ {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (hfree : (cycleGraph 4).Free G) :
    (covered G (evenVertices n) univ).card =
      ∑ x ∈ evenVertices n, (directions G x).card.choose 3 := by
  simpa only [inter_univ] using card_covered hfree (Subset.rfl : evenVertices n ⊆ _) univ

private def facetVertices (j : Fin n) (b : Bool) : Finset (Vertex n) :=
  (evenVertices n).filter fun x => x j = b

private def inFacet (j : Fin n) (b : Bool) (f : Face n) : Prop := j ∉ f.1 ∧ f.2 j = b

private instance facetDecidable (j : Fin n) (b : Bool) (f : Face n) :
    Decidable (inFacet j b f) := by unfold inFacet; infer_instance

private def facetFaces (j : Fin n) (b : Bool) : Finset (Face n) :=
  (faces n 3).filter (inFacet j b)

private theorem covered_facet {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (j : Fin n) (b : Bool) :
    covered G (facetVertices j b) (univ.erase j) =
      (covered G (evenVertices n) univ).filter (inFacet j b) := by
  ext f
  simp only [covered, mem_filter, mem_image]
  constructor
  · rintro ⟨⟨x, s⟩, hp, rfl⟩
    obtain ⟨hx, hs⟩ := mem_sigma.mp hp
    obtain ⟨hxs, hc⟩ := mem_powersetCard.mp hs
    obtain ⟨he, hb⟩ := mem_filter.mp hx
    have hj : j ∉ s := fun hj => (mem_erase.mp (mem_inter.mp (hxs hj)).2).1 rfl
    refine ⟨⟨⟨x, s⟩, mem_sigma.mpr ⟨he, mem_powersetCard.mpr ⟨?_, hc⟩⟩, rfl⟩, ?_⟩
    · intro i hi
      exact mem_inter.mpr ⟨(mem_inter.mp (hxs hi)).1, mem_univ _⟩
    · exact ⟨hj, by simpa [claimFace, faceOf, hj] using hb⟩
  · rintro ⟨⟨⟨x, s⟩, hp, rfl⟩, hj, hb⟩
    obtain ⟨hx, hs⟩ := mem_sigma.mp hp
    obtain ⟨hxs, hc⟩ := mem_powersetCard.mp hs
    refine ⟨⟨x, s⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨hx, ?_⟩,
      mem_powersetCard.mpr ⟨?_, hc⟩⟩, rfl⟩
    · change j ∉ s at hj
      change (if j ∈ s then false else x j) = b at hb
      rwa [ite_eq_right hj] at hb
    · intro i hi
      exact mem_inter.mpr ⟨(mem_inter.mp (hxs hi)).1,
        mem_erase.mpr ⟨fun h => hj (h ▸ hi), mem_univ _⟩⟩

private theorem missing_facet {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (j : Fin n) (b : Bool) :
    facetFaces j b \ covered G (facetVertices j b) (univ.erase j) =
      (faces n 3 \ covered G (evenVertices n) univ).filter (inFacet j b) := by
  rw [facetFaces, covered_facet]
  ext f
  simp only [mem_sdiff, mem_filter]
  tauto

private theorem directions_card_le (G : SimpleGraph (Vertex n)) [DecidableRel G.Adj]
    (x : Vertex n) : (directions G x).card ≤ n := by
  simpa using card_le_univ (directions G x)

private theorem inter_erase_eq (s : Finset (Fin n)) (j : Fin n) :
    s ∩ univ.erase j = s.erase j := by
  ext i
  simp [and_comm]

private theorem card_facet_directions {G : SimpleGraph (Vertex 6)} [DecidableRel G.Adj]
    {x : Vertex 6} (j : Fin 6) (h₁ : 4 ≤ (directions G x).card)
    (h₂ : (directions G x).card ≤ 5) :
    let d := (directions G x ∩ univ.erase j).card
    3 ≤ d ∧ d ≤ 5 := by
  dsimp
  rw [inter_erase_eq]
  by_cases h : j ∈ directions G x
  · rw [card_erase_of_mem h]
    omega
  · rw [erase_eq_of_notMem h]
    exact ⟨by omega, h₂⟩

private theorem upperFive {G : SimpleGraph (Vertex 5)}
    (hle : G ≤ hypercubeGraph 5) (hfree : (cycleGraph 4).Free G) : G.edgeSet.ncard ≤ 56 := by
  classical
  have hsum : (∑ x ∈ evenVertices 5, (directions G x).card.choose 3) ≤ 40 := by
    rw [← card_covered_univ hfree]
    exact (card_le_card (covered_subset _ _)).trans_eq (by decide +kernel)
  have ht : ∀ d : Fin 6, 3 * d.val ≤ d.val.choose 3 + 8 := by decide +kernel
  have h := sum_le_sum (s := evenVertices 5) (fun x _ =>
    ht ⟨(directions G x).card, Nat.lt_succ_of_le (directions_card_le G x)⟩)
  simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul,
    sum_directions_eq_ncard hle] at h
  have hc : (evenVertices 5).card = 16 := by decide +kernel
  omega

private def slack (d : ℕ) : ℕ := d.choose 3 + 20 - 6 * d

set_option maxHeartbeats 1200000 in
-- Count the three-faces of the twelve coordinate facets by kernel reduction.
private theorem facetFaces_card (j : Fin 6) (b : Bool) : (facetFaces j b).card = 40 := by
  fin_cases j <;> cases b <;> decide +kernel

private theorem facetVertices_card (j : Fin 6) (b : Bool) : (facetVertices j b).card = 16 := by
  fin_cases j <;> cases b <;> decide +kernel

private theorem missed_eq_empty_of_facets {n : ℕ} (hn : 3 < n) (used : Finset (Face n))
    (hfull : ∀ (j : Fin n) (b : Bool), ((faces n 3 \ used).filter (inFacet j b)) = ∅) :
    faces n 3 \ used = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr ?_
  intro f hf
  have hfc : f.1.card = 3 := face_card (mem_sdiff.mp hf).1
  have hnot : ¬ ∀ j : Fin n, j ∈ f.1 := by
    intro hall
    have he : f.1 = univ := eq_univ_of_forall hall
    rw [he, card_univ, Fintype.card_fin] at hfc
    omega
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have h : f ∈ (faces n 3 \ used).filter (inFacet j (f.2 j)) :=
    mem_filter.mpr ⟨hf, hj, rfl⟩
  rw [hfull] at h
  exact notMem_empty f h

private theorem upperSix {G : SimpleGraph (Vertex 6)}
    (hle : G ≤ hypercubeGraph 6) (hfree : (cycleGraph 4).Free G) : G.edgeSet.ncard ≤ 132 := by
  classical
  let used := covered G (evenVertices 6) univ
  let missed := faces 6 3 \ used
  let gap := ∑ x ∈ evenVertices 6, slack (directions G x).card
  have hsub : used ⊆ faces 6 3 := covered_subset _ _
  have hcard : (faces 6 3).card = 160 := by decide +kernel
  have heven : (evenVertices 6).card = 32 := by decide +kernel
  have hused : used.card ≤ 160 := (card_le_card hsub).trans_eq hcard
  have ht : ∀ d : Fin 7, 6 * d.val + slack d.val = d.val.choose 3 + 20 := by decide +kernel
  have hbalance : 6 * G.edgeSet.ncard + gap = used.card + 640 := by
    have h := sum_congr (s₁ := evenVertices 6) rfl (fun x _ =>
      ht ⟨(directions G x).card, Nat.lt_succ_of_le (directions_card_le G x)⟩)
    simpa only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul,
      sum_directions_eq_ncard hle, ← card_covered_univ hfree, heven] using h
  by_contra hbig
  have hgap : gap ≤ 2 := by omega
  have hmiss : missed.card ≤ 2 := by
    change (faces 6 3 \ used).card ≤ 2
    rw [card_sdiff_of_subset hsub, hcard]
    omega
  have hdegree (x : Vertex 6) (hx : x ∈ evenVertices 6) :
      4 ≤ (directions G x).card ∧ (directions G x).card ≤ 5 := by
    have hsmall : slack (directions G x).card ≤ gap :=
      single_le_sum (f := fun y : Vertex 6 => slack (directions G y).card)
        (s := evenVertices 6) (fun _ _ => Nat.zero_le _) hx
    have hd : ∀ d : Fin 7, slack d.val ≤ 2 → 4 ≤ d.val ∧ d.val ≤ 5 := by decide +kernel
    exact hd ⟨_, Nat.lt_succ_of_le (directions_card_le G x)⟩ (hsmall.trans hgap)
  have hgapZero : gap = 0 := by
    apply sum_eq_zero
    intro x hx
    have hd := hdegree x hx
    have hor : (directions G x).card = 4 ∨ (directions G x).card = 5 := by omega
    rcases hor with h | h <;> rw [h] <;> decide
  -- The local count is 16 modulo three, so the deficit from 40 is a multiple of three.
  have hFacetFull (j : Fin 6) (b : Bool) : missed.filter (inFacet j b) = ∅ := by
    let localUsed := covered G (facetVertices j b) (univ.erase j)
    have hloc : localUsed ⊆ facetFaces j b := by
      rw [show localUsed = _ from covered_facet (G := G) j b]
      exact filter_subset_filter _ hsub
    let d (x : Vertex 6) := (directions G x ∩ univ.erase j).card
    have hmod : ∀ a : Fin 6, 3 ≤ a.val → a.val.choose 3 = 3 * (a.val.choose 3 / 3) + 1 := by
      decide +kernel
    have hpoint (x : Vertex 6) (hx : x ∈ facetVertices j b) :
        (d x).choose 3 = 3 * ((d x).choose 3 / 3) + 1 := by
      have h := hdegree x (mem_filter.mp hx).1
      have hh : 3 ≤ d x ∧ d x ≤ 5 := card_facet_directions j h.1 h.2
      exact hmod ⟨d x, Nat.lt_succ_of_le hh.2⟩ hh.1
    have hv : facetVertices j b ⊆ evenVertices 6 := by
      intro x hx
      exact (mem_filter.mp hx).1
    have hcount : localUsed.card = ∑ x ∈ facetVertices j b, (d x).choose 3 :=
      card_covered (G := G) hfree (vertices := facetVertices j b) hv (univ.erase j)
    have hlocal : localUsed.card = 3 * (∑ x ∈ facetVertices j b, (d x).choose 3 / 3) + 16 := by
      calc
        localUsed.card = ∑ x ∈ facetVertices j b, (d x).choose 3 := hcount
        _ = ∑ x ∈ facetVertices j b, (3 * ((d x).choose 3 / 3) + 1) := sum_congr rfl hpoint
        _ = _ := by
          simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one,
            facetVertices_card]
    have hsmall : (missed.filter (inFacet j b)).card ≤ 2 :=
      (card_le_card (filter_subset (inFacet j b) missed)).trans hmiss
    have hleLocal : localUsed.card ≤ 40 := (card_le_card hloc).trans_eq (facetFaces_card j b)
    have hdiff : (missed.filter (inFacet j b)).card = 40 - localUsed.card := by
      have heq : missed.filter (inFacet j b) = facetFaces j b \ localUsed :=
        (missing_facet (G := G) j b).symm
      rw [heq, card_sdiff_of_subset hloc, facetFaces_card]
    apply card_eq_zero.mp
    omega
  have hnone : missed = ∅ := missed_eq_empty_of_facets (by decide : 3 < 6) used hFacetFull
  have hz : missed.card = 0 := by rw [hnone, card_empty]
  change (faces 6 3 \ used).card = 0 at hz
  rw [card_sdiff_of_subset hsub, hcard] at hz
  omega

-- Orient each missing edge from its even endpoint; the other direction determines a square.
private def missingIncidences (G : SimpleGraph (Vertex n)) [DecidableRel G.Adj] :
    Finset (Σ _ : Vertex n, Σ _ : Fin n, Fin n) :=
  (evenVertices n).sigma fun x => (univ \ directions G x).sigma fun i => univ.erase i

private def incidenceFace (p : Σ _ : Vertex n, Σ _ : Fin n, Fin n) : Face n :=
  faceOf p.1 {p.2.1, p.2.2}

private theorem exists_missingIncidence {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (x : Vertex n) {i j : Fin n} (hij : i ≠ j) (h : ¬ G.Adj x (flip x i)) :
    ∃ p ∈ missingIncidences G, incidenceFace p = faceOf x {i, j} := by
  by_cases hx : x ∈ evenVertices n
  · refine ⟨⟨x, i, j⟩, ?_, rfl⟩
    simp [missingIncidences, hx, h, Ne.symm hij]
  · refine ⟨⟨flip x i, i, j⟩, ?_, faceOf_flip x (by simp)⟩
    have he := (mem_evenVertices_flip x i).mpr hx
    have hh : ¬ G.Adj (flip x i) x := fun ha => h (ha.symm)
    simp [missingIncidences, he, hh, Ne.symm hij]

private theorem squares_le_missingIncidences {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (hfree : (cycleGraph 4).Free G) : (faces n 2).card ≤ (missingIncidences G).card := by
  apply card_le_card_of_surjOn incidenceFace
  intro f hf
  change f ∈ faces n 2 at hf
  obtain ⟨i, j, hij, hijset⟩ := card_eq_two.mp (face_card hf)
  change ∃ p ∈ missingIncidences G, incidenceFace p = f
  let x := f.2
  have hface : faceOf x {i, j} = f := by rw [← hijset]; exact faceOf_anchor hf
  have hface' : faceOf x {j, i} = f := by rw [pair_comm, hface]
  by_cases hi : G.Adj x (flip x i)
  swap
  · simpa only [hface] using exists_missingIncidence x hij hi
  by_cases hj : G.Adj x (flip x j)
  swap
  · simpa only [hface'] using exists_missingIncidence x (Ne.symm hij) hj
  by_cases hij₁ : G.Adj (flip x i) (flip (flip x i) j)
  swap
  · have hh : faceOf (flip x i) {j, i} = f := by rw [faceOf_flip x (by simp), hface']
    simpa only [hh] using exists_missingIncidence (flip x i) (Ne.symm hij) hij₁
  have hij₂ : ¬ G.Adj (flip x j) (flip (flip x j) i) := by
    intro h
    rw [flip_comm x j i] at h
    exact square_not_free ⟨x, i, j, hij, hi, hj, hij₁, h⟩ hfree
  have hh : faceOf (flip x j) {i, j} = f := by rw [faceOf_flip x (by simp), hface]
  simpa only [hh] using exists_missingIncidence (flip x j) hij hij₂

private theorem card_missingIncidences {G : SimpleGraph (Vertex n)} [DecidableRel G.Adj]
    (hle : G ≤ hypercubeGraph n) :
    (missingIncidences G).card = ((evenVertices n).card * n - G.edgeSet.ncard) * (n - 1) := by
  have hc (i : Fin n) : ((univ : Finset (Fin n)).erase i).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hdirs (x : Vertex n) : (univ \ directions G x).card = n - (directions G x).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  simp only [missingIncidences, card_sigma, hc, sum_const, smul_eq_mul, ← sum_mul]
  congr 1
  have hpoint (x : Vertex n) :
      (univ \ directions G x).card + (directions G x).card = n := by
    rw [hdirs]
    have hd := directions_card_le G x
    omega
  have hsum := sum_congr (s₁ := evenVertices n) rfl (fun x _ => hpoint x)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, sum_directions_eq_ncard hle] at hsum
  omega

private theorem upperOne {G : SimpleGraph (Vertex 1)}
    (hle : G ≤ hypercubeGraph 1) : G.edgeSet.ncard ≤ 1 := by
  classical
  rw [← sum_directions_eq_ncard hle]
  have h : (evenVertices 1).card = 1 := by decide +kernel
  simpa only [sum_const, smul_eq_mul, h, mul_one] using
    sum_le_sum (s := evenVertices 1) (fun x _ => directions_card_le G x)

private theorem upperTwoToFour {G : SimpleGraph (Vertex n)}
    (hle : G ≤ hypercubeGraph n) (hfree : (cycleGraph 4).Free G) :
    (faces n 2).card ≤ ((evenVertices n).card * n - G.edgeSet.ncard) * (n - 1) := by
  classical
  rw [← card_missingIncidences hle]
  exact squares_le_missingIncidences hfree

-- Bit i of the index encodes coordinate i. Character u of the spin string is the spin at u.
-- Data: q6_odd_square_132.json in Minamo Minamoto's c4free-hypercube repository at
-- 918025df85b509c4311675e0d1ba65f26f23d98d; see arXiv:2603.29127v5.
private def spins : List Bool :=
  "1110000000000000110010111000111010111111000101101100111111100100".toList.map (· == '1')

private def liftIndex (dims : Fin n → Fin 6) (anchor : ℕ) (x : Vertex n) : ℕ :=
  anchor + ∑ i, (x i).toNat * 2 ^ (dims i).val

private def keep (dims : Fin n → Fin 6) (anchor : ℕ) (x : Vertex n) (i : Fin n) : Bool :=
  let u := liftIndex dims anchor x
  let v := liftIndex dims anchor (flip x i)
  let lowerOnes : ℕ := ∑ j : Fin 6,
    if j < dims i then ((min u v).testBit j.val).toNat else 0
  (spins[u]?.getD false != spins[v]?.getD false) == (lowerOnes % 2 == 1)

private theorem keep_flip (dims : Fin n → Fin 6) (anchor : ℕ) (x : Vertex n) (i : Fin n) :
    keep dims anchor (flip x i) i = keep dims anchor x i := by
  simp only [keep, flip_flip, min_comm (liftIndex dims anchor (flip x i))]
  rw [bne_comm]

private def witness (dims : Fin n → Fin 6) (anchor : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := ∃ i, y = flip x i ∧ keep dims anchor x i = true
  symm := ⟨by
    rintro x _ ⟨i, rfl, hi⟩
    exact ⟨i, (flip_flip x i).symm, (keep_flip dims anchor x i).trans hi⟩⟩
  loopless := ⟨by
    rintro x ⟨i, h, _⟩
    exact flip_ne x i h.symm⟩

private theorem witness_le (dims : Fin n → Fin 6) (anchor : ℕ) :
    witness dims anchor ≤ hypercubeGraph n := by
  rintro x y ⟨i, hi, _⟩
  exact (cube_adj_iff_flip x y).mpr ⟨i, hi⟩

private theorem witness_adj_flip (dims : Fin n → Fin 6) (anchor : ℕ) (x : Vertex n)
    (i : Fin n) : (witness dims anchor).Adj x (flip x i) ↔ keep dims anchor x i = true := by
  constructor
  · rintro ⟨j, hj, hk⟩
    rwa [← flip_dirs_injective x hj] at hk
  · exact fun h => ⟨i, rfl, h⟩

private def witnessCount (dims : Fin n → Fin 6) (anchor : ℕ) : ℕ :=
  ∑ x ∈ evenVertices n, (univ.filter fun i => keep dims anchor x i = true).card

private theorem witness_ncard (dims : Fin n → Fin 6) (anchor : ℕ) :
    (witness dims anchor).edgeSet.ncard = witnessCount dims anchor := by
  classical
  rw [← sum_directions_eq_ncard (witness_le dims anchor)]
  unfold witnessCount
  apply sum_congr rfl
  intro x _
  congr 1
  ext i
  simp [witness_adj_flip]

private theorem witness_free (dims : Fin n → Fin 6) (anchor : ℕ)
    (h : ∀ x : Vertex n, ∀ i j : Fin n, i ≠ j →
      ¬ (keep dims anchor x i = true ∧ keep dims anchor x j = true ∧
        keep dims anchor (flip x i) j = true ∧ keep dims anchor (flip x j) i = true)) :
    (cycleGraph 4).Free (witness dims anchor) := by
  by_contra hf
  obtain ⟨x, i, j, hij, h₁, h₂, h₃, h₄⟩ :=
    hasSquare_of_copy (witness_le dims anchor) hf
  rw [flip_comm x i j] at h₄
  exact h x i j hij ⟨(witness_adj_flip _ _ _ _).mp h₁, (witness_adj_flip _ _ _ _).mp h₂,
    (witness_adj_flip _ _ _ _).mp h₃, (witness_adj_flip _ _ _ _).mp h₄⟩

private theorem witness_attains (dims : Fin n → Fin 6) (anchor m : ℕ)
    (hcount : witnessCount dims anchor = m) (hfree : (cycleGraph 4).Free (witness dims anchor))
    (hupper : ∀ G : SimpleGraph (Vertex n), G ≤ hypercubeGraph n → (cycleGraph 4).Free G →
      G.edgeSet.ncard ≤ m) : hypercubeTuranNumber n (cycleGraph 4) = m := by
  let G := witness dims anchor
  let S := SimpleGraph.toSubgraph G (witness_le dims anchor)
  have hS : (cycleGraph 4).Free S.coe := by
    intro h
    exact hfree (h.trans ⟨S.coeEmbeddingSpanningCoe.toCopy⟩)
  have hSm : S.edgeSet.ncard = m := by
    rw [← Subgraph.edgeSet_spanningCoe]
    exact (witness_ncard dims anchor).trans hcount
  apply le_antisymm _ (hSm ▸ le_hypercubeTuranNumber n S hS)
  obtain ⟨T, hT, hm⟩ := exists_attains_hypercubeTuranNumber n ⟨S, hS⟩
  have ht : (cycleGraph 4).Free T.spanningCoe := by
    intro h
    obtain ⟨f⟩ := h
    have hm0 (i : Fin 4) : f i ∈ T.verts := by
      have hneighbor : ∀ i : Fin 4, ∃ j, (cycleGraph 4).Adj i j := by decide +kernel
      obtain ⟨j, hj⟩ := hneighbor i
      exact T.edge_vert (f.toHom.map_adj hj)
    exact hT ⟨⟨⟨fun i => ⟨f i, hm0 i⟩, fun h => f.toHom.map_adj h⟩,
      fun _ _ he => f.injective (congrArg Subtype.val he)⟩⟩
  rw [← hm, ← Subgraph.edgeSet_spanningCoe]
  exact hupper T.spanningCoe T.spanningCoe_le ht

private theorem valueOne : hypercubeTuranNumber 1 (cycleGraph 4) = 1 := by
  classical
  apply witness_attains ![5] 29 1 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · exact fun _ hle _ => upperOne hle

private theorem valueTwo : hypercubeTuranNumber 2 (cycleGraph 4) = 3 := by
  classical
  apply witness_attains ![4, 5] 15 3 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · intro G hle hf
    have h := upperTwoToFour hle hf
    rw [show (faces 2 2).card = 1 by decide +kernel,
      show (evenVertices 2).card = 2 by decide +kernel] at h
    change 1 ≤ (4 - G.edgeSet.ncard) * 1 at h
    omega

private theorem valueThree : hypercubeTuranNumber 3 (cycleGraph 4) = 9 := by
  classical
  apply witness_attains ![3, 4, 5] 7 9 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · intro G hle hf
    have h := upperTwoToFour hle hf
    rw [show (faces 3 2).card = 6 by decide +kernel,
      show (evenVertices 3).card = 4 by decide +kernel] at h
    change 6 ≤ (12 - G.edgeSet.ncard) * 2 at h
    omega

private theorem valueFour : hypercubeTuranNumber 4 (cycleGraph 4) = 24 := by
  classical
  apply witness_attains ![1, 2, 4, 5] 8 24 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · intro G hle hf
    have h := upperTwoToFour hle hf
    rw [show (faces 4 2).card = 24 by decide +kernel,
      show (evenVertices 4).card = 8 by decide +kernel] at h
    change 24 ≤ (32 - G.edgeSet.ncard) * 3 at h
    omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Evaluate the explicit restriction on the coordinate squares of Q₅.
private theorem valueFive : hypercubeTuranNumber 5 (cycleGraph 4) = 56 := by
  classical
  apply witness_attains ![1, 2, 3, 4, 5] 0 56 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · exact fun _ hle hf => upperFive hle hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
-- Evaluate the published witness on the coordinate squares of Q₆.
private theorem valueSix : hypercubeTuranNumber 6 (cycleGraph 4) = 132 := by
  classical
  apply witness_attains id 0 132 (by decide +kernel)
  · apply witness_free
    decide +kernel
  · exact fun _ hle hf => upperSix hle hf

/-- **Four-cycle-free subgraphs of the hypercubes of dimensions one to six.** For a natural
number $n$, let $Q_n$ be the $n$-dimensional hypercube, let $C_4$ be the cycle on four vertices,
and let $\mathrm{ex}(Q_n, C_4)$ be the largest number of edges of a subgraph of $Q_n$ that
contains no copy of $C_4$. Then for $n = 1, 2, 3, 4, 5, 6$ the value of $\mathrm{ex}(Q_n, C_4)$
is $1$, $3$, $9$, $24$, $56$ and $132$ respectively.

Source: OEIS A245762; `ex(Q₆, C₄) = 132` is H. Harborth and H. Nienborg,
*Maximum number of edges in squarefree subgraphs of the n-cube*, Bull. Inst.
Combin. Appl. 12 (1994), 55–60; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem hypercubeTuranNumber_cycleGraph_four_one_to_six :
    (List.range 6).map (fun i => hypercubeTuranNumber (i + 1) (cycleGraph 4)) =
      [1, 3, 9, 24, 56, 132] := by
  change [hypercubeTuranNumber 1 _, hypercubeTuranNumber 2 _, hypercubeTuranNumber 3 _,
    hypercubeTuranNumber 4 _, hypercubeTuranNumber 5 _, hypercubeTuranNumber 6 _] = _
  rw [valueOne, valueTwo, valueThree, valueFour, valueFive, valueSix]

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
