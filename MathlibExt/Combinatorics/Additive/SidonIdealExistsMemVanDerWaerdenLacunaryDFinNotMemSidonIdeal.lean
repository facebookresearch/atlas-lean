/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Data.Fintype.Pigeonhole
public import MathlibExt.Combinatorics.Additive.SidonIdeal

/-!
# A gap-lacunary set outside the Sidon ideal

We combine affine copies of base-three digit cubes. Finite grids obstruct Sidon covers, while
separation of the cubes gives growing gaps and excludes arithmetic progressions.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

private def cube (d : ℕ) : Finset ℕ :=
  (Behrend.box d 2).image (Behrend.map 3)

private lemma cube_free (d : ℕ) : ThreeAPFree (cube d : Set ℕ) := by
  rw [cube, Finset.coe_image]
  apply ThreeAPFree.image' (Behrend.map 3) (Behrend.map_injOn.mono _) _
  · rw [Set.add_subset_iff]
    intro a ha b hb i
    have ha' := Behrend.mem_box.mp ha i
    have hb' := Behrend.mem_box.mp hb i
    change a i + b i < 3
    omega
  · intro a ha b hb c hc h
    ext i
    have ha' := Behrend.mem_box.mp ha i
    have hb' := Behrend.mem_box.mp hb i
    have hc' := Behrend.mem_box.mp hc i
    have hi := congrFun h i
    change a i + c i = b i + b i at hi
    omega

private lemma pair_mem_cube {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    3 ^ (i : ℕ) + 3 ^ (j : ℕ) ∈ cube d := by
  let x : Fin d → ℕ := Pi.single i 1 + Pi.single j 1
  have hx : x ∈ Behrend.box d 2 := by
    rw [Behrend.mem_box]
    intro k
    simp only [x, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp_all
  refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
  simp [x, Behrend.map_apply, Finset.sum_add_distrib, add_mul, Pi.single_apply]

private lemma grid_obstruction (n : ℕ) (f : Fin (n * (n + 1) * (n + 1) + 1) → Fin (n + 1) → ℕ)
    (hrow : ∀ j, Function.Injective (fun i => f i j))
    (hcol : ∀ i, Function.Injective (f i))
    (hrect : ∀ i k j l, f i j + f k l = f i l + f k j)
    (S : Fin n → Set ℕ) (hS : ∀ k, (S k).IsSidon)
    (hcover : ∀ i j, f i j ∈ ⋃ k, S k) : False := by
  classical
  have hc (i) (j) : ∃ k, f i j ∈ S k := Set.mem_iUnion.mp (hcover i j)
  choose color hcolor using hc
  have hp (i) := Fintype.exists_ne_map_eq_of_card_lt (color i)
    (by simp : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)))
  choose a b hab heq using hp
  let tag (i : Fin (n * (n + 1) * (n + 1) + 1)) : Fin n × Fin (n + 1) × Fin (n + 1) :=
    (color i (a i), a i, b i)
  obtain ⟨i, k, hik, htag⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by simp [mul_assoc])
  have hcik : color i (a i) = color k (a k) := congrArg Prod.fst htag
  have haik : a i = a k := congrArg (fun t => t.2.1) htag
  have hbik : b i = b k := congrArg (fun t => t.2.2) htag
  have hi1 := hcolor i (a i)
  have hi2 : f i (b i) ∈ S (color i (a i)) := by rw [heq i]; exact hcolor i (b i)
  have hk1 : f k (a i) ∈ S (color i (a i)) := by rw [hcik, haik]; exact hcolor k (a k)
  have hk2 : f k (b i) ∈ S (color i (a i)) := by
    rw [hcik, hbik, heq k]; exact hcolor k (b k)
  rcases hS _ _ hi1 _ hk2 _ hi2 _ hk1 (hrect i k (a i) (b i)) with h | h
  · exact hab i (hcol i h.1)
  · exact hik (hrow (a i) h.1)

private def dimension (n : ℕ) := n + 1 + (n * (n + 1) * (n + 1) + 1)

private lemma cube_obstruction (n c t : ℕ) (hc : 0 < c)
    (S : Fin n → Set ℕ) (hS : ∀ k, (S k).IsSidon)
    (hcover : (fun x => t + c * x) '' (cube (dimension n) : Set ℕ) ⊆ ⋃ k, S k) : False := by
  let f (i : Fin (n * (n + 1) * (n + 1) + 1)) (j : Fin (n + 1)) :=
    t + c * (3 ^ (n + 1 + (i : ℕ)) + 3 ^ (j : ℕ))
  refine grid_obstruction n f ?_ ?_ ?_ S hS ?_
  · intro j i k h
    have hp : 3 ^ (n + 1 + (i : ℕ)) = 3 ^ (n + 1 + (k : ℕ)) := by
      dsimp [f] at h
      nlinarith
    have he := Nat.pow_right_injective (by omega : 1 < 3) hp
    exact Fin.ext (by omega)
  · intro i j k h
    have hp : 3 ^ (j : ℕ) = 3 ^ (k : ℕ) := by
      dsimp [f] at h
      nlinarith
    exact Fin.ext (Nat.pow_right_injective (by omega : 1 < 3) hp)
  · intro i k j l
    dsimp [f]
    ring
  · intro i j
    apply hcover
    refine ⟨_, ?_, rfl⟩
    exact pair_mem_cube ⟨n + 1 + i, by dsimp [dimension]; omega⟩
      ⟨j, by dsimp [dimension]; omega⟩ (by
        intro h
        have := congrArg Fin.val h
        dsimp at this
        omega)

private def width (n : ℕ) : ℕ := 3 * (n + 1) * (cube (dimension n)).sup id

private def offset : ℕ → ℕ
  | 0 => 3 * (width 0 + 1) + 1
  | n + 1 => 3 * (offset n + width n + width (n + 1) + n + 1) + 1

private lemma offset_large (n : ℕ) : 3 * width n < offset n := by
  cases n <;> simp only [offset] <;> omega

private lemma offset_strict : StrictMono offset := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [offset]
  omega

private lemma separated {i j : ℕ} (h : i < j) :
    3 * (offset i + width i) + i < offset j := by
  have hj := offset_strict.monotone (show i + 1 ≤ j by omega)
  simp only [offset] at hj
  omega

private def sparseSet : Set ℕ :=
  {x | ∃ n, ∃ y ∈ cube (dimension n), x = offset n + 3 * (n + 1) * y}

private lemma block_bounds {n y : ℕ} (hy : y ∈ cube (dimension n)) :
    offset n ≤ offset n + 3 * (n + 1) * y ∧
      offset n + 3 * (n + 1) * y ≤ offset n + width n := by
  constructor
  · omega
  · have h := Finset.le_sup (f := id) hy
    dsimp [width, id] at *
    nlinarith

private lemma sparse_not_sidon : sparseSet ∉ sidonIdeal := by
  rintro ⟨n, S, hS, hcover⟩
  apply cube_obstruction n (3 * (n + 1)) (offset n) (by omega) S hS
  rintro x ⟨y, hy, rfl⟩
  exact hcover ⟨n, y, hy, rfl⟩

private lemma cube_zero (d : ℕ) : 0 ∈ cube d := by
  refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
  · rw [Behrend.mem_box]
    intro i
    simp
  · simp

private lemma sparse_infinite : sparseSet.Infinite := by
  apply (Set.infinite_range_of_injective offset_strict.injective).mono
  rintro x ⟨n, rfl⟩
  exact ⟨n, 0, cube_zero _, by simp⟩

private lemma same_block {i j k a b c : ℕ}
    (ha : offset i ≤ a ∧ a ≤ offset i + width i)
    (hb : offset j ≤ b ∧ b ≤ offset j + width j)
    (hc : offset k ≤ c ∧ c ≤ offset k + width k)
    (heq : a + c = b + b) : i = j := by
  have hij : i ≤ j := by
    by_contra! h
    have hs := separated h
    omega
  by_contra hne
  have hij' : i < j := by omega
  have hkj : k ≤ j := by
    by_contra! h
    have hs := separated h
    omega
  have hc' : c ≤ offset j + width j := by
    rcases hkj.eq_or_lt with h | h
    · simpa [h] using hc.2
    · have hs := separated h
      omega
  have hs := separated hij'
  have hw := offset_large j
  omega

private lemma sparse_free : ThreeAPFree sparseSet := by
  rintro a ⟨i, x, hx, rfl⟩ b ⟨j, y, hy, rfl⟩ c ⟨k, z, hz, rfl⟩ heq
  have hi := same_block (block_bounds hx) (block_bounds hy) (block_bounds hz) heq
  have hk := same_block (block_bounds hz) (block_bounds hy) (block_bounds hx) (by omega)
  subst i
  subst k
  have hxyz : x + z = y + y := by nlinarith
  have hxy := cube_free (dimension j) hx hy hz hxyz
  simp [hxy]

private lemma sparse_vdw : sparseSet ∈ vanDerWaerdenIdeal := by
  refine ⟨3, by omega, ?_⟩
  intro a r hr
  by_contra! h
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [mul_zero, add_zero, mul_one] at h0 h1
  have heq := sparse_free h0 h1 h2 (by omega)
  omega

private lemma sparse_gap {a b N : ℕ} (ha : a ∈ sparseSet) (hb : b ∈ sparseSet)
    (hab : a < b) (hN : offset N ≤ a) : N ≤ b - a := by
  obtain ⟨i, x, hx, rfl⟩ := ha
  obtain ⟨j, y, hy, rfl⟩ := hb
  obtain ⟨ha1, ha2⟩ := block_bounds hx
  obtain ⟨hb1, hb2⟩ := block_bounds hy
  have hNi : N ≤ i := by
    by_contra! h
    have hs := separated h
    omega
  have hij : i ≤ j := by
    by_contra! h
    have hs := separated h
    omega
  rcases hij.eq_or_lt with heq | hlt
  · subst j
    have hxy : x < y := by nlinarith
    have hstep : 3 * (i + 1) * x + 3 * (i + 1) ≤ 3 * (i + 1) * y := by nlinarith
    omega
  · have hs := separated hlt
    omega

private lemma sparse_lacunary : IsGapLacunarySet sparseSet := by
  refine ⟨sparse_infinite, ?_⟩
  rw [Filter.tendsto_atTop_atTop]
  intro N
  refine ⟨offset N, fun n hn => ?_⟩
  apply sparse_gap (Nat.nth_mem_of_infinite sparse_infinite n)
    (Nat.nth_mem_of_infinite sparse_infinite (n + 1))
    (Nat.nth_strictMono sparse_infinite (by omega))
  exact hn.trans ((Nat.nth_strictMono sparse_infinite).id_le n)

private lemma sparse_mod {x : ℕ} (hx : x ∈ sparseSet) : x % 3 = 1 := by
  obtain ⟨n, y, hy, rfl⟩ := hx
  cases n <;> simp [offset, Nat.add_mod, Nat.mul_mod]

private lemma difference_triple {Z : Set ℕ} (hsub : positiveDifferences Z ⊆ sparseSet)
    {a b c : ℕ} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z)
    (hab : a < b) (hbc : b < c) : False := by
  have h1 := sparse_mod (hsub ⟨b, hb, a, ha, hab, rfl⟩)
  have h2 := sparse_mod (hsub ⟨c, hc, b, hb, hbc, rfl⟩)
  have h3 := sparse_mod (hsub ⟨c, hc, a, ha, hab.trans hbc, rfl⟩)
  omega

private lemma sparse_dfin : sparseSet ∈ dFinIdeal := by
  refine ⟨3, ?_⟩
  intro Z hZ hsub
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hZ
  have ha : a ∈ ({a, b, c} : Finset ℕ) := by simp
  have hb : b ∈ ({a, b, c} : Finset ℕ) := by simp
  have hc : c ∈ ({a, b, c} : Finset ℕ) := by simp
  rcases Nat.lt_or_gt_of_ne hab with hab | hba
  · rcases Nat.lt_or_gt_of_ne hbc with hbc | hcb
    · exact difference_triple hsub ha hb hc hab hbc
    · rcases Nat.lt_or_gt_of_ne hac with hac | hca
      · exact difference_triple hsub ha hc hb hac hcb
      · exact difference_triple hsub hc ha hb hca hab
  · rcases Nat.lt_or_gt_of_ne hac with hac | hca
    · exact difference_triple hsub hb ha hc hba hac
    · rcases Nat.lt_or_gt_of_ne hbc with hbc | hcb
      · exact difference_triple hsub hb hc ha hbc hca
      · exact difference_triple hsub hc hb ha hcb hba

/-- **A set in the van der Waerden, lacunary and difference-set ideals outside the Sidon ideal.**
There is a set $A \subseteq \mathbb{N}$ that belongs to the van der Waerden ideal, is contained in
a finite union of gap-lacunary sets (infinite sets whose gaps between consecutive elements tend to
infinity), and belongs to the ideal $D_{\mathrm{fin}}$ of sets avoiding large difference sets, but
is not contained in any finite union of Sidon sets.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Theorem 5 (`integers-2025-A91-thm-5`). -/
public theorem exists_mem_vanDerWaerden_lacunary_dFin_not_mem_sidonIdeal :
    ∃ A : Set ℕ, A ∈ vanDerWaerdenIdeal ∧ A ∈ generatedIdeal IsGapLacunarySet ∧
      A ∈ dFinIdeal ∧ A ∉ sidonIdeal := by
  exact ⟨sparseSet, sparse_vdw, mem_generatedIdeal sparse_lacunary, sparse_dfin, sparse_not_sidon⟩

end

end MetaMathlibExt
