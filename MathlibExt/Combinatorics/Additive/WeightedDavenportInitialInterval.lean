/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Combinatorics.Additive.WeightedDavenportInterval
import all MathlibExt.Combinatorics.Additive.WeightedDavenportInterval

/-!
# The weighted Davenport constant for initial intervals

A sequence of ones gives the lower bound. For the upper bound, every entry of a
zero-sum-free sequence adds at least `r` new sums when coefficients range from zero to `r`.

## References

* Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
  Constants*, INTEGERS 26 (2026), Article A89, pp. 1–14, Corollary 1, first part (p. 7).
  The sequence of ones also appears in the proof of Theorem 5.
* Sukumar Das Adhikari, Chantal David, and Jorge Jiménez Urroz,
  *Generalizations of Some Zero-sum Theorems*, INTEGERS 8 (2008), Article A52, pp. 1–11,
  Theorem 8(i), one of the original proofs credited in Corollary 1.
* Xingwu Xia and Zhigang Li, *Some Davenport Constants with Weights and Adhikari & Rath’s
  Conjecture*, Ars Combinatoria 88 (2008), pp. 83–95, Theorem 3(i), the independent original proof.
* Sukumar Das Adhikari and Purusottam Rath, *Davenport Constant with Weights and Some Related
  Questions*, INTEGERS 6 (2006), Article A30, pp. 1–6, Theorem 2(i), the earlier prime-modulus
  case whose argument Adhikari, David, and Jiménez Urroz extend.
-/

namespace MetaMathlibExt

namespace weightedDavenportInterval

variable {ι G : Type*} [DecidableEq ι] [Fintype ι] [AddCommGroup G] [DecidableEq G]

/-- Sums using the indices in `I` with coefficients between `0` and `r`. -/
private def boundedSums (x : ι → G) (I : Finset ι) (r : ℕ) : Finset G :=
  Finset.univ.image fun a : ι → Fin (r + 1) => ∑ j ∈ I, (a j : ℕ) • x j

/-- Add to any element of `S` up to `t` copies of `x`. -/
private def addCopies (S : Finset G) (x : G) (t : ℕ) : Finset G :=
  ((Finset.range (t + 1)) ×ˢ S).image fun p => p.1 • x + p.2

private theorem mem_addCopies {S : Finset G} {x y : G} {t : ℕ} :
    y ∈ addCopies S x t ↔ ∃ u ≤ t, ∃ z ∈ S, u • x + z = y := by
  simp only [addCopies, Finset.mem_image, Prod.exists, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨u, z, ⟨hu, hz⟩, h⟩
    exact ⟨u, hu, z, hz, h⟩
  · rintro ⟨u, hu, z, hz, h⟩
    exact ⟨u, z, ⟨hu, hz⟩, h⟩

-- The translate of the previous set, together with zero, fits in the next set.
private theorem card_addCopies_ge {S : Finset G} (h0 : 0 ∈ S) {x : G} {t : ℕ}
    (hfree : ∀ u, 0 < u → u ≤ t → ∀ z ∈ S, u • x + z ≠ 0) :
    S.card + t ≤ (addCopies S x t).card := by
  induction t with
  | zero =>
    apply Finset.card_le_card
    intro y hy
    exact mem_addCopies.mpr ⟨0, le_rfl, y, hy, by simp⟩
  | succ t ih =>
    let f (z : G) := x + z
    have hf : Function.Injective f := fun _ _ h => add_left_cancel h
    let T := (addCopies S x t).image f
    have hT : 0 ∉ T := by
      intro h
      obtain ⟨y, hy, hf0⟩ := Finset.mem_image.mp h
      obtain ⟨u, hu, z, hz, rfl⟩ := mem_addCopies.mp hy
      apply hfree (u + 1) (by omega) (by omega) z hz
      simpa [f, add_smul, add_assoc, add_left_comm, add_comm] using hf0
    have hsub : insert 0 T ⊆ addCopies S x (t + 1) := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact mem_addCopies.mpr ⟨0, Nat.zero_le _, 0, h0, by simp⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨u, hu, z, hz, rfl⟩ := mem_addCopies.mp hv
        exact mem_addCopies.mpr ⟨u + 1, by omega, z, hz,
          by simp [f, add_smul, add_left_comm, add_comm]⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hT, Finset.card_image_of_injective _ hf] at hcard
    have hl := ih fun u hu hut => hfree u hu (hut.trans (Nat.le_succ _))
    omega

private theorem card_boundedSums_ge (x : ι → G) (r : ℕ)
    (hne : ∀ (I : Finset ι) (a : ι → Fin (r + 1)) (i : ι), i ∈ I →
      0 < (a i : ℕ) → (∑ j ∈ I, (a j : ℕ) • x j) ≠ 0) (I : Finset ι) :
    r * I.card + 1 ≤ (boundedSums x I r).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [boundedSums]
  | @insert i I hi ih =>
    let S := boundedSums x I r
    have h0 : 0 ∈ S := Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, by simp⟩
    have extend (u : ℕ) (hu : u ≤ r) (y : G) (hy : y ∈ S) :
        ∃ a : ι → Fin (r + 1), (a i : ℕ) = u ∧
          (∑ j ∈ insert i I, (a j : ℕ) • x j) = u • x i + y := by
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
      let a := Function.update b i (⟨u, Nat.lt_succ_of_le hu⟩ : Fin (r + 1))
      have hai : (a i : ℕ) = u := by simp [a]
      refine ⟨a, hai, ?_⟩
      rw [Finset.sum_insert hi, hai]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by
        have hji : j ≠ i := fun e => hi (e ▸ hj)
        simp [a, hji]
    have hgrow := card_addCopies_ge (x := x i) (t := r) h0 (by
      intro u hup hu y hy
      obtain ⟨a, hai, hsum⟩ := extend u hu y hy
      rw [← hsum]
      exact hne _ a i (Finset.mem_insert_self _ _) (hai.symm ▸ hup))
    have hsub : addCopies S (x i) r ⊆ boundedSums x (insert i I) r := by
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := mem_addCopies.mp hy
      obtain ⟨a, -, ha⟩ := extend u hu z hz
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
    calc
      r * (insert i I).card + 1 = (r * I.card + 1) + r := by
        rw [Finset.card_insert_of_notMem hi, Nat.mul_succ]
        omega
      _ ≤ S.card + r := Nat.add_le_add_right ih r
      _ ≤ (boundedSums x (insert i I) r).card := hgrow.trans (Finset.card_le_card hsub)

omit [DecidableEq G] in
private theorem sum_ne_zero_of_pos {s : List G} {r : ℕ}
    (hfree : IsWeightedZeroSumFree (Finset.Icc 1 r) s)
    (I : Finset (Fin s.length)) (a : Fin s.length → Fin (r + 1))
    (i : Fin s.length) (hi : i ∈ I) (ha : 0 < (a i : ℕ)) :
    (∑ j ∈ I, (a j : ℕ) • s.get j) ≠ 0 := by
  let J := I.filter fun j => 0 < (a j : ℕ)
  have hJ : J.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩⟩
  have hw (j) (hj : j ∈ J) : (a j : ℕ) ∈ Finset.Icc 1 r :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hj).2, Nat.le_of_lt_succ (a j).isLt⟩
  have hsum : (∑ j ∈ J, (a j : ℕ) • s.get j) = ∑ j ∈ I, (a j : ℕ) • s.get j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hnot
    have hzero : (a j : ℕ) = 0 := by
      by_contra! h
      exact hnot (Finset.mem_filter.mpr ⟨hj, Nat.pos_of_ne_zero h⟩)
    simp [hzero]
  rw [← hsum]
  exact hfree J hJ (fun j => (a j : ℕ)) hw

end weightedDavenportInterval

open weightedDavenportInterval weightedDavenport_zmod_Icc_of_dvd in
/-- **Weighted Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ for the weights $\{1, \dots, r\}$.**
Let $n$ and $r$ be natural numbers with $1 < r < n$ and let $A = \{1, \dots, r\}$. Then the
$A$-weighted Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ is
$D_A(\mathbb{Z}/n\mathbb{Z}) = \lceil n/r \rceil$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 1, first part (`integers-2026-A89-cor-1`). -/
public theorem weightedDavenport_zmod_Icc (n r : ℕ) (hr : 1 < r) (hrn : r < n) :
    weightedDavenport (Finset.Icc 1 r) (ZMod n) = ((n ⌈/⌉ r : ℕ) : ℕ∞) := by
  classical
  have hrpos : 0 < r := by omega
  have hn : NeZero n := ⟨by omega⟩
  let q := n ⌈/⌉ r
  have hnq : n ≤ r * q := (gc_mul_ceilDiv hrpos).le_u_l _
  have hq : 0 < q := by
    by_contra h
    have hzero : q = 0 := by omega
    rw [hzero, Nat.mul_zero] at hnq
    omega
  apply le_antisymm
  · apply weightedDavenport_le
    intro s hs hfree
    have h := card_boundedSums_ge s.get r (sum_ne_zero_of_pos hfree) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at h
    have hcard := (boundedSums s.get Finset.univ r).card_le_univ
    rw [ZMod.card] at hcard
    change s.length = q at hs
    have hmass : r * q = r * s.length := congrArg (r * ·) hs.symm
    omega
  · have hlt : (q - 1) * r < n := by
      rw [Nat.mul_comm]
      exact (gc_mul_ceilDiv hrpos).lt_iff_lt.mp (by change q - 1 < q; omega)
    have h := Order.add_one_le_of_lt (lt_weightedDavenport (replicate_one_free hlt))
    simpa only [List.length_replicate, ← Nat.cast_succ, Nat.succ_eq_add_one,
      Nat.sub_add_cancel hq] using h

end MetaMathlibExt
