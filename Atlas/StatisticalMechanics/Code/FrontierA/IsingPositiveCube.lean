/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusBlockQuantitative
import Code.FrontierA.IsingMessagerMiracleInfinite

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Lattice

variable {d m k : Nat}


def isingPositiveCubeEmbedding (d m : Nat) :
    (Fin d -> Fin m) ↪ Site d where
  toFun a i := (a i : Nat)
  inj' := by
    intro a b h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    change (((a i).val : Nat) : Int) = ((b i).val : Int) at hi
    exact_mod_cast hi


def isingPositiveCube (d m : Nat) : Finset (Site d) :=
  Finset.univ.map (isingPositiveCubeEmbedding d m)

theorem isingPositiveCube_card (d m : Nat) :
    (isingPositiveCube d m).card = m ^ d := by
  simp [isingPositiveCube, Fintype.card_fun]

theorem isingPositiveCube_subset_box (d m : Nat) :
    (isingPositiveCube d m : Set (Site d)) ⊆ box d m := by
  intro x hx i
  have hx' : x ∈ isingPositiveCube d m := hx
  rw [isingPositiveCube, Finset.mem_map] at hx'
  obtain ⟨a, _, rfl⟩ := hx'
  change (a i).val <= m
  exact (a i).isLt.le

theorem isingPositiveCube_nonempty (d m : Nat) (hm : 1 <= m) :
    (isingPositiveCube d m).Nonempty := by
  apply Finset.card_pos.mp
  rw [isingPositiveCube_card]
  positivity

theorem isingPositiveCube_difference_l1_le
    {a b : Site d} (ha : a ∈ isingPositiveCube d m)
    (hb : b ∈ isingPositiveCube d m) :
    (∑ i, (b i - a i).natAbs) <= d * m := by
  rw [isingPositiveCube, Finset.mem_map] at ha hb
  obtain ⟨u, _, rfl⟩ := ha
  obtain ⟨v, _, rfl⟩ := hb
  calc
    (∑ i, (((v i : Nat) : Int) - ((u i : Nat) : Int)).natAbs) <=
        ∑ _i : Fin d, m := by
      apply Finset.sum_le_sum
      intro i _
      have hu : (u i).val < m := (u i).isLt
      have hv : (v i).val < m := (v i).isLt
      omega
    _ = d * m := by simp [mul_comm]

theorem isingPositiveCube_difference_mem_box
    {a b : Site d} (ha : a ∈ isingPositiveCube d m)
    (hb : b ∈ isingPositiveCube d m) : b - a ∈ box d m := by
  rw [isingPositiveCube, Finset.mem_map] at ha hb
  obtain ⟨u, _, rfl⟩ := ha
  obtain ⟨v, _, rfl⟩ := hb
  intro i
  have hu : (u i).val < m := (u i).isLt
  have hv : (v i).val < m := (v i).isLt
  have huEq : isingPositiveCubeEmbedding d m u i = ((u i).val : Int) := rfl
  have hvEq : isingPositiveCubeEmbedding d m v i = ((v i).val : Int) := rfl
  rw [Pi.sub_apply, huEq, hvEq]
  omega


noncomputable def isingTorusPositiveCube (d m k : Nat) :
    Finset (IsingDyadicTorus d k) :=
  isingTorusImageFinset k (isingPositiveCube d m)

theorem isingTorusPositiveCube_card
    (hside : 2 * m < isingDyadicSide k) :
    (isingTorusPositiveCube d m k).card = m ^ d := by
  unfold isingTorusPositiveCube isingTorusImageFinset
  rw [Finset.card_image_iff.mpr]
  · exact isingPositiveCube_card d m
  · intro x hx y hy hxy
    exact isingSiteToDyadicTorus_injectiveOn_finset
      (isingPositiveCube d m) (isingPositiveCube_subset_box d m)
        hside hx hy hxy

theorem isingTorusPositiveCube_nonempty
    (hm : 1 <= m) : (isingTorusPositiveCube d m k).Nonempty := by
  unfold isingTorusPositiveCube isingTorusImageFinset
  exact (isingPositiveCube_nonempty d m hm).image _

theorem finiteTorusBlockDifferenceAverage_image
    {Gamma : Type*} [Fintype Gamma] [DecidableEq Gamma] [AddCommGroup Gamma]
    (G : Gamma -> Real) (S : Finset (Site d)) (f : Site d -> Gamma)
    (hf : Set.InjOn f (S : Set (Site d))) :
    finiteTorusBlockDifferenceAverage G (S.image f) =
      (1 / (S.card : Real) ^ 2) *
        ∑ a ∈ S, ∑ b ∈ S, G (f b - f a) := by
  unfold finiteTorusBlockDifferenceAverage
  rw [Finset.card_image_iff.mpr]
  · congr 1
    rw [Finset.sum_image hf]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image hf]
  · intro a ha b hb hab
    exact hf ha hb hab


theorem exists_isingTorusPositiveCube_green_le_power
    {d : Nat} (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ m : Nat, 2 <= m ->
      ∀ᶠ k : Nat in Filter.atTop,
        finiteTorusBlockDifferenceAverage
            (finiteTorusZeroModeGreen
              (isingTorusCharacterDispersion (d := d) (k := k)))
            (isingTorusPositiveCube d m k) <=
          C / (m : Real) ^ (d - 2) := by
  obtain ⟨C0, hC0, hbound⟩ :=
    exists_finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power hd
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro m hm
  have hmpos : 0 < m := by omega
  have hside : ∀ᶠ k : Nat in Filter.atTop,
      2 * m < isingDyadicSide k := by
    have htendsto : Filter.Tendsto isingDyadicSide
        Filter.atTop Filter.atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    exact htendsto.eventually_gt_atTop (2 * m)
  filter_upwards [hside] with k hk
  let M := isingDyadicSide k / m
  have hM : 1 <= M := by
    have hmside : m <= isingDyadicSide k := by omega
    change 1 <= isingDyadicSide k / m
    exact (Nat.one_le_div_iff hmpos).2 hmside
  have hMhalf : M <= isingDyadicSide k / 2 := by
    dsimp [M]
    exact Nat.div_le_div_left hm (by omega)
  have hcard : (isingTorusPositiveCube d m k).card = m ^ d :=
    isingTorusPositiveCube_card hk
  have hraw := hbound k (isingTorusPositiveCube d m k)
    (isingTorusPositiveCube_nonempty (d := d) (by omega)) M hM hMhalf
  rw [hcard] at hraw
  push_cast at hraw
  have hLpos : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hmR : (0 : Real) < m := by exact_mod_cast hmpos
  have hMmul : M * m <= isingDyadicSide k := by
    dsimp [M]
    exact Nat.div_mul_le_self _ _
  have hratio : (M : Real) / isingDyadicSide k <= 1 / (m : Real) := by
    rw [div_le_div_iff₀ hLpos hmR]
    norm_num
    exact_mod_cast hMmul
  have hLupperNat : isingDyadicSide k < (M + 1) * m := by
    dsimp [M]
    exact (Nat.div_lt_iff_lt_mul hmpos).mp (Nat.lt_succ_self _)
  have hLupper : (isingDyadicSide k : Real) <= ((M + 1) : Real) * m := by
    exact_mod_cast hLupperNat.le
  have hpowm : (m : Real) ^ d =
      (m : Real) ^ (d - 2) * (m : Real) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hlow : C0 * ((M : Real) / isingDyadicSide k) ^ (d - 2) <=
      C0 / (m : Real) ^ (d - 2) := by
    calc
      C0 * ((M : Real) / isingDyadicSide k) ^ (d - 2) <=
          C0 * (1 / (m : Real)) ^ (d - 2) := by gcongr
      _ = C0 / (m : Real) ^ (d - 2) := by rw [one_div, inv_pow]; ring
  have hhigh :
      (isingDyadicSide k : Real) ^ 2 /
          (16 * (((M + 1 : Nat) : Real)) ^ 2 * (m : Real) ^ d) <=
        1 / (m : Real) ^ (d - 2) := by
    rw [hpowm]
    have hsq : (isingDyadicSide k : Real) ^ 2 <=
        (((M + 1 : Nat) : Real) ^ 2) * (m : Real) ^ 2 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ hLpos.le
      · simpa only [Nat.cast_add, Nat.cast_one] using hLupper
    have hpowpos : (0 : Real) < (m : Real) ^ (d - 2) := pow_pos hmR _
    calc
      (isingDyadicSide k : Real) ^ 2 /
            (16 * (((M + 1 : Nat) : Real)) ^ 2 *
              ((m : Real) ^ (d - 2) * (m : Real) ^ 2)) <=
          ((((M + 1 : Nat) : Real)) ^ 2 * (m : Real) ^ 2) /
            (16 * (((M + 1 : Nat) : Real)) ^ 2 *
              ((m : Real) ^ (d - 2) * (m : Real) ^ 2)) := by
        exact div_le_div_of_nonneg_right hsq (by positivity)
      _ = 1 / (16 * (m : Real) ^ (d - 2)) := by
        field_simp [hpowpos.ne', hmR.ne']
      _ <= 1 / (m : Real) ^ (d - 2) := by
        rw [div_le_div_iff₀ (by positivity) hpowpos]
        nlinarith
  calc
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusPositiveCube d m k) <=
        C0 * ((M : Real) / isingDyadicSide k) ^ (d - 2) +
          (isingDyadicSide k : Real) ^ 2 /
            (16 * (((M + 1 : Nat) : Real)) ^ 2 * (m : Real) ^ d) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hraw
    _ <= C0 / (m : Real) ^ (d - 2) +
        1 / (m : Real) ^ (d - 2) := add_le_add hlow hhigh
    _ = (C0 + 1) / (m : Real) ^ (d - 2) := by ring

end StatMech.FrontierA
