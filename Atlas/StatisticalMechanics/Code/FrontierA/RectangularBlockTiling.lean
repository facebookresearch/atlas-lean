/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionThermodynamic

namespace StatMech.FrontierA


def SeparatelySubadditive (F : Nat -> Nat -> Real) : Prop :=
  HorizontallySubadditive F /\ VerticallySubadditive F


def HasRectangularAreaBound (F : Nat -> Nat -> Real) : Prop :=
  exists L : Real, 0 <= L /\ forall m n : Nat,
    F m n <= L * (m : Real) * (n : Real)



theorem hasRectangularBlockGluing_of_separatelySubadditive_areaBound
    {F : Nat -> Nat -> Real} (hF : forall m n, 0 <= F m n)
    (hsub : SeparatelySubadditive F)
    (harea : HasRectangularAreaBound F) :
    HasRectangularBlockGluing F := by
  intro m k hm hk
  obtain ⟨L, hL, harea⟩ := harea
  refine ⟨L * (m + k + m * k), by positivity, ?_⟩
  intro n hn
  let q := n / m
  let r := n % m
  let s := n / k
  let t := n % k
  have hqm : q * m <= n := by
    simpa [q] using Nat.div_mul_le_self n m
  have hsk : s * k <= n := by
    simpa [s] using Nat.div_mul_le_self n k
  have hr : r < m := by
    simpa [r] using Nat.mod_lt n hm
  have ht : t < k := by
    simpa [t] using Nat.mod_lt n hk
  have hn_qr : q * m + r = n := by
    rw [Nat.mul_comm]
    simpa [q, r] using Nat.div_add_mod n m
  have hn_st : s * k + t = n := by
    rw [Nat.mul_comm]
    simpa [s, t] using Nat.div_add_mod n k
  have hhorizontal : F n n <= (q : Real) * F m n + F r n := by
    have h := (hsub.1 n).apply_mul_add_le q m r
    rwa [hn_qr] at h
  have hvertical_m : F m n <= (s : Real) * F m k + F m t := by
    have h := (hsub.2 m).apply_mul_add_le s k t
    rwa [hn_st] at h
  have hvertical_r : F r n <= (s : Real) * F r k + F r t := by
    have h := (hsub.2 r).apply_mul_add_le s k t
    rwa [hn_st] at h
  have htile : F n n <=
      (q : Real) * (s : Real) * F m k +
        (q : Real) * F m t + (s : Real) * F r k + F r t := by
    calc
      F n n <= (q : Real) * F m n + F r n := hhorizontal
      _ <= (q : Real) * ((s : Real) * F m k + F m t) +
          ((s : Real) * F r k + F r t) := by
        gcongr
      _ = _ := by ring
  have hqm_real : (q : Real) * (m : Real) <= n := by
    exact_mod_cast hqm
  have hsk_real : (s : Real) * (k : Real) <= n := by
    exact_mod_cast hsk
  have hr_real : (r : Real) <= m := by
    exact_mod_cast hr.le
  have ht_real : (t : Real) <= k := by
    exact_mod_cast ht.le
  have hqmt : (q : Real) * (m : Real) * (t : Real) <=
      (n : Real) * (k : Real) := by
    exact mul_le_mul hqm_real ht_real (Nat.cast_nonneg t) (Nat.cast_nonneg n)
  have hsrk : (s : Real) * (r : Real) * (k : Real) <=
      (n : Real) * (m : Real) := by
    calc
      (s : Real) * (r : Real) * (k : Real) =
          (r : Real) * ((s : Real) * (k : Real)) := by ring
      _ <= (m : Real) * (n : Real) :=
        mul_le_mul hr_real hsk_real (by positivity) (by positivity)
      _ = (n : Real) * (m : Real) := by ring
  have hrt : (r : Real) * (t : Real) <= (m : Real) * (k : Real) :=
    mul_le_mul hr_real ht_real (by positivity) (by positivity)
  have hrem_q : (q : Real) * F m t <=
      L * (n : Real) * (k : Real) := by
    calc
      (q : Real) * F m t <=
          (q : Real) * (L * (m : Real) * (t : Real)) :=
        mul_le_mul_of_nonneg_left (harea m t) (Nat.cast_nonneg q)
      _ = L * ((q : Real) * (m : Real) * (t : Real)) := by ring
      _ <= L * ((n : Real) * (k : Real)) :=
        mul_le_mul_of_nonneg_left hqmt hL
      _ = L * (n : Real) * (k : Real) := by ring
  have hrem_s : (s : Real) * F r k <=
      L * (n : Real) * (m : Real) := by
    calc
      (s : Real) * F r k <=
          (s : Real) * (L * (r : Real) * (k : Real)) :=
        mul_le_mul_of_nonneg_left (harea r k) (Nat.cast_nonneg s)
      _ = L * ((s : Real) * (r : Real) * (k : Real)) := by ring
      _ <= L * ((n : Real) * (m : Real)) :=
        mul_le_mul_of_nonneg_left hsrk hL
      _ = L * (n : Real) * (m : Real) := by ring
  have hrem_rt : F r t <= L * (m : Real) * (k : Real) := by
    calc
      F r t <= L * (r : Real) * (t : Real) := harea r t
      _ = L * ((r : Real) * (t : Real)) := by ring
      _ <= L * ((m : Real) * (k : Real)) :=
        mul_le_mul_of_nonneg_left hrt hL
      _ = L * (m : Real) * (k : Real) := by ring
  have hmk : 0 < (m : Real) * (k : Real) := by positivity
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hn2 : 0 < (n : Real) * (n : Real) := mul_pos hnreal hnreal
  have hblock_count : (q : Real) * (s : Real) <=
      ((n : Real) * (n : Real)) / ((m : Real) * (k : Real)) := by
    rw [le_div_iff₀ hmk]
    calc
      (q : Real) * (s : Real) * ((m : Real) * (k : Real)) =
          ((q : Real) * (m : Real)) * ((s : Real) * (k : Real)) := by ring
      _ <= (n : Real) * (n : Real) :=
        mul_le_mul hqm_real hsk_real (by positivity) (by positivity)
  have hmain : (q : Real) * (s : Real) * F m k <=
      (((n : Real) * (n : Real)) / ((m : Real) * (k : Real))) * F m k :=
    mul_le_mul_of_nonneg_right hblock_count (hF m k)
  have hlast : L * (m : Real) * (k : Real) <=
      L * (m : Real) * (k : Real) * (n : Real) := by
    have hn_one : (1 : Real) <= n := by exact_mod_cast hn
    exact le_mul_of_one_le_right (by positivity) hn_one
  have htotal : F n n <=
      (((n : Real) * (n : Real)) / ((m : Real) * (k : Real))) * F m k +
        (L * ((m : Real) + (k : Real) + (m : Real) * (k : Real))) * n := by
    calc
      F n n <= (q : Real) * (s : Real) * F m k +
          (q : Real) * F m t + (s : Real) * F r k + F r t := htile
      _ <= (((n : Real) * (n : Real)) / ((m : Real) * (k : Real))) * F m k +
          (L * (n : Real) * (k : Real) + L * (n : Real) * (m : Real) +
            L * (m : Real) * (k : Real)) := by linarith
      _ <= (((n : Real) * (n : Real)) / ((m : Real) * (k : Real))) * F m k +
          (L * (n : Real) * (k : Real) + L * (n : Real) * (m : Real) +
            L * (m : Real) * (k : Real) * (n : Real)) := by linarith
      _ = _ := by ring
  rw [rectangularSurfaceDensity, rectangularSurfaceDensity]
  apply (div_le_iff₀ hn2).2
  calc
    F n n <= (((n : Real) * (n : Real)) / ((m : Real) * (k : Real))) * F m k +
        (L * ((m : Real) + (k : Real) + (m : Real) * (k : Real))) * n := htotal
    _ = (F m k / ((m : Real) * (k : Real)) +
          (L * ((m : Real) + (k : Real) + (m : Real) * (k : Real))) / n) *
          ((n : Real) * (n : Real)) := by
      field_simp

end StatMech.FrontierA
