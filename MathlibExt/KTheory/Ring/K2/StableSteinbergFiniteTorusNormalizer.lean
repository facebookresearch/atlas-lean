/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylTorusTransport

/-! # Finite Weyl normalization of the finite torus

For `[Field F]` and `n : ℕ`, every bounded finite-rank Weyl generator normalizes
`StableSteinberg.finiteTorusSubgroup n`, hence the whole `finiteWeylSubgroup n`
normalizes it. A direct adjacent-simple-Weyl corollary for `weyl m (m+1) _ 1`
under `m + 1 < n` is exposed in the orientation needed by Steinberg Lemma 24.

Proof route: reuse the accepted noncircular `exists_torus_through_weightedWeylProd`
on a singleton inverse-Weyl word to transport each torus generator, absorb its
cocycle defect with `torusCocycleSubgroup_le_finiteTorusSubgroup` (with `2 ≤ n`
from two bounded distinct endpoints via `omega`), then subgroup closure and
normalizer induction. Inverse conjugation uses `weyl_neg_eq_inv`.

Orientation is always `w * t * w⁻¹` (conjugator on the left).

Nonclaims: no quotient, Borel or two-cell subgroup, Bruhat decomposition,
double-coset argument, kernel inclusion, Matsumoto theorem, defect-free torus
equality (`c = 1` is false in general), or normality in all of
`StableSteinberg`. The cocycle defect is only absorbed into the finite torus,
never claimed trivial.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- Bounded ordered label from distinct `ℕ` endpoints below `n`. -/
private def swapLabelOfBound {n : ℕ} {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : SwapLabel n :=
  ⟨(⟨i, hi⟩, ⟨j, hj⟩), fun h => hij (Fin.ext_iff.mp h)⟩

/-- Bounded `weyl` agrees with its swap-label form. -/
private theorem weyl_ofBound_eq {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (u : Fˣ) :
    StableSteinberg.weyl (R := F) i j hij u =
      weylOfSwapLabel (swapLabelOfBound hi hj hij) u := by
  unfold weylOfSwapLabel swapLabelOfBound
  rfl

/-- One bounded Weyl generator conjugates one bounded torus generator back into
the finite torus, via singleton inverse-word transport. -/
private theorem weyl_conj_torus_generator_mem {n i j p q : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (u : Fˣ)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q) (v : Fˣ) :
    StableSteinberg.weyl (R := F) i j hij u *
        StableSteinberg.torus (R := F) p q hpq v *
        (StableSteinberg.weyl (R := F) i j hij u)⁻¹ ∈
      StableSteinberg.finiteTorusSubgroup (R := F) n := by
  let b : SwapLabel n := swapLabelOfBound hi hj hij
  let a : SwapLabel n := swapLabelOfBound hp hq hpq
  have hW : StableSteinberg.weyl (R := F) i j hij u = weylOfSwapLabel b u :=
    weyl_ofBound_eq hi hj hij u
  have hProd : weightedWeylProd [(b, -u)] = weylOfSwapLabel b (-u) := by
    simp [weightedWeylProd]
  have hInv : weylOfSwapLabel b (-u) = (weylOfSwapLabel b u)⁻¹ := by
    unfold weylOfSwapLabel
    exact StableSteinberg.weyl_neg_eq_inv _ _ _ _
  have hWinv : weightedWeylProd [(b, -u)] =
      (StableSteinberg.weyl (R := F) i j hij u)⁻¹ := by
    rw [hProd, hInv, ← hW]
  have hn2 : 2 ≤ n := by omega
  obtain ⟨c, a', r', hc, hTmem, hEq⟩ :=
    exists_torus_through_weightedWeylProd a v [(b, -u)]
  have hT : StableSteinberg.torus (R := F) p q hpq v =
      StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
        (fun h => a.property (Fin.ext h)) v := by
    unfold a swapLabelOfBound
    rfl
  have hEq' : StableSteinberg.torus (R := F) p q hpq v *
        (StableSteinberg.weyl (R := F) i j hij u)⁻¹ =
        c * ((StableSteinberg.weyl (R := F) i j hij u)⁻¹ *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
    have h := hEq
    rw [← hT, hWinv] at h
    exact h
  have hcen : c ∈ Subgroup.center (StableSteinberg F) :=
    StableSteinberg.torusCocycleSubgroup_le_center hc
  have hcomm : StableSteinberg.weyl (R := F) i j hij u * c =
      c * StableSteinberg.weyl (R := F) i j hij u :=
    Subgroup.mem_center_iff.mp hcen _
  have hcFin : c ∈ StableSteinberg.finiteTorusSubgroup (R := F) n :=
    StableSteinberg.torusCocycleSubgroup_le_finiteTorusSubgroup hn2 hc
  have hFinal : StableSteinberg.weyl (R := F) i j hij u *
        StableSteinberg.torus (R := F) p q hpq v *
        (StableSteinberg.weyl (R := F) i j hij u)⁻¹ = c *
        StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r' := by
    calc StableSteinberg.weyl (R := F) i j hij u *
            StableSteinberg.torus (R := F) p q hpq v *
            (StableSteinberg.weyl (R := F) i j hij u)⁻¹
        = StableSteinberg.weyl (R := F) i j hij u *
            (StableSteinberg.torus (R := F) p q hpq v *
              (StableSteinberg.weyl (R := F) i j hij u)⁻¹) := by
          rw [mul_assoc]
      _ = StableSteinberg.weyl (R := F) i j hij u *
            (c * ((StableSteinberg.weyl (R := F) i j hij u)⁻¹ *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r')) := by
          rw [hEq']
      _ = (StableSteinberg.weyl (R := F) i j hij u * c) *
            ((StableSteinberg.weyl (R := F) i j hij u)⁻¹ *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r') := by
          rw [← mul_assoc]
      _ = (c * StableSteinberg.weyl (R := F) i j hij u) *
            ((StableSteinberg.weyl (R := F) i j hij u)⁻¹ *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r') := by
          rw [hcomm]
      _ = c * (StableSteinberg.weyl (R := F) i j hij u *
            ((StableSteinberg.weyl (R := F) i j hij u)⁻¹ *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r')) := by
          rw [mul_assoc]
      _ = c * ((StableSteinberg.weyl (R := F) i j hij u *
            (StableSteinberg.weyl (R := F) i j hij u)⁻¹) *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r') := by
          rw [← mul_assoc (StableSteinberg.weyl (R := F) i j hij u) _ _]
      _ = c * StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r' := by
          rw [mul_inv_cancel, one_mul]
  rw [hFinal]
  exact Subgroup.mul_mem _ hcFin hTmem

/-- A bounded Weyl generator conjugates a finite-torus element back into the
finite torus.

Hypotheses: `[Field F]`, bounded distinct Weyl endpoints `i ≠ j` with
`i < n`, `j < n`, arbitrary `u : Fˣ`, and `t ∈ finiteTorusSubgroup n`.
Orientation: `w * t * w⁻¹` with `w = weyl i j hij u`.

Nonclaims: no quotient, Borel, Bruhat, double-coset, kernel inclusion,
Matsumoto, defect-free equality, or normality in all of `StableSteinberg`. -/
public theorem weyl_conj_finiteTorus_mem {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (u : Fˣ) {t : StableSteinberg F}
    (ht : t ∈ StableSteinberg.finiteTorusSubgroup (R := F) n) :
    StableSteinberg.weyl (R := F) i j hij u * t *
      (StableSteinberg.weyl (R := F) i j hij u)⁻¹ ∈
    StableSteinberg.finiteTorusSubgroup (R := F) n := by
  let w := StableSteinberg.weyl (R := F) i j hij u
  induction ht using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨p, q, hpq, v, rfl, hp, hq⟩ := hy
    exact weyl_conj_torus_generator_mem hi hj hij u hp hq hpq v
  | one => simp
  | mul x y _ _ ihx ihy =>
    have h_eq : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by
      simp [mul_assoc]
    rw [h_eq]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have h_eq : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by
      simp [mul_assoc]
    rw [h_eq]
    exact Subgroup.inv_mem _ ih

/-- A bounded Weyl generator lies in the normalizer of the finite torus. -/
private theorem weyl_generator_mem_normalizer {n i j : ℕ} (hi : i < n)
    (hj : j < n) (hij : i ≠ j) (u : Fˣ) :
    StableSteinberg.weyl (R := F) i j hij u ∈
      Subgroup.normalizer (StableSteinberg.finiteTorusSubgroup (R := F) n) := by
  let w := StableSteinberg.weyl (R := F) i j hij u
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact weyl_conj_finiteTorus_mem hi hj hij u hg
  · intro hg
    have hInvMem : StableSteinberg.weyl (R := F) i j hij (-u) *
          (w * g * w⁻¹) *
          (StableSteinberg.weyl (R := F) i j hij (-u))⁻¹ ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n :=
      weyl_conj_finiteTorus_mem hi hj hij (-u) hg
    have hWInv : StableSteinberg.weyl (R := F) i j hij (-u) = w⁻¹ :=
      StableSteinberg.weyl_neg_eq_inv _ _ _ _
    have hEq : StableSteinberg.weyl (R := F) i j hij (-u) * (w * g * w⁻¹) *
          (StableSteinberg.weyl (R := F) i j hij (-u))⁻¹ = g := by
      rw [hWInv, inv_inv]
      simp [mul_assoc]
    rw [hEq] at hInvMem
    exact hInvMem

/-- The whole bounded finite Weyl subgroup normalizes the finite torus.

Hypotheses: `[Field F]`, no rank hypothesis (ranks `0` and `1` are bottom).
Orientation: `w * t * w⁻¹` for `w ∈ finiteWeylSubgroup n`.

Nonclaims: no quotient, Borel, Bruhat, double-coset, kernel inclusion,
Matsumoto, defect-free equality, or normality in all of `StableSteinberg`. -/
public theorem finiteWeylSubgroup_le_normalizer_finiteTorusSubgroup (n : ℕ) :
    StableSteinberg.finiteWeylSubgroup (R := F) n ≤
      Subgroup.normalizer (StableSteinberg.finiteTorusSubgroup (R := F) n) := by
  rw [StableSteinberg.finiteWeylSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, u, rfl, hi, hj⟩ := hg
  exact weyl_generator_mem_normalizer hi hj hij u

/-- Adjacent simple Weyl generator normalizes the finite torus.

Hypotheses: `[Field F]`, `hm : m + 1 < n`, unit `1`. Orientation:
`weyl m (m+1) _ 1 * t * (weyl m (m+1) _ 1)⁻¹` for Lemma 24.

Nonclaims: no quotient, Borel, Bruhat, double-coset, kernel inclusion,
Matsumoto, defect-free equality, or normality in all of `StableSteinberg`. -/
public theorem simpleWeyl_mem_normalizer_finiteTorus {n m : ℕ} (hm : m + 1 < n) :
    StableSteinberg.weyl (R := F) m (m + 1)
        (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) ∈
      Subgroup.normalizer (StableSteinberg.finiteTorusSubgroup (R := F) n) := by
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hwmem := StableSteinberg.weyl_mem_finiteWeylSubgroup (R := F) hm_n hm
    (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)
  exact finiteWeylSubgroup_le_normalizer_finiteTorusSubgroup (F := F) n hwmem

end AlgebraicKTheory

end
