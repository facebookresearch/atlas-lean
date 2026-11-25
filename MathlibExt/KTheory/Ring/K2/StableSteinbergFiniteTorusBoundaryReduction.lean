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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatBoundaryTorusIdentities

/-! # Finite torus generator to boundary-pair reduction

For `[Field F]`, `i < n`, `j < n`, `i ≠ j`, and `u : Fˣ`, the finite torus
generator `torus i j u` factors head-left as a left central cocycle defect
times the boundary pair `torus i n u * (torus j n u)⁻¹`.

The defect is an explicit product of one same-pair Weyl defect, one
share-first Weyl/torus defect, and one transporter defect; each lies in
`torusCocycleSubgroup` and is moved head-left by
`torusCocycleSubgroup_le_center`. The proof expands the triangle
`torus i j u * torus j n u` into Weyl words, reorders the middle Weyl pair
by exact conjugation (`weyl_conj_weyl_mixed`) and swap (`weyl_swap`),
collapses the resulting same-pair Weyl product by
`weyl_samePair_mul_eq_cocycle_mul_torus`, transports the inner torus by
`weyl_conj_torus_shareFirst`, and flips the last index by the central-defect
transporter (`torus_eq_torusCocycleAt_mul_swap`). Equalities of `toStableE`
images are never used to infer membership; membership follows solely from
`torusCocycleAt_mem_torusCocycleSubgroup` (via the same-pair and share-first
existential witnesses) and subgroup closure.

Orientation is head-left throughout: `torus i j u = c * (...)`, matching
`torus_mul_eq_torusCocycleAt_mul` and
`weyl_samePair_mul_eq_cocycle_mul_torus`.

Edge cases: `n = 0` makes `i < 0` impossible; `n = 1` forces `i = j = 0`,
contradicting `i ≠ j`; both are vacuous via `omega`. Characteristic two
(`-1 = 1`) and `u = 1` are safe: all unit algebra uses `Units.ext`
coercions, never assuming `-1 ≠ 1` or `u ≠ 1`.

Nonclaims: this is only one generator reduction; no word normal form,
finite-torus landing, finite-central containment, finite-stage induction,
TWT, inverse, naturality, or Matsumoto theorem.
-/

@[expose] public section

namespace AlgebraicKTheory.StableSteinberg

universe u
variable {F : Type u} [Field F]

open scoped commutatorElement

/-- Exact Weyl-word reordering for the triangle product.

`weyl i j u * weyl i j (-1) * (weyl j n u * weyl j n (-1))`
equals
`weyl j n 1 * weyl j i a * (weyl j i 1 * weyl j n (-1))`
with `a = -u⁻¹`, using only exact Weyl conjugation
(`weyl_conj_weyl_mixed`) and swap (`weyl_swap`) plus unit algebra.
No cocycle defect is introduced here; defects arise in the next helper. -/
private theorem weyl_triangle_reorder {n i j : ℕ}
    (hin : i ≠ n) (hjn : j ≠ n) (hij : i ≠ j) (u : Fˣ) :
    weyl (R := F) i j hij u * weyl (R := F) i j hij (-1 : Fˣ) *
      (weyl (R := F) j n hjn u * weyl (R := F) j n hjn (-1 : Fˣ)) =
    weyl (R := F) j n hjn (1 : Fˣ) *
      weyl (R := F) j i hij.symm (-u⁻¹) *
      (weyl (R := F) j i hij.symm (1 : Fˣ) *
        weyl (R := F) j n hjn (-1 : Fˣ)) := by
  have hji : j ≠ i := Ne.symm hij
  have hni : n ≠ i := Ne.symm hin
  have hnj : n ≠ j := Ne.symm hjn
  -- `(-1) * u = -u` in `Fˣ`.
  have h_neg_one_mul : (-1 : Fˣ) * u = -u := by
    apply Units.ext
    simp
  -- `(-u⁻¹) * (-u) = 1` in `Fˣ`.
  have h_prod_one : (-u⁻¹ : Fˣ) * (-u : Fˣ) = 1 := by
    have hne : ((u : Fˣ) : F) ≠ 0 := Units.ne_zero _
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val,
      Units.val_one]
    rw [neg_mul_neg, inv_mul_cancel₀ hne]
  -- `(-1)⁻¹ = -1` in `Fˣ`.
  have h_inv_neg_one : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by
    apply Units.ext
    simp
  -- `W_ij(-1) = W_ji(1)`.
  have h_swap_m1 : weyl (R := F) i j hij (-1 : Fˣ) =
      weyl (R := F) j i hij.symm (1 : Fˣ) := by
    have h := weyl_swap (R := F) i j hij (-1 : Fˣ)
    rw [h_inv_neg_one] at h
    have h_neg : (-(-1 : Fˣ) : Fˣ) = (1 : Fˣ) := by
      apply Units.ext
      simp
    rw [h_neg] at h
    exact h
  -- `W_ij(u) = W_ji(-u⁻¹)`.
  have h_swap_u : weyl (R := F) i j hij u =
      weyl (R := F) j i hij.symm (-u⁻¹) :=
    weyl_swap (R := F) i j hij u
  -- Middle exact: `W_ij(-1) * W_jn(u) = W_in(-u) * W_ij(-1)`.
  have h_mid : weyl (R := F) i j hij (-1 : Fˣ) *
      weyl (R := F) j n hjn u =
      weyl (R := F) i n hin (-u) * weyl (R := F) i j hij (-1 : Fˣ) := by
    have h_conj := weyl_conj_weyl_mixed (R := F) i n j hin hij hjn
      (-1 : Fˣ) u
    rw [h_neg_one_mul] at h_conj
    calc weyl (R := F) i j hij (-1 : Fˣ) * weyl (R := F) j n hjn u
        = (weyl (R := F) i j hij (-1 : Fˣ) * weyl (R := F) j n hjn u *
            (weyl (R := F) i j hij (-1 : Fˣ))⁻¹) *
          weyl (R := F) i j hij (-1 : Fˣ) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = weyl (R := F) i n hin (-u) * weyl (R := F) i j hij (-1 : Fˣ) := by
          rw [h_conj]
  -- Same-first middle exact: `W_ij(u) * W_in(-u) = W_jn(1) * W_ji(-u⁻¹)`.
  have h_same_first : weyl (R := F) i j hij u *
      weyl (R := F) i n hin (-u) =
      weyl (R := F) j n hjn (1 : Fˣ) *
        weyl (R := F) j i hij.symm (-u⁻¹) := by
    rw [h_swap_u]
    have h_conj := weyl_conj_weyl_mixed (R := F) j n i hjn hji hin
      (-u⁻¹ : Fˣ) (-u : Fˣ)
    rw [h_prod_one] at h_conj
    calc weyl (R := F) j i hij.symm (-u⁻¹) * weyl (R := F) i n hin (-u)
        = (weyl (R := F) j i hij.symm (-u⁻¹) * weyl (R := F) i n hin (-u) *
            (weyl (R := F) j i hij.symm (-u⁻¹))⁻¹) *
          weyl (R := F) j i hij.symm (-u⁻¹) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = weyl (R := F) j n hjn (1 : Fˣ) *
          weyl (R := F) j i hij.symm (-u⁻¹) := by
          rw [h_conj]
  calc weyl (R := F) i j hij u * weyl (R := F) i j hij (-1 : Fˣ) *
      (weyl (R := F) j n hjn u * weyl (R := F) j n hjn (-1 : Fˣ))
      = weyl (R := F) i j hij u *
        (weyl (R := F) i j hij (-1 : Fˣ) * weyl (R := F) j n hjn u) *
        weyl (R := F) j n hjn (-1 : Fˣ) := by
        simp only [mul_assoc]
    _ = weyl (R := F) i j hij u *
        (weyl (R := F) i n hin (-u) * weyl (R := F) i j hij (-1 : Fˣ)) *
        weyl (R := F) j n hjn (-1 : Fˣ) := by
        rw [h_mid]
    _ = (weyl (R := F) i j hij u * weyl (R := F) i n hin (-u)) *
        weyl (R := F) i j hij (-1 : Fˣ) * weyl (R := F) j n hjn (-1 : Fˣ) := by
        simp only [mul_assoc]
    _ = (weyl (R := F) j n hjn (1 : Fˣ) *
          weyl (R := F) j i hij.symm (-u⁻¹)) *
        weyl (R := F) i j hij (-1 : Fˣ) * weyl (R := F) j n hjn (-1 : Fˣ) := by
        rw [h_same_first]
    _ = weyl (R := F) j n hjn (1 : Fˣ) *
        weyl (R := F) j i hij.symm (-u⁻¹) *
        (weyl (R := F) j i hij.symm (1 : Fˣ) *
          weyl (R := F) j n hjn (-1 : Fˣ)) := by
        rw [h_swap_m1]
        simp only [mul_assoc]

/-- Triangle product with explicit left cocycle defect.

`weyl j n 1 * weyl j i a * (weyl j i 1 * weyl j n (-1))`
with `a = -u⁻¹` equals `c * torus i n u` for an explicit
`c ∈ torusCocycleSubgroup`, via same-pair collapse
(`weyl_samePair_mul_eq_cocycle_mul_torus`), share-first transport
(`weyl_conj_torus_shareFirst`), the transporter
(`torus_eq_torusCocycleAt_mul_swap`), and centrality. -/
private theorem weyl_reordered_eq_cocycle_mul_torus {n i j : ℕ}
    (hin : i ≠ n) (hjn : j ≠ n) (hij : i ≠ j) (u : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      weyl (R := F) j n hjn (1 : Fˣ) *
        weyl (R := F) j i hij.symm (-u⁻¹) *
        (weyl (R := F) j i hij.symm (1 : Fˣ) *
          weyl (R := F) j n hjn (-1 : Fˣ)) =
      c * torus (R := F) i n hin u := by
  have hji : j ≠ i := Ne.symm hij
  have hni : n ≠ i := Ne.symm hin
  -- Same-pair collapse: `W_ji(a) * W_ji(1) = c₂ * T_ji(u⁻¹)`.
  have h_param : (-(-u⁻¹ : Fˣ)) * (1 : Fˣ)⁻¹ = u⁻¹ := by
    have h_neg : (-(-u⁻¹ : Fˣ) : Fˣ) = u⁻¹ := by
      apply Units.ext
      simp
    rw [h_neg, inv_one, mul_one]
  obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ :=
    weyl_samePair_mul_eq_cocycle_mul_torus (F := F) j i hji (-u⁻¹ : Fˣ) (1 : Fˣ)
  rw [h_param] at hc₂_eq
  -- Share-first transport: `W_jn(1) * T_ji(u⁻¹) * W_jn(1)⁻¹ = c_s * T_ni(u⁻¹)`.
  obtain ⟨c_s, hcs_mem, hcs_eq⟩ :=
    weyl_conj_torus_shareFirst (F := F) (i := j) (j := i) (k := n)
      hji hjn hni (1 : Fˣ) (u⁻¹ : Fˣ)
  -- Transporter: `T_ni(u⁻¹) = C_ni * T_in(u)`.
  have h_trans := torus_eq_torusCocycleAt_mul_swap (F := F) n i hni (u⁻¹ : Fˣ)
  have h_inv_inv : ((u⁻¹ : Fˣ)⁻¹ : Fˣ) = u := inv_inv u
  rw [h_inv_inv] at h_trans
  have hC_mem := torusCocycleAt_mem_torusCocycleSubgroup (F := F) n i hni
    (u⁻¹ : Fˣ) (-1 : Fˣ)
  -- `W_jn(-1) = W_jn(1)⁻¹`.
  have h_w_inv : weyl (R := F) j n hjn (-1 : Fˣ) =
      (weyl (R := F) j n hjn (1 : Fˣ))⁻¹ :=
    weyl_neg_eq_inv (R := F) j n hjn (1 : Fˣ)
  -- Centrality moves.
  have hc₂_center : c₂ ∈ Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center (F := F) hc₂_mem
  have hcs_center : c_s ∈ Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center (F := F) hcs_mem
  have hC_center : torusCocycleAt (F := F) n i hni (u⁻¹ : Fˣ) (-1 : Fˣ) ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center (F := F) hC_mem
  have h_comm_c₂ : Commute c₂ (weyl (R := F) j n hjn (1 : Fˣ)) := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp hc₂_center _).symm
  refine ⟨c₂ * c_s * torusCocycleAt (F := F) n i hni (u⁻¹ : Fˣ) (-1 : Fˣ),
    (torusCocycleSubgroup (F := F)).mul_mem
      ((torusCocycleSubgroup (F := F)).mul_mem hc₂_mem hcs_mem) hC_mem, ?_⟩
  calc weyl (R := F) j n hjn (1 : Fˣ) *
        weyl (R := F) j i hij.symm (-u⁻¹) *
        (weyl (R := F) j i hij.symm (1 : Fˣ) *
          weyl (R := F) j n hjn (-1 : Fˣ))
      = weyl (R := F) j n hjn (1 : Fˣ) *
        (weyl (R := F) j i hij.symm (-u⁻¹) *
          weyl (R := F) j i hij.symm (1 : Fˣ)) *
        weyl (R := F) j n hjn (-1 : Fˣ) := by
        simp only [mul_assoc]
    _ = weyl (R := F) j n hjn (1 : Fˣ) *
        (c₂ * torus (R := F) j i hji (u⁻¹ : Fˣ)) *
        weyl (R := F) j n hjn (-1 : Fˣ) := by
        rw [hc₂_eq]
    _ = c₂ * (weyl (R := F) j n hjn (1 : Fˣ) *
        torus (R := F) j i hji (u⁻¹ : Fˣ) *
        weyl (R := F) j n hjn (-1 : Fˣ)) := by
        have h1 : weyl (R := F) j n hjn (1 : Fˣ) *
            (c₂ * torus (R := F) j i hji (u⁻¹ : Fˣ)) =
            c₂ * (weyl (R := F) j n hjn (1 : Fˣ) *
              torus (R := F) j i hji (u⁻¹ : Fˣ)) :=
          (h_comm_c₂.symm).left_comm _
        calc weyl (R := F) j n hjn (1 : Fˣ) *
              (c₂ * torus (R := F) j i hji (u⁻¹ : Fˣ)) *
              weyl (R := F) j n hjn (-1 : Fˣ)
            = (c₂ * (weyl (R := F) j n hjn (1 : Fˣ) *
                torus (R := F) j i hji (u⁻¹ : Fˣ))) *
              weyl (R := F) j n hjn (-1 : Fˣ) := by
              rw [h1]
          _ = c₂ * (weyl (R := F) j n hjn (1 : Fˣ) *
                torus (R := F) j i hji (u⁻¹ : Fˣ) *
                weyl (R := F) j n hjn (-1 : Fˣ)) := by
              simp only [mul_assoc]
    _ = c₂ * (weyl (R := F) j n hjn (1 : Fˣ) *
        torus (R := F) j i hji (u⁻¹ : Fˣ) *
        (weyl (R := F) j n hjn (1 : Fˣ))⁻¹) := by
        rw [h_w_inv]
    _ = c₂ * (c_s * torus (R := F) n i hni (u⁻¹ : Fˣ)) := by
        rw [hcs_eq]
    _ = c₂ * c_s * torus (R := F) n i hni (u⁻¹ : Fˣ) := by
        rw [← mul_assoc]
    _ = c₂ * c_s *
        (torusCocycleAt (F := F) n i hni (u⁻¹ : Fˣ) (-1 : Fˣ) *
          torus (R := F) i n hin u) := by
        rw [h_trans]
    _ = (c₂ * c_s * torusCocycleAt (F := F) n i hni (u⁻¹ : Fˣ) (-1 : Fˣ)) *
        torus (R := F) i n hin u := by
        simp only [mul_assoc]

/-- Finite torus generator as a left cocycle times a boundary pair.

Purpose: reduce the finite generator `torus i j u` (`i,j < n`, `i ≠ j`)
to `torus i n u * (torus j n u)⁻¹` up to an explicit left defect in
`torusCocycleSubgroup`. Orientation is head-left. The `n = 0, 1` cases are
vacuous (`omega`); `-1 = 1` in characteristic two and `u = 1` need no
extra hypothesis.

Nonclaims: one generator only; no word normal form, finite-torus landing,
finite-central containment, finite-stage induction, TWT, inverse,
naturality, or Matsumoto claim. -/
public theorem torus_finitePair_eq_cocycle_mul_boundaryPair
    {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (u : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      torus (R := F) i j hij u =
        c * (torus (R := F) i n (Nat.ne_of_lt hi) u *
          (torus (R := F) j n (Nat.ne_of_lt hj) u)⁻¹) := by
  by_cases h2 : 2 ≤ n
  · -- Pairwise distinct indices.
    have hin : i ≠ n := Nat.ne_of_lt hi
    have hjn : j ≠ n := Nat.ne_of_lt hj
    -- Triangle: `T_ij * T_jn = c_tri * T_in`.
    have h_reorder := weyl_triangle_reorder (F := F) hin hjn hij u
    obtain ⟨c_tri, hc_tri_mem, hc_tri_eq⟩ :=
      weyl_reordered_eq_cocycle_mul_torus (F := F) hin hjn hij u
    have h_torus_ij : torus (R := F) i j hij u =
        weyl (R := F) i j hij u * weyl (R := F) i j hij (-1 : Fˣ) := rfl
    have h_torus_jn : torus (R := F) j n hjn u =
        weyl (R := F) j n hjn u * weyl (R := F) j n hjn (-1 : Fˣ) := rfl
    have h_torus_in : torus (R := F) i n hin u =
        weyl (R := F) i n hin u * weyl (R := F) i n hin (-1 : Fˣ) := rfl
    -- Combine reordering with the defect to get the triangle.
    have h_triangle : torus (R := F) i j hij u * torus (R := F) j n hjn u =
        c_tri * torus (R := F) i n hin u := by
      calc torus (R := F) i j hij u * torus (R := F) j n hjn u
          = (weyl (R := F) i j hij u * weyl (R := F) i j hij (-1 : Fˣ)) *
            (weyl (R := F) j n hjn u * weyl (R := F) j n hjn (-1 : Fˣ)) := by
            rw [← h_torus_ij, ← h_torus_jn]
        _ = weyl (R := F) i j hij u * weyl (R := F) i j hij (-1 : Fˣ) *
            (weyl (R := F) j n hjn u * weyl (R := F) j n hjn (-1 : Fˣ)) := by
            rw [← mul_assoc]
        _ = weyl (R := F) j n hjn (1 : Fˣ) *
            weyl (R := F) j i hij.symm (-u⁻¹) *
            (weyl (R := F) j i hij.symm (1 : Fˣ) *
              weyl (R := F) j n hjn (-1 : Fˣ)) := h_reorder
        _ = c_tri * torus (R := F) i n hin u := hc_tri_eq
    -- From `T_ij * T_jn = c * T_in` deduce `T_ij = c * T_in * T_jn⁻¹`.
    -- (`hin`/`hjn` are proof-irrelevant vs `Nat.ne_of_lt hi/hj`.)
    refine ⟨c_tri, hc_tri_mem, ?_⟩
    calc torus (R := F) i j hij u
        = (torus (R := F) i j hij u * torus (R := F) j n (Nat.ne_of_lt hj) u) *
          (torus (R := F) j n (Nat.ne_of_lt hj) u)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = (c_tri * torus (R := F) i n (Nat.ne_of_lt hi) u) *
          (torus (R := F) j n (Nat.ne_of_lt hj) u)⁻¹ := by
          rw [h_triangle]
      _ = c_tri * (torus (R := F) i n (Nat.ne_of_lt hi) u *
          (torus (R := F) j n (Nat.ne_of_lt hj) u)⁻¹) := by
          rw [mul_assoc]
  · -- `n < 2` with `i,j < n` and `i ≠ j` is impossible.
    omega

end AlgebraicKTheory.StableSteinberg

end
