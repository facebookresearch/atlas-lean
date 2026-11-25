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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergBoundarySymbolClosure
public import MathlibExt.KTheory.Ring.K2.MatsumotoKernelGeneration

/-! # Boundary-torus defect identities — production r1

Minimal sound torus-aware normalization API:

* Same-index: pair, triangle, and list. Derived from
  `torus_mul_eq_torusCocycleAt_mul`, `torusCocycleAt_mem_torusCocycleSubgroup`,
  `torus_one`, and `torusCocycleSubgroup_le_center`. Multiplication order is
  explicit; all correction factors are exhibited on the left, matching the
  orientation of `torus_mul_eq_torusCocycleAt_mul`.

* Distinct last-coordinate (fixed `n`, distinct `i < n`): commutator lies in
  `ker toStableE` via `toStableE_torus_fin_last_pairwise_commute`. An upgrade
  for the same-first distinct-second orientation (`i` fixed, distinct second
  indices) is proved noncircularly and lies in `torusCocycleSubgroup` with exact
  sign `⁅torus i k u, torus i j v⁆ = (torusCocycleAt i j v u)⁻¹`.

* Distinct-first same-second (the boundary-torus orientation `torus i n`,
  `torus j n` with `i ≠ j`): the central-defect transporter
  `torus i j u = torusCocycleAt i j u (-1) * torus j i u⁻¹` and the
  `torusCocycleSubgroup` commutator upgrade
  `⁅torus i n u, torus j n v⁆ = (torusCocycleAt n j v⁻¹ u⁻¹)⁻¹` are now present,
  proved noncircularly from the transporter, centrality of `torusCocycleAt`,
  and the same-first distinct-second identity; no false defect-free equality
  `torus i j u = torus j i u⁻¹` is claimed.

* Same-pair Weyl product (`weyl_samePair_mul_eq_cocycle_mul_torus`):
  `weyl i j p * weyl i j q = c * torus i j ((-p) * q⁻¹)` with defect
  `c ∈ torusCocycleSubgroup` on the left. This is the prerequisite for
  mixed Weyl/torus transport; it asserts no trivial defect, normal form,
  finite-central containment, TWT, kernel generation, or Matsumoto claim.

* Mixed Weyl/torus transport (`weyl_conj_torus_mixed`):
  `weyl i k u * torus k j v * (weyl i k u)⁻¹ = c * torus i j v` with
  defect `c ∈ torusCocycleSubgroup` on the left. The torus parameter is
  unchanged (`v`); the Weyl word rewrites via `weyl_conj_weyl_mixed` and
  the resulting same-pair product via
  `weyl_samePair_mul_eq_cocycle_mul_torus`. No defect-free equality,
  ordered torus normal form, finite-central containment, TWT, kernel
  generation, or Matsumoto claim is made.

Nonclaim: `∀ n u, Finset.univ.prod u = 1 → boundaryTorusProd n u ∈
torusCocycleSubgroup` for arbitrary `n` is false and does not appear.
No claim of `ker toStableE = torusCocycleSubgroup` or arbitrary
alternating-word collapse is made.
-/

@[expose] public section

namespace AlgebraicKTheory.StableSteinberg

universe u
variable {F : Type u} [Field F]

open scoped commutatorElement

section SameIndexTorusNormalization

/-- Same-index pair: `torus i n u * torus i n v = C * torus i n (u*v)` with
`C = torusCocycleAt i n u v`. Orientation matches
`torus_mul_eq_torusCocycleAt_mul`. -/
public theorem torus_sameIndex_pair {n i : ℕ} (hij : i ≠ n) (u v : Fˣ) :
    torus (R := F) i n hij u * torus (R := F) i n hij v =
      torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v) :=
  torus_mul_eq_torusCocycleAt_mul (F := F) (n := n) (i := i) hij u v

/-- Same-index pair cocycle lies in `torusCocycleSubgroup`. -/
public theorem torus_sameIndex_pair_mem_torusCocycleSubgroup {n i : ℕ}
    (hij : i ≠ n) (u v : Fˣ) :
    torusCocycleAt (F := F) i n hij u v ∈ torusCocycleSubgroup (F := F) :=
  torusCocycleAt_mem_torusCocycleSubgroup (F := F) i n hij u v

/-- `torusCocycleAt u 1 = 1` via `torus_one`. -/
public theorem torusCocycleAt_one_right {n i : ℕ} (hij : i ≠ n) (u : Fˣ) :
    torusCocycleAt (F := F) i n hij u (1 : Fˣ) = 1 := by
  unfold torusCocycleAt
  rw [torus_one (R := F) i n hij, mul_one, mul_one, mul_inv_cancel]

/-- `torusCocycleAt 1 v = 1` via `torus_one`. -/
public theorem torusCocycleAt_one_left {n i : ℕ} (hij : i ≠ n) (v : Fˣ) :
    torusCocycleAt (F := F) i n hij (1 : Fˣ) v = 1 := by
  unfold torusCocycleAt
  rw [torus_one (R := F) i n hij, one_mul, one_mul, mul_inv_cancel]

/-- `torusCocycleAt` is central, via `torusCocycleSubgroup_le_center`. -/
public theorem torusCocycleAt_mem_center {n i : ℕ} (hij : i ≠ n) (u v : Fˣ) :
    torusCocycleAt (F := F) i n hij u v ∈ Subgroup.center (StableSteinberg F) := by
  exact torusCocycleSubgroup_le_center (F := F)
    (torusCocycleAt_mem_torusCocycleSubgroup (F := F) i n hij u v)

/-- Same-index triangle with explicit left-to-right cocycle factors:
`(a b) c = C_uv * (t_uv c) = C_uv * C_{uv,w} * t_{uvw}`. -/
public theorem torus_sameIndex_triangle {n i : ℕ} (hij : i ≠ n) (u v w : Fˣ) :
    torus (R := F) i n hij u * torus (R := F) i n hij v * torus (R := F) i n hij w =
      torusCocycleAt (F := F) i n hij u v *
        torusCocycleAt (F := F) i n hij (u * v) w *
        torus (R := F) i n hij (u * v * w) := by
  have h1 : torus (R := F) i n hij u * torus (R := F) i n hij v =
      torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) (n := n) (i := i) hij u v
  have h2 : torus (R := F) i n hij (u * v) * torus (R := F) i n hij w =
      torusCocycleAt (F := F) i n hij (u * v) w *
        torus (R := F) i n hij (u * v * w) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) (n := n) (i := i) hij (u * v) w
  calc torus (R := F) i n hij u * torus (R := F) i n hij v * torus (R := F) i n hij w
      = (torus (R := F) i n hij u * torus (R := F) i n hij v) *
          torus (R := F) i n hij w := rfl
    _ = (torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v)) *
          torus (R := F) i n hij w := by rw [h1]
    _ = torusCocycleAt (F := F) i n hij u v *
          (torus (R := F) i n hij (u * v) * torus (R := F) i n hij w) := by rw [mul_assoc]
    _ = torusCocycleAt (F := F) i n hij u v *
          (torusCocycleAt (F := F) i n hij (u * v) w *
            torus (R := F) i n hij (u * v * w)) := by rw [h2]
    _ = torusCocycleAt (F := F) i n hij u v * torusCocycleAt (F := F) i n hij (u * v) w *
          torus (R := F) i n hij (u * v * w) := by rw [← mul_assoc]

/-- Same-index cocycle list accumulating corrections on the left:
`[] ↦ 1`, `[u] ↦ 1`, `u :: vs ↦ defect vs * C(u, vs.prod)`. -/
public noncomputable def sameIndexCocycleList {n i : ℕ} (hij : i ≠ n) :
    List Fˣ → StableSteinberg F
  | [] => 1
  | [_] => 1
  | u :: vs => sameIndexCocycleList hij vs * torusCocycleAt (F := F) i n hij u vs.prod

@[simp]
public theorem sameIndexCocycleList_nil {n i : ℕ} (hij : i ≠ n) :
    sameIndexCocycleList (F := F) (n := n) (i := i) hij [] = 1 := rfl

@[simp]
public theorem sameIndexCocycleList_singleton {n i : ℕ} (hij : i ≠ n) (u : Fˣ) :
    sameIndexCocycleList (F := F) (n := n) (i := i) hij [u] = 1 := rfl

private theorem sameIndexCocycleList_cons_cons {n i : ℕ} (hij : i ≠ n)
    (u v : Fˣ) (vs : List Fˣ) :
    sameIndexCocycleList (F := F) (n := n) (i := i) hij (u :: v :: vs) =
      sameIndexCocycleList (F := F) hij (v :: vs) *
        torusCocycleAt (F := F) i n hij u (v :: vs).prod := rfl

/-- Defect lies in `torusCocycleSubgroup`. Uses `torusCocycleAt_mem_torusCocycleSubgroup`
and closure under `*`. The `C(u,1)=1` case follows from `torus_one` via
`torusCocycleAt_one_right`; singleton returns `1` definitionally. -/
public theorem sameIndexCocycleList_mem_torusCocycleSubgroup {n i : ℕ}
    (hij : i ≠ n) (us : List Fˣ) :
    sameIndexCocycleList (F := F) hij us ∈ torusCocycleSubgroup (F := F) := by
  induction us with
  | nil =>
    simp only [sameIndexCocycleList]
    exact (torusCocycleSubgroup (F := F)).one_mem
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [sameIndexCocycleList]
      exact (torusCocycleSubgroup (F := F)).one_mem
    | cons hd2 tl2 =>
      simp only [sameIndexCocycleList]
      exact (torusCocycleSubgroup (F := F)).mul_mem ih
        (torusCocycleAt_mem_torusCocycleSubgroup (F := F) i n hij hd (hd2 :: tl2).prod)

/-- Defect is central. -/
public theorem sameIndexCocycleList_mem_center {n i : ℕ} (hij : i ≠ n)
    (us : List Fˣ) :
    sameIndexCocycleList (F := F) hij us ∈ Subgroup.center (StableSteinberg F) := by
  exact torusCocycleSubgroup_le_center (F := F)
    (sameIndexCocycleList_mem_torusCocycleSubgroup (F := F) hij us)

/-- Main same-index list normalization with explicit left cocycle factor:
`∏ map torus us = defect us * torus (us.prod)`. Uses
`torus_mul_eq_torusCocycleAt_mul`, `torus_one`, centrality of defect, and
`mul_assoc`. Multiplication order: defect on the left, then torus of product. -/
public theorem torus_sameIndex_list {n i : ℕ} (hij : i ≠ n) (us : List Fˣ) :
    (us.map (torus (R := F) i n hij)).prod =
      sameIndexCocycleList (F := F) hij us *
        torus (R := F) i n hij us.prod := by
  induction us with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.prod_nil, sameIndexCocycleList,
      torus_one (R := F) i n hij, mul_one]
  | cons hd tl ih =>
    cases tl with
    | nil =>
      -- singleton
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        sameIndexCocycleList, one_mul, mul_one]
    | cons hd2 tl2 =>
      -- tl = hd2 :: tl2 non-empty
      have h_center : sameIndexCocycleList (F := F) hij (hd2 :: tl2) ∈
          Subgroup.center (StableSteinberg F) :=
        sameIndexCocycleList_mem_center (F := F) hij (hd2 :: tl2)
      have h_comm : Commute
          (sameIndexCocycleList (F := F) hij (hd2 :: tl2))
          (torus (R := F) i n hij hd) :=
        (Subgroup.mem_center_iff.mp h_center (torus (R := F) i n hij hd)).symm
      have h_pair : torus (R := F) i n hij hd *
          torus (R := F) i n hij (hd2 :: tl2).prod =
          torusCocycleAt (F := F) i n hij hd (hd2 :: tl2).prod *
            torus (R := F) i n hij (hd :: hd2 :: tl2).prod := by
        exact torus_mul_eq_torusCocycleAt_mul (F := F) (n := n) (i := i) hij hd
          (hd2 :: tl2).prod
      calc (List.map (torus (R := F) i n hij) (hd :: hd2 :: tl2)).prod
          = torus (R := F) i n hij hd *
              (List.map (torus (R := F) i n hij) (hd2 :: tl2)).prod := by rfl
        _ = torus (R := F) i n hij hd *
              (sameIndexCocycleList (F := F) hij (hd2 :: tl2) *
                torus (R := F) i n hij (hd2 :: tl2).prod) := by rw [ih]
        _ = (torus (R := F) i n hij hd * sameIndexCocycleList (F := F) hij (hd2 :: tl2)) *
              torus (R := F) i n hij (hd2 :: tl2).prod := by rw [← mul_assoc]
        _ = (sameIndexCocycleList (F := F) hij (hd2 :: tl2) * torus (R := F) i n hij hd) *
              torus (R := F) i n hij (hd2 :: tl2).prod := by rw [← h_comm.eq]
        _ = sameIndexCocycleList (F := F) hij (hd2 :: tl2) *
              (torus (R := F) i n hij hd * torus (R := F) i n hij (hd2 :: tl2).prod) := by
            rw [mul_assoc]
        _ = sameIndexCocycleList (F := F) hij (hd2 :: tl2) *
              (torusCocycleAt (F := F) i n hij hd (hd2 :: tl2).prod *
                torus (R := F) i n hij (hd :: hd2 :: tl2).prod) := by rw [h_pair]
        _ = (sameIndexCocycleList (F := F) hij (hd2 :: tl2) *
              torusCocycleAt (F := F) i n hij hd (hd2 :: tl2).prod) *
              torus (R := F) i n hij (hd :: hd2 :: tl2).prod := by rw [← mul_assoc]
        _ = sameIndexCocycleList (F := F) hij (hd :: hd2 :: tl2) *
              torus (R := F) i n hij (hd :: hd2 :: tl2).prod := rfl

end SameIndexTorusNormalization

section DistinctLastCoordinateCommutator

/-- The canonical pairwise commuting of boundary-torus images after `toStableE`
for `i : Fin n`. Orientation: images commute, no claim in `StableSteinberg`. -/
private theorem toStableE_torus_fin_last_commute_of_ne {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (u v : Fˣ)
    (uf : Fin n → Fˣ)
    (h_ui : uf i = u) (h_uj : uf j = v) :
    Commute (toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) u))
      (toStableE (R := F) (torus j.val n (Nat.ne_of_lt j.isLt) v)) := by
  have h_pair := toStableE_torus_fin_last_pairwise_commute (F := F) n uf
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have h_com := h_pair hi_mem hj_mem hij
  -- transport via uf values
  have h_eq_i : toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (uf i)) =
      toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) u) := by rw [h_ui]
  have h_eq_j : toStableE (R := F) (torus j.val n (Nat.ne_of_lt j.isLt) (uf j)) =
      toStableE (R := F) (torus j.val n (Nat.ne_of_lt j.isLt) v) := by rw [h_uj]
  rw [← h_eq_i, ← h_eq_j]
  exact h_com

/-- Helper: choose `uf` with prescribed values at `i, j` and `1` elsewhere. -/
private noncomputable def finTorusUnit (n : ℕ) (i j : Fin n) (_hij : i ≠ j) (u v : Fˣ) :
    Fin n → Fˣ :=
  fun k => if k = i then u else if k = j then v else 1

@[simp]
private theorem finTorusUnit_apply_i {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u v : Fˣ) :
    finTorusUnit (F := F) n i j hij u v i = u := by
  simp [finTorusUnit]

@[simp]
private theorem finTorusUnit_apply_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u v : Fˣ) :
    finTorusUnit (F := F) n i j hij u v j = v := by
  simp [finTorusUnit, Ne.symm hij]

/-- Distinct last-coordinate torus factors commute after `toStableE`. -/
public theorem toStableE_torus_fin_last_commute {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (u v : Fˣ) :
    Commute (toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) u))
      (toStableE (R := F) (torus j.val n (Nat.ne_of_lt j.isLt) v)) := by
  let uf := finTorusUnit (F := F) n i j hij u v
  have hi : uf i = u := finTorusUnit_apply_i (F := F) hij u v
  have hj : uf j = v := finTorusUnit_apply_j (F := F) hij u v
  exact toStableE_torus_fin_last_commute_of_ne (F := F) hij u v uf hi hj

/-- Commutator of distinct last-coordinate torus factors maps to `1` in `StableE`. -/
public theorem torus_distinct_last_comm_toStableE_eq_one {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (u v : Fˣ) :
    toStableE (R := F) ⁅torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u,
      torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v⁆ = 1 := by
  have h_comm := toStableE_torus_fin_last_commute (F := F) (n := n) (i := i) (j := j) hij u v
  have h_map : toStableE (R := F)
      ⁅torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u,
        torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v⁆ =
      ⁅toStableE (R := F) (torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u),
        toStableE (R := F) (torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v)⁆ := by
    simp [commutatorElement_def, map_mul, map_inv]
  rw [h_map, commutatorElement_eq_one_iff_commute.mpr h_comm]

/-- Distinct last-coordinate torus commutator lies in `ker toStableE`. Uses
`toStableE_torus_fin_last_pairwise_commute`. -/
public theorem torus_distinct_last_comm_mem_ker {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u,
      torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v⁆ ∈
      MonoidHom.ker (toStableE (R := F)) := by
  rw [MonoidHom.mem_ker]
  exact torus_distinct_last_comm_toStableE_eq_one (F := F) hij u v

/-- Nat-indexed variant: distinct `i < n`, `j < n`, `i ≠ j`. -/
public theorem torus_distinct_last_comm_mem_ker_nat {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i n (Nat.ne_of_lt hi) u,
      torus (R := F) j n (Nat.ne_of_lt hj) v⁆ ∈
      MonoidHom.ker (toStableE (R := F)) := by
  let i' : Fin n := ⟨i, hi⟩
  let j' : Fin n := ⟨j, hj⟩
  have hij' : i' ≠ j' := by
    intro h
    have hv : i = j := congrArg Fin.val h
    exact hij hv
  have := torus_distinct_last_comm_mem_ker (F := F) (n := n) (i := i') (j := j') hij' u v
  simpa [i', j'] using this

/-- Same-index torus commutator identity: `[t_u, t_v] = C_uv * C_vu⁻¹` where
`C_uv = torusCocycleAt i j u v`. Uses `torus_mul_eq_torusCocycleAt_mul` and
centrality of `torusCocycleSubgroup`. -/
public theorem torus_sameIndex_comm_eq {n i : ℕ} (hij : i ≠ n) (u v : Fˣ) :
    ⁅torus (R := F) i n hij u, torus (R := F) i n hij v⁆ =
      torusCocycleAt (F := F) i n hij u v *
        (torusCocycleAt (F := F) i n hij v u)⁻¹ := by
  have h_uv : torus (R := F) i n hij u * torus (R := F) i n hij v =
      torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) hij u v
  have h_vu : torus (R := F) i n hij v * torus (R := F) i n hij u =
      torusCocycleAt (F := F) i n hij v u * torus (R := F) i n hij (v * u) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) hij v u
  have h_prod : v * u = u * v := mul_comm v u
  have h_tuv : torus (R := F) i n hij (v * u) =
      torus (R := F) i n hij (u * v) := by rw [h_prod]
  -- centrality of cocycles
  have hCuv_center : torusCocycleAt (F := F) i n hij u v ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleAt_mem_center (F := F) hij u v
  have hCvu_center : torusCocycleAt (F := F) i n hij v u ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleAt_mem_center (F := F) hij v u
  calc ⁅torus i n hij u, torus i n hij v⁆
      = torus i n hij u * torus i n hij v *
          (torus i n hij v * torus i n hij u)⁻¹ := by
        rw [commutatorElement_def, mul_assoc, ← mul_inv_rev]
    _ = (torusCocycleAt i n hij u v * torus i n hij (u * v)) *
          (torusCocycleAt i n hij v u * torus i n hij (v * u))⁻¹ := by
        rw [h_uv, h_vu]
    _ = torusCocycleAt i n hij u v * torus i n hij (u * v) *
          (torus i n hij (v * u))⁻¹ * (torusCocycleAt i n hij v u)⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc]
    _ = torusCocycleAt i n hij u v * torus i n hij (u * v) *
          (torus i n hij (u * v))⁻¹ * (torusCocycleAt i n hij v u)⁻¹ := by
        rw [h_tuv]
    _ = (torusCocycleAt i n hij u v * (torus i n hij (u * v) * (torus i n hij (u * v))⁻¹)) *
          (torusCocycleAt i n hij v u)⁻¹ := by
        rw [mul_assoc (torusCocycleAt i n hij u v) (torus i n hij (u * v)) _]
    _ = torusCocycleAt i n hij u v *
          ((torus i n hij (u * v) * (torus i n hij (u * v))⁻¹) *
            (torusCocycleAt i n hij v u)⁻¹) := by
        rw [mul_assoc (torusCocycleAt i n hij u v) _ _]
    _ = torusCocycleAt i n hij u v * (torusCocycleAt i n hij v u)⁻¹ := by
        rw [mul_inv_cancel, one_mul]

/-- Same-first distinct-second commutator orientation:
`⁅torus i k u, torus i j v⁆ = (torusCocycleAt i j v u)⁻¹`. Proved from
`torus_conj_torus` and same-index pair. Lies in `torusCocycleSubgroup`. -/
public theorem torus_sameFirst_distinctSecond_comm_eq_inv {i j k : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i k hik u, torus (R := F) i j hij v⁆ =
      (torusCocycleAt (F := F) i j hij v u)⁻¹ := by
  have h_conj := torus_conj_torus (R := F) i j k hij hik hkj u v
  -- h_conj : torus i k u * torus i j v * (torus i k u)⁻¹ =
  --          torus i j (u*v) * (torus i j u)⁻¹
  have h_uv : torus (R := F) i j hij u * torus (R := F) i j hij v =
      torusCocycleAt (F := F) i j hij u v * torus (R := F) i j hij (u * v) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) hij u v
  have h_vu : torus (R := F) i j hij v * torus (R := F) i j hij u =
      torusCocycleAt (F := F) i j hij v u * torus (R := F) i j hij (v * u) :=
    torus_mul_eq_torusCocycleAt_mul (F := F) hij v u
  have h_comm : v * u = u * v := mul_comm v u
  have h_tvu : torus (R := F) i j hij (v * u) =
      torus (R := F) i j hij (u * v) := by rw [h_comm]
  calc ⁅torus i k hik u, torus i j hij v⁆
      = torus i k hik u * torus i j hij v * (torus i k hik u)⁻¹ *
          (torus i j hij v)⁻¹ := by rfl
    _ = (torus i j hij (u * v) * (torus i j hij u)⁻¹) *
          (torus i j hij v)⁻¹ := by rw [h_conj]
    _ = torus i j hij (u * v) * (torus i j hij u)⁻¹ * (torus i j hij v)⁻¹ := rfl
    _ = torus i j hij (u * v) * (torus i j hij v * torus i j hij u)⁻¹ := by
        rw [mul_assoc, ← mul_inv_rev]
    _ = torus i j hij (u * v) *
          (torusCocycleAt i j hij v u * torus i j hij (v * u))⁻¹ := by rw [h_vu]
    _ = torus i j hij (u * v) *
          (torus i j hij (v * u))⁻¹ * (torusCocycleAt i j hij v u)⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc]
    _ = torus i j hij (u * v) * (torus i j hij (u * v))⁻¹ *
          (torusCocycleAt i j hij v u)⁻¹ := by rw [h_tvu]
    _ = (torusCocycleAt i j hij v u)⁻¹ := by rw [mul_inv_cancel, one_mul]

/-- Same-first distinct-second commutator lies in `torusCocycleSubgroup`. -/
public theorem torus_sameFirst_distinctSecond_comm_mem_torusCocycleSubgroup
    {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i k hik u, torus (R := F) i j hij v⁆ ∈
      torusCocycleSubgroup (F := F) := by
  rw [torus_sameFirst_distinctSecond_comm_eq_inv (F := F) hij hik hkj u v]
  exact (torusCocycleSubgroup (F := F)).inv_mem
    (torusCocycleAt_mem_torusCocycleSubgroup (F := F) i j hij v u)

end DistinctLastCoordinateCommutator

section CentralDefectTransporter

private theorem torus_swap_aux (i j : ℕ) (hij : i ≠ j) (u : Fˣ) :
    torus (R := F) j i hij.symm u⁻¹ =
      torus (R := F) i j hij (-u) * (torus (R := F) i j hij (-1 : Fˣ))⁻¹ := by
  unfold torus
  have h1 : weyl (R := F) j i hij.symm u⁻¹ = weyl (R := F) i j hij (-u) := by
    have h := weyl_swap (R := F) j i hij.symm u⁻¹
    have h_units : (-(u⁻¹)⁻¹ : Fˣ) = -u := by simp
    rw [h, h_units]
  have h2 : weyl (R := F) j i hij.symm (-1 : Fˣ) =
      (weyl (R := F) i j hij (-1 : Fˣ))⁻¹ := by
    have h_swap : weyl (R := F) j i hij.symm (-1 : Fˣ) =
        weyl (R := F) i j hij (1 : Fˣ) := by
      have h := weyl_swap (R := F) j i hij.symm (-1 : Fˣ)
      have h_eq : (-(-1 : Fˣ)⁻¹ : Fˣ) = (1 : Fˣ) := by
        have h_inv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by ext; simp
        rw [h_inv]; simp
      rw [h, h_eq]
    have h_neg : weyl (R := F) i j hij (-1 : Fˣ) =
        (weyl (R := F) i j hij (1 : Fˣ))⁻¹ :=
      weyl_neg_eq_inv (R := F) i j hij (1 : Fˣ)
    rw [h_swap, h_neg, inv_inv]
  rw [h1, h2]
  let w := weyl (R := F) i j hij (-1 : Fˣ)
  let a := weyl (R := F) i j hij (-u)
  have h_eq : (a * w) * (w * w)⁻¹ = a * w⁻¹ := by
    calc (a * w) * (w * w)⁻¹
        = (a * w) * (w⁻¹ * w⁻¹) := by rw [mul_inv_rev]
      _ = a * (w * (w⁻¹ * w⁻¹)) := by rw [mul_assoc]
      _ = a * ((w * w⁻¹) * w⁻¹) := by
          rw [← mul_assoc (a := w)]
      _ = a * ((1 : StableSteinberg F) * w⁻¹) := by
          rw [mul_inv_cancel]
      _ = a * w⁻¹ := by rw [one_mul]
  rw [← h_eq]

/-- Central-defect torus transporter: `torus i j u` equals the central cocycle
defect `torusCocycleAt i j u (-1)` times the swapped torus `torus j i u⁻¹`.
Proved noncircularly from `weyl_swap`, `weyl_neg_eq_inv`, `torus`, and
`torus_mul_eq_torusCocycleAt_mul`; no defect-free equality
`torus i j u = torus j i u⁻¹` is claimed. -/
public theorem torus_eq_torusCocycleAt_mul_swap (i j : ℕ) (hij : i ≠ j) (u : Fˣ) :
    torus (R := F) i j hij u =
      torusCocycleAt (F := F) i j hij u (-1 : Fˣ) *
        torus (R := F) j i hij.symm u⁻¹ := by
  have h_mul : torus (R := F) i j hij u * torus (R := F) i j hij (-1 : Fˣ) =
      torusCocycleAt (F := F) i j hij u (-1 : Fˣ) * torus (R := F) i j hij (-u) := by
    have h := torus_mul_eq_torusCocycleAt_mul (F := F) (n := j) (i := i) hij u (-1 : Fˣ)
    have h_eq : (u * (-1 : Fˣ)) = (-u : Fˣ) := by simp
    rw [h_eq] at h
    exact h
  have h_aux := torus_swap_aux (F := F) i j hij u
  calc torus (R := F) i j hij u
      = torus (R := F) i j hij u * torus (R := F) i j hij (-1 : Fˣ) *
          (torus (R := F) i j hij (-1 : Fˣ))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = torusCocycleAt (F := F) i j hij u (-1 : Fˣ) * torus (R := F) i j hij (-u) *
          (torus (R := F) i j hij (-1 : Fˣ))⁻¹ := by rw [h_mul, mul_assoc]
    _ = torusCocycleAt (F := F) i j hij u (-1 : Fˣ) *
          (torus (R := F) i j hij (-u) * (torus (R := F) i j hij (-1 : Fˣ))⁻¹) := by
        rw [mul_assoc]
    _ = torusCocycleAt (F := F) i j hij u (-1 : Fˣ) *
          torus (R := F) j i hij.symm u⁻¹ := by rw [← h_aux]

end CentralDefectTransporter

section DistinctFirstSameSecondCommutator

private theorem central_left_comm_eq (c a b : StableSteinberg F)
    (hc : c ∈ Subgroup.center (StableSteinberg F)) :
    ⁅c * a, b⁆ = ⁅a, b⁆ := by
  have h_comm : ∀ x : StableSteinberg F, Commute c x := fun x => by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp hc x).symm
  have h_cb : ⁅c, b⁆ = (1 : StableSteinberg F) := (h_comm b).commutator_eq
  have h_conj : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := (h_comm ⁅a, b⁆).mul_inv_cancel
  calc ⁅c * a, b⁆ = c * ⁅a, b⁆ * c⁻¹ * ⁅c, b⁆ :=
        commutatorElement_mul_left_eq_conj_mul c a b
    _ = c * ⁅a, b⁆ * c⁻¹ * 1 := by rw [h_cb]
    _ = c * ⁅a, b⁆ * c⁻¹ := by rw [mul_one]
    _ = ⁅a, b⁆ := h_conj

private theorem central_right_comm_eq (a c b : StableSteinberg F)
    (hc : c ∈ Subgroup.center (StableSteinberg F)) :
    ⁅a, c * b⁆ = ⁅a, b⁆ := by
  have h_comm : ∀ x : StableSteinberg F, Commute c x := fun x => by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp hc x).symm
  have h_ac : ⁅a, c⁆ = (1 : StableSteinberg F) := ((h_comm a).symm).commutator_eq
  have h_conj : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := (h_comm ⁅a, b⁆).mul_inv_cancel
  calc ⁅a, c * b⁆ = ⁅a, c⁆ * c * ⁅a, b⁆ * c⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj a c b
    _ = 1 * c * ⁅a, b⁆ * c⁻¹ := by rw [h_ac]
    _ = c * ⁅a, b⁆ * c⁻¹ := by rw [one_mul]
    _ = ⁅a, b⁆ := h_conj

/-- Distinct-first same-second boundary commutator equality:
`⁅torus i n u, torus j n v⁆ = (torusCocycleAt n j v⁻¹ u⁻¹)⁻¹`.
Rewrites each boundary torus via `torus_eq_torusCocycleAt_mul_swap`, removes
the central left factors with `torusCocycleAt_mem_center`, then reuses
`torus_sameFirst_distinctSecond_comm_eq_inv` at `n` with units `u⁻¹, v⁻¹`. -/
public theorem torus_distinctFirst_sameSecond_comm_eq_inv {i j n : ℕ}
    (hin : i ≠ n) (hjn : j ≠ n) (hij : i ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i n hin u, torus (R := F) j n hjn v⁆ =
      (torusCocycleAt (F := F) n j hjn.symm v⁻¹ u⁻¹)⁻¹ := by
  have hCi : torusCocycleAt (F := F) i n hin u (-1) ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleAt_mem_center (F := F) hin u (-1)
  have hCj : torusCocycleAt (F := F) j n hjn v (-1) ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleAt_mem_center (F := F) hjn v (-1)
  have hti : torus (R := F) i n hin u =
      torusCocycleAt (F := F) i n hin u (-1) *
        torus (R := F) n i hin.symm u⁻¹ :=
    torus_eq_torusCocycleAt_mul_swap (F := F) i n hin u
  have htj : torus (R := F) j n hjn v =
      torusCocycleAt (F := F) j n hjn v (-1) *
        torus (R := F) n j hjn.symm v⁻¹ :=
    torus_eq_torusCocycleAt_mul_swap (F := F) j n hjn v
  calc ⁅torus (R := F) i n hin u, torus (R := F) j n hjn v⁆
      = ⁅torusCocycleAt (F := F) i n hin u (-1) *
          torus (R := F) n i hin.symm u⁻¹,
        torusCocycleAt (F := F) j n hjn v (-1) *
          torus (R := F) n j hjn.symm v⁻¹⁆ := by rw [hti, htj]
    _ = ⁅torus (R := F) n i hin.symm u⁻¹,
        torusCocycleAt (F := F) j n hjn v (-1) *
          torus (R := F) n j hjn.symm v⁻¹⁆ :=
        central_left_comm_eq _ _ _ hCi
    _ = ⁅torus (R := F) n i hin.symm u⁻¹,
        torus (R := F) n j hjn.symm v⁻¹⁆ :=
        central_right_comm_eq _ _ _ hCj
    _ = (torusCocycleAt (F := F) n j hjn.symm v⁻¹ u⁻¹)⁻¹ :=
        torus_sameFirst_distinctSecond_comm_eq_inv (F := F)
          hjn.symm hin.symm hij u⁻¹ v⁻¹

/-- Distinct-first same-second commutator lies in `torusCocycleSubgroup`. -/
public theorem torus_distinctFirst_sameSecond_comm_mem_torusCocycleSubgroup
    {i j n : ℕ} (hin : i ≠ n) (hjn : j ≠ n) (hij : i ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i n hin u, torus (R := F) j n hjn v⁆ ∈
      torusCocycleSubgroup (F := F) := by
  rw [torus_distinctFirst_sameSecond_comm_eq_inv (F := F) hin hjn hij u v]
  exact Subgroup.inv_mem (torusCocycleSubgroup (F := F))
    (torusCocycleAt_mem_torusCocycleSubgroup (F := F) n j hjn.symm v⁻¹ u⁻¹)

/-- `Fin n` boundary wrapper for the distinct-first same-second commutator,
matching the orientation of `torus_distinct_last_comm_mem_ker`. -/
public theorem torus_distinct_last_comm_mem_torusCocycleSubgroup
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u v : Fˣ) :
    ⁅torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u,
      torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v⁆ ∈
      torusCocycleSubgroup (F := F) := by
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  exact torus_distinctFirst_sameSecond_comm_mem_torusCocycleSubgroup
    (F := F) (hin := Nat.ne_of_lt i.isLt) (hjn := Nat.ne_of_lt j.isLt) hij' u v

end DistinctFirstSameSecondCommutator

section AllIndexBoundarySwap

/-- Same-index commutator lies in `torusCocycleSubgroup`.
Orientation: `⁅torus i n u, torus i n v⁆ = torusCocycleAt i n u v * (torusCocycleAt i n v u)⁻¹`.
No claim that the factors commute exactly. -/
public theorem torus_sameIndex_comm_mem_torusCocycleSubgroup {n i : ℕ}
    (hij : i ≠ n) (u v : Fˣ) :
    ⁅torus (R := F) i n hij u, torus (R := F) i n hij v⁆ ∈
      torusCocycleSubgroup (F := F) := by
  rw [torus_sameIndex_comm_eq (F := F) hij u v]
  exact (torusCocycleSubgroup (F := F)).mul_mem
    (torusCocycleAt_mem_torusCocycleSubgroup (F := F) i n hij u v)
    ((torusCocycleSubgroup (F := F)).inv_mem
      (torusCocycleAt_mem_torusCocycleSubgroup (F := F) i n hij v u))

/-- Unified `Fin n` boundary commutator: any two last-coordinate torus factors
commute modulo `torusCocycleSubgroup`. Splits on `i = j`; same-index uses
`torus_sameIndex_comm_mem_torusCocycleSubgroup`, distinct uses
`torus_distinct_last_comm_mem_torusCocycleSubgroup`. No defect-free
commutativity is claimed. -/
public theorem torus_last_comm_mem_torusCocycleSubgroup {n : ℕ} (i j : Fin n)
    (u v : Fˣ) :
    ⁅torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u,
      torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v⁆ ∈
      torusCocycleSubgroup (F := F) := by
  by_cases hij : i = j
  · subst hij
    exact torus_sameIndex_comm_mem_torusCocycleSubgroup
      (F := F) (hij := Nat.ne_of_lt i.isLt) u v
  · exact torus_distinct_last_comm_mem_torusCocycleSubgroup (F := F) hij u v

/-- Pair swap modulo `torusCocycleSubgroup`: any two last-coordinate torus
factors swap at the cost of the commutator cocycle `c = ⁅a, b⁆`.
Orientation: `a * b = c * (b * a)` with `c ∈ torusCocycleSubgroup`
from `torus_last_comm_mem_torusCocycleSubgroup` and `commutatorElement_def`.
No exact commutativity `a * b = b * a` is claimed. -/
public theorem torus_last_mul_eq_cocycle_mul_swap {n : ℕ} (i j : Fin n)
    (u v : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u *
        torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v =
        c * (torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v *
          torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u) := by
  let a := torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u
  let b := torus (R := F) j.val n (Nat.ne_of_lt j.isLt) v
  have hmem : ⁅a, b⁆ ∈ torusCocycleSubgroup (F := F) :=
    torus_last_comm_mem_torusCocycleSubgroup (F := F) (i := i) (j := j) u v
  refine ⟨⁅a, b⁆, hmem, ?_⟩
  have h_eq : a * b = ⁅a, b⁆ * (b * a) := by
    have h1 : ⁅a, b⁆ * (b * a) = a * b := by
      calc ⁅a, b⁆ * (b * a)
          = (a * b * a⁻¹ * b⁻¹) * (b * a) := by rw [commutatorElement_def]
        _ = a * b * a⁻¹ * (b⁻¹ * (b * a)) := by rw [mul_assoc, mul_assoc]
        _ = a * b * a⁻¹ * ((b⁻¹ * b) * a) := by rw [← mul_assoc b⁻¹ b a]
        _ = a * b * a⁻¹ * a := by rw [inv_mul_cancel, one_mul]
        _ = a * b * (a⁻¹ * a) := by rw [← mul_assoc (a * b) a⁻¹ a]
        _ = a * b := by rw [inv_mul_cancel, mul_one]
    exact h1.symm
  -- `h_eq` is `a * b = ⁅a,b⁆ * (b*a)` but with `a,b` let-bound; rewrite to goal
  simpa [a, b] using h_eq

end AllIndexBoundarySwap

/-- `L : List (Fin n × Fˣ)` encodes `word L = ∏ torus` via
`L.map (fun p => torus p.1.val n p.2) |>.prod`. If `L₁.Perm L₂` then
`word L₁ = c * word L₂` with `c ∈ torusCocycleSubgroup` left.
`cons` uses `torusCocycleSubgroup_le_center`; `swap` uses
`torus_last_mul_eq_cocycle_mul_swap`; `trans` multiplies defects. -/
public theorem torus_boundaryWord_perm_of_perm {n : ℕ}
    (L₁ L₂ : List (Fin n × Fˣ)) (h : L₁.Perm L₂) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      (L₁.map (fun p : Fin n × Fˣ =>
        torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod =
      c * (L₂.map (fun p : Fin n × Fˣ =>
        torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod := by
  induction h with
  | nil => exact ⟨1, (torusCocycleSubgroup (F := F)).one_mem, by simp⟩
  | @cons x l₁ l₂ _ ih =>
    obtain ⟨c, hc_mem, hc_eq⟩ := ih
    refine ⟨c, hc_mem, ?_⟩
    have h_comm : torus (R := F) x.1.val n (Nat.ne_of_lt x.1.isLt) x.2 * c =
        c * torus (R := F) x.1.val n (Nat.ne_of_lt x.1.isLt) x.2 :=
      Subgroup.mem_center_iff.mp
        (torusCocycleSubgroup_le_center (F := F) hc_mem) _
    simp only [List.map_cons, List.prod_cons] at hc_eq ⊢
    rw [hc_eq, ← mul_assoc, h_comm, mul_assoc]
  | swap x y l =>
    obtain ⟨c, hc_mem, hc_eq⟩ :=
      torus_last_mul_eq_cocycle_mul_swap (F := F) (i := y.1) (j := x.1) y.2 x.2
    refine ⟨c, hc_mem, ?_⟩
    simp only [List.map_cons, List.prod_cons] at hc_eq ⊢
    rw [← mul_assoc, hc_eq, mul_assoc, mul_assoc]
  | @trans l₁ l₂ l₃ _ _ ih₁₂ ih₂₃ =>
    obtain ⟨c₁, hc₁_mem, hc₁_eq⟩ := ih₁₂
    obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ := ih₂₃
    refine ⟨c₁ * c₂, (torusCocycleSubgroup (F := F)).mul_mem hc₁_mem hc₂_mem, ?_⟩
    calc (l₁.map (fun p : Fin n × Fˣ =>
          torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod
        = c₁ * (l₂.map (fun p : Fin n × Fˣ =>
            torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod := hc₁_eq
      _ = c₁ * (c₂ * (l₃.map (fun p : Fin n × Fˣ =>
            torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod) := by
        rw [hc₂_eq]
      _ = (c₁ * c₂) * (l₃.map (fun p : Fin n × Fˣ =>
            torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod := by
        rw [mul_assoc]

section BoundaryTorusWordApi

/-- Boundary torus word: product of `torus` factors indexed by `Fin n`.
Field only; `n = 0` gives empty product `1`. No collection claim. -/
public noncomputable def boundaryTorusWord {n : ℕ}
    (L : List (Fin n × Fˣ)) : StableSteinberg F :=
  (L.map (fun p : Fin n × Fˣ =>
    torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod

@[simp]
public theorem boundaryTorusWord_nil {n : ℕ} :
    boundaryTorusWord (F := F) (n := n) [] = 1 := rfl

@[simp]
public theorem boundaryTorusWord_cons {n : ℕ}
    (p : Fin n × Fˣ) (L : List (Fin n × Fˣ)) :
    boundaryTorusWord (F := F) (p :: L) =
      torus (R := F) p.1.val n (Nat.ne_of_lt p.1.isLt) p.2 *
        boundaryTorusWord (F := F) L := rfl

/-- Per-index coordinate product from a boundary word list: filter by
`Fin n` equality, map `Prod.snd`, take `List.prod`. No `DecidableEq Fˣ`
required; `n = 0` has no coordinate index. No claim about word reconstruction. -/
public def boundaryTorusCoord {n : ℕ} (i : Fin n)
    (L : List (Fin n × Fˣ)) : Fˣ :=
  ((L.filter (fun p : Fin n × Fˣ => p.1 == i)).map Prod.snd).prod

/-- Permuted boundary torus words differ by a left `torusCocycleSubgroup`
factor. Wrapper around `torus_boundaryWord_perm_of_perm`. -/
public theorem boundaryTorusWord_perm_of_perm {n : ℕ}
    (L₁ L₂ : List (Fin n × Fˣ)) (h : L₁.Perm L₂) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      boundaryTorusWord (F := F) L₁ = c * boundaryTorusWord (F := F) L₂ := by
  simpa [boundaryTorusWord] using torus_boundaryWord_perm_of_perm (F := F) L₁ L₂ h

end BoundaryTorusWordApi

section BoundaryTorusCoordinateCollection

private theorem boundaryTorusCoord_cons {n : ℕ} (k : Fin n) (w : Fˣ)
    (L : List (Fin n × Fˣ)) (i : Fin n) :
    boundaryTorusCoord (F := F) i ((k, w) :: L) =
      if k == i then w * boundaryTorusCoord (F := F) i L
      else boundaryTorusCoord (F := F) i L := by
  simp only [boundaryTorusCoord]
  by_cases h : k == i
  · simp [h]
  · simp [h]

private theorem boundaryTorusProd_all_one {n : ℕ} :
    boundaryTorusProd (F := F) n (fun _ : Fin n => (1 : Fˣ)) = 1 := by
  rw [boundaryTorusProd_eq_finRange]
  simp [torus_one]

private theorem torusCocycle_mem_center_of_mem {c : StableSteinberg F}
    (hc : c ∈ torusCocycleSubgroup (F := F)) :
    c ∈ Subgroup.center (StableSteinberg F) :=
  torusCocycleSubgroup_le_center (F := F) hc

private theorem commute_of_mem_center {c : StableSteinberg F}
    (hc : c ∈ Subgroup.center (StableSteinberg F)) (x : StableSteinberg F) :
    Commute c x := by
  rw [commute_iff_eq]
  exact (Subgroup.mem_center_iff.mp hc x).symm

-- Auxiliary insertion: `torus k w * Prod_{l} torus = c * Prod_{l} (updated)`
private theorem torus_mul_finRange_aux {n : ℕ} (k : Fin n) (w : Fˣ)
    (l : List (Fin n)) (u : Fin n → Fˣ) (hl : l.Nodup) (hk : k ∈ l) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
        (l.map (fun i : Fin n => torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod =
      c * (l.map (fun i : Fin n => torus (R := F) i.val n (Nat.ne_of_lt i.isLt)
        (if k == i then w * u i else u i))).prod := by
  induction l with
  | nil =>
    simp at hk
  | cons i rest ih =>
    have hl_cons : (i :: rest).Nodup := hl
    have hi_not_mem : i ∉ rest := (List.nodup_cons.mp hl_cons).1
    have hl_rest : rest.Nodup := (List.nodup_cons.mp hl_cons).2
    have hk_mem : k ∈ i :: rest := hk
    by_cases h_eq : k = i
    · -- k = i is head: same-index merge, avoid `subst` that erases `i`
      have hk_not_mem_rest : k ∉ rest := by
        intro h_mem
        exact hi_not_mem (h_eq ▸ h_mem)
      have h_same : torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (u k) =
          torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w (u k) *
            torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (w * u k) :=
        torus_mul_eq_torusCocycleAt_mul (F := F) (n := n) (i := k.val) (Nat.ne_of_lt k.isLt) w (u k)
      have hc_mem : torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w (u k) ∈
          torusCocycleSubgroup (F := F) :=
        torusCocycleAt_mem_torusCocycleSubgroup (F := F) k.val n (Nat.ne_of_lt k.isLt) w (u k)
      have h_rest_eq : (rest.map (fun j : Fin n => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
          (if k == j then w * u j else u j))).prod =
          (rest.map (fun j : Fin n =>
              torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod := by
        apply congrArg List.prod
        apply List.map_congr_left
        intro j hj
        have hj_mem : j ∈ rest := hj
        have hj_ne : j ≠ k := fun h => hk_not_mem_rest (h ▸ hj_mem)
        have h_not_beq : ¬ (k == j) := by
          intro h_beq
          have hj_eq : k = j := LawfulBEq.eq_of_beq h_beq
          exact hj_ne hj_eq.symm
        rw [ite_eq_right h_not_beq]
      -- head torus rewrites from `i` to `k` via `h_eq`
      have h_head_eq : torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) =
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (u k) := by
        rw [← h_eq]
      have h_head_upd_eq :
          torus (R := F) i.val n (Nat.ne_of_lt i.isLt)
            (if k == i then w * u i else u i) =
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (w * u k) := by
        have h_beq : (k == i) = true := by rw [h_eq, BEq.rfl]
        rw [ite_eq_left h_beq, ← h_eq]
      have h_left : torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
          ((i :: rest).map (fun j : Fin n =>
              torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod =
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
            torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (u k) *
            (rest.map (fun j : Fin n =>
                torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod := by
        simp only [List.map_cons, List.prod_cons, mul_assoc, h_head_eq]
      have h_right : ((i :: rest).map (fun j : Fin n =>
              torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod =
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) (w * u k) *
            (rest.map (fun j : Fin n =>
                torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod := by
        simp only [List.map_cons, List.prod_cons, h_head_upd_eq, h_rest_eq]
      rw [h_left, h_right, h_same]
      exact ⟨_, hc_mem, by rw [mul_assoc]⟩
    · -- k ≠ i, k ∈ rest
      have hk_rest : k ∈ rest := by
        cases List.mem_cons.mp hk_mem with
        | inl h => exact absurd h h_eq
        | inr h => exact h
      obtain ⟨c_rest, hc_rest_mem, hc_rest_eq⟩ := ih hl_rest hk_rest
      obtain ⟨c_swap, hc_swap_mem, hc_swap_eq⟩ :=
        torus_last_mul_eq_cocycle_mul_swap (F := F) (i := k) (j := i) (u := w) (v := u i)
      -- `c_swap` is `⁅torus k w, torus i (u i)⁆`
      have hc_rest_center := torusCocycle_mem_center_of_mem hc_rest_mem
      have h_comm_rest : Commute c_rest (torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i)) :=
        commute_of_mem_center hc_rest_center (torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))
      have h_not_beq : ¬ (k == i) := by
        intro h_beq
        have h_eq' : k = i := LawfulBEq.eq_of_beq h_beq
        exact h_eq h_eq'
      refine ⟨c_swap * c_rest, (torusCocycleSubgroup (F := F)).mul_mem hc_swap_mem hc_rest_mem, ?_⟩
      calc torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
            ((i :: rest).map (fun j : Fin n =>
                torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod
          = torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
              torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) *
              (rest.map (fun j : Fin n =>
                  torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod := by
            simp [List.map_cons, List.prod_cons, mul_assoc]
        _ = c_swap * torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) *
              torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
              (rest.map (fun j => torus (R := F) j.val n (Nat.ne_of_lt j.isLt) (u j))).prod := by
            rw [hc_swap_eq]
            simp only [mul_assoc]
        _ = c_swap * torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) *
              (c_rest * (rest.map (fun j : Fin n => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod) := by
            have h_congr :=
              congrArg (fun z =>
                (c_swap * torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i)) * z)
                hc_rest_eq
            simpa only [mul_assoc] using h_congr
        _ = c_swap * (torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) * c_rest) *
              (rest.map (fun j : Fin n => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod := by
            simp only [mul_assoc]
        _ = c_swap * (c_rest * torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i)) *
              (rest.map (fun j : Fin n => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod := by
            rw [h_comm_rest.eq.symm]
        _ = (c_swap * c_rest) * torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i) *
              (rest.map (fun j => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod := by
            rw [← mul_assoc c_swap c_rest, mul_assoc]
        _ = (c_swap * c_rest) *
              ((i :: rest).map (fun j : Fin n => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod := by
            have h_cons : ((i :: rest).map (fun j => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                (if k == j then w * u j else u j))).prod =
                torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (if k == i then w * u i else u i) *
                (rest.map (fun j => torus (R := F) j.val n (Nat.ne_of_lt j.isLt)
                  (if k == j then w * u j else u j))).prod := by
              simp [List.map_cons, List.prod_cons]
            rw [h_cons, ite_eq_right h_not_beq]
            simp [mul_assoc]

private theorem torus_mul_boundaryTorusProd {n : ℕ} (k : Fin n) (w : Fˣ)
    (u : Fin n → Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w * boundaryTorusProd (F := F) n u =
      c * boundaryTorusProd (F := F) n (fun i => if k == i then w * u i else u i) := by
  rw [boundaryTorusProd_eq_finRange, boundaryTorusProd_eq_finRange]
  exact torus_mul_finRange_aux (F := F) k w (List.finRange n) u
    (List.nodup_finRange n) (List.mem_finRange k)

/-- Boundary word equals cocycle times canonical product of per-index coordinates.
Pointwise left-defect orientation; `n = 0` via empty product `1`; lawful `BEq (Fin n)`
filtering; `torusCocycleSubgroup` defects only; centrality for reordering. -/
public theorem boundaryTorusWord_eq_cocycle_mul_boundaryTorusProd
    {n : ℕ} (L : List (Fin n × Fˣ)) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      boundaryTorusWord (F := F) L =
        c * boundaryTorusProd (F := F) n
          (fun i => boundaryTorusCoord (F := F) i L) := by
  induction L with
  | nil =>
    refine ⟨1, (torusCocycleSubgroup (F := F)).one_mem, ?_⟩
    have h_coord :
        (fun i : Fin n => boundaryTorusCoord (F := F) i []) =
          fun _ : Fin n => (1 : Fˣ) := by
      funext i
      simp [boundaryTorusCoord]
    simp [boundaryTorusWord, h_coord, boundaryTorusProd_all_one]
  | cons p L' ih =>
    obtain ⟨k, w⟩ := p
    obtain ⟨c', hc'_mem, hc'_eq⟩ := ih
    have h_coord_update : ∀ i : Fin n, boundaryTorusCoord (F := F) i ((k, w) :: L') =
        if k == i then w * boundaryTorusCoord (F := F) i L'
        else boundaryTorusCoord (F := F) i L' :=
      fun i => boundaryTorusCoord_cons (F := F) k w L' i
    -- rewrite word cons
    have h_word_cons : boundaryTorusWord (F := F) ((k, w) :: L') =
        torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w * boundaryTorusWord (F := F) L' := rfl
    rw [h_word_cons, hc'_eq]
    have h_center : c' ∈ Subgroup.center (StableSteinberg F) :=
      torusCocycle_mem_center_of_mem hc'_mem
    have h_comm : Commute c' (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w) :=
      commute_of_mem_center h_center (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)
    -- move `c'` left past `torus k w`
    have h_swap_c' : torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w * c' =
        c' * torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w := by
      rw [h_comm.eq.symm]
    -- need insertion helper
    let u' : Fin n → Fˣ := fun i => boundaryTorusCoord (F := F) i L'
    let u : Fin n → Fˣ := fun i => boundaryTorusCoord (F := F) i ((k, w) :: L')
    have hu_eq : u = fun i => if k == i then w * u' i else u' i := by
      funext i
      exact h_coord_update i
    have h_insert : ∃ c₂ ∈ torusCocycleSubgroup (F := F),
        torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w * boundaryTorusProd (F := F) n u' =
        c₂ * boundaryTorusProd (F := F) n u := by
      have h_u_eq : (fun i => if k == i then w * u' i else u' i) = u := by
        funext i
        rw [hu_eq]
      rw [← h_u_eq]
      exact torus_mul_boundaryTorusProd (F := F) k w u'
    obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ := h_insert
    refine ⟨c' * c₂, (torusCocycleSubgroup (F := F)).mul_mem hc'_mem hc₂_mem, ?_⟩
    calc torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
            (c' * boundaryTorusProd (F := F) n u')
        = (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w * c') *
            boundaryTorusProd (F := F) n u' := by
          rw [← mul_assoc]
      _ = (c' * torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w) *
            boundaryTorusProd (F := F) n u' := by
          rw [h_swap_c']
      _ = c' * (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
            boundaryTorusProd (F := F) n u') := by
          rw [mul_assoc]
      _ = c' * (c₂ * boundaryTorusProd (F := F) n u) := by
          rw [hc₂_eq]
      _ = (c' * c₂) * boundaryTorusProd (F := F) n u := by
          rw [← mul_assoc]

end BoundaryTorusCoordinateCollection

section TorusRankLowering

private theorem torus_inv_conj_x_0i {n i : ℕ} (hi : i < n) (hi0 : 0 < i)
    (u : Fˣ) (a : F) :
    let h0n : 0 ≠ n := Nat.ne_of_lt (Nat.lt_trans hi0 hi)
    let h0i : 0 ≠ i := Nat.ne_of_lt hi0
    (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) 0 i h0i a *
      torus (R := F) 0 n h0n u =
      x (R := F) 0 i h0i ((↑u⁻¹ : F) * a) := by
  intro h0n h0i
  have hn_i : n ≠ i := Ne.symm (Nat.ne_of_lt hi)
  have h_forward : torus (R := F) 0 n h0n u *
      x (R := F) 0 i h0i ((↑u⁻¹ : F) * a) * (torus (R := F) 0 n h0n u)⁻¹ =
      x (R := F) 0 i h0i a := by
    have h_scale : (↑u : F) * ((↑u⁻¹ : F) * a) = a := by
      calc (↑u : F) * ((↑u⁻¹ : F) * a) = ((↑u : F) * (↑u⁻¹ : F)) * a := by rw [mul_assoc]
        _ = ((↑(u * u⁻¹) : F)) * a := by rw [Units.val_mul]
        _ = ((↑(1 : Fˣ) : F)) * a := by rw [mul_inv_cancel]
        _ = (1 : F) * a := by rw [Units.val_one]
        _ = a := by rw [one_mul]
    have h_conj := torus_conj_x_ik (R := F) 0 n i h0n hn_i h0i u ((↑u⁻¹ : F) * a)
    rw [h_scale] at h_conj
    exact h_conj
  calc (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) 0 i h0i a * torus (R := F) 0 n h0n u
      = (torus (R := F) 0 n h0n u)⁻¹ *
        (torus (R := F) 0 n h0n u * x (R := F) 0 i h0i ((↑u⁻¹ : F) * a) *
          (torus (R := F) 0 n h0n u)⁻¹) * torus (R := F) 0 n h0n u := by
        rw [← h_forward]
    _ = x (R := F) 0 i h0i ((↑u⁻¹ : F) * a) := by
        simp [mul_assoc]

private theorem torus_inv_conj_x_i0 {n i : ℕ} (hi : i < n) (hi0 : 0 < i)
    (u : Fˣ) (a : F) :
    let h0n : 0 ≠ n := Nat.ne_of_lt (Nat.lt_trans hi0 hi)
    let h0i : 0 ≠ i := Nat.ne_of_lt hi0
    (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) i 0 h0i.symm a *
      torus (R := F) 0 n h0n u =
      x (R := F) i 0 h0i.symm (a * (↑u : F)) := by
  intro h0n h0i
  have hn_i : n ≠ i := Ne.symm (Nat.ne_of_lt hi)
  have h_forward : torus (R := F) 0 n h0n u *
      x (R := F) i 0 h0i.symm (a * (↑u : F)) * (torus (R := F) 0 n h0n u)⁻¹ =
      x (R := F) i 0 h0i.symm a := by
    have h_scale : (a * (↑u : F)) * (↑u⁻¹ : F) = a := by
      calc (a * (↑u : F)) * (↑u⁻¹ : F) = a * ((↑u : F) * (↑u⁻¹ : F)) := by rw [mul_assoc]
        _ = a * ((↑(u * u⁻¹) : F)) := by rw [Units.val_mul]
        _ = a * ((↑(1 : Fˣ) : F)) := by rw [mul_inv_cancel]
        _ = a * (1 : F) := by rw [Units.val_one]
        _ = a := by rw [mul_one]
    have h_conj := torus_conj_x_ki (R := F) 0 n i h0n hn_i h0i u (a * (↑u : F))
    rw [h_scale] at h_conj
    exact h_conj
  calc (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) i 0 h0i.symm a * torus (R := F) 0 n h0n u
      = (torus (R := F) 0 n h0n u)⁻¹ *
        (torus (R := F) 0 n h0n u * x (R := F) i 0 h0i.symm (a * (↑u : F)) *
          (torus (R := F) 0 n h0n u)⁻¹) * torus (R := F) 0 n h0n u := by
        rw [← h_forward]
    _ = x (R := F) i 0 h0i.symm (a * (↑u : F)) := by
        simp [mul_assoc]

/-- One-factor torus rank lowering: `torus i n u` differs from `torus 0 n u` by a
`finiteStage n` factor. For `i = 0` use `1` and proof irrelevance; for `0 < i`
use `W = weyl 0 i (-1)`, `t = torus 0 n u`, `f = t⁻¹ * W * t * W⁻¹` and expand
`W` into its three roots. -/
public theorem torus_eq_zero_last_mul_finiteStage {n i : ℕ} (hi : i < n) (u : Fˣ) :
    ∃ f ∈ finiteStage (R := F) n,
      torus (R := F) i n (Nat.ne_of_lt hi) u =
        torus (R := F) 0 n (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) u * f := by
  have h0n : 0 ≠ n := Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  by_cases h_i0 : i = 0
  · subst h_i0
    have h_eq : (Nat.ne_of_lt hi) = h0n := Subsingleton.elim _ _
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [mul_one, h_eq]
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero h_i0
    have h0i : 0 ≠ i := Nat.ne_of_lt hi_pos
    have hn_i : n ≠ i := Ne.symm (Nat.ne_of_lt hi)
    let t := torus (R := F) 0 n h0n u
    let W := weyl (R := F) 0 i h0i (-1 : Fˣ)
    have h_conj : W * t * W⁻¹ = torus (R := F) i n (Nat.ne_of_lt hi) u :=
      torus_conj_w_ik (R := F) 0 n i h0n h0i (Nat.ne_of_lt hi) u
    have hW_eq : W =
        x (R := F) 0 i h0i (-1 : F) *
        x (R := F) i 0 h0i.symm (1 : F) *
        x (R := F) 0 i h0i (-1 : F) := by
      unfold W weyl
      have h_coe : (↑(-1 : Fˣ) : F) = (-1 : F) := by simp
      have h_mid : (-(↑(-1 : Fˣ)⁻¹ : F)) = (1 : F) := by
        have h_inv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by ext; simp
        rw [h_inv, h_coe, neg_neg]
      rw [h_coe, h_mid]
    have h_t_inv_conj_W : t⁻¹ * W * t =
        x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) *
        x (R := F) i 0 h0i.symm ((1 : F) * (↑u : F)) *
        x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) := by
      have h1 : t⁻¹ * x (R := F) 0 i h0i (-1 : F) * t =
          x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) :=
        torus_inv_conj_x_0i (F := F) hi hi_pos u (-1 : F)
      have h2 : t⁻¹ * x (R := F) i 0 h0i.symm (1 : F) * t =
          x (R := F) i 0 h0i.symm ((1 : F) * (↑u : F)) :=
        torus_inv_conj_x_i0 (F := F) hi hi_pos u (1 : F)
      calc t⁻¹ * W * t
          = t⁻¹ * (x (R := F) 0 i h0i (-1 : F) *
            x (R := F) i 0 h0i.symm (1 : F) * x (R := F) 0 i h0i (-1 : F)) * t := by
            rw [hW_eq]
        _ = (t⁻¹ * x (R := F) 0 i h0i (-1 : F) * t) *
            (t⁻¹ * x (R := F) i 0 h0i.symm (1 : F) * t) *
            (t⁻¹ * x (R := F) 0 i h0i (-1 : F) * t) := by
            simp [mul_assoc]
        _ = x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) *
            x (R := F) i 0 h0i.symm ((1 : F) * (↑u : F)) *
            x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) := by
            rw [h1, h2]
    have h0_lt_n : 0 < n := Nat.lt_trans hi_pos hi
    have hx1_mem : x (R := F) 0 i h0i (-1 : F) ∈ finiteStage (R := F) n :=
      x_mem_finiteStage (R := F) h0_lt_n hi
    have hx2_mem : x (R := F) i 0 h0i.symm (1 : F) ∈ finiteStage (R := F) n :=
      x_mem_finiteStage (R := F) hi h0_lt_n
    have hW_mem : W ∈ finiteStage (R := F) n := by
      rw [hW_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx1_mem hx2_mem) hx1_mem
    have hx1u_mem : x (R := F) 0 i h0i ((↑u⁻¹ : F) * (-1 : F)) ∈ finiteStage (R := F) n :=
      x_mem_finiteStage (R := F) h0_lt_n hi
    have hx2u_mem : x (R := F) i 0 h0i.symm ((1 : F) * (↑u : F)) ∈ finiteStage (R := F) n :=
      x_mem_finiteStage (R := F) hi h0_lt_n
    have hWt_mem : t⁻¹ * W * t ∈ finiteStage (R := F) n := by
      rw [h_t_inv_conj_W]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx1u_mem hx2u_mem) hx1u_mem
    have hWinv_mem : W⁻¹ ∈ finiteStage (R := F) n :=
      Subgroup.inv_mem _ hW_mem
    let f := t⁻¹ * W * t * W⁻¹
    have hf_mem : f ∈ finiteStage (R := F) n :=
      Subgroup.mul_mem _ hWt_mem hWinv_mem
    refine ⟨f, hf_mem, ?_⟩
    have h_tf : t * f = W * t * W⁻¹ := by
      simp [f, mul_assoc]
    rw [← h_conj, ← h_tf]

end TorusRankLowering

section TorusZeroLastNormalizer

private theorem torus_comm_of_disjoint_x {n p q : ℕ} (hn : 0 < n)
    (hp : p < n) (hq : q < n) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hij : p ≠ q)
    (u : Fˣ) (a : F) :
    Commute (torus (R := F) 0 n (Nat.ne_of_lt hn) u)
      (x (R := F) p q hij a) := by
  have h0n : 0 ≠ n := Nat.ne_of_lt hn
  have hpn : p ≠ n := Nat.ne_of_lt hp
  have hqn : q ≠ n := Nat.ne_of_lt hq
  have h0q : (0 : ℕ) ≠ q := Ne.symm hq0
  have h0p : (0 : ℕ) ≠ p := Ne.symm hp0
  have hnq : n ≠ q := Ne.symm hqn
  have hnp : n ≠ p := Ne.symm hpn
  have hn0 : n ≠ 0 := Ne.symm h0n
  have h_comm_0n_u : Commute (x (R := F) 0 n h0n (↑u : F))
      (x (R := F) p q hij a) := by
    rw [commute_iff_eq]
    have h := x_comm (R := F) 0 n p q h0n hij h0q hnp (↑u : F) a
    exact (commutatorElement_eq_one_iff_commute.mp h).eq
  have h_comm_n0_u : Commute (x (R := F) n 0 hn0 (-(↑u⁻¹ : F)))
      (x (R := F) p q hij a) := by
    rw [commute_iff_eq]
    have h := x_comm (R := F) n 0 p q hn0 hij hnq h0p (-(↑u⁻¹ : F)) a
    exact (commutatorElement_eq_one_iff_commute.mp h).eq
  have h_comm_0n_1 : Commute (x (R := F) 0 n h0n (-1 : F))
      (x (R := F) p q hij a) := by
    rw [commute_iff_eq]
    have h := x_comm (R := F) 0 n p q h0n hij h0q hnp (-1 : F) a
    exact (commutatorElement_eq_one_iff_commute.mp h).eq
  have h_comm_n0_1 : Commute (x (R := F) n 0 hn0 (1 : F))
      (x (R := F) p q hij a) := by
    rw [commute_iff_eq]
    have h := x_comm (R := F) n 0 p q hn0 hij hnq h0p (1 : F) a
    exact (commutatorElement_eq_one_iff_commute.mp h).eq
  have hW_u : Commute (weyl (R := F) 0 n h0n u)
      (x (R := F) p q hij a) := by
    unfold weyl
    have h1 : Commute (x (R := F) 0 n h0n (↑u : F) *
        x (R := F) n 0 hn0 (-(↑u⁻¹ : F)))
        (x (R := F) p q hij a) :=
      Commute.mul_left h_comm_0n_u h_comm_n0_u
    exact Commute.mul_left h1 h_comm_0n_u
  have hW_m1 : Commute (weyl (R := F) 0 n h0n (-1 : Fˣ))
      (x (R := F) p q hij a) := by
    unfold weyl
    have h_coe : (↑(-1 : Fˣ) : F) = (-1 : F) := by simp
    have h_inv : (-(↑(-1 : Fˣ)⁻¹ : F)) = (1 : F) := by
      have h : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by ext; simp
      rw [h, h_coe, neg_neg]
    rw [h_coe, h_inv]
    have h1 : Commute (x (R := F) 0 n h0n (-1 : F) *
        x (R := F) n 0 hn0 (1 : F))
        (x (R := F) p q hij a) :=
      Commute.mul_left h_comm_0n_1 h_comm_n0_1
    exact Commute.mul_left h1 h_comm_0n_1
  unfold torus
  exact Commute.mul_left hW_u hW_m1

private theorem torus_zero_last_conj_x_mem {n p q : ℕ} (hn : 0 < n)
    (hp : p < n) (hq : q < n) (hij : p ≠ q) (u : Fˣ) (a : F) :
    let h0n : 0 ≠ n := Nat.ne_of_lt hn
    torus (R := F) 0 n h0n u * x (R := F) p q hij a *
      (torus (R := F) 0 n h0n u)⁻¹ ∈ finiteStage (R := F) n := by
  intro h0n
  by_cases h_p0 : p = 0
  · subst h_p0
    have h0q : (0 : ℕ) ≠ q := hij
    have hnq : n ≠ q := Ne.symm (Nat.ne_of_lt hq)
    have h_conj := torus_conj_x_ik (R := F) 0 n q h0n hnq h0q u a
    rw [h_conj]
    exact x_mem_finiteStage (R := F) hn hq
  · by_cases h_q0 : q = 0
    · subst h_q0
      have hn_p : n ≠ p := Ne.symm (Nat.ne_of_lt hp)
      have h0p : (0 : ℕ) ≠ p := Ne.symm h_p0
      have h_conj := torus_conj_x_ki (R := F) 0 n p h0n hn_p h0p u a
      rw [h_conj]
      exact x_mem_finiteStage (R := F) hp hn
    · have h_comm := torus_comm_of_disjoint_x (F := F) hn hp hq h_p0 h_q0 hij u a
      have h_eq : torus (R := F) 0 n h0n u * x (R := F) p q hij a *
          (torus (R := F) 0 n h0n u)⁻¹ = x (R := F) p q hij a :=
        h_comm.mul_inv_cancel
      rw [h_eq]
      exact Subgroup.subset_closure ⟨p, q, hij, a, rfl, hp, hq⟩

private theorem torus_zero_last_inv_conj_x_mem {n p q : ℕ} (hn : 0 < n)
    (hp : p < n) (hq : q < n) (hij : p ≠ q) (u : Fˣ) (a : F) :
    let h0n : 0 ≠ n := Nat.ne_of_lt hn
    (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) p q hij a *
      torus (R := F) 0 n h0n u ∈ finiteStage (R := F) n := by
  intro h0n
  by_cases h_p0 : p = 0
  · subst h_p0
    have h0q : (0 : ℕ) ≠ q := hij
    have hnq : n ≠ q := Ne.symm (Nat.ne_of_lt hq)
    let t := torus (R := F) 0 n h0n u
    have h_forward : t * x (R := F) 0 q hij ((↑u⁻¹ : F) * a) * t⁻¹ =
        x (R := F) 0 q hij a := by
      have h_conj := torus_conj_x_ik (R := F) 0 n q h0n hnq h0q u ((↑u⁻¹ : F) * a)
      have h_scale : (↑u : F) * ((↑u⁻¹ : F) * a) = a := by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          one_mul]
      calc t * x (R := F) 0 q hij ((↑u⁻¹ : F) * a) * t⁻¹
          = x (R := F) 0 q hij ((↑u : F) * ((↑u⁻¹ : F) * a)) := h_conj
        _ = x (R := F) 0 q hij a := by rw [h_scale]
    have h_eq : t⁻¹ * x (R := F) 0 q hij a * t =
        x (R := F) 0 q hij ((↑u⁻¹ : F) * a) := by
      calc t⁻¹ * x (R := F) 0 q hij a * t
          = t⁻¹ * (t * x (R := F) 0 q hij ((↑u⁻¹ : F) * a) * t⁻¹) * t := by
            rw [h_forward]
        _ = x (R := F) 0 q hij ((↑u⁻¹ : F) * a) := by simp [mul_assoc]
    rw [h_eq]
    exact x_mem_finiteStage (R := F) hn hq
  · by_cases h_q0 : q = 0
    · subst h_q0
      have h0p : (0 : ℕ) ≠ p := Ne.symm h_p0
      have hnp : n ≠ p := Ne.symm (Nat.ne_of_lt hp)
      let t := torus (R := F) 0 n h0n u
      have h_forward : t * x (R := F) p 0 hij (a * (↑u : F)) * t⁻¹ =
          x (R := F) p 0 hij a := by
        have h_conj := torus_conj_x_ki (R := F) 0 n p h0n hnp h0p u (a * (↑u : F))
        have h_scale : (a * (↑u : F)) * (↑u⁻¹ : F) = a := by
          rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            mul_one]
        calc t * x (R := F) p 0 hij (a * (↑u : F)) * t⁻¹
            = x (R := F) p 0 hij ((a * (↑u : F)) * (↑u⁻¹ : F)) := h_conj
          _ = x (R := F) p 0 hij a := by rw [h_scale]
      have h_eq : t⁻¹ * x (R := F) p 0 hij a * t =
          x (R := F) p 0 hij (a * (↑u : F)) := by
        calc t⁻¹ * x (R := F) p 0 hij a * t
            = t⁻¹ * (t * x (R := F) p 0 hij (a * (↑u : F)) * t⁻¹) * t := by
              rw [h_forward]
          _ = x (R := F) p 0 hij (a * (↑u : F)) := by simp [mul_assoc]
      rw [h_eq]
      exact x_mem_finiteStage (R := F) hp hn
    · have h_comm := torus_comm_of_disjoint_x (F := F) hn hp hq h_p0 h_q0 hij u a
      have h_eq' : (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) p q hij a *
          torus (R := F) 0 n h0n u = x (R := F) p q hij a := by
        calc (torus (R := F) 0 n h0n u)⁻¹ * x (R := F) p q hij a *
            torus (R := F) 0 n h0n u
            = (torus (R := F) 0 n h0n u)⁻¹ *
              (torus (R := F) 0 n h0n u * x (R := F) p q hij a *
                (torus (R := F) 0 n h0n u)⁻¹) *
              torus (R := F) 0 n h0n u := by
              rw [h_comm.mul_inv_cancel]
            _ = x (R := F) p q hij a := by simp [mul_assoc]
      rw [h_eq']
      exact Subgroup.subset_closure ⟨p, q, hij, a, rfl, hp, hq⟩

/-- Common-base torus normalizes the lower finite stage.

For `0 < n` and `u : Fˣ`, `torus 0 n u` normalizes `finiteStage n`.
For a generator `x p q a` with `p,q < n`, split on `p = 0` and `q = 0`:
use `torus_conj_x_ik` for `x 0 q`, `torus_conj_x_ki` for `x p 0`,
and `torus`/`weyl` unfolding plus `x_comm` when both are disjoint from
`0,n`. Both directions of `mem_normalizer_iff` hold; the inverse direction
uses inverse coefficient rescaling. Every resulting root keeps both indices
`< n`. -/
public theorem torus_zero_last_mem_normalizer_finiteStage {n : ℕ}
    (hn : 0 < n) (u : Fˣ) :
    torus (R := F) 0 n (Nat.ne_of_lt hn) u ∈
      Subgroup.normalizer (finiteStage (R := F) n) := by
  let h0n : 0 ≠ n := Nat.ne_of_lt hn
  let t := torus (R := F) 0 n h0n u
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨p, q, hij, a, rfl, hp, hq⟩ := hy
      exact torus_zero_last_conj_x_mem (F := F) hn hp hq hij u a
    | one => simp
    | mul g1 g2 _ _ ih1 ih2 =>
      have h_eq : t * (g1 * g2) * t⁻¹ = (t * g1 * t⁻¹) * (t * g2 * t⁻¹) := by
        simp [mul_assoc]
      rw [h_eq]
      exact Subgroup.mul_mem _ ih1 ih2
    | inv g _ ih =>
      have h_eq : t * g⁻¹ * t⁻¹ = (t * g * t⁻¹)⁻¹ := by
        simp [mul_assoc]
      rw [h_eq]
      exact Subgroup.inv_mem _ ih
  · intro hg
    have h_inv_conj_mem : ∀ h ∈ finiteStage (R := F) n,
        t⁻¹ * h * t ∈ finiteStage (R := F) n := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨p, q, hij, a, rfl, hp, hq⟩ := hy
        exact torus_zero_last_inv_conj_x_mem (F := F) hn hp hq hij u a
      | one => simp
      | mul g1 g2 _ _ ih1 ih2 =>
        have h_eq : t⁻¹ * (g1 * g2) * t = (t⁻¹ * g1 * t) * (t⁻¹ * g2 * t) := by
          simp [mul_assoc]
        rw [h_eq]
        exact Subgroup.mul_mem _ ih1 ih2
      | inv g _ ih =>
        have h_eq : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by
          simp [mul_assoc]
        rw [h_eq]
        exact Subgroup.inv_mem _ ih
    have h_mem : t⁻¹ * (t * g * t⁻¹) * t ∈ finiteStage (R := F) n :=
      h_inv_conj_mem (t * g * t⁻¹) hg
    have h_eq : t⁻¹ * (t * g * t⁻¹) * t = g := by simp [mul_assoc]
    rw [h_eq] at h_mem
    exact h_mem

/-- Arbitrary-index torus normalizer membership.

For any `i < n` and `u : Fˣ`, the torus `torus i n u` lies in the normalizer of
`finiteStage n`. Uses `torus_eq_zero_last_mul_finiteStage` to write
`torus i n u = torus 0 n u * f` with `f ∈ finiteStage n`, the common-base
`torus_zero_last_mem_normalizer_finiteStage` at `0 < n` for the `torus 0 n`
factor (up to proof irrelevance for the `0 ≠ n` witness), `Subgroup.le_normalizer`
for the `finiteStage` factor, and closure of the normalizer subgroup under
multiplication. Generic in the existing field section; valid for all `i < n`
including `i = 0`. No claim of membership in `finiteStage n`, centrality,
absorption, kernel generation, or Matsumoto. -/
public theorem torus_mem_normalizer_finiteStage {n i : ℕ}
    (hi : i < n) (u : Fˣ) :
    torus (R := F) i n (Nat.ne_of_lt hi) u ∈
      Subgroup.normalizer (finiteStage (R := F) n) := by
  have h0_lt_n : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have h0_norm : torus (R := F) 0 n (Nat.ne_of_lt h0_lt_n) u ∈
      Subgroup.normalizer (finiteStage (R := F) n) :=
    torus_zero_last_mem_normalizer_finiteStage (F := F) h0_lt_n u
  obtain ⟨f, hf_mem, hf_eq⟩ :=
    torus_eq_zero_last_mul_finiteStage (F := F) hi u
  have h_proof_eq :
      Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le i) hi) =
        Nat.ne_of_lt h0_lt_n :=
    Subsingleton.elim _ _
  rw [h_proof_eq] at hf_eq
  have hf_norm : f ∈ Subgroup.normalizer (finiteStage (R := F) n) :=
    (finiteStage (R := F) n).le_normalizer hf_mem
  have h_mul_mem : torus (R := F) 0 n (Nat.ne_of_lt h0_lt_n) u * f ∈
      Subgroup.normalizer (finiteStage (R := F) n) :=
    Subgroup.mul_mem _ h0_norm hf_norm
  rw [← hf_eq] at h_mul_mem
  exact h_mul_mem

end TorusZeroLastNormalizer

section BoundaryTorusProductOne

private theorem aux_list_eq_torus_zero_prod {n : ℕ} (hn : 0 < n)
    (u : Fin n → Fˣ) (l : List (Fin n)) :
    ∃ f ∈ finiteStage (R := F) n,
      (l.map (fun i : Fin n =>
        torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod =
      (l.map (fun i : Fin n =>
        torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod * f := by
  induction l with
  | nil =>
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | cons hd tl ih =>
    obtain ⟨f_tl, hf_tl_mem, hf_tl_eq⟩ := ih
    obtain ⟨f_hd, hf_hd_mem, hf_hd_eq⟩ :=
      torus_eq_zero_last_mul_finiteStage (F := F) hd.isLt (u hd)
    have h_proof_eq : Nat.ne_of_lt
        (Nat.lt_of_le_of_lt (Nat.zero_le hd.val) hd.isLt) =
        Nat.ne_of_lt hn :=
      Subsingleton.elim _ _
    rw [h_proof_eq] at hf_hd_eq
    have h_norm_each : ∀ i : Fin n,
        torus (R := F) 0 n (Nat.ne_of_lt hn) (u i) ∈
          Subgroup.normalizer (finiteStage (R := F) n) :=
      fun i => torus_zero_last_mem_normalizer_finiteStage (F := F) hn (u i)
    have h_prod_mem : ∀ t : List (Fin n),
        (t.map (fun i : Fin n =>
          torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod ∈
          Subgroup.normalizer (finiteStage (R := F) n) := by
      intro t
      induction t with
      | nil => simp
      | cons hd2 tl2 ih2 =>
        simp only [List.map_cons, List.prod_cons]
        exact Subgroup.mul_mem _ (h_norm_each hd2) ih2
    have h_rest0_mem :
        (tl.map (fun i : Fin n =>
          torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod ∈
          Subgroup.normalizer (finiteStage (R := F) n) :=
      h_prod_mem tl
    have h_rest0_inv_mem :
        ((tl.map (fun i : Fin n =>
          torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod)⁻¹ ∈
          Subgroup.normalizer (finiteStage (R := F) n) :=
      Subgroup.inv_mem _ h_rest0_mem
    let rest0 :=
      (tl.map (fun i : Fin n =>
        torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod
    have hf_hd'_mem :
        rest0⁻¹ * f_hd * rest0 ∈ finiteStage (R := F) n := by
      have h_iff := Subgroup.mem_normalizer_iff.mp h_rest0_inv_mem f_hd
      have hmem := h_iff.mp hf_hd_mem
      simpa [inv_inv] using hmem
    let f_hd' := rest0⁻¹ * f_hd * rest0
    have h_move : f_hd * rest0 = rest0 * f_hd' := by
      simp only [f_hd', rest0]
      calc f_hd * rest0
          = rest0 * (rest0⁻¹ * f_hd * rest0) := by
            calc f_hd * rest0
                = (rest0 * rest0⁻¹) * f_hd * rest0 := by
                  simp
              _ = rest0 * (rest0⁻¹ * f_hd * rest0) := by
                  simp [mul_assoc]
          _ = rest0 * f_hd' := rfl
    refine ⟨f_hd' * f_tl, Subgroup.mul_mem _ hf_hd'_mem hf_tl_mem, ?_⟩
    have h_head : torus (R := F) hd.val n (Nat.ne_of_lt hd.isLt) (u hd) =
        torus (R := F) 0 n (Nat.ne_of_lt hn) (u hd) * f_hd :=
      hf_hd_eq
    calc (List.map (fun i : Fin n =>
          torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i)) (hd :: tl)).prod
        = torus (R := F) hd.val n (Nat.ne_of_lt hd.isLt) (u hd) *
          (tl.map (fun i : Fin n =>
            torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod := by
          simp [List.map_cons, List.prod_cons]
      _ = (torus (R := F) 0 n (Nat.ne_of_lt hn) (u hd) * f_hd) *
          (rest0 * f_tl) := by
          rw [h_head, hf_tl_eq]
      _ = torus (R := F) 0 n (Nat.ne_of_lt hn) (u hd) * (f_hd * rest0) * f_tl := by
          simp [rest0, mul_assoc]
      _ = torus (R := F) 0 n (Nat.ne_of_lt hn) (u hd) * (rest0 * f_hd') * f_tl := by
          rw [h_move]
      _ = (torus (R := F) 0 n (Nat.ne_of_lt hn) (u hd) * rest0) * (f_hd' * f_tl) := by
          simp [mul_assoc]
      _ = ((hd :: tl).map (fun i : Fin n =>
          torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod * (f_hd' * f_tl) := by
          simp [rest0, List.map_cons, List.prod_cons, mul_assoc]

private theorem finRange_torusProd_eq_torusZeroProd_mul_finiteStage
    {n : ℕ} (hn : 0 < n) (u : Fin n → Fˣ) :
    ∃ f ∈ finiteStage (R := F) n,
      ((List.finRange n).map
          (fun i : Fin n => torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod =
        ((List.finRange n).map
          (fun i : Fin n => torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod * f :=
  aux_list_eq_torus_zero_prod (F := F) hn u (List.finRange n)

private theorem boundaryTorusProd_eq_cocycle_mul_torus_zero_mul_finiteStage
    {n : ℕ} (hn : 0 < n) (u : Fin n → Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      ∃ f ∈ finiteStage (R := F) n,
        boundaryTorusProd (F := F) n u =
          c * torus (R := F) 0 n (Nat.ne_of_lt hn) (∏ i, u i) * f := by
  have h_eq_finRange :
      boundaryTorusProd (F := F) n u =
        ((List.finRange n).map
          (fun i : Fin n => torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod := by
    rw [boundaryTorusProd_eq_finRange]
  obtain ⟨f1, hf1_mem, hf1_eq⟩ :=
    finRange_torusProd_eq_torusZeroProd_mul_finiteStage (F := F) hn u
  rw [h_eq_finRange, hf1_eq]
  let us : List Fˣ := List.ofFn u
  have h_us_prod : us.prod = ∏ i, u i := by
    rw [List.prod_ofFn]
  have h_map_eq :
      ((List.finRange n).map
        (fun i : Fin n => torus (R := F) 0 n (Nat.ne_of_lt hn) (u i))).prod =
      (us.map (torus (R := F) 0 n (Nat.ne_of_lt hn))).prod := by
    have h_ofFn : us = (List.finRange n).map u := by
      simp [us, List.ofFn_eq_map]
    rw [h_ofFn, List.map_map]
    rfl
  rw [h_map_eq]
  have h_same := torus_sameIndex_list (F := F) (n := n) (i := 0)
    (Nat.ne_of_lt hn) us
  rw [h_same]
  have hc_mem : sameIndexCocycleList (F := F) (Nat.ne_of_lt hn) us ∈
      torusCocycleSubgroup (F := F) :=
    sameIndexCocycleList_mem_torusCocycleSubgroup (F := F) (Nat.ne_of_lt hn) us
  rw [h_us_prod]
  refine ⟨sameIndexCocycleList (F := F) (Nat.ne_of_lt hn) us, hc_mem, f1, hf1_mem, ?_⟩
  simp [mul_assoc]

/-- For `u : Fin n → Fˣ` with `∏ i, u i = 1`, `boundaryTorusProd n u`
factors as `c * f` with `c ∈ torusCocycleSubgroup` on the left and
`f ∈ finiteStage n` on the right (`cocycle * finiteStage` order).
For `n = 0` the product is `1` by `boundaryTorusProd_zero`. Neither factor
is claimed trivial, and the theorem does not claim membership in the cocycle
subgroup alone nor in `ker toStableE`. -/
public theorem boundaryTorusProd_eq_cocycle_mul_finiteStage_of_prod_eq_one
    {n : ℕ} (u : Fin n → Fˣ) (hprod : ∏ i, u i = 1) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      ∃ f ∈ finiteStage (R := F) n,
        boundaryTorusProd (F := F) n u = c * f := by
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : boundaryTorusProd (F := F) 0 u = 1 :=
      boundaryTorusProd_zero (F := F) u
    refine ⟨1, (torusCocycleSubgroup (F := F)).one_mem, 1,
      (finiteStage (R := F) 0).one_mem, ?_⟩
    rw [h0, mul_one]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨c, hc, f, hf, h_eq⟩ :=
      boundaryTorusProd_eq_cocycle_mul_torus_zero_mul_finiteStage (F := F) hn u
    have h_torus_one :
        torus (R := F) 0 n (Nat.ne_of_lt hn) (∏ i, u i) = 1 := by
      rw [hprod, torus_one]
    rw [h_torus_one, mul_one] at h_eq
    exact ⟨c, hc, f, hf, h_eq⟩

end BoundaryTorusProductOne

section BoundaryTorusWordKernel

private theorem boundaryTorusWord_prod_eq_one_of_mem_ker {n : ℕ}
    (L : List (Fin n × Fˣ))
    (u : Fin n → Fˣ)
    (c : StableSteinberg F) (hc : c ∈ torusCocycleSubgroup (F := F))
    (h_eq : boundaryTorusWord (F := F) L = c * boundaryTorusProd (F := F) n u)
    (hker : boundaryTorusWord (F := F) L ∈ MonoidHom.ker (toStableE (R := F))) :
    Finset.univ.prod u = 1 := by
  have h_word_one : toStableE (R := F) (boundaryTorusWord (F := F) L) = 1 :=
    MonoidHom.mem_ker.mp hker
  have hc_one : toStableE (R := F) c = 1 :=
    MonoidHom.mem_ker.mp (torusCocycleSubgroup_le_ker_toStableE (F := F) hc)
  have h_to_prod : toStableE (R := F) (boundaryTorusProd (F := F) n u) = 1 := by
    have h_to_eq : toStableE (R := F) (c * boundaryTorusProd (F := F) n u) = 1 := by
      rw [← h_eq, h_word_one]
    rw [map_mul, hc_one, one_mul] at h_to_eq
    exact h_to_eq
  have h_pi : toStableE_torus_fin_last_piHom (F := F) n u = 1 := by
    rw [← toStableE_boundaryTorusProd (F := F) n u, h_to_prod]
  have h_range : toStableE_torus_fin_last_piHom (F := F) n u ∈
      Set.range (StableE.fromFinite F n) := by
    rw [h_pi]
    exact ⟨1, map_one (StableE.fromFinite F n)⟩
  exact (toStableE_torus_fin_last_piHom_mem_range_iff (F := F) n u).mp h_range

/-- Kernel boundary-word rank reduction: a boundary word in `ker toStableE`
factors as left `torusCocycleSubgroup` times right `finiteStage n`.
Covers `n = 0` via empty product, preserves `c * f` order, and makes no
product-one-only cocycle claim. -/
public theorem boundaryTorusWord_eq_cocycle_mul_finiteStage_of_mem_ker
    {n : ℕ} (L : List (Fin n × Fˣ))
    (hker : boundaryTorusWord (F := F) L ∈ MonoidHom.ker (toStableE (R := F))) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      ∃ f ∈ finiteStage (R := F) n,
        boundaryTorusWord (F := F) L = c * f := by
  obtain ⟨c₁, hc₁, h_eq₁⟩ :=
    boundaryTorusWord_eq_cocycle_mul_boundaryTorusProd (F := F) L
  let u : Fin n → Fˣ := fun i => boundaryTorusCoord (F := F) i L
  have h_prod_one : Finset.univ.prod u = 1 :=
    boundaryTorusWord_prod_eq_one_of_mem_ker (F := F) L u c₁ hc₁ h_eq₁ hker
  obtain ⟨c₂, hc₂, f, hf, h_eq₂⟩ :=
    boundaryTorusProd_eq_cocycle_mul_finiteStage_of_prod_eq_one (F := F) u h_prod_one
  refine ⟨c₁ * c₂, (torusCocycleSubgroup (F := F)).mul_mem hc₁ hc₂, f, hf, ?_⟩
  calc boundaryTorusWord (F := F) L
      = c₁ * boundaryTorusProd (F := F) n u := h_eq₁
    _ = c₁ * (c₂ * f) := by rw [h_eq₂]
    _ = (c₁ * c₂) * f := by rw [mul_assoc]

end BoundaryTorusWordKernel

section SamePairWeylProduct

/-- Same-pair Weyl product modulo the torus cocycle.

Hypotheses: `[Field F]`, distinct indices `i ≠ j` (`hij`), units `p q : Fˣ`.

Exact orientation: `weyl i j p * weyl i j q = c * torus i j ((-p) * q⁻¹)`
with the cocycle defect `c ∈ torusCocycleSubgroup` exhibited on the left.

Purpose: supplies the mixed Weyl/torus transport step that rewrites an
arbitrary same-pair Weyl product as a left central defect times a torus word;
downstream conjugation then moves torus words across Weyl words.

Nonclaims: no defect triviality (`c = 1` is false in general), no Weyl
conjugation theorem, no ordered torus normal form, no `C ≤ H`, no TWT
closure, no kernel generation, and no Matsumoto comparison or isomorphism. -/
public theorem weyl_samePair_mul_eq_cocycle_mul_torus (i j : ℕ)
    (hij : i ≠ j) (p q : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      weyl (R := F) i j hij p * weyl (R := F) i j hij q =
        c * torus (R := F) i j hij ((-p) * q⁻¹) := by
  have hneg1 := weyl_neg_eq_inv (R := F) i j hij (1 : Fˣ)
  have hW1 : (weyl (R := F) i j hij (-1 : Fˣ))⁻¹ =
      weyl (R := F) i j hij (1 : Fˣ) := by
    rw [hneg1, inv_inv]
  have hWq : weyl (R := F) i j hij (-q) =
      (weyl (R := F) i j hij q)⁻¹ :=
    weyl_neg_eq_inv (R := F) i j hij q
  have hWqInv : (weyl (R := F) i j hij (-q))⁻¹ =
      weyl (R := F) i j hij q := by
    rw [hWq, inv_inv]
  have hHp : torus (R := F) i j hij p =
      weyl (R := F) i j hij p * weyl (R := F) i j hij (-1 : Fˣ) := rfl
  have hHnq : torus (R := F) i j hij (-q) =
      weyl (R := F) i j hij (-q) *
        weyl (R := F) i j hij (-1 : Fˣ) := rfl
  have hInvNq : (torus (R := F) i j hij (-q))⁻¹ =
      weyl (R := F) i j hij (1 : Fˣ) * weyl (R := F) i j hij q := by
    calc (torus (R := F) i j hij (-q))⁻¹
        = (weyl (R := F) i j hij (-q) *
          weyl (R := F) i j hij (-1 : Fˣ))⁻¹ := by
          rw [hHnq]
      _ = (weyl (R := F) i j hij (-1 : Fˣ))⁻¹ *
          (weyl (R := F) i j hij (-q))⁻¹ := by
          rw [mul_inv_rev]
      _ = weyl (R := F) i j hij (1 : Fˣ) *
          weyl (R := F) i j hij q := by
          rw [hW1, hWqInv]
  have hProd : weyl (R := F) i j hij p * weyl (R := F) i j hij q =
      torus (R := F) i j hij p * (torus (R := F) i j hij (-q))⁻¹ := by
    rw [hHp, hInvNq, ← hW1]
    have hinner : weyl (R := F) i j hij (-1 : Fˣ) *
        ((weyl (R := F) i j hij (-1 : Fˣ))⁻¹ *
          weyl (R := F) i j hij q) =
        weyl (R := F) i j hij q := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc weyl (R := F) i j hij p * weyl (R := F) i j hij q
        = weyl (R := F) i j hij p *
          (weyl (R := F) i j hij (-1 : Fˣ) *
            ((weyl (R := F) i j hij (-1 : Fˣ))⁻¹ *
              weyl (R := F) i j hij q)) := by
          rw [hinner]
      _ = (weyl (R := F) i j hij p *
          weyl (R := F) i j hij (-1 : Fˣ)) *
          ((weyl (R := F) i j hij (-1 : Fˣ))⁻¹ *
            weyl (R := F) i j hij q) := by
          rw [mul_assoc]
  have hNegInv : (-q)⁻¹ = -(q⁻¹ : Fˣ) := by
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val]
    change ((-(q : Fˣ) : F))⁻¹ = (-((q⁻¹ : Fˣ) : F))
    rw [show ((-(q : Fˣ) : F)) = (-((q : Fˣ) : F)) from rfl]
    rw [show (((q⁻¹ : Fˣ) : F)) = (((q : Fˣ) : F))⁻¹ from
      Units.val_inv_eq_inv_val _]
    exact neg_inv.symm
  have hMulEq : p * (-(q⁻¹ : Fˣ)) = (-p) * q⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul]
    change ((p : Fˣ) : F) * ((-(q⁻¹ : Fˣ) : F)) =
      ((-(p : Fˣ) : F)) * (((q⁻¹ : Fˣ) : F))
    rw [show ((-(q⁻¹ : Fˣ) : F)) = (-(((q⁻¹ : Fˣ) : F))) from rfl]
    rw [show ((-(p : Fˣ) : F)) = (-(((p : Fˣ) : F))) from rfl]
    rw [show (((q⁻¹ : Fˣ) : F)) = ((((q : Fˣ) : F))⁻¹) from
      Units.val_inv_eq_inv_val _]
    rw [mul_neg, neg_mul]
  have hC3mem : torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) ∈
      torusCocycleSubgroup (F := F) :=
    torusCocycleAt_mem_torusCocycleSubgroup i j hij (-q) (-(q⁻¹ : Fˣ))
  have hC4mem : torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) ∈
      torusCocycleSubgroup (F := F) :=
    torusCocycleAt_mem_torusCocycleSubgroup i j hij p (-(q⁻¹ : Fˣ))
  have hMulNq : torus (R := F) i j hij (-q) *
      torus (R := F) i j hij (-(q⁻¹ : Fˣ)) =
      torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) *
        torus (R := F) i j hij ((-q) * (-(q⁻¹ : Fˣ))) :=
    torus_mul_eq_torusCocycleAt_mul hij (-q) (-(q⁻¹ : Fˣ))
  have hUnitNq : (-q) * (-(q⁻¹ : Fˣ)) = (1 : Fˣ) := by
    calc (-q) * (-(q⁻¹ : Fˣ)) = (-q) * ((-q)⁻¹) := by
          rw [← hNegInv]
      _ = (1 : Fˣ) := by
          rw [mul_inv_cancel]
  have hMulNqC : torus (R := F) i j hij (-q) *
      torus (R := F) i j hij (-(q⁻¹ : Fˣ)) =
      torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) := by
    calc torus (R := F) i j hij (-q) *
          torus (R := F) i j hij (-(q⁻¹ : Fˣ))
        = torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) *
          torus (R := F) i j hij ((-q) * (-(q⁻¹ : Fˣ))) := hMulNq
      _ = torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) *
          torus (R := F) i j hij (1 : Fˣ) := by
          rw [hUnitNq]
      _ = torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) := by
          rw [torus_one, mul_one]
  have hRinv : torus (R := F) i j hij (-q) *
      (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
        (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹) =
      1 := by
    calc torus (R := F) i j hij (-q) *
          (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
            (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹)
        = (torus (R := F) i j hij (-q) *
          torus (R := F) i j hij (-(q⁻¹ : Fˣ))) *
          (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ := by
          rw [← mul_assoc]
      _ = torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) *
          (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ := by
          rw [hMulNqC]
      _ = 1 := by
          rw [mul_inv_cancel]
  have hInvEq : (torus (R := F) i j hij (-q))⁻¹ =
      torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
        (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ := by
    calc (torus (R := F) i j hij (-q))⁻¹
        = (torus (R := F) i j hij (-q))⁻¹ * 1 := by
          rw [mul_one]
      _ = (torus (R := F) i j hij (-q))⁻¹ *
          (torus (R := F) i j hij (-q) *
            (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
              (torusCocycleAt (F := F) i j hij (-q)
                (-(q⁻¹ : Fˣ)))⁻¹)) := by
          rw [← hRinv]
      _ = ((torus (R := F) i j hij (-q))⁻¹ *
          torus (R := F) i j hij (-q)) *
          (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
            (torusCocycleAt (F := F) i j hij (-q)
              (-(q⁻¹ : Fˣ)))⁻¹) := by
          rw [mul_assoc]
      _ = 1 * (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
          (torusCocycleAt (F := F) i j hij (-q)
            (-(q⁻¹ : Fˣ)))⁻¹) := by
          rw [inv_mul_cancel]
      _ = torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
          (torusCocycleAt (F := F) i j hij (-q)
            (-(q⁻¹ : Fˣ)))⁻¹ := by
          rw [one_mul]
  have hMulP : torus (R := F) i j hij p *
      torus (R := F) i j hij (-(q⁻¹ : Fˣ)) =
      torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
        torus (R := F) i j hij ((-p) * q⁻¹) := by
    calc torus (R := F) i j hij p *
          torus (R := F) i j hij (-(q⁻¹ : Fˣ))
        = torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
          torus (R := F) i j hij (p * (-(q⁻¹ : Fˣ))) :=
          torus_mul_eq_torusCocycleAt_mul hij p (-(q⁻¹ : Fˣ))
      _ = torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
          torus (R := F) i j hij ((-p) * q⁻¹) := by
          rw [hMulEq]
  have hC3center : torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)) ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center hC3mem
  have hC3invCenter : (torusCocycleAt (F := F) i j hij (-q)
      (-(q⁻¹ : Fˣ)))⁻¹ ∈ Subgroup.center (StableSteinberg F) :=
    (Subgroup.center (StableSteinberg F)).inv_mem hC3center
  have hComm : torus (R := F) i j hij ((-p) * q⁻¹) *
      (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ =
      (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ *
        torus (R := F) i j hij ((-p) * q⁻¹) :=
    (Subgroup.mem_center_iff.mp hC3invCenter
      (torus (R := F) i j hij ((-p) * q⁻¹)))
  refine ⟨torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
    (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹,
    (torusCocycleSubgroup (F := F)).mul_mem hC4mem
      ((torusCocycleSubgroup (F := F)).inv_mem hC3mem), ?_⟩
  calc weyl (R := F) i j hij p * weyl (R := F) i j hij q
      = torus (R := F) i j hij p *
        (torus (R := F) i j hij (-q))⁻¹ := hProd
    _ = torus (R := F) i j hij p *
        (torus (R := F) i j hij (-(q⁻¹ : Fˣ)) *
          (torusCocycleAt (F := F) i j hij (-q)
            (-(q⁻¹ : Fˣ)))⁻¹) := by
        rw [hInvEq]
    _ = (torus (R := F) i j hij p *
        torus (R := F) i j hij (-(q⁻¹ : Fˣ))) *
        (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ := by
        rw [mul_assoc]
    _ = (torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
        torus (R := F) i j hij ((-p) * q⁻¹)) *
        (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ := by
        rw [hMulP]
    _ = torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
        (torus (R := F) i j hij ((-p) * q⁻¹) *
          (torusCocycleAt (F := F) i j hij (-q)
            (-(q⁻¹ : Fˣ)))⁻¹) := by
        rw [mul_assoc]
    _ = torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
        ((torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹ *
          torus (R := F) i j hij ((-p) * q⁻¹)) := by
        rw [hComm]
    _ = (torusCocycleAt (F := F) i j hij p (-(q⁻¹ : Fˣ)) *
        (torusCocycleAt (F := F) i j hij (-q) (-(q⁻¹ : Fˣ)))⁻¹) *
        torus (R := F) i j hij ((-p) * q⁻¹) := by
        rw [← mul_assoc]

end SamePairWeylProduct

section WeylConjTorusMixed

/-- Mixed Weyl conjugation of a torus generator, modulo the torus cocycle.

Hypotheses: `[Field F]`, pairwise-distinct indices `i ≠ j` (`hij`),
`i ≠ k` (`hik`), `k ≠ j` (`hkj`), units `u v : Fˣ`.

Exact orientation: `weyl i k u * torus k j v * (weyl i k u)⁻¹ =
c * torus i j v` with the cocycle defect `c ∈ torusCocycleSubgroup`
exhibited on the left. The torus parameter is unchanged (`v`): the mixed
Weyl rewrite `weyl_conj_weyl_mixed` sends the conjugated torus word to
the same-pair product `weyl i j (u * v) * weyl i j (-u)`, and
`weyl_samePair_mul_eq_cocycle_mul_torus` rewrites that product to a left
defect times `torus i j v`, since `(-(u * v)) * (-u)⁻¹ = v` in `Fˣ`.

Purpose: transports a torus generator on the mixed three-index
configuration `(k, j)` across the Weyl generator on `(i, k)`; the
subsequent three-index transfer packet consumes exactly this orientation.

Edge cases: `u` and `v` are arbitrary units (including `1` and `-1`);
the unit/sign/inverse computation uses `mul_neg`, `mul_comm`,
`mul_inv_cancel₀` with `neg_ne_zero`, and `Units.ext` coercion algebra,
hence is valid in characteristic two where `-1 = 1`.

Nonclaims: no defect-free equality (`c = 1` is false in general), no
ordered torus normal form, no finite-central containment, no TWT
closure, no kernel generation, and no Matsumoto comparison or
isomorphism. -/
public theorem weyl_conj_torus_mixed (i j k : ℕ)
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u v : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      weyl (R := F) i k hik u * torus (R := F) k j hkj v *
        (weyl (R := F) i k hik u)⁻¹ =
        c * torus (R := F) i j hij v := by
  have hConj : weyl (R := F) i k hik u *
      torus (R := F) k j hkj v * (weyl (R := F) i k hik u)⁻¹ =
      weyl (R := F) i j hij (u * v) * weyl (R := F) i j hij (-u) := by
    change MulAut.conj (weyl (R := F) i k hik u)
        (torus (R := F) k j hkj v) = _
    simp only [torus, map_mul, MulAut.conj_apply]
    rw [weyl_conj_weyl_mixed (R := F) i j k hij hik hkj u v,
      weyl_conj_weyl_mixed (R := F) i j k hij hik hkj u (-1 : Fˣ)]
    simp
  obtain ⟨c, hc, hEq⟩ :=
    weyl_samePair_mul_eq_cocycle_mul_torus (F := F) i j hij (u * v) (-u)
  have hParam : (-(u * v)) * (-u)⁻¹ = v := by
    have hNegU : (((-u : Fˣ)) : F) = -(((u : Fˣ)) : F) := rfl
    have hNegUV : (((-(u * v) : Fˣ)) : F) = -((((u * v) : Fˣ)) : F) :=
      rfl
    have hU0 : (((u : Fˣ)) : F) ≠ 0 := Units.ne_zero _
    have h1 : -((((u : Fˣ)) : F) * (((v : Fˣ)) : F)) =
        (((v : Fˣ)) : F) * (-(((u : Fˣ)) : F)) := by
      rw [mul_neg, mul_comm (((v : Fˣ)) : F) (((u : Fˣ)) : F)]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, hNegUV, hNegU,
      Units.val_mul]
    rw [h1, mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hU0), mul_one]
  refine ⟨c, hc, ?_⟩
  calc weyl (R := F) i k hik u * torus (R := F) k j hkj v *
        (weyl (R := F) i k hik u)⁻¹
      = weyl (R := F) i j hij (u * v) *
        weyl (R := F) i j hij (-u) := hConj
    _ = c * torus (R := F) i j hij ((-((u * v))) * (-u)⁻¹) := hEq
    _ = c * torus (R := F) i j hij v := by rw [hParam]

end WeylConjTorusMixed

section WeylConjTorusShareFirst

/-- Share-first Weyl conjugation of a torus generator, modulo the torus cocycle.

Hypotheses: `[Field F]`, pairwise-distinct indices `i ≠ j` (`hij`),
`i ≠ k` (`hik`), `k ≠ j` (`hkj`), arbitrary units `u v : Fˣ`
(including `1` and `-1`).

Exact share-first orientation: `weyl i k u * torus i j v * (weyl i k u)⁻¹ =
c * torus k j v` with the cocycle defect `c ∈ torusCocycleSubgroup`
exhibited on the left. The torus parameter is unchanged (`v`): the
conjugating Weyl rewrites via `weyl_swap` to `weyl k i (-u⁻¹)`, and the
existing `weyl_conj_torus_mixed` at `(k, j, i)` closes the goal with no
new unit algebra.

Purpose: rank-free transport of a share-first torus generator across its
shared-index Weyl generator; the overlap-word packet consumes exactly this
orientation with no rank bound.

Nonclaims: no defect-free equality (`c = 1` is false in general), no
finite(-central) containment, no TWT closure, no ordered torus normal form,
no kernel generation, and no Matsumoto comparison or isomorphism. -/
public theorem weyl_conj_torus_shareFirst {i j k : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (u v : Fˣ) :
    ∃ c ∈ torusCocycleSubgroup (F := F),
      weyl (R := F) i k hik u * torus (R := F) i j hij v *
        (weyl (R := F) i k hik u)⁻¹ =
        c * torus (R := F) k j hkj v := by
  have hSwap : weyl (R := F) i k hik u =
      weyl (R := F) k i hik.symm (-u⁻¹) :=
    weyl_swap (R := F) i k hik u
  rw [hSwap]
  exact weyl_conj_torus_mixed (F := F) k j i hkj hik.symm hij (-u⁻¹) v

end WeylConjTorusShareFirst

end AlgebraicKTheory.StableSteinberg

end
