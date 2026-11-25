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

public import MathlibExt.KTheory.Ring.K2.SteinbergSymbolIndexIndependence

/-!
# Boundary torus products in the stable Steinberg group

Over a field, torus cocycles lie in the boundary torus subgroup, and ordered
boundary torus products have explicit elementary-group images. Membership in
the intersection of the boundary and finite-stage subgroups enlarged by the
projection kernel is expressed by a unit tuple with product one and a kernel
factor multiplying its boundary torus product.
-/

namespace AlgebraicKTheory.StableSteinberg

universe u
variable {F : Type u} [Field F]

public theorem torusCocycleAt_mem_boundaryTorusSubgroup {n i : ℕ}
    (hi : i < n) (u v : Fˣ) :
    torusCocycleAt (F := F) i n (Nat.ne_of_lt hi) u v ∈
      boundaryTorusSubgroup (R := F) n := by
  have hU : torus (R := F) i n (Nat.ne_of_lt hi) u ∈
      boundaryTorusSubgroup (R := F) n := by
    apply Subgroup.subset_closure
    exact ⟨i, hi, Nat.ne_of_lt hi, u, rfl⟩
  have hV : torus (R := F) i n (Nat.ne_of_lt hi) v ∈
      boundaryTorusSubgroup (R := F) n := by
    apply Subgroup.subset_closure
    exact ⟨i, hi, Nat.ne_of_lt hi, v, rfl⟩
  have hUV : torus (R := F) i n (Nat.ne_of_lt hi) (u * v) ∈
      boundaryTorusSubgroup (R := F) n := by
    apply Subgroup.subset_closure
    exact ⟨i, hi, Nat.ne_of_lt hi, u * v, rfl⟩
  have hMul := (boundaryTorusSubgroup (R := F) n).mul_mem hU hV
  have hInv := (boundaryTorusSubgroup (R := F) n).inv_mem hUV
  simp only [torusCocycleAt]
  exact (boundaryTorusSubgroup (R := F) n).mul_mem hMul hInv

public theorem torus_mul_eq_torusCocycleAt_mul {n i : ℕ}
    (hij : i ≠ n) (u v : Fˣ) :
    torus (R := F) i n hij u * torus (R := F) i n hij v =
      torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v) := by
  have h : torusCocycleAt (F := F) i n hij u v * torus (R := F) i n hij (u * v) =
      torus (R := F) i n hij u * torus (R := F) i n hij v := by
    simp only [torusCocycleAt, mul_assoc, inv_mul_cancel, mul_one]
  exact h.symm

public def boundaryTorusProd (n : ℕ) (u : Fin n → Fˣ) : StableSteinberg F :=
  (List.ofFn (fun i : Fin n => torus i.val n (Nat.ne_of_lt i.isLt) (u i))).prod

/-- Compute `boundaryTorusProd` as the ordered product over `List.finRange`. -/
public theorem boundaryTorusProd_eq_finRange (n : ℕ) (u : Fin n → Fˣ) :
    boundaryTorusProd (F := F) n u =
      ((List.finRange n).map (fun i : Fin n =>
        torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i))).prod := by
  unfold boundaryTorusProd
  rw [List.ofFn_eq_map]

/-- Evaluation at rank zero: `boundaryTorusProd 0` is the empty product.

- Order: `boundaryTorusProd` is defined as
  `(List.ofFn (fun i : Fin n => torus i.val n _ (u i))).prod`.
  `List.ofFn` enumerates `Fin n` in increasing order `0,1,…,n-1`. `List.prod` multiplies
  as `a₀ * (a₁ * (⋯ * 1))`. At `n = 0`, `List.ofFn` on `Fin 0` is `[]` (`List.ofFn_zero`),
  and `List.prod [] = 1` (`List.prod_nil`). So the orientation is the empty product.

Nonclaims: this lemma makes no claim about a general `(n+1)` successor decomposition,
no claim that `∏ u = 1` implies `boundaryTorusProd = 1`, no kernel-membership claim,
and no cocycle-identity claim. Only the `n = 0` evaluation with the exact
`List.ofFn`/`List.prod` orientation. -/
public theorem boundaryTorusProd_zero (u : Fin 0 → Fˣ) :
    boundaryTorusProd (F := F) 0 u = 1 := by
  unfold boundaryTorusProd
  rw [List.ofFn_zero]
  rfl

/-- Evaluation at rank one: `boundaryTorusProd 1` is the single torus factor.

- Order: `List.ofFn` on `Fin 1 = Fin (0+1)` satisfies `List.ofFn_succ`:
  `ofFn f = f 0 :: ofFn (fun i : Fin 0 => f (Fin.succ i))`. With `List.ofFn_zero` the tail
  is `[]`, so the list is the singleton `[f 0]` and `List.prod [a] = a * 1 = a`
  (`List.prod_cons`, `List.prod_nil`, `mul_one`). The function
  `f` here is `fun i : Fin 1 => torus i.val 1 (Nat.ne_of_lt i.isLt) (u i)`;
  for `i = 0 : Fin 1`, `i.val = 0` definitionally and the inequality proof is
  `Nat.ne_of_lt (0 : Fin 1).isLt : 0 ≠ 1`. Hence the orientation is exactly the
  head-first singleton product induced by `List.ofFn`/`List.prod`.

- Proof closure: after reducing `List.ofFn` on `Fin 1` to the singleton head
  and applying `List.prod_cons`/`List.prod_nil`/`mul_one`, the remaining goal is
  equality of `torus` factors differing only by the `Fin.val` projection and the
  `0 ≠ 1` proof. It is closed by `rfl` giving `hv : (0 : Fin 1).val = 0`
  followed by `simp only [hv]`; the inequality proofs are identified by proof
  irrelevance (subsingleton) and the remaining arguments by `rfl`.

Nonclaims: no general `n+1` successor theorem, no claim that product-one of `u`
forces `boundaryTorusProd = 1`, no kernel claim (`ker toStableE`), and no cocycle
claim; only the exact `n = 1` orientation from the existing definition. -/
public theorem boundaryTorusProd_one (u : Fin 1 → Fˣ) :
    boundaryTorusProd (F := F) 1 u =
      torus (R := F) 0 1 (Nat.ne_of_lt (0 : Fin 1).isLt) (u 0) := by
  unfold boundaryTorusProd
  have hSucc : (List.ofFn (fun i : Fin 1 =>
      torus (R := F) i.val 1 (Nat.ne_of_lt i.isLt) (u i))) =
      (torus (R := F) (0 : Fin 1).val 1 (Nat.ne_of_lt (0 : Fin 1).isLt) (u (0 : Fin 1))) ::
      List.ofFn (fun i : Fin 0 =>
        torus (R := F) (Fin.succ i).val 1 (Nat.ne_of_lt (Fin.succ i).isLt) (u (Fin.succ i))) := by
    rw [List.ofFn_succ]
  rw [hSucc]
  have hZero : (List.ofFn (fun i : Fin 0 =>
      torus (R := F) (Fin.succ i).val 1
        (Nat.ne_of_lt (Fin.succ i).isLt) (u (Fin.succ i)))) = [] := by
    rw [List.ofFn_zero]
  rw [hZero]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  have hv : (0 : Fin 1).val = 0 := rfl
  simp only [hv]

public theorem boundaryTorusProd_mem_boundaryTorusSubgroup (n : ℕ)
    (u : Fin n → Fˣ) :
    boundaryTorusProd (F := F) n u ∈ boundaryTorusSubgroup (R := F) n := by
  unfold boundaryTorusProd
  let H := boundaryTorusSubgroup (R := F) n
  have hEach : ∀ g ∈ List.ofFn
      (fun i : Fin n => torus (R := F) i.val n (Nat.ne_of_lt i.isLt) (u i)), g ∈ H := by
    intro g hg
    rw [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    apply Subgroup.subset_closure
    exact ⟨i.val, i.isLt, Nat.ne_of_lt i.isLt, u i, rfl⟩
  have hProd : ∀ (L : List (StableSteinberg F)), (∀ g ∈ L, g ∈ H) → L.prod ∈ H := by
    intro L
    induction L with
    | nil => intro _; exact H.one_mem
    | cons hd tl ih =>
      intro hL
      exact H.mul_mem (hL hd List.mem_cons_self) (ih fun g hg => hL g (List.mem_cons_of_mem hd hg))
  exact hProd _ hEach

public theorem toStableE_boundaryTorusProd (n : ℕ) (u : Fin n → Fˣ) :
    toStableE (R := F) (boundaryTorusProd (F := F) n u) =
      toStableE_torus_fin_last_piHom (F := F) n u := by
  unfold boundaryTorusProd
  rw [MonoidHom.map_list_prod, List.map_ofFn, List.ofFn_eq_map]
  have hToFin : (List.finRange n).toFinset = Finset.univ := by
    ext x
    simp
  have hComm_univ : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
      (Function.onFun Commute fun i : Fin n =>
        toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (u i))) :=
    toStableE_torus_fin_last_pairwise_commute (F := F) n u
  have hComm : Set.Pairwise (↑(List.finRange n).toFinset : Set (Fin n))
      (Function.onFun Commute fun i : Fin n =>
        toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (u i))) := by
    rw [hToFin]
    exact hComm_univ
  have hNodup : (List.finRange n).Nodup := List.nodup_finRange n
  have hComp : (List.finRange n).map
      (⇑(toStableE (R := F)) ∘ fun i : Fin n =>
        torus i.val n (Nat.ne_of_lt i.isLt) (u i)) =
      (List.finRange n).map (fun i : Fin n =>
        toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (u i))) := by
    rfl
  rw [hComp]
  have hProd : ((List.finRange n).map (fun i : Fin n =>
      toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (u i)))).prod =
      (Finset.univ : Finset (Fin n)).noncommProd (fun i =>
        toStableE (R := F) (torus i.val n (Nat.ne_of_lt i.isLt) (u i)))
        hComm_univ := by
    calc ((List.finRange n).map _).prod
        = (List.finRange n).toFinset.noncommProd _ hComm := by
          rw [Finset.noncommProd_toFinset _ _ _ hNodup]
      _ = _ := by
        simp
  rw [hProd, toStableE_torus_fin_last_piHom, MonoidHom.noncommPiCoprod_apply]
  exact Finset.noncommProd_congr rfl (fun i _ => rfl) hComm_univ

/-- Refined factorization for the joined boundary-torus / finite-stage intersection.

Given `g` in `(boundaryTorusSubgroup n ⊔ ker toStableE) ⊓
(finiteStage n ⊔ ker toStableE)`, there exist `u : Fin n → Fˣ` with
`∏ u = 1` and `k ∈ ker toStableE` such that
`toStableE g = piHom n u = toStableE (boundaryTorusProd n u)` and
`g = k * boundaryTorusProd n u`.

This is a refined factorization and not exact subgroup equality; it only
factors the `ker`-joined intersection via a product-one torus and a kernel
correction. -/
public theorem
    boundaryTorus_sup_ker_inf_finiteStage_sup_ker_refined_factorization
    (n : ℕ) (g : StableSteinberg F)
    (hg : g ∈ (boundaryTorusSubgroup (R := F) n ⊔
            (toStableE (R := F)).ker) ⊓
            (finiteStage (R := F) n ⊔ (toStableE (R := F)).ker)) :
    ∃ (u : Fin n → Fˣ) (k : StableSteinberg F),
      Finset.univ.prod u = 1 ∧
      k ∈ (toStableE (R := F)).ker ∧
      toStableE (R := F) g = toStableE_torus_fin_last_piHom (F := F) n u ∧
      toStableE (R := F) g =
        toStableE (R := F) (boundaryTorusProd (F := F) n u) ∧
      g = k * boundaryTorusProd (F := F) n u := by
  have hImg : toStableE (R := F) g ∈
      (toStableE_torus_fin_last_piHom (F := F) n).range ⊓
        (StableE.fromFinite F n).range := by
    rwa [← boundaryTorus_sup_ker_inf_finiteStage_sup_ker_mem_iff (F := F) n g]
  obtain ⟨u, hProd, hEq⟩ :=
    (toStableE_torus_fin_last_piHom_range_inf_fromFinite_range_mem_iff
      (F := F) n (toStableE (R := F) g)).mp hImg
  have hToPi : toStableE (R := F) g =
      toStableE_torus_fin_last_piHom (F := F) n u := hEq.symm
  have hToProd : toStableE (R := F) g =
      toStableE (R := F) (boundaryTorusProd (F := F) n u) := by
    calc toStableE (R := F) g =
        toStableE_torus_fin_last_piHom (F := F) n u := hToPi
      _ = toStableE (R := F) (boundaryTorusProd (F := F) n u) :=
        (toStableE_boundaryTorusProd (F := F) n u).symm
  let b := boundaryTorusProd (F := F) n u
  let k := g * b⁻¹
  have hk : k ∈ (toStableE (R := F)).ker := by
    rw [MonoidHom.mem_ker]
    simp [k, b, hToProd, map_mul, map_inv]
  have hgEq : g = k * b := by
    simp [k, b]
  exact ⟨u, k, hProd, hk, hToPi, hToProd, hgEq⟩

end AlgebraicKTheory.StableSteinberg
