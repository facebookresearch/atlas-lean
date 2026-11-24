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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootSubgroups

/-!
# Boundary Pi-to-list bridge

For generic `[Ring R]`, `lastColumnProduct` and `lastRowProduct` on
`Fin n → Multiplicative R` equal the ordered list products `lastColumnListProd`
and `lastRowListProd` via `List.ofFn` in increasing `0, ..., n-1` order;
`n = 0` gives the empty product `1`. These are equalities in
`StableSteinberg R` only, not finite-stage, centrality, kernel, or
Matsumoto results.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

private def myColHom (n : ℕ) (i : Fin n) :
    Multiplicative R →* StableSteinberg R where
  toFun a := x i.val n (Nat.ne_of_lt i.isLt) a.toAdd
  map_one' := by
    change x i.val n (Nat.ne_of_lt i.isLt) (1 : Multiplicative R).toAdd = 1
    have h : (1 : Multiplicative R).toAdd = (0 : R) := rfl
    rw [h, x_zero]
  map_mul' := by
    intro a b
    change x i.val n (Nat.ne_of_lt i.isLt) (a * b).toAdd =
      x i.val n (Nat.ne_of_lt i.isLt) a.toAdd *
        x i.val n (Nat.ne_of_lt i.isLt) b.toAdd
    have h : (a * b).toAdd = a.toAdd + b.toAdd := rfl
    rw [h]
    exact (x_add i.val n (Nat.ne_of_lt i.isLt) a.toAdd b.toAdd).symm

private def myRowHom (n : ℕ) (i : Fin n) :
    Multiplicative R →* StableSteinberg R where
  toFun a := x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) a.toAdd
  map_one' := by
    change x n i.val (Ne.symm (Nat.ne_of_lt i.isLt))
        (1 : Multiplicative R).toAdd = 1
    have h : (1 : Multiplicative R).toAdd = (0 : R) := rfl
    rw [h, x_zero]
  map_mul' := by
    intro a b
    change x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (a * b).toAdd =
      x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) a.toAdd *
        x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) b.toAdd
    have h : (a * b).toAdd = a.toAdd + b.toAdd := rfl
    rw [h]
    exact (x_add n i.val (Ne.symm (Nat.ne_of_lt i.isLt))
      a.toAdd b.toAdd).symm

private lemma myColHom_pairwise (n : ℕ) :
    Pairwise fun (i j : Fin n) =>
      ∀ (a b : Multiplicative R),
        Commute (myColHom (R := R) n i a) (myColHom n j b) := by
  intro i j hij a b
  have hi : (i.val ≠ n) := Nat.ne_of_lt i.isLt
  have hj : (j.val ≠ n) := Nat.ne_of_lt j.isLt
  have h : ⁅x i.val n hi a.toAdd, x j.val n hj b.toAdd⁆ = 1 :=
    x_comm i.val n j.val n hi hj hi (Ne.symm hj) a.toAdd b.toAdd
  exact commutatorElement_eq_one_iff_commute.mp h

private lemma myRowHom_pairwise (n : ℕ) :
    Pairwise fun (i j : Fin n) =>
      ∀ (a b : Multiplicative R),
        Commute (myRowHom (R := R) n i a) (myRowHom n j b) := by
  intro i j hij a b
  have hi : (n ≠ i.val) := Ne.symm (Nat.ne_of_lt i.isLt)
  have hj : (n ≠ j.val) := Ne.symm (Nat.ne_of_lt j.isLt)
  have h : ⁅x n i.val hi a.toAdd, x n j.val hj b.toAdd⁆ = 1 :=
    x_comm n i.val n j.val hi hj hj (Nat.ne_of_lt i.isLt) a.toAdd b.toAdd
  exact commutatorElement_eq_one_iff_commute.mp h

private def myLastColumnProduct (n : ℕ) :
    ((i : Fin n) → Multiplicative R) →* StableSteinberg R :=
  MonoidHom.noncommPiCoprod (myColHom (R := R) n) (myColHom_pairwise n)

private def myLastRowProduct (n : ℕ) :
    ((i : Fin n) → Multiplicative R) →* StableSteinberg R :=
  MonoidHom.noncommPiCoprod (myRowHom (R := R) n) (myRowHom_pairwise n)

private lemma myLastColumnProduct_eq (n : ℕ) :
    myLastColumnProduct (R := R) n = lastColumnProduct (R := R) n := rfl

private lemma myLastRowProduct_eq (n : ℕ) :
    myLastRowProduct (R := R) n = lastRowProduct (R := R) n := rfl

private lemma lastColumnListProd_map (n : ℕ) (L : List (Fin n × R)) :
    (L.map (fun p : Fin n × R =>
        x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod =
      lastColumnListProd (R := R) n L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have h1 : (List.map
          (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)
          (p :: L)).prod =
        x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2 *
          (List.map
            (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)
            L).prod := by
      simp [List.prod_cons]
    have h2 : lastColumnListProd (R := R) n (p :: L) =
        x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2 *
          lastColumnListProd (R := R) n L := rfl
    calc (List.map
          (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)
          (p :: L)).prod
        = x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2 *
            (List.map
              (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)
              L).prod := h1
      _ = x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2 *
            lastColumnListProd (R := R) n L := by rw [ih]
      _ = lastColumnListProd (R := R) n (p :: L) := h2.symm

private lemma lastRowListProd_map (n : ℕ) (L : List (Fin n × R)) :
    (L.map (fun p : Fin n × R =>
        x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)).prod =
      lastRowListProd (R := R) n L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have h1 : (List.map
          (fun p : Fin n × R =>
            x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)
          (p :: L)).prod =
        x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
          (List.map
            (fun p : Fin n × R =>
              x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)
            L).prod := by
      simp [List.prod_cons]
    have h2 : lastRowListProd (R := R) n (p :: L) =
        x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
          lastRowListProd (R := R) n L := rfl
    calc (List.map
          (fun p : Fin n × R =>
            x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)
          (p :: L)).prod
        = x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
            (List.map
              (fun p : Fin n × R =>
                x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)
              L).prod := h1
      _ = x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
            lastRowListProd (R := R) n L := by rw [ih]
      _ = lastRowListProd (R := R) n (p :: L) := h2.symm

private lemma col_finRange_map_eq_ofFn (n : ℕ)
    (c : Fin n → Multiplicative R) :
    (List.finRange n).map
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd) =
      (List.ofFn (fun i : Fin n => (i, (c i).toAdd))).map
        (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2) := by
  rw [← List.ofFn_eq_map
    (f := fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)]
  rw [show (List.ofFn (fun i : Fin n => (i, (c i).toAdd))).map
        (fun p : Fin n × R => x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2) =
      List.ofFn
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd) from by
    rw [List.map_ofFn]
    rfl]

private lemma row_finRange_map_eq_ofFn (n : ℕ)
    (r : Fin n → Multiplicative R) :
    (List.finRange n).map
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd) =
      (List.ofFn (fun i : Fin n => (i, (r i).toAdd))).map
        (fun p : Fin n × R =>
          x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2) := by
  rw [← List.ofFn_eq_map
    (f := fun i : Fin n =>
      x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)]
  rw [show (List.ofFn (fun i : Fin n => (i, (r i).toAdd))).map
        (fun p : Fin n × R =>
          x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2) =
      List.ofFn
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd) from by
    rw [List.map_ofFn]
    rfl]

/-- For generic `[Ring R]`, `lastColumnProduct` on `Fin n → Multiplicative R`
equals the ordered `List.ofFn` product `lastColumnListProd` in increasing
`0, ..., n-1` order (`n = 0` is `1`). Equality in `StableSteinberg R` only,
not a finite-stage, centrality, kernel, or Matsumoto result. -/
theorem lastColumnProduct_eq_lastColumnListProd_ofFn
    (n : ℕ) (c : Fin n → Multiplicative R) :
    lastColumnProduct (R := R) n c =
      lastColumnListProd (R := R) n
        (List.ofFn (fun i : Fin n => (i, (c i).toAdd))) := by
  have h_eq : lastColumnProduct (R := R) n c =
      myLastColumnProduct (R := R) n c := by
    rw [myLastColumnProduct_eq]
  rw [h_eq]
  have hcomm : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      fun a b : Fin n =>
        Commute (x a.val n (Nat.ne_of_lt a.isLt) (c a).toAdd)
          (x b.val n (Nat.ne_of_lt b.isLt) (c b).toAdd) := by
    intro a _ b _ hab
    have ha : (a.val ≠ n) := Nat.ne_of_lt a.isLt
    have hb : (b.val ≠ n) := Nat.ne_of_lt b.isLt
    have h : ⁅x a.val n ha (c a).toAdd,
        x b.val n hb (c b).toAdd⁆ = 1 :=
      x_comm a.val n b.val n ha hb ha (Ne.symm hb)
        (c a).toAdd (c b).toAdd
    exact commutatorElement_eq_one_iff_commute.mp h
  have h1 : myLastColumnProduct (R := R) n c =
      Finset.univ.noncommProd
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        hcomm :=
    MonoidHom.noncommPiCoprod_apply
      (ϕ := myColHom (R := R) n) (hcomm := myColHom_pairwise n) c
  have huniv : (List.finRange n).toFinset =
      (Finset.univ : Finset (Fin n)) :=
    List.toFinset_finRange n
  have hnodup : (List.finRange n).Nodup := List.nodup_finRange n
  have hcomm_list : ((List.finRange n).toFinset : Set (Fin n)).Pairwise
      fun a b : Fin n =>
        Commute (x a.val n (Nat.ne_of_lt a.isLt) (c a).toAdd)
          (x b.val n (Nat.ne_of_lt b.isLt) (c b).toAdd) := by
    rw [huniv]; exact hcomm
  have h2' : (List.finRange n).toFinset.noncommProd
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        hcomm_list =
        ((List.finRange n).map
          (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        ).prod := by
    rw [Finset.noncommProd_toFinset _ _ _ hnodup]
  have h_eq : Finset.univ.noncommProd
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        hcomm =
      (List.finRange n).toFinset.noncommProd
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        hcomm_list := by
    apply Finset.noncommProd_congr
    · exact huniv.symm
    · intro x hx; rfl
  have h2 : Finset.univ.noncommProd
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
        hcomm =
      ((List.finRange n).map
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
      ).prod := by
    rw [h_eq, h2']
  rw [h1, h2]
  have h3 := col_finRange_map_eq_ofFn (R := R) n c
  have h4 := lastColumnListProd_map (R := R) n
    (List.ofFn (fun i : Fin n => (i, (c i).toAdd)))
  calc ((List.finRange n).map
        (fun i : Fin n => x i.val n (Nat.ne_of_lt i.isLt) (c i).toAdd)
      ).prod
      = ((List.ofFn (fun i : Fin n => (i, (c i).toAdd))).map
          (fun p : Fin n × R =>
            x p.1.val n (Nat.ne_of_lt p.1.isLt) p.2)).prod := by
        rw [h3]
    _ = lastColumnListProd (R := R) n
          (List.ofFn (fun i : Fin n => (i, (c i).toAdd))) := h4

/-- For generic `[Ring R]`, `lastRowProduct` on `Fin n → Multiplicative R`
equals the ordered `List.ofFn` product `lastRowListProd` in increasing
`0, ..., n-1` order (`n = 0` is `1`). Equality in `StableSteinberg R` only,
not a finite-stage, centrality, kernel, or Matsumoto result. -/
theorem lastRowProduct_eq_lastRowListProd_ofFn
    (n : ℕ) (r : Fin n → Multiplicative R) :
    lastRowProduct (R := R) n r =
      lastRowListProd (R := R) n
        (List.ofFn (fun i : Fin n => (i, (r i).toAdd))) := by
  have h_eq : lastRowProduct (R := R) n r =
      myLastRowProduct (R := R) n r := by
    rw [myLastRowProduct_eq]
  rw [h_eq]
  have hcomm : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      fun a b : Fin n =>
        Commute
          (x n a.val (Ne.symm (Nat.ne_of_lt a.isLt)) (r a).toAdd)
          (x n b.val (Ne.symm (Nat.ne_of_lt b.isLt)) (r b).toAdd) := by
    intro a _ b _ hab
    have ha : (n ≠ a.val) := Ne.symm (Nat.ne_of_lt a.isLt)
    have hb : (n ≠ b.val) := Ne.symm (Nat.ne_of_lt b.isLt)
    have h : ⁅x n a.val ha (r a).toAdd,
        x n b.val hb (r b).toAdd⁆ = 1 :=
      x_comm n a.val n b.val ha hb hb (Nat.ne_of_lt a.isLt)
        (r a).toAdd (r b).toAdd
    exact commutatorElement_eq_one_iff_commute.mp h
  have h1 : myLastRowProduct (R := R) n r =
      Finset.univ.noncommProd
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        hcomm :=
    MonoidHom.noncommPiCoprod_apply
      (ϕ := myRowHom (R := R) n) (hcomm := myRowHom_pairwise n) r
  have huniv : (List.finRange n).toFinset =
      (Finset.univ : Finset (Fin n)) :=
    List.toFinset_finRange n
  have hnodup : (List.finRange n).Nodup := List.nodup_finRange n
  have hcomm_list : ((List.finRange n).toFinset : Set (Fin n)).Pairwise
      fun a b : Fin n =>
        Commute
          (x n a.val (Ne.symm (Nat.ne_of_lt a.isLt)) (r a).toAdd)
          (x n b.val (Ne.symm (Nat.ne_of_lt b.isLt)) (r b).toAdd) := by
    rw [huniv]; exact hcomm
  have h2' : (List.finRange n).toFinset.noncommProd
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        hcomm_list =
        ((List.finRange n).map
          (fun i : Fin n =>
            x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        ).prod := by
    rw [Finset.noncommProd_toFinset _ _ _ hnodup]
  have h_eq : Finset.univ.noncommProd
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        hcomm =
      (List.finRange n).toFinset.noncommProd
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        hcomm_list := by
    apply Finset.noncommProd_congr
    · exact huniv.symm
    · intro x hx; rfl
  have h2 : Finset.univ.noncommProd
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
        hcomm =
      ((List.finRange n).map
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
      ).prod := by
    rw [h_eq, h2']
  rw [h1, h2]
  have h3 := row_finRange_map_eq_ofFn (R := R) n r
  have h4 := lastRowListProd_map (R := R) n
    (List.ofFn (fun i : Fin n => (i, (r i).toAdd)))
  calc ((List.finRange n).map
        (fun i : Fin n =>
          x n i.val (Ne.symm (Nat.ne_of_lt i.isLt)) (r i).toAdd)
      ).prod
      = ((List.ofFn (fun i : Fin n => (i, (r i).toAdd))).map
          (fun p : Fin n × R =>
            x n p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2)).prod := by
        rw [h3]
    _ = lastRowListProd (R := R) n
          (List.ofFn (fun i : Fin n => (i, (r i).toAdd))) := h4

/-- For generic `[Ring R]`, `lastColumnProduct` at `k : Fin n` splits the
increasing `List.ofFn` product into `A` before `k`, the singleton
`x k.val n (Nat.ne_of_lt k.isLt) (c k).toAdd`, and `C` after `k`.
Uses `Nat.ne_of_lt k.isLt` for the root witness and pinned `List.take` /
`List.drop` / `List.getElem` to preserve `0, ..., n-1` order. Equality in
`StableSteinberg R` only, not a finite-stage, kernel, collection, landing,
minimal-normal-form, or Matsumoto result. -/
theorem lastColumnProduct_exists_split_at (n : ℕ)
    (c : Fin n → Multiplicative R) (k : Fin n) :
    ∃ (A C : List (Fin n × R)),
      lastColumnProduct (R := R) n c =
        lastColumnListProd n A * x k.val n (Nat.ne_of_lt k.isLt) (c k).toAdd *
          lastColumnListProd n C ∧
      (∀ p ∈ A, p.1.val < k.val) ∧ (∀ p ∈ C, k.val < p.1.val) := by
  let L : List (Fin n × R) := List.ofFn fun i : Fin n => (i, (c i).toAdd)
  have hBridge : lastColumnProduct (R := R) n c = lastColumnListProd n L :=
    lastColumnProduct_eq_lastColumnListProd_ofFn n c
  have hLen : L.length = n := List.length_ofFn
  have hkLt : k.val < L.length := by rw [hLen]; exact k.isLt
  have hGet : L[k.val]'hkLt = (k, (c k).toAdd) := by
    simp [L, List.getElem_ofFn]
  let A : List (Fin n × R) := L.take k.val
  let C : List (Fin n × R) := L.drop (k.val + 1)
  have hSplit : L = A ++ [(k, (c k).toAdd)] ++ C := by
    have h1 : L.take k.val ++ L.drop k.val = L := by
      simp [List.take_append_drop]
    have h2 : L.drop k.val = L[k.val]'hkLt :: L.drop (k.val + 1) := by
      have := List.drop_eq_getElem_cons hkLt
      simpa [hGet] using this
    calc L = L.take k.val ++ L.drop k.val := h1.symm
      _ = L.take k.val ++ (L[k.val]'hkLt :: L.drop (k.val + 1)) := by
          rw [h2]
      _ = L.take k.val ++ ([(k, (c k).toAdd)] ++ L.drop (k.val + 1)) := by
          simp [hGet]
      _ = A ++ [(k, (c k).toAdd)] ++ C := by
          simp [A, C, List.append_assoc]
  have hColAppend : ∀ (L₁ L₂ : List (Fin n × R)),
      lastColumnListProd n (L₁ ++ L₂) =
        lastColumnListProd n L₁ * lastColumnListProd n L₂ := by
    intro L₁ L₂
    induction L₁ with
    | nil => simp [lastColumnListProd]
    | cons p L₁ ih => simp [lastColumnListProd, ih, mul_assoc]
  have hProd : lastColumnListProd n L =
      lastColumnListProd n A * x k.val n (Nat.ne_of_lt k.isLt) (c k).toAdd *
        lastColumnListProd n C := by
    calc lastColumnListProd n L
        = lastColumnListProd n (A ++ [(k, (c k).toAdd)] ++ C) := by
            rw [← hSplit]
      _ = lastColumnListProd n (A ++ [(k, (c k).toAdd)]) *
            lastColumnListProd n C := by
            rw [hColAppend]
      _ = (lastColumnListProd n A * lastColumnListProd n [(k, (c k).toAdd)]) *
            lastColumnListProd n C := by
            rw [hColAppend]
      _ = lastColumnListProd n A * x k.val n (Nat.ne_of_lt k.isLt) (c k).toAdd *
            lastColumnListProd n C := by
            simp [lastColumnListProd]
  have hA : ∀ p ∈ A, p.1.val < k.val := by
    intro p hp
    have hp' : p ∈ L.take k.val := hp
    obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hp'
    have hTakeLen : (L.take k.val).length = k.val := by
      rw [List.length_take, hLen, Nat.min_eq_left (Nat.le_of_lt k.isLt)]
    have hiBound : i < k.val := by rw [hTakeLen] at hi; exact hi
    have hiLtN : i < n := Nat.lt_trans hiBound k.isLt
    have hEqTake : (L.take k.val)[i]'hi = L[i]'(by rw [hLen]; exact hiLtN) := by
      rw [List.getElem_take]
    have hVal : (L[i]'(by rw [hLen]; exact hiLtN)).1.val = i := by
      simp [L, List.getElem_ofFn]
    have hPeq : p = (L.take k.val)[i]'hi := hEq.symm
    calc p.1.val = ((L.take k.val)[i]'hi).1.val := by rw [hPeq]
      _ = (L[i]'(by rw [hLen]; exact hiLtN)).1.val := by
          rw [hEqTake]
      _ = i := hVal
      _ < k.val := hiBound
  have hC : ∀ p ∈ C, k.val < p.1.val := by
    intro p hp
    have hp' : p ∈ L.drop (k.val + 1) := hp
    obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hp'
    have hDropLen : (L.drop (k.val + 1)).length = n - (k.val + 1) := by
      rw [List.length_drop, hLen]
    have hiLtLen : i < n - (k.val + 1) := by rw [← hDropLen]; exact hi
    have hkLe : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have hiBound : i + (k.val + 1) < n := by omega
    have hGetDrop : (L.drop (k.val + 1))[i]'hi =
        L[(k.val + 1) + i]'(by rw [hLen]; omega) := by
      rw [List.getElem_drop]
    have hVal : (L[(k.val + 1) + i]'(by rw [hLen]; omega)).1.val = (k.val + 1) + i := by
      simp [L, List.getElem_ofFn]
    have hPeq : p = (L.drop (k.val + 1))[i]'hi := hEq.symm
    have hPv : p.1.val = (k.val + 1) + i := by
      calc p.1.val = ((L.drop (k.val + 1))[i]'hi).1.val := by rw [hPeq]
        _ = (L[(k.val + 1) + i]'(by rw [hLen]; omega)).1.val := by rw [hGetDrop]
        _ = (k.val + 1) + i := hVal
    have : p.1.val = i + (k.val + 1) := by rw [hPv, Nat.add_comm]
    omega
  refine ⟨A, C, ?_, hA, hC⟩
  rw [hBridge, hProd]

/-- For generic `[Ring R]`, `lastRowProduct` at `k : Fin n` splits the
increasing `List.ofFn` product into `A` before `k`, the singleton
`x n k.val (Ne.symm (Nat.ne_of_lt k.isLt)) (r k).toAdd`, and `C` after `k`.
Uses `Ne.symm (Nat.ne_of_lt k.isLt)` for the root witness and pinned
`List.take` / `List.drop` / `List.getElem` to preserve `0, ..., n-1` order.
Equality in `StableSteinberg R` only, not a finite-stage, kernel, collection,
landing, minimal-normal-form, or Matsumoto result. -/
theorem lastRowProduct_exists_split_at (n : ℕ)
    (r : Fin n → Multiplicative R) (k : Fin n) :
    ∃ (A C : List (Fin n × R)),
      lastRowProduct (R := R) n r =
        lastRowListProd n A * x n k.val (Ne.symm (Nat.ne_of_lt k.isLt)) (r k).toAdd *
          lastRowListProd n C ∧
      (∀ p ∈ A, p.1.val < k.val) ∧ (∀ p ∈ C, k.val < p.1.val) := by
  let L : List (Fin n × R) := List.ofFn fun i : Fin n => (i, (r i).toAdd)
  have hBridge : lastRowProduct (R := R) n r = lastRowListProd n L :=
    lastRowProduct_eq_lastRowListProd_ofFn n r
  have hLen : L.length = n := List.length_ofFn
  have hkLt : k.val < L.length := by rw [hLen]; exact k.isLt
  have hGet : L[k.val]'hkLt = (k, (r k).toAdd) := by
    simp [L, List.getElem_ofFn]
  let A : List (Fin n × R) := L.take k.val
  let C : List (Fin n × R) := L.drop (k.val + 1)
  have hSplit : L = A ++ [(k, (r k).toAdd)] ++ C := by
    have h1 : L.take k.val ++ L.drop k.val = L := by
      simp [List.take_append_drop]
    have h2 : L.drop k.val = L[k.val]'hkLt :: L.drop (k.val + 1) := by
      have := List.drop_eq_getElem_cons hkLt
      simpa [hGet] using this
    calc L = L.take k.val ++ L.drop k.val := h1.symm
      _ = L.take k.val ++ (L[k.val]'hkLt :: L.drop (k.val + 1)) := by
          rw [h2]
      _ = L.take k.val ++ ([(k, (r k).toAdd)] ++ L.drop (k.val + 1)) := by
          simp [hGet]
      _ = A ++ [(k, (r k).toAdd)] ++ C := by
          simp [A, C, List.append_assoc]
  have hRowAppend : ∀ (L₁ L₂ : List (Fin n × R)),
      lastRowListProd n (L₁ ++ L₂) =
        lastRowListProd n L₁ * lastRowListProd n L₂ := by
    intro L₁ L₂
    induction L₁ with
    | nil => simp [lastRowListProd]
    | cons p L₁ ih => simp [lastRowListProd, ih, mul_assoc]
  have hProd : lastRowListProd n L =
      lastRowListProd n A * x n k.val (Ne.symm (Nat.ne_of_lt k.isLt)) (r k).toAdd *
        lastRowListProd n C := by
    calc lastRowListProd n L
        = lastRowListProd n (A ++ [(k, (r k).toAdd)] ++ C) := by
            rw [← hSplit]
      _ = lastRowListProd n (A ++ [(k, (r k).toAdd)]) *
            lastRowListProd n C := by
            rw [hRowAppend]
      _ = (lastRowListProd n A * lastRowListProd n [(k, (r k).toAdd)]) *
            lastRowListProd n C := by
            rw [hRowAppend]
      _ = lastRowListProd n A * x n k.val (Ne.symm (Nat.ne_of_lt k.isLt)) (r k).toAdd *
            lastRowListProd n C := by
            simp [lastRowListProd]
  have hA : ∀ p ∈ A, p.1.val < k.val := by
    intro p hp
    have hp' : p ∈ L.take k.val := hp
    obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hp'
    have hTakeLen : (L.take k.val).length = k.val := by
      rw [List.length_take, hLen, Nat.min_eq_left (Nat.le_of_lt k.isLt)]
    have hiBound : i < k.val := by rw [hTakeLen] at hi; exact hi
    have hiLtN : i < n := Nat.lt_trans hiBound k.isLt
    have hEqTake : (L.take k.val)[i]'hi = L[i]'(by rw [hLen]; exact hiLtN) := by
      rw [List.getElem_take]
    have hVal : (L[i]'(by rw [hLen]; exact hiLtN)).1.val = i := by
      simp [L, List.getElem_ofFn]
    have hPeq : p = (L.take k.val)[i]'hi := hEq.symm
    calc p.1.val = ((L.take k.val)[i]'hi).1.val := by rw [hPeq]
      _ = (L[i]'(by rw [hLen]; exact hiLtN)).1.val := by
          rw [hEqTake]
      _ = i := hVal
      _ < k.val := hiBound
  have hC : ∀ p ∈ C, k.val < p.1.val := by
    intro p hp
    have hp' : p ∈ L.drop (k.val + 1) := hp
    obtain ⟨i, hi, hEq⟩ := List.mem_iff_getElem.mp hp'
    have hDropLen : (L.drop (k.val + 1)).length = n - (k.val + 1) := by
      rw [List.length_drop, hLen]
    have hiLtLen : i < n - (k.val + 1) := by rw [← hDropLen]; exact hi
    have hkLe : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have hiBound : i + (k.val + 1) < n := by omega
    have hGetDrop : (L.drop (k.val + 1))[i]'hi =
        L[(k.val + 1) + i]'(by rw [hLen]; omega) := by
      rw [List.getElem_drop]
    have hVal : (L[(k.val + 1) + i]'(by rw [hLen]; omega)).1.val = (k.val + 1) + i := by
      simp [L, List.getElem_ofFn]
    have hPeq : p = (L.drop (k.val + 1))[i]'hi := hEq.symm
    have hPv : p.1.val = (k.val + 1) + i := by
      calc p.1.val = ((L.drop (k.val + 1))[i]'hi).1.val := by rw [hPeq]
        _ = (L[(k.val + 1) + i]'(by rw [hLen]; omega)).1.val := by rw [hGetDrop]
        _ = (k.val + 1) + i := hVal
    have : p.1.val = i + (k.val + 1) := by rw [hPv, Nat.add_comm]
    omega
  refine ⟨A, C, ?_, hA, hC⟩
  rw [hBridge, hProd]

end StableSteinberg

end AlgebraicKTheory

end
