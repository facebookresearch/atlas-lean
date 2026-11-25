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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergUpperUnipotent
public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary
public import MathlibExt.KTheory.Ring.StableElementary.Inclusions
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementarySweep

/-! # Injectivity of the upper-unipotent evaluator through `toStableE`

For `[Ring R]`, equal `toStableE` images of two ordered upper-unipotent
products force agreement of all coefficients on `a < b < n`. The ordered
product maps through `toStableE` to a finite elementary word, finite
injectivity descends to the finite word, and the accepted full-row-sweep
coefficient uniqueness recovers each coefficient. Rank `0` and `1` are
degenerate with empty root lists. This proves only coefficient equality on
`orderedPositiveRoots`; it makes no subgroup-injectivity, existence,
normal-form, TWT/Bruhat, kernel-generation, or Matsumoto claim.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

open Matrix.GeneralLinearGroup

/-- Finite generator for the ordered word, trivial off the rank bounds. -/
private def finGen (n : ℕ) (p : ℕ × ℕ) (a : R) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R :=
  if h : p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 then
    Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
      ⟨p.1, h.1⟩ ⟨p.2, h.2.1⟩ (fun heq => h.2.2 (congrArg Fin.val heq)) a
  else 1

/-- Finite ordered word over `orderedPositiveRoots n`. -/
private def finiteWord (n : ℕ) (c : ℕ × ℕ → R) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R :=
  ((orderedPositiveRoots n).map (fun p => finGen n p (c p))).prod

/-- Row-sweep coefficients from an ordered assignment. -/
private def sweepCoeff (n : ℕ) (c : ℕ × ℕ → R) (r : Fin n)
    (i : Matrix.GeneralLinearGroup.RowIdx (Fin n) r) :
    Multiplicative R :=
  Multiplicative.ofAdd (c (i.val.val, r.val))

/-- Matrix-level factor for an ordered pair, trivial off the rank bounds. -/
private def finElem (n : ℕ) (c : ℕ × ℕ → R) (p : ℕ × ℕ) :
    Matrix.GeneralLinearGroup (Fin n) R :=
  if h : p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 then
    Matrix.GeneralLinearGroup.elementary
      (⟨p.1, h.1⟩ : Fin n) (⟨p.2, h.2.1⟩ : Fin n)
      (fun heq => h.2.2 (congrArg Fin.val heq)) (c p)
  else 1

/-- Finite generators stabilize: the level-`n + 1` and level-`n` images of a
root below `n` agree in `StableE`, both equalling the natural generator. -/
private theorem finGen_transport (c : ℕ × ℕ → R) {n : ℕ} (p : ℕ × ℕ)
    (hp : p ∈ orderedPositiveRoots n) :
    AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
        (finGen (R := R) (n + 1) p (c p)) =
      AlgebraicKTheory.StableE.fromFinite (R := R) n
        (finGen (R := R) n p (c p)) := by
  have hmem : p.1 < p.2 ∧ p.2 < n := orderedPositiveRoots_mem.mp hp
  have hlt : p.1 < n := Nat.lt_trans hmem.1 hmem.2
  have hne : p.1 ≠ p.2 := ne_of_lt hmem.1
  have h1 : p.1 < n + 1 ∧ p.2 < n + 1 ∧ p.1 ≠ p.2 :=
    ⟨Nat.lt_succ_of_lt hlt, Nat.lt_succ_of_lt hmem.2, hne⟩
  have h0 : p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 := ⟨hlt, hmem.2, hne⟩
  have e1 : finGen (R := R) (n + 1) p (c p) =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨p.1, h1.1⟩ : Fin (n + 1)) (⟨p.2, h1.2.1⟩ : Fin (n + 1))
        (fun heq => h1.2.2 (congrArg Fin.val heq)) (c p) := by
    unfold finGen
    rw [dite_eq_left h1]
  have e0 : finGen (R := R) n p (c p) =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨p.1, h0.1⟩ : Fin n) (⟨p.2, h0.2.1⟩ : Fin n)
        (fun heq => h0.2.2 (congrArg Fin.val heq)) (c p) := by
    unfold finGen
    rw [dite_eq_left h0]
  rw [e1, e0, AlgebraicKTheory.StableE.fromFinite_elementary,
    AlgebraicKTheory.StableE.fromFinite_elementary]
  have hN1 := AlgebraicKTheory.StableE.natElementary_fin (R := R)
    (n := n + 1) (i := (⟨p.1, h1.1⟩ : Fin (n + 1)))
    (j := (⟨p.2, h1.2.1⟩ : Fin (n + 1)))
    (fun heq => h1.2.2 (congrArg Fin.val heq)) (c p)
  have hN0 := AlgebraicKTheory.StableE.natElementary_fin (R := R)
    (n := n) (i := (⟨p.1, h0.1⟩ : Fin n))
    (j := (⟨p.2, h0.2.1⟩ : Fin n))
    (fun heq => h0.2.2 (congrArg Fin.val heq)) (c p)
  exact hN1.symm.trans hN0

/-- The ordered product maps through `toStableE` to the finite word.
Proved by rank induction via the public successor factorization, so the
private root generator is never referenced outside this file. -/
private theorem toStableE_upper_eq_fromFinite (n : ℕ)
    (c : ℕ × ℕ → R) :
    toStableE (R := R) (upperUnipotentProd (R := R) n c) =
      AlgebraicKTheory.StableE.fromFinite (R := R) n
        (finiteWord (R := R) n c) := by
  induction n with
  | zero =>
    have hL : upperUnipotentProd (R := R) 0 c = 1 :=
      upperUnipotentProd_zero c
    have hR : finiteWord (R := R) 0 c = 1 := by
      simp [finiteWord, orderedPositiveRoots_zero]
    rw [hL, hR, map_one, map_one]
  | succ n ih =>
    have hunfold : finiteWord (R := R) (n + 1) c =
        (((orderedPositiveRoots n).map
          (fun p => finGen (R := R) (n + 1) p (c p)))).prod *
        ((((List.range n).map (fun i => (i, n))).map
          (fun p => finGen (R := R) (n + 1) p (c p)))).prod := by
      unfold finiteWord
      rw [orderedPositiveRoots_succ, List.map_append, List.prod_append]
    rw [upperUnipotentProd_succ, map_mul, ih, hunfold, map_mul]
    congr 1
    · rw [MonoidHom.map_list_prod]
      unfold finiteWord
      rw [MonoidHom.map_list_prod, List.map_map, List.map_map]
      apply congrArg
      refine List.map_congr_left
        (fun p hp => (finGen_transport (n := n) c p hp).symm)
    · have hcol : ∀ i ∈ List.range n,
          toStableE (R := R)
            (if h : i ≠ n then x (R := R) i n h (c (i, n)) else 1) =
            AlgebraicKTheory.StableE.fromFinite (R := R) (n + 1)
              (finGen (R := R) (n + 1) (i, n) (c (i, n))) := by
        intro i hi
        have hi_lt : i < n := List.mem_range.mp hi
        have hine : i ≠ n := ne_of_lt hi_lt
        have hi1 : i < n + 1 := Nat.lt_succ_of_lt hi_lt
        have hn1 : n < n + 1 := Nat.lt_succ_self n
        have hcond : i < n + 1 ∧ n < n + 1 ∧ i ≠ n :=
          ⟨hi1, hn1, hine⟩
        have efin : finGen (R := R) (n + 1) (i, n) (c (i, n)) =
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨i, hi1⟩ : Fin (n + 1)) (⟨n, hn1⟩ : Fin (n + 1))
              (fun heq => hine (congrArg Fin.val heq))
              (c (i, n)) := by
          unfold finGen
          rw [dite_eq_left hcond]
        rw [dite_eq_left hine, efin,
          AlgebraicKTheory.StableE.fromFinite_elementary,
          toStableE_x]
        exact AlgebraicKTheory.StableE.natElementary_fin (R := R)
          (n := n + 1) (i := (⟨i, hi1⟩ : Fin (n + 1)))
          (j := (⟨n, hn1⟩ : Fin (n + 1)))
          (fun heq => hine (congrArg Fin.val heq)) (c (i, n))
      have hcolFuse : ((((List.range n).map (fun i => (i, n))).map
            (fun p => finGen (R := R) (n + 1) p (c p)))) =
          ((List.range n).map
            (fun i => finGen (R := R) (n + 1) (i, n) (c (i, n)))) :=
        List.map_map
      rw [MonoidHom.map_list_prod, hcolFuse, MonoidHom.map_list_prod,
        List.map_map, List.map_map]
      apply congrArg
      refine List.map_congr_left (fun i hi => hcol i hi)

/-- Pure list identity: ordered roots are the join of per-column ranges. -/
private theorem orderedRoots_eq_joinRange (n : ℕ) :
    orderedPositiveRoots n =
      ((List.range n).map
        (fun r => (List.range r).map (fun i => (i, r)))).flatten := by
  induction n with
  | zero => simp [orderedPositiveRoots_zero]
  | succ m ih =>
    rw [orderedPositiveRoots_succ, ih]
    simp [List.range_succ, List.map_append, List.flatten_append]

/-- Ascending enumeration of a row index type. -/
private def rowIdxList (n : ℕ) (r : Fin n) : List (RowIdx (Fin n) r) :=
  (List.range r.val).pmap
    (fun k hk =>
      (⟨⟨k, Nat.lt_trans (List.mem_range.mp hk) r.isLt⟩,
        List.mem_range.mp hk⟩ :
        RowIdx (Fin n) r))
    (fun _ hk => hk)

private theorem rowIdxList_nodup (n : ℕ) (r : Fin n) :
    (rowIdxList n r).Nodup := by
  unfold rowIdxList
  apply List.Nodup.pmap
  · intro a _ b _ hab
    simpa using hab
  · exact List.nodup_range

private theorem rowIdxList_mem_all (n : ℕ) (r : Fin n)
    (i : RowIdx (Fin n) r) : i ∈ rowIdxList n r := by
  unfold rowIdxList
  have hval : i.val.val < r.val := Fin.lt_def.mp i.prop
  have hmem : i.val.val ∈ List.range r.val := List.mem_range.mpr hval
  have heq : (⟨⟨i.val.val, Nat.lt_trans hval r.isLt⟩, hval⟩ :
        RowIdx (Fin n) r) = i := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  rw [← heq]
  exact List.mem_pmap.mpr ⟨i.val.val, hmem, rfl⟩

/-- Inner row list maps to the column range pairs. -/
private theorem rowIdxList_pair_eq_range (n : ℕ) (r : Fin n) :
    (rowIdxList n r).map (fun i => (i.val.val, r.val)) =
      (List.range r.val).map (fun k => (k, r.val)) := by
  unfold rowIdxList
  rw [List.map_pmap]
  have hcongr : ∀ k (hk : k ∈ List.range r.val),
      (((⟨⟨k, Nat.lt_trans (List.mem_range.mp hk) r.isLt⟩,
        List.mem_range.mp hk⟩ :
        RowIdx (Fin n) r)).val.val, r.val) = (k, r.val) := by
    intro k hk
    rfl
  have hrewrite : List.pmap
        (fun k hk =>
          (((⟨⟨k, Nat.lt_trans (List.mem_range.mp hk) r.isLt⟩,
            List.mem_range.mp hk⟩ :
            RowIdx (Fin n) r)).val.val, r.val))
        (List.range r.val) (fun _ hk => hk) =
      List.pmap (fun k _ => (k, r.val)) (List.range r.val)
        (fun _ hk => hk) := by
    apply List.pmap_congr_left
    intro k hk h1 h2
    exact hcongr k hk
  rw [hrewrite]
  exact List.pmap_eq_map _

/-- Each sweep is the ascending column list product. -/
private theorem rowSweep_eq_colProd (n : ℕ) (c : ℕ × ℕ → R)
    (r : Fin n) :
    rowSweep (R := R) r (sweepCoeff (R := R) n c r) =
      (((rowIdxList n r).map
        (fun i => Matrix.GeneralLinearGroup.elementary i.val r
          (ne_of_lt i.prop) ((sweepCoeff (R := R) n c r i).toAdd))).prod :
        Matrix.GeneralLinearGroup (Fin n) R) := by
  have hcomm : ((Finset.univ : Finset (RowIdx (Fin n) r)) : Set _).Pairwise
      fun a b =>
        Commute (rowFamily (R := R) r a (sweepCoeff (R := R) n c r a))
          (rowFamily (R := R) r b (sweepCoeff (R := R) n c r b)) := by
    intro a _ b _ hab
    exact rowFamily_commute (R := R) r hab _ _
  have happly : rowSweep (R := R) r (sweepCoeff (R := R) n c r) =
      Finset.univ.noncommProd
        (fun i => rowFamily (R := R) r i (sweepCoeff (R := R) n c r i))
        hcomm := rfl
  have huniv : (rowIdxList n r).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact List.mem_toFinset.mpr (rowIdxList_mem_all n r i)
  have hnodup := rowIdxList_nodup n r
  have h2 : (rowIdxList n r).toFinset.noncommProd
        (fun i => rowFamily (R := R) r i (sweepCoeff (R := R) n c r i))
        (by rw [huniv]; exact hcomm) =
      ((rowIdxList n r).map
        (fun i => rowFamily (R := R) r i
          (sweepCoeff (R := R) n c r i))).prod := by
    rw [Finset.noncommProd_toFinset _ _ _ hnodup]
  have heq : Finset.univ.noncommProd
        (fun i => rowFamily (R := R) r i (sweepCoeff (R := R) n c r i))
        hcomm =
      (rowIdxList n r).toFinset.noncommProd
        (fun i => rowFamily (R := R) r i (sweepCoeff (R := R) n c r i))
        (by rw [huniv]; exact hcomm) := by
    apply Finset.noncommProd_congr
    · exact huniv.symm
    · intro x hx
      rfl
  rw [happly, heq, h2]
  apply congrArg
  apply List.map_congr_left
  intro i _
  rfl

/-- Coerced finite generators agree with the matrix factors on roots. -/
private theorem coe_finGen_eq (n : ℕ) (c : ℕ × ℕ → R) (p : ℕ × ℕ)
    (hp : p ∈ orderedPositiveRoots n) :
    ((finGen (R := R) n p (c p) :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) =
      finElem (R := R) n c p := by
  have hmem : p.1 < p.2 ∧ p.2 < n := orderedPositiveRoots_mem.mp hp
  have h : p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 :=
    ⟨Nat.lt_trans hmem.1 hmem.2, hmem.2, ne_of_lt hmem.1⟩
  unfold finGen finElem
  simp only [dite_eq_left h]
  rw [Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary]

/-- A mapped flattened product splits into per-block products. -/
private theorem flattenMapProd (n : ℕ) (L : List (List (ℕ × ℕ)))
    (F : ℕ × ℕ → Matrix.GeneralLinearGroup (Fin n) R) :
    (((L.flatten).map F).prod) =
      (((L.map (fun l => ((l.map F).prod)))).prod) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatten_cons, List.map_append, List.prod_append, ih,
      List.map_cons, List.prod_cons]

/-- Finite word coercion equals the full row-sweep product. -/
private theorem coe_finiteWord_eq_sweepProd (n : ℕ)
    (c : ℕ × ℕ → R) :
    ((finiteWord (R := R) n c : Matrix.GeneralLinearGroup.elementarySubgroup
      (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) =
      (List.ofFn (fun r : Fin n =>
        rowSweep (R := R) r (sweepCoeff (R := R) n c r))).prod := by
  have hfin : ((finiteWord (R := R) n c :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) =
      (((orderedPositiveRoots n).map (finElem (R := R) n c)).prod) := by
    unfold finiteWord
    rw [SubmonoidClass.coe_list_prod]
    simp only [List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro p hp
    exact coe_finGen_eq n c p hp
  have hrow : ∀ r : Fin n,
      rowSweep (R := R) r (sweepCoeff (R := R) n c r) =
        ((((List.range r.val).map (fun k => (k, r.val))).map
          (finElem (R := R) n c))).prod := by
    intro r
    rw [rowSweep_eq_colProd, ← rowIdxList_pair_eq_range,
      List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro i _
    change Matrix.GeneralLinearGroup.elementary i.val r
        (ne_of_lt i.prop) ((sweepCoeff (R := R) n c r i).toAdd) =
      finElem (R := R) n c (i.val.val, r.val)
    unfold sweepCoeff finElem
    have h1 : i.val.val < r.val := Fin.lt_def.mp i.prop
    have h2 : r.val < n := r.isLt
    have hcond : (i.val.val, r.val).1 < n ∧
        (i.val.val, r.val).2 < n ∧
        (i.val.val, r.val).1 ≠ (i.val.val, r.val).2 :=
      ⟨Nat.lt_trans h1 h2, h2, ne_of_lt h1⟩
    rw [dite_eq_left hcond]
    rfl
  have hflat := flattenMapProd n
    ((List.range n).map (fun r => (List.range r).map (fun i => (i, r))))
    (finElem (R := R) n c)
  have houter : (List.finRange n).map
      (fun r : Fin n => ((((List.range r.val).map
        (fun k => (k, r.val))).map (finElem (R := R) n c))).prod) =
      (List.range n).map
        (fun k => ((((List.range k).map
          (fun i => (i, k))).map (finElem (R := R) n c))).prod) := by
    have hbase : (List.finRange n).map Fin.val = List.range n :=
      List.map_coe_finRange_eq_range
    have hmap := congrArg
      (fun l => l.map (fun k => ((((List.range k).map
        (fun i => (i, k))).map (finElem (R := R) n c))).prod)) hbase
    rwa [List.map_map] at hmap
  rw [hfin, List.ofFn_eq_map, orderedRoots_eq_joinRange, hflat]
  simp only [List.map_map]
  have hmap : (List.finRange n).map
      (fun r : Fin n => rowSweep (R := R) r
        (sweepCoeff (R := R) n c r)) =
      (List.finRange n).map
        (fun r : Fin n => ((((List.range r.val).map
          (fun k => (k, r.val))).map (finElem (R := R) n c))).prod) := by
    apply List.map_congr_left
    intro r _
    exact hrow r
  rw [hmap, houter]
  rfl

/-- Main injectivity: equal images force coefficient agreement. -/
public theorem upperUnipotentProd_toStableE_eq_imp_coeff_eq
    (n : ℕ) (c₁ c₂ : ℕ × ℕ → R)
    (h : toStableE (R := R) (upperUnipotentProd (R := R) n c₁) =
      toStableE (R := R) (upperUnipotentProd (R := R) n c₂)) :
    ∀ a b : ℕ, a < b → b < n → c₁ (a, b) = c₂ (a, b) := by
  intro a b hab hbn
  have hfin : finiteWord (R := R) n c₁ = finiteWord (R := R) n c₂ := by
    apply AlgebraicKTheory.StableE.fromFinite_injective (R := R) n
    rw [← toStableE_upper_eq_fromFinite, ← toStableE_upper_eq_fromFinite]
    exact h
  have hgl : ((finiteWord (R := R) n c₁ :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) =
      ((finiteWord (R := R) n c₂ :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R) :
        Matrix.GeneralLinearGroup (Fin n) R) := by
    rw [hfin]
  rw [coe_finiteWord_eq_sweepProd, coe_finiteWord_eq_sweepProd] at hgl
  have hcoeff := Matrix.GeneralLinearGroup.fullRowSweepProd_eq_imp
    (sweepCoeff (R := R) n c₁) (sweepCoeff (R := R) n c₂) hgl
  have han : a < n := Nat.lt_trans hab hbn
  let r : Fin n := ⟨b, hbn⟩
  let i : Matrix.GeneralLinearGroup.RowIdx (Fin n) r :=
    ⟨⟨a, han⟩, hab⟩
  have heq := hcoeff r i
  have h1 : sweepCoeff (R := R) n c₁ r i =
      Multiplicative.ofAdd (c₁ (a, b)) := rfl
  have h2 : sweepCoeff (R := R) n c₂ r i =
      Multiplicative.ofAdd (c₂ (a, b)) := rfl
  rw [h1, h2] at heq
  have hto := congrArg Multiplicative.toAdd heq
  simpa using hto

end StableSteinberg

end AlgebraicKTheory
