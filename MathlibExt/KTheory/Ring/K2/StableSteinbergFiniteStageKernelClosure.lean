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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteStageWeakBruhat
public import MathlibExt.KTheory.Ring.K2.StableSteinbergUpperUnipotentCollection
public import MathlibExt.KTheory.Ring.K2.StableSteinbergUpperUnipotentInjectivity
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteCentralKernelContainment
import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylWord

/-! # Finite-stage kernel closure modulo torus cocycles

For `[Field F]`, `ker StableSteinberg.toStableE ≤ torusCocycleSubgroup`.

Proof route: for `g ∈ ker`, choose `n` by `exists_mem_finiteStage` and factor
`g = u * w * v` at the same rank by `finiteStage_exists_upper_mul_weyl_mul_upper`.
Upper factors are ordered `upperUnipotentProd` words; the Weyl factor is a bounded
`weyl` list. Their `toStableE` images are the same-rank `fromFinite` images of
finite elementary words. Hence `toStableE g = 1` descends by `fromFinite_injective`
to a finite `GL` identity `U * W * V = 1`. Lifting to `SL` with the accepted
`weylSLUnit`/`UpperElementary` bridges puts the identity in Bruhat form
`U * M * V = 1` with `M` the monomial word; middle uniqueness forces `M = 1`,
so `toStableE w = 1` and `w` lies in the finite central kernel, hence in the
cocycle subgroup. Centrality rewrites `g = w * (u * v)`; the upper product maps
to one, so coefficient injectivity plus `x_zero` forces `u * v = 1`. The reverse
inclusion is the accepted `torusCocycleSubgroup_le_ker_toStableE`.

Orientation is head-left `List.prod` throughout. Ranks `0`/`1` are trivial by the
bottom-subgroup theorems. Characteristic two and `F₂` safe: only group identities
and the accepted APIs occur.

Nonclaims: no Matsumoto equivalence or naturality, no quotient injectivity, no UCE
or stable-extension faithfulness, no arbitrary Borel-through-Weyl transport, no
boundary-word confluence, no unproved finite-stage injection. Matrix Bruhat
uniqueness is used only in the elimination direction on the identity cell.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Finite elementary factor for an ordered pair, trivial off the rank bounds. -/
private def upperFinElem (n : ℕ) (p : ℕ × ℕ) (a : F) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F :=
  if h : p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2 then
    Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
      ⟨p.1, h.1⟩ ⟨p.2, h.2.1⟩ (fun heq => h.2.2 (congrArg Fin.val heq)) a
  else 1

/-- Finite elementary word for an upper coefficient assignment. -/
private def upperFinWord (n : ℕ) (c : ℕ × ℕ → F) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F :=
  ((orderedPositiveRoots n).map (fun p => upperFinElem n p (c p))).prod

/-- Each finite upper factor maps through `fromFinite` to the natural generator. -/
private theorem upperFinElem_fromFinite_eq (n : ℕ) (p : ℕ × ℕ) (c : F)
    (hmem : p ∈ orderedPositiveRoots n) :
    StableE.fromFinite (R := F) n (upperFinElem n p c) =
      StableE.natElementary (R := F) p.1 p.2 (ne_of_lt (orderedPositiveRoots_mem.mp hmem).1) c := by
  obtain ⟨i, j⟩ := p
  simp only at hmem ⊢
  have hmem' := orderedPositiveRoots_mem.mp hmem
  have hlt : i < j := hmem'.1
  have hbn : j < n := hmem'.2
  have han : i < n := Nat.lt_trans hlt hbn
  have hne : i ≠ j := ne_of_lt hlt
  have hcond : i < n ∧ j < n ∧ i ≠ j := ⟨han, hbn, hne⟩
  have helem : upperFinElem n (i, j) c =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨i, han⟩ : Fin n) (⟨j, hbn⟩ : Fin n)
        (fun heq => hne (congrArg Fin.val heq)) c := by
    unfold upperFinElem
    rw [dite_eq_left hcond]
  rw [helem, StableE.fromFinite_elementary]
  have hfin : StableE.elementary (R := F) n (⟨i, han⟩ : Fin n) (⟨j, hbn⟩ : Fin n)
      (fun heq => hne (congrArg Fin.val heq)) c =
      StableE.natElementary (R := F) i j hne c := by
    rw [← StableE.natElementary_fin]
  rw [hfin]

/-- Finite generators stabilize across ranks through the natural generator. -/
private theorem upperFinElem_transport (c : ℕ × ℕ → F) {n : ℕ} (p : ℕ × ℕ)
    (hp : p ∈ orderedPositiveRoots n) :
    StableE.fromFinite (R := F) (n + 1) (upperFinElem (n + 1) p (c p)) =
      StableE.fromFinite (R := F) n (upperFinElem n p (c p)) := by
  have hmem_n1 : p ∈ orderedPositiveRoots (n + 1) := by
    have hmem := orderedPositiveRoots_mem.mp hp
    exact orderedPositiveRoots_mem.mpr ⟨hmem.1, Nat.lt_succ_of_lt hmem.2⟩
  rw [upperFinElem_fromFinite_eq (n + 1) p (c p) hmem_n1,
    upperFinElem_fromFinite_eq n p (c p) hp]

/-- `toStableE` of the ordered upper product is the finite image. -/
private theorem toStableE_upper_eq (n : ℕ) (c : ℕ × ℕ → F) :
    toStableE (R := F) (upperUnipotentProd (R := F) n c) =
      StableE.fromFinite (R := F) n (upperFinWord n c) := by
  induction n with
  | zero =>
    have hL : upperUnipotentProd (R := F) 0 c = 1 := upperUnipotentProd_zero c
    have hR : upperFinWord (n := 0) (c := c) = 1 := by
      unfold upperFinWord
      rw [orderedPositiveRoots_zero]
      simp
    rw [hL, hR, map_one, map_one]
  | succ n ih =>
    have hunfold : upperFinWord (n + 1) c =
        (((orderedPositiveRoots n).map
          (fun p => upperFinElem (n + 1) p (c p)))).prod *
        ((((List.range n).map (fun i => (i, n))).map
          (fun p => upperFinElem (n + 1) p (c p)))).prod := by
      unfold upperFinWord
      rw [orderedPositiveRoots_succ, List.map_append, List.prod_append]
    rw [upperUnipotentProd_succ, map_mul, ih, hunfold, map_mul]
    congr 1
    · rw [MonoidHom.map_list_prod]
      unfold upperFinWord
      rw [MonoidHom.map_list_prod, List.map_map, List.map_map]
      apply congrArg
      refine List.map_congr_left
        (fun p hp => (upperFinElem_transport c p hp).symm)
    · have hcol : ∀ i ∈ List.range n,
          toStableE (R := F)
            (if h : i ≠ n then x (R := F) i n h (c (i, n)) else 1) =
            StableE.fromFinite (R := F) (n + 1)
              (upperFinElem (n + 1) (i, n) (c (i, n))) := by
        intro i hi
        have hi_lt : i < n := List.mem_range.mp hi
        have hine : i ≠ n := Nat.ne_of_lt hi_lt
        have hi1 : i < n + 1 := Nat.lt_succ_of_lt hi_lt
        have hn1 : n < n + 1 := Nat.lt_succ_self n
        have hcond : i < n + 1 ∧ n < n + 1 ∧ i ≠ n := ⟨hi1, hn1, hine⟩
        have efin : upperFinElem (n + 1) (i, n) (c (i, n)) =
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨i, hi1⟩ : Fin (n + 1)) (⟨n, hn1⟩ : Fin (n + 1))
              (fun heq => hine (congrArg Fin.val heq)) (c (i, n)) := by
          unfold upperFinElem
          rw [dite_eq_left hcond]
        rw [dite_eq_left hine, efin, StableE.fromFinite_elementary, toStableE_x]
        exact StableE.natElementary_fin (R := F)
          (n := n + 1) (i := (⟨i, hi1⟩ : Fin (n + 1)))
          (j := (⟨n, hn1⟩ : Fin (n + 1)))
          (fun heq => hine (congrArg Fin.val heq)) (c (i, n))
      have hcolFuse : ((((List.range n).map (fun i => (i, n))).map
            (fun p => upperFinElem (n + 1) p (c p)))) =
          ((List.range n).map
            (fun i => upperFinElem (n + 1) (i, n) (c (i, n)))) :=
        List.map_map
      rw [MonoidHom.map_list_prod, hcolFuse, MonoidHom.map_list_prod,
        List.map_map, List.map_map]
      apply congrArg
      refine List.map_congr_left (fun i hi => hcol i hi)

/-- Vanishing coefficients give the identity, by rank induction via `x_zero`. -/
private theorem upperProd_one_of_zero_on_roots (n : ℕ) (d : ℕ × ℕ → F)
    (h : ∀ p ∈ orderedPositiveRoots n, d p = 0) :
    upperUnipotentProd (R := F) n d = 1 := by
  induction n with
  | zero => exact upperUnipotentProd_zero d
  | succ n ih =>
    have hpre : ∀ p ∈ orderedPositiveRoots n, d p = 0 := by
      intro p hp
      have hmem := orderedPositiveRoots_mem.mp hp
      have hmem' : p ∈ orderedPositiveRoots (n + 1) :=
        orderedPositiveRoots_mem.mpr ⟨hmem.1, Nat.lt_succ_of_lt hmem.2⟩
      exact h p hmem'
    have hcol : ∀ i ∈ List.range n,
        (if hh : i ≠ n then x (R := F) i n hh (d (i, n)) else 1) = 1 := by
      intro i hi
      have hi_lt : i < n := List.mem_range.mp hi
      have hine : i ≠ n := Nat.ne_of_lt hi_lt
      have hmem : (i, n) ∈ orderedPositiveRoots (n + 1) :=
        orderedPositiveRoots_mem.mpr ⟨hi_lt, Nat.lt_succ_self n⟩
      have hd0 : d (i, n) = 0 := h (i, n) hmem
      rw [dite_eq_left hine, hd0]
      exact x_zero i n hine
    rw [upperUnipotentProd_succ, ih hpre]
    have hprod : ((List.range n).map (fun i =>
        if hh : i ≠ n then x (R := F) i n hh (d (i, n)) else 1)).prod = 1 := by
      rw [List.prod_eq_one]
      intro g hg
      rw [List.mem_map] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      exact hcol i hi
    rw [hprod, one_mul]

/-- Finite elementary triple word for a bounded Weyl list. -/
private def weylFinTriple (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F :=
  (List.ofFn (fun k =>
    Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
      (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
      (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) *
    Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
      (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
      (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : F)) *
    Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
      (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
      (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F))).prod

/-- `toStableE` of a bounded Weyl word is the finite triple image. -/
private theorem toStableE_weylWord_eq (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    toStableE (R := F)
        ((List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (u k))).prod) =
      StableE.fromFinite (R := F) n (weylFinTriple n m a b ha hb hab u) := by
  rw [finiteWeyl_list_toStableE_eq n m a b ha hb hab u]
  unfold weylFinTriple
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  have hfun : (fun k =>
        StableE.elementary (R := F) n ⟨a k, ha k⟩ ⟨b k, hb k⟩
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) *
        StableE.elementary (R := F) n ⟨b k, hb k⟩ ⟨a k, ha k⟩
          (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : F)) *
        StableE.elementary (R := F) n ⟨a k, ha k⟩ ⟨b k, hb k⟩
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F)) =
      (⇑(StableE.fromFinite F n) ∘ fun k =>
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
          (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : F)) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F)) := by
    funext k
    simp only [Function.comp_apply, map_mul, StableE.fromFinite_elementary]
  rw [hfun]

/-- Upper `SL` word over the ordered roots. -/
private def upperSLWord (n : ℕ) (c : ℕ × ℕ → F) :
    Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F :=
  ((orderedPositiveRoots n).map (fun p =>
    if hlt : p.1 < p.2 then
      if hn : p.1 < n ∧ p.2 < n then
        Matrix.GeneralLinearGroup.UpperElementary.elementary
          (⟨p.1, hn.1⟩ : Fin n) (⟨p.2, hn.2⟩ : Fin n)
          (by simpa [Fin.lt_def] using hlt) (c p)
      else 1
    else 1)).prod

/-- Bundled Weyl word for bounded natural-number data. -/
private def boundedWeylWord (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    Matrix.GeneralLinearGroup.FiniteWeylWord F (Fin n) :=
  Matrix.GeneralLinearGroup.FiniteWeylWord.ofBoundedNat
    a b ha hb hab u

/-- Weyl `SL` word for a bounded list. -/
private noncomputable def weylSLWord (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  Matrix.GeneralLinearGroup.FiniteWeylWord.specialLinearEval
    (boundedWeylWord n m a b ha hb hab u)

/-- Monomial word for a bounded list. -/
private noncomputable def weylMonomialWord (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    Matrix.GeneralLinearGroup.MonomialSL F (Fin n) :=
  Matrix.GeneralLinearGroup.FiniteWeylWord.monomialSLEval
    (boundedWeylWord n m a b ha hb hab u)

/-- The Weyl `SL` word is the monomial image. -/
private theorem weylSLWord_eq_monomial (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    weylSLWord n m a b ha hb hab u =
      Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
        (weylMonomialWord n m a b ha hb hab u) := by
  exact
    Matrix.GeneralLinearGroup.FiniteWeylWord.specialLinearEval_eq_monomialSLHom
      (boundedWeylWord n m a b ha hb hab u)

/-- `SL` Weyl units coerce to the subgroup triple word factors. -/
private theorem weylSLUnit_toGL_eq_triple (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) (k : Fin m) :
    Matrix.SpecialLinearGroup.toGL
      (Matrix.GeneralLinearGroup.weylSLUnit
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (u k)) =
      ((Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) := by
  apply Units.ext
  simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
    Matrix.GeneralLinearGroup.coe_elementary]

/-- The `SL` Weyl word coerces to the subgroup triple word. -/
private theorem weylSLWord_toGL_eq (n m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ) :
    Matrix.SpecialLinearGroup.toGL (weylSLWord n m a b ha hb hab u) =
      ((weylFinTriple n m a b ha hb hab u :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) := by
  have hfunS : (Matrix.SpecialLinearGroup.toGL ∘ (fun k : Fin m =>
      Matrix.GeneralLinearGroup.weylSLUnit (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (u k))) =
      (Subgroup.subtype
        (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) ∘
        (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (↑(u k) : F))) :=
    funext fun k => weylSLUnit_toGL_eq_triple n m a b ha hb hab u k
  unfold weylSLWord boundedWeylWord
  rw [Matrix.GeneralLinearGroup.FiniteWeylWord.specialLinearEval_ofBoundedNat]
  unfold weylFinTriple
  rw [map_list_prod, List.map_ofFn, hfunS, ← List.map_ofFn, ← map_list_prod]
  rfl

/-- The Weyl factor maps to one once its monomial word is trivial. -/
private theorem weyl_toStableE_eq_one_of_monomial_eq_one (n m : ℕ)
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ)
    (hmono : weylMonomialWord n m a b ha hb hab u = 1) :
    toStableE (R := F)
        ((List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (u k))).prod) = 1 := by
  have hSL1 : weylSLWord n m a b ha hb hab u = 1 := by
    rw [weylSLWord_eq_monomial, hmono, map_one]
  have htriple : weylFinTriple n m a b ha hb hab u = 1 := by
    apply Subtype.ext
    have h := weylSLWord_toGL_eq n m a b ha hb hab u
    rw [hSL1, map_one] at h
    simpa using h.symm
  rw [toStableE_weylWord_eq n m a b ha hb hab u, htriple, map_one]

/-- Upper factors agree at the matrix level. -/
private theorem upperFactor_toGL_eq (n : ℕ) (c : ℕ × ℕ → F) (a b : ℕ)
    (hab : a < b) (hbn : b < n) :
    ((upperFinElem n (a, b) (c (a, b)) :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) =
    (((if hlt : a < b then
      if hn : a < n ∧ b < n then
        Matrix.GeneralLinearGroup.UpperElementary.elementary
          (⟨a, hn.1⟩ : Fin n) (⟨b, hn.2⟩ : Fin n)
          (by simpa [Fin.lt_def] using hlt) (c (a, b))
      else 1
    else 1 : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F)) :
      Matrix.GeneralLinearGroup (Fin n) F) := by
  have han : a < n := Nat.lt_trans hab hbn
  have hcond : a < n ∧ b < n ∧ a ≠ b := ⟨han, hbn, ne_of_lt hab⟩
  unfold upperFinElem
  rw [dite_eq_left hcond, dite_eq_left hab, dite_eq_left ⟨han, hbn⟩,
    Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
    Matrix.GeneralLinearGroup.UpperElementary.coe_elementary]

/-- Upper subgroup word coerces to the upper `SL` word. -/
private theorem upperFinWord_toGL_eq (n : ℕ) (c : ℕ × ℕ → F) :
    ((upperFinWord n c :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) =
    ((upperSLWord n c :
      Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) := by
  unfold upperFinWord upperSLWord
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
    List.map_map, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro p hp
  obtain ⟨a, b⟩ := p
  have hmem : a < b ∧ b < n := orderedPositiveRoots_mem.mp hp
  simp only [Function.comp_def]
  exact upperFactor_toGL_eq n c a b hmem.1 hmem.2

/-- Bruhat elimination forces the Weyl image to one. -/
private theorem weylWord_toStableE_eq_one_of_ker
    (n : ℕ) (cu cv : ℕ × ℕ → F) (m : ℕ) (a b : Fin m → ℕ)
    (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ)
    (hker : toStableE (R := F)
      (upperUnipotentProd (R := F) n cu *
        (List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (u k))).prod *
        upperUnipotentProd (R := F) n cv) = 1) :
    toStableE (R := F)
        ((List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (u k))).prod) = 1 := by
  have hUu : toStableE (R := F) (upperUnipotentProd (R := F) n cu) =
      StableE.fromFinite (R := F) n (upperFinWord n cu) :=
    toStableE_upper_eq n cu
  have hUv : toStableE (R := F) (upperUnipotentProd (R := F) n cv) =
      StableE.fromFinite (R := F) n (upperFinWord n cv) :=
    toStableE_upper_eq n cv
  have hW : toStableE (R := F)
        ((List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (u k))).prod) =
      StableE.fromFinite (R := F) n (weylFinTriple n m a b ha hb hab u) :=
    toStableE_weylWord_eq n m a b ha hb hab u
  have hfrom : StableE.fromFinite (R := F) n
      (upperFinWord n cu * weylFinTriple n m a b ha hb hab u *
        upperFinWord n cv) = 1 := by
    have hker' := hker
    rw [map_mul, map_mul, hUu, hW, hUv, ← map_mul, ← map_mul] at hker'
    exact hker'
  have hsub : upperFinWord n cu * weylFinTriple n m a b ha hb hab u *
      upperFinWord n cv = 1 := by
    apply StableE.fromFinite_injective (R := F) n
    rw [hfrom, map_one]
  have helim : Matrix.GeneralLinearGroup.bruhatMiddle
      (Matrix.GeneralLinearGroup.UpperElementary.toSLHom (upperSLWord n cu) *
        Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
          (weylMonomialWord n m a b ha hb hab u) *
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom (upperSLWord n cv)) =
      weylMonomialWord n m a b ha hb hab u :=
    Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ _ _ _ rfl
  have hbm1 : Matrix.GeneralLinearGroup.bruhatMiddle
      (1 : Matrix.SpecialLinearGroup (Fin n) F) = 1 := by
    have hfac : (1 : Matrix.SpecialLinearGroup (Fin n) F) =
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom
          (1 : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F) *
        Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
          (1 : Matrix.GeneralLinearGroup.MonomialSL F (Fin n)) *
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom
          (1 : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F) := by
      simp
    exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ 1 1 1 hfac
  have hmid : Matrix.SpecialLinearGroup.toGL
        (Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
          (weylMonomialWord n m a b ha hb hab u)) =
      ((weylFinTriple n m a b ha hb hab u :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
        Matrix.GeneralLinearGroup (Fin n) F) := by
    rw [← weylSLWord_eq_monomial]
    exact weylSLWord_toGL_eq n m a b ha hb hab u
  have hGL : ((upperFinWord n cu :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
        Matrix.GeneralLinearGroup (Fin n) F) *
      ((weylFinTriple n m a b ha hb hab u :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
        Matrix.GeneralLinearGroup (Fin n) F) *
      ((upperFinWord n cv :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
        Matrix.GeneralLinearGroup (Fin n) F) = 1 := by
    have h : (Subgroup.subtype
          (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F))
          (upperFinWord n cu * weylFinTriple n m a b ha hb hab u *
            upperFinWord n cv) =
        (Subgroup.subtype
          (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F)) 1 :=
      congrArg _ hsub
    rwa [map_mul, map_mul, map_one] at h
  have hg1 : Matrix.GeneralLinearGroup.UpperElementary.toSLHom (upperSLWord n cu) *
        Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
          (weylMonomialWord n m a b ha hb hab u) *
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom (upperSLWord n cv) =
        1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_one,
      Matrix.GeneralLinearGroup.UpperElementary.toGL_toSLHom,
      Matrix.GeneralLinearGroup.UpperElementary.toGL_toSLHom,
      hmid, ← upperFinWord_toGL_eq n cu, ← upperFinWord_toGL_eq n cv]
    exact hGL
  have hmono : weylMonomialWord n m a b ha hb hab u = 1 := by
    have h := helim
    rw [hg1, hbm1] at h
    exact h.symm
  exact weyl_toStableE_eq_one_of_monomial_eq_one n m a b ha hb hab u hmono

/-- The Weyl factor lies in the cocycle subgroup once its image is trivial. -/
private theorem weyl_mem_cocycle_of_image_one (n : ℕ) (w : StableSteinberg F)
    (hw : w ∈ finiteWeylSubgroup (R := F) n)
    (hone : toStableE (R := F) w = 1) :
    w ∈ torusCocycleSubgroup (F := F) := by
  have hmem : w ∈ finiteCentralKernelSubgroup (R := F) n :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr hone, hw⟩
  exact finiteCentralKernelSubgroup_le_torusCocycleSubgroup hmem

/-- The upper product is trivial once its image is trivial. -/
private theorem upperMul_eq_one_of_image_one (n : ℕ) (cu cv : ℕ × ℕ → F)
    (hone : toStableE (R := F)
      (upperUnipotentProd (R := F) n cu * upperUnipotentProd (R := F) n cv) = 1) :
    upperUnipotentProd (R := F) n cu * upperUnipotentProd (R := F) n cv = 1 := by
  obtain ⟨c', hc'eq, _⟩ := upperUnipotentProd_mul_closed (R := F) n cu cv
  have h0 : upperUnipotentProd (R := F) n (fun _ => 0) = 1 :=
    upperProd_one_of_zero_on_roots n _ (fun p _ => rfl)
  have him : toStableE (R := F) (upperUnipotentProd (R := F) n c') = 1 := by
    rw [← hc'eq]
    exact hone
  have hU0 : toStableE (R := F)
      (upperUnipotentProd (R := F) n (fun _ => 0)) = 1 := by
    rw [h0, map_one]
  have hcoeff := upperUnipotentProd_toStableE_eq_imp_coeff_eq (R := F) n c'
    (fun _ => 0) (him.trans hU0.symm)
  have hvan : ∀ p ∈ orderedPositiveRoots n, c' p = 0 := by
    intro p hp
    obtain ⟨a, b⟩ := p
    have hmem : a < b ∧ b < n := orderedPositiveRoots_mem.mp hp
    have hcongr := hcoeff a b hmem.1 hmem.2
    simpa using hcongr
  rw [hc'eq]
  exact upperProd_one_of_zero_on_roots n c' hvan

/-- Missing Matsumoto kernel direction. -/
public theorem ker_toStableE_le_torusCocycleSubgroup {F : Type u} [Field F] :
    MonoidHom.ker (StableSteinberg.toStableE (R := F)) ≤
      StableSteinberg.torusCocycleSubgroup (F := F) := by
  intro g hg
  have hg1 : toStableE (R := F) g = 1 := MonoidHom.mem_ker.mp hg
  obtain ⟨n, hn⟩ := exists_mem_finiteStage g
  obtain ⟨u, hu, w, v, hv, hfactor⟩ :=
    finiteStage_exists_upper_mul_weyl_mul_upper hn
  obtain ⟨cu, hcu_eq, _⟩ := upperUnipotentSubgroup_exists_prod_repr hu
  obtain ⟨cv, hcv_eq, _⟩ := upperUnipotentSubgroup_exists_prod_repr hv
  obtain ⟨m, a, b, ha, hb, hab, uu, hw_eq⟩ :=
    finiteWeylSubgroup_exists_list_repr w.2
  have hW1 : toStableE (R := F)
      ((List.ofFn (fun k => weyl (R := F) (a k) (b k) (hab k) (uu k))).prod) = 1 := by
    apply weylWord_toStableE_eq_one_of_ker n cu cv m a b ha hb hab uu
    rw [← hcu_eq, ← hcv_eq, ← hw_eq, ← hfactor]
    exact hg1
  have hw1 : toStableE (R := F) (↑w : StableSteinberg F) = 1 := by
    rw [hw_eq]
    exact hW1
  have hwmem : (↑w : StableSteinberg F) ∈ torusCocycleSubgroup :=
    weyl_mem_cocycle_of_image_one n _ w.2 hw1
  have hwcenter : (↑w : StableSteinberg F) ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center hwmem
  have h2 : (↑u : StableSteinberg F) * (↑w : StableSteinberg F) =
      (↑w : StableSteinberg F) * (↑u : StableSteinberg F) :=
    Subgroup.mem_center_iff.mp hwcenter _
  have hcomm : (↑u : StableSteinberg F) * (↑w : StableSteinberg F) *
      (↑v : StableSteinberg F) =
      (↑w : StableSteinberg F) *
        ((↑u : StableSteinberg F) * (↑v : StableSteinberg F)) := by
    rw [h2, mul_assoc]
  have huv1 : toStableE (R := F)
      ((↑u : StableSteinberg F) * (↑v : StableSteinberg F)) = 1 := by
    have hmap : toStableE (R := F) g =
        toStableE (R := F) (↑w : StableSteinberg F) *
          toStableE (R := F)
            ((↑u : StableSteinberg F) * (↑v : StableSteinberg F)) := by
      rw [hfactor, hcomm, map_mul]
    rw [hg1, hw1, one_mul] at hmap
    exact hmap.symm
  have huv_eq : (↑u : StableSteinberg F) * (↑v : StableSteinberg F) = 1 := by
    have h : upperUnipotentProd (R := F) n cu *
        upperUnipotentProd (R := F) n cv = 1 := by
      apply upperMul_eq_one_of_image_one n cu cv
      rw [← hcu_eq, ← hcv_eq]
      exact huv1
    rw [← hcu_eq, ← hcv_eq] at h
    exact h
  rw [hfactor, hcomm, huv_eq, mul_one]
  exact hwmem

/-- Kernel equality with the torus-cocycle subgroup. -/
public theorem ker_toStableE_eq_torusCocycleSubgroup {F : Type u} [Field F] :
    MonoidHom.ker (StableSteinberg.toStableE (R := F)) =
      StableSteinberg.torusCocycleSubgroup (F := F) := by
  apply le_antisymm
  · exact ker_toStableE_le_torusCocycleSubgroup
  · exact torusCocycleSubgroup_le_ker_toStableE

end StableSteinberg

end AlgebraicKTheory

end
