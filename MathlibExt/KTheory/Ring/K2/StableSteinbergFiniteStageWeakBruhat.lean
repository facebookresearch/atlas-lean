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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergBoundaryProductLists
public import MathlibExt.KTheory.Ring.K2.StableSteinbergLemmaTwentyFive
public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleWeylGeneration

/-! # Finite-stage weak Bruhat factorization

For `[Field F]`, every `g ∈ finiteStage n` factors as `g = u * w * v` with
`u, v ∈ upperUnipotentSubgroup n` and `w ∈ finiteWeylSubgroup n`.

Proof route: fixed-rank left-to-right prefix accumulation over the accepted
`finiteStage_succ_exists_lastBoundaryBlocks` word. There is no rank induction
and no rank-IH split: the boundary-block decomposition gives an arbitrary list
of last-column/last-row blocks at one fixed rank, and the accumulator
`prefix = ↑u * ↑w * b` (upper, finite-Weyl, finite-Borel) consumes blocks on
the right. Last-column blocks are wholly upper (`x_mem_upperUnipotentSubgroup`)
and absorbed into the pending Borel by subgroup closure. Last-row blocks go
through the Pi-to-list bridge and are consumed coefficient-by-coefficient from
the left: `x_zero` drops zero coefficients, while `x_ji_neg_inv_mul_x_ij`
factors each nonzero lower-root element exactly as upper * one arbitrary Weyl
generator * upper. Each arbitrary generator is normalized by
`weyl_eq_borel_mul_simpleWeyl_mul_borel`, and the emitted adjacent unit-one
word is consumed head-first by `lemmaTwentyFive_alternative` with structural
List induction. When Lemma 25 emits a left Borel factor, it is split by
`finiteBorel_exists_upper_mul_torus`: the upper part merges into the left
accumulator and the torus part multiplies directly into the finite-Weyl middle
via `finiteTorusSubgroup_le_finiteWeylSubgroup`. The terminal Borel is split
the same way, and the torus half is moved left past the upper half by the
explicit inverse-conjugation orientation of
`finiteTorusSubgroup_le_normalizer_upperUnipotent`. No Borel factor is ever
commuted through an arbitrary Weyl word, and no nonsingular opposite-pair
identity emitting a lower remainder is used.

Orientation is head-left `List.prod` throughout; conjugation is always
conjugator on the left. All bounds stay at the same rank. Characteristic-two
and `F₂` safe: only group identities and the accepted APIs occur.

Nonclaims: no uniqueness, no arbitrary stable Bruhat theorem, no kernel
containment, no quotient injectivity, no universal-central-extension
faithfulness, and no Matsumoto theorem. The statement is deliberately
cocycle-free: no step emits a cocycle. The cases `n = 0` and `n = 1` use the
accepted bottom-subgroup theorems.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

section Accum

variable {F : Type u} [Field F]

/-- Adjacent unit-one simple lift at `k`. Purpose: shared head-left word
alphabet for the Lemma-25 fold, so block products need no `Fin`-index
plumbing until the public boundary. Nonclaim: no generation or Bruhat claim. -/
private def adjLift (k : ℕ) : StableSteinberg F :=
  weyl (R := F) k (k + 1) (Nat.ne_of_lt (Nat.lt_succ_self k)) (1 : Fˣ)

/-- Last-column list products lie in the upper subgroup. Each factor
`x i K a` with `i < K < N` is a positive root below `N`. Purpose: whole-block
absorption of column blocks. Nonclaim: no row, Weyl, or Bruhat claim. -/
private theorem colprod_mem_upper {N K : ℕ} (hKN : K < N)
    (Cl : List (Fin K × F)) :
    lastColumnListProd (R := F) K Cl ∈
      upperUnipotentSubgroup (R := F) N := by
  induction Cl with
  | nil => exact Subgroup.one_mem _
  | cons p Cl ih =>
    have hhead : x (R := F) p.1.val K (Nat.ne_of_lt p.1.isLt) p.2 ∈
        upperUnipotentSubgroup (R := F) N :=
      x_mem_upperUnipotentSubgroup _ p.1.isLt
        (Nat.lt_trans p.1.isLt hKN) hKN _
    have hcons : lastColumnListProd (R := F) K (p :: Cl) =
        x (R := F) p.1.val K (Nat.ne_of_lt p.1.isLt) p.2 *
          lastColumnListProd (R := F) K Cl := rfl
    rw [hcons]
    exact Subgroup.mul_mem _ hhead ih

/-- One adjacent-lift absorption: `↑w * b * s = u' * ↑w' * b'` for
`s = weyl m (m + 1) 1`. Both Lemma-25 branches split the emitted left Borel
by `finiteBorel_exists_upper_mul_torus`; the torus half multiplies directly
into the Weyl middle. Purpose: single-letter fold for the word induction.
Nonclaim: no word, Bruhat, or quotient claim. -/
private theorem weyl_step {N : ℕ} (w : ↥(finiteWeylSubgroup (R := F) N))
    (b : StableSteinberg F) :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∀ {m : ℕ}, m + 1 < N →
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑w : StableSteinberg F) * b *
        weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) =
        u' * (↑w' : StableSteinberg F) * b' := by
  intro hb m hm
  have hmn : m < N := Nat.lt_of_succ_lt hm
  have hTleW : finiteTorusSubgroup (R := F) N ≤
      finiteWeylSubgroup (R := F) N :=
    finiteTorusSubgroup_le_finiteWeylSubgroup N
  rcases lemmaTwentyFive_alternative (F := F) hm w hb with
    ⟨b₁, hb₁, b₂, hb₂, hext⟩ | ⟨c₁, hc₁, c₂, hc₂, hret⟩
  · obtain ⟨u₂, hu₂, h₂, hh₂, hb₁eq⟩ := finiteBorel_exists_upper_mul_torus hb₁
    refine ⟨u₂, hu₂, ⟨h₂, hTleW hh₂⟩ * w *
      ⟨weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ),
        weyl_mem_finiteWeylSubgroup (R := F) hmn hm _ _⟩,
      b₂, hb₂, ?_⟩
    have hWcoe : ((⟨h₂, hTleW hh₂⟩ * w *
        ⟨weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ),
          weyl_mem_finiteWeylSubgroup (R := F) hmn hm _ _⟩ :
        ↥(finiteWeylSubgroup (R := F) N)) : StableSteinberg F) =
        h₂ * (↑w : StableSteinberg F) *
          weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) :=
      rfl
    rw [hext, hb₁eq, hWcoe]
    group
  · obtain ⟨u₂, hu₂, h₂, hh₂, hc₁eq⟩ := finiteBorel_exists_upper_mul_torus hc₁
    refine ⟨u₂, hu₂, ⟨h₂, hTleW hh₂⟩ * w, c₂, hc₂, ?_⟩
    have hWcoe : ((⟨h₂, hTleW hh₂⟩ * w :
        ↥(finiteWeylSubgroup (R := F) N)) : StableSteinberg F) =
        h₂ * (↑w : StableSteinberg F) := rfl
    rw [hret, hc₁eq, hWcoe]
    group

/-- Adjacent-word absorption: `↑w * b * (blk.map adjLift).prod` is again
`upper * Weyl * Borel`. Structural induction on `blk`, head-first, via
`weyl_step`; both branches strictly shorten the list. Purpose: consumes the
explicit words emitted by arbitrary-generator normalization. Nonclaim: no
Bruhat or quotient claim. -/
private theorem word_step {N : ℕ} (w : ↥(finiteWeylSubgroup (R := F) N))
    (b : StableSteinberg F) (blk : List ℕ) :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∀ _hblk : ∀ k ∈ blk, k + 1 < N,
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑w : StableSteinberg F) * b * (blk.map adjLift).prod =
        u' * (↑w' : StableSteinberg F) * b' := by
  induction blk generalizing w b with
  | nil =>
    intro hb _
    refine ⟨1, Subgroup.one_mem _, w, b, hb, ?_⟩
    rw [show (([] : List ℕ).map adjLift).prod = 1 from rfl, mul_one, one_mul]
  | cons m rest ih =>
    intro hb hblk
    have hm : m + 1 < N := hblk m (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ k ∈ rest, k + 1 < N :=
      fun k hk => hblk k (List.mem_cons.mpr (Or.inr hk))
    have hsm : adjLift m = weyl (R := F) m (m + 1)
        (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) := rfl
    have hA : (↑w : StableSteinberg F) * b * ((m :: rest).map adjLift).prod =
        ((↑w : StableSteinberg F) * b *
          weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)) *
          (rest.map adjLift).prod := by
      simp only [List.map_cons, List.prod_cons, hsm]
      group
    obtain ⟨u₁, hu₁, w₁, b₁, hb₁, hstep⟩ := weyl_step w b hb hm
    obtain ⟨u₂, hu₂, w₂, b₂, hb₂, hih⟩ := ih w₁ b₁ hb₁ hrest
    refine ⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂, w₂, b₂, hb₂, ?_⟩
    have hD : (u₁ * (↑w₁ : StableSteinberg F) * b₁) *
        (rest.map adjLift).prod =
        u₁ * ((↑w₁ : StableSteinberg F) * b₁ *
          (rest.map adjLift).prod) := by group
    rw [hA, hstep, hD, hih]
    group

/-- Arbitrary-Weyl-generator absorption: `↑w * b * weyl i j u` is again
`upper * Weyl * Borel`. The generator is normalized once by
`weyl_eq_borel_mul_simpleWeyl_mul_borel`; neighboring Borel factors merge by
closure and the middle word folds by `word_step`. Purpose: consumes the Weyl
half of each nonzero row coefficient. Nonclaim: no Bruhat or quotient claim. -/
private theorem arb_weyl_step {N : ℕ} (w : ↥(finiteWeylSubgroup (R := F) N))
    {b : StableSteinberg F} :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∀ {i j : ℕ}, i < N → j < N → ∀ (hij : i ≠ j) (u : Fˣ),
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑w : StableSteinberg F) * b * weyl (R := F) i j hij u =
        u' * (↑w' : StableSteinberg F) * b' := by
  intro hb i j hi hj hij u
  obtain ⟨mg, cg, hcg, b1g, hb1g, b2g, hb2g, hgen⟩ :=
    weyl_eq_borel_mul_simpleWeyl_mul_borel (F := F) hi hj hij u
  set blk : List ℕ := List.ofFn cg with hblk_def
  have hblk : ∀ k ∈ blk, k + 1 < N := by
    intro k hk
    rw [hblk_def, List.mem_ofFn] at hk
    obtain ⟨k', rfl⟩ := hk
    exact hcg k'
  have hW : (List.ofFn fun k => weyl (R := F) (cg k) (cg k + 1)
      (Nat.ne_of_lt (Nat.lt_succ_self (cg k))) (1 : Fˣ)).prod =
      (blk.map adjLift).prod := by
    have hfun : (fun k => weyl (R := F) (cg k) (cg k + 1)
        (Nat.ne_of_lt (Nat.lt_succ_self (cg k))) (1 : Fˣ)) =
        (adjLift ∘ cg) := by
      funext k
      rfl
    rw [hfun, hblk_def, List.map_ofFn]
  have hbb : b * b1g ∈ finiteBorelSubgroup (F := F) N :=
    Subgroup.mul_mem _ hb hb1g
  obtain ⟨u₁, hu₁, w₁, b₁, hb₁, hinner⟩ := word_step w (b * b1g) blk hbb hblk
  refine ⟨u₁, hu₁, w₁, b₁ * b2g, Subgroup.mul_mem _ hb₁ hb2g, ?_⟩
  have hr : (↑w : StableSteinberg F) * b *
      (b1g * (blk.map adjLift).prod * b2g) =
      ((↑w : StableSteinberg F) * (b * b1g) * (blk.map adjLift).prod) * b2g := by
    group
  have hs : (u₁ * (↑w₁ : StableSteinberg F) * b₁) * b2g =
      u₁ * (↑w₁ : StableSteinberg F) * (b₁ * b2g) := by group
  rw [hgen, hW, hr, hinner, hs]

/-- One last-row coefficient absorption: `↑w * b * x K i a` is again
`upper * Weyl * Borel`. Zero coefficients drop by `x_zero`; for `a ≠ 0` the
unit `u = mk0 (-(a⁻¹))` makes `a = -(↑u⁻¹)`, so `x_ji_neg_inv_mul_x_ij`
factors the lower-root element exactly as upper * arbitrary Weyl * upper.
Purpose: single leftmost step of the row-list fold. Nonclaim: no Bruhat,
quotient, or remainder claim. -/
private theorem row_coeff_step {N K i : ℕ}
    (w : ↥(finiteWeylSubgroup (R := F) N)) (b : StableSteinberg F) :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∀ (_ : i < K) (_ : K < N) (hiji : i ≠ K) (a : F),
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑w : StableSteinberg F) * b * x (R := F) K i hiji.symm a =
        u' * (↑w' : StableSteinberg F) * b' := by
  intro hb hiK hKN hiji a
  have hiN : i < N := Nat.lt_trans hiK hKN
  have hUle : upperUnipotentSubgroup (R := F) N ≤
      finiteBorelSubgroup (F := F) N :=
    upperUnipotentSubgroup_le_finiteBorelSubgroup N
  by_cases ha : a = 0
  · subst ha
    refine ⟨1, Subgroup.one_mem _, w, b, hb, ?_⟩
    simp [x_zero]
  · have hainv : -(a⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ha)
    let u : Fˣ := Units.mk0 (-(a⁻¹)) hainv
    have hcoe : ((u : Fˣ) : F) = -(a⁻¹) := Units.val_mk0 hainv
    have hu_inv : ((u⁻¹ : Fˣ) : F) = -a := by
      rw [Units.val_inv_eq_inv_val, hcoe, inv_neg, inv_inv]
    have ha_eq : a = -(↑u⁻¹ : F) := by rw [hu_inv, neg_neg]
    have hbase := x_ji_neg_inv_mul_x_ij (R := F) i K hiji u
    rw [← ha_eq] at hbase
    have hsol : x (R := F) K i hiji.symm a =
        x (R := F) i K hiji (-(↑u : F)) *
          weyl (R := F) i K hiji u *
          (x (R := F) i K hiji (↑u : F))⁻¹ := by
      rw [← hbase, mul_inv_cancel_right]
    have hxC : x (R := F) i K hiji (-(↑u : F)) ∈
        upperUnipotentSubgroup (R := F) N :=
      x_mem_upperUnipotentSubgroup hiji hiK hiN hKN _
    have hxB : (x (R := F) i K hiji (↑u : F))⁻¹ ∈
        upperUnipotentSubgroup (R := F) N :=
      Subgroup.inv_mem _
        (x_mem_upperUnipotentSubgroup hiji hiK hiN hKN _)
    have hbC : b * x (R := F) i K hiji (-(↑u : F)) ∈
        finiteBorelSubgroup (F := F) N :=
      Subgroup.mul_mem _ hb (hUle hxC)
    obtain ⟨u₁, hu₁, w₁, b₁, hb₁, harb⟩ :=
      arb_weyl_step w hbC hiN hKN hiji u
    have hbB : b₁ * (x (R := F) i K hiji (↑u : F))⁻¹ ∈
        finiteBorelSubgroup (F := F) N :=
      Subgroup.mul_mem _ hb₁ (hUle hxB)
    refine ⟨u₁, hu₁, w₁, b₁ * (x (R := F) i K hiji (↑u : F))⁻¹, hbB, ?_⟩
    have hA : (↑w : StableSteinberg F) * b *
        (x (R := F) i K hiji (-(↑u : F)) *
          weyl (R := F) i K hiji u *
          (x (R := F) i K hiji (↑u : F))⁻¹) =
        ((↑w : StableSteinberg F) * (b * x (R := F) i K hiji (-(↑u : F))) *
          weyl (R := F) i K hiji u) *
          (x (R := F) i K hiji (↑u : F))⁻¹ := by group
    have hD : (u₁ * (↑w₁ : StableSteinberg F) * b₁) *
        (x (R := F) i K hiji (↑u : F))⁻¹ =
        u₁ * (↑w₁ : StableSteinberg F) *
          (b₁ * (x (R := F) i K hiji (↑u : F))⁻¹) := by group
    rw [hsol, hA, harb, hD]

/-- Last-row list absorption: `↑w * b * lastRowListProd K Rl` is again
`upper * Weyl * Borel`. Structural induction on `Rl`, consuming the head
coefficient by `row_coeff_step`. Purpose: whole-block absorption of row
blocks. Nonclaim: no column, Bruhat, or quotient claim. -/
private theorem rowlist_step {N K : ℕ} (hKN : K < N)
    (w : ↥(finiteWeylSubgroup (R := F) N)) (b : StableSteinberg F)
    (Rl : List (Fin K × F)) :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑w : StableSteinberg F) * b * lastRowListProd (R := F) K Rl =
        u' * (↑w' : StableSteinberg F) * b' := by
  induction Rl generalizing w b with
  | nil =>
    intro hb
    refine ⟨1, Subgroup.one_mem _, w, b, hb, ?_⟩
    rw [show lastRowListProd (R := F) K [] = 1 from rfl, mul_one, one_mul]
  | cons p Rl ih =>
    intro hb
    have hA : lastRowListProd (R := F) K (p :: Rl) =
        x (R := F) K p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
          lastRowListProd (R := F) K Rl := rfl
    obtain ⟨u₁, hu₁, w₁, b₁, hb₁, hrow⟩ :=
      row_coeff_step w b hb p.1.isLt hKN (Nat.ne_of_lt p.1.isLt) p.2
    obtain ⟨u₂, hu₂, w₂, b₂, hb₂, hih⟩ := ih w₁ b₁ hb₁
    refine ⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂, w₂, b₂, hb₂, ?_⟩
    have hB : (↑w : StableSteinberg F) * b *
        (x (R := F) K p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2 *
          lastRowListProd (R := F) K Rl) =
        ((↑w : StableSteinberg F) * b *
          x (R := F) K p.1.val (Ne.symm (Nat.ne_of_lt p.1.isLt)) p.2) *
          lastRowListProd (R := F) K Rl := by group
    have hD : (u₁ * (↑w₁ : StableSteinberg F) * b₁) *
        lastRowListProd (R := F) K Rl =
        u₁ * ((↑w₁ : StableSteinberg F) * b₁ *
          lastRowListProd (R := F) K Rl) := by group
    rw [hA, hB, hrow, hD, hih]
    group

/-- Boundary-block word absorption: `↑wcur * b * (L.map block).prod` is again
`upper * Weyl * Borel`. Structural induction on `L`, head-first: column
blocks go through the Pi-to-list bridge into `colprod_mem_upper` and merge
into the pending Borel; row blocks go through the bridge into `rowlist_step`.
Purpose: left-to-right prefix accumulation over the fixed-rank boundary word.
Nonclaim: no rank induction, Bruhat, or quotient claim. -/
private theorem blocks_step {N K : ℕ} (hKN : K < N)
    (wcur : ↥(finiteWeylSubgroup (R := F) N)) (b : StableSteinberg F)
    (L : List (Sum ((i : Fin K) → Multiplicative F)
      ((i : Fin K) → Multiplicative F))) :
    b ∈ finiteBorelSubgroup (F := F) N →
    ∃ u' ∈ upperUnipotentSubgroup (R := F) N,
    ∃ w' : ↥(finiteWeylSubgroup (R := F) N),
    ∃ b' ∈ finiteBorelSubgroup (F := F) N,
      (↑wcur : StableSteinberg F) * b *
        (L.map (lastBoundaryBlock (R := F) K)).prod = u' * (↑w' : StableSteinberg F) * b' := by
  induction L generalizing wcur b with
  | nil =>
    intro hb
    refine ⟨1, Subgroup.one_mem _, wcur, b, hb, ?_⟩
    rw [show (([] : List (Sum ((i : Fin K) → Multiplicative F)
      ((i : Fin K) → Multiplicative F))).map
      (lastBoundaryBlock (R := F) K)).prod = 1 from rfl, mul_one, one_mul]
  | cons hd tl ih =>
    intro hb
    have hcons : ((hd :: tl).map (lastBoundaryBlock (R := F) K)).prod =
        lastBoundaryBlock (R := F) K hd *
          (tl.map (lastBoundaryBlock (R := F) K)).prod := by
      simp only [List.map_cons, List.prod_cons]
    cases hd with
    | inl c =>
      rw [hcons, lastBoundaryBlock_inl,
        lastColumnProduct_eq_lastColumnListProd_ofFn (R := F) K c]
      have hcol : lastColumnListProd (R := F) K
          (List.ofFn fun i : Fin K => (i, (c i).toAdd)) ∈
          upperUnipotentSubgroup (R := F) N := colprod_mem_upper hKN _
      have hb₁ : b * lastColumnListProd (R := F) K
          (List.ofFn fun i : Fin K => (i, (c i).toAdd)) ∈
          finiteBorelSubgroup (F := F) N :=
        Subgroup.mul_mem _ hb
          (upperUnipotentSubgroup_le_finiteBorelSubgroup N hcol)
      obtain ⟨u₂, hu₂, w₂, b₂, hb₂, hih⟩ := ih wcur _ hb₁
      refine ⟨u₂, hu₂, w₂, b₂, hb₂, ?_⟩
      have hA : (↑wcur : StableSteinberg F) * b *
          (lastColumnListProd (R := F) K
            (List.ofFn fun i : Fin K => (i, (c i).toAdd)) *
            (tl.map (lastBoundaryBlock (R := F) K)).prod) =
          (↑wcur : StableSteinberg F) *
            (b * lastColumnListProd (R := F) K
              (List.ofFn fun i : Fin K => (i, (c i).toAdd))) *
            (tl.map (lastBoundaryBlock (R := F) K)).prod := by group
      rw [hA]
      exact hih
    | inr r =>
      rw [hcons, lastBoundaryBlock_inr,
        lastRowProduct_eq_lastRowListProd_ofFn (R := F) K r]
      obtain ⟨u₁, hu₁, w₁, b₁, hb₁, hrow⟩ :=
        rowlist_step hKN wcur b
          (List.ofFn fun i : Fin K => (i, (r i).toAdd)) hb
      obtain ⟨u₂, hu₂, w₂, b₂, hb₂, hih⟩ := ih w₁ b₁ hb₁
      refine ⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂, w₂, b₂, hb₂, ?_⟩
      have hA : (↑wcur : StableSteinberg F) * b *
          (lastRowListProd (R := F) K
            (List.ofFn fun i : Fin K => (i, (r i).toAdd)) *
            (tl.map (lastBoundaryBlock (R := F) K)).prod) =
          ((↑wcur : StableSteinberg F) * b *
            lastRowListProd (R := F) K
              (List.ofFn fun i : Fin K => (i, (r i).toAdd))) *
            (tl.map (lastBoundaryBlock (R := F) K)).prod := by group
      have hD : (u₁ * (↑w₁ : StableSteinberg F) * b₁) *
          (tl.map (lastBoundaryBlock (R := F) K)).prod =
          u₁ * ((↑w₁ : StableSteinberg F) * b₁ *
            (tl.map (lastBoundaryBlock (R := F) K)).prod) := by group
      rw [hA, hrow, hD, hih]
      group

end Accum

/-- Finite-stage weak Bruhat factorization: every `g ∈ finiteStage n` is
`g = ↑u * ↑w * ↑v` with `u, v` upper-unipotent and `w` finite-Weyl, all at the
same rank `n`. Ranks `0` and `1` are trivial by the bottom-subgroup theorems;
at rank `K + 2` the boundary-block word folds left-to-right by `blocks_step`,
and the terminal Borel splits into an upper half (staying left) and a torus
half (folding into the Weyl middle, with the upper half inverse-conjugated).
Same-rank existence only.
Nonclaims: no uniqueness, no arbitrary stable Bruhat theorem, no kernel
containment, no quotient injectivity, no universal-central-extension
faithfulness, and no Matsumoto theorem. -/
public theorem finiteStage_exists_upper_mul_weyl_mul_upper
    {F : Type u} [Field F] {n : ℕ} {g : StableSteinberg F}
    (hg : g ∈ finiteStage (R := F) n) :
    ∃ u ∈ upperUnipotentSubgroup (R := F) n,
    ∃ w : ↥(finiteWeylSubgroup (R := F) n),
    ∃ v ∈ upperUnipotentSubgroup (R := F) n,
      g = ↑u * ↑w * ↑v := by
  cases n with
  | zero =>
    simp only [finiteStage_zero_eq_bot] at hg
    obtain rfl : g = 1 := Subgroup.mem_bot.mp hg
    exact ⟨1, Subgroup.one_mem _, 1, 1, Subgroup.one_mem _, by simp⟩
  | succ K =>
    cases K with
    | zero =>
      have hg1 : g ∈ finiteStage (R := F) 1 := hg
      simp only [finiteStage_one_eq_bot] at hg1
      obtain rfl : g = 1 := Subgroup.mem_bot.mp hg1
      exact ⟨1, Subgroup.one_mem _, 1, 1, Subgroup.one_mem _, by simp⟩
    | succ K =>
      obtain ⟨L, hL⟩ :=
        finiteStage_succ_exists_lastBoundaryBlocks (R := F) (n := K + 1) hg
      obtain ⟨u, hu, w, b, hb, hacc⟩ :=
        blocks_step (N := K + 1 + 1) (K := K + 1) (Nat.lt_succ_self _)
          1 1 L (Subgroup.one_mem _)
      have h1 : ((1 : ↥(finiteWeylSubgroup (R := F) (K + 1 + 1))) :
          StableSteinberg F) = 1 := rfl
      simp only [h1, one_mul, mul_one] at hacc
      obtain ⟨u₂, hu₂, h₂, hh₂, hb_eq⟩ :=
        finiteBorel_exists_upper_mul_torus hb
      have hTleW : finiteTorusSubgroup (R := F) (K + 1 + 1) ≤
          finiteWeylSubgroup (R := F) (K + 1 + 1) :=
        finiteTorusSubgroup_le_finiteWeylSubgroup _
      have h_norm_mem : h₂⁻¹ ∈
          Subgroup.normalizer (upperUnipotentSubgroup (R := F) (K + 1 + 1)) :=
        Subgroup.inv_mem _
          (finiteTorusSubgroup_le_normalizer_upperUnipotent (F := F) _ hh₂)
      have h_mem := Subgroup.mem_normalizer_iff.mp h_norm_mem u₂
      have hconj : h₂⁻¹ * u₂ * h₂ ∈
          upperUnipotentSubgroup (R := F) (K + 1 + 1) := by
        have h := h_mem.mp hu₂
        simpa [inv_inv] using h
      have hWcoe : ((w * ⟨h₂, hTleW hh₂⟩ :
          ↥(finiteWeylSubgroup (R := F) (K + 1 + 1))) : StableSteinberg F) =
          (↑w : StableSteinberg F) * h₂ := rfl
      have htorus_swap : u₂ * h₂ = h₂ * (h₂⁻¹ * u₂ * h₂) := by group
      refine ⟨u, hu, w * ⟨h₂, hTleW hh₂⟩, h₂⁻¹ * u₂ * h₂, hconj, ?_⟩
      rw [← hL, hacc, hb_eq, htorus_swap, hWcoe]
      group

end StableSteinberg

end AlgebraicKTheory

end
