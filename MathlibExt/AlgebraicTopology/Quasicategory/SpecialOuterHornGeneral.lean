/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHorn
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan

/-!
# Joyal's special outer horn filling in all dimensions

This file is packet T21, generalizing
`MathlibExt/AlgebraicTopology/Quasicategory/SpecialOuterHorn.lean`
(packet T18, dimensions `2` and `3`) to all dimensions, discharging
the blocker recorded in
`MathlibExt/AlgebraicTopology/Quasicategory/CoreKan.lean`.

## Main results

* `SSet.exists_fill_horn_left_of_isEquivalence`: for every
  quasicategory `X`, every left outer horn `Λ[n + 2, 0] ⟶ X` whose
  `(0, 1)`-edge is an equivalence extends to `Δ[n + 2]`.
* `SSet.exists_fill_horn_right_of_isEquivalence`: dually, every
  right outer horn `Λ[n + 2, n + 2] ⟶ X` whose last edge is an
  equivalence extends to `Δ[n + 2]`.
* `SSet.hasSpecialOuterHornFilling_of_quasicategory`: every
  quasicategory has `SSet.HasSpecialOuterHornFilling`.
* `SSet.kanComplex_core_of_quasicategory`: consequently (via
  `SSet.kanComplex_core_of_special_horn_filling` in
  `CoreKan.lean`), the core of every quasicategory is a Kan
  complex, also available as an instance of priority below the
  Kan-specialized instance of `CoreKan.lean`.

The proof is Dugger's filtration argument (Dugger–Spivak,
*Mapping spaces in quasi-categories*, Appendix B.9, after Joyal),
of which `SpecialOuterHorn.lean` is the case `n = 1`, carried out
at the level of simplices indexed by order embeddings
`u : Fin k ↪o Fin (N + 1)` representing subsets `S ⊆ {2, ..., N + 2}`:
round one attaches `(1, 0, 1, S)` along `Λ[|S| + 2, 2]` producing
`(1, 0, S)`; round two attaches `(0, 1, 0, S)` along `Λ[|S| + 2, 2]`
producing a provisional `(0, 1, S)'`; the correction (the two-step
argument in Joyal's slice `X / ∂Δ{2, ..., N + 2}` written out in
`X`) attaches `(0, 1, 0, 1, S)` along `Λ[|S| + 3, 2]` and
`(0, 1, 1, 0, S)` along `Λ[|S| + 3, 1]`, producing corrected
`(0, 1, 0, S)` whose `d₂` face is the prescribed `(0, 1, S)`, all
sharing the two underlying three-dimensional fillers
`(0, 1, 0, 1)` and `(0, 1, 1, 0)` at `S = ∅`; finally
`(1, 0, 2, ..., N + 2)` along `Λ[N + 2, 1]` and the
`Λ[N + 3, 2]` horn on `(0, 1, 0', 2, ..., N + 2)` give the filler.
Each round is an induction on `|S|` using only the simplex-level
inner-horn filler `SSet.exists_simplex_of_isCompatible` of
`SpecialOuterHorn.lean`. The rounds are factored through the
abstract statement `SSet.exists_filler_simplex_of_leftData`, which
takes the horn's face families `(0, S)`, `(1, S)`, `(0, 1, S)` and
inverse data for the `(0, 1)`-edge as hypotheses.

The right horns are not proved by a second filtration: the
abstract statement is applied to the opposite simplicial set.
`SSet.quasicategory_op` shows `X.op` is a quasicategory by
transporting inner horns through `opObjEquiv` with reversed face
indices, and the suffix families `(S, N + 2)`, `(S, N + 1)`,
`(S, N + 1, N + 2)` of a right horn (section
`RightHornFamilies`, built from the snoc embeddings `emb2r`,
`emb1r`, `emb12r`) are transported to the prefix families of
`X.op` along the reversed subset embeddings `revEmb`; the
inverse data of the reversed edge is the transport of the
inverse data of the last edge, with the two homotopies swapped
(section `RightHornTheorem`).

Apart from the main results above, the order-embedding notation
occurring in their statements, and a few embedding identities
pinned by the tests, every declaration in this file is private:
the embedding combinatorics and the four filtration rounds are
implementation details of the proof.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace SSet

variable {X : SSet.{u}}

section SimplexIdentities

/-- The simplicial identity `δᵢδⱼ₊₁ = δⱼδᵢ` for `i ≤ j`, at the
level of simplices (the general-index form of the private lemma of
`SpecialOuterHorn.lean`). -/
private lemma δ_δ_of_le' {n : ℕ} (s : X _⦋n + 2⦌) (i j : Fin (n + 2))
    (h : i ≤ j) :
    X.δ i (X.δ (Fin.succ j) s) = X.δ j (X.δ (Fin.castSucc i) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_δ X h) s

/-- The simplicial identity `δᵢδⱼ = δⱼ₋₁δᵢ` for `i < j`, at the
level of simplices. -/
private lemma δ_δ_of_lt' {n : ℕ} (s : X _⦋n + 2⦌) (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : Fin.castSucc i < j) :
    X.δ i (X.δ j s) = X.δ (j.pred h.ne_zero) (X.δ (Fin.castSucc i) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_δ' X h) s

/-- The `0`-face of the `0`-degeneracy of a simplex. -/
private lemma δ_zero_σ_zero {n : ℕ} (s : X _⦋n⦌) :
    X.δ (0 : Fin (n + 2)) (X.σ (0 : Fin (n + 1)) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' X
    (show (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) from rfl)) s

/-- The `1`-face of the `0`-degeneracy of a simplex. -/
private lemma δ_one_σ_zero {n : ℕ} (s : X _⦋n⦌) :
    X.δ (1 : Fin (n + 2)) (X.σ (0 : Fin (n + 1)) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' X
    (show (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) by
      ext; simp)) s

/-- The `(j + 2)`-face of the `0`-degeneracy of a simplex is the
`0`-degeneracy of the `(j + 1)`-face. -/
private lemma δ_succ_succ_σ_zero {n : ℕ} (s : X _⦋n + 1⦌) (j : Fin (n + 1)) :
    X.δ j.succ.succ (X.σ (0 : Fin (n + 2)) s) =
      X.σ (0 : Fin (n + 1)) (X.δ j.succ s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_gt' X
    (show (0 : Fin (n + 2)).succ < j.succ.succ by
      rw [Fin.lt_def]; simp)) s

end SimplexIdentities

section EmbeddingCombinatorics

-- Public: deletion of order embeddings occurs in the statement
-- of `exists_filler_simplex_of_leftData` and in the tests.
/-- Deleting the `j`-th element of an order embedding. -/
def delEmb {k N : ℕ} (u : Fin (k + 1) ↪o Fin (N + 1)) (j : Fin (k + 1)) :
    Fin k ↪o Fin (N + 1) :=
  (Fin.succAboveOrderEmb j).comp u

@[simp]
private lemma delEmb_apply {k N : ℕ} (u : Fin (k + 1) ↪o Fin (N + 1))
    (j : Fin (k + 1)) (i : Fin k) :
    delEmb u j i = u (Fin.succAbove j i) := rfl

/-- The value of `Fin.succAbove`. -/
private lemma succAbove_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (Fin.succAbove p i).val = if i.val < p.val then i.val else i.val + 1 := by
  rw [Fin.succAbove]
  split <;> simp_all [Fin.lt_def]

-- Public: this identity is pinned by the tests.
/-- Double deletion of order embeddings commutes in the usual
simplicial way: deleting `l` then `j` (for `j < l`) is deleting
`j` then `l - 1`. -/
lemma delEmb_delEmb {k N : ℕ} (u : Fin (k + 2) ↪o Fin (N + 1))
    {j l : Fin (k + 2)} (hjl : j < l) :
    delEmb (delEmb u l) (j.castLT (by
      have h1 := l.isLt
      rw [Fin.lt_def] at hjl
      omega)) =
      delEmb (delEmb u j) (l.pred (Fin.ne_zero_of_lt hjl)) := by
  ext i
  have key : Fin.succAbove l (Fin.succAbove (j.castLT (by
        have h1 := l.isLt
        rw [Fin.lt_def] at hjl
        omega)) i) =
      Fin.succAbove j (Fin.succAbove (l.pred (Fin.ne_zero_of_lt hjl)) i) := by
    ext
    simp only [succAbove_val, Fin.val_castLT]
    have hlp : (l.pred (Fin.ne_zero_of_lt hjl)).val = l.val - 1 := by
      simp [Fin.pred]
    rw [hlp]
    rw [Fin.lt_def] at hjl
    split_ifs <;> omega
  have key2 : delEmb (delEmb u l) (j.castLT (by
        have h1 := l.isLt
        rw [Fin.lt_def] at hjl
        omega)) i =
      delEmb (delEmb u j) (l.pred (Fin.ne_zero_of_lt hjl)) i := by
    simp only [delEmb_apply, key]
  rw [key2]

-- Public: used in the definitions of the public embeddings
-- `emb0` and `emb01`.
/-- Prefixing an order embedding into `Fin (N + 3)` by a smaller
element. -/
def consEmb {k N : ℕ} (a : Fin (N + 3)) (e : Fin k ↪o Fin (N + 3))
    (h : ∀ i, a < e i) : Fin (k + 1) ↪o Fin (N + 3) :=
  OrderEmbedding.ofStrictMono (Fin.cons a (fun i ↦ e i)) (by
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp at hij
    · simpa using h j
    · simp at hij
    · simpa using e.strictMono (Fin.succ_lt_succ_iff.mp hij))

@[simp]
private lemma consEmb_zero {k N : ℕ} (a : Fin (N + 3)) (e : Fin k ↪o Fin (N + 3))
    (h : ∀ i, a < e i) : consEmb a e h 0 = a := rfl

@[simp]
private lemma consEmb_succ {k N : ℕ} (a : Fin (N + 3)) (e : Fin k ↪o Fin (N + 3))
    (h : ∀ i, a < e i) (i : Fin k) : consEmb a e h i.succ = e i := rfl

private lemma range_consEmb {k N : ℕ} (a : Fin (N + 3)) (e : Fin k ↪o Fin (N + 3))
    (h : ∀ i, a < e i) :
    Set.range (consEmb a e h) = {a} ∪ Set.range e := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp
    · simp
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨i.succ, by simp⟩

/-- Deleting the first element of a prefixed embedding. -/
private lemma consEmb_comp_succAbove_zero {k N : ℕ} (a : Fin (N + 3))
    (e : Fin k ↪o Fin (N + 3)) (h : ∀ i, a < e i) :
    (Fin.succAboveOrderEmb (0 : Fin (k + 1))).comp (consEmb a e h) = e := by
  ext i
  have key : ((Fin.succAboveOrderEmb (0 : Fin (k + 1))).comp (consEmb a e h)) i =
      e i := by
    change consEmb a e h (Fin.succAbove (0 : Fin (k + 1)) i) = e i
    rw [Fin.succAbove_zero]
    simp
  rw [key]

/-- Deleting a later element of a prefixed embedding. -/
private lemma consEmb_comp_succAbove_succ {k N : ℕ} (a : Fin (N + 3))
    (e : Fin (k + 1) ↪o Fin (N + 3)) (h : ∀ i, a < e i) (j : Fin (k + 1)) :
    (Fin.succAboveOrderEmb j.succ).comp (consEmb a e h) =
      consEmb a (delEmb e j) (fun _i ↦ h _) := by
  ext i
  have key : ((Fin.succAboveOrderEmb j.succ).comp (consEmb a e h)) i =
      consEmb a (delEmb e j) (fun i ↦ h _) i := by
    change consEmb a e h (Fin.succAbove j.succ i) = consEmb a (delEmb e j) _ i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [show Fin.succAbove j.succ (0 : Fin (k + 1)) = 0 from by
        ext
        rw [succAbove_val]
        simp]
      exact (consEmb_zero a e h).trans (consEmb_zero a (delEmb e j) _).symm
    · rw [show Fin.succAbove j.succ i.succ = (Fin.succAbove j i).succ from by
        ext
        simp only [succAbove_val, Fin.val_succ]
        split_ifs <;> omega]
      simp [delEmb]
  rw [key]

-- Public: used in the definitions of the public embeddings
-- `emb0` and `emb01`.
/-- The embedding of the tail vertices `{2, ..., N + 2}`. -/
def tailEmb (N : ℕ) : Fin (N + 1) ↪o Fin (N + 3) :=
  (Fin.succAboveOrderEmb (0 : Fin (N + 2))).comp
    (Fin.succAboveOrderEmb (0 : Fin (N + 3)))

private lemma tailEmb_val (N : ℕ) (i : Fin (N + 1)) :
    (tailEmb N i).val = i.val + 2 := by
  change (Fin.succAbove (0 : Fin (N + 3)) (Fin.succAbove (0 : Fin (N + 2)) i)).val = _
  rw [succAbove_val, succAbove_val]
  simp

/-- Deleting from a composite embedding deletes from the first
factor. -/
private lemma delEmb_comp {k N M : ℕ} (u : Fin (k + 1) ↪o Fin (N + 1))
    (w : Fin (N + 1) ↪o Fin (M + 1)) (j : Fin (k + 1)) :
    delEmb (u.comp w) j = (delEmb u j).comp w :=
  (OrderEmbedding.comp_assoc _ _ _).symm

private lemma one_eq_succ_zero {k : ℕ} : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
  ext
  simp

-- Public: this embedding occurs in the hypotheses of
-- `exists_filler_simplex_of_leftData`.
/-- The unique order embedding out of `Fin 0`. -/
def emptyEmb {N : ℕ} : Fin 0 ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (fun i ↦ i.elim0) (fun i ↦ i.elim0)

private lemma eq_emptyEmb {N : ℕ} (u : Fin 0 ↪o Fin (N + 1)) : u = emptyEmb := by
  ext x
  exact x.elim0

/-- Every element of `Fin (K + 3)` is `0`, `1`, or a double
successor. -/
private lemma fin_classify2 {K : ℕ} (a : Fin (K + 3)) :
    a = 0 ∨ a = 1 ∨ ∃ j : Fin (K + 1), a = j.succ.succ := by
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ 2 ≤ a.val) with h | h | h
  · refine Or.inl (Fin.ext ?_)
    have hv : (0 : Fin (K + 3)).val = 0 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inl (Fin.ext ?_))
    have hv : (1 : Fin (K + 3)).val = 1 := by simp
    rw [hv, h]
  · exact Or.inr (Or.inr ⟨⟨a.val - 2, by have := a.isLt; omega⟩,
      Fin.ext (by simp; omega)⟩)

/-- Every element of `Fin (K + 4)` is `0`, `1`, `2`, or a triple
successor. -/
private lemma fin_classify3 {K : ℕ} (a : Fin (K + 4)) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ ∃ j : Fin (K + 1), a = j.succ.succ.succ := by
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ 3 ≤ a.val) with
    h | h | h | h
  · refine Or.inl (Fin.ext ?_)
    have hv : (0 : Fin (K + 4)).val = 0 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inl (Fin.ext ?_))
    have hv : (1 : Fin (K + 4)).val = 1 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
    have hv : (2 : Fin (K + 4)).val = 2 := by simp
    rw [hv, h]
  · exact Or.inr (Or.inr (Or.inr ⟨⟨a.val - 3, by have := a.isLt; omega⟩,
      Fin.ext (by simp; omega)⟩))

/-- Every element of `Fin (K + 5)` is `0`, `1`, `2`, `3`, or a
quadruple successor. -/
private lemma fin_classify4 {K : ℕ} (a : Fin (K + 5)) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨
      ∃ j : Fin (K + 1), a = j.succ.succ.succ.succ := by
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨
      4 ≤ a.val) with h | h | h | h | h
  · refine Or.inl (Fin.ext ?_)
    have hv : (0 : Fin (K + 5)).val = 0 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inl (Fin.ext ?_))
    have hv : (1 : Fin (K + 5)).val = 1 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
    have hv : (2 : Fin (K + 5)).val = 2 := by simp
    rw [hv, h]
  · refine Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext ?_))))
    have hv : (3 : Fin (K + 5)).val = 3 := by simp
    rw [hv, h]
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨a.val - 4, by
      have := a.isLt; omega⟩, Fin.ext (by simp; omega)⟩)))

private lemma pred_one'' {K : ℕ} (h : (1 : Fin (K + 2)) ≠ 0) :
    (1 : Fin (K + 2)).pred h = 0 := by
  ext
  simp [Fin.pred]

private lemma pred_two'' {K : ℕ} (h : (2 : Fin (K + 3)) ≠ 0) :
    (2 : Fin (K + 3)).pred h = 1 := by
  ext
  simp [Fin.pred]

private lemma pred_succ_succ' {K : ℕ} (j : Fin (K + 1)) (h : j.succ.succ ≠ 0) :
    j.succ.succ.pred h = j.succ := by
  ext
  simp [Fin.pred]

private lemma pred_succ_succ_succ' {K : ℕ} (j : Fin (K + 1))
    (h : j.succ.succ.succ ≠ 0) :
    j.succ.succ.succ.pred h = j.succ.succ := by
  ext
  simp [Fin.pred]

private lemma pred_succ_succ_succ_succ' {K : ℕ} (j : Fin (K + 1))
    (h : j.succ.succ.succ.succ ≠ 0) :
    j.succ.succ.succ.succ.pred h = j.succ.succ.succ := by
  ext
  simp [Fin.pred]

private lemma castPred_zero'' {K : ℕ} (h : (0 : Fin (K + 2)) ≠ Fin.last (K + 1)) :
    (0 : Fin (K + 2)).castPred h = 0 := by
  ext
  simp

private lemma castPred_one'' {K : ℕ} (h : (1 : Fin (K + 3)) ≠ Fin.last (K + 2)) :
    (1 : Fin (K + 3)).castPred h = 1 := by
  ext
  simp

private lemma castPred_two'' {K : ℕ} (h : (2 : Fin (K + 4)) ≠ Fin.last (K + 3)) :
    (2 : Fin (K + 4)).castPred h = 2 := by
  ext
  change (2 : Fin (K + 4)).val = (2 : Fin (K + 3)).val
  rw [show (2 : Fin (K + 4)).val = 2 by simp,
    show (2 : Fin (K + 3)).val = 2 by simp]

private lemma castPred_three'' {K : ℕ} (h : (3 : Fin (K + 5)) ≠ Fin.last (K + 4)) :
    (3 : Fin (K + 5)).castPred h = 3 := by
  ext
  change (3 : Fin (K + 5)).val = (3 : Fin (K + 4)).val
  rw [show (3 : Fin (K + 5)).val = 3 by simp,
    show (3 : Fin (K + 4)).val = 3 by simp]

private lemma castPred_succ_succ' {K : ℕ} (j : Fin (K + 1)) (hj : j.val < K)
    (h : j.succ.succ ≠ Fin.last (K + 2)) :
    j.succ.succ.castPred h = (j.castLT hj).succ.succ := by
  ext
  simp

private lemma castPred_succ_succ_succ' {K : ℕ} (j : Fin (K + 1)) (hj : j.val < K)
    (h : j.succ.succ.succ ≠ Fin.last (K + 3)) :
    j.succ.succ.succ.castPred h = (j.castLT hj).succ.succ.succ := by
  ext
  simp

private lemma castPred_succ_succ_succ_succ' {K : ℕ} (j : Fin (K + 1)) (hj : j.val < K)
    (h : j.succ.succ.succ.succ ≠ Fin.last (K + 4)) :
    j.succ.succ.succ.succ.castPred h =
      (j.castLT hj).succ.succ.succ.succ := by
  ext
  simp

private lemma castSucc_zero'' {K : ℕ} :
    Fin.castSucc (0 : Fin (K + 2)) = (0 : Fin (K + 3)) := by
  ext
  simp

private lemma castSucc_one'' {K : ℕ} :
    Fin.castSucc (1 : Fin (K + 2)) = (1 : Fin (K + 3)) := by
  ext
  simp

private lemma castSucc_two'' {K : ℕ} :
    Fin.castSucc (2 : Fin (K + 3)) = (2 : Fin (K + 4)) := by
  ext
  change (2 : Fin (K + 3)).val = (2 : Fin (K + 4)).val
  rw [show (2 : Fin (K + 3)).val = 2 by simp,
    show (2 : Fin (K + 4)).val = 2 by simp]

private lemma succ_pred_eq {K : ℕ} (j : Fin (K + 2)) (h : j ≠ 0) :
    (j.pred h).succ = j := by
  ext
  simp only [Fin.val_succ, Fin.val_pred]
  have hj : 0 < j.val := Fin.pos_iff_ne_zero.mpr h
  omega

end EmbeddingCombinatorics

section HornSimplices

variable {N : ℕ} {Z : SSet.{u}}

/-- The morphism in the simplex category determined by an order
embedding. -/
private def homOfEmb {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom e.toOrderHom

/-- Precomposing the morphism of an embedding with a face map
deletes an element of the embedding. -/
private lemma δ_comp_homOfEmb {k n : ℕ} (e : Fin (k + 2) ↪o Fin (n + 1))
    (i : Fin (k + 2)) :
    SimplexCategory.δ i ≫ homOfEmb e = homOfEmb (delEmb e i) := by
  ext x
  change (e ((SimplexCategory.δ i).toOrderHom x)).val = (e (Fin.succAbove i x)).val
  rfl

/-- The simplex of the left horn `Λ[N + 2, 0]` determined by an
order embedding whose range avoids some vertex other than `0`. -/
private def hornSimplex {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e) :
    (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}) _⦋m⦌ :=
  ⟨stdSimplex.objEquiv.symm (homOfEmb e), by
    rw [mem_horn_iff_notMem_range]
    obtain ⟨j, hj0, hj⟩ := h
    refine ⟨j, hj0, ?_⟩
    have hrange : Set.range (stdSimplex.objEquiv.symm (homOfEmb e)) =
        Set.range e := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange]
    exact hj⟩

private lemma hornSimplex_val {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e) :
    (hornSimplex e h).val = stdSimplex.objEquiv.symm (homOfEmb e) := rfl

/-- The image in `Z` of the horn simplex determined by `e`, under
a horn `σ₀ : Λ[N + 2, 0] ⟶ Z`. -/
private def hornApp (σ₀ : (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}) ⟶ Z)
    {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e) : Z _⦋m⦌ :=
  σ₀.app _ (hornSimplex e h)

private lemma hornApp_congr (σ₀ : (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}) ⟶ Z)
    {m : ℕ} {e₁ e₂ : Fin (m + 1) ↪o Fin (N + 3)}
    (h₁ : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e₁)
    (h₂ : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e₂) (he : e₁ = e₂) :
    hornApp σ₀ e₁ h₁ = hornApp σ₀ e₂ h₂ := by
  subst he
  rfl

private lemma range_delEmb_subset {k : ℕ} (e : Fin (k + 2) ↪o Fin (N + 3))
    (i : Fin (k + 2)) : Set.range (delEmb e i) ⊆ Set.range e := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨Fin.succAbove i a, rfl⟩

/-- Faces of horn simplices are horn simplices of deleted
embeddings. -/
private lemma δ_hornApp (σ₀ : (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}) ⟶ Z)
    {k : ℕ} (e : Fin (k + 2) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e) (i : Fin (k + 2)) :
    Z.δ i (hornApp σ₀ e h) =
      hornApp σ₀ (delEmb e i)
        (by
          obtain ⟨j, hj0, hj⟩ := h
          exact ⟨j, hj0, fun hjr ↦ hj (range_delEmb_subset e i hjr)⟩) := by
  have hs : (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}).δ i (hornSimplex e h) =
      hornSimplex (delEmb e i)
        (by
          obtain ⟨j, hj0, hj⟩ := h
          exact ⟨j, hj0, fun hjr ↦ hj (range_delEmb_subset e i hjr)⟩) := by
    apply Subtype.ext
    change Δ[N + 2].δ i (stdSimplex.objEquiv.symm (homOfEmb e)) =
      stdSimplex.objEquiv.symm (homOfEmb (delEmb e i))
    rw [show Δ[N + 2].δ i (stdSimplex.objEquiv.symm (homOfEmb e)) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ i ≫ homOfEmb e) from rfl,
      δ_comp_homOfEmb]
  have hnat : σ₀.app _ ((Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}).δ i
      (hornSimplex e h)) = Z.δ i (σ₀.app _ (hornSimplex e h)) :=
    NatTrans.naturality_apply σ₀ (SimplexCategory.δ i).op (hornSimplex e h)
  rw [hs] at hnat
  exact hnat.symm

end HornSimplices

section LeftHornFamilies

variable {N : ℕ} {Z : SSet.{u}} (σ₀ : (Λ[N + 2, (0 : Fin (N + 3))] : SSet.{u}) ⟶ Z)
  {k : ℕ} (u : Fin k ↪o Fin (N + 1))

-- Public: this embedding occurs in statements pinned by the tests.
/-- The embedding of vertices `(0, S)`. -/
def emb0 : Fin (k + 1) ↪o Fin (N + 3) :=
  consEmb 0 (u.comp (tailEmb N)) (fun i ↦ by
    rw [Fin.lt_def]
    change (0 : Fin (N + 3)).val < (tailEmb N (u i)).val
    simp only [Fin.val_zero, tailEmb_val]
    omega)

-- Public: used in the definition of the public embedding `emb01`.
/-- The embedding of vertices `(1, S)`. -/
def emb1 : Fin (k + 1) ↪o Fin (N + 3) :=
  consEmb 1 (u.comp (tailEmb N)) (fun i ↦ by
    rw [Fin.lt_def]
    change (1 : Fin (N + 3)).val < (tailEmb N (u i)).val
    simp only [tailEmb_val]
    have h1 : (1 : Fin (N + 3)).val = 1 := by simp
    rw [h1]
    omega)

-- Public: this embedding occurs in statements pinned by the tests.
/-- The embedding of vertices `(0, 1, S)`. -/
def emb01 : Fin (k + 2) ↪o Fin (N + 3) :=
  consEmb 0 (emb1 u) (fun i ↦ by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [Fin.lt_def]
      show (0 : Fin (N + 3)).val < (emb1 u 0).val
      rw [show emb1 u 0 = 1 from rfl]
      simp
    · rw [Fin.lt_def]
      show (0 : Fin (N + 3)).val < (emb1 u i.succ).val
      rw [show emb1 u i.succ = u.comp (tailEmb N) i from rfl]
      change (0 : Fin (N + 3)).val < (tailEmb N (u i)).val
      simp only [Fin.val_zero, tailEmb_val]
      omega)

private lemma exists_notMem_range (hk : k ≤ N) :
    ∃ t : Fin (N + 1), t ∉ Set.range u := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective u := fun t ↦ hcon t
  have hcard := Fintype.card_le_of_surjective u hsurj
  simp only [Fintype.card_fin] at hcard
  omega

private lemma emb0_avoid :
    ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range (emb0 u) := by
  refine ⟨1, by
    intro hcon
    have := congrArg Fin.val hcon
    simp at this, ?_⟩
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [show emb0 u 0 = 0 from rfl] at hval
    simp at hval
  · rw [show emb0 u i.succ = u.comp (tailEmb N) i from rfl] at hval
    have hval2 : (tailEmb N (u i)).val = (1 : Fin (N + 3)).val := hval
    simp only [tailEmb_val] at hval2
    have h1 : (1 : Fin (N + 3)).val = 1 := by simp
    rw [h1] at hval2
    omega

private lemma emb1_avoid (hk : k ≤ N) :
    ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range (emb1 u) := by
  obtain ⟨t, ht⟩ := exists_notMem_range u hk
  refine ⟨tailEmb N t, by
    intro hcon
    have := congrArg Fin.val hcon
    simp only [tailEmb_val, Fin.val_zero] at this
    omega, ?_⟩
  rintro ⟨i, hi⟩
  apply ht
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [show emb1 u 0 = 1 from rfl] at hi
    have hval := congrArg Fin.val hi
    simp only [tailEmb_val] at hval
    have h1 : (1 : Fin (N + 3)).val = 1 := by simp
    rw [h1] at hval
    omega
  · rw [show emb1 u i.succ = u.comp (tailEmb N) i from rfl] at hi
    have h2 : tailEmb N (u i) = tailEmb N t := hi
    exact ⟨i, (tailEmb N).injective h2⟩

private lemma emb01_avoid (hk : k ≤ N) :
    ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range (emb01 u) := by
  obtain ⟨j, hj0, hj⟩ := emb1_avoid u hk
  refine ⟨j, hj0, ?_⟩
  rintro ⟨i, hi⟩
  apply hj
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [show emb01 u 0 = 0 from rfl] at hi
    exact absurd hi.symm hj0
  · exact ⟨i, hi⟩

/-- The `(0, S)` simplex of the horn `σ₀`. -/
private def g0 : Z _⦋k⦌ := hornApp σ₀ (emb0 u) (emb0_avoid u)

/-- The `(1, S)` simplex of the horn `σ₀` (totalized with `g0`
outside the proper range `k ≤ N`). -/
private def g1 : Z _⦋k⦌ :=
  if hk : k ≤ N then hornApp σ₀ (emb1 u) (emb1_avoid u hk) else g0 σ₀ u

/-- The `(0, 1, S)` simplex of the horn `σ₀` (totalized outside
the proper range `k ≤ N`). -/
private def g01 : Z _⦋k + 1⦌ :=
  if hk : k ≤ N then hornApp σ₀ (emb01 u) (emb01_avoid u hk)
  else Z.σ 0 (g0 σ₀ u)

private lemma delEmb_emb1_zero :
    delEmb (emb1 u) (0 : Fin (k + 1)) = u.comp (tailEmb N) :=
  consEmb_comp_succAbove_zero _ _ _

private lemma delEmb_emb0_zero :
    delEmb (emb0 u) (0 : Fin (k + 1)) = u.comp (tailEmb N) :=
  consEmb_comp_succAbove_zero _ _ _

private lemma delEmb_emb01_zero :
    delEmb (emb01 u) (0 : Fin (k + 2)) = emb1 u :=
  consEmb_comp_succAbove_zero _ _ _

private lemma delEmb_emb01_one :
    delEmb (emb01 u) (1 : Fin (k + 2)) = emb0 u := by
  rw [one_eq_succ_zero]
  change (Fin.succAboveOrderEmb (0 : Fin (k + 1)).succ).comp (emb01 u) = emb0 u
  change (Fin.succAboveOrderEmb (0 : Fin (k + 1)).succ).comp
    (consEmb 0 (emb1 u) _) = emb0 u
  rw [consEmb_comp_succAbove_succ]
  change consEmb 0 (delEmb (emb1 u) (0 : Fin (k + 1))) _ =
    consEmb 0 (u.comp (tailEmb N)) _
  congr 1

private lemma delEmb_emb01_succ_succ {u : Fin (k + 1) ↪o Fin (N + 1)}
    (j : Fin (k + 1)) :
    delEmb (emb01 u) j.succ.succ = emb01 (delEmb u j) := by
  change (Fin.succAboveOrderEmb j.succ.succ).comp (emb01 u) = emb01 (delEmb u j)
  change (Fin.succAboveOrderEmb j.succ.succ).comp (consEmb 0 (emb1 u) _) =
    emb01 (delEmb u j)
  rw [consEmb_comp_succAbove_succ]
  change consEmb 0 (delEmb (emb1 u) j.succ) _ =
    consEmb 0 (emb1 (delEmb u j)) _
  congr 1
  change (Fin.succAboveOrderEmb j.succ).comp (emb1 u) = emb1 (delEmb u j)
  change (Fin.succAboveOrderEmb j.succ).comp
    (consEmb 1 (u.comp (tailEmb N)) _) = emb1 (delEmb u j)
  rw [consEmb_comp_succAbove_succ]
  change consEmb 1 (delEmb (u.comp (tailEmb N)) j) _ =
    consEmb 1 ((delEmb u j).comp (tailEmb N)) _
  congr 1

private lemma delEmb_emb0_succ {u : Fin (k + 1) ↪o Fin (N + 1)}
    (j : Fin (k + 1)) :
    delEmb (emb0 u) j.succ = emb0 (delEmb u j) := by
  change (Fin.succAboveOrderEmb j.succ).comp (emb0 u) = emb0 (delEmb u j)
  change (Fin.succAboveOrderEmb j.succ).comp
    (consEmb 0 (u.comp (tailEmb N)) _) = emb0 (delEmb u j)
  rw [consEmb_comp_succAbove_succ]
  change consEmb 0 (delEmb (u.comp (tailEmb N)) j) _ =
    consEmb 0 ((delEmb u j).comp (tailEmb N)) _
  congr 1

private lemma delEmb_emb1_succ {u : Fin (k + 1) ↪o Fin (N + 1)}
    (j : Fin (k + 1)) :
    delEmb (emb1 u) j.succ = emb1 (delEmb u j) := by
  change (Fin.succAboveOrderEmb j.succ).comp (emb1 u) = emb1 (delEmb u j)
  change (Fin.succAboveOrderEmb j.succ).comp
    (consEmb 1 (u.comp (tailEmb N)) _) = emb1 (delEmb u j)
  rw [consEmb_comp_succAbove_succ]
  change consEmb 1 (delEmb (u.comp (tailEmb N)) j) _ =
    consEmb 1 ((delEmb u j).comp (tailEmb N)) _
  congr 1

private lemma δ_g01_zero (hk : k ≤ N) :
    Z.δ 0 (g01 σ₀ u) = g1 σ₀ u := by
  rw [g01, g1, dite_eq_left hk, dite_eq_left hk, δ_hornApp]
  exact hornApp_congr σ₀ _ _ (delEmb_emb01_zero u)

private lemma δ_g01_one (hk : k ≤ N) :
    Z.δ 1 (g01 σ₀ u) = g0 σ₀ u := by
  rw [g01, dite_eq_left hk, δ_hornApp]
  exact hornApp_congr σ₀ _ _ (delEmb_emb01_one u)

private lemma δ_g01_succ_succ {u : Fin (k + 1) ↪o Fin (N + 1)} (hk : k + 1 ≤ N)
    (j : Fin (k + 1)) :
    Z.δ j.succ.succ (g01 σ₀ u) = g01 σ₀ (delEmb u j) := by
  have hk' : k ≤ N := by omega
  rw [g01, g01, dite_eq_left hk, dite_eq_left hk', δ_hornApp]
  exact hornApp_congr σ₀ _ _ (delEmb_emb01_succ_succ (u := u) j)

private lemma δ_g0_succ {u : Fin (k + 1) ↪o Fin (N + 1)} (j : Fin (k + 1)) :
    Z.δ j.succ (g0 σ₀ u) = g0 σ₀ (delEmb u j) := by
  rw [g0, g0, δ_hornApp]
  exact hornApp_congr σ₀ _ _ (delEmb_emb0_succ (u := u) j)

private lemma δ_g1_succ {u : Fin (k + 1) ↪o Fin (N + 1)} (hk : k + 1 ≤ N)
    (j : Fin (k + 1)) :
    Z.δ j.succ (g1 σ₀ u) = g1 σ₀ (delEmb u j) := by
  have hk' : k ≤ N := by omega
  rw [g1, g1, dite_eq_left hk, dite_eq_left hk', δ_hornApp]
  exact hornApp_congr σ₀ _ _ (delEmb_emb1_succ (u := u) j)

end LeftHornFamilies

/-- The `2`-face of the `0`-degeneracy of a simplex is the
`0`-degeneracy of its `1`-face. -/
private lemma δ_two_σ_zero {n : ℕ} (s : X _⦋n + 1⦌) :
    X.δ 2 (X.σ 0 s) = X.σ 0 (X.δ 1 s) := by
  rw [show (2 : Fin (n + 3)) = (0 : Fin (n + 1)).succ.succ from by
    ext
    simp only [Fin.val_succ]
    rw [show (0 : Fin (n + 1)).val = 0 by simp,
      show (2 : Fin (n + 3)).val = 2 by simp],
    δ_succ_succ_σ_zero, ← one_eq_succ_zero]

/-- The predecessor of `3`. -/
private lemma pred_three'' {K : ℕ} (h : (3 : Fin (K + 4)) ≠ 0) :
    (3 : Fin (K + 4)).pred h = 2 := by
  ext
  simp only [Fin.val_pred]
  rw [show (3 : Fin (K + 4)).val = 3 by simp,
    show (2 : Fin (K + 3)).val = 2 by simp]

/-- The successor of `1` is `2`. -/
private lemma succ_one_eq {K : ℕ} : (1 : Fin (K + 2)).succ = (2 : Fin (K + 3)) := by
  ext
  simp only [Fin.val_succ]
  rw [show (1 : Fin (K + 2)).val = 1 by simp,
    show (2 : Fin (K + 3)).val = 2 by simp]

/-- The successor of `2` is `3`. -/
private lemma succ_two_eq {K : ℕ} : (2 : Fin (K + 3)).succ = (3 : Fin (K + 4)) := by
  ext
  simp only [Fin.val_succ]
  rw [show (2 : Fin (K + 3)).val = 2 by simp,
    show (3 : Fin (K + 4)).val = 3 by simp]

section AbstractRounds

variable {Y : SSet.{u}} [Quasicategory Y] {N : ℕ}
  (g01 : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 1⦌)
  (g0 : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k⦌)
  (g1 : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k⦌)
  (hg01_0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
    Y.δ 0 (g01 k u) = g1 k u)
  (hg01_1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
    Y.δ 1 (g01 k u) = g0 k u)
  (hg01_succ : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
    (j : Fin (k + 1)), Y.δ j.succ.succ (g01 (k + 1) u) = g01 k (delEmb u j))
  (hg0_succ : ∀ (k : ℕ) (u : Fin (k + 1) ↪o Fin (N + 1)) (j : Fin (k + 1)),
    Y.δ j.succ (g0 (k + 1) u) = g0 k (delEmb u j))
  (hg1_succ : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
    (j : Fin (k + 1)), Y.δ j.succ (g1 (k + 1) u) = g1 k (delEmb u j))
  (α β : Y _⦋2⦌) (invE : Y _⦋1⦌)
  (hα0 : Y.δ 0 α = invE)
  (hα1 : Y.δ 1 α = Y.σ 0 (Y.δ 1 (g01 0 emptyEmb)))
  (hα2 : Y.δ 2 α = g01 0 emptyEmb)
  (hβ0 : Y.δ 0 β = g01 0 emptyEmb)
  (hβ1 : Y.δ 1 β = Y.σ 0 (Y.δ 0 (g01 0 emptyEmb)))
  (hβ2 : Y.δ 2 β = invE)
  (hinvSrc : Y.δ 1 invE = Y.δ 0 (g01 0 emptyEmb))
  (hinvTgt : Y.δ 0 invE = Y.δ 1 (g01 0 emptyEmb))

include hg01_0 hg01_succ hg1_succ hβ0 hβ1 in
/-- Round one of Dugger's filtration: simplices `(1, 0, 1, S)`
attached along inner horns `Λ[|S| + 2, 2]`, by induction on
`|S|`, with `β` at `S = ∅`. -/
private lemma exists_WB :
    ∃ W : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌,
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 0 (W k u) = g01 k u) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 1 (W k u) = Y.σ 0 (g1 k u)) ∧
      (∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
        (j : Fin (k + 1)),
        Y.δ j.succ.succ.succ (W (k + 1) u) = W k (delEmb u j)) ∧
      (∀ u : Fin 0 ↪o Fin (N + 1), W 0 u = β) := by
  have key : ∀ (K : ℕ) (_ : K ≤ N),
      ∃ W : ∀ (j : Fin (K + 1)) (u : Fin j.val ↪o Fin (N + 1)), Y _⦋j.val + 2⦌,
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 0 (W ⟨k, by omega⟩ u) = g01 k u) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 1 (W ⟨k, by omega⟩ u) = Y.σ 0 (g1 k u)) ∧
        (∀ (k : ℕ) (hk : k + 1 ≤ K) (u : Fin (k + 1) ↪o Fin (N + 1))
          (j : Fin (k + 1)),
          Y.δ j.succ.succ.succ (W ⟨k + 1, by omega⟩ u) =
            W ⟨k, by omega⟩ (delEmb u j)) ∧
        (∀ u : Fin 0 ↪o Fin (N + 1), W ⟨0, by omega⟩ u = β) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun j u =>
        Fin.cases (motive := fun j : Fin 1 =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
          (fun _ => β) (fun j => Fin.elim0 j) j u, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 0 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => β) (fun j => Fin.elim0 j) (0 : Fin 1) u) = g01 0 u
        rw [Fin.cases_zero, eq_emptyEmb u]
        exact hβ0
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 1 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => β) (fun j => Fin.elim0 j) (0 : Fin 1) u) =
          Y.σ 0 (g1 0 u)
        rw [Fin.cases_zero, eq_emptyEmb u, hβ1,
          hg01_0 0 (Nat.zero_le N) emptyEmb]
      · intro k hk u j
        exact (Nat.not_succ_le_zero k hk).elim
      · intro u
        change (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => β) (fun j => Fin.elim0 j) (0 : Fin 1) u) = β
        rw [Fin.cases_zero]
    | succ K ih =>
      intro hKN
      obtain ⟨W, hW0, hW1, hWdel, hWβ⟩ := ih (by omega)
      have hv0 : (0 : Fin (K + 4)).val = 0 := by simp
      have hv1 : (1 : Fin (K + 4)).val = 1 := by simp
      have hv2 : (2 : Fin (K + 4)).val = 2 := by simp
      have hex : ∀ u : Fin (K + 1) ↪o Fin (N + 1), ∃ σ : Y _⦋K + 3⦌,
          Y.δ 0 σ = g01 (K + 1) u ∧ Y.δ 1 σ = Y.σ 0 (g1 (K + 1) u) ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ σ = W ⟨K, by omega⟩ (delEmb u j) := by
        intro u
        set s : ∀ (a : Fin (K + 4)) (_ : a ≠ 2), Y _⦋K + 2⦌ := fun a ha =>
          if h0 : a = 0 then g01 (K + 1) u
          else if h1 : a = 1 then Y.σ 0 (g1 (K + 1) u)
          else W ⟨K, by omega⟩ (delEmb u ⟨a.val - 3, by
            have ha2 : a.val ≠ 2 := fun hcon =>
              ha (Fin.ext (hcon.trans hv2.symm))
            have ha0 : a.val ≠ 0 := fun hcon =>
              h0 (Fin.ext (hcon.trans hv0.symm))
            have ha1 : a.val ≠ 1 := fun hcon =>
              h1 (Fin.ext (hcon.trans hv1.symm))
            have hlt := a.isLt
            change a.val - 3 < K + 1
            omega⟩) with hs_def
        have hs0 : ∀ h : (0 : Fin (K + 4)) ≠ 2, s 0 h = g01 (K + 1) u := by
          intro h
          rw [hs_def]
          exact dite_eq_left rfl
        have hs1 : ∀ h : (1 : Fin (K + 4)) ≠ 2,
            s 1 h = Y.σ 0 (g1 (K + 1) u) := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans (dite_eq_left rfl)
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv1, hv0] at h2
          omega
        have hsS : ∀ (j : Fin (K + 1)) (h : j.succ.succ.succ ≠ 2),
            s j.succ.succ.succ h = W ⟨K, by omega⟩ (delEmb u j) := by
          intro j h
          have hne0 : j.succ.succ.succ ≠ (0 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv0] at h2
            omega
          have hne1 : j.succ.succ.succ ≠ (1 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv1] at h2
            omega
          have hstep : s j.succ.succ.succ h =
              W ⟨K, by omega⟩ (delEmb u ⟨j.succ.succ.succ.val - 3, by
                simp only [Fin.val_succ]
                have := j.isLt
                omega⟩) := by
            rw [hs_def]
            exact (dite_eq_right hne0).trans (dite_eq_right hne1)
          rw [hstep]
          refine congrArg (fun t : Fin (K + 1) =>
            W ⟨K, by omega⟩ (delEmb u t)) (Fin.ext ?_)
          simp only [Fin.val_succ]
          omega
        obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := Y)
          (i := (2 : Fin (K + 4)))
          (Fin.lt_def.mpr (by rw [hv0, hv2]; omega))
          (by
            rw [Fin.lt_def, hv2]
            simp [Fin.val_last])
          s
          (by
            intro a b ha hb hab
            have habv : a.val < b.val := Fin.lt_def.mp hab
            rcases fin_classify3 a with rfl | rfl | rfl | ⟨ja, rfl⟩
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · omega
              · rw [hs0 ha, hs1 hb, pred_one'', castPred_zero'']
                exact (hg01_0 (K + 1) hKN u).trans (δ_zero_σ_zero _).symm
              · exact (hb rfl).elim
              · rw [hs0 ha, hsS jb hb, pred_succ_succ_succ', castPred_zero'']
                exact (hg01_succ K hKN u jb).trans
                  (hW0 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv1] at habv
                omega
              · omega
              · exact (hb rfl).elim
              · rw [hs1 ha, hsS jb hb, pred_succ_succ_succ', castPred_one'',
                  δ_succ_succ_σ_zero, hg1_succ K hKN u jb]
                exact (hW1 K le_rfl (delEmb u jb)).symm
            · exact (ha rfl).elim
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · simp only [Fin.val_succ, hv0] at habv
                omega
              · simp only [Fin.val_succ, hv1] at habv
                omega
              · exact (hb rfl).elim
              · have hjj : ja < jb := Fin.lt_def.mpr (by
                  simp only [Fin.val_succ] at habv
                  omega)
                rw [hsS ja ha, hsS jb hb, pred_succ_succ_succ',
                  castPred_succ_succ_succ' ja (by
                    have h1 := Fin.lt_def.mp hjj
                    have h2 := jb.isLt
                    omega)]
                obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
                  have h1 := Fin.lt_def.mp hjj
                  have h2 := jb.isLt
                  omega⟩
                have hjb : jb.succ.succ =
                    (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ.succ := by
                  rw [succ_pred_eq]
                rw [hjb]
                exact (hWdel K' le_rfl (delEmb u ja) _).trans
                  ((congrArg (W ⟨K', by omega⟩)
                    (delEmb_delEmb u hjj).symm).trans
                    (hWdel K' le_rfl (delEmb u jb) _).symm))
        refine ⟨σ, ?_, ?_, ?_⟩
        · have hne : (0 : Fin (K + 4)) ≠ 2 := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv0, hv2] at h2
            omega
          rw [hσ 0 hne]
          exact hs0 hne
        · have hne : (1 : Fin (K + 4)) ≠ 2 := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv1, hv2] at h2
            omega
          rw [hσ 1 hne]
          exact hs1 hne
        · intro j
          have hne : j.succ.succ.succ ≠ (2 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv2] at h2
            omega
          rw [hσ _ hne]
          exact hsS j hne
      set chosen : ∀ u : Fin (K + 1) ↪o Fin (N + 1), Y _⦋K + 3⦌ :=
        fun u => (hex u).choose with hchosen
      have hspec : ∀ u : Fin (K + 1) ↪o Fin (N + 1),
          Y.δ 0 (chosen u) = g01 (K + 1) u ∧
            Y.δ 1 (chosen u) = Y.σ 0 (g1 (K + 1) u) ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ (chosen u) =
                W ⟨K, by omega⟩ (delEmb u j) :=
        fun u => (hex u).choose_spec
      refine ⟨fun j u =>
        Fin.lastCases (motive := fun j : Fin (K + 2) =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
          (fun u => chosen u) (fun j u => W j u) j u, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = g01 k u
          rw [Fin.lastCases_castSucc]
          exact hW0 k hkK u
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.last (K + 1)) u) = g01 (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Y.σ 0 (g1 k u)
          rw [Fin.lastCases_castSucc]
          exact hW1 k hkK u
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.last (K + 1)) u) = Y.σ 0 (g1 (K + 1) u)
          rw [Fin.lastCases_last]
          exact (hspec u).2.1
      · intro k hk u j
        rcases (by omega : k + 1 ≤ K ∨ k = K) with hkK | rfl
        · change Y.δ j.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.castSucc ⟨k + 1, by omega⟩) u) =
            Fin.lastCases (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          exact hWdel k hkK u j
        · change Y.δ j.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.last (k + 1)) u) =
            Fin.lastCases (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => W j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact (hspec u).2.2 j
      · intro u
        change (Fin.lastCases (motive := fun j : Fin (K + 2) =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun u => chosen u) (fun j u => W j u)
            (Fin.castSucc ⟨0, by omega⟩) u) = β
        rw [Fin.lastCases_castSucc]
        exact hWβ u
  obtain ⟨W', hW0, hW1, hWdel, hWβ⟩ := key N le_rfl
  refine ⟨fun k u =>
    if hk : k ≤ N then W' ⟨k, by omega⟩ u else Y.σ 0 (Y.σ 0 (g1 k u)),
    ?_, ?_, ?_, ?_⟩
  · intro k hk u
    change Y.δ 0 (if hk' : k ≤ N then W' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g1 k u))) = g01 k u
    rw [dite_eq_left hk]
    exact hW0 k hk u
  · intro k hk u
    change Y.δ 1 (if hk' : k ≤ N then W' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g1 k u))) = Y.σ 0 (g1 k u)
    rw [dite_eq_left hk]
    exact hW1 k hk u
  · intro k hk u j
    change Y.δ j.succ.succ.succ (if hk' : k + 1 ≤ N then W' ⟨k + 1, by omega⟩ u
        else Y.σ 0 (Y.σ 0 (g1 (k + 1) u))) =
      (if hk' : k ≤ N then W' ⟨k, by omega⟩ (delEmb u j)
        else Y.σ 0 (Y.σ 0 (g1 k (delEmb u j))))
    rw [dite_eq_left hk, dite_eq_left (show k ≤ N by omega)]
    exact hWdel k hk u j
  · intro u
    change (if hk' : 0 ≤ N then W' ⟨0, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g1 0 u))) = β
    rw [dite_eq_left (Nat.zero_le N)]
    exact hWβ u


include hg01_1 hg0_succ hα0 hα1 in
/-- Round two of Dugger's filtration: provisional simplices
`(0, 1, 0, S)` attached along inner horns `Λ[|S| + 2, 2]`, by
induction on `|S|`, with `α` at `S = ∅`. -/
private lemma exists_Fp
    (B : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 1⦌)
    (hB0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (B k u) = g0 k u)
    (hBdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)), Y.δ j.succ.succ (B (k + 1) u) = B k (delEmb u j))
    (hBempty : ∀ u : Fin 0 ↪o Fin (N + 1), B 0 u = invE) :
    ∃ Fp : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌,
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 0 (Fp k u) = B k u) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 1 (Fp k u) = Y.σ 0 (g0 k u)) ∧
      (∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
        (j : Fin (k + 1)),
        Y.δ j.succ.succ.succ (Fp (k + 1) u) = Fp k (delEmb u j)) ∧
      (∀ u : Fin 0 ↪o Fin (N + 1), Fp 0 u = α) := by
  have key : ∀ (K : ℕ) (_ : K ≤ N),
      ∃ Fp : ∀ (j : Fin (K + 1)) (u : Fin j.val ↪o Fin (N + 1)), Y _⦋j.val + 2⦌,
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 0 (Fp ⟨k, by omega⟩ u) = B k u) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 1 (Fp ⟨k, by omega⟩ u) = Y.σ 0 (g0 k u)) ∧
        (∀ (k : ℕ) (hk : k + 1 ≤ K) (u : Fin (k + 1) ↪o Fin (N + 1))
          (j : Fin (k + 1)),
          Y.δ j.succ.succ.succ (Fp ⟨k + 1, by omega⟩ u) =
            Fp ⟨k, by omega⟩ (delEmb u j)) ∧
        (∀ u : Fin 0 ↪o Fin (N + 1), Fp ⟨0, by omega⟩ u = α) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun j u =>
        Fin.cases (motive := fun j : Fin 1 =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
          (fun _ => α) (fun j => Fin.elim0 j) j u, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 0 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => α) (fun j => Fin.elim0 j) (0 : Fin 1) u) = B 0 u
        rw [Fin.cases_zero, hα0]
        exact (hBempty u).symm
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 1 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => α) (fun j => Fin.elim0 j) (0 : Fin 1) u) =
          Y.σ 0 (g0 0 u)
        rw [Fin.cases_zero, eq_emptyEmb u, hα1,
          hg01_1 0 (Nat.zero_le N) emptyEmb]
      · intro k hk u j
        exact (Nat.not_succ_le_zero k hk).elim
      · intro u
        change (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun _ => α) (fun j => Fin.elim0 j) (0 : Fin 1) u) = α
        rw [Fin.cases_zero]
    | succ K ih =>
      intro hKN
      obtain ⟨Fp, hFp0, hFp1, hFpdel, hFpα⟩ := ih (by omega)
      have hv0 : (0 : Fin (K + 4)).val = 0 := by simp
      have hv1 : (1 : Fin (K + 4)).val = 1 := by simp
      have hv2 : (2 : Fin (K + 4)).val = 2 := by simp
      have hex : ∀ u : Fin (K + 1) ↪o Fin (N + 1), ∃ σ : Y _⦋K + 3⦌,
          Y.δ 0 σ = B (K + 1) u ∧ Y.δ 1 σ = Y.σ 0 (g0 (K + 1) u) ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ σ = Fp ⟨K, by omega⟩ (delEmb u j) := by
        intro u
        set s : ∀ (a : Fin (K + 4)) (_ : a ≠ 2), Y _⦋K + 2⦌ := fun a ha =>
          if h0 : a = 0 then B (K + 1) u
          else if h1 : a = 1 then Y.σ 0 (g0 (K + 1) u)
          else Fp ⟨K, by omega⟩ (delEmb u ⟨a.val - 3, by
            have ha2 : a.val ≠ 2 := fun hcon =>
              ha (Fin.ext (hcon.trans hv2.symm))
            have ha0 : a.val ≠ 0 := fun hcon =>
              h0 (Fin.ext (hcon.trans hv0.symm))
            have ha1 : a.val ≠ 1 := fun hcon =>
              h1 (Fin.ext (hcon.trans hv1.symm))
            have hlt := a.isLt
            change a.val - 3 < K + 1
            omega⟩) with hs_def
        have hs0 : ∀ h : (0 : Fin (K + 4)) ≠ 2, s 0 h = B (K + 1) u := by
          intro h
          rw [hs_def]
          exact dite_eq_left rfl
        have hs1 : ∀ h : (1 : Fin (K + 4)) ≠ 2,
            s 1 h = Y.σ 0 (g0 (K + 1) u) := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans (dite_eq_left rfl)
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv1, hv0] at h2
          omega
        have hsS : ∀ (j : Fin (K + 1)) (h : j.succ.succ.succ ≠ 2),
            s j.succ.succ.succ h = Fp ⟨K, by omega⟩ (delEmb u j) := by
          intro j h
          have hne0 : j.succ.succ.succ ≠ (0 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv0] at h2
            omega
          have hne1 : j.succ.succ.succ ≠ (1 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv1] at h2
            omega
          have hstep : s j.succ.succ.succ h =
              Fp ⟨K, by omega⟩ (delEmb u ⟨j.succ.succ.succ.val - 3, by
                simp only [Fin.val_succ]
                have := j.isLt
                omega⟩) := by
            rw [hs_def]
            exact (dite_eq_right hne0).trans (dite_eq_right hne1)
          rw [hstep]
          refine congrArg (fun t : Fin (K + 1) =>
            Fp ⟨K, by omega⟩ (delEmb u t)) (Fin.ext ?_)
          simp only [Fin.val_succ]
          omega
        obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := Y)
          (i := (2 : Fin (K + 4)))
          (Fin.lt_def.mpr (by rw [hv0, hv2]; omega))
          (by
            rw [Fin.lt_def, hv2]
            simp [Fin.val_last])
          s
          (by
            intro a b ha hb hab
            have habv : a.val < b.val := Fin.lt_def.mp hab
            rcases fin_classify3 a with rfl | rfl | rfl | ⟨ja, rfl⟩
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · omega
              · rw [hs0 ha, hs1 hb, pred_one'', castPred_zero'']
                exact (hB0 (K + 1) hKN u).trans (δ_zero_σ_zero _).symm
              · exact (hb rfl).elim
              · rw [hs0 ha, hsS jb hb, pred_succ_succ_succ', castPred_zero'']
                exact (hBdel K hKN u jb).trans
                  (hFp0 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv1] at habv
                omega
              · omega
              · exact (hb rfl).elim
              · rw [hs1 ha, hsS jb hb, pred_succ_succ_succ', castPred_one'',
                  δ_succ_succ_σ_zero, hg0_succ K u jb]
                exact (hFp1 K le_rfl (delEmb u jb)).symm
            · exact (ha rfl).elim
            · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
              · simp only [Fin.val_succ, hv0] at habv
                omega
              · simp only [Fin.val_succ, hv1] at habv
                omega
              · exact (hb rfl).elim
              · have hjj : ja < jb := Fin.lt_def.mpr (by
                  simp only [Fin.val_succ] at habv
                  omega)
                rw [hsS ja ha, hsS jb hb, pred_succ_succ_succ',
                  castPred_succ_succ_succ' ja (by
                    have h1 := Fin.lt_def.mp hjj
                    have h2 := jb.isLt
                    omega)]
                obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
                  have h1 := Fin.lt_def.mp hjj
                  have h2 := jb.isLt
                  omega⟩
                have hjb : jb.succ.succ =
                    (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ.succ := by
                  rw [succ_pred_eq]
                rw [hjb]
                exact (hFpdel K' le_rfl (delEmb u ja) _).trans
                  ((congrArg (Fp ⟨K', by omega⟩)
                    (delEmb_delEmb u hjj).symm).trans
                    (hFpdel K' le_rfl (delEmb u jb) _).symm))
        refine ⟨σ, ?_, ?_, ?_⟩
        · have hne : (0 : Fin (K + 4)) ≠ 2 := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv0, hv2] at h2
            omega
          rw [hσ 0 hne]
          exact hs0 hne
        · have hne : (1 : Fin (K + 4)) ≠ 2 := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv1, hv2] at h2
            omega
          rw [hσ 1 hne]
          exact hs1 hne
        · intro j
          have hne : j.succ.succ.succ ≠ (2 : Fin (K + 4)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv2] at h2
            omega
          rw [hσ _ hne]
          exact hsS j hne
      set chosen : ∀ u : Fin (K + 1) ↪o Fin (N + 1), Y _⦋K + 3⦌ :=
        fun u => (hex u).choose with hchosen
      have hspec : ∀ u : Fin (K + 1) ↪o Fin (N + 1),
          Y.δ 0 (chosen u) = B (K + 1) u ∧
            Y.δ 1 (chosen u) = Y.σ 0 (g0 (K + 1) u) ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ (chosen u) =
                Fp ⟨K, by omega⟩ (delEmb u j) :=
        fun u => (hex u).choose_spec
      refine ⟨fun j u =>
        Fin.lastCases (motive := fun j : Fin (K + 2) =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
          (fun u => chosen u) (fun j u => Fp j u) j u, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = B k u
          rw [Fin.lastCases_castSucc]
          exact hFp0 k hkK u
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.last (K + 1)) u) = B (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Y.σ 0 (g0 k u)
          rw [Fin.lastCases_castSucc]
          exact hFp1 k hkK u
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.last (K + 1)) u) = Y.σ 0 (g0 (K + 1) u)
          rw [Fin.lastCases_last]
          exact (hspec u).2.1
      · intro k hk u j
        rcases (by omega : k + 1 ≤ K ∨ k = K) with hkK | rfl
        · change Y.δ j.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.castSucc ⟨k + 1, by omega⟩) u) =
            Fin.lastCases (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          exact hFpdel k hkK u j
        · change Y.δ j.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.last (k + 1)) u) =
            Fin.lastCases (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
              (fun u => chosen u) (fun j u => Fp j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact (hspec u).2.2 j
      · intro u
        change (Fin.lastCases (motive := fun j : Fin (K + 2) =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 2⦌)
            (fun u => chosen u) (fun j u => Fp j u)
            (Fin.castSucc ⟨0, by omega⟩) u) = α
        rw [Fin.lastCases_castSucc]
        exact hFpα u
  obtain ⟨Fp', hFp0, hFp1, hFpdel, hFpα⟩ := key N le_rfl
  refine ⟨fun k u =>
    if hk : k ≤ N then Fp' ⟨k, by omega⟩ u else Y.σ 0 (Y.σ 0 (g0 k u)),
    ?_, ?_, ?_, ?_⟩
  · intro k hk u
    change Y.δ 0 (if hk' : k ≤ N then Fp' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g0 k u))) = B k u
    rw [dite_eq_left hk]
    exact hFp0 k hk u
  · intro k hk u
    change Y.δ 1 (if hk' : k ≤ N then Fp' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g0 k u))) = Y.σ 0 (g0 k u)
    rw [dite_eq_left hk]
    exact hFp1 k hk u
  · intro k hk u j
    change Y.δ j.succ.succ.succ (if hk' : k + 1 ≤ N then Fp' ⟨k + 1, by omega⟩ u
        else Y.σ 0 (Y.σ 0 (g0 (k + 1) u))) =
      (if hk' : k ≤ N then Fp' ⟨k, by omega⟩ (delEmb u j)
        else Y.σ 0 (Y.σ 0 (g0 k (delEmb u j))))
    rw [dite_eq_left hk, dite_eq_left (show k ≤ N by omega)]
    exact hFpdel k hk u j
  · intro u
    change (if hk' : 0 ≤ N then Fp' ⟨0, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g0 0 u))) = α
    rw [dite_eq_left (Nat.zero_le N)]
    exact hFpα u
include hg01_1 hg01_succ in
/-- The first correction round: simplices `(0, 1, 0, 1, S)`
attached along inner horns `Λ[|S| + 3, 2]`, by induction on
`|S|`, with the given three-dimensional filler `H` at `S = ∅`.
Its missing faces are homotopies `(0, 1, 1, S)` from the
provisional `(0, 1, S)'` to the prescribed `(0, 1, S)`. -/
private lemma exists_Sη
    (W : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌)
    (hW0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (W k u) = g01 k u)
    (hWdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (W (k + 1) u) = W k (delEmb u j))
    (hWβ : ∀ u : Fin 0 ↪o Fin (N + 1), W 0 u = β)
    (B : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 1⦌)
    (hB : ∀ (k : ℕ) (u : Fin k ↪o Fin (N + 1)), B k u = Y.δ 2 (W k u))
    (Fp : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌)
    (hFp0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (Fp k u) = B k u)
    (hFp1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 1 (Fp k u) = Y.σ 0 (g0 k u))
    (hFpdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (Fp (k + 1) u) = Fp k (delEmb u j))
    (hFpα : ∀ u : Fin 0 ↪o Fin (N + 1), Fp 0 u = α)
    (H : Y _⦋3⦌)
    (hH0 : Y.δ 0 H = β)
    (hH1 : Y.δ 1 H = Y.σ 0 (g01 0 emptyEmb))
    (hH3 : Y.δ 3 H = α) :
    ∃ Sη : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 3⦌,
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 0 (Sη k u) = W k u) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 1 (Sη k u) = Y.σ 0 (g01 k u)) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 3 (Sη k u) = Fp k u) ∧
      (∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
        (j : Fin (k + 1)),
        Y.δ j.succ.succ.succ.succ (Sη (k + 1) u) = Sη k (delEmb u j)) ∧
      (∀ u : Fin 0 ↪o Fin (N + 1), Sη 0 u = H) := by
  have key : ∀ (K : ℕ) (_ : K ≤ N),
      ∃ Sη : ∀ (j : Fin (K + 1)) (u : Fin j.val ↪o Fin (N + 1)),
          Y _⦋j.val + 3⦌,
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 0 (Sη ⟨k, by omega⟩ u) = W k u) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 1 (Sη ⟨k, by omega⟩ u) = Y.σ 0 (g01 k u)) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 3 (Sη ⟨k, by omega⟩ u) = Fp k u) ∧
        (∀ (k : ℕ) (hk : k + 1 ≤ K) (u : Fin (k + 1) ↪o Fin (N + 1))
          (j : Fin (k + 1)),
          Y.δ j.succ.succ.succ.succ (Sη ⟨k + 1, by omega⟩ u) =
            Sη ⟨k, by omega⟩ (delEmb u j)) ∧
        (∀ u : Fin 0 ↪o Fin (N + 1), Sη ⟨0, by omega⟩ u = H) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun j u =>
        Fin.cases (motive := fun j : Fin 1 =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
          (fun _ => H) (fun j => Fin.elim0 j) j u, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 0 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => H) (fun j => Fin.elim0 j) (0 : Fin 1) u) = W 0 u
        rw [Fin.cases_zero]
        exact hH0.trans (hWβ u).symm
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 1 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => H) (fun j => Fin.elim0 j) (0 : Fin 1) u) =
          Y.σ 0 (g01 0 u)
        rw [Fin.cases_zero, eq_emptyEmb u]
        exact hH1
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 3 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => H) (fun j => Fin.elim0 j) (0 : Fin 1) u) = Fp 0 u
        rw [Fin.cases_zero]
        exact hH3.trans (hFpα u).symm
      · intro k hk u j
        exact (Nat.not_succ_le_zero k hk).elim
      · intro u
        change (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => H) (fun j => Fin.elim0 j) (0 : Fin 1) u) = H
        rw [Fin.cases_zero]
    | succ K ih =>
      intro hKN
      obtain ⟨Sη, hS0, hS1, hS3, hSdel, hSH⟩ := ih (by omega)
      have hv0 : (0 : Fin (K + 5)).val = 0 := by simp
      have hv1 : (1 : Fin (K + 5)).val = 1 := by simp
      have hv2 : (2 : Fin (K + 5)).val = 2 := by simp
      have hv3 : (3 : Fin (K + 5)).val = 3 := by simp
      have hex : ∀ u : Fin (K + 1) ↪o Fin (N + 1), ∃ σ : Y _⦋K + 4⦌,
          Y.δ 0 σ = W (K + 1) u ∧ Y.δ 1 σ = Y.σ 0 (g01 (K + 1) u) ∧
            Y.δ 3 σ = Fp (K + 1) u ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ.succ σ = Sη ⟨K, by omega⟩ (delEmb u j) := by
        intro u
        set s : ∀ (a : Fin (K + 5)) (_ : a ≠ 2), Y _⦋K + 3⦌ := fun a ha =>
          if h0 : a = 0 then W (K + 1) u
          else if h1 : a = 1 then Y.σ 0 (g01 (K + 1) u)
          else if h3 : a = 3 then Fp (K + 1) u
          else Sη ⟨K, by omega⟩ (delEmb u ⟨a.val - 4, by
            have ha2 : a.val ≠ 2 := fun hcon =>
              ha (Fin.ext (hcon.trans hv2.symm))
            have ha0 : a.val ≠ 0 := fun hcon =>
              h0 (Fin.ext (hcon.trans hv0.symm))
            have ha1 : a.val ≠ 1 := fun hcon =>
              h1 (Fin.ext (hcon.trans hv1.symm))
            have ha3 : a.val ≠ 3 := fun hcon =>
              h3 (Fin.ext (hcon.trans hv3.symm))
            have hlt := a.isLt
            change a.val - 4 < K + 1
            omega⟩) with hs_def
        have hs0 : ∀ h : (0 : Fin (K + 5)) ≠ 2, s 0 h = W (K + 1) u := by
          intro h
          rw [hs_def]
          exact dite_eq_left rfl
        have hs1 : ∀ h : (1 : Fin (K + 5)) ≠ 2,
            s 1 h = Y.σ 0 (g01 (K + 1) u) := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans (dite_eq_left rfl)
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv1, hv0] at h2
          omega
        have hs3 : ∀ h : (3 : Fin (K + 5)) ≠ 2, s 3 h = Fp (K + 1) u := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans
            ((dite_eq_right ?_).trans (dite_eq_left rfl))
          · intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv3, hv0] at h2
            omega
          · intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv3, hv1] at h2
            omega
        have hsS : ∀ (j : Fin (K + 1)) (h : j.succ.succ.succ.succ ≠ 2),
            s j.succ.succ.succ.succ h = Sη ⟨K, by omega⟩ (delEmb u j) := by
          intro j h
          have hne0 : j.succ.succ.succ.succ ≠ (0 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv0] at h2
            omega
          have hne1 : j.succ.succ.succ.succ ≠ (1 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv1] at h2
            omega
          have hne3 : j.succ.succ.succ.succ ≠ (3 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv3] at h2
            omega
          have hstep : s j.succ.succ.succ.succ h =
              Sη ⟨K, by omega⟩ (delEmb u ⟨j.succ.succ.succ.succ.val - 4, by
                simp only [Fin.val_succ]
                have := j.isLt
                omega⟩) := by
            rw [hs_def]
            exact (dite_eq_right hne0).trans
              ((dite_eq_right hne1).trans (dite_eq_right hne3))
          rw [hstep]
          refine congrArg (fun t : Fin (K + 1) =>
            Sη ⟨K, by omega⟩ (delEmb u t)) (Fin.ext ?_)
          simp only [Fin.val_succ]
          omega
        obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := Y)
          (i := (2 : Fin (K + 5)))
          (Fin.lt_def.mpr (by rw [hv0, hv2]; omega))
          (by
            rw [Fin.lt_def, hv2]
            simp [Fin.val_last])
          s
          (by
            intro a b ha hb hab
            have habv : a.val < b.val := Fin.lt_def.mp hab
            rcases fin_classify4 a with rfl | rfl | rfl | rfl | ⟨ja, rfl⟩
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · omega
              · rw [hs0 ha, hs1 hb, pred_one'', castPred_zero'']
                exact (hW0 (K + 1) hKN u).trans (δ_zero_σ_zero _).symm
              · exact (hb rfl).elim
              · rw [hs0 ha, hs3 hb, pred_three'', castPred_zero'']
                exact (hB (K + 1) u).symm.trans (hFp0 (K + 1) hKN u).symm
              · rw [hs0 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_zero'']
                exact (hWdel K hKN u jb).trans
                  (hS0 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv1] at habv
                omega
              · omega
              · exact (hb rfl).elim
              · rw [hs1 ha, hs3 hb, pred_three'', castPred_one'',
                  δ_two_σ_zero, hg01_1 (K + 1) hKN u]
                exact (hFp1 (K + 1) hKN u).symm
              · rw [hs1 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_one'', δ_succ_succ_σ_zero, hg01_succ K hKN u jb]
                exact (hS1 K le_rfl (delEmb u jb)).symm
            · exact (ha rfl).elim
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv3] at habv
                omega
              · rw [hv1, hv3] at habv
                omega
              · exact (hb rfl).elim
              · omega
              · rw [hs3 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_three'']
                exact (hFpdel K hKN u jb).trans
                  (hS3 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · simp only [Fin.val_succ, hv0] at habv
                omega
              · simp only [Fin.val_succ, hv1] at habv
                omega
              · exact (hb rfl).elim
              · simp only [Fin.val_succ, hv3] at habv
                omega
              · have hjj : ja < jb := Fin.lt_def.mpr (by
                  simp only [Fin.val_succ] at habv
                  omega)
                rw [hsS ja ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_succ_succ_succ_succ' ja (by
                    have h1 := Fin.lt_def.mp hjj
                    have h2 := jb.isLt
                    omega)]
                obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
                  have h1 := Fin.lt_def.mp hjj
                  have h2 := jb.isLt
                  omega⟩
                have hjb : jb.succ.succ.succ =
                    (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ.succ.succ := by
                  rw [succ_pred_eq]
                rw [hjb]
                exact (hSdel K' le_rfl (delEmb u ja) _).trans
                  ((congrArg (Sη ⟨K', by omega⟩)
                    (delEmb_delEmb u hjj).symm).trans
                    (hSdel K' le_rfl (delEmb u jb) _).symm))
        have hne02 : (0 : Fin (K + 5)) ≠ 2 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv0, hv2] at h2
          omega
        have hne12 : (1 : Fin (K + 5)) ≠ 2 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv1, hv2] at h2
          omega
        have hne32 : (3 : Fin (K + 5)) ≠ 2 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv3, hv2] at h2
          omega
        refine ⟨σ, ?_, ?_, ?_, ?_⟩
        · rw [hσ 0 hne02]
          exact hs0 hne02
        · rw [hσ 1 hne12]
          exact hs1 hne12
        · rw [hσ 3 hne32]
          exact hs3 hne32
        · intro j
          have hne : j.succ.succ.succ.succ ≠ (2 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv2] at h2
            omega
          rw [hσ _ hne]
          exact hsS j hne
      set chosen : ∀ u : Fin (K + 1) ↪o Fin (N + 1), Y _⦋K + 4⦌ :=
        fun u => (hex u).choose with hchosen
      have hspec : ∀ u : Fin (K + 1) ↪o Fin (N + 1),
          Y.δ 0 (chosen u) = W (K + 1) u ∧
            Y.δ 1 (chosen u) = Y.σ 0 (g01 (K + 1) u) ∧
            Y.δ 3 (chosen u) = Fp (K + 1) u ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ.succ (chosen u) =
                Sη ⟨K, by omega⟩ (delEmb u j) :=
        fun u => (hex u).choose_spec
      refine ⟨fun j u =>
        Fin.lastCases (motive := fun j : Fin (K + 2) =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
          (fun u => chosen u) (fun j u => Sη j u) j u, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = W k u
          rw [Fin.lastCases_castSucc]
          exact hS0 k hkK u
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.last (K + 1)) u) = W (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Y.σ 0 (g01 k u)
          rw [Fin.lastCases_castSucc]
          exact hS1 k hkK u
        · change Y.δ 1 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.last (K + 1)) u) = Y.σ 0 (g01 (K + 1) u)
          rw [Fin.lastCases_last]
          exact (hspec u).2.1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 3 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Fp k u
          rw [Fin.lastCases_castSucc]
          exact hS3 k hkK u
        · change Y.δ 3 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.last (K + 1)) u) = Fp (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).2.2.1
      · intro k hk u j
        rcases (by omega : k + 1 ≤ K ∨ k = K) with hkK | rfl
        · change Y.δ j.succ.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k + 1, by omega⟩) u) =
            Fin.lastCases (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          exact hSdel k hkK u j
        · change Y.δ j.succ.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.last (k + 1)) u) =
            Fin.lastCases (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => Sη j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact (hspec u).2.2.2 j
      · intro u
        change (Fin.lastCases (motive := fun j : Fin (K + 2) =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun u => chosen u) (fun j u => Sη j u)
            (Fin.castSucc ⟨0, by omega⟩) u) = H
        rw [Fin.lastCases_castSucc]
        exact hSH u
  obtain ⟨Sη', hS0, hS1, hS3, hSdel, hSH⟩ := key N le_rfl
  refine ⟨fun k u =>
    if hk : k ≤ N then Sη' ⟨k, by omega⟩ u
    else Y.σ 0 (Y.σ 0 (g01 k u)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk u
    change Y.δ 0 (if hk' : k ≤ N then Sη' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g01 k u))) = W k u
    rw [dite_eq_left hk]
    exact hS0 k hk u
  · intro k hk u
    change Y.δ 1 (if hk' : k ≤ N then Sη' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g01 k u))) = Y.σ 0 (g01 k u)
    rw [dite_eq_left hk]
    exact hS1 k hk u
  · intro k hk u
    change Y.δ 3 (if hk' : k ≤ N then Sη' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g01 k u))) = Fp k u
    rw [dite_eq_left hk]
    exact hS3 k hk u
  · intro k hk u j
    change Y.δ j.succ.succ.succ.succ (if hk' : k + 1 ≤ N
        then Sη' ⟨k + 1, by omega⟩ u
        else Y.σ 0 (Y.σ 0 (g01 (k + 1) u))) =
      (if hk' : k ≤ N then Sη' ⟨k, by omega⟩ (delEmb u j)
        else Y.σ 0 (Y.σ 0 (g01 k (delEmb u j))))
    rw [dite_eq_left hk, dite_eq_left (show k ≤ N by omega)]
    exact hSdel k hk u j
  · intro u
    change (if hk' : 0 ≤ N then Sη' ⟨0, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (g01 0 u))) = H
    rw [dite_eq_left (Nat.zero_le N)]
    exact hSH u

/-- The second correction round: simplices `(0, 1, 1, 0, S)`
attached along inner horns `Λ[|S| + 3, 1]`, by induction on
`|S|`, with the given three-dimensional filler `Ks` at `S = ∅`.
Its missing faces are the corrected `(0, 1, 0, S)`. -/
private lemma exists_SF
    (B : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 1⦌)
    (hB1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 1 (B k u) = g1 k u)
    (hBdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)), Y.δ j.succ.succ (B (k + 1) u) = B k (delEmb u j))
    (hBempty : ∀ u : Fin 0 ↪o Fin (N + 1), B 0 u = invE)
    (Fp : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌)
    (hFp0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (Fp k u) = B k u)
    (hFpdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (Fp (k + 1) u) = Fp k (delEmb u j))
    (hFpα : ∀ u : Fin 0 ↪o Fin (N + 1), Fp 0 u = α)
    (η : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌)
    (hη0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (η k u) = Y.σ 0 (g1 k u))
    (hη2 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 2 (η k u) = Y.δ 2 (Fp k u))
    (hηdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (η (k + 1) u) = η k (delEmb u j))
    (Ks : Y _⦋3⦌)
    (hKs0 : Y.δ 0 Ks = Y.σ 0 invE)
    (hKs2 : Y.δ 2 Ks = α)
    (hKs3 : Y.δ 3 Ks = η 0 emptyEmb) :
    ∃ SF : ∀ (k : ℕ) (_u : Fin k ↪o Fin (N + 1)), Y _⦋k + 3⦌,
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 0 (SF k u) = Y.σ 0 (B k u)) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 2 (SF k u) = Fp k u) ∧
      (∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
        Y.δ 3 (SF k u) = η k u) ∧
      (∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
        (j : Fin (k + 1)),
        Y.δ j.succ.succ.succ.succ (SF (k + 1) u) = SF k (delEmb u j)) ∧
      (∀ u : Fin 0 ↪o Fin (N + 1), SF 0 u = Ks) := by
  have key : ∀ (K : ℕ) (_ : K ≤ N),
      ∃ SF : ∀ (j : Fin (K + 1)) (u : Fin j.val ↪o Fin (N + 1)),
          Y _⦋j.val + 3⦌,
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 0 (SF ⟨k, by omega⟩ u) = Y.σ 0 (B k u)) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 2 (SF ⟨k, by omega⟩ u) = Fp k u) ∧
        (∀ (k : ℕ) (hk : k ≤ K) (u : Fin k ↪o Fin (N + 1)),
          Y.δ 3 (SF ⟨k, by omega⟩ u) = η k u) ∧
        (∀ (k : ℕ) (hk : k + 1 ≤ K) (u : Fin (k + 1) ↪o Fin (N + 1))
          (j : Fin (k + 1)),
          Y.δ j.succ.succ.succ.succ (SF ⟨k + 1, by omega⟩ u) =
            SF ⟨k, by omega⟩ (delEmb u j)) ∧
        (∀ u : Fin 0 ↪o Fin (N + 1), SF ⟨0, by omega⟩ u = Ks) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun j u =>
        Fin.cases (motive := fun j : Fin 1 =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
          (fun _ => Ks) (fun j => Fin.elim0 j) j u, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 0 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => Ks) (fun j => Fin.elim0 j) (0 : Fin 1) u) =
          Y.σ 0 (B 0 u)
        rw [Fin.cases_zero, hKs0, hBempty u]
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 2 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => Ks) (fun j => Fin.elim0 j) (0 : Fin 1) u) = Fp 0 u
        rw [Fin.cases_zero]
        exact hKs2.trans (hFpα u).symm
      · intro k hk u
        have hk0 : k = 0 := by omega
        subst hk0
        change Y.δ 3 (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => Ks) (fun j => Fin.elim0 j) (0 : Fin 1) u) = η 0 u
        rw [Fin.cases_zero, eq_emptyEmb u]
        exact hKs3
      · intro k hk u j
        exact (Nat.not_succ_le_zero k hk).elim
      · intro u
        change (Fin.cases (motive := fun j : Fin 1 =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun _ => Ks) (fun j => Fin.elim0 j) (0 : Fin 1) u) = Ks
        rw [Fin.cases_zero]
    | succ K ih =>
      intro hKN
      obtain ⟨SF, hSF0, hSF2, hSF3, hSFdel, hSFK⟩ := ih (by omega)
      have hv0 : (0 : Fin (K + 5)).val = 0 := by simp
      have hv1 : (1 : Fin (K + 5)).val = 1 := by simp
      have hv2 : (2 : Fin (K + 5)).val = 2 := by simp
      have hv3 : (3 : Fin (K + 5)).val = 3 := by simp
      have hex : ∀ u : Fin (K + 1) ↪o Fin (N + 1), ∃ σ : Y _⦋K + 4⦌,
          Y.δ 0 σ = Y.σ 0 (B (K + 1) u) ∧ Y.δ 2 σ = Fp (K + 1) u ∧
            Y.δ 3 σ = η (K + 1) u ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ.succ σ = SF ⟨K, by omega⟩ (delEmb u j) := by
        intro u
        set s : ∀ (a : Fin (K + 5)) (_ : a ≠ 1), Y _⦋K + 3⦌ := fun a ha =>
          if h0 : a = 0 then Y.σ 0 (B (K + 1) u)
          else if h2 : a = 2 then Fp (K + 1) u
          else if h3 : a = 3 then η (K + 1) u
          else SF ⟨K, by omega⟩ (delEmb u ⟨a.val - 4, by
            have ha1 : a.val ≠ 1 := fun hcon =>
              ha (Fin.ext (hcon.trans hv1.symm))
            have ha0 : a.val ≠ 0 := fun hcon =>
              h0 (Fin.ext (hcon.trans hv0.symm))
            have ha2 : a.val ≠ 2 := fun hcon =>
              h2 (Fin.ext (hcon.trans hv2.symm))
            have ha3 : a.val ≠ 3 := fun hcon =>
              h3 (Fin.ext (hcon.trans hv3.symm))
            have hlt := a.isLt
            change a.val - 4 < K + 1
            omega⟩) with hs_def
        have hs0 : ∀ h : (0 : Fin (K + 5)) ≠ 1,
            s 0 h = Y.σ 0 (B (K + 1) u) := by
          intro h
          rw [hs_def]
          exact dite_eq_left rfl
        have hs2 : ∀ h : (2 : Fin (K + 5)) ≠ 1, s 2 h = Fp (K + 1) u := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans (dite_eq_left rfl)
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv2, hv0] at h2
          omega
        have hs3 : ∀ h : (3 : Fin (K + 5)) ≠ 1, s 3 h = η (K + 1) u := by
          intro h
          rw [hs_def]
          refine (dite_eq_right ?_).trans
            ((dite_eq_right ?_).trans (dite_eq_left rfl))
          · intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv3, hv0] at h2
            omega
          · intro hcon
            have h2 := congrArg Fin.val hcon
            rw [hv3, hv2] at h2
            omega
        have hsS : ∀ (j : Fin (K + 1)) (h : j.succ.succ.succ.succ ≠ 1),
            s j.succ.succ.succ.succ h = SF ⟨K, by omega⟩ (delEmb u j) := by
          intro j h
          have hne0 : j.succ.succ.succ.succ ≠ (0 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv0] at h2
            omega
          have hne2 : j.succ.succ.succ.succ ≠ (2 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv2] at h2
            omega
          have hne3 : j.succ.succ.succ.succ ≠ (3 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv3] at h2
            omega
          have hstep : s j.succ.succ.succ.succ h =
              SF ⟨K, by omega⟩ (delEmb u ⟨j.succ.succ.succ.succ.val - 4, by
                simp only [Fin.val_succ]
                have := j.isLt
                omega⟩) := by
            rw [hs_def]
            exact (dite_eq_right hne0).trans
              ((dite_eq_right hne2).trans (dite_eq_right hne3))
          rw [hstep]
          refine congrArg (fun t : Fin (K + 1) =>
            SF ⟨K, by omega⟩ (delEmb u t)) (Fin.ext ?_)
          simp only [Fin.val_succ]
          omega
        obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := Y)
          (i := (1 : Fin (K + 5)))
          (Fin.lt_def.mpr (by rw [hv0, hv1]; omega))
          (by
            rw [Fin.lt_def, hv1]
            simp only [Fin.val_last]
            omega)
          s
          (by
            intro a b ha hb hab
            have habv : a.val < b.val := Fin.lt_def.mp hab
            rcases fin_classify4 a with rfl | rfl | rfl | rfl | ⟨ja, rfl⟩
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · omega
              · exact (hb rfl).elim
              · rw [hs0 ha, hs2 hb, pred_two'', castPred_zero'',
                  δ_one_σ_zero]
                exact (hFp0 (K + 1) hKN u).symm
              · rw [hs0 ha, hs3 hb, pred_three'', castPred_zero'',
                  δ_two_σ_zero, hB1 (K + 1) hKN u]
                exact (hη0 (K + 1) hKN u).symm
              · rw [hs0 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_zero'', δ_succ_succ_σ_zero, hBdel K hKN u jb]
                exact (hSF0 K le_rfl (delEmb u jb)).symm
            · exact (ha rfl).elim
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv2] at habv
                omega
              · exact (hb rfl).elim
              · omega
              · rw [hs2 ha, hs3 hb, pred_three'', castPred_two'']
                exact (hη2 (K + 1) hKN u).symm
              · rw [hs2 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_two'']
                exact (hFpdel K hKN u jb).trans
                  (hSF2 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · rw [hv0, hv3] at habv
                omega
              · exact (hb rfl).elim
              · rw [hv2, hv3] at habv
                omega
              · omega
              · rw [hs3 ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_three'']
                exact (hηdel K hKN u jb).trans
                  (hSF3 K le_rfl (delEmb u jb)).symm
            · rcases fin_classify4 b with rfl | rfl | rfl | rfl | ⟨jb, rfl⟩
              · simp only [Fin.val_succ, hv0] at habv
                omega
              · exact (hb rfl).elim
              · simp only [Fin.val_succ, hv2] at habv
                omega
              · simp only [Fin.val_succ, hv3] at habv
                omega
              · have hjj : ja < jb := Fin.lt_def.mpr (by
                  simp only [Fin.val_succ] at habv
                  omega)
                rw [hsS ja ha, hsS jb hb, pred_succ_succ_succ_succ',
                  castPred_succ_succ_succ_succ' ja (by
                    have h1 := Fin.lt_def.mp hjj
                    have h2 := jb.isLt
                    omega)]
                obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
                  have h1 := Fin.lt_def.mp hjj
                  have h2 := jb.isLt
                  omega⟩
                have hjb : jb.succ.succ.succ =
                    (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ.succ.succ := by
                  rw [succ_pred_eq]
                rw [hjb]
                exact (hSFdel K' le_rfl (delEmb u ja) _).trans
                  ((congrArg (SF ⟨K', by omega⟩)
                    (delEmb_delEmb u hjj).symm).trans
                    (hSFdel K' le_rfl (delEmb u jb) _).symm))
        have hne01 : (0 : Fin (K + 5)) ≠ 1 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv0, hv1] at h2
          omega
        have hne21 : (2 : Fin (K + 5)) ≠ 1 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv2, hv1] at h2
          omega
        have hne31 : (3 : Fin (K + 5)) ≠ 1 := by
          intro hcon
          have h2 := congrArg Fin.val hcon
          rw [hv3, hv1] at h2
          omega
        refine ⟨σ, ?_, ?_, ?_, ?_⟩
        · rw [hσ 0 hne01]
          exact hs0 hne01
        · rw [hσ 2 hne21]
          exact hs2 hne21
        · rw [hσ 3 hne31]
          exact hs3 hne31
        · intro j
          have hne : j.succ.succ.succ.succ ≠ (1 : Fin (K + 5)) := by
            intro hcon
            have h2 := congrArg Fin.val hcon
            simp only [Fin.val_succ, hv1] at h2
            omega
          rw [hσ _ hne]
          exact hsS j hne
      set chosen : ∀ u : Fin (K + 1) ↪o Fin (N + 1), Y _⦋K + 4⦌ :=
        fun u => (hex u).choose with hchosen
      have hspec : ∀ u : Fin (K + 1) ↪o Fin (N + 1),
          Y.δ 0 (chosen u) = Y.σ 0 (B (K + 1) u) ∧
            Y.δ 2 (chosen u) = Fp (K + 1) u ∧
            Y.δ 3 (chosen u) = η (K + 1) u ∧
            ∀ j : Fin (K + 1),
              Y.δ j.succ.succ.succ.succ (chosen u) =
                SF ⟨K, by omega⟩ (delEmb u j) :=
        fun u => (hex u).choose_spec
      refine ⟨fun j u =>
        Fin.lastCases (motive := fun j : Fin (K + 2) =>
          (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
          (fun u => chosen u) (fun j u => SF j u) j u, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Y.σ 0 (B k u)
          rw [Fin.lastCases_castSucc]
          exact hSF0 k hkK u
        · change Y.δ 0 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.last (K + 1)) u) = Y.σ 0 (B (K + 1) u)
          rw [Fin.lastCases_last]
          exact (hspec u).1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 2 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = Fp k u
          rw [Fin.lastCases_castSucc]
          exact hSF2 k hkK u
        · change Y.δ 2 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.last (K + 1)) u) = Fp (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).2.1
      · intro k hk u
        rcases (by omega : k ≤ K ∨ k = K + 1) with hkK | rfl
        · change Y.δ 3 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k, by omega⟩) u) = η k u
          rw [Fin.lastCases_castSucc]
          exact hSF3 k hkK u
        · change Y.δ 3 (Fin.lastCases (motive := fun j : Fin (K + 2) =>
              (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.last (K + 1)) u) = η (K + 1) u
          rw [Fin.lastCases_last]
          exact (hspec u).2.2.1
      · intro k hk u j
        rcases (by omega : k + 1 ≤ K ∨ k = K) with hkK | rfl
        · change Y.δ j.succ.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k + 1, by omega⟩) u) =
            Fin.lastCases (motive := fun j : Fin (K + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          exact hSFdel k hkK u j
        · change Y.δ j.succ.succ.succ.succ (Fin.lastCases
              (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.last (k + 1)) u) =
            Fin.lastCases (motive := fun j : Fin (k + 2) =>
                (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
              (fun u => chosen u) (fun j u => SF j u)
              (Fin.castSucc ⟨k, by omega⟩) (delEmb u j)
          rw [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact (hspec u).2.2.2 j
      · intro u
        change (Fin.lastCases (motive := fun j : Fin (K + 2) =>
            (Fin j.val ↪o Fin (N + 1)) → Y _⦋j.val + 3⦌)
            (fun u => chosen u) (fun j u => SF j u)
            (Fin.castSucc ⟨0, by omega⟩) u) = Ks
        rw [Fin.lastCases_castSucc]
        exact hSFK u
  obtain ⟨SF', hSF0, hSF2, hSF3, hSFdel, hSFK⟩ := key N le_rfl
  refine ⟨fun k u =>
    if hk : k ≤ N then SF' ⟨k, by omega⟩ u
    else Y.σ 0 (Y.σ 0 (B k u)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk u
    change Y.δ 0 (if hk' : k ≤ N then SF' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (B k u))) = Y.σ 0 (B k u)
    rw [dite_eq_left hk]
    exact hSF0 k hk u
  · intro k hk u
    change Y.δ 2 (if hk' : k ≤ N then SF' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (B k u))) = Fp k u
    rw [dite_eq_left hk]
    exact hSF2 k hk u
  · intro k hk u
    change Y.δ 3 (if hk' : k ≤ N then SF' ⟨k, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (B k u))) = η k u
    rw [dite_eq_left hk]
    exact hSF3 k hk u
  · intro k hk u j
    change Y.δ j.succ.succ.succ.succ (if hk' : k + 1 ≤ N
        then SF' ⟨k + 1, by omega⟩ u
        else Y.σ 0 (Y.σ 0 (B (k + 1) u))) =
      (if hk' : k ≤ N then SF' ⟨k, by omega⟩ (delEmb u j)
        else Y.σ 0 (Y.σ 0 (B k (delEmb u j))))
    rw [dite_eq_left hk, dite_eq_left (show k ≤ N by omega)]
    exact hSFdel k hk u j
  · intro u
    change (if hk' : 0 ≤ N then SF' ⟨0, by omega⟩ u
      else Y.σ 0 (Y.σ 0 (B 0 u))) = Ks
    rw [dite_eq_left (Nat.zero_le N)]
    exact hSFK u

-- Public: this is the abstract core of the two horn-filling
-- theorems below and is exercised in the tests.
include hg01_0 hg01_1 hg01_succ hg0_succ hg1_succ hα0 hα1 hβ0 hβ1 hβ2
  hinvSrc in
/-- The abstract simplex-level form of Joyal's special left outer
horn filling: from compatible families `(0, S)`, `(1, S)`,
`(0, 1, S)` for `S ⊆ {2, ..., N + 2}` and inverse data
`α = (0, 1, 0)`, `β = (1, 0, 1)` for the `(0, 1)`-edge
`g01 0 emptyEmb`, Dugger's filtration (rounds `exists_WB`,
`exists_Fp`, `exists_Sη`, `exists_SF`, the
`(1, 0, 2, ..., N + 2)` simplex along `Λ[N + 2, 1]`, and the final
`Λ[N + 3, 2]` horn on `(0, 1, 0', 2, ..., N + 2)`) produces an
`(N + 2)`-simplex whose `1`-face is `(0, 2, ..., N + 2)` and whose
`(j + 2)`-face is `(0, 1, ..., ĵ, ..., N + 2)`. -/
theorem exists_filler_simplex_of_leftData :
    ∃ σ : Y _⦋N + 2⦌, Y.δ 1 σ = g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) ∧
      ∀ j : Fin (N + 1),
        Y.δ j.succ.succ σ = g01 N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) := by
  obtain ⟨W, hW0, hW1, hWdel, hWβ⟩ := exists_WB (g01 := g01) (g1 := g1)
    (hg01_0 := hg01_0) (hg01_succ := hg01_succ) (hg1_succ := hg1_succ)
    (β := β) (hβ0 := hβ0) (hβ1 := hβ1)
  set B : ∀ (k : ℕ) (u : Fin k ↪o Fin (N + 1)), Y _⦋k + 1⦌ :=
    fun k u => Y.δ 2 (W k u) with hBdef
  have hB : ∀ (k : ℕ) (u : Fin k ↪o Fin (N + 1)), B k u = Y.δ 2 (W k u) :=
    fun k u => rfl
  have hB0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (B k u) = g0 k u := by
    intro k hk u
    have hdd := δ_δ_of_lt' (W k u) (0 : Fin (k + 2)) (2 : Fin (k + 3)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv0 : (0 : Fin (k + 2)).val = 0 := by simp
      have hv2 : (2 : Fin (k + 3)).val = 2 := by simp
      omega)
    rw [pred_two'', castSucc_zero'', hW0 k hk u] at hdd
    exact hdd.trans (hg01_1 k hk u)
  have hB1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 1 (B k u) = g1 k u := by
    intro k hk u
    have hdd := δ_δ_of_lt' (W k u) (1 : Fin (k + 2)) (2 : Fin (k + 3)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv1 : (1 : Fin (k + 2)).val = 1 := by simp
      have hv2 : (2 : Fin (k + 3)).val = 2 := by simp
      omega)
    rw [pred_two'', castSucc_one'', hW1 k hk u] at hdd
    exact hdd.trans (δ_one_σ_zero _)
  have hBdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)), Y.δ j.succ.succ (B (k + 1) u) = B k (delEmb u j) := by
    intro k hk u j
    have hdd := δ_δ_of_le' (W (k + 1) u) (2 : Fin (k + 3)) j.succ.succ (by
      rw [Fin.le_def]
      have hv2 : (2 : Fin (k + 3)).val = 2 := by simp
      simp only [Fin.val_succ, hv2]
      omega)
    rw [castSucc_two''] at hdd
    exact hdd.symm.trans (congrArg (Y.δ 2) (hWdel k hk u j))
  have hBempty : ∀ u : Fin 0 ↪o Fin (N + 1), B 0 u = invE := by
    intro u
    rw [hB, hWβ u]
    exact hβ2
  obtain ⟨Fp, hFp0, hFp1, hFpdel, hFpα⟩ := exists_Fp (g01 := g01)
    (g0 := g0) (hg01_1 := hg01_1) (hg0_succ := hg0_succ) (α := α)
    (invE := invE) (hα0 := hα0) (hα1 := hα1) B hB0 hBdel hBempty
  obtain ⟨H, hH0, hH1, hH3⟩ := exists_simplex_three_missing_two (X := Y)
    (s₀ := β) (s₁ := Y.σ 0 (g01 0 emptyEmb)) (s₃ := Fp 0 emptyEmb)
    (by rw [hβ0, δ_zero_σ_zero])
    (by exact hβ2.trans ((hBempty emptyEmb).symm.trans
          (hFp0 0 (Nat.zero_le N) emptyEmb).symm))
    (by
      rw [δ_two_σ_zero, hg01_1 0 (Nat.zero_le N) emptyEmb]
      exact (hFp1 0 (Nat.zero_le N) emptyEmb).symm)
  obtain ⟨Sη, hS0, hS1, hS3, hSdel, hSH⟩ := exists_Sη (g01 := g01)
    (g0 := g0) (hg01_1 := hg01_1) (hg01_succ := hg01_succ)
    (α := α) (β := β) W hW0 hWdel hWβ B hB Fp hFp0 hFp1 hFpdel hFpα
    H hH0 hH1 (hH3.trans (hFpα emptyEmb))
  set η : ∀ (k : ℕ) (u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌ :=
    fun k u => Y.δ 2 (Sη k u) with hηdef
  have hη0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (η k u) = Y.σ 0 (g1 k u) := by
    intro k hk u
    have hdd := δ_δ_of_lt' (Sη k u) (0 : Fin (k + 3)) (2 : Fin (k + 4)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv0 : (0 : Fin (k + 3)).val = 0 := by simp
      have hv2 : (2 : Fin (k + 4)).val = 2 := by simp
      omega)
    rw [pred_two'', castSucc_zero'', hS0 k hk u] at hdd
    exact hdd.trans (hW1 k hk u)
  have hη1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 1 (η k u) = g01 k u := by
    intro k hk u
    have hdd := δ_δ_of_lt' (Sη k u) (1 : Fin (k + 3)) (2 : Fin (k + 4)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv1 : (1 : Fin (k + 3)).val = 1 := by simp
      have hv2 : (2 : Fin (k + 4)).val = 2 := by simp
      omega)
    rw [pred_two'', castSucc_one'', hS1 k hk u] at hdd
    exact hdd.trans (δ_one_σ_zero _)
  have hη2 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 2 (η k u) = Y.δ 2 (Fp k u) := by
    intro k hk u
    have hdd := δ_δ_of_le' (Sη k u) (2 : Fin (k + 3)) (2 : Fin (k + 3))
      le_rfl
    rw [succ_two_eq, castSucc_two''] at hdd
    exact hdd.symm.trans (congrArg (Y.δ 2) (hS3 k hk u))
  have hηdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (η (k + 1) u) = η k (delEmb u j) := by
    intro k hk u j
    have hdd := δ_δ_of_le' (Sη (k + 1) u) (2 : Fin (k + 4))
      j.succ.succ.succ (by
        rw [Fin.le_def]
        have hv2 : (2 : Fin (k + 4)).val = 2 := by simp
        simp only [Fin.val_succ, hv2]
        omega)
    rw [castSucc_two''] at hdd
    exact hdd.symm.trans (congrArg (Y.δ 2) (hSdel k hk u j))
  obtain ⟨Ks, hKs0, hKs2, hKs3⟩ := exists_simplex_three_missing_one (X := Y)
    (s₀ := Y.σ 0 invE) (s₂ := Fp 0 emptyEmb) (s₃ := η 0 emptyEmb)
    (by
      rw [δ_one_σ_zero]
      exact (hBempty emptyEmb).symm.trans
        (hFp0 0 (Nat.zero_le N) emptyEmb).symm)
    (by
      rw [δ_two_σ_zero, hinvSrc, hg01_0 0 (Nat.zero_le N) emptyEmb]
      exact (hη0 0 (Nat.zero_le N) emptyEmb).symm)
    (by exact (hη2 0 (Nat.zero_le N) emptyEmb).symm)
  obtain ⟨SF, hSF0, hSF2, hSF3, hSFdel, hSFK⟩ := exists_SF
    (g1 := g1) (α := α) (invE := invE) B hB1 hBdel hBempty Fp hFp0
    hFpdel hFpα η hη0 hη2 hηdel Ks hKs0 (hKs2.trans (hFpα emptyEmb)) hKs3
  set F : ∀ (k : ℕ) (u : Fin k ↪o Fin (N + 1)), Y _⦋k + 2⦌ :=
    fun k u => Y.δ 1 (SF k u) with hFdef
  have hF0 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 0 (F k u) = B k u := by
    intro k hk u
    have hdd := δ_δ_of_lt' (SF k u) (0 : Fin (k + 3)) (1 : Fin (k + 4)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv0 : (0 : Fin (k + 3)).val = 0 := by simp
      have hv1 : (1 : Fin (k + 4)).val = 1 := by simp
      omega)
    rw [pred_one'', castSucc_zero'', hSF0 k hk u] at hdd
    exact hdd.trans (δ_zero_σ_zero _)
  have hF1 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 1 (F k u) = Y.σ 0 (g0 k u) := by
    intro k hk u
    have hdd := δ_δ_of_le' (SF k u) (1 : Fin (k + 3)) (1 : Fin (k + 3))
      le_rfl
    rw [succ_one_eq, castSucc_one''] at hdd
    exact hdd.symm.trans
      ((congrArg (Y.δ 1) (hSF2 k hk u)).trans (hFp1 k hk u))
  have hF2 : ∀ (k : ℕ) (_ : k ≤ N) (u : Fin k ↪o Fin (N + 1)),
      Y.δ 2 (F k u) = g01 k u := by
    intro k hk u
    have hdd := δ_δ_of_le' (SF k u) (1 : Fin (k + 3)) (2 : Fin (k + 3)) (by
      rw [Fin.le_def]
      have hv1 : (1 : Fin (k + 3)).val = 1 := by simp
      have hv2 : (2 : Fin (k + 3)).val = 2 := by simp
      omega)
    rw [succ_two_eq, castSucc_one''] at hdd
    exact hdd.symm.trans
      ((congrArg (Y.δ 1) (hSF3 k hk u)).trans (hη1 k hk u))
  have hFdel : ∀ (k : ℕ) (_ : k + 1 ≤ N) (u : Fin (k + 1) ↪o Fin (N + 1))
      (j : Fin (k + 1)),
      Y.δ j.succ.succ.succ (F (k + 1) u) = F k (delEmb u j) := by
    intro k hk u j
    have hdd := δ_δ_of_le' (SF (k + 1) u) (1 : Fin (k + 4))
      j.succ.succ.succ (by
        rw [Fin.le_def]
        have hv1 : (1 : Fin (k + 4)).val = 1 := by simp
        simp only [Fin.val_succ, hv1]
        omega)
    rw [castSucc_one''] at hdd
    exact hdd.symm.trans (congrArg (Y.δ 1) (hSFdel k hk u j))
  have hT : ∃ T : Y _⦋N + 2⦌,
      Y.δ 0 T = g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) ∧
        ∀ j : Fin (N + 1),
          Y.δ j.succ.succ T = B N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) := by
    have hv0 : (0 : Fin (N + 3)).val = 0 := by simp
    have hv1 : (1 : Fin (N + 3)).val = 1 := by simp
    set sT : ∀ (a : Fin (N + 3)) (_ : a ≠ 1), Y _⦋N + 1⦌ := fun a ha =>
      if h0 : a = 0 then g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
      else B N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) ⟨a.val - 2, by
        have ha1 : a.val ≠ 1 := fun hcon =>
          ha (Fin.ext (hcon.trans hv1.symm))
        have ha0 : a.val ≠ 0 := fun hcon =>
          h0 (Fin.ext (hcon.trans hv0.symm))
        have hlt := a.isLt
        omega⟩) with hsT_def
    have hsT0 : ∀ h : (0 : Fin (N + 3)) ≠ 1,
        sT 0 h = g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) := by
      intro h
      rw [hsT_def]
      exact dite_eq_left rfl
    have hsTS : ∀ (j : Fin (N + 1)) (h : j.succ.succ ≠ 1),
        sT j.succ.succ h = B N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) := by
      intro j h
      have hne0 : j.succ.succ ≠ (0 : Fin (N + 3)) := by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_succ, hv0] at h2
        omega
      have hstep : sT j.succ.succ h =
          B N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
            ⟨j.succ.succ.val - 2, by
              simp only [Fin.val_succ]
              have := j.isLt
              omega⟩) := by
        rw [hsT_def]
        exact dite_eq_right hne0
      rw [hstep]
      refine congrArg (fun t : Fin (N + 1) =>
        B N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) t)) (Fin.ext ?_)
      simp only [Fin.val_succ]
      omega
    obtain ⟨T, hTσ⟩ := exists_simplex_of_isCompatible (X := Y)
      (i := (1 : Fin (N + 3)))
      (Fin.lt_def.mpr (by rw [hv0, hv1]; omega))
      (by
        rw [Fin.lt_def, hv1]
        simp only [Fin.val_last]
        omega)
      sT
      (by
        intro a b ha hb hab
        have habv : a.val < b.val := Fin.lt_def.mp hab
        rcases fin_classify2 a with rfl | rfl | ⟨ja, rfl⟩
        · rcases fin_classify2 b with rfl | rfl | ⟨jb, rfl⟩
          · omega
          · exact (hb rfl).elim
          · rw [hsT0 ha, hsTS jb hb, pred_succ_succ', castPred_zero'']
            exact (hg0_succ N ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) jb).trans
              (hB0 N le_rfl _).symm
        · exact (ha rfl).elim
        · rcases fin_classify2 b with rfl | rfl | ⟨jb, rfl⟩
          · simp only [Fin.val_succ, hv0] at habv
            omega
          · exact (hb rfl).elim
          · have hjj : ja < jb := Fin.lt_def.mpr (by
              simp only [Fin.val_succ] at habv
              omega)
            rw [hsTS ja ha, hsTS jb hb, pred_succ_succ',
              castPred_succ_succ' ja (by
                have h1 := Fin.lt_def.mp hjj
                have h2 := jb.isLt
                omega)]
            obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by
              have h1 := Fin.lt_def.mp hjj
              have h2 := jb.isLt
              omega⟩
            have hjb : jb.succ =
                (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ := by
              rw [succ_pred_eq]
            rw [hjb]
            exact (hBdel N' le_rfl
              (delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding) ja)
              _).trans
              ((congrArg (B N')
                (delEmb_delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding)
                  hjj).symm).trans
                (hBdel N' le_rfl
                  (delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding) jb)
                  _).symm))
    have hne01 : (0 : Fin (N + 3)) ≠ 1 := by
      intro hcon
      have h2 := congrArg Fin.val hcon
      rw [hv0, hv1] at h2
      omega
    refine ⟨T, by rw [hTσ 0 hne01]; exact hsT0 hne01, fun j => ?_⟩
    have hne : j.succ.succ ≠ (1 : Fin (N + 3)) := by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp only [Fin.val_succ, hv1] at h2
      omega
    rw [hTσ _ hne]
    exact hsTS j hne
  obtain ⟨T, hT0, hTdel⟩ := hT
  have hFs : ∃ Fs : Y _⦋N + 3⦌, Y.δ 0 Fs = T ∧
      Y.δ 1 Fs = Y.σ 0 (g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)) ∧
        ∀ j : Fin (N + 1),
          Y.δ j.succ.succ.succ Fs =
            F N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) := by
    have hv0 : (0 : Fin (N + 4)).val = 0 := by simp
    have hv1 : (1 : Fin (N + 4)).val = 1 := by simp
    have hv2 : (2 : Fin (N + 4)).val = 2 := by simp
    set sF : ∀ (a : Fin (N + 4)) (_ : a ≠ 2), Y _⦋N + 2⦌ := fun a ha =>
      if h0 : a = 0 then T
      else if h1 : a = 1 then Y.σ 0 (g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding))
      else F N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) ⟨a.val - 3, by
        have ha2 : a.val ≠ 2 := fun hcon =>
          ha (Fin.ext (hcon.trans hv2.symm))
        have ha0 : a.val ≠ 0 := fun hcon =>
          h0 (Fin.ext (hcon.trans hv0.symm))
        have ha1 : a.val ≠ 1 := fun hcon =>
          h1 (Fin.ext (hcon.trans hv1.symm))
        have hlt := a.isLt
        omega⟩) with hsF_def
    have hsF0 : ∀ h : (0 : Fin (N + 4)) ≠ 2, sF 0 h = T := by
      intro h
      rw [hsF_def]
      exact dite_eq_left rfl
    have hsF1 : ∀ h : (1 : Fin (N + 4)) ≠ 2,
        sF 1 h = Y.σ 0 (g0 (N + 1) ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)) := by
      intro h
      rw [hsF_def]
      refine (dite_eq_right ?_).trans (dite_eq_left rfl)
      intro hcon
      have h2 := congrArg Fin.val hcon
      rw [hv1, hv0] at h2
      omega
    have hsFS : ∀ (j : Fin (N + 1)) (h : j.succ.succ.succ ≠ 2),
        sF j.succ.succ.succ h =
          F N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) := by
      intro j h
      have hne0 : j.succ.succ.succ ≠ (0 : Fin (N + 4)) := by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_succ, hv0] at h2
        omega
      have hne1 : j.succ.succ.succ ≠ (1 : Fin (N + 4)) := by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_succ, hv1] at h2
        omega
      have hstep : sF j.succ.succ.succ h =
          F N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
            ⟨j.succ.succ.succ.val - 3, by
              simp only [Fin.val_succ]
              have := j.isLt
              omega⟩) := by
        rw [hsF_def]
        exact (dite_eq_right hne0).trans (dite_eq_right hne1)
      rw [hstep]
      refine congrArg (fun t : Fin (N + 1) =>
        F N (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) t)) (Fin.ext ?_)
      simp only [Fin.val_succ]
      omega
    obtain ⟨Fs, hFσ⟩ := exists_simplex_of_isCompatible (X := Y)
      (i := (2 : Fin (N + 4)))
      (Fin.lt_def.mpr (by rw [hv0, hv2]; omega))
      (by
        rw [Fin.lt_def, hv2]
        simp [Fin.val_last])
      sF
      (by
        intro a b ha hb hab
        have habv : a.val < b.val := Fin.lt_def.mp hab
        rcases fin_classify3 a with rfl | rfl | rfl | ⟨ja, rfl⟩
        · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
          · omega
          · rw [hsF0 ha, hsF1 hb, pred_one'', castPred_zero'']
            exact hT0.trans (δ_zero_σ_zero _).symm
          · exact (hb rfl).elim
          · rw [hsF0 ha, hsFS jb hb, pred_succ_succ_succ',
              castPred_zero'']
            exact (hTdel jb).trans (hF0 N le_rfl _).symm
        · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
          · rw [hv0, hv1] at habv
            omega
          · omega
          · exact (hb rfl).elim
          · rw [hsF1 ha, hsFS jb hb, pred_succ_succ_succ',
              castPred_one'', δ_succ_succ_σ_zero,
              hg0_succ N ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) jb]
            exact (hF1 N le_rfl _).symm
        · exact (ha rfl).elim
        · rcases fin_classify3 b with rfl | rfl | rfl | ⟨jb, rfl⟩
          · simp only [Fin.val_succ, hv0] at habv
            omega
          · simp only [Fin.val_succ, hv1] at habv
            omega
          · exact (hb rfl).elim
          · have hjj : ja < jb := Fin.lt_def.mpr (by
              simp only [Fin.val_succ] at habv
              omega)
            rw [hsFS ja ha, hsFS jb hb, pred_succ_succ_succ',
              castPred_succ_succ_succ' ja (by
                have h1 := Fin.lt_def.mp hjj
                have h2 := jb.isLt
                omega)]
            obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by
              have h1 := Fin.lt_def.mp hjj
              have h2 := jb.isLt
              omega⟩
            have hjb : jb.succ.succ =
                (jb.pred (Fin.ne_zero_of_lt hjj)).succ.succ.succ := by
              rw [succ_pred_eq]
            rw [hjb]
            exact (hFdel N' le_rfl
              (delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding) ja)
              _).trans
              ((congrArg (F N')
                (delEmb_delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding)
                  hjj).symm).trans
                (hFdel N' le_rfl
                  (delEmb ((OrderIso.refl (Fin (N' + 2))).toOrderEmbedding) jb)
                  _).symm))
    have hne02 : (0 : Fin (N + 4)) ≠ 2 := by
      intro hcon
      have h2 := congrArg Fin.val hcon
      rw [hv0, hv2] at h2
      omega
    have hne12 : (1 : Fin (N + 4)) ≠ 2 := by
      intro hcon
      have h2 := congrArg Fin.val hcon
      rw [hv1, hv2] at h2
      omega
    refine ⟨Fs, by rw [hFσ 0 hne02]; exact hsF0 hne02,
      by rw [hFσ 1 hne12]; exact hsF1 hne12, fun j => ?_⟩
    have hne : j.succ.succ.succ ≠ (2 : Fin (N + 4)) := by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp only [Fin.val_succ, hv2] at h2
      omega
    rw [hFσ _ hne]
    exact hsFS j hne
  obtain ⟨Fs, hFs0, hFs1, hFsdel⟩ := hFs
  refine ⟨Y.δ 2 Fs, ?_, ?_⟩
  · have hdd := δ_δ_of_lt' Fs (1 : Fin (N + 3)) (2 : Fin (N + 4)) (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hv1 : (1 : Fin (N + 3)).val = 1 := by simp
      have hv2 : (2 : Fin (N + 4)).val = 2 := by simp
      omega)
    rw [pred_two'', castSucc_one'', hFs1] at hdd
    exact hdd.trans (δ_one_σ_zero _)
  · intro j
    have hdd := δ_δ_of_le' Fs (2 : Fin (N + 3)) j.succ.succ (by
      rw [Fin.le_def]
      have hv2 : (2 : Fin (N + 3)).val = 2 := by simp
      simp only [Fin.val_succ, hv2]
      omega)
    rw [castSucc_two''] at hdd
    exact hdd.symm.trans
      ((congrArg (Y.δ 2) (hFsdel j)).trans (hF2 N le_rfl _))

end AbstractRounds

section HornIdentification

/-- The underlying simplex of a horn face is the corresponding
face of the standard simplex. -/
private lemma horn_face_val {n : ℕ} (j : Fin (n + 3)) (hj : j ≠ (0 : Fin (n + 3))) :
    (horn.face (0 : Fin (n + 3)) j hj).val =
      stdSimplex.objEquiv.symm (SimplexCategory.δ j) := rfl

/-- A horn simplex whose embedding is a face embedding is the
corresponding horn face. -/
private lemma hornSimplex_eq_face {N : ℕ} (e : Fin (N + 2) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ 0 ∧ j ∉ Set.range e)
    (j : Fin (N + 3)) (hj : j ≠ 0) (he : e = Fin.succAboveOrderEmb j) :
    hornSimplex e h = horn.face (0 : Fin (N + 3)) j hj := by
  apply Subtype.ext
  rw [hornSimplex_val, horn_face_val]
  congr 1
  rw [he]
  rfl

-- Public: this identity is pinned by the tests.
/-- The embedding `(0, 2, ..., N + 2)` is the first face
embedding. -/
lemma emb0_reflEmb {N : ℕ} :
    emb0 ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) =
      Fin.succAboveOrderEmb (1 : Fin (N + 3)) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · change ((emb0 ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)) 0).val =
      (Fin.succAbove (1 : Fin (N + 3)) 0).val
    have h1 : (1 : Fin (N + 3)).val = 1 := by simp
    simp [emb0]
  · intro i
    have h1 : (1 : Fin (N + 3)).val = 1 := by simp
    change ((emb0 ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)) i.succ).val =
      (Fin.succAbove (1 : Fin (N + 3)) i.succ).val
    rw [show emb0 ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) i.succ =
        tailEmb N i from rfl, tailEmb_val, succAbove_val]
    simp only [Fin.val_succ, h1]
    split_ifs <;> omega

-- Public: this identity is pinned by the tests.
/-- The embedding `(0, 1, 2, ..., ĵ, ..., N + 2)` is the
`(j + 2)`-nd face embedding. -/
lemma emb01_delEmb_reflEmb {N : ℕ} (j : Fin (N + 1)) :
    emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) =
      Fin.succAboveOrderEmb j.succ.succ := by
  ext i
  refine Fin.cases ?_ ?_ i
  · change ((emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j))
        0).val = (Fin.succAbove j.succ.succ 0).val
    simp [emb01]
  · intro i
    refine Fin.cases ?_ ?_ i
    · have hv1 : (1 : Fin (N + 3)).val = 1 := by simp
      change ((emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j))
          (0 : Fin (N + 1)).succ).val =
        (Fin.succAbove j.succ.succ (0 : Fin (N + 1)).succ).val
      rw [show emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j)
          (0 : Fin (N + 1)).succ = (1 : Fin (N + 3)) from rfl, succAbove_val,
        hv1]
      simp [Fin.val_succ]
    · intro i
      change ((emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j))
          i.succ.succ).val =
        (Fin.succAbove j.succ.succ i.succ.succ).val
      rw [show emb01 (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j)
          i.succ.succ = tailEmb N (Fin.succAbove j i) from rfl,
        tailEmb_val, succAbove_val, succAbove_val]
      simp only [Fin.val_succ]
      split_ifs <;> omega

/-- The `(0, 1)`-edge simplex of `Λ[n + 2, 0]` is the horn
simplex of the embedding `(0, 1)`. -/
private lemma leftHornEdgeSimplex_val (n : ℕ) :
    (leftHornEdgeSimplex.{u} n).val =
      stdSimplex.objEquiv.symm (homOfEmb (emb01 emptyEmb)) := by
  apply stdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  change stdSimplex.objEquiv (stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩
    (Fin.zero_le _)) = homOfEmb (emb01 emptyEmb)
  have hv1 : (1 : Fin (n + 3)).val = 1 := by simp
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [stdSimplex.edge, homOfEmb, emb01, emb1]
  · intro i'
    have hi' : i' = 0 := Subsingleton.elim i' 0
    subst hi'
    change ((stdSimplex.edge (n + 2) 0 ⟨1, by omega⟩ (Fin.zero_le _))
        (0 : Fin 1).succ).val = ((emb01 emptyEmb) (0 : Fin 1).succ).val
    rw [show emb01 emptyEmb (0 : Fin 1).succ = (1 : Fin (n + 3)) from rfl]
    exact hv1.symm

end HornIdentification

section LeftHornTheorem

variable {X : SSet.{u}} [Quasicategory X]

/-- **Joyal's special left outer horn filling in all
dimensions**: in a quasicategory, every left outer horn
`Λ[n + 2, 0] ⟶ X` whose `(0, 1)`-edge is an equivalence extends
to `Δ[n + 2]`. This generalizes `exists_fill_horn_three_zero_of_isEquivalence`
(`SpecialOuterHorn.lean`, packet T18, `n = 1`) following Dugger's
filtration argument, factored through
`exists_filler_simplex_of_leftData`. -/
theorem exists_fill_horn_left_of_isEquivalence {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ := by
  have hed : (leftHornEdge σ₀).edge = g01 σ₀ emptyEmb := by
    rw [leftHornEdge_edge, g01, dite_eq_left (Nat.zero_le n)]
    exact congrArg (σ₀.app _) (by
      apply Subtype.ext
      rw [leftHornEdgeSimplex_val, hornSimplex_val])
  have h01 : (Edge.mk' (g01 σ₀ emptyEmb)).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (leftHornEdge σ₀).edge = (Edge.mk' (g01 σ₀ emptyEmb)).edge from hed)).mp h
  obtain ⟨I⟩ := h01.nonempty_invStruct
  obtain ⟨σ_s, hσ1, hσdel⟩ := exists_filler_simplex_of_leftData (Y := X)
    (N := n) (g01 := fun k u => g01 σ₀ u) (g0 := fun k u => g0 σ₀ u)
    (g1 := fun k u => g1 σ₀ u)
    (hg01_0 := fun k hk u => δ_g01_zero σ₀ u hk)
    (hg01_1 := fun k hk u => δ_g01_one σ₀ u hk)
    (hg01_succ := fun k hk u j => δ_g01_succ_succ σ₀ hk j)
    (hg0_succ := fun k u j => δ_g0_succ σ₀ j)
    (hg1_succ := fun k hk u j => δ_g1_succ σ₀ hk j)
    (α := I.homInvId.simplex) (β := I.invHomId.simplex)
    (invE := I.inv.edge)
    (hα0 := I.homInvId.d₀)
    (hα1 := by rw [I.homInvId.d₁, Edge.id_edge])
    (hβ0 := I.invHomId.d₀)
    (hβ1 := by rw [I.invHomId.d₁, Edge.id_edge])
    (hβ2 := I.invHomId.d₂)
    (hinvSrc := I.inv.src_eq)
  refine ⟨yonedaEquiv.symm σ_s, horn.hom_ext' fun j hj => ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  rcases fin_classify2 (K := n) j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd rfl hj
  · have hface : σ₀.app _ (horn.face (0 : Fin (n + 3)) (1 : Fin (n + 3)) hj) =
        g0 σ₀ ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding) := by
      rw [g0]
      exact congrArg (σ₀.app _)
        (hornSimplex_eq_face (emb0
          ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding)) _
          (1 : Fin (n + 3)) hj emb0_reflEmb).symm
    rw [hface]
    exact hσ1.symm
  · have hface : σ₀.app _ (horn.face (0 : Fin (n + 3)) j'.succ.succ hj) =
        g01 σ₀ (delEmb ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding) j') := by
      rw [g01, dite_eq_left (le_refl n)]
      exact congrArg (σ₀.app _)
        (hornSimplex_eq_face (emb01
          (delEmb ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding) j')) _
          j'.succ.succ hj (emb01_delEmb_reflEmb j')).symm
    rw [hface]
    exact (hσdel j').symm

end LeftHornTheorem

section RightInfrastructure

-- Public: used in the definitions of the public embeddings
-- `emb2r` and `emb12r`.
/-- Appending a larger element to an order embedding into
`Fin (N + 3)`. -/
def snocEmb {k N : ℕ} (e : Fin k ↪o Fin (N + 3)) (a : Fin (N + 3))
    (h : ∀ i, e i < a) : Fin (k + 1) ↪o Fin (N + 3) :=
  OrderEmbedding.ofStrictMono (Fin.snoc (fun i ↦ e i) a) (by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simpa using e.strictMono (Fin.castSucc_lt_castSucc_iff.mp hij)
      · rw [Fin.lt_def] at hij
        simp only [Fin.val_castSucc, Fin.val_last] at hij
        have hj := j.isLt
        omega
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simpa using h i
      · simp at hij)

@[simp]
private lemma snocEmb_last {k N : ℕ} (e : Fin k ↪o Fin (N + 3)) (a : Fin (N + 3))
    (h : ∀ i, e i < a) : snocEmb e a h (Fin.last k) = a := by
  simp [snocEmb]

@[simp]
private lemma snocEmb_castSucc {k N : ℕ} (e : Fin k ↪o Fin (N + 3)) (a : Fin (N + 3))
    (h : ∀ i, e i < a) (i : Fin k) : snocEmb e a h i.castSucc = e i := by
  simp [snocEmb]

private lemma range_snocEmb {k N : ℕ} (e : Fin k ↪o Fin (N + 3)) (a : Fin (N + 3))
    (h : ∀ i, e i < a) :
    Set.range (snocEmb e a h) = Set.range e ∪ {a} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp
    · simp
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, by simp⟩
    · exact ⟨Fin.last k, by simp⟩

/-- Deleting the last element of a snoc'd embedding. -/
private lemma delEmb_snocEmb_last {k N : ℕ} (e : Fin k ↪o Fin (N + 3))
    (a : Fin (N + 3)) (h : ∀ i, e i < a) :
    delEmb (snocEmb e a h) (Fin.last k) = e := by
  ext i
  have key : ((Fin.succAboveOrderEmb (Fin.last k)).comp (snocEmb e a h)) i =
      e i := by
    change snocEmb e a h (Fin.succAbove (Fin.last k) i) = e i
    rw [show Fin.succAbove (Fin.last k) i = i.castSucc from by
      ext
      rw [succAbove_val]
      have hi := i.isLt
      simp [Fin.val_last, hi]]
    simp
  exact congrArg Fin.val key

/-- Deleting an earlier element of a snoc'd embedding. -/
private lemma delEmb_snocEmb_castSucc {k N : ℕ} (e : Fin (k + 1) ↪o Fin (N + 3))
    (a : Fin (N + 3)) (h : ∀ i, e i < a) (j : Fin (k + 1)) :
    delEmb (snocEmb e a h) j.castSucc =
      snocEmb (delEmb e j) a (fun _i ↦ h _) := by
  ext i
  have key : ((Fin.succAboveOrderEmb j.castSucc).comp (snocEmb e a h)) i =
      snocEmb (delEmb e j) a (fun i ↦ h _) i := by
    change snocEmb e a h (Fin.succAbove j.castSucc i) =
      snocEmb (delEmb e j) a _ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rw [show Fin.succAbove j.castSucc i.castSucc =
          (Fin.succAbove j i).castSucc from by
        ext
        rw [Fin.val_castSucc, succAbove_val, succAbove_val]
        simp only [Fin.val_castSucc]]
      exact (snocEmb_castSucc e a h _).trans
        (snocEmb_castSucc (delEmb e j) a _ i).symm
    · rw [show Fin.succAbove j.castSucc (Fin.last k) = Fin.last (k + 1) from by
        ext
        rw [succAbove_val]
        simp only [Fin.val_castSucc, Fin.val_last]
        have hj := j.isLt
        split_ifs <;> omega]
      exact (snocEmb_last e a h).trans (snocEmb_last (delEmb e j) a _).symm
  exact congrArg Fin.val key

-- Public: used in the definitions of the public embeddings
-- `emb2r` and `emb12r`.
/-- The embedding of the head vertices `{0, ..., N}`. -/
def headEmb (N : ℕ) : Fin (N + 1) ↪o Fin (N + 3) :=
  OrderEmbedding.ofStrictMono (fun i ↦ i.castSucc.castSucc) (by
    intro a b hab
    exact hab)

private lemma headEmb_val (N : ℕ) (i : Fin (N + 1)) :
    (headEmb N i).val = i.val := rfl

-- Public: this embedding occurs in statements pinned by the tests.
/-- Reversing an order embedding: `i ↦ (u (rev i)).rev`. -/
def revEmb {k N : ℕ} (u : Fin k ↪o Fin (N + 1)) : Fin k ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (fun i ↦ (u i.rev).rev) (by
    intro a b hab
    have h1 : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    have h2 := u.strictMono h1
    exact Fin.rev_lt_rev.mpr h2)

@[simp]
private lemma revEmb_apply {k N : ℕ} (u : Fin k ↪o Fin (N + 1)) (i : Fin k) :
    revEmb u i = (u i.rev).rev := rfl

-- Public: this identity is pinned by the tests.
/-- Reversal commutes with deletion, reversing the deleted
position. -/
lemma delEmb_revEmb {k N : ℕ} (u : Fin (k + 1) ↪o Fin (N + 1))
    (j : Fin (k + 1)) :
    delEmb (revEmb u) j.rev = revEmb (delEmb u j) := by
  ext i
  have key : delEmb (revEmb u) j.rev i = revEmb (delEmb u j) i := by
    change (u (Fin.succAbove j.rev i).rev).rev = (u (Fin.succAbove j i.rev)).rev
    congr 1
    congr 1
    ext
    simp only [Fin.val_rev, succAbove_val]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> omega
  rw [key]

/-- Reversing the identity embedding does nothing. -/
private lemma revEmb_reflEmb {N : ℕ} :
    revEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) =
      (OrderIso.refl (Fin (N + 1))).toOrderEmbedding := by
  ext i
  change ((i.rev).rev).val = i.val
  simp only [Fin.val_rev]
  have hi := i.isLt
  omega

-- Public: this embedding occurs in statements pinned by the tests.
/-- Suffix the top vertex `N + 2`: the embedding `S ∪ {N + 2}`. -/
def emb2r {k N : ℕ} (u : Fin k ↪o Fin (N + 1)) :
    Fin (k + 1) ↪o Fin (N + 3) :=
  snocEmb (u.comp (headEmb N)) (Fin.last (N + 2)) (fun i ↦ by
    rw [Fin.lt_def, Fin.val_last]
    change (headEmb N (u i)).val < N + 2
    rw [headEmb_val]
    have hi := (u i).isLt
    omega)

-- Public: used in the definition of the public embedding `emb12r`.
/-- Suffix the vertex `N + 1`: the embedding `S ∪ {N + 1}`. -/
def emb1r {k N : ℕ} (u : Fin k ↪o Fin (N + 1)) :
    Fin (k + 1) ↪o Fin (N + 3) :=
  snocEmb (u.comp (headEmb N)) ⟨N + 1, by omega⟩ (fun i ↦ by
    rw [Fin.lt_def]
    change (headEmb N (u i)).val < N + 1
    rw [headEmb_val]
    exact (u i).isLt)

-- Public: this embedding occurs in statements pinned by the tests.
/-- Suffix both top vertices: the embedding
`S ∪ {N + 1, N + 2}`. -/
def emb12r {k N : ℕ} (u : Fin k ↪o Fin (N + 1)) :
    Fin (k + 2) ↪o Fin (N + 3) :=
  snocEmb (emb1r u) (Fin.last (N + 2)) (fun i ↦ by
    rw [Fin.lt_def, Fin.val_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · have e1 : emb1r u i.castSucc = headEmb N (u i) :=
        snocEmb_castSucc ..
      rw [e1, headEmb_val]
      have hi := (u i).isLt
      omega
    · have e2 : emb1r u (Fin.last k) = ⟨N + 1, by omega⟩ :=
        snocEmb_last ..
      rw [e2]
      change N + 1 < N + 2
      omega)

end RightInfrastructure

section OppositeQuasicategory

-- Public: the opposite-quasicategory transport is used by
-- the right-horn argument and is exercised in the tests.
/-- The opposite of a quasicategory is a quasicategory: inner
horns in `X.op` at `i` are transported, through `opObjEquiv` and
reversal of face indices, to inner horns in `X` at `i.rev`, which
are filled there at the simplex level
(`exists_simplex_of_isCompatible`). -/
lemma quasicategory_op (X : SSet.{u}) [Quasicategory X] :
    Quasicategory X.op := by
  apply quasicategory_of_filler
  intro n i σ₀ h0 hn
  have h0' : 0 < i.rev := by
    rw [Fin.lt_def] at hn ⊢
    simp only [Fin.val_rev, Fin.val_last, Fin.val_zero] at hn ⊢
    omega
  have hn' : i.rev < Fin.last (n + 2) := by
    rw [Fin.lt_def] at h0 ⊢
    simp only [Fin.val_rev, Fin.val_last, Fin.val_zero] at h0 ⊢
    omega
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X) (i := i.rev)
    h0' hn'
    (fun j hj => opObjEquiv (σ₀.app _ (horn.face i j.rev (by
      intro hcon
      apply hj
      rw [← Fin.rev_rev j, hcon]))))
    (by
      intro a b ha hb hab
      have hab' : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
      have hc := horn.IsCompatible.of_hom σ₀ b.rev a.rev
        (by
          intro hcon
          apply hb
          rw [← Fin.rev_rev b, hcon])
        (by
          intro hcon
          apply ha
          rw [← Fin.rev_rev a, hcon]) hab'
      have hc2 := congrArg yonedaEquiv hc
      simp only [] at hc2
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
        horn.ι, horn.ι, yonedaEquiv_symm_comp, yonedaEquiv_symm_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hc2
      simp only []
      rw [δ_opObjEquiv, δ_opObjEquiv, Fin.rev_pred, Fin.rev_castPred]
      exact congrArg opObjEquiv hc2.symm)
  refine ⟨opObjEquiv.symm σ, fun j hj => ?_⟩
  rw [op_δ]
  have hj' : j.rev ≠ i.rev := by
    intro hcon
    apply hj
    rw [← Fin.rev_rev j, hcon, Fin.rev_rev]
  rw [Equiv.apply_symm_apply, hσ j.rev hj']
  simp only []
  rw [Equiv.symm_apply_apply]
  congr 1
  exact Subtype.ext (by
    change stdSimplex.objEquiv.symm (SimplexCategory.δ j.rev.rev) =
      stdSimplex.objEquiv.symm (SimplexCategory.δ j)
    rw [Fin.rev_rev])

end OppositeQuasicategory

section RightHornSimplices

variable {N : ℕ} {Z : SSet.{u}}

/-- The simplex of the right horn `Λ[N + 2, N + 2]` determined by
an order embedding whose range avoids some vertex other than the
last. -/
private def hornSimplexR {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e) :
    (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}) _⦋m⦌ :=
  ⟨stdSimplex.objEquiv.symm (homOfEmb e), by
    rw [mem_horn_iff_notMem_range]
    obtain ⟨j, hj0, hj⟩ := h
    refine ⟨j, hj0, ?_⟩
    have hrange : Set.range (stdSimplex.objEquiv.symm (homOfEmb e)) =
        Set.range e := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange]
    exact hj⟩

private lemma hornSimplexR_val {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e) :
    (hornSimplexR e h).val = stdSimplex.objEquiv.symm (homOfEmb e) := rfl

/-- The image in `Z` of the right horn simplex determined by
`e`. -/
private def hornAppR (σ₀ : (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}) ⟶ Z)
    {m : ℕ} (e : Fin (m + 1) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e) :
    Z _⦋m⦌ :=
  σ₀.app _ (hornSimplexR e h)

private lemma hornAppR_congr (σ₀ : (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}) ⟶ Z)
    {m : ℕ} {e₁ e₂ : Fin (m + 1) ↪o Fin (N + 3)}
    (h₁ : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e₁)
    (h₂ : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e₂)
    (he : e₁ = e₂) :
    hornAppR σ₀ e₁ h₁ = hornAppR σ₀ e₂ h₂ := by
  subst he
  rfl

/-- Faces of right horn simplices are right horn simplices of
deleted embeddings. -/
private lemma δ_hornAppR (σ₀ : (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}) ⟶ Z)
    {k : ℕ} (e : Fin (k + 2) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e)
    (i : Fin (k + 2)) :
    Z.δ i (hornAppR σ₀ e h) =
      hornAppR σ₀ (delEmb e i)
        (by
          obtain ⟨j, hj0, hj⟩ := h
          exact ⟨j, hj0, fun hjr ↦ hj (range_delEmb_subset e i hjr)⟩) := by
  have hs : (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}).δ i (hornSimplexR e h) =
      hornSimplexR (delEmb e i)
        (by
          obtain ⟨j, hj0, hj⟩ := h
          exact ⟨j, hj0, fun hjr ↦ hj (range_delEmb_subset e i hjr)⟩) := by
    apply Subtype.ext
    change Δ[N + 2].δ i (stdSimplex.objEquiv.symm (homOfEmb e)) =
      stdSimplex.objEquiv.symm (homOfEmb (delEmb e i))
    rw [show Δ[N + 2].δ i (stdSimplex.objEquiv.symm (homOfEmb e)) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ i ≫ homOfEmb e) from rfl,
      δ_comp_homOfEmb]
  have hnat : σ₀.app _ ((Λ[N + 2, Fin.last (N + 2)] : SSet.{u}).δ i
      (hornSimplexR e h)) = Z.δ i (σ₀.app _ (hornSimplexR e h)) :=
    NatTrans.naturality_apply σ₀ (SimplexCategory.δ i).op (hornSimplexR e h)
  rw [hs] at hnat
  exact hnat.symm

/-- The underlying simplex of a right horn face. -/
private lemma horn_faceR_val {n : ℕ} (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) :
    (horn.face (Fin.last (n + 2)) j hj).val =
      stdSimplex.objEquiv.symm (SimplexCategory.δ j) := rfl

/-- A right horn simplex whose embedding is a face embedding is
the corresponding horn face. -/
private lemma hornSimplexR_eq_face {N : ℕ} (e : Fin (N + 2) ↪o Fin (N + 3))
    (h : ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range e)
    (j : Fin (N + 3)) (hj : j ≠ Fin.last (N + 2))
    (he : e = Fin.succAboveOrderEmb j) :
    hornSimplexR e h = horn.face (Fin.last (N + 2)) j hj := by
  apply Subtype.ext
  rw [hornSimplexR_val, horn_faceR_val]
  congr 1
  rw [he]
  rfl

/-- The `(N + 1, N + 2)`-edge simplex of `Λ[n + 2, n + 2]` is the
right horn simplex of the embedding `(N + 1, N + 2)` given by
`emb12r` at the empty tail. -/
private lemma rightHornEdgeSimplex_val (n : ℕ) :
    (rightHornEdgeSimplex.{u} n).val =
      stdSimplex.objEquiv.symm (homOfEmb (emb12r emptyEmb)) := by
  apply stdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  change stdSimplex.objEquiv (stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩
    (Fin.last (n + 2)) (by simp [Fin.le_def])) = homOfEmb (emb12r emptyEmb)
  ext i
  refine Fin.cases ?_ ?_ i
  · change ((stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
        (by simp [Fin.le_def])) 0).val = ((emb12r emptyEmb) 0).val
    rw [show emb12r emptyEmb 0 = ⟨n + 1, by omega⟩ from by
      change snocEmb (emb1r emptyEmb) (Fin.last (n + 2)) _ 0 = _
      rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
        snocEmb_castSucc]
      change snocEmb (emptyEmb.comp (headEmb n)) ⟨n + 1, by omega⟩ _ 0 = _
      rw [show (0 : Fin 1) = Fin.last 0 from rfl, snocEmb_last]]
    rfl
  · intro i'
    have hi' : i' = 0 := Subsingleton.elim i' 0
    subst hi'
    change ((stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
        (by simp [Fin.le_def])) (0 : Fin 1).succ).val =
      ((emb12r emptyEmb) (0 : Fin 1).succ).val
    rw [show emb12r emptyEmb (0 : Fin 1).succ = Fin.last (n + 2) from by
      change snocEmb (emb1r emptyEmb) (Fin.last (n + 2)) _ (0 : Fin 1).succ = _
      rw [show (0 : Fin 1).succ = Fin.last 1 from rfl, snocEmb_last]]
    rfl

end RightHornSimplices

section RightHornFamilies

variable {N : ℕ} {Z : SSet.{u}}
  (σ₀ : (Λ[N + 2, Fin.last (N + 2)] : SSet.{u}) ⟶ Z)
  {k : ℕ} (u : Fin k ↪o Fin (N + 1))

private lemma emb2r_castSucc (i : Fin k) :
    emb2r u i.castSucc = headEmb N (u i) := snocEmb_castSucc ..

private lemma emb2r_last : emb2r u (Fin.last k) = Fin.last (N + 2) :=
  snocEmb_last ..

private lemma emb1r_castSucc (i : Fin k) :
    emb1r u i.castSucc = headEmb N (u i) := snocEmb_castSucc ..

private lemma emb1r_last : emb1r u (Fin.last k) = ⟨N + 1, by omega⟩ :=
  snocEmb_last ..

private lemma emb12r_castSucc (i : Fin (k + 1)) :
    emb12r u i.castSucc = emb1r u i := snocEmb_castSucc ..

private lemma emb12r_last :
    emb12r u (Fin.last (k + 1)) = Fin.last (N + 2) := snocEmb_last ..

private lemma emb2r_avoid :
    ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range (emb2r u) := by
  refine ⟨⟨N + 1, by omega⟩, by
    intro hcon
    have h2 := congrArg Fin.val hcon
    rw [Fin.val_last] at h2
    change N + 1 = N + 2 at h2
    omega, ?_⟩
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rw [emb2r_castSucc, headEmb_val] at hval
    change (u i).val = N + 1 at hval
    have hi2 := (u i).isLt
    omega
  · rw [emb2r_last, Fin.val_last] at hval
    change N + 2 = N + 1 at hval
    omega

private lemma emb1r_avoid (hk : k ≤ N) :
    ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range (emb1r u) := by
  obtain ⟨t, ht⟩ := exists_notMem_range u hk
  refine ⟨headEmb N t, by
    intro hcon
    have h2 := congrArg Fin.val hcon
    rw [headEmb_val, Fin.val_last] at h2
    have ht2 := t.isLt
    omega, ?_⟩
  rintro ⟨i, hi⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rw [emb1r_castSucc] at hi
    exact ht ⟨i, (headEmb N).injective hi⟩
  · rw [emb1r_last] at hi
    have hval := congrArg Fin.val hi
    rw [headEmb_val] at hval
    change N + 1 = t.val at hval
    have ht2 := t.isLt
    omega

private lemma emb12r_avoid (hk : k ≤ N) :
    ∃ j : Fin (N + 3), j ≠ Fin.last (N + 2) ∧ j ∉ Set.range (emb12r u) := by
  obtain ⟨j, hj0, hj⟩ := emb1r_avoid u hk
  refine ⟨j, hj0, ?_⟩
  rintro ⟨i, hi⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rw [emb12r_castSucc] at hi
    exact hj ⟨i, hi⟩
  · rw [emb12r_last] at hi
    exact hj0 hi.symm

/-- The `(S, N + 2)` simplex of the right horn `σ₀`. -/
private def r2 : Z _⦋k⦌ := hornAppR σ₀ (emb2r u) (emb2r_avoid u)

/-- The `(S, N + 1)` simplex of the right horn `σ₀` (totalized
with `r2` outside the proper range `k ≤ N`). -/
private def r1 : Z _⦋k⦌ :=
  if hk : k ≤ N then hornAppR σ₀ (emb1r u) (emb1r_avoid u hk)
  else r2 σ₀ u

/-- The `(S, N + 1, N + 2)` simplex of the right horn `σ₀`
(totalized outside the proper range `k ≤ N`). -/
private def r12 : Z _⦋k + 1⦌ :=
  if hk : k ≤ N then hornAppR σ₀ (emb12r u) (emb12r_avoid u hk)
  else Z.σ 0 (r2 σ₀ u)

private lemma delEmb_emb12r_last :
    delEmb (emb12r u) (Fin.last (k + 1)) = emb1r u :=
  delEmb_snocEmb_last ..

private lemma delEmb_emb12r_castSucc_last :
    delEmb (emb12r u) (Fin.last k).castSucc = emb2r u := by
  change delEmb (snocEmb (emb1r u) (Fin.last (N + 2)) _) (Fin.last k).castSucc =
    emb2r u
  rw [delEmb_snocEmb_castSucc]
  change snocEmb (delEmb (emb1r u) (Fin.last k)) (Fin.last (N + 2)) _ =
    snocEmb (u.comp (headEmb N)) (Fin.last (N + 2)) _
  congr 1
  exact delEmb_snocEmb_last ..

private lemma delEmb_emb12r_castSucc_castSucc
    {u : Fin (k + 1) ↪o Fin (N + 1)} (j : Fin (k + 1)) :
    delEmb (emb12r u) j.castSucc.castSucc = emb12r (delEmb u j) := by
  change delEmb (snocEmb (emb1r u) (Fin.last (N + 2)) _) j.castSucc.castSucc =
    emb12r (delEmb u j)
  rw [delEmb_snocEmb_castSucc]
  change snocEmb (delEmb (emb1r u) j.castSucc) (Fin.last (N + 2)) _ =
    snocEmb (emb1r (delEmb u j)) (Fin.last (N + 2)) _
  congr 1
  change delEmb (snocEmb (u.comp (headEmb N)) ⟨N + 1, by omega⟩ _) j.castSucc =
    snocEmb ((delEmb u j).comp (headEmb N)) ⟨N + 1, by omega⟩ _
  rw [delEmb_snocEmb_castSucc]
  congr 1

private lemma delEmb_emb2r_castSucc {u : Fin (k + 1) ↪o Fin (N + 1)}
    (j : Fin (k + 1)) :
    delEmb (emb2r u) j.castSucc = emb2r (delEmb u j) := by
  change delEmb (snocEmb (u.comp (headEmb N)) (Fin.last (N + 2)) _) j.castSucc =
    emb2r (delEmb u j)
  rw [delEmb_snocEmb_castSucc]
  change snocEmb (delEmb (u.comp (headEmb N)) j) (Fin.last (N + 2)) _ =
    snocEmb ((delEmb u j).comp (headEmb N)) (Fin.last (N + 2)) _
  congr 1

private lemma delEmb_emb1r_castSucc {u : Fin (k + 1) ↪o Fin (N + 1)}
    (j : Fin (k + 1)) :
    delEmb (emb1r u) j.castSucc = emb1r (delEmb u j) := by
  change delEmb (snocEmb (u.comp (headEmb N)) ⟨N + 1, by omega⟩ _) j.castSucc =
    emb1r (delEmb u j)
  rw [delEmb_snocEmb_castSucc]
  change snocEmb (delEmb (u.comp (headEmb N)) j) ⟨N + 1, by omega⟩ _ =
    snocEmb ((delEmb u j).comp (headEmb N)) ⟨N + 1, by omega⟩ _
  congr 1

private lemma δ_r12_last (hk : k ≤ N) :
    Z.δ (Fin.last (k + 1)) (r12 σ₀ u) = r1 σ₀ u := by
  rw [r12, r1, dite_eq_left hk, dite_eq_left hk, δ_hornAppR]
  exact hornAppR_congr σ₀ _ _ (delEmb_emb12r_last u)

private lemma δ_r12_castSucc_last (hk : k ≤ N) :
    Z.δ (Fin.last k).castSucc (r12 σ₀ u) = r2 σ₀ u := by
  rw [r12, dite_eq_left hk, δ_hornAppR]
  exact hornAppR_congr σ₀ _ _ (delEmb_emb12r_castSucc_last u)

private lemma δ_r12_castSucc_castSucc {u : Fin (k + 1) ↪o Fin (N + 1)}
    (hk : k + 1 ≤ N) (j : Fin (k + 1)) :
    Z.δ j.castSucc.castSucc (r12 σ₀ u) = r12 σ₀ (delEmb u j) := by
  have hk' : k ≤ N := by omega
  rw [r12, r12, dite_eq_left hk, dite_eq_left hk', δ_hornAppR]
  exact hornAppR_congr σ₀ _ _ (delEmb_emb12r_castSucc_castSucc (u := u) j)

private lemma δ_r2_castSucc {u : Fin (k + 1) ↪o Fin (N + 1)} (j : Fin (k + 1)) :
    Z.δ j.castSucc (r2 σ₀ u) = r2 σ₀ (delEmb u j) := by
  rw [r2, r2, δ_hornAppR]
  exact hornAppR_congr σ₀ _ _ (delEmb_emb2r_castSucc (u := u) j)

private lemma δ_r1_castSucc {u : Fin (k + 1) ↪o Fin (N + 1)} (hk : k + 1 ≤ N)
    (j : Fin (k + 1)) :
    Z.δ j.castSucc (r1 σ₀ u) = r1 σ₀ (delEmb u j) := by
  have hk' : k ≤ N := by omega
  rw [r1, r1, dite_eq_left hk, dite_eq_left hk', δ_hornAppR]
  exact hornAppR_congr σ₀ _ _ (delEmb_emb1r_castSucc (u := u) j)

end RightHornFamilies

section RightHornIdentification

-- Public: this identity is pinned by the tests.
/-- The embedding `(0, ..., N, N + 2)` is the `(N + 1)`-st face
embedding. -/
lemma emb2r_reflEmb {N : ℕ} :
    emb2r ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) =
      Fin.succAboveOrderEmb (Fin.last (N + 1)).castSucc := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · change ((emb2r ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding))
        i.castSucc).val =
      (Fin.succAbove (Fin.last (N + 1)).castSucc i.castSucc).val
    rw [emb2r_castSucc, headEmb_val]
    change i.val = (Fin.succAbove (Fin.last (N + 1)).castSucc i.castSucc).val
    rw [succAbove_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hi := i.isLt
    split_ifs; omega
  · change ((emb2r ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding))
        (Fin.last (N + 1))).val =
      (Fin.succAbove (Fin.last (N + 1)).castSucc (Fin.last (N + 1))).val
    rw [emb2r_last, Fin.val_last, succAbove_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    split_ifs <;> omega

-- Public: this identity is pinned by the tests.
/-- The embedding `(0, ..., ĵ, ..., N, N + 1, N + 2)` is the
`j`-th face embedding. -/
lemma emb12r_delEmb_reflEmb {N : ℕ} (j : Fin (N + 1)) :
    emb12r (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding) j) =
      Fin.succAboveOrderEmb j.castSucc.castSucc := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · change ((emb12r (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
          j)) i.castSucc.castSucc).val =
        (Fin.succAbove j.castSucc.castSucc i.castSucc.castSucc).val
      rw [emb12r_castSucc, emb1r_castSucc, headEmb_val, delEmb_apply]
      change (Fin.succAbove j i).val =
        (Fin.succAbove j.castSucc.castSucc i.castSucc.castSucc).val
      rw [succAbove_val, succAbove_val]
      simp only [Fin.val_castSucc]
    · change ((emb12r (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
          j)) (Fin.last N).castSucc).val =
        (Fin.succAbove j.castSucc.castSucc (Fin.last N).castSucc).val
      rw [emb12r_castSucc, emb1r_last]
      change N + 1 =
        (Fin.succAbove j.castSucc.castSucc (Fin.last N).castSucc).val
      rw [succAbove_val]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hj := j.isLt
      split_ifs <;> omega
  · change ((emb12r (delEmb ((OrderIso.refl (Fin (N + 1))).toOrderEmbedding)
        j)) (Fin.last (N + 1))).val =
      (Fin.succAbove j.castSucc.castSucc (Fin.last (N + 1))).val
    rw [emb12r_last, Fin.val_last, succAbove_val]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hj := j.isLt
    split_ifs <;> omega

end RightHornIdentification

section OppositeTransport

/-- Faces in `X.op` of transported simplices are transported
faces at reversed indices. -/
private lemma opδ_symm {X : SSet.{u}} {m : ℕ} (x : X _⦋m + 1⦌)
    (i : Fin (m + 2)) :
    X.op.δ i (opObjEquiv.symm x) = opObjEquiv.symm (X.δ i.rev x) := by
  rw [op_δ, Equiv.apply_symm_apply]

/-- Degeneracies in `X.op` of transported simplices are
transported degeneracies at reversed indices. -/
private lemma opσ_symm {X : SSet.{u}} {m : ℕ} (x : X _⦋m⦌)
    (i : Fin (m + 1)) :
    X.op.σ i (opObjEquiv.symm x) = opObjEquiv.symm (X.σ i.rev x) := by
  rw [op_σ, Equiv.apply_symm_apply]

/-- Transporting a face in `X.op` back to `X` reverses the face
index. -/
private lemma opδ_apply {X : SSet.{u}} {m : ℕ} (y : X.op _⦋m + 1⦌)
    (i : Fin (m + 2)) :
    opObjEquiv (X.op.δ i y) = X.δ i.rev (opObjEquiv y) := by
  rw [op_δ, Equiv.apply_symm_apply]

/-- Reversal sends `0` to the last index. -/
private lemma rev_zero' {k : ℕ} : (0 : Fin (k + 2)).rev = Fin.last (k + 1) := by
  ext
  have h0 : (0 : Fin (k + 2)).val = 0 := by simp
  rw [Fin.val_rev, Fin.val_last, h0]
  omega

/-- Reversal sends `1` to the second-to-last index. -/
private lemma rev_one' {k : ℕ} :
    (1 : Fin (k + 2)).rev = (Fin.last k).castSucc := by
  ext
  have h1 : (1 : Fin (k + 2)).val = 1 := by simp
  rw [Fin.val_rev, Fin.val_castSucc, Fin.val_last, h1]
  omega

/-- Reversal commutes with successor, as a cast successor. -/
private lemma rev_succ' {k : ℕ} (j : Fin (k + 1)) :
    j.succ.rev = j.rev.castSucc := by
  ext
  rw [Fin.val_rev, Fin.val_castSucc, Fin.val_rev]
  simp only [Fin.val_succ]
  have hj := j.isLt
  omega

/-- Reversal commutes with double successor, as a double cast
successor. -/
private lemma rev_succ_succ' {k : ℕ} (j : Fin (k + 1)) :
    j.succ.succ.rev = j.rev.castSucc.castSucc := by
  ext
  rw [Fin.val_rev, Fin.val_castSucc, Fin.val_castSucc, Fin.val_rev]
  simp only [Fin.val_succ]
  have hj := j.isLt
  omega

/-- Classification of the face indices of a right horn: the last
index, the second-to-last, or a double cast successor. -/
private lemma fin_classifyR {K : ℕ} (j : Fin (K + 3)) :
    j = Fin.last (K + 2) ∨ j = (Fin.last (K + 1)).castSucc ∨
      ∃ i : Fin (K + 1), j = i.castSucc.castSucc := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

end OppositeTransport

section RightHornTheorem

variable {X : SSet.{u}} [Quasicategory X]

/-- **Joyal's special right outer horn filling in all
dimensions**: in a quasicategory, every right outer horn
`Λ[n + 2, n + 2] ⟶ X` whose `(n + 1, n + 2)`-edge is an
equivalence extends to `Δ[n + 2]`. This is
`exists_filler_simplex_of_leftData` applied to `X.op` (a
quasicategory by `quasicategory_op`) with the suffix families
`r12`, `r1`, `r2` transported through `opObjEquiv` along
reversed subset embeddings; the inverse data of the reversed
edge is the transport of the inverse data of the right edge,
with the roles of the two homotopies swapped. -/
theorem exists_fill_horn_right_of_isEquivalence {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  have hed : (rightHornEdge σ₀).edge = r12 σ₀ emptyEmb := by
    rw [rightHornEdge_edge, r12, dite_eq_left (Nat.zero_le n)]
    exact congrArg (σ₀.app _) (by
      apply Subtype.ext
      rw [rightHornEdgeSimplex_val, hornSimplexR_val])
  have h12 : (Edge.mk' (r12 σ₀ emptyEmb)).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (rightHornEdge σ₀).edge = (Edge.mk' (r12 σ₀ emptyEmb)).edge from
      hed)).mp h
  obtain ⟨I⟩ := h12.nonempty_invStruct
  have : Quasicategory X.op := quasicategory_op X
  obtain ⟨σ_op, hσ1, hσdel⟩ := exists_filler_simplex_of_leftData
    (Y := X.op) (N := n)
    (g01 := fun k u => opObjEquiv.symm (r12 σ₀ (revEmb u)))
    (g0 := fun k u => opObjEquiv.symm (r2 σ₀ (revEmb u)))
    (g1 := fun k u => opObjEquiv.symm (r1 σ₀ (revEmb u)))
    (hg01_0 := fun k hk u => by
      show X.op.δ 0 (opObjEquiv.symm (r12 σ₀ (revEmb u))) =
        opObjEquiv.symm (r1 σ₀ (revEmb u))
      rw [opδ_symm, rev_zero', δ_r12_last σ₀ (revEmb u) hk])
    (hg01_1 := fun k hk u => by
      show X.op.δ 1 (opObjEquiv.symm (r12 σ₀ (revEmb u))) =
        opObjEquiv.symm (r2 σ₀ (revEmb u))
      rw [opδ_symm, rev_one', δ_r12_castSucc_last σ₀ (revEmb u) hk])
    (hg01_succ := fun k hk u j => by
      show X.op.δ j.succ.succ (opObjEquiv.symm (r12 σ₀ (revEmb u))) =
        opObjEquiv.symm (r12 σ₀ (revEmb (delEmb u j)))
      rw [opδ_symm, rev_succ_succ', δ_r12_castSucc_castSucc σ₀ hk j.rev,
        delEmb_revEmb])
    (hg0_succ := fun k u j => by
      show X.op.δ j.succ (opObjEquiv.symm (r2 σ₀ (revEmb u))) =
        opObjEquiv.symm (r2 σ₀ (revEmb (delEmb u j)))
      rw [opδ_symm, rev_succ', δ_r2_castSucc σ₀ j.rev, delEmb_revEmb])
    (hg1_succ := fun k hk u j => by
      show X.op.δ j.succ (opObjEquiv.symm (r1 σ₀ (revEmb u))) =
        opObjEquiv.symm (r1 σ₀ (revEmb (delEmb u j)))
      rw [opδ_symm, rev_succ', δ_r1_castSucc σ₀ hk j.rev, delEmb_revEmb])
    (α := opObjEquiv.symm I.invHomId.simplex)
    (β := opObjEquiv.symm I.homInvId.simplex)
    (invE := opObjEquiv.symm I.inv.edge)
    (hα0 := by
      change X.op.δ 0 (opObjEquiv.symm I.invHomId.simplex) =
        opObjEquiv.symm I.inv.edge
      rw [opδ_symm, show (0 : Fin 3).rev = 2 from by decide,
        I.invHomId.d₂])
    (hα1 := by
      change X.op.δ 1 (opObjEquiv.symm I.invHomId.simplex) =
        X.op.σ 0 (X.op.δ 1 (opObjEquiv.symm (r12 σ₀ (revEmb emptyEmb))))
      rw [eq_emptyEmb (revEmb emptyEmb), opδ_symm, opδ_symm, opσ_symm,
        show (1 : Fin 3).rev = 1 from by decide,
        show (1 : Fin 2).rev = 0 from by decide,
        show (0 : Fin 1).rev = 0 from by decide,
        I.invHomId.d₁, Edge.id_edge])
    (hβ0 := by
      change X.op.δ 0 (opObjEquiv.symm I.homInvId.simplex) =
        opObjEquiv.symm (r12 σ₀ (revEmb emptyEmb))
      rw [eq_emptyEmb (revEmb emptyEmb), opδ_symm,
        show (0 : Fin 3).rev = 2 from by decide, I.homInvId.d₂]
      rfl)
    (hβ1 := by
      change X.op.δ 1 (opObjEquiv.symm I.homInvId.simplex) =
        X.op.σ 0 (X.op.δ 0 (opObjEquiv.symm (r12 σ₀ (revEmb emptyEmb))))
      rw [eq_emptyEmb (revEmb emptyEmb), opδ_symm, opδ_symm, opσ_symm,
        show (1 : Fin 3).rev = 1 from by decide,
        show (0 : Fin 2).rev = 1 from by decide,
        show (0 : Fin 1).rev = 0 from by decide,
        I.homInvId.d₁, Edge.id_edge])
    (hβ2 := by
      change X.op.δ 2 (opObjEquiv.symm I.homInvId.simplex) =
        opObjEquiv.symm I.inv.edge
      rw [opδ_symm, show (2 : Fin 3).rev = 0 from by decide,
        I.homInvId.d₀])
    (hinvSrc := by
      change X.op.δ 1 (opObjEquiv.symm I.inv.edge) =
        X.op.δ 0 (opObjEquiv.symm (r12 σ₀ (revEmb emptyEmb)))
      rw [eq_emptyEmb (revEmb emptyEmb), opδ_symm, opδ_symm,
        show (1 : Fin 2).rev = 0 from by decide,
        show (0 : Fin 2).rev = 1 from by decide]
      exact congrArg opObjEquiv.symm I.inv.tgt_eq)
  refine ⟨yonedaEquiv.symm (opObjEquiv σ_op), horn.hom_ext' fun j hj => ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  rcases fin_classifyR (K := n) j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd rfl hj
  · have hface : σ₀.app _ (horn.face (Fin.last (n + 2))
          (Fin.last (n + 1)).castSucc hj) =
        r2 σ₀ ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding) := by
      rw [r2]
      exact congrArg (σ₀.app _)
        (hornSimplexR_eq_face (emb2r
          ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding)) _
          (Fin.last (n + 1)).castSucc hj emb2r_reflEmb).symm
    rw [hface]
    have h2 := congrArg opObjEquiv hσ1
    simp only [] at h2
    rw [opδ_apply, rev_one', Equiv.apply_symm_apply, revEmb_reflEmb] at h2
    exact h2.symm
  · have hface : σ₀.app _ (horn.face (Fin.last (n + 2))
          j'.castSucc.castSucc hj) =
        r12 σ₀ (delEmb ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding)
          j') := by
      rw [r12, dite_eq_left (le_refl n)]
      exact congrArg (σ₀.app _)
        (hornSimplexR_eq_face (emb12r
          (delEmb ((OrderIso.refl (Fin (n + 1))).toOrderEmbedding) j')) _
          j'.castSucc.castSucc hj (emb12r_delEmb_reflEmb j')).symm
    rw [hface]
    have h2 := congrArg opObjEquiv (hσdel j'.rev)
    simp only [] at h2
    rw [opδ_apply, rev_succ_succ', Fin.rev_rev, Equiv.apply_symm_apply,
      ← delEmb_revEmb, Fin.rev_rev, revEmb_reflEmb] at h2
    exact h2.symm

end RightHornTheorem

section SpecialOuterHornFilling

/-- **Joyal's special outer horn filling for every
quasicategory**, in all dimensions: left horns by
`exists_fill_horn_left_of_isEquivalence`, right horns by
`exists_fill_horn_right_of_isEquivalence`. -/
theorem hasSpecialOuterHornFilling_of_quasicategory (X : SSet.{u})
    [Quasicategory X] : HasSpecialOuterHornFilling X :=
  ⟨fun σ₀ hσ => exists_fill_horn_left_of_isEquivalence σ₀ hσ,
    fun σ₀ hσ => exists_fill_horn_right_of_isEquivalence σ₀ hσ⟩

/-- **The core of a quasicategory is a Kan complex**
(unconditional form of
`kanComplex_core_of_special_horn_filling`). -/
theorem kanComplex_core_of_quasicategory (X : SSet.{u})
    [Quasicategory X] : KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_special_horn_filling
    (hasSpecialOuterHornFilling_of_quasicategory X)

/-- The core of a quasicategory is a Kan complex, as an
instance. The priority is strictly below `low`, the priority of
the Kan-specialized instance in `CoreKan.lean`, so that under
`[KanComplex X]` the specialized route is tried first. -/
instance (priority := 90) (X : SSet.{u}) [Quasicategory X] :
    KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_quasicategory X

end SpecialOuterHornFilling

end SSet
