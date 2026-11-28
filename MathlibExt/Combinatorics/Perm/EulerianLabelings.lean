/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianCuts
public import MathlibExt.Data.Sym.SortedTuple

/-!
# Descent labelings and stable sorting fibers

For `σ ∈ S_N`, define the descent prefix `r_i` to be the number of descent positions before
`i`. A descent labeling is nondecreasing and rises strictly at every descent of `σ`.

For positive length `N` and alphabet size `m>d`, subtracting `r_i` from a descent labeling
gives a nondecreasing labeling in `Fin(m-d)`; adding `r_i` gives the inverse. The number of
such labelings is `choose(N+m-1-d,N)`.

The stable-sort fiber `sort f = σ` is equivalent to descent labelings by `f ↦ f ∘ σ`, with
inverse `g ↦ g ∘ σ⁻¹`.

Reference: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 3.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Let `N : ℕ`, `σ ∈ S_N`, and `Des(σ)` be its adjacent descent positions. Put `d = descentNumber
σ` and `r_i = |{j ∈ Des(σ) | j<i}|`. A descent labeling in alphabet `Fin m` is a nondecreasing
`g : Fin N → Fin m` with `g(j)<g(j+1)` at each descent. For `i : Fin N`, `descentPrefix σ i =
r_i` counts descent positions strictly before `i`. -/
def descentPrefix {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : ℕ :=
  ((descentPositions σ).filter (fun j => j.val < i.val)).card

/-- Let `N : ℕ`, `σ ∈ S_N`, and `Des(σ)` be its adjacent descent positions. Put `d = descentNumber
σ` and `r_i = |{j ∈ Des(σ) | j<i}|`. A descent labeling in alphabet `Fin m` is a nondecreasing
`g : Fin N → Fin m` with `g(j)<g(j+1)` at each descent. `DescentLabeling σ m` is the subtype
of labelings with these monotonicity and strict-descent-rise conditions. -/
abbrev DescentLabeling {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :=
  {g : Fin n → Fin m // Monotone g ∧
    ∀ (j : Fin n) (h : j.val + 1 < n),
      j ∈ descentPositions σ → g j < g ⟨j.val + 1, h⟩}

/-- For `n : ℕ` and `σ ∈ S_(n+1)`, `descentPrefix σ 0 = 0` because no descent position precedes
the first position. -/
theorem descentPrefix_zero {n : ℕ} (σ : Perm (Fin (n + 1))) : descentPrefix σ 0 = 0 := by
  simp [descentPrefix]

/-- For `n : ℕ`, `σ ∈ S_(n+1)`, and `i : Fin n`, the prefixes satisfy `r_(i.succ) = r_(i.castSucc)
+ (if i.castSucc ∈ Des(σ) then 1 else 0)`. -/
theorem descentPrefix_succ {n : ℕ} (σ : Perm (Fin (n + 1))) (i : Fin n) :
    descentPrefix σ i.succ = descentPrefix σ i.castSucc +
      if i.castSucc ∈ descentPositions σ then 1 else 0 := by
  classical
  have hnot : i.castSucc ∉ (descentPositions σ).filter (fun j => j.val < i.val) := by
    intro hi
    have hlt := (Finset.mem_filter.mp hi).2
    change i.val < i.val at hlt
    exact (Nat.lt_irrefl _) hlt
  have hf : (descentPositions σ).filter (fun j => j.val < i.val + 1) =
      if i.castSucc ∈ descentPositions σ then
        insert i.castSucc ((descentPositions σ).filter (fun j => j.val < i.val))
      else (descentPositions σ).filter (fun j => j.val < i.val) := by
    apply Finset.ext
    intro j
    by_cases hi : i.castSucc ∈ descentPositions σ
    · rw [ite_eq_left hi]
      constructor
      · intro hj
        obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
        by_cases heq : j = i.castSucc
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · apply Finset.mem_insert.mpr
          apply Or.inr
          apply Finset.mem_filter.mpr
          refine ⟨hj, ?_⟩
          have hne : j.val ≠ i.val := fun h => heq (Fin.ext h)
          omega
      · intro hj
        obtain heq | hj := Finset.mem_insert.mp hj
        · subst j
          apply Finset.mem_filter.mpr
          refine ⟨hi, ?_⟩
          change i.val < i.val + 1
          exact Nat.lt_succ_self _
        · obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨hj, lt_trans hlt (Nat.lt_succ_self _)⟩
    · rw [ite_eq_right hi]
      constructor
      · intro hj
        obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
        apply Finset.mem_filter.mpr
        refine ⟨hj, ?_⟩
        have hne : j.val ≠ i.val := by
          intro he
          have heq : j = i.castSucc := Fin.ext he
          exact hi (heq ▸ hj)
        omega
      · intro hj
        obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hj, lt_trans hlt (Nat.lt_succ_self _)⟩
  simp only [descentPrefix, Fin.val_succ, Fin.val_castSucc]
  rw [hf]
  by_cases hi : i.castSucc ∈ descentPositions σ
  · simp only [ite_eq_left hi, Finset.card_insert_of_notMem hnot]
  · simp only [ite_eq_right hi, Nat.add_zero]

/-- Let `N : ℕ`, `σ ∈ S_N`, and `Des(σ)` be its adjacent descent positions. Put `d = descentNumber
σ` and `r_i = |{j ∈ Des(σ) | j<i}|`. A descent labeling in alphabet `Fin m` is a nondecreasing
`g : Fin N → Fin m` with `g(j)<g(j+1)` at each descent. The natural-number function `i ↦
descentPrefix σ i` is monotone on `Fin N`. -/
theorem descentPrefix_monotone {n : ℕ} (σ : Perm (Fin n)) : Monotone (descentPrefix σ) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, lt_of_lt_of_le hlt hij⟩

/-- For `n : ℕ` and `σ ∈ S_(n+1)`, the prefix before the last position is `descentPrefix σ
(Fin.last n) = descentNumber σ`. -/
theorem descentPrefix_last {n : ℕ} (σ : Perm (Fin (n + 1))) :
    descentPrefix σ (Fin.last n) = descentNumber σ := by
  unfold descentPrefix descentNumber
  congr 1
  apply Finset.filter_eq_self.mpr
  intro j hj
  obtain ⟨h, _⟩ := (Finset.mem_filter.mp hj).2
  simp only [Fin.val_last]
  omega

/-- Let `n,m : ℕ`, `σ ∈ S_(n+1)`, and `g : DescentLabeling σ m`. For every position `i :
Fin(n+1)`, `descentPrefix σ i ≤ (g i).val`. -/
theorem descentPrefix_le_label {n m : ℕ} (σ : Perm (Fin (n + 1)))
    (g : DescentLabeling σ m) (i : Fin (n + 1)) : descentPrefix σ i ≤ (g.val i).val := by
  induction i using Fin.induction with
  | zero => rw [descentPrefix_zero]; exact Nat.zero_le _
  | succ i hi =>
    rw [descentPrefix_succ]
    by_cases hd : i.castSucc ∈ descentPositions σ
    · simp only [ite_eq_left hd]
      have h : (g.val i.castSucc).val < (g.val i.succ).val :=
        g.property.2 i.castSucc (by
          change i.val + 1 < n + 1
          exact i.succ.isLt) hd
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hi h)
    · simp only [ite_eq_right hd, Nat.add_zero]
      have hindex : i.castSucc ≤ i.succ := by
        change i.val ≤ i.val + 1
        exact Nat.le_succ _
      have h : (g.val i.castSucc).val ≤ (g.val i.succ).val := g.property.1 hindex
      exact hi.trans h

/-- Let `n,m : ℕ`, `σ ∈ S_(n+1)`, and `g : DescentLabeling σ m`. The natural-number function `i ↦
(g i).val - descentPrefix σ i` is monotone, with subtraction in `ℕ`. -/
theorem label_sub_descentPrefix_monotone {n m : ℕ} (σ : Perm (Fin (n + 1)))
    (g : DescentLabeling σ m) : Monotone (fun i => (g.val i).val - descentPrefix σ i) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  change (g.val i.castSucc).val - descentPrefix σ i.castSucc ≤
    (g.val i.succ).val - descentPrefix σ i.succ
  have hp := descentPrefix_le_label σ g i.castSucc
  have hq := descentPrefix_le_label σ g i.succ
  have hprefix := descentPrefix_succ σ i
  by_cases hd : i.castSucc ∈ descentPositions σ
  · simp only [ite_eq_left hd] at hprefix
    have hg : (g.val i.castSucc).val < (g.val i.succ).val :=
      g.property.2 i.castSucc (by
        change i.val + 1 < n + 1
        exact i.succ.isLt) hd
    omega
  · simp only [ite_eq_right hd, Nat.add_zero] at hprefix
    have hindex : i.castSucc ≤ i.succ := by
      change i.val ≤ i.val + 1
      exact Nat.le_succ _
    have hg : (g.val i.castSucc).val ≤ (g.val i.succ).val := g.property.1 hindex
    omega

/-- For `n,m : ℕ`, `σ ∈ S_(n+1)`, and any `g : DescentLabeling σ m`, `descentNumber σ < m`. The
positive word length forces room for every required strict rise. -/
theorem descentNumber_lt_labelAlphabet {n m : ℕ} (σ : Perm (Fin (n + 1)))
    (g : DescentLabeling σ m) : descentNumber σ < m := by
  have h := descentPrefix_le_label σ g (Fin.last n)
  rw [descentPrefix_last] at h
  exact h.trans_lt (g.val (Fin.last n)).isLt

/-- Let `n,m : ℕ`, `σ ∈ S_(n+1)`, and `d = descentNumber σ < m`. There is an equivalence
`DescentLabeling σ m ≃ {h : Fin(n+1) → Fin(m-d) // Monotone h}`. It sends `g_i` to the finite
index with value `g_i.val - descentPrefix σ i`; its inverse adds the same prefix. -/
def descentLabelingEquivMonotone {n : ℕ} (σ : Perm (Fin (n + 1))) (m : ℕ)
    (hm : descentNumber σ < m) :
    DescentLabeling σ m ≃ {g : Fin (n + 1) → Fin (m - descentNumber σ) // Monotone g} where
  toFun g :=
    ⟨fun i => ⟨(g.val i).val - descentPrefix σ i, by
      have hmono := label_sub_descentPrefix_monotone σ g
      have hbound : (g.val i).val - descentPrefix σ i ≤
          (g.val (Fin.last n)).val - descentPrefix σ (Fin.last n) := hmono (Fin.le_last i)
      rw [descentPrefix_last] at hbound
      have hlast := (g.val (Fin.last n)).isLt
      omega⟩, fun _ _ hij => label_sub_descentPrefix_monotone σ g hij⟩
  invFun g :=
    ⟨fun i => ⟨(g.val i).val + descentPrefix σ i, by
      have hmono : (g.val i).val ≤ (g.val (Fin.last n)).val := g.property (Fin.le_last i)
      have hlast := (g.val (Fin.last n)).isLt
      have hp := descentPrefix_monotone σ (Fin.le_last i)
      rw [descentPrefix_last] at hp
      omega⟩, by
        constructor
        · intro i j hij
          change (g.val i).val + descentPrefix σ i ≤ (g.val j).val + descentPrefix σ j
          exact Nat.add_le_add (g.property hij) (descentPrefix_monotone σ hij)
        · intro j hj hd
          let i : Fin n := ⟨j.val, by omega⟩
          have heq : i.castSucc = j := by apply Fin.ext; rfl
          have heq' : i.succ = (⟨j.val + 1, hj⟩ : Fin (n + 1)) := by apply Fin.ext; rfl
          have hp := descentPrefix_succ σ i
          rw [heq, heq', ite_eq_left hd] at hp
          have hmono := g.property (show j ≤ ⟨j.val + 1, hj⟩ by change j.val ≤ j.val + 1; omega)
          change (g.val j).val + descentPrefix σ j <
            (g.val ⟨j.val + 1, hj⟩).val + descentPrefix σ ⟨j.val + 1, hj⟩
          change (g.val j).val ≤ (g.val ⟨j.val + 1, hj⟩).val at hmono
          omega⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (g.val i).val - descentPrefix σ i + descentPrefix σ i = (g.val i).val
    exact Nat.sub_add_cancel (descentPrefix_le_label σ g i)
  right_inv g := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (g.val i).val + descentPrefix σ i - descentPrefix σ i = (g.val i).val
    exact Nat.add_sub_cancel _ _

/-- For `n,m : ℕ` and `σ ∈ S_(n+1)`, writing `d = descentNumber σ`, `Fintype.card (DescentLabeling
σ m) = Nat.choose (n+m-d) (n+1)`. This includes the empty-labeling cases when the alphabet has
too few labels. -/
theorem card_descentLabeling {n : ℕ} (σ : Perm (Fin (n + 1))) (m : ℕ) :
    Fintype.card (DescentLabeling σ m) = (n + m - descentNumber σ).choose (n + 1) := by
  classical
  by_cases hm : descentNumber σ < m
  · rw [Fintype.card_congr (descentLabelingEquivMonotone σ m hm), Sym.card_monotone_fin]
    congr 1
    omega
  · let : IsEmpty (DescentLabeling σ m) :=
      ⟨fun g => hm (descentNumber_lt_labelAlphabet σ g)⟩
    rw [Fintype.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]

/-- For `n,m : ℕ` and `σ ∈ S_n`, the fiber `{f : Fin n → Fin m // Tuple.sort f = σ}` is equivalent
to `DescentLabeling σ m`. The forward map is `f ↦ f ∘ σ`; the inverse is `g ↦ g ∘ σ⁻¹`. This
includes `n=0`. -/
def sortFiberEquivDescentLabeling {n m : ℕ} (σ : Perm (Fin n)) :
    {f : Fin n → Fin m // Tuple.sort f = σ} ≃ DescentLabeling σ m where
  toFun f :=
    ⟨f.val ∘ σ, by
      obtain ⟨hmono, htie⟩ := (Tuple.eq_sort_iff).mp f.property.symm
      refine ⟨hmono, ?_⟩
      intro j hj hd
      have hle := hmono (show j ≤ ⟨j.val + 1, hj⟩ by change j.val ≤ j.val + 1; omega)
      apply lt_of_le_of_ne hle
      intro heq
      have hindex := htie (i := j) (j := ⟨j.val + 1, hj⟩)
        (by change j.val ≤ j.val + 1; omega) heq
      obtain ⟨h, hdesc⟩ := (Finset.mem_filter.mp hd).2
      exact (not_le_of_gt hdesc) hindex⟩
  invFun g :=
    ⟨g.val ∘ σ.symm, by
      apply Eq.symm
      apply Tuple.eq_sort_iff'.mpr
      cases n with
      | zero =>
        intro i
        exact Fin.elim0 i
      | succ n =>
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        simp only [Equiv.trans_apply]
        change (Tuple.graphEquiv₁ (g.val ∘ σ.symm) (σ i.castSucc)).val <
          (Tuple.graphEquiv₁ (g.val ∘ σ.symm) (σ i.succ)).val
        have hgraph (x : Fin (n + 1)) :
            (Tuple.graphEquiv₁ (g.val ∘ σ.symm) (σ x)).val = toLex (g.val x, σ x) := by
          change toLex (g.val (σ.symm (σ x)), σ x) = toLex (g.val x, σ x)
          rw [Equiv.symm_apply_apply]
        rw [hgraph, hgraph]
        apply Prod.Lex.toLex_lt_toLex.mpr
        have hindex : i.castSucc ≤ i.succ := by
          change i.val ≤ i.val + 1
          exact Nat.le_succ _
        obtain hlt | heq := (g.property.1 hindex).lt_or_eq
        · exact Or.inl hlt
        · refine Or.inr ⟨heq, ?_⟩
          have hne : σ i.castSucc ≠ σ i.succ := by
            intro he
            have h := congrArg Fin.val (σ.injective he)
            change i.val = i.val + 1 at h
            omega
          apply lt_of_le_of_ne (le_of_not_gt ?_) hne
          intro hdesc
          have hd : i.castSucc ∈ descentPositions σ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨by
              change i.val + 1 < n + 1
              exact i.succ.isLt, hdesc⟩⟩
          have h : g.val i.castSucc < g.val i.succ := g.property.2 i.castSucc (by
            change i.val + 1 < n + 1
            exact i.succ.isLt) hd
          exact (ne_of_lt (a := g.val i.castSucc) (b := g.val i.succ) h) heq⟩
  left_inv f := by apply Subtype.ext; funext i; exact congrArg f.val (σ.apply_symm_apply i)
  right_inv g := by
    apply Subtype.ext
    change (g.val ∘ σ.symm) ∘ σ = g.val
    funext i
    exact congrArg g.val (σ.symm_apply_apply i)

/-- For `n,m : ℕ` and `σ ∈ S_(n+1)`, `Fintype.card {f : Fin(n+1) → Fin m // Tuple.sort f = σ} =
Nat.choose (n+m-descentNumber σ) (n+1)`. -/
theorem card_sortFiber {n : ℕ} (σ : Perm (Fin (n + 1))) (m : ℕ) :
    Fintype.card {f : Fin (n + 1) → Fin m // Tuple.sort f = σ} =
      (n + m - descentNumber σ).choose (n + 1) := by
  rw [Fintype.card_congr (sortFiberEquivDescentLabeling σ), card_descentLabeling]

end Equiv.Perm
