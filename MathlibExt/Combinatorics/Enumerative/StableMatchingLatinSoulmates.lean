/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.GroupTheory.Perm.Fin

/-!
# Counting Latin stable-matching profiles by soulmate pairs

The first column of a Latin men's profile assigns each woman exactly one man who ranks her
first. A soulmate pair occurs exactly when she also ranks that man first. After choosing the
set of women who do so, the other first choices and the tails of all women's lists are independent.
-/

set_option autoImplicit false

namespace MetaMathlibExt.StableMatchingSequences

open Finset Nat

private abbrev Rows (n : ℕ) := Fin n → Equiv.Perm (Fin n)

private abbrev LatinRows (n : ℕ) :=
  {M : Rows n // ∀ r : Fin n, Function.Injective fun i => M i r}

private noncomputable def firstColumn {n : ℕ} (M : LatinRows (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun i => M.1 i 0) (Finite.injective_iff_bijective.mp (M.2 0))

private theorem rank_zero_iff {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1)) :
    (σ.symm x : ℕ) = 0 ↔ x = σ 0 := by
  rw [Fin.val_eq_zero_iff, Equiv.symm_apply_eq]

private theorem isSoulmatePair_iff {n : ℕ} (M : LatinRows (n + 1)) (W : Rows (n + 1))
    (i j : Fin (n + 1)) :
    IsSoulmatePair (M.1, W) i j ↔ (firstColumn M).symm j = i ∧ W j 0 = i := by
  simp only [IsSoulmatePair, manRank, womanRank, rank_zero_iff]
  rw [Equiv.symm_apply_eq]
  exact and_congr Iff.rfl eq_comm

private def matchingWomen {n : ℕ} (d f : Fin (n + 1) → Fin (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter fun j => f j = d j

private theorem soulmatePairCount_eq_card {n : ℕ} (M : LatinRows (n + 1)) (W : Rows (n + 1)) :
    soulmatePairCount (M.1, W) = (matchingWomen (firstColumn M).symm (fun j => W j 0)).card := by
  let s := matchingWomen (firstColumn M).symm (fun j => W j 0)
  have mem (j : Fin (n + 1)) : j ∈ s ↔ W j 0 = (firstColumn M).symm j := by
    simp [s, matchingWomen]
  let e : {ij : Fin (n + 1) × Fin (n + 1) // IsSoulmatePair (M.1, W) ij.1 ij.2} ≃ ↥s :=
    { toFun := fun ⟨⟨i, j⟩, h⟩ =>
        let h' := (isSoulmatePair_iff M W i j).mp h
        ⟨j, (mem j).mpr (h'.2.trans h'.1.symm)⟩
      invFun := fun ⟨j, hj⟩ =>
        ⟨((firstColumn M).symm j, j), (isSoulmatePair_iff M W _ _).mpr ⟨rfl, (mem j).mp hj⟩⟩
      left_inv := fun ⟨⟨i, j⟩, h⟩ =>
        Subtype.ext (Prod.ext ((isSoulmatePair_iff M W i j).mp h).1 rfl)
      right_inv := fun _ => rfl }
  rw [soulmatePairCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

-- First choices split into fibers indexed by the set of matching women.
private def firstChoicesEquiv {n : ℕ} (d : Fin (n + 1) → Fin (n + 1)) (k : ℕ) :
    {f // (matchingWomen d f).card = k} ≃
      Σ s : {s : Finset (Fin (n + 1)) // s.card = k},
        {f : Fin (n + 1) → Fin (n + 1) // ∀ j, f j = d j ↔ j ∈ s.1} where
  toFun f := ⟨⟨matchingWomen d f.1, f.2⟩, f.1, fun j => by simp [matchingWomen]⟩
  invFun x := ⟨x.2.1, by
    have hs : matchingWomen d x.2.1 = x.1.1 := by
      ext j
      simpa [matchingWomen] using x.2.2 j
    rw [hs, x.1.2]⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨s, hs⟩, f, hf⟩
    have h : matchingWomen d f = s := by
      ext j
      simpa [matchingWomen] using hf j
    subst s
    rfl

private theorem firstChoicesFiber_card {n : ℕ} (d : Fin (n + 1) → Fin (n + 1))
    (s : Finset (Fin (n + 1))) :
    Nat.card {f : Fin (n + 1) → Fin (n + 1) // ∀ j, f j = d j ↔ j ∈ s} =
      n ^ (n + 1 - s.card) := by
  classical
  let e := Equiv.subtypePiEquivPi (p := fun j (a : Fin (n + 1)) => a = d j ↔ j ∈ s)
  have h (j : Fin (n + 1)) : Fintype.card {a : Fin (n + 1) // a = d j ↔ j ∈ s} =
      if j ∈ s then 1 else n := by
    by_cases hj : j ∈ s
    · rw [ite_eq_left hj]
      let e : {a : Fin (n + 1) // a = d j ↔ j ∈ s} ≃ {a // a = d j} :=
        Equiv.subtypeEquivRight fun a => by simp [hj]
      rw [Fintype.card_congr e, Fintype.card_subtype_eq]
    · rw [ite_eq_right hj]
      let e : {a : Fin (n + 1) // a = d j ↔ j ∈ s} ≃ {a // a ≠ d j} :=
        Equiv.subtypeEquivRight fun a => by simp [hj]
      rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun a => a = d j)]
      simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [h, prod_ite, prod_const, one_pow, one_mul, ← compl_filter]
  rw [show univ.filter (· ∈ s) = s by ext; simp, card_compl, Fintype.card_fin]

private theorem firstChoices_card {n : ℕ} (d : Fin (n + 1) → Fin (n + 1)) (k : ℕ) :
    Nat.card {f // (matchingWomen d f).card = k} = (n + 1).choose k * n ^ (n + 1 - k) := by
  classical
  have fiber (s : {s : Finset (Fin (n + 1)) // s.card = k}) :
      Nat.card {f : Fin (n + 1) → Fin (n + 1) // ∀ j, f j = d j ↔ j ∈ s.1} =
        n ^ (n + 1 - k) := by
    rw [firstChoicesFiber_card, s.2]
  rw [Nat.card_congr (firstChoicesEquiv d k), Nat.card_sigma]
  simp only [fiber, sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]

private noncomputable def womenRowsEquiv (n : ℕ) :
    Rows (n + 1) ≃ (Fin (n + 1) → Fin (n + 1)) × (Fin (n + 1) → Equiv.Perm (Fin n)) :=
  (Equiv.piCongrRight fun _ => Equiv.Perm.decomposeFin).trans (Equiv.arrowProdEquivProdArrow ..)

private theorem womenRowsEquiv_fst {n : ℕ} (W : Rows (n + 1)) (j : Fin (n + 1)) :
    (womenRowsEquiv n W).1 j = W j 0 := by
  have h := Equiv.Perm.decomposeFin_symm_apply_zero
    (Equiv.Perm.decomposeFin (W j)).1 (Equiv.Perm.decomposeFin (W j)).2
  rw [Prod.eta, Equiv.symm_apply_apply] at h
  exact h.symm

private theorem womenRows_card {n : ℕ} (M : LatinRows (n + 1)) (k : ℕ) :
    Nat.card {W : Rows (n + 1) // soulmatePairCount (M.1, W) = k} =
      (n + 1).choose k * n ^ (n + 1 - k) * n.factorial ^ (n + 1) := by
  let d := (firstColumn M).symm
  let e := (womenRowsEquiv n).subtypeEquiv
    (p := fun W => soulmatePairCount (M.1, W) = k)
    (q := fun x => (matchingWomen d x.1).card = k ∧ True) (fun W => by
      simp only [and_true, d, soulmatePairCount_eq_card, funext (womenRowsEquiv_fst W)])
  let split := Equiv.subtypeProdEquivProd
    (p := fun f => (matchingWomen d f).card = k)
    (q := fun _ : Fin (n + 1) → Equiv.Perm (Fin n) => True)
  rw [Nat.card_congr (e.trans split), Nat.card_prod,
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), firstChoices_card, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

private def profilesEquiv (n k : ℕ) :
    {P : PreferenceProfile n //
      (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = k} ≃
      Σ M : LatinRows n, {W : Rows n // soulmatePairCount (M.1, W) = k} where
  toFun P := ⟨⟨P.1.1, P.2.1⟩, P.1.2, P.2.2⟩
  invFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Profiles with Latin-square men's preferences, counted by soulmate pairs.** For all
$n, k \in \mathbb{N}$, the number of preference profiles of $n$ men and $n$ women in which, for
every position $r$, different men rank different women at position $r$ (the men's rankings form
a Latin square), and which have exactly $k$ soulmate pairs, is
$$L_n \binom{n}{k} (n-1)^{n-k} ((n-1)!)^n,$$
where $L_n$ is the number of Latin squares of order $n$.

Here $n - 1$ and $n - k$ are truncated subtractions in $\mathbb{N}$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 8
(`jis-2024-24.2.2-thm-8`). -/
public theorem men_latin_soulmate_profiles_card (n k : ℕ) :
    Nat.card {P : PreferenceProfile n //
        (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = k} =
      latinSquareCount n * n.choose k * (n - 1) ^ (n - k) * ((n - 1)!) ^ n := by
  classical
  by_cases hk : n < k
  · have : IsEmpty {P : PreferenceProfile n //
          (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = k} :=
      ⟨fun P => (not_le_of_gt hk) (P.2.2 ▸ soulmatePairCount_le P.1)⟩
    simp [Nat.choose_eq_zero_of_lt hk]
  cases n with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp only [latinSquareCount_zero, Nat.choose_zero_right, Nat.sub_zero, Nat.pow_zero,
      Nat.mul_one]
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (Prod.ext (funext fun i => i.elim0)
      (funext fun j => j.elim0))⟩, ?_⟩
    let P : PreferenceProfile 0 := (fun i => i.elim0, fun j => j.elim0)
    exact ⟨⟨P, fun r => r.elim0, Nat.eq_zero_of_le_zero (soulmatePairCount_le P)⟩⟩
  | succ n =>
    let : Fintype (LatinRows (n + 1)) := Fintype.ofFinite _
    rw [Nat.card_congr (profilesEquiv _ _), Nat.card_sigma]
    simp only [womenRows_card, sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.add_sub_cancel]
    change latinSquareCount (n + 1) * _ = _
    simp only [Nat.mul_assoc]

end MetaMathlibExt.StableMatchingSequences
