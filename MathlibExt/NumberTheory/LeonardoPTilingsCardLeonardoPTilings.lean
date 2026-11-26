/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.LeonardoP
public import MathlibExt.NumberTheory.LeonardoPTilings
import Mathlib.Data.Set.Card

/-!
# Counting Leonardo `p`-tilings

The number of tilings in the Leonardo `p`-tiling set `K_{p,n}` equals the Leonardo
`p`-number `𝓛_{p,n}`. Splitting the tilings by their last piece shows both sides satisfy
the same recurrence (`card_leonardoPTilings`).

Statements from Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo
`p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57
(<https://math.colgate.edu/~integers/z57/z57.pdf>).
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.LeonardoPWanted

-- Membership in the tiling set, unfolded.
private theorem mem_leonardoPTilings {p n : ℕ} {o : Option (Fin p × ℕ)} {bs : List Bool} :
    (o, bs) ∈ leonardoPTilings p n ↔
      (∀ c l, o = some (c, l) → p + 1 ≤ l) ∧
        o.elim 0 Prod.snd + (bs.map fun b => if b then p + 1 else 1).sum = n := by
  simp only [leonardoPTilings, Set.mem_ofPred_eq]

-- Appending a square adds `1` to the tail weight.
private theorem map_sum_append_false (p : ℕ) (bs : List Bool) :
    ((bs ++ [false]).map fun b => if b then p + 1 else 1).sum =
      (bs.map fun b => if b then p + 1 else 1).sum + 1 := by
  simp

-- Appending a `p`-mino adds `p + 1` to the tail weight.
private theorem map_sum_append_true (p : ℕ) (bs : List Bool) :
    ((bs ++ [true]).map fun b => if b then p + 1 else 1).sum =
      (bs.map fun b => if b then p + 1 else 1).sum + (p + 1) := by
  simp

-- A tail of weight `0` is empty.
private theorem eq_nil_of_map_sum_eq_zero (p : ℕ) (bs : List Bool)
    (h : (bs.map fun b => if b then p + 1 else 1).sum = 0) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      cases b <;> simp_all

-- Appending a final square to a tiling.
private def appendSquare {p : ℕ} :
    Option (Fin p × ℕ) × List Bool → Option (Fin p × ℕ) × List Bool
  | (o, bs) => (o, bs ++ [false])

private theorem appendSquare_injective (p : ℕ) :
    Function.Injective (@appendSquare p) := by
  intro t t' h
  obtain ⟨o, bs⟩ := t
  obtain ⟨o', bs'⟩ := t'
  simp only [appendSquare, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  exact Prod.ext h1 (List.append_left_injective [false] h2)

-- Appending a final `p`-mino to a tiling.
private def appendMino {p : ℕ} :
    Option (Fin p × ℕ) × List Bool → Option (Fin p × ℕ) × List Bool
  | (o, bs) => (o, bs ++ [true])

private theorem appendMino_injective (p : ℕ) :
    Function.Injective (@appendMino p) := by
  intro t t' h
  obtain ⟨o, bs⟩ := t
  obtain ⟨o', bs'⟩ := t'
  simp only [appendMino, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  exact Prod.ext h1 (List.append_left_injective [true] h2)

-- Distinct colors give distinct lone `p`-tiles.
private theorem injective_tileConst (p n : ℕ) :
    Function.Injective (fun c : Fin p => (some (c, n + 1), ([] : List Bool))) := by
  intro c c' hcc
  simp_all

-- Tilings whose last piece is a square.
private def tiltA (p n : ℕ) : Set (Option (Fin p × ℕ) × List Bool) :=
  {t | t ∈ leonardoPTilings p n ∧ ∃ bs, t.2 = bs ++ [false]}

-- Tilings whose last piece is a `p`-mino.
private def tiltB (p n : ℕ) : Set (Option (Fin p × ℕ) × List Bool) :=
  {t | t ∈ leonardoPTilings p n ∧ ∃ bs, t.2 = bs ++ [true]}

-- Tilings with no tail pieces.
private def tiltC (p n : ℕ) : Set (Option (Fin p × ℕ) × List Bool) :=
  {t | t ∈ leonardoPTilings p n ∧ t.2 = []}

-- Every tiling ends in a square, a `p`-mino, or nothing.
private theorem union_tiltABC (p n : ℕ) :
    leonardoPTilings p n = tiltA p n ∪ tiltB p n ∪ tiltC p n := by
  ext t
  simp only [tiltA, tiltB, tiltC, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro ht
    rcases List.eq_nil_or_concat' t.2 with h | ⟨bs, b, h⟩
    · exact Or.inr ⟨ht, h⟩
    · cases b
      · exact Or.inl (Or.inl ⟨ht, bs, h⟩)
      · exact Or.inl (Or.inr ⟨ht, bs, h⟩)
  · rintro ((⟨ht, -⟩ | ⟨ht, -⟩) | ⟨ht, -⟩) <;> exact ht

private theorem disjoint_tiltAB (p n : ℕ) : Disjoint (tiltA p n) (tiltB p n) := by
  rw [Set.disjoint_left]
  intro t hA hBmem
  obtain ⟨-, bs, hbs⟩ := hA
  obtain ⟨-, bs', hbs'⟩ := hBmem
  have h : bs ++ [false] = bs' ++ [true] := by rw [← hbs, hbs']
  simp at h

private theorem disjoint_tiltAC (p n : ℕ) : Disjoint (tiltA p n) (tiltC p n) := by
  rw [Set.disjoint_left]
  intro t hA hCmem
  obtain ⟨-, bs, hbs⟩ := hA
  obtain ⟨-, hnil⟩ := hCmem
  have h : bs ++ [false] = ([] : List Bool) := by rw [← hbs, hnil]
  have hlen := congrArg List.length h
  simp at hlen

private theorem disjoint_tiltBC (p n : ℕ) : Disjoint (tiltB p n) (tiltC p n) := by
  rw [Set.disjoint_left]
  intro t hB hCmem
  obtain ⟨-, bs, hbs⟩ := hB
  obtain ⟨-, hnil⟩ := hCmem
  have h : bs ++ [true] = ([] : List Bool) := by rw [← hbs, hnil]
  have hlen := congrArg List.length h
  simp at hlen

-- Tilings ending in a square are tilings of `n` with a square appended.
private theorem tiltA_eq_image (p n : ℕ) :
    tiltA p (n + 1) = appendSquare '' leonardoPTilings p n := by
  ext ⟨o, bs'⟩
  simp only [Set.mem_image]
  constructor
  · intro hmem
    simp only [tiltA, Set.mem_ofPred_eq] at hmem
    obtain ⟨ht, bs, hbs⟩ := hmem
    refine ⟨(o, bs), ?_, ?_⟩
    · rw [mem_leonardoPTilings] at ht ⊢
      obtain ⟨htile, hsum⟩ := ht
      refine ⟨htile, ?_⟩
      rw [hbs, map_sum_append_false] at hsum
      omega
    · exact Prod.ext rfl hbs.symm
  · rintro ⟨t', ht', heq⟩
    obtain ⟨o', bs⟩ := t'
    rw [← heq]
    simp only [appendSquare, tiltA, Set.mem_ofPred_eq]
    refine ⟨?_, bs, rfl⟩
    rw [mem_leonardoPTilings] at ht' ⊢
    obtain ⟨htile, hsum⟩ := ht'
    refine ⟨htile, ?_⟩
    rw [map_sum_append_false]
    omega

-- Tilings ending in a `p`-mino are tilings of `n + 1 - p - 1` with a mino appended.
private theorem tiltB_eq_image (p n : ℕ) (h : p + 1 ≤ n + 1) :
    tiltB p (n + 1) = appendMino '' leonardoPTilings p (n + 1 - p - 1) := by
  ext ⟨o, bs'⟩
  simp only [Set.mem_image]
  constructor
  · intro hmem
    simp only [tiltB, Set.mem_ofPred_eq] at hmem
    obtain ⟨ht, bs, hbs⟩ := hmem
    refine ⟨(o, bs), ?_, ?_⟩
    · rw [mem_leonardoPTilings] at ht ⊢
      obtain ⟨htile, hsum⟩ := ht
      refine ⟨htile, ?_⟩
      rw [hbs, map_sum_append_true] at hsum
      omega
    · exact Prod.ext rfl hbs.symm
  · rintro ⟨t', ht', heq⟩
    obtain ⟨o', bs⟩ := t'
    rw [← heq]
    simp only [appendMino, tiltB, Set.mem_ofPred_eq]
    refine ⟨?_, bs, rfl⟩
    rw [mem_leonardoPTilings] at ht' ⊢
    obtain ⟨htile, hsum⟩ := ht'
    refine ⟨htile, ?_⟩
    rw [map_sum_append_true]
    omega

-- No tiling of a short board ends in a `p`-mino.
private theorem tiltB_eq_empty (p n : ℕ) (h : ¬ p + 1 ≤ n + 1) :
    tiltB p (n + 1) = ∅ := by
  ext ⟨o, bs'⟩
  simp only [tiltB, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ht, bs, hbs⟩
  rw [mem_leonardoPTilings] at ht
  obtain ⟨-, hsum⟩ := ht
  rw [hbs, map_sum_append_true] at hsum
  omega

-- Tailless tilings of a long board are lone `p`-tiles, one per color.
private theorem tiltC_eq_image (p n : ℕ) (h : p + 1 ≤ n + 1) :
    tiltC p (n + 1) =
      (fun c : Fin p => (some (c, n + 1), ([] : List Bool))) '' Set.univ := by
  ext ⟨o, bs'⟩
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · intro hmem
    simp only [tiltC, Set.mem_ofPred_eq] at hmem
    obtain ⟨ht, hbs⟩ := hmem
    rw [mem_leonardoPTilings] at ht
    obtain ⟨htile, hsum⟩ := ht
    subst hbs
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hsum
    cases o with
    | none =>
        have h0 : Option.elim (none : Option (Fin p × ℕ)) 0 Prod.snd = 0 := rfl
        omega
    | some x =>
        have hx : x.2 = n + 1 := hsum
        refine ⟨x.1, ?_⟩
        have hxpair : (x.1, n + 1) = x := Prod.ext rfl hx.symm
        rw [hxpair]
  · rintro ⟨c', heq⟩
    rw [← heq]
    simp only [tiltC, Set.mem_ofPred_eq]
    refine ⟨?_, trivial⟩
    rw [mem_leonardoPTilings]
    refine ⟨?_, ?_⟩
    · intro c l hcon
      simp at hcon
      omega
    · rfl

-- No tailless tiling of a short positive board exists.
private theorem tiltC_eq_empty (p n : ℕ) (h : ¬ p + 1 ≤ n + 1) :
    tiltC p (n + 1) = ∅ := by
  ext ⟨o, bs'⟩
  simp only [tiltC, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ht, hbs⟩
  rw [mem_leonardoPTilings] at ht
  obtain ⟨htile, hsum⟩ := ht
  subst hbs
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hsum
  cases o with
  | none =>
      have h0 : Option.elim (none : Option (Fin p × ℕ)) 0 Prod.snd = 0 := rfl
      omega
  | some x =>
      have hx : x.2 = n + 1 := hsum
      have hle := htile x.1 x.2 rfl
      omega

-- The `0`-board has only the empty tiling.
private theorem leonardoPTilings_zero (p : ℕ) :
    leonardoPTilings p 0 = {(none, [])} := by
  ext ⟨o, bs⟩
  simp only [leonardoPTilings, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨htile, hsum⟩
    have h1 : o.elim 0 Prod.snd = 0 := by omega
    have h2 : (bs.map fun b => if b then p + 1 else 1).sum = 0 := by omega
    have hbs : bs = [] := eq_nil_of_map_sum_eq_zero p bs h2
    subst hbs
    cases o with
    | none => exact ⟨rfl, rfl⟩
    | some x =>
        have hx : x.2 = 0 := h1
        have hle := htile x.1 x.2 rfl
        omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · intro c l hcon
      simp at hcon
    · rfl

-- The generalized Leonardo recurrence at `n + 1` for `n + 1 > p`.
private theorem leonardoPK_succ_of_gt (p k n : ℕ) (h : p < n + 1) :
    leonardoPK p k (n + 1) =
      leonardoPK p k n + leonardoPK p k (n + 1 - p - 1) + (k : ℤ) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = p + i := ⟨n - p, by omega⟩
  have hi : p + i + 1 - p - 1 = i := by omega
  rw [hi]
  exact leonardoPK_recurrence p k i

private theorem finite_tiltA_of (p n : ℕ)
    (hfin : (leonardoPTilings p n).Finite) : (tiltA p (n + 1)).Finite := by
  rw [tiltA_eq_image p n]
  exact hfin.image _

private theorem finite_tiltB_of (p n : ℕ)
    (hfin : (leonardoPTilings p (n + 1 - p - 1)).Finite) :
    (tiltB p (n + 1)).Finite := by
  by_cases h : p + 1 ≤ n + 1
  · rw [tiltB_eq_image p n h]
    exact hfin.image _
  · rw [tiltB_eq_empty p n h]
    exact Set.finite_empty

private theorem finite_tiltC (p n : ℕ) : (tiltC p (n + 1)).Finite := by
  by_cases h : p + 1 ≤ n + 1
  · rw [tiltC_eq_image p n h]
    exact Set.finite_univ.image _
  · rw [tiltC_eq_empty p n h]
    exact Set.finite_empty

-- Every tiling set is finite.
private theorem finite_leonardoPTilings (p n : ℕ) :
    (leonardoPTilings p n).Finite := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [leonardoPTilings_zero p]
          exact Set.finite_singleton _
      | succ n =>
          rw [union_tiltABC p (n + 1)]
          exact ((finite_tiltA_of p n (ih n (by omega))).union
            (finite_tiltB_of p n (ih (n + 1 - p - 1) (by omega)))).union
            (finite_tiltC p n)

-- The tiling count satisfies the Leonardo `p`-recurrence.
private theorem ncard_eq_leonardoPK (p n : ℕ) :
    ((leonardoPTilings p n).ncard : ℤ) = leonardoPK p p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [leonardoPTilings_zero p, Set.ncard_singleton,
            leonardoPK_of_le p p 0 (Nat.zero_le p), Nat.cast_one]
      | succ n =>
          have hunion : (leonardoPTilings p (n + 1)).ncard =
              (tiltA p (n + 1)).ncard + (tiltB p (n + 1)).ncard +
                (tiltC p (n + 1)).ncard := by
            have d1 : Disjoint (tiltA p (n + 1) ∪ tiltB p (n + 1))
                (tiltC p (n + 1)) :=
              Set.disjoint_union_left.mpr
                ⟨disjoint_tiltAC p (n + 1), disjoint_tiltBC p (n + 1)⟩
            have d2 : Disjoint (tiltA p (n + 1)) (tiltB p (n + 1)) :=
              disjoint_tiltAB p (n + 1)
            have fA := finite_tiltA_of p n (finite_leonardoPTilings p n)
            have fB := finite_tiltB_of p n
              (finite_leonardoPTilings p (n + 1 - p - 1))
            have fC := finite_tiltC p n
            rw [union_tiltABC, Set.ncard_union_eq d1 (fA.union fB) fC,
              Set.ncard_union_eq d2 fA fB]
          have eA : (tiltA p (n + 1)).ncard =
              (leonardoPTilings p n).ncard := by
            rw [tiltA_eq_image]
            exact Set.ncard_image_of_injective _ (appendSquare_injective p)
          by_cases h : p + 1 ≤ n + 1
          · have eB : (tiltB p (n + 1)).ncard =
                (leonardoPTilings p (n + 1 - p - 1)).ncard := by
              rw [tiltB_eq_image p n h]
              exact Set.ncard_image_of_injective _ (appendMino_injective p)
            have eC : (tiltC p (n + 1)).ncard = p := by
              rw [tiltC_eq_image p n h]
              rw [Set.ncard_image_of_injective _ (injective_tileConst p n),
                Set.ncard_univ, Nat.card_fin]
            have hcard : (leonardoPTilings p (n + 1)).ncard =
                (leonardoPTilings p n).ncard +
                  (leonardoPTilings p (n + 1 - p - 1)).ncard + p := by
              rw [hunion, eA, eB, eC]
            have hrec := leonardoPK_succ_of_gt p p n (by omega : p < n + 1)
            rw [hcard, Nat.cast_add, Nat.cast_add, ih n (by omega : n < n + 1),
              ih (n + 1 - p - 1) (by omega : n + 1 - p - 1 < n + 1), hrec]
          · have eB : (tiltB p (n + 1)).ncard = 0 := by
              rw [tiltB_eq_empty p n h, Set.ncard_empty]
            have eC : (tiltC p (n + 1)).ncard = 0 := by
              rw [tiltC_eq_empty p n h, Set.ncard_empty]
            have hcard : (leonardoPTilings p (n + 1)).ncard =
                (leonardoPTilings p n).ncard := by
              rw [hunion, eA, eB, eC, add_zero, add_zero]
            rw [hcard, ih n (by omega : n < n + 1),
              leonardoPK_of_le p p n (by omega : n ≤ p),
              leonardoPK_of_le p p (n + 1) (by omega : n + 1 ≤ p)]

-- The statement retains the positivity hypothesis from the source.
set_option linter.unusedVariables false in
/-- **Counting Leonardo $p$-tilings.** For all natural numbers $p \ge 1$ and $n$, let $K_{p,n}$ be
the set of linear tilings of an $n$-board by squares (length $1$), $p$-minos (length $p + 1$) and
at most one $p$-tile, which comes in one of $p$ colors, has length at least $p + 1$ and can only
be the initial piece. Then the number of tilings in $K_{p,n}$ equals the Leonardo $p$-number
$\mathcal{L}_{p,n}$, the generalized Leonardo $p$-number $\mathcal{L}_{p,k}(n)$ at $k = p$:
$\mathcal{L}_{p,n} = 1$ for $n \le p$ and
$\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 1. -/
public theorem card_leonardoPTilings (p n : ℕ) (hp : 1 ≤ p) :
    (Nat.card (leonardoPTilings p n) : ℤ) = leonardoPK p p n := by
  rw [Nat.card_coe_set_eq]
  exact ncard_eq_leonardoPK p n

end

end MetaMathlibExt
