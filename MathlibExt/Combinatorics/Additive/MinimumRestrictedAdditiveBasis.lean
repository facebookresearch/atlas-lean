/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

public section

namespace MetaMathlibExt

private theorem mrab_exists_of_even (s : Nat) (hs : Even s) :
    ∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  obtain ⟨r, rfl⟩ := hs
  refine ⟨Finset.range (r + 1), ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_range] at ha
    omega
  · intro x hx
    refine ⟨min x r, Finset.mem_range.mpr (by omega), x - min x r,
      Finset.mem_range.mpr (by omega), ?_⟩
    have hle : min x r ≤ x := Nat.min_le_left x r
    omega

private theorem mrab_not_exists_of_odd {s : Nat} (hs : Odd s) :
    ¬∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  rintro ⟨A, hbound, hcover⟩
  obtain ⟨a, haA, b, hbA, hab⟩ := hcover s le_rfl
  have ha := hbound a haA
  have hb := hbound b hbA
  rw [Nat.odd_iff] at hs
  omega

open Classical in
/-- **Minimum size of a restricted additive basis.** Let $s$ be a natural number. A restricted
additive basis of $\{0, 1, \dots, s\}$ is a finite set $A$ of natural numbers with $2a \le s$ for
every $a \in A$ such that every natural number $x \le s$ can be written as $x = a + b$ with
$a, b \in A$, where $a = b$ is allowed. The minimum restricted additive basis size $k^*(s)$ is
the smallest cardinality of a restricted additive basis of $\{0, 1, \dots, s\}$; it is undefined
when no restricted additive basis of $\{0, 1, \dots, s\}$ exists.

The restriction $2a \le s$ is imposed for odd $s$ as well as for even $s$.

Proves `Wanted` entry `minimumRestrictedAdditiveBasisCard`.

Source: Jukka Kohonen, Visa Koivunen, and Robin Rajamäki, *Planar Additive
Bases for Rectangles*, Journal of Integer Sequences 21 (2018), Article
18.9.8: additive-basis notion (`A + A ⊇ [0, n]`), lines 126–128;
one-dimensional restricted basis (`A ⊆ [0, n/2]`), lines 170–171; minimum
restricted-basis notation `k^*`, lines 200–203,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Rajamaki/raj.tex>.
The one-dimensional `k^*(s, 0)` notion supports G. Yu's restricted 2-basis
bound (`s_x / k^*(s_x, 0)^2 ≤ 0.41983`, equation `eq:yu_restr`, lines
897–901), quoting G. Yu, *Upper bounds for finite additive 2-bases*,
Proc. Amer. Math. Soc. 137 (2009), 11–18, Theorem 1.2. -/
public noncomputable def minimumRestrictedAdditiveBasisCard (s : Nat) :
    { opt : Option Nat //
      (∀ k : Nat, opt = some k →
        ((∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x) ∧ A.card = k) ∧
          (∀ B : Finset Nat, (∀ b ∈ B, 2 * b ≤ s) →
            (∀ x : Nat, x ≤ s → ∃ a ∈ B, ∃ b ∈ B, a + b = x) → k ≤ B.card))) ∧
      (opt = none →
        ¬∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) } := by
  by_cases h : ∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x
  · have hex : ∃ k, ∃ A : Finset Nat, ((∀ a ∈ A, 2 * a ≤ s) ∧
        (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) ∧ A.card = k := by
      obtain ⟨A₀, hA₀⟩ := h
      exact ⟨A₀.card, A₀, hA₀, rfl⟩
    refine ⟨some (Nat.find hex), ?_, ?_⟩
    · intro k hk
      have hk' : Nat.find hex = k := Option.some_inj.mp hk
      subst hk'
      obtain ⟨A, hA, hcard⟩ := Nat.find_spec hex
      obtain ⟨hbound, hcover⟩ := hA
      refine ⟨⟨A, hbound, hcover, hcard⟩, ?_⟩
      intro B hBbound hBcover
      have hmem : ∃ A : Finset Nat, ((∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) ∧
          A.card = B.card :=
        ⟨B, ⟨hBbound, hBcover⟩, rfl⟩
      exact Nat.find_min' hex hmem
    · intro hnone
      cases hnone
  · refine ⟨none, ?_, ?_⟩
    · intro k hk
      cases hk
    · intro _ hx
      exact h hx

/-- **The minimum restricted additive basis size is undefined exactly in the odd case.** For
every natural number $s$, the minimum size $k^*(s)$ of a restricted additive basis of
$\{0, 1, \dots, s\}$, that is, of a finite set $A$ of natural numbers with $2a \le s$ for every
$a \in A$ such that every natural number $x \le s$ equals $a + b$ for some $a, b \in A$, is
undefined if and only if $s$ is odd. -/
public theorem minimumRestrictedAdditiveBasisCard_eq_none_iff (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val = none ↔ s % 2 = 1 := by
  rw [← Nat.odd_iff]
  constructor
  · intro hnone
    have hno := (minimumRestrictedAdditiveBasisCard s).property.2 hnone
    have hEven : ¬Even s := fun hev => hno (mrab_exists_of_even s hev)
    rwa [Nat.not_even_iff_odd] at hEven
  · intro hodd
    have hno := mrab_not_exists_of_odd hodd
    cases hval : (minimumRestrictedAdditiveBasisCard s).val with
    | none => rfl
    | some k =>
      have hex := ((minimumRestrictedAdditiveBasisCard s).property.1 k hval).1
      obtain ⟨A, hP, hQ, -⟩ := hex
      exact absurd ⟨A, hP, hQ⟩ hno

/-- **The minimum restricted additive basis size is defined exactly in the even case.** For
every natural number $s$, the minimum size $k^*(s)$ of a restricted additive basis of
$\{0, 1, \dots, s\}$, that is, of a finite set $A$ of natural numbers with $2a \le s$ for every
$a \in A$ such that every natural number $x \le s$ equals $a + b$ for some $a, b \in A$, is
defined if and only if $s$ is even. -/
public theorem minimumRestrictedAdditiveBasisCard_isSome_iff (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val.isSome ↔ s % 2 = 0 := by
  rw [← Nat.even_iff]
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨k, hk⟩
    have hex := ((minimumRestrictedAdditiveBasisCard s).property.1 k hk).1
    obtain ⟨A, hP, hQ, -⟩ := hex
    have hno : ¬Odd s :=
      fun hodd => (mrab_not_exists_of_odd hodd) ⟨A, hP, hQ⟩
    rwa [Nat.not_odd_iff_even] at hno
  · intro hev
    have hne : (minimumRestrictedAdditiveBasisCard s).val ≠ none := by
      intro hnone
      have hno := (minimumRestrictedAdditiveBasisCard s).property.2 hnone
      exact hno (mrab_exists_of_even s hev)
    exact Option.ne_none_iff_exists'.mp hne

end MetaMathlibExt
