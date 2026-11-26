/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.MahlerPopkenComplexity.BinaryUpperBound

/-!
# Recursion for the binary Mahler–Popken complexity

For `n ≥ 3`, the binary (`2`-ary) Mahler–Popken complexity of `n` equals the minimum of the
sums over its nontrivial divisors and over its splits into two positive parts.

Statements from John M. Campbell, "A Binary Version of the
Mahler-Popken Complexity Function", *INTEGERS* 24 (2024),
Article A94 (<https://math.colgate.edu/~integers/y94/y94.pdf>).
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

/-- **Recursion for the binary Mahler–Popken complexity.** For every natural number $n \ge 3$,
the binary ($2$-ary) Mahler–Popken complexity $\lVert n \rVert_2$ equals the minimum of the sums
$\lVert d \rVert_2 + \lVert n/d \rVert_2$ over the divisors $d$ of $n$ with $d \ne 1$ and
$d \ne n$, and of the sums $\lVert \eta \rVert_2 + \lVert n - \eta \rVert_2$ over $0 < \eta < n$.
This is the recursion (9) for $m = 2$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
public theorem mahlerPopkenComplexity_two_eq_recursionValue
    (n : ℕ) (hn : 3 ≤ n) :
    mahlerPopkenComplexity 2 n = mahlerPopkenRecursionValue 2 n := by
  apply le_antisymm
  · have hne : {k : ℕ |
        (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
          k = mahlerPopkenComplexity 2 d +
            mahlerPopkenComplexity 2 (n / d)) ∨
        (∃ η : ℕ, 0 < η ∧ η < n ∧
          k = mahlerPopkenComplexity 2 η +
            mahlerPopkenComplexity 2 (n - η))}.Nonempty :=
      ⟨mahlerPopkenComplexity 2 1 + mahlerPopkenComplexity 2 (n - 1),
        Or.inr ⟨1, by omega, by omega, rfl⟩⟩
    have hmem : mahlerPopkenRecursionValue 2 n ∈ {k : ℕ |
        (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
          k = mahlerPopkenComplexity 2 d +
            mahlerPopkenComplexity 2 (n / d)) ∨
        (∃ η : ℕ, 0 < η ∧ η < n ∧
          k = mahlerPopkenComplexity 2 η +
            mahlerPopkenComplexity 2 (n - η))} :=
      Nat.sInf_mem hne
    simp only [Set.mem_ofPred_eq] at hmem
    rcases hmem with ⟨d, hdvd, -, -, hEq⟩ | ⟨η, hηpos, hηlt, hEq⟩
    · have hd_pos : 1 ≤ d := by
        by_contra h
        have hd0 : d = 0 := by omega
        obtain ⟨q, hq⟩ := hdvd
        rw [hd0, zero_mul] at hq
        omega
      have hdiv_pos : 1 ≤ n / d :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd_pos
      have hsub := mahlerPopkenComplexity_mul_le (m := 2) (a := d) (b := n / d)
        (by decide) hd_pos hdiv_pos
      rw [Nat.mul_div_cancel' hdvd] at hsub
      rw [hEq]
      exact hsub
    · have hsub := mahlerPopkenComplexity_add_le (m := 2) (a := η) (b := n - η)
        (by decide) hηpos (by omega)
      rw [show η + (n - η) = n by omega] at hsub
      rw [hEq]
      exact hsub
  · obtain ⟨e, he, hc⟩ :=
      mahlerPopkenComplexity_spec (m := 2) (n := n) (by decide) (by omega)
    cases e with
    | leaf i =>
      simp only [MahlerPopkenExpr.eval_leaf] at he
      have hi := i.isLt
      omega
    | add a b =>
      simp only [MahlerPopkenExpr.eval_add, MahlerPopkenExpr.count_add] at he hc
      have ha_pos := a.eval_pos
      have hb_pos := b.eval_pos
      have hηlt : a.eval < n := by omega
      have hsub_eq : n - a.eval = b.eval := by omega
      have hmem : mahlerPopkenComplexity 2 a.eval +
          mahlerPopkenComplexity 2 b.eval ∈ {k : ℕ |
          (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
            k = mahlerPopkenComplexity 2 d +
              mahlerPopkenComplexity 2 (n / d)) ∨
          (∃ η : ℕ, 0 < η ∧ η < n ∧
            k = mahlerPopkenComplexity 2 η +
              mahlerPopkenComplexity 2 (n - η))} :=
        Or.inr ⟨a.eval, ha_pos, hηlt, by rw [hsub_eq]⟩
      have hle : mahlerPopkenRecursionValue 2 n ≤
          mahlerPopkenComplexity 2 a.eval + mahlerPopkenComplexity 2 b.eval :=
        Nat.sInf_le hmem
      have ha := mahlerPopkenComplexity_min_le (m := 2) a rfl
      have hb := mahlerPopkenComplexity_min_le (m := 2) b rfl
      refine hle.trans ?_
      rw [← hc]
      exact Nat.add_le_add ha hb
    | mul a b =>
      simp only [MahlerPopkenExpr.eval_mul, MahlerPopkenExpr.count_mul] at he hc
      have ha_pos := a.eval_pos
      have hdvd : a.eval ∣ n := ⟨b.eval, he.symm⟩
      have hd1 : a.eval ≠ 1 := by
        intro h1
        have hb_eq : b.eval = n := by simpa [h1] using he
        have hb := mahlerPopkenComplexity_min_le (m := 2) (n := n) b hb_eq
        have hac := a.count_pos
        omega
      have hdn : a.eval ≠ n := by
        intro h1
        have ha := mahlerPopkenComplexity_min_le (m := 2) (n := n) a h1
        have hbc := b.count_pos
        omega
      have hdiv_eq : n / a.eval = b.eval := by
        rw [← he]
        exact Nat.mul_div_cancel_left _ ha_pos
      have hmem : mahlerPopkenComplexity 2 a.eval +
          mahlerPopkenComplexity 2 b.eval ∈ {k : ℕ |
          (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
            k = mahlerPopkenComplexity 2 d +
              mahlerPopkenComplexity 2 (n / d)) ∨
          (∃ η : ℕ, 0 < η ∧ η < n ∧
            k = mahlerPopkenComplexity 2 η +
              mahlerPopkenComplexity 2 (n - η))} :=
        Or.inl ⟨a.eval, hdvd, hd1, hdn, by rw [hdiv_eq]⟩
      have hle : mahlerPopkenRecursionValue 2 n ≤
          mahlerPopkenComplexity 2 a.eval + mahlerPopkenComplexity 2 b.eval :=
        Nat.sInf_le hmem
      have ha := mahlerPopkenComplexity_min_le (m := 2) a rfl
      have hb := mahlerPopkenComplexity_min_le (m := 2) b rfl
      refine hle.trans ?_
      rw [← hc]
      exact Nat.add_le_add ha hb

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted
