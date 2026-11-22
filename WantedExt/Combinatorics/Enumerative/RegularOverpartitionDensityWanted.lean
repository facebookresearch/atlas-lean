/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Arithmetic density of ℓ-regular overpartitions (statements)

Statement-only targets from Murugan P and Fathima S. N, *Arithmetic Density of Certain
ℓ-Regular Overpartitions*. `A_ℓ(n)` is `regularOverpartitionCount ℓ n`, counted with the
existing `Nat.Overpartition` structure.
-/

namespace MetaMathlibExt

open scoped Topology

@[expose] public section


/--
`regularOverpartitionCount ℓ n` is `A_ℓ(n)`, the number of overpartitions of
`n` whose every part is not divisible by `ℓ`. This is the combinatorial
interpretation of the product in Identity (1); no positivity restriction is
placed on `ℓ` in the definition.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public noncomputable def regularOverpartitionCount (ℓ n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a}

/--
There is exactly one `ℓ`-regular overpartition of zero, namely the empty
overpartition. The statement also covers `ℓ = 0`, a harmless extension of
the paper's positive regularity parameter.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_zero (ℓ : ℕ) :
    regularOverpartitionCount ℓ 0 = 1 := by
  let O : {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨Nat.Overpartition.ofPartition default, by
      intro a ha
      simp [_root_.Nat.Partition.partition_zero_parts] at ha⟩
  let _ : Nonempty {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} := ⟨O⟩
  let _ : Subsingleton {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨fun O₁ O₂ => Subtype.ext (Nat.Overpartition.eq_of_zero O₁.1 O₂.1)⟩
  exact Nat.card_unique

/--
If `2 ≤ ℓ`, the two `ℓ`-regular overpartitions of one are the part `1`
without an overline and with an overline. The hypothesis formalizes that
`ℓ` does not divide the sole part.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_one (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    regularOverpartitionCount ℓ 1 = 2 := by
  let e :
      {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} ≃ Bool := {
    toFun O := decide (1 ∈ O.1.overlines)
    invFun b :=
      ⟨{
        toPartition := default
        overlines := if b = true then {1} else ∅
        overlines_subset := by
          intro a ha
          rw [_root_.Nat.Partition.partition_one_parts]
          cases b <;> simp_all
      }, by
        intro a ha hdiv
        rw [_root_.Nat.Partition.partition_one_parts] at ha
        have haone : a = 1 := by simpa using ha
        subst a
        have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide) hdiv
        omega⟩
    left_inv O := by
      apply Subtype.ext
      apply Nat.Overpartition.ext
      · exact Subsingleton.elim _ _
      · have hsub : O.1.overlines ⊆ {1} := by
          intro a ha
          have h := O.1.overlines_subset ha
          rw [_root_.Nat.Partition.partition_one_parts] at h
          simpa using h
        by_cases hmem : 1 ∈ O.1.overlines
        · have hover : O.1.overlines = {1} := by
            apply Finset.Subset.antisymm hsub
            simpa using hmem
          simp [hover]
        · have hover : O.1.overlines = ∅ := by
            apply Finset.Subset.antisymm
            · intro a ha
              have haone : a = 1 := by simpa using hsub ha
              subst a
              exact (hmem ha).elim
            · exact Finset.empty_subset _
          simp [hover]
    right_inv b := by
      cases b <;> simp
  }
  unfold regularOverpartitionCount
  calc
    Nat.card {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} =
        Nat.card Bool := Nat.card_congr e
    _ = 2 := by simp

/--
For `1 ≤ ℓ` and `n ≤ N`, the coefficient of `Xⁿ` in the finite product
over `1 ≤ k ≤ N` with `ℓ ∤ k` of
`(1 + Xᵏ) · ∑_{i ≤ N} X^(ki)` equals `A_ℓ(n)`. Bounding every geometric
sum by `N` and asking only for coefficients through degree `N` is the
finite-polynomial version of the paper's infinite generating function.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem_wanted regularOverpartitionCount_eq_coeff_truncatedProduct
    (ℓ N n : ℕ) (hℓ : 1 ≤ ℓ) (hn : n ≤ N) :
    (∏ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ ℓ ∣ k),
      (((1 : Polynomial ℕ) + Polynomial.X ^ k) *
        ∑ i ∈ Finset.range (N + 1), Polynomial.X ^ (k * i))).coeff n =
      regularOverpartitionCount ℓ n

/--
If `p` is an odd prime and `j ≥ 1`, the natural density of natural numbers
`n ≤ X` for which `2ʲ ∣ A_p(n)` tends to one. The numerator uses
`Finset.range (X + 1)`, exactly encoding `0 ≤ n ≤ X`, while the denominator
is the paper's `X`.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 1.
-/
public theorem_wanted regularOverpartition_prime_power_two_density
    (p j : ℕ) (hp : p.Prime) (hpodd : Odd p) (hj : 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n => 2 ^ j ∣ regularOverpartitionCount p n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
If `p` is an odd prime and `j ≥ 1`, the natural density of natural numbers
`n ≤ X` for which `2ʲ ∣ A_{3p}(n)` tends to one. The range and denominator
formalize the paper's counting quotient exactly as in Theorem 1.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 2.
-/
public theorem_wanted regularOverpartition_three_mul_prime_power_two_density
    (p j : ℕ) (hp : p.Prime) (hpodd : Odd p) (hj : 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n => 2 ^ j ∣ regularOverpartitionCount (3 * p) n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
For positive `α` and `j` with `α + 1 ≤ j` (so `j` is positive), the natural density of
`n ≤ X` for which `2ʲ ∣ A_{3·2^α}(n)` tends to one. The formal count
includes zero and uses the paper's denominator `X`.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 3.
-/
public theorem_wanted regularOverpartition_three_mul_two_power_density
    (j α : ℕ) (hα : 1 ≤ α) (hja : α + 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n =>
            2 ^ j ∣ regularOverpartitionCount (3 * 2 ^ α) n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
For every positive `α`, there is a nonnegative `c` such that, for every
`d ≥ 1`, every injectively indexed family of `c + d` primes coprime to
`6`, and every `n` coprime to all those primes, `A_{3·2^α}` at the
product of the primes times `n / 24` is zero modulo `2ᵈ`. The hypothesis
`24 ∣ n` is added because the paper obtains a coefficient in a series in
`q²⁴`; when `24 ∤ n`, that coefficient is zero rather than the displayed
natural-number argument being justified.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 4.
-/
public theorem_wanted regularOverpartition_three_mul_two_power_many_primes
    (α : ℕ) (hα : 0 < α) :
    ∃ c : ℕ, ∀ (d : ℕ), 1 ≤ d →
      ∀ (ps : Fin (c + d) → ℕ), Function.Injective ps →
        (∀ i, (ps i).Prime) →
        (∀ i, Nat.Coprime (ps i) 6) →
        ∀ n : ℕ, (∀ i, Nat.Coprime n (ps i)) → 24 ∣ n →
          Nat.ModEq (2 ^ d)
            (regularOverpartitionCount (3 * 2 ^ α)
              ((∏ i, ps i) * n / 24))
            0

/--
Let `ℓ ≡ 3 (mod 4)`; for `k + 1` (not necessarily distinct) primes, all
greater than two and congruent to three modulo four, and natural `j` not
congruent to zero modulo the last prime, the displayed unshifted argument of
`A_ℓ` is zero modulo four. The product over `Fin k` is
`p₁²⋯p_k²`, and `ps (Fin.last k)` is `p_{k+1}`. The paper takes `j`
to be an integer; this formalization uses `j : ℕ`, as required by the
reading, and deliberately does not use the false shifted interpretation.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 5.
-/
public theorem_wanted regularOverpartition_mod_four_prime_family
    (ℓ n k j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (ps : Fin (k + 1) → ℕ)
    (hps : ∀ i, (ps i).Prime ∧ 2 < ps i ∧ Nat.ModEq 4 (ps i) 3)
    (hj : ¬ Nat.ModEq (ps (Fin.last k)) j 0) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ
        ((∏ i : Fin k, (ps i.castSucc) ^ 2) *
          ps (Fin.last k) *
          (ps (Fin.last k) * (4 * n + 1) + 4 * j)))
      0

/--
If `ℓ ≡ 3 (mod 4)` and `p > 2` is prime with the printed condition
`p ≢ 1 (mod 6)`, then for all natural `k,n,j` with `j ≢ 0 (mod p)`,
`A_ℓ(p^(2k+2)(4n+1) + p^(2k+1)·4j)` is zero modulo four. The condition
modulo six is retained exactly as printed rather than replaced by the
modulo-four condition used in Theorem 5.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Corollary 1.
-/
public theorem_wanted regularOverpartition_mod_four_single_prime
    (ℓ p k n j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (hp : p.Prime) (hp2 : 2 < p) (hp6 : ¬ Nat.ModEq 6 p 1)
    (hj : ¬ Nat.ModEq p j 0) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ
        (p ^ (2 * k + 2) * (4 * n + 1) +
          p ^ (2 * k + 1) * (4 * j)))
      0

/--
If `ℓ ≡ 3 (mod 4)` and natural `j` is not congruent to
`(ℓ - 3) / 4` modulo `ℓ`, then `A_ℓ(4ℓn + 4j + 3)` is zero modulo
four. The unused `k ≥ 0` occurring in the extraction is omitted. Natural
subtraction and division formalize the displayed quotient; the congruence
hypothesis ensures the intended positive case.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 6.
-/
public theorem_wanted regularOverpartition_mod_four_progression
    (ℓ n j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (hj : ¬ Nat.ModEq ℓ j ((ℓ - 3) / 4)) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ (4 * ℓ * n + 4 * j + 3))
      0

/--
For all natural `n,k`, `A₇(7^(2k)(4n+3))` is congruent modulo seven to
`A₇(4n+3)`. Naturals directly encode the paper's nonnegativity hypotheses.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 7.
-/
public theorem_wanted regularOverpartition_seven_self_similarity
    (n k : ℕ) :
    Nat.ModEq 7
      (regularOverpartitionCount 7 (7 ^ (2 * k) * (4 * n + 3)))
      (regularOverpartitionCount 7 (4 * n + 3))

/--
For every natural `n`, the four families printed in Theorem 8 vanish
modulo seven: residue `4` modulo `16`; residues below `64` congruent
to `4` modulo `32`; residues below `256` congruent to `4` modulo
`32`; and residues below `1024` congruent to `4` modulo `32`.
The bounded modular descriptions are exactly the explicit residue sets in
the paper.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 8.
-/
public theorem_wanted regularOverpartition_seven_ramanujan_congruences
    (n : ℕ) :
    Nat.ModEq 7 (regularOverpartitionCount 7 (16 * n + 4)) 0 ∧
    (∀ i : ℕ, i % 32 = 4 → i < 64 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (64 * n + i)) 0) ∧
    (∀ j : ℕ, j % 32 = 4 → j < 256 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (256 * n + j)) 0) ∧
    (∀ k : ℕ, k % 32 = 4 → k < 1024 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (1024 * n + k)) 0)

/--
For positive `s,t` and prime `p`, and every cutoff `N`, every
coefficient of
`(∏_{1≤m≤N}(1-X^(sm)))^(p^t) -
  (∏_{1≤m≤N}(1-X^(spm)))^(p^(t-1))`
is divisible in `ℤ` by `p^t`. This faithful finite-polynomial form implies
the paper's formal-series congruence coefficientwise as `N` increases.
Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 1.
-/
public theorem_wanted finiteEulerProduct_primePower_congruence
    (s t p N : ℕ) (hs : 0 < s) (ht : 0 < t) (hp : p.Prime) :
    ∀ r : ℕ, (p : ℤ) ^ t ∣
      ((∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * m))) ^ (p ^ t) -
        (∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * p * m))) ^
            (p ^ (t - 1))).coeff r

/-- Double coset representatives for `Γ₀(N) \ SL₂(ℤ) / Γ_∞`: if `N` or `N / 2` is
squarefree, every `γ ∈ SL₂(ℤ)` lies in `Γ₀(N) [[1, 0], [δ, 1]] Γ_∞` for exactly one `δ ∣ N`
(coverage and pairwise inequivalence of the representatives), where `Γ_∞` is generated by
`T = [[1, 1], [0, 1]]` (adding `-I` changes nothing, as `-I ∈ Γ₀(N)`).

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 3 (`integers-2025-A3-lem-3`), quoting Wang, Lemma 4.3.
"`N / 2` is squarefree" is read with `2 ∣ N`. -/
public theorem_wanted exists_gamma0_lowerUnipotent_T_zpow_decomposition (N : ℕ)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃! δ : ℕ, δ ∣ N ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 N, ∃ h : ℤ,
      γ = A * ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩ * ModularGroup.T ^ h

end

end MetaMathlibExt
