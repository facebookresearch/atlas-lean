/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Solvability of diagonal congruences

The number of nonzero power residues is bounded below by counting roots of polynomials.
Cauchy–Davenport then shows that the sum of the scaled power-residue sets covers the field.
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem card_powerImage {p k : ℕ} [Fact p.Prime] (hk : 0 < k) :
    p - 1 ≤ k * ((Finset.univ.image fun x : ZMod p => x ^ k).card - 1) := by
  classical
  let P := Finset.univ.image fun x : ZMod p => x ^ k
  have hP₀ : 0 ∈ P := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, zero_pow hk.ne'⟩
  -- Count only nonzero inputs and outputs: the fiber over zero is a singleton.
  have h : (Finset.univ.erase (0 : ZMod p)).card ≤ k * (P.erase 0).card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := fun x : ZMod p => x ^ k) ?_ k ?_
    · intro x hx
      exact Finset.mem_erase.mpr ⟨pow_ne_zero _ (Finset.ne_of_mem_erase hx),
        Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
    · intro y _
      calc
        _ ≤ (Polynomial.nthRootsFinset k y).card := Finset.card_le_card fun x hx =>
          (Polynomial.mem_nthRootsFinset hk y).mpr (Finset.mem_filter.mp hx).2
        _ ≤ k := by
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots k y)
  simpa only [Finset.card_erase_of_mem hP₀, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card] using h

/-- **Diagonal congruences in $k$ variables are solvable.** Let $p$ be a prime and $k \ge 1$. For
all integers $a_1, \dots, a_k$ not divisible by $p$ and every integer $c$, there are integers
$x_1, \dots, x_k$ with $a_1 x_1^k + \dots + a_k x_k^k \equiv c \pmod p$.

Equivalently, $\Gamma(k, p) \le k$, where $\Gamma(k, p)$ is the least $n$ such that every such
congruence in $n$ variables is solvable; extra variables can be set to $0$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 2
(`integers-2026-A14-lem-2`). -/
public theorem diagonal_congruence_solvable_of_card_eq_exponent (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (c : ℤ) :
    ∃ x : Fin k → ℤ, ∑ i, a i * x i ^ k ≡ c [ZMOD p] := by
  classical
  have hk₀ : k ≠ 0 := Nat.ne_of_gt hk
  let P := Finset.univ.image fun x : ZMod p => x ^ k
  have hP₀ : 0 ∈ P := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, zero_pow hk₀⟩
  have hPpos : 0 < P.card := Finset.card_pos.mpr ⟨0, hP₀⟩
  let values (n : ℕ) (b : Fin n → ZMod p) :=
    Finset.univ.image fun x : Fin n → ZMod p => ∑ i, b i * x i ^ k
  have hzero (n : ℕ) (b : Fin n → ZMod p) : 0 ∈ values n b :=
    Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, by simp [zero_pow hk₀]⟩
  -- Each variable contributes at least `P.card - 1` new values, until the field is covered.
  have hcard (n : ℕ) (b : Fin n → ZMod p) (hb : ∀ i, b i ≠ 0) :
      min p (1 + n * (P.card - 1)) ≤ (values n b).card := by
    induction n with
    | zero =>
      simpa only [Nat.zero_mul, Nat.add_zero] using
        (min_le_right p 1).trans (Finset.card_pos.mpr ⟨0, hzero 0 b⟩)
    | succ n ih =>
      let S := P.image (b 0 * ·)
      have hS : S.card = P.card :=
        Finset.card_image_of_injective _ fun _ _ => mul_left_cancel₀ (hb 0)
      have hS₀ : 0 ∈ S := Finset.mem_image.mpr ⟨0, hP₀, mul_zero _⟩
      have hadd : values (n + 1) b = S + values n (fun i => b i.succ) := by
        have hS' : S = Finset.univ.image (fun x : ZMod p => b 0 * x ^ k) := Finset.image_image
        ext z
        simp only [values, hS', Finset.mem_add, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨_, ⟨x 0, rfl⟩, _, ⟨fun i => x i.succ, rfl⟩, by rw [Fin.sum_univ_succ]⟩
        · rintro ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
          exact ⟨Fin.cons u v, by rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]⟩
      have hgrowth := ZMod.cauchy_davenport (Fact.out : p.Prime) ⟨0, hS₀⟩
        ⟨0, hzero n (fun i => b i.succ)⟩
      rw [← hadd, hS] at hgrowth
      have htail := ih (fun i => b i.succ) (fun i => hb i.succ)
      rw [Nat.succ_mul]
      omega
  let b (i : Fin k) : ZMod p := a i
  have hb (i : Fin k) : b i ≠ 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) p).mp (ha i)
  have hfull : values k b = Finset.univ := by
    have hp := (Fact.out : p.Prime).pos
    have hP : p - 1 ≤ k * (P.card - 1) := card_powerImage hk
    have h := hcard k b hb
    have hle : p ≤ (values k b).card := by omega
    apply Finset.eq_univ_of_card
    rw [ZMod.card]
    refine le_antisymm ?_ hle
    simpa only [ZMod.card] using Finset.card_le_univ (values k b)
  have hc : (c : ZMod p) ∈ values k b := hfull ▸ Finset.mem_univ _
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
  refine ⟨fun i => (x i).val, (ZMod.intCast_eq_intCast_iff _ _ p).mp ?_⟩
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_zmod_val]
    using hx

end MetaMathlibExt
