/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.Defs
public import MathlibExt.NumberTheory.NicomacheanTranslations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nicomachean families sharing a quadratic factor

For every natural number $N$, there are $N$ lists of positive integers with zero Nicomachean
defect, distinct even as multisets, with a common sum $c$. Appending integers $a,b$ to any of
these lists gives defect $-(a+b)(a^2-ab+b^2-a-b-2c)$. The case $N=0$ is vacuous.

For $N=n+1$, take products of $n$ factors from the two lists in Section 9 of Kim and Stolarsky.
Both lists have sum $66$ and cube sum $66^2$, so these products have sum $66^n$ and cube sum
$(66^n)^2$. The two lists have lengths $11$ and $12$, so the product lengths strictly increase as
more long factors are used. This gives the required distinctness without relying on order.

## References

- Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean Identity*,
  Journal of Integer Sequences 27 (2024), Article 24.6.3, pp. 1–23, Sections 4 and 9,
  Proposition 12.
- John Mason, *Generalising ‘Sums of cubes equal to squares of sums’*, The Mathematical Gazette
  85 (2001), no. 502, pp. 50–58 (the bag product, cited in Kim and Stolarsky, Section 1).
-/

namespace MetaMathlibExt

private def seed (long : Bool) : List ℤ :=
  if long then [1, 2, 3, 3, 3, 5, 5, 6, 7, 9, 10, 12] else [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

private theorem sum_product_map_mul {R : Type*} [Semiring R] {α β : Type*}
    (s : List α) (t : List β) (f : α → R) (g : β → R) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum = (s.map f).sum * (t.map g).sum := by
  change ((s.flatMap fun x => t.map (x, ·)).map _).sum = _
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten]
  simp only [List.map_map, Function.comp_def, List.sum_map_mul_left, List.sum_map_mul_right]

private theorem exists_family (n : ℕ) :
    ∃ σ : Fin (n + 1) → List ℤ, StrictMono (fun i => (σ i).length) ∧ ∀ i,
      0 < (σ i).length ∧ (∀ x ∈ σ i, 0 < x) ∧ (σ i).sum = (66 : ℤ) ^ n ∧
        ((σ i).map (· ^ 3)).sum = ((66 : ℤ) ^ n) ^ 2 := by
  induction n with
  | zero =>
    refine ⟨fun _ => [1], Fin.strictMono_iff_lt_succ.mpr Fin.elim0, fun _ => ?_⟩
    norm_num [List.forall_mem_cons]
  | succ n ih =>
    obtain ⟨σ, hσmono, hσ⟩ := ih
    let lift (long : Bool) (i : Fin (n + 1)) :=
      (seed long ×ˢ σ i).map (fun p => p.1 * p.2)
    have hliftLength (long : Bool) (i : Fin (n + 1)) :
        (lift long i).length = (seed long).length * (σ i).length := by
      simp only [lift, List.length_map, List.length_product]
    have hlift (long : Bool) (i : Fin (n + 1)) :
        0 < (lift long i).length ∧ (∀ x ∈ lift long i, 0 < x) ∧
          (lift long i).sum = (66 : ℤ) ^ (n + 1) ∧
          ((lift long i).map (· ^ 3)).sum = ((66 : ℤ) ^ (n + 1)) ^ 2 := by
      have hlen : 0 < (seed long).length := by cases long <;> decide
      have hpos : ∀ x ∈ seed long, 0 < x := by cases long <;> norm_num [seed, List.forall_mem_cons]
      have hsum : (seed long).sum = 66 := by cases long <;> decide
      have hcubes : ((seed long).map (· ^ 3)).sum = (66 : ℤ) ^ 2 := by cases long <;> decide
      obtain ⟨hiLen, hiPos, hiSum, hiCubes⟩ := hσ i
      refine ⟨by rw [hliftLength]; exact Nat.mul_pos hlen hiLen, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ha, hb⟩ := List.mem_product.mp hab
        exact mul_pos (hpos a ha) (hiPos b hb)
      · have h := sum_product_map_mul (seed long) (σ i) id id
        simp only [id_eq, List.map_id] at h
        dsimp only [lift]
        rw [h, hsum, hiSum, pow_succ']
      · have h := sum_product_map_mul (seed long) (σ i) (· ^ 3) (· ^ 3)
        rw [hcubes, hiCubes] at h
        simpa only [lift, List.map_map, Function.comp_def, mul_pow, pow_succ' (66 : ℤ) n] using h
    refine ⟨Fin.cons (lift false 0) (lift true), ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hliftLength]
        exact Nat.mul_lt_mul_of_pos_right (by decide) (hσ 0).1
      | succ i =>
        simp only [Fin.castSucc_succ, Fin.cons_succ, hliftLength]
        exact Nat.mul_lt_mul_of_pos_left (hσmono (Fin.castSucc_lt_succ (i := i))) (by decide)
    · intro i
      cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using hlift false 0
      | succ i => simpa only [Fin.cons_succ] using hlift true i

/-- **Nicomachean families sharing a quadratic factor.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $N$ there are finite sequences
$\sigma_1, \dots, \sigma_N$ of positive integers, pairwise distinct as multisets, and an integer
$c$ such that for every $i$ we have $\nu(\sigma_i) = 0$ and, for all integers $a$ and $b$, the
sequence $(\sigma_i, a, b)$ obtained by appending $a$ and $b$ to $\sigma_i$ satisfies
$\nu(\sigma_i, a, b) = -(a + b)(a^2 - ab + b^2 - a - b - 2c)$.

Since $\nu(\sigma_i) = 0$, the identity forces $c$ to be the sum of the entries of every
$\sigma_i$. Positivity of the entries, the paper's setting, excludes trivial families such as
$(k, -k, 1)$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 12
(`jis-2024-24.6.3-prop-12`). -/
public theorem exists_nicomachean_family_same_quadratic_factor (N : ℕ) :
    ∃ σ : Fin N → List ℤ, Function.Injective (fun i => (σ i : Multiset ℤ)) ∧ ∃ c : ℤ, ∀ i,
      (∀ x ∈ σ i, 0 < x) ∧ nicomacheanNu (σ i) = 0 ∧
        ∀ a b : ℤ, nicomacheanNu (σ i ++ [a, b]) =
          -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 2 * c) := by
  cases N with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, 0, fun i => i.elim0⟩
  | succ n =>
    obtain ⟨σ, hmono, hσ⟩ := exists_family n
    refine ⟨σ, ?_, (66 : ℤ) ^ n, fun i => ?_⟩
    · intro i j hij
      exact hmono.injective (by simpa only [Multiset.coe_card] using congrArg Multiset.card hij)
    · obtain ⟨_, hpos, hsum, hcubes⟩ := hσ i
      have hnil : nicomacheanNu ([] : List ℤ) = 0 := by decide
      have hν : nicomacheanNu (σ i) = 0 := by
        have h := nicomacheanNu_append [] (σ i)
        simpa only [List.nil_append, List.sum_nil, hnil, mul_zero, zero_add, hsum, hcubes,
          ← pow_two, sub_self] using h
      refine ⟨hpos, hν, fun a b => ?_⟩
      rw [nicomacheanNu_append, hν, hsum]
      simp only [List.sum_cons, List.sum_nil, add_zero, List.map_cons, List.map_nil, zero_add]
      ring

end MetaMathlibExt
