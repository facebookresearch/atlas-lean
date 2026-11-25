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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteTorusNormalizer
public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleRootComplement

/-! # Adjacent simple-Weyl generation modulo the finite Borel

For `[Field F]`, bounded distinct `i, j < n`, and `u : Fˣ`, express the
arbitrary Weyl generator `weyl i j u` as finite-Borel factors around an
explicit finite product of adjacent unit-one simple Weyl lifts
`weyl k (k + 1) 1` with `k + 1 < n`.

Proof route (per recovery note after session `30577`): stable-level left-peel
induction using `weyl_conj_weyl_mixed`, avoiding explicit monomial-weight
bookkeeping. For `i < j`, peel the leftmost adjacent lift:
`weyl i j 1 = s * weyl (i + 1) j 1 * s⁻¹` with `s = weyl i (i + 1) 1`; the
`s⁻¹`-vs-`s` mismatch is absorbed by `s * s = (torus i (i + 1) (-1))⁻¹` in the
finite torus, and torus conjugates stay in the finite torus by
`weyl_conj_finiteTorus_mem`. The adjacent word is the standard palindrome
realizing transposition `(i j)`: `W(i, j) = s_i ++ W(i + 1, j) ++ s_i` with
`W(j - 1, j) = [s_{j - 1}]`, of length `2 * (j - i) - 1`; termination is by the
strictly decreasing natural distance. Units are stripped once via
`weyl u = torus u * weyl 1` (`torus`/`weyl_neg_eq_inv`); the `j < i` order
reduces to `i < j` by `weyl_swap`. Ranks `0`/`1` need no special case: with
`i < n`, `j < n`, `i ≠ j` in context, every index bound closes by `omega`.
Characteristic-two/`F₂` safe: only group identities, `weyl_neg_eq_inv`,
torus membership, and index arithmetic occur; no `(-1 ≠ 1)` or `(2 ≠ 0)`.

Orientation: conjugation is always `c * y * c⁻¹` (conjugator on the left);
list products are head-left `List.ofFn`/`List.prod` order.

Nonclaims: no arbitrary finite-Weyl word factorization, no Lemma-25
iteration, no full Bruhat existence, no Matsumoto theorem, no target kernel
containment, no quotient injectivity, and no universal central extension are
used or claimed.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Arbitrary-unit Weyl split: `weyl q p u = torus q p u * weyl q p 1`.
Follows `torus` (`weyl u * weyl (-1)`) and `weyl_neg_eq_inv`.
Characteristic-two safe. -/
private theorem weyl_eq_torus_mul_weyl_one {q p : ℕ} (hij : q ≠ p) (u : Fˣ) :
    weyl (R := F) q p hij u =
      torus (R := F) q p hij u * weyl (R := F) q p hij (1 : Fˣ) := by
  have hw1 : weyl (R := F) q p hij (-1 : Fˣ) =
      (weyl (R := F) q p hij (1 : Fˣ))⁻¹ :=
    weyl_neg_eq_inv _ _ _ _
  have hdecomp : torus (R := F) q p hij u * weyl (R := F) q p hij (1 : Fˣ) =
      weyl (R := F) q p hij u := by
    change weyl (R := F) q p hij u * weyl (R := F) q p hij (-1 : Fˣ) *
      weyl (R := F) q p hij (1 : Fˣ) = _
    rw [hw1, inv_mul_cancel_right]
  exact hdecomp.symm

/-- Unit-one left-peel generation: for `i + 1 + d < n`, `weyl i (i + 1 + d) 1`
is an explicit adjacent unit-one word (the standard palindrome for
transposition `(i, i + 1 + d)`) times a finite-torus element. Induction on the
distance `d` via `weyl_conj_weyl_mixed`; the conclusion quantifies over all
`≠` proofs so callers may supply their own. Characteristic-two safe. -/
private theorem weyl_one_eq_adjacent_mul_torus {n : ℕ} (d : ℕ) :
    ∀ i : ℕ, i + 1 + d < n →
      ∃ (m : ℕ) (c : Fin m → ℕ),
        (∀ k, c k + 1 < n) ∧
        ∃ t ∈ finiteTorusSubgroup (R := F) n,
          ∀ hij : i ≠ i + 1 + d,
            weyl (R := F) i (i + 1 + d) hij (1 : Fˣ) =
              (List.ofFn fun k => weyl (R := F) (c k) (c k + 1)
                (Nat.ne_of_lt (Nat.lt_succ_self (c k))) (1 : Fˣ)).prod * t := by
  induction d with
  | zero =>
      intro i hi
      refine ⟨1, fun _ => i, fun _ => by simpa using hi, 1,
        Subgroup.one_mem _, fun hij => ?_⟩
      simp
  | succ d ih =>
      intro i hi
      have hin : i < n := by omega
      have hin1 : i + 1 < n := by omega
      have hi2 : (i + 1) + 1 + d < n := by omega
      have hidx : (i + 1) + 1 + d = i + 1 + (d + 1) := by omega
      have hik : i ≠ i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
      have hkj : i + 1 ≠ i + 1 + (d + 1) := by omega
      have h11 : (1 : Fˣ) * 1 = 1 := mul_one _
      obtain ⟨m', c', hc', t', ht', hW'⟩ := ih (i + 1) hi2
      rw [hidx] at hW'
      have hIH := hW' hkj
      have ht0 : torus (R := F) i (i + 1) hik (-1 : Fˣ) ∈
          finiteTorusSubgroup (R := F) n :=
        torus_mem_finiteTorusSubgroup hin hin1 hik _
      have ht1 : weyl (R := F) i (i + 1) hik (1 : Fˣ) * t' *
          (weyl (R := F) i (i + 1) hik (1 : Fˣ))⁻¹ ∈
          finiteTorusSubgroup (R := F) n :=
        weyl_conj_finiteTorus_mem hin hin1 hik _ ht'
      have hwneg : weyl (R := F) i (i + 1) hik (-1 : Fˣ) =
          (weyl (R := F) i (i + 1) hik (1 : Fˣ))⁻¹ :=
        weyl_neg_eq_inv _ _ _ _
      have ht0eq : torus (R := F) i (i + 1) hik (-1 : Fˣ) =
          (weyl (R := F) i (i + 1) hik (1 : Fˣ))⁻¹ *
            (weyl (R := F) i (i + 1) hik (1 : Fˣ))⁻¹ := by
        change weyl (R := F) i (i + 1) hik (-1 : Fˣ) *
          weyl (R := F) i (i + 1) hik (-1 : Fˣ) = _
        rw [hwneg]
      refine ⟨(1 + m') + 1,
        Fin.append (Fin.append (fun _ : Fin 1 => i) c') (fun _ : Fin 1 => i),
        ?_, torus (R := F) i (i + 1) hik (-1 : Fˣ) *
          (weyl (R := F) i (i + 1) hik (1 : Fˣ) * t' *
            (weyl (R := F) i (i + 1) hik (1 : Fˣ))⁻¹),
        Subgroup.mul_mem _ ht0 ht1, ?_⟩
      · intro k
        refine Fin.addCases (fun a => ?_) (fun b => ?_) k
        · refine Fin.addCases (fun a1 => ?_) (fun b1 => ?_) a
          · rw [Fin.append_left, Fin.append_left]
            exact hin1
          · rw [Fin.append_left, Fin.append_right]
            exact hc' b1
        · rw [Fin.append_right]
          exact hin1
      · intro hij
        have hpeel := weyl_conj_weyl_mixed (R := F) i (i + 1 + (d + 1)) (i + 1)
          hij hik hkj (1 : Fˣ) (1 : Fˣ)
        rw [h11] at hpeel
        have hfun : (fun k => weyl (R := F)
              ((Fin.append (Fin.append (fun _ : Fin 1 => i) c')
                (fun _ : Fin 1 => i)) k)
              (((Fin.append (Fin.append (fun _ : Fin 1 => i) c')
                (fun _ : Fin 1 => i)) k) + 1)
              (Nat.ne_of_lt (Nat.lt_succ_self _)) (1 : Fˣ))
            = Fin.append (Fin.append
                (fun _ : Fin 1 => weyl (R := F) i (i + 1) hik (1 : Fˣ))
                (fun k => weyl (R := F) (c' k) (c' k + 1)
                  (Nat.ne_of_lt (Nat.lt_succ_self (c' k))) (1 : Fˣ)))
              (fun _ : Fin 1 => weyl (R := F) i (i + 1) hik (1 : Fˣ)) := by
          funext k
          refine Fin.addCases (fun a => ?_) (fun b => ?_) k
          · refine Fin.addCases (fun a1 => ?_) (fun b1 => ?_) a <;>
              simp [Fin.append_left, Fin.append_right]
          · simp [Fin.append_right]
        have hprod : (List.ofFn fun k => weyl (R := F)
              ((Fin.append (Fin.append (fun _ : Fin 1 => i) c')
                (fun _ : Fin 1 => i)) k)
              (((Fin.append (Fin.append (fun _ : Fin 1 => i) c')
                (fun _ : Fin 1 => i)) k) + 1)
              (Nat.ne_of_lt (Nat.lt_succ_self _)) (1 : Fˣ)).prod =
            weyl (R := F) i (i + 1) hik (1 : Fˣ) *
              ((List.ofFn fun k => weyl (R := F) (c' k) (c' k + 1)
                (Nat.ne_of_lt (Nat.lt_succ_self (c' k))) (1 : Fˣ)).prod *
                weyl (R := F) i (i + 1) hik (1 : Fˣ)) := by
          rw [hfun, List.ofFn_fin_append, List.ofFn_fin_append,
            List.prod_append, List.prod_append]
          simp [mul_assoc]
        rw [← hpeel, hIH, hprod, ht0eq]
        group

/-- Unit-one generation for `i < j`: `weyl i j 1` is an adjacent unit-one
word times a finite-torus element. Distance `d = j - i - 1` fed to the peel
induction. -/
private theorem weyl_one_of_lt {n i j : ℕ} (hj : j < n)
    (hlt : i < j) :
    ∃ (m : ℕ) (c : Fin m → ℕ),
      (∀ k, c k + 1 < n) ∧
      ∃ t ∈ finiteTorusSubgroup (R := F) n,
        ∀ hij : i ≠ j,
          weyl (R := F) i j hij (1 : Fˣ) =
            (List.ofFn fun k => weyl (R := F) (c k) (c k + 1)
              (Nat.ne_of_lt (Nat.lt_succ_self (c k))) (1 : Fˣ)).prod * t := by
  have hdist : i + 1 + (j - i - 1) = j := by omega
  have hbound : i + 1 + (j - i - 1) < n := by omega
  obtain ⟨m, c, hc, t, ht, hW⟩ :=
    weyl_one_eq_adjacent_mul_torus (F := F) (j - i - 1) i hbound
  rw [hdist] at hW
  exact ⟨m, c, hc, t, ht, hW⟩

/-- Adjacent simple-Weyl generation modulo the finite Borel: for bounded
distinct `i, j < n` and `u : Fˣ`, `weyl i j u = b₁ * W * b₂` with Borel
`b₁, b₂` and `W` an explicit finite product of adjacent unit-one simple Weyl
lifts `weyl k (k + 1) 1` (`k + 1 < n`), the standard palindrome realizing
transposition `(i j)` of length `2 * |j - i| - 1`.
Purpose: one-file generation packet feeding the Lemma-25 word induction; the
conclusion directly supplies Borel witnesses for downstream iteration.
The `i < j` branch strips the unit once (`weyl u = torus u * weyl 1`) and
applies the peel induction; the `j < i` branch reduces by `weyl_swap` to the
same palindrome for `(j i) = (i j)`. Characteristic-two safe.
Nonclaims: no arbitrary finite-Weyl word factorization, no Lemma-25
iteration, no full Bruhat existence, no Matsumoto theorem, no target kernel
containment, no quotient injectivity, and no universal central extension. -/
public theorem weyl_eq_borel_mul_simpleWeyl_mul_borel {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (u : Fˣ) :
    ∃ (m : ℕ) (c : Fin m → ℕ),
      (∀ k, c k + 1 < n) ∧
      ∃ b₁ ∈ finiteBorelSubgroup (F := F) n,
      ∃ b₂ ∈ finiteBorelSubgroup (F := F) n,
        weyl (R := F) i j hij u =
          b₁ * (List.ofFn fun k => weyl (R := F) (c k) (c k + 1)
            (Nat.ne_of_lt (Nat.lt_succ_self (c k))) (1 : Fˣ)).prod * b₂ := by
  have hTle : finiteTorusSubgroup (R := F) n ≤ finiteBorelSubgroup (F := F) n :=
    finiteTorusSubgroup_le_finiteBorelSubgroup n
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have htu : torus (R := F) i j hij u ∈ finiteTorusSubgroup (R := F) n :=
      torus_mem_finiteTorusSubgroup hi hj hij u
    rw [weyl_eq_torus_mul_weyl_one hij u]
    obtain ⟨m, c, hc, t, ht, hW⟩ := weyl_one_of_lt (F := F) hj hlt
    have hW1 := hW hij
    exact ⟨m, c, hc, _, hTle htu, _, hTle ht, by rw [hW1, mul_assoc]⟩
  · have htu : torus (R := F) j i hij.symm (-u⁻¹) ∈
        finiteTorusSubgroup (R := F) n :=
      torus_mem_finiteTorusSubgroup hj hi _ _
    rw [weyl_swap (R := F) i j hij u, weyl_eq_torus_mul_weyl_one hij.symm (-u⁻¹)]
    obtain ⟨m, c, hc, t, ht, hW⟩ := weyl_one_of_lt (F := F) hi hgt
    have hW1 := hW hij.symm
    exact ⟨m, c, hc, _, hTle htu, _, hTle ht, by rw [hW1, mul_assoc]⟩

end StableSteinberg

end AlgebraicKTheory

end
