/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import MathlibExt.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
public import MathlibExt.Combinatorics.Enumerative.MeshPatternStirlingRecursion
import MathlibExt.Combinatorics.Enumerative.MeshPatternGeneratingFunction
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

-- Helper: `Polynomial.C a` as a Nat cast in `Polynomial ℕ`.
-- Stated without the inner `Nat.cast` so it rewrites `C (m - 1)` directly
-- (plain `rw [Polynomial.C_eq_natCast]` fails to match in `ℕ[X]`).
private theorem poly_C_eq_natCast (a : ℕ) :
    (Polynomial.C a : Polynomial ℕ) = ((a : ℕ) : Polynomial ℕ) :=
  Polynomial.C_eq_natCast a

-- Helper N5: r-Stirling number at j + r is the coefficient of the shifted rising product.
private theorem rStirlingFirst_add_eq_coeff_prod_range (n r j : ℕ) :
    rStirlingFirst n (j + r) r =
      (∏ i ∈ Finset.range (n - r),
        ((Polynomial.X : Polynomial ℕ) + ((r + i : ℕ) : Polynomial ℕ))).coeff j := by
  unfold rStirlingFirst
  rw [Polynomial.coeff_X_pow_mul]
  have h : (∏ k ∈ Finset.Ico r n,
        ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) =
      (∏ i ∈ Finset.range (n - r),
        ((Polynomial.X : Polynomial ℕ) + ((r + i : ℕ) : Polynomial ℕ))) := by
    rw [Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    simp
  rw [h]

-- Helper N6: global maximum of a permutation exists and is unique.
private theorem perm_fin_exists_globalMax {n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin n)) : ∃ M : Fin n, ∀ h, σ h ≤ σ M := by
  obtain ⟨m, hm⟩ : ∃ m : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  obtain ⟨M, _, hM⟩ :=
    Finset.exists_max_image Finset.univ (fun i => σ i) ⟨m, Finset.mem_univ m⟩
  exact ⟨M, fun h => hM h (Finset.mem_univ h)⟩

private theorem perm_fin_globalMax_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (a b : Fin n) (ha : ∀ h, σ h ≤ σ a) (hb : ∀ h, σ h ≤ σ b) : a = b := by
  have h1 : σ b ≤ σ a := ha b
  have h2 : σ a ≤ σ b := hb a
  have heq : σ a = σ b := le_antisymm h2 h1
  exact Equiv.injective σ heq

-- Helper N8: distribution of a statistic = coefficients of its generating polynomial.
private theorem fintype_card_fiber_eq_coeff_sum_X_pow {α : Type*} [Fintype α]
    (f : α → ℕ) (j : ℕ) :
    Fintype.card {a // f a = j} =
      (∑ a, (Polynomial.X : Polynomial ℕ) ^ f a).coeff j := by
  classical
  rw [Polynomial.finsetSum_coeff Finset.univ]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  rw [Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [eq_comm]

private def meshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (∀ h : Fin n, h < i → σ h < σ i) ∧
    k - 1 ≤ (Finset.univ.filter fun q : Fin n =>
      i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q).card

private instance decMeshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    DecidablePred (meshWantedMatch k σ) := fun i => by
  unfold meshWantedMatch
  infer_instance

private def meshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) ∧ k ≤ m.val + 1

private instance decMeshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Decidable (meshWantedZero k σ) := by
  unfold meshWantedZero
  infer_instance

private def meshWantedCount (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (meshWantedMatch k σ)).card +
    (if meshWantedZero k σ then 1 else 0)

-- Helper N2: insertion recurrence for the canonical polynomial.
private theorem meshPoly_step (k m : ℕ) (hk : 1 < k) (hm : k ≤ m) :
    PolyN m k =
      (Polynomial.X + (((m - 1 : ℕ)) : Polynomial ℕ)) * PolyN (m - 1) k := by
  have h : PolyN m k =
      (Polynomial.X + Polynomial.C (m - 1)) * PolyN (m - 1) k :=
    (meshPatternCount_stirlingRecursion k m 1 hk hm one_pos).2.1
  rwa [poly_C_eq_natCast] at h

-- Helper N3: base case for the canonical polynomial.
private theorem meshPoly_base (k : ℕ) (hk : 1 < k) :
    PolyN (k - 1) k = ((((k - 1).factorial : ℕ)) : Polynomial ℕ) := by
  have h : PolyN (k - 1) k = Polynomial.C ((k - 1).factorial) :=
    (meshPatternCount_stirlingRecursion k k 1 hk le_rfl one_pos).2.2.2
  rwa [poly_C_eq_natCast] at h

-- Helper N4: closed product form for the canonical polynomial.
private theorem meshPoly_eq_factorial_mul_prod (n k : ℕ) (hkn : k ≤ n) (hk : 2 ≤ k) :
    PolyN n k =
      ((((k - 1).factorial : ℕ)) : Polynomial ℕ) *
        ∏ i ∈ Finset.range (n - k + 1),
          (Polynomial.X + ((((k - 1 + i : ℕ))) : Polynomial ℕ)) := by
  have hk1 : 1 < k := by omega
  have hk0 : 0 < k := by omega
  exact meshPatternGeneratingFunction_eq_factorial_mul_prod_general PolyN n k
    Polynomial.X hk0 hkn (meshPoly_base k hk1)
    (fun m hm => meshPoly_step k m hk1 hm)

-- Helper N7: the Wanted statistic equals the canonical statistic.
private theorem meshWantedCount_eq_meshN {n k : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin n)) :
    meshWantedCount k σ = meshN k σ := by
  obtain ⟨M, hM⟩ := perm_fin_exists_globalMax hn σ
  have hsub : ∀ q : Fin n,
      (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ↔ q < M := by
    intro q
    constructor
    · intro h
      exact h M hM
    · intro hqm m hm
      have hmM : m = M := perm_fin_globalMax_unique σ m M hm hM
      rw [hmM]
      exact hqm
  have hfil : ∀ i : Fin n,
      (Finset.univ.filter fun t : Fin n => i < t ∧ t < M ∧ σ i < σ t) =
        (Finset.univ.filter fun q : Fin n =>
          i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q) := by
    intro i
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hiq, hqM, hlt⟩
      exact ⟨hiq, (hsub q).mpr hqM, hlt⟩
    · rintro ⟨hiq, hq, hlt⟩
      exact ⟨hiq, (hsub q).mp hq, hlt⟩
  have hpw : ∀ i : Fin n, meshWantedMatch k σ i ↔ MatchPred k σ i := by
    intro i
    unfold meshWantedMatch MatchPred
    constructor
    · rintro ⟨hltr, hcard⟩
      refine ⟨M, hM, ?_, hltr⟩
      rw [hfil i]
      exact hcard
    · rintro ⟨maxIndex, hmax, hcard, hltr⟩
      have hMM : maxIndex = M := perm_fin_globalMax_unique σ maxIndex M hmax hM
      subst hMM
      refine ⟨hltr, ?_⟩
      rw [← hfil i]
      exact hcard
  have houter : (Finset.univ.filter (meshWantedMatch k σ)) =
      (Finset.univ.filter (MatchPred k σ)) := by
    apply Finset.filter_congr
    intro i _
    exact hpw i
  -- The two zero predicates are the same proposition up to bound-variable
  -- names (and defeq decidability instances), so `congr` closes the goal.
  unfold meshWantedCount meshN
  rw [houter]
  congr 1

-- Helper N9: the Wanted generating sum equals the canonical polynomial.
private theorem sum_X_pow_meshWantedCount_eq_PolyN {n k : ℕ} (hn : 0 < n) :
    (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshWantedCount k σ) =
      PolyN n k := by
  show (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshWantedCount k σ) =
    ∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshN k σ
  apply Finset.sum_congr rfl
  intro σ _
  rw [meshWantedCount_eq_meshN hn σ]

/--
**Distribution of the canonical mesh-pattern statistic.** Let $2 \le k \le n$ and let $j$ be a
natural number. For a permutation $\sigma$ of $\{1, \dots, n\}$ with positions numbered
$1, \dots, n$, let $p$ be the position of its largest value, and let $N_k(\sigma)$ be the
canonical mesh-pattern statistic: the number of positions $i$ such that $\sigma(t) < \sigma(i)$
for all $t < i$ and at least $k - 1$ positions $t$ with $i < t < p$ have $\sigma(t) > \sigma(i)$,
plus $1$ if $p \ge k$. Then the number of permutations $\sigma$ of $\{1, \dots, n\}$ with
$N_k(\sigma) = j$ equals $(k-1)!\, c_{k-1}(n, j + k - 1)$, where the unsigned $r$-Stirling
number of the first kind $c_r(n, m)$ is the coefficient of $X^m$ in
$X^r (X + r)(X + r + 1) \cdots (X + n - 1)$.
-/
theorem meshPatternCount_eq_factorial_mul_rStirlingNumber_general
    (n k j : ℕ) (hkn : k ≤ n) (hk : 2 ≤ k) :
    Fintype.card {σ : Equiv.Perm (Fin n) // meshN k σ = j} =
      (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1) := by
  have hsum : (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshN k σ) =
      PolyN n k := rfl
  rw [fintype_card_fiber_eq_coeff_sum_X_pow]
  rw [hsum]
  rw [meshPoly_eq_factorial_mul_prod n k hkn hk]
  rw [Polynomial.coeff_natCast_mul]
  simp only [Nat.cast_id]
  have hjk : j + k - 1 = j + (k - 1) := by omega
  rw [hjk]
  rw [rStirlingFirst_add_eq_coeff_prod_range n (k - 1) j]
  have hrange : n - (k - 1) = n - k + 1 := by omega
  rw [hrange]

/--
**Counting permutations by mesh-pattern matches.** Let $2 \le k \le n$ and let $j$ be a
natural number. For a permutation $\sigma$ of $\{1, \dots, n\}$, let $p$ be the position of its
largest entry, and call a position $i$ a match if $\sigma(t) < \sigma(i)$ for every position
$t < i$ and at least $k - 1$ positions $q$ with $i < q < p$ have $\sigma(q) > \sigma(i)$. Let
$N(\sigma)$ be the number of matches, plus $1$ if $p \ge k$. Then the number of permutations
$\sigma$ of $\{1, \dots, n\}$ with $N(\sigma) = j$ equals $(k-1)!\, c_{k-1}(n, j + k - 1)$, where
the unsigned $r$-Stirling number of the first kind $c_r(n, m)$ is the coefficient of $X^m$ in
$X^r (X + r)(X + r + 1) \cdots (X + n - 1)$.

Source: Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers", Journal of Integer Sequences 18 (2015), Article 15.10.1, Theorem `thm:rstir`, line 201, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.

Proves `Wanted` entry `meshPatternCount_eq_factorial_mul_rStirlingNumber`.
-/
theorem meshPatternCount_eq_factorial_mul_rStirlingNumber
    (n k j : ℕ) (hkn : k ≤ n) (hk : 2 ≤ k) :
    let isLeftToRightMaximum := fun (σ : Equiv.Perm (Fin n)) (i : Fin n) =>
      ∀ h : Fin n, h < i → σ h < σ i
    let isGlobalMaximum := fun (σ : Equiv.Perm (Fin n)) (i : Fin n) =>
      ∀ h : Fin n, σ h ≤ σ i
    let matchesMeshPattern := fun (σ : Equiv.Perm (Fin n)) (i : Fin n) =>
      isLeftToRightMaximum σ i ∧
        k - 1 ≤ (Finset.univ.filter fun q : Fin n =>
          i < q ∧
            (∀ m : Fin n, isGlobalMaximum σ m → q < m) ∧
            σ i < σ q).card
    Fintype.card {σ : Equiv.Perm (Fin n) //
        (Finset.univ.filter (matchesMeshPattern σ)).card +
          (if ∃ m : Fin n, isGlobalMaximum σ m ∧ k ≤ m.val + 1 then 1 else 0) = j} =
      (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1) := by
  have hn : 0 < n := by omega
  change Fintype.card {σ : Equiv.Perm (Fin n) // meshWantedCount k σ = j} =
    (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1)
  simp only [meshWantedCount_eq_meshN hn]
  exact meshPatternCount_eq_factorial_mul_rStirlingNumber_general n k j hkn hk

end MetaMathlibExt
end
