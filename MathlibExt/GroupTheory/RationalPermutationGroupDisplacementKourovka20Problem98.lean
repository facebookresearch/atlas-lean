/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Order.Interval.Finset.Nat

/-!
# Infinite displacement in rational permutation groups

Every subgroup of the permutations of the naturals isomorphic to the additive rationals contains
an element with infinitely many distinct integer displacements (Kourovka Notebook, Problem 20.98).
The proof counts orbit points of the permutation corresponding to `1 / r` for large `r`.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/RationalPermutationGroupDisplacementKourovka20Problem98Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.98 (N. M. Suchkov). UnsolvedMath record
UM-00701756 (`KOU-20.98`), dataset ulamai/UnsolvedMath v1.8.0.

Permutations act on Lean's `ℕ` (from `0`); shifting by one does not change the differences. The
Notebook's `ag` is the image of `a` under `g`, written `g a`; the differences are taken in `ℤ`. The
additive group of `ℚ` is `Multiplicative ℚ`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98Wanted

/-- **Suchkov's question on displacements in permutation groups isomorphic to the rationals
(Kourovka 20.98).** The statement that for every subgroup $G$ of the group of permutations of
$\mathbb{N} = \{0, 1, 2, \dots\}$ that is isomorphic to the additive group $(\mathbb{Q}, +)$,
there is an element $g \in G$ such that the set of displacements $\{a - g(a) : a \in \mathbb{N}\}$,
computed in $\mathbb{Z}$, is infinite.

Kourovka 20.98 (N. M. Suchkov) is stated for permutations of the positive integers; shifting by
one does not change the displacements. -/
def rationalPermutationGroupInfiniteDisplacement : Prop :=
  ∀ G : Subgroup (Equiv.Perm ℕ), Nonempty (G ≃* Multiplicative ℚ) →
    ∃ g ∈ G, {d : ℤ | ∃ a : ℕ, (a : ℤ) - (g a : ℤ) = d}.Infinite

private lemma exists_dist_bound (g : Equiv.Perm ℕ)
    (h : {d : ℤ | ∃ a : ℕ, (a : ℤ) - (g a : ℤ) = d}.Finite) :
    ∃ K : ℕ, ∀ a, Nat.dist a (g a) ≤ K := by
  obtain ⟨K, hK⟩ := (h.image Int.natAbs).bddAbove
  refine ⟨K, fun a ↦ ?_⟩
  have hle : ((a : ℤ) - (g a : ℤ)).natAbs ≤ K := hK ⟨_, ⟨a, rfl⟩, rfl⟩
  unfold Nat.dist
  omega

private lemma dist_pow_le (g : Equiv.Perm ℕ) {K : ℕ} (h : ∀ a, Nat.dist a (g a) ≤ K)
    (n a : ℕ) : Nat.dist a ((g ^ n) a) ≤ n * K := by
  induction n with
  | zero => simp [Equiv.Perm.one_apply]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Nat.succ_mul]
    exact (Nat.dist.triangle_inequality _ _ _).trans (Nat.add_le_add ih (h _))

/-- An infinite-order permutation has arbitrarily long orbit segments without repetitions.
A collision in the first `N` steps forces the factorial power to fix the starting point. -/
private lemma exists_long_orbit (g : Equiv.Perm ℕ) (N : ℕ) (hg : g ^ N.factorial ≠ 1) :
    ∃ a, ∀ i < N, ∀ j < N, (g ^ i) a = (g ^ j) a → i = j := by
  obtain ⟨a, ha⟩ : ∃ a, (g ^ N.factorial) a ≠ a := by
    by_contra! h
    exact hg (Equiv.ext h)
  refine ⟨a, fun i hi j hj hij ↦ ?_⟩
  wlog hle : i ≤ j generalizing i j
  · exact (this j hj i hi hij.symm (by omega)).symm
  by_contra hne
  have hfix : (g ^ (j - i)) a = a := by
    apply (g ^ i).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hle]
    exact hij.symm
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (show 0 < j - i by omega) (show j - i ≤ N by omega)
  apply ha
  rw [hm, pow_mul]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix m

/-- Packing a long orbit into an interval bounds how high a root of a bounded-displacement
permutation can be if the root itself has bounded displacement and infinite order. -/
private lemma root_degree_le (g : Equiv.Perm ℕ) {r K C : ℕ} (hr : 0 < r)
    (hK : ∀ a, Nat.dist a ((g ^ r) a) ≤ K) (hC : ∀ a, Nat.dist a (g a) ≤ C)
    (hg : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) : r ≤ 2 * K := by
  let M := 2 * (r * C) + 2
  let R := M * K + r * C
  obtain ⟨a, ha⟩ := exists_long_orbit g (r * M) (hg _ (Nat.factorial_pos _))
  have horbit (i : ℕ) (hi : i < r * M) : (g ^ i) a ∈ Finset.Icc (a - R) (a + R) := by
    have hq : i / r ≤ M := ((Nat.div_lt_iff_lt_mul hr).2 (Nat.mul_comm r M ▸ hi)).le
    have hs : i % r ≤ r := (Nat.mod_lt _ hr).le
    have hpow : (g ^ i) a = ((g ^ r) ^ (i / r)) ((g ^ (i % r)) a) := by
      rw [← Equiv.Perm.mul_apply, ← pow_mul, ← pow_add, Nat.div_add_mod]
    have hd : Nat.dist a ((g ^ i) a) ≤ R := by
      rw [hpow]
      calc
        _ ≤ _ := Nat.dist.triangle_inequality a ((g ^ (i % r)) a) _
        _ ≤ i % r * C + (i / r) * K :=
          Nat.add_le_add (dist_pow_le g hC _ _) (dist_pow_le (g ^ r) hK _ _)
        _ ≤ R := by
          rw [Nat.add_comm]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ hq) (Nat.mul_le_mul_right _ hs)
    simp only [Finset.mem_Icc]
    unfold Nat.dist at hd
    omega
  have hcard := Finset.le_card_of_inj_on_range (fun i ↦ (g ^ i) a) horbit ha
  rw [Nat.card_Icc] at hcard
  by_contra! h
  have hmul := Nat.mul_le_mul_right M (show 2 * K + 1 ≤ r by omega)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm K M] at hmul
  dsimp [R, M] at hcard hmul
  omega

/--
**Permutation groups isomorphic to the rationals have infinite displacement (Kourovka 20.98).**
For every subgroup $G$ of the group of permutations of $\mathbb{N} = \{0, 1, 2, \dots\}$ that is
isomorphic to the additive group $(\mathbb{Q}, +)$, there is an element $g \in G$ such that the
set of displacements $\{a - g(a) : a \in \mathbb{N}\}$, computed in $\mathbb{Z}$, is infinite.
That is, the answer to Kourovka Problem 20.98 is yes.

The 21st issue of the Kourovka Notebook marks 20.98 solved ("Yes, it must"), citing Suchkov,
Shlepkin and Taysnyov (2024).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.98 (N. M.
Suchkov); resolution: N. M. Suchkov, A. A. Shlepkin and D. A. Taysnyov, On the existence of
countable unlimited groups, Siberian Math. J. 65 (2024), no. 6, 1390-1394, abstract: the additive
group of the rationals is not isomorphic to a subgroup of the group of all limited permutations of
the naturals; Kourovka Notebook (21st issue), Problem 20.98: Yes, it must,
https://www.mathnet.ru/eng/smj7921.
-/
theorem rationalPermutationGroupInfiniteDisplacement_holds :
    rationalPermutationGroupInfiniteDisplacement := by
  intro G ⟨e⟩
  by_contra! h
  let φ := G.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have bounded (q : ℚ) := exists_dist_bound (φ (Multiplicative.ofAdd q))
    (h _ (e.symm (Multiplicative.ofAdd q)).property)
  obtain ⟨K, hK⟩ := bounded 1
  let r := 2 * K + 1
  have hr : 0 < r := Nat.succ_pos _
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  let g := φ (Multiplicative.ofAdd (r : ℚ)⁻¹)
  have hpow (n : ℕ) : g ^ n = φ (Multiplicative.ofAdd ((n : ℚ) * (r : ℚ)⁻¹)) := by
    rw [← nsmul_eq_mul, ofAdd_nsmul, map_pow]
  have hroot : g ^ r = φ (Multiplicative.ofAdd 1) := by rw [hpow, mul_inv_cancel₀ hr']
  obtain ⟨C, hC⟩ := bounded (r : ℚ)⁻¹
  have horder (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
    rw [hpow, ← map_one φ]
    exact fun he ↦ (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (inv_ne_zero hr'))
      (congrArg Multiplicative.toAdd (hφ he))
  have := root_degree_le g hr (hroot ▸ hK) hC horder
  omega

end MathlibExt.GroupTheory.RationalPermutationGroupDisplacementKourovka20Problem98Wanted
