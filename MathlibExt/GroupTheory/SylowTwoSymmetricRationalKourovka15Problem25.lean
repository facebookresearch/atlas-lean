/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Rationality of Sylow 2-subgroups of symmetric groups of degree a power of two

Every element of a Sylow 2-subgroup of the symmetric group on `2 ^ n` points is conjugate
within that subgroup to each power whose exponent is coprime to its order. Following the solution to
Kourovka Problem 15.25, we prove conjugacy to odd powers by induction on the iterated wreath
product with the group of order two.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/SylowTwoSymmetricRationalKourovka15Problem25Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.25 (Ya. G.
Berkovich). UnsolvedMath record UM-00701113 (`KOU-15.25`), dataset ulamai/UnsolvedMath v1.8.0.

Rationality is stated through the standard equivalent conjugacy criterion: a finite group is
rational if and only if every element `g` is conjugate to `gᵏ` for every `k` coprime to the order of
`g`. Conjugacy is taken inside the Sylow subgroup itself. Every `n ≥ 0` is included (`n = 0, 1` give
groups of order `1` and `2`).
-/

public section

namespace MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted

@[expose] section

/-- **Rational group (conjugacy form, Kourovka 15.25).** A group $G$ is rational when every element
$g \in G$ is conjugate in $G$ to $g^k$ for every natural number $k$ coprime to the order of $g$ (an
element of infinite order counts as having order $0$, so for it only $k = 1$ qualifies).

For finite groups this is equivalent to every irreducible complex character taking only rational
values. -/
def IsRationalGroup (G : Type*) [Group G] : Prop :=
  ∀ (g : G) (k : ℕ), k.Coprime (orderOf g) → IsConj g (g ^ k)

/-- **Kourovka Problem 15.25 (statement).** The statement that for every natural number $n$, every
Sylow $2$-subgroup $P$ of the symmetric group $S_{2^n}$ on $2^n$ points is rational as a group in
its own right: every $g \in P$ is conjugate within $P$ to $g^k$ for every natural number $k$ coprime
to the order of $g$. -/
def sylowTwoSubgroupSymmetricRational : Prop :=
  ∀ (n : ℕ) (P : Sylow 2 (Equiv.Perm (Fin (2 ^ n)))),
    IsRationalGroup (P : Subgroup (Equiv.Perm (Fin (2 ^ n))))

end

open RegularWreathProduct

variable {G : Type*} [Group G]

private lemma right_pow (x : G ≀ᵣ ℤˣ) (k : ℕ) : (x ^ k).right = x.right ^ k :=
  map_pow (rightHom : G ≀ᵣ ℤˣ →* ℤˣ) x k

-- Powers in the base group are computed separately in each coordinate.
private lemma left_pow_of_right_one (x : G ≀ᵣ ℤˣ) (hx : x.right = 1) (k : ℕ) (i : ℤˣ) :
    (x ^ k).left i = x.left i ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, right_pow, hx, ih]

-- In the other coset, the conjugacy class is determined by the product of the two coordinates.
private lemma isConj_of_isConj_product (x y : G ≀ᵣ ℤˣ) (hx : x.right = -1) (hy : y.right = -1)
    (h : IsConj (x.left 1 * x.left (-1)) (y.left 1 * y.left (-1))) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hprod := mul_inv_eq_iff_eq_mul.mp hc
  let d : G ≀ᵣ ℤˣ := ⟨fun i ↦ if i = 1 then c else (y.left 1)⁻¹ * c * x.left 1, 1⟩
  refine isConj_iff.mpr ⟨d, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply RegularWreathProduct.ext
  · funext i
    rcases Int.units_eq_one_or i with rfl | rfl
    · simp [d, hy, mul_assoc]
    · simpa [d, hy, mul_assoc] using congrArg ((y.left 1)⁻¹ * ·) hprod
  · simp [d, hx, hy]

private lemma wreath_odd_pow (k : ℕ) (hk : Odd k) (ih : ∀ a : G, IsConj a (a ^ k))
    (x : G ≀ᵣ ℤˣ) : IsConj x (x ^ k) := by
  rcases Int.units_eq_one_or x.right with hx | hx
  · choose c hc using fun i ↦ isConj_iff.mp (ih (x.left i))
    refine isConj_iff.mpr ⟨⟨c, 1⟩, ?_⟩
    apply RegularWreathProduct.ext
    · funext i
      simpa [hx, left_pow_of_right_one x hx] using hc i
    · simp [hx, right_pow]
  · have hy : (x ^ k).right = -1 := by rw [right_pow, hx, hk.neg_one_pow]
    apply isConj_of_isConj_product x (x ^ k) hx hy
    -- Squaring returns to the base group. Its first coordinate is the product in question.
    have hsq : (x ^ 2).right = 1 := by simp [sq, hx]
    have hp := left_pow_of_right_one (x ^ 2) hsq k 1
    rw [← pow_mul, Nat.mul_comm, pow_mul] at hp
    have hprod := ih ((x ^ 2).left 1)
    rw [← hp] at hprod
    simpa [sq, hx, hy] using hprod

private lemma iterated_odd_pow (n k : ℕ) (hk : Odd k) (x : IteratedWreathProduct ℤˣ n) :
    IsConj x (x ^ k) := by
  induction n with
  | zero =>
    have : Subsingleton (IteratedWreathProduct ℤˣ 0) := inferInstanceAs (Subsingleton PUnit)
    rw [Subsingleton.elim (x ^ k) x]
  | succ n ih => exact wreath_odd_pow k hk ih x

/--
**Sylow 2-subgroups of the symmetric groups of degree $2^n$ are rational (Kourovka 15.25).** For
every natural number $n$, every Sylow $2$-subgroup $P$ of the symmetric group $S_{2^n}$ on $2^n$
points is rational as a group in its own right: every $g \in P$ is conjugate within $P$ to $g^k$ for
every natural number $k$ coprime to the order of $g$.

A Sylow $2$-subgroup $T_n$ of $S_{2^n}$ is the wreath product of $T_{n-1}$ with a group of order
$2$, which is rational when $T_{n-1}$ is (Kletzing, Corollary 70), so induction on $n$ applies.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.25 (Ya. G.
Berkovich); resolution: A. Mann, letter of 1 October 2002, as recorded in the Kourovka Archive,
Problem 15.25, using D. Kletzing, Structure and representations of Q-groups, Lecture Notes in Math.
1084, Springer, Berlin, 1984, Corollary 70, Kourovka Archive, Problem 15.25 (answer: Yes, they are;
T_n = T_(n-1) wr C_2 and wreath products with C_2 preserve rationality),
https://arxiv.org/abs/1401.0300v49.
-/
theorem sylowTwoSubgroupSymmetricRational_holds : sylowTwoSubgroupSymmetricRational := by
  intro n P g k hk
  by_cases hg : g = 1
  · simp [hg]
  have hodd := (hk.coprime_dvd_right (P.isPGroup.dvd_orderOf hg)).odd_of_right
  let e := Sylow.mulEquivIteratedWreathProduct 2 n _ (Nat.card_fin _) ℤˣ
    (by simp [Nat.card_eq_fintype_card]) P
  simpa using e.symm.toMonoidHom.map_isConj (iterated_odd_pow n k hodd (e g))

end MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted
