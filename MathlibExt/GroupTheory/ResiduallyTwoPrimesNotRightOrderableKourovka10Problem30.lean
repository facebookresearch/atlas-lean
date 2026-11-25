/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import MathlibExt.GroupTheory.ResiduallyFiniteP
public import MathlibExt.GroupTheory.RightOrderable
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.NumberTheory.Basic

/-!
# Non-right-orderable groups residually `p` for two primes (Kourovka Notebook Problem 10.30)

Kourovka Notebook, Archive of Solved Problems, Problem 10.30 (N. Ya. Medvedev): does there exist a
non-right-orderable group which is residually a finite `p`-group for a finite set of primes `p`
containing at least two different primes?

Linnell's answer is yes, and this file follows his proof of Theorem 1. The principal congruence
subgroup `congruenceSubgroup n m` of level `m` of `GL n ℤ` is residually a finite `p`-group for
every prime `p ∣ m` (`isResiduallyFiniteP_congruenceSubgroup`), and for `m ≠ 0` the congruence
subgroup of level `m` of `GL₃(ℤ)` is not right-orderable
(`not_isRightOrderable_congruenceSubgroup`). The level `6` gives
`residuallyTwoPrimesNotRightOrderable_holds`.

Linnell deduces non-right-orderability from Witte's theorem that no finite-index subgroup of
`SL(n, ℤ)`, `n ≥ 3`, is left-orderable. Here Witte's argument is carried out directly for the six
elementary matrices `1 + m E_{ij}`, `i ≠ j`, of the congruence subgroup. In a right-ordered group,
if `x * y = z ^ k * (y * x)` with `k ≠ 0` and `z ≠ 1` commuting with `x` and `y`, then the larger
of `z` and `z⁻¹` is smaller than the largest of `x`, `x⁻¹`, `y` and `y⁻¹` (a weak form of a lemma
of Ault and Rhemtulla). Each of the six matrices is such a `z` for two of the others, which is
impossible for the one whose larger of itself and its inverse is largest.

## References

* P. A. Linnell, *Right orderable residually finite p-groups and a Kourovka notebook problem*,
  J. Algebra 248 (2002), 605-607, arXiv:math/0107094, Theorem 1 and its proof.
* D. Witte Morris, *Can lattices in SL(n,ℝ) act on the circle?*, arXiv:0811.0051, Lemma 3.6 and
  the proof of Theorem 3.1 (Witte's theorem).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.30 (N. Ya.
Medvedev). UnsolvedMath record UM-00700645 (`KOU-10.30`), dataset ulamai/UnsolvedMath v1.8.0.

A group that is residually a finite `p`-group for every prime of a finite set with two distinct
primes `p ≠ q` is residually `p` and residually `q`, so the statement uses two distinct primes; such
a group is torsion-free, so there is no trivial witness. Right-orderable means that some linear
order is invariant under right multiplication.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsResiduallyFiniteP)

/-- **Medvedev's question on right-orderability (Kourovka 10.30).** The statement that there exist
a group $G$ and distinct primes $p$ and $q$ such that $G$ is residually a finite $p$-group and
residually a finite $q$-group, but $G$ is not right-orderable. -/
def residuallyTwoPrimesNotRightOrderable : Prop :=
  ∃ (G : Type) (_ : Group G) (p q : ℕ), p.Prime ∧ q.Prime ∧ p ≠ q ∧
    IsResiduallyFiniteP p G ∧ IsResiduallyFiniteP q G ∧ ¬ IsRightOrderable G

open Matrix

/-! ### Heisenberg relations in right-ordered groups -/

section RightOrdered

variable {G : Type*} [Group G]

/-- If `x * y = Z * (y * x)` and `Z` commutes with `y`, then `x * y ^ n = Z ^ n * (y ^ n * x)`. -/
private theorem heisenberg_pow_right {x y Z : G} (hZy : Commute Z y)
    (hxy : x * y = Z * (y * x)) : ∀ n : ℕ, x * y ^ n = Z ^ n * (y ^ n * x)
  | 0 => by simp
  | n + 1 => by
    have ih := heisenberg_pow_right hZy hxy n
    have hc : y ^ n * Z = Z * y ^ n := ((hZy.pow_right n).eq).symm
    calc x * y ^ (n + 1) = (x * y ^ n) * y := by rw [pow_succ, mul_assoc]
      _ = Z ^ n * (y ^ n * (x * y)) := by rw [ih]; simp only [mul_assoc]
      _ = Z ^ n * ((y ^ n * Z) * (y * x)) := by rw [hxy]; simp only [mul_assoc]
      _ = Z ^ (n + 1) * (y ^ (n + 1) * x) := by
        rw [hc, pow_succ Z n, pow_succ y n]; simp only [mul_assoc]

/-- The commutator identity `[x ^ m, y ^ n] = [x, y] ^ (m * n)` when `[x, y]` is central in
`⟨x, y⟩`, written as `x ^ m * y ^ n = Z ^ (m * n) * (y ^ n * x ^ m)`. -/
private theorem heisenberg_pow {x y Z : G} (hZx : Commute Z x) (hZy : Commute Z y)
    (hxy : x * y = Z * (y * x)) (n : ℕ) : ∀ m : ℕ, x ^ m * y ^ n = Z ^ (m * n) * (y ^ n * x ^ m)
  | 0 => by simp
  | m + 1 => by
    have ih := heisenberg_pow hZx hZy hxy n m
    have hc : x * Z ^ (m * n) = Z ^ (m * n) * x := ((hZx.pow_left (m * n)).eq).symm
    calc x ^ (m + 1) * y ^ n = x * (x ^ m * y ^ n) := by rw [pow_succ', mul_assoc]
      _ = (x * Z ^ (m * n)) * (y ^ n * x ^ m) := by rw [ih, mul_assoc]
      _ = Z ^ (m * n) * ((x * y ^ n) * x ^ m) := by rw [hc]; simp only [mul_assoc]
      _ = Z ^ ((m + 1) * n) * (y ^ n * x ^ (m + 1)) := by
        rw [heisenberg_pow_right hZy hxy n, Nat.succ_mul, pow_add, pow_succ']
        simp only [mul_assoc]

variable [LinearOrder G] (h : ∀ a b c : G, a ≤ b → a * c ≤ b * c)
include h

private theorem le_of_mul_le_mul_right_of_rightInvariant {a b : G} (c : G)
    (hab : a * c ≤ b * c) : a ≤ b := by
  simpa using h _ _ c⁻¹ hab

private theorem mul_lt_mul_right_of_rightInvariant {a b : G} (c : G) (hab : a < b) :
    a * c < b * c :=
  lt_of_le_of_ne (h _ _ c hab.le) (fun he => hab.ne (mul_right_cancel he))

private theorem pow_le_pow_of_commute {a b : G} (hab : a ≤ b) (hc : Commute a b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    calc a ^ (n + 1) = a ^ n * a := pow_succ a n
      _ ≤ b ^ n * a := h _ _ _ (pow_le_pow_of_commute hab hc n)
      _ = a * b ^ n := ((hc.pow_right n).eq).symm
      _ ≤ b * b ^ n := h _ _ _ hab
      _ = b ^ (n + 1) := (pow_succ' b n).symm

private theorem one_lt_pow_succ_of_one_lt {a : G} (ha : 1 < a) : ∀ n : ℕ, 1 < a ^ (n + 1)
  | 0 => by simpa using ha
  | n + 1 => by
    calc (1 : G) < a ^ (n + 1) := one_lt_pow_succ_of_one_lt ha n
      _ = 1 * a ^ (n + 1) := (one_mul _).symm
      _ < a * a ^ (n + 1) := mul_lt_mul_right_of_rightInvariant h _ ha
      _ = a ^ (n + 1 + 1) := (pow_succ' a _).symm

private theorem pow_mul_pow_le {x y Z : G} (hZx : Commute Z x) (hZy : Commute Z y)
    (hx : x ≤ Z) (hy : y ≤ Z) (n : ℕ) : x ^ n * y ^ n ≤ Z ^ (n + n) := by
  calc x ^ n * y ^ n ≤ Z ^ n * y ^ n := h _ _ _ (pow_le_pow_of_commute h hx hZx.symm n)
    _ = y ^ n * Z ^ n := (hZy.pow_pow n n).eq
    _ ≤ Z ^ n * Z ^ n := h _ _ _ (pow_le_pow_of_commute h hy hZy.symm n)
    _ = Z ^ (n + n) := (pow_add Z n n).symm

private theorem inv_le_of_inv_le_of_commute {x Z : G} (hZx : Commute Z x) (hx : x⁻¹ ≤ Z) :
    Z⁻¹ ≤ x :=
  calc Z⁻¹ = x⁻¹ * (x * Z⁻¹) := (inv_mul_cancel_left x Z⁻¹).symm
    _ ≤ Z * (x * Z⁻¹) := h _ _ _ hx
    _ = x := by rw [← mul_assoc, hZx.eq, mul_inv_cancel_right]

/-- A central commutator `Z = [x, y] > 1` cannot bound `x`, `x⁻¹`, `y` and `y⁻¹` from above: the
identity `x ^ 5 * y ^ 5 = Z ^ 25 * (y ^ 5 * x ^ 5)` would give `Z ^ 15 ≤ Z ^ 10`. -/
private theorem heisenberg_false {x y Z : G} (hZ : 1 < Z) (hZx : Commute Z x)
    (hZy : Commute Z y) (hxy : x * y = Z * (y * x)) (hx : x ≤ Z) (hx' : x⁻¹ ≤ Z) (hy : y ≤ Z)
    (hy' : y⁻¹ ≤ Z) : False := by
  have hup : x ^ 5 * y ^ 5 ≤ Z ^ 10 := pow_mul_pow_le h hZx hZy hx hy 5
  have hlow : Z⁻¹ ^ 10 ≤ y ^ 5 * x ^ 5 := by
    have h₁ : Z⁻¹ ^ 5 ≤ x ^ 5 :=
      pow_le_pow_of_commute h (inv_le_of_inv_le_of_commute h hZx hx') hZx.inv_left 5
    have h₂ : Z⁻¹ ^ 5 ≤ y ^ 5 :=
      pow_le_pow_of_commute h (inv_le_of_inv_le_of_commute h hZy hy') hZy.inv_left 5
    calc Z⁻¹ ^ 10 = Z⁻¹ ^ 5 * Z⁻¹ ^ 5 := by rw [← pow_add]
      _ ≤ x ^ 5 * Z⁻¹ ^ 5 := h _ _ _ h₁
      _ = Z⁻¹ ^ 5 * x ^ 5 := ((hZx.inv_left.pow_pow 5 5).eq).symm
      _ ≤ y ^ 5 * x ^ 5 := h _ _ _ h₂
  have hcomm : Commute (Z ^ 25) (y ^ 5 * x ^ 5) :=
    (hZy.pow_pow 25 5).mul_right (hZx.pow_pow 25 5)
  have key : Z ^ 15 ≤ Z ^ 10 := by
    calc Z ^ 15 = Z⁻¹ ^ 10 * Z ^ 25 := by
          rw [inv_pow, show 25 = 10 + 15 from rfl, pow_add, inv_mul_cancel_left]
      _ ≤ (y ^ 5 * x ^ 5) * Z ^ 25 := h _ _ _ hlow
      _ = Z ^ 25 * (y ^ 5 * x ^ 5) := hcomm.eq.symm
      _ = x ^ 5 * y ^ 5 := (heisenberg_pow hZx hZy hxy 5 5).symm
      _ ≤ Z ^ 10 := hup
  have h₅ : Z ^ 5 ≤ 1 := by
    apply le_of_mul_le_mul_right_of_rightInvariant h (Z ^ 10)
    rwa [← pow_add, one_mul]
  exact absurd h₅ (not_le.mpr (one_lt_pow_succ_of_one_lt h hZ 4))

/-- **Central commutators are small (after Ault and Rhemtulla).** In a right-ordered group, if
`x * y = z ^ k * (y * x)` with `k ≠ 0`, `z ≠ 1` and `z` commuting with `x` and `y`, then
`max z z⁻¹ < max (max x x⁻¹) (max y y⁻¹)`. -/
private theorem max_inv_lt_max_max {x y z : G} {k : ℕ} (hk : k ≠ 0) (hzx : Commute z x)
    (hzy : Commute z y) (hxy : x * y = z ^ k * (y * x)) (hz : z ≠ 1) :
    max z z⁻¹ < max (max x x⁻¹) (max y y⁻¹) := by
  by_contra! hcon
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  have hC : 1 < max z z⁻¹ := by
    rcases lt_or_gt_of_ne hz with hz₁ | hz₁
    · exact lt_max_of_lt_right (by simpa using mul_lt_mul_right_of_rightInvariant h z⁻¹ hz₁)
    · exact lt_max_of_lt_left hz₁
  have hCZ : max z z⁻¹ ≤ max z z⁻¹ ^ (j + 1) := by
    calc max z z⁻¹ = 1 * max z z⁻¹ := (one_mul _).symm
      _ ≤ max z z⁻¹ ^ j * max z z⁻¹ := by
          refine h _ _ _ ?_
          simpa using pow_le_pow_of_commute h hC.le (Commute.one_left _) j
      _ = max z z⁻¹ ^ (j + 1) := (pow_succ _ j).symm
  have hZ : 1 < max z z⁻¹ ^ (j + 1) := one_lt_pow_succ_of_one_lt h hC j
  have hx : max x x⁻¹ ≤ max z z⁻¹ ^ (j + 1) := ((le_max_left _ _).trans hcon).trans hCZ
  have hy : max y y⁻¹ ≤ max z z⁻¹ ^ (j + 1) := ((le_max_right _ _).trans hcon).trans hCZ
  rcases max_choice z z⁻¹ with hCz | hCz <;> rw [hCz] at hZ hx hy
  · exact heisenberg_false h hZ (hzx.pow_left _) (hzy.pow_left _) hxy
      ((le_max_left _ _).trans hx) ((le_max_right _ _).trans hx)
      ((le_max_left _ _).trans hy) ((le_max_right _ _).trans hy)
  · refine heisenberg_false h hZ (hzy.inv_left.pow_left _) (hzx.inv_left.pow_left _) ?_
      ((le_max_left _ _).trans hy) ((le_max_right _ _).trans hy)
      ((le_max_left _ _).trans hx) ((le_max_right _ _).trans hx)
    rw [inv_pow, hxy, inv_mul_cancel_left]

end RightOrdered

section Elementary

/-- Six elements of a linear order, each strictly below the larger of two others in this cyclic
pattern, cannot exist: the largest of them would be below itself. -/
private theorem false_of_lt_max_six {α : Type*} [LinearOrder α] {a₀₁ a₀₂ a₁₀ a₁₂ a₂₀ a₂₁ : α}
    (h₁ : a₀₂ < max a₀₁ a₁₂) (h₂ : a₀₁ < max a₀₂ a₂₁) (h₃ : a₁₂ < max a₁₀ a₀₂)
    (h₄ : a₁₀ < max a₁₂ a₂₀) (h₅ : a₂₁ < max a₂₀ a₀₁) (h₆ : a₂₀ < max a₂₁ a₁₀) : False := by
  set M := max (max (max a₀₁ a₀₂) (max a₁₀ a₁₂)) (max a₂₀ a₂₁) with hM
  have l₀₁ : a₀₁ ≤ M := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have l₀₂ : a₀₂ ≤ M := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have l₁₀ : a₁₀ ≤ M := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have l₁₂ : a₁₂ ≤ M := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have l₂₀ : a₂₀ ≤ M := le_max_of_le_right (le_max_left _ _)
  have l₂₁ : a₂₁ ≤ M := le_max_of_le_right (le_max_right _ _)
  refine lt_irrefl M ?_
  conv_lhs => rw [hM]
  exact max_lt (max_lt (max_lt (h₂.trans_le (max_le l₀₂ l₂₁)) (h₁.trans_le (max_le l₀₁ l₁₂)))
    (max_lt (h₄.trans_le (max_le l₁₂ l₂₀)) (h₃.trans_le (max_le l₁₀ l₀₂))))
    (max_lt (h₆.trans_le (max_le l₂₁ l₁₀)) (h₅.trans_le (max_le l₂₀ l₀₁)))

variable {G : Type*} [Group G]

/-- **Witte's argument.** A group is not right-orderable if it contains elements `u i j`,
`i ≠ j` in `Fin 3`, different from `1`, satisfying the commutation relations of the elementary
matrices `1 + m E_{ij}` of `SL(3, ℤ)`. -/
private theorem not_isRightOrderable_of_elementary {k : ℕ} (hk : k ≠ 0)
    (u : ∀ i j : Fin 3, i ≠ j → G)
    (hrel : ∀ i j l (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      u i j hij * u j l hjl = u i l hil ^ k * (u j l hjl * u i j hij))
    (hcomm₁ : ∀ i j l (hij : i ≠ j) (hil : i ≠ l), j ≠ l → Commute (u i l hil) (u i j hij))
    (hcomm₂ : ∀ i j l (hjl : j ≠ l) (hil : i ≠ l), i ≠ j → Commute (u i l hil) (u j l hjl))
    (hne : ∀ i l (hil : i ≠ l), u i l hil ≠ 1) : ¬ IsRightOrderable G := by
  rintro ⟨_, h⟩
  have key : ∀ i j l (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      max (u i l hil) (u i l hil)⁻¹ <
        max (max (u i j hij) (u i j hij)⁻¹) (max (u j l hjl) (u j l hjl)⁻¹) :=
    fun i j l hij hjl hil => max_inv_lt_max_max h hk (hcomm₁ i j l hij hil hjl)
      (hcomm₂ i j l hjl hil hij) (hrel i j l hij hjl hil) (hne i l hil)
  have h₁ := key 0 1 2 (by decide) (by decide) (by decide)
  have h₂ := key 0 2 1 (by decide) (by decide) (by decide)
  have h₃ := key 1 0 2 (by decide) (by decide) (by decide)
  have h₄ := key 1 2 0 (by decide) (by decide) (by decide)
  have h₅ := key 2 0 1 (by decide) (by decide) (by decide)
  have h₆ := key 2 1 0 (by decide) (by decide) (by decide)
  exact false_of_lt_max_six h₁ h₂ h₃ h₄ h₅ h₆

end Elementary

/-! ### Congruence subgroups are residually `p` -/

/-- **Principal congruence subgroups of $\mathrm{GL}_n(\mathbb{Z})$.** For a natural number $m$,
the principal congruence subgroup of level $m$ is the kernel of reduction modulo $m$,
$\mathrm{GL}_n(\mathbb{Z}) \to \mathrm{GL}_n(\mathbb{Z}/m\mathbb{Z})$: the integer matrices
congruent to the identity modulo $m$ (`mem_congruenceSubgroup_iff`). For $m = 0$ it is trivial
and for $m = 1$ it is all of $\mathrm{GL}_n(\mathbb{Z})$.

Source: P. A. Linnell, Right orderable residually finite p-groups and a Kourovka notebook problem,
J. Algebra 248 (2002), 605-607, arXiv:math/0107094, proof of Theorem 1. -/
def congruenceSubgroup (n : Type*) [Fintype n] [DecidableEq n] (m : ℕ) : Subgroup (GL n ℤ) :=
  (GeneralLinearGroup.map (Int.castRingHom (ZMod m))).ker

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Membership in a principal congruence subgroup.** An element $g$ of
$\mathrm{GL}_n(\mathbb{Z})$ lies in the principal congruence subgroup of level $m$ if and only if
every entry of $g - 1$ is divisible by $m$.

Source: P. A. Linnell, Right orderable residually finite p-groups and a Kourovka notebook problem,
J. Algebra 248 (2002), 605-607, arXiv:math/0107094, proof of Theorem 1. -/
theorem mem_congruenceSubgroup_iff {m : ℕ} {g : GL n ℤ} :
    g ∈ congruenceSubgroup n m ↔
      ∀ i j, (m : ℤ) ∣ (g : Matrix n n ℤ) i j - (1 : Matrix n n ℤ) i j := by
  simp only [congruenceSubgroup, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff,
    Units.val_one]
  refine forall₂_congr fun i j => ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ← Matrix.map_apply (f := (Int.cast : ℤ → ZMod m)),
    Matrix.map_one _ Int.cast_zero Int.cast_one, GeneralLinearGroup.map_apply, eq_comm]
  rfl

/-- Over `ZMod (p ^ k)`, `(1 + p • B) ^ (p ^ k) = 1`: in `ℤ[X]`, `p ^ (k + 1)` divides
`(1 + p X) ^ (p ^ k) - 1`. -/
private theorem one_add_nsmul_pow_eq_one (p k : ℕ) (B : Matrix n n (ZMod (p ^ k))) :
    (1 + p • B) ^ p ^ k = 1 := by
  obtain ⟨Q, hQ⟩ : ((p : Polynomial ℤ)) ^ (k + 1) ∣
      (1 + (p : Polynomial ℤ) * Polynomial.X) ^ p ^ k - 1 ^ p ^ k :=
    dvd_sub_pow_of_dvd_sub (by simp) k
  have hB := congrArg (Polynomial.aeval B) hQ
  simp only [map_sub, map_pow, map_add, map_mul, map_one, map_natCast, Polynomial.aeval_X,
    one_pow] at hB
  have hp0 : ((p : Matrix n n (ZMod (p ^ k)))) ^ (k + 1) = 0 := by
    have h0 : ((p ^ (k + 1) : ℕ) : ZMod (p ^ k)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p (Nat.le_succ k))
    rw [← Nat.cast_pow, ← diagonal_natCast, h0, diagonal_zero]
  rw [hp0, zero_mul, sub_eq_zero] at hB
  rwa [nsmul_eq_mul]

/-- For `p ∣ m`, reducing an element of the level-`m` congruence subgroup modulo `p ^ k` gives an
element of order dividing `p ^ k`. -/
private theorem map_pow_eq_one_of_mem {p m : ℕ} (hpm : p ∣ m) (k : ℕ) {g : GL n ℤ}
    (hg : g ∈ congruenceSubgroup n m) :
    GeneralLinearGroup.map (Int.castRingHom (ZMod (p ^ k))) g ^ p ^ k = 1 := by
  rw [mem_congruenceSubgroup_iff] at hg
  have hp : ∀ i j, (p : ℤ) ∣ (g : Matrix n n ℤ) i j - (1 : Matrix n n ℤ) i j :=
    fun i j => (Int.natCast_dvd_natCast.mpr hpm).trans (hg i j)
  let B : Matrix n n (ZMod (p ^ k)) := fun i j =>
    (((g : Matrix n n ℤ) i j - (1 : Matrix n n ℤ) i j) / p : ℤ)
  have hB : ((GeneralLinearGroup.map (Int.castRingHom (ZMod (p ^ k))) g :
      GL n (ZMod (p ^ k))) : Matrix n n (ZMod (p ^ k))) = 1 + p • B := by
    ext i j
    have hij : (g : Matrix n n ℤ) i j = (1 : Matrix n n ℤ) i j +
        p * (((g : Matrix n n ℤ) i j - (1 : Matrix n n ℤ) i j) / p) := by
      rw [Int.mul_ediv_cancel' (hp i j), add_sub_cancel]
    rw [GeneralLinearGroup.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    conv_lhs => rw [hij]
    simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, B]
    congr 1
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  ext1
  rw [Units.val_pow_eq_pow_val, hB, one_add_nsmul_pow_eq_one, Units.val_one]

/-- **Congruence subgroups are residually $p$.** For a prime $p$ dividing $m$, the principal
congruence subgroup of level $m$ of $\mathrm{GL}_n(\mathbb{Z})$ is residually a finite
$p$-group: an element $g \ne 1$ is not congruent to the identity modulo some $p^k$, and reduction
modulo $p^k$ maps the congruence subgroup onto a finite $p$-group.

Source: P. A. Linnell, Right orderable residually finite p-groups and a Kourovka notebook problem,
J. Algebra 248 (2002), 605-607, arXiv:math/0107094, proof of Theorem 1. -/
theorem isResiduallyFiniteP_congruenceSubgroup {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    IsResiduallyFiniteP p (congruenceSubgroup n m) := by
  intro g hg
  obtain ⟨a, b, hab⟩ :
      ∃ a b, ((g : GL n ℤ) : Matrix n n ℤ) a b ≠ (1 : Matrix n n ℤ) a b := by
    by_contra! hcon
    exact hg (Subtype.ext (Units.ext (Matrix.ext hcon)))
  set d := ((g : GL n ℤ) : Matrix n n ℤ) a b - (1 : Matrix n n ℤ) a b with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr hab
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ d.natAbs) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hk : ¬ ((p ^ d.natAbs : ℕ) : ℤ) ∣ d := by
    intro hdvd
    have h₁ : p ^ d.natAbs ≤ d.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hd) (Int.natCast_dvd.mp hdvd)
    have h₂ : d.natAbs < p ^ d.natAbs := Nat.lt_pow_self hp.one_lt
    omega
  let φ : congruenceSubgroup n m →* GL n (ZMod (p ^ d.natAbs)) :=
    (GeneralLinearGroup.map (Int.castRingHom (ZMod (p ^ d.natAbs)))).comp
      (congruenceSubgroup n m).subtype
  refine ⟨φ.ker, φ.normal_ker, ?_, ?_⟩
  · rw [Subgroup.index_ker]
    refine IsPGroup.iff_card.mp ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨d.natAbs, Subtype.ext (map_pow_eq_one_of_mem hpm _ x.2)⟩
  · intro hmem
    apply hk
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hmem
    have hab' := hmem a b
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hd_def, Int.cast_sub, sub_eq_zero]
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply,
      eq_intCast, Units.val_one] at hab'
    rw [hab', ← Matrix.map_apply (f := (Int.cast : ℤ → ZMod (p ^ d.natAbs))),
      Matrix.map_one _ Int.cast_zero Int.cast_one]

/-! ### Congruence subgroups of `GL₃(ℤ)` are not right-orderable -/

private theorem transvection_mul_transvection_eq {i j l : n} (hjl : j ≠ l) (hil : i ≠ l)
    (a b : ℤ) :
    transvection i j a * transvection j l b =
      transvection i l (a * b) * (transvection j l b * transvection i j a) := by
  simp [transvection, Matrix.mul_add, Matrix.add_mul, hil.symm, hjl.symm]
  abel

private theorem commute_transvection_transvection_left {i j l : n} (hij : i ≠ j) (hil : i ≠ l)
    (a c : ℤ) : Commute (transvection i l c) (transvection i j a) := by
  simp [Commute, SemiconjBy, transvection, Matrix.mul_add, Matrix.add_mul, hil.symm, hij.symm]
  abel

private theorem commute_transvection_transvection_right {i j l : n} (hjl : j ≠ l) (hil : i ≠ l)
    (b c : ℤ) : Commute (transvection i l c) (transvection j l b) := by
  simp [Commute, SemiconjBy, transvection, Matrix.mul_add, Matrix.add_mul, hil.symm, hjl.symm]
  abel

private theorem transvection_pow {i j : n} (hij : i ≠ j) (c : ℤ) :
    ∀ k : ℕ, transvection i j c ^ k = transvection i j (k * c)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, transvection_pow hij c k, transvection_mul_transvection_same i j hij]
    push_cast
    ring_nf

/-- The elementary matrix `1 + t E_{ij}`, `i ≠ j`, as an element of `GL n ℤ`. -/
private def elementary (i j : n) (hij : i ≠ j) (t : ℤ) : GL n ℤ :=
  ⟨transvection i j t, transvection i j (-t),
    by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j hij, neg_add_cancel, transvection_zero]⟩

private theorem elementary_mem (m : ℕ) (i j : n) (hij : i ≠ j) :
    elementary i j hij m ∈ congruenceSubgroup n m := by
  rw [mem_congruenceSubgroup_iff]
  intro a b
  simp only [elementary, transvection, Matrix.add_apply, add_sub_cancel_left, single_apply]
  split_ifs <;> simp

/-- **Congruence subgroups of $\mathrm{GL}_3(\mathbb{Z})$ are not right-orderable (Witte).** For
$m \ne 0$, the principal congruence subgroup of level $m$ of $\mathrm{GL}_3(\mathbb{Z})$ is not
right-orderable. The six elementary matrices $1 + m E_{ij}$, $i \ne j$, lie in it, and for
$i, j, l$ distinct the commutator $[1 + m E_{ij}, 1 + m E_{jl}] = (1 + m E_{il})^m$ is central in
the subgroup generated by the two. In a right-ordered group the larger of such a central element
$z \ne 1$ and its inverse is smaller than the largest of the two generators and their inverses,
which is impossible for the largest of the six in this sense.

Source: P. A. Linnell, Right orderable residually finite p-groups and a Kourovka notebook problem,
J. Algebra 248 (2002), 605-607, arXiv:math/0107094, proof of Theorem 1; D. Witte Morris, Can
lattices in SL(n,ℝ) act on the circle?, arXiv:0811.0051, Lemma 3.6 and the proof of
Theorem 3.1. -/
theorem not_isRightOrderable_congruenceSubgroup {m : ℕ} (hm : m ≠ 0) :
    ¬ IsRightOrderable (congruenceSubgroup (Fin 3) m) := by
  let u : ∀ i j : Fin 3, i ≠ j → congruenceSubgroup (Fin 3) m :=
    fun i j hij => ⟨elementary i j hij m, elementary_mem m i j hij⟩
  refine not_isRightOrderable_of_elementary (k := m) hm u ?_ ?_ ?_ ?_
  · intro i j l hij hjl hil
    refine Subtype.ext (Units.ext ?_)
    simp only [u, Subgroup.coe_mul, SubgroupClass.coe_pow, Units.val_mul,
      Units.val_pow_eq_pow_val, elementary]
    rw [transvection_mul_transvection_eq hjl hil, transvection_pow hil]
  · intro i j l hij hil _
    exact Subtype.ext (Units.ext (commute_transvection_transvection_left hij hil _ _).eq)
  · intro i j l hjl hil _
    exact Subtype.ext (Units.ext (commute_transvection_transvection_right hjl hil _ _).eq)
  · intro i l hil h1
    have h := congrArg (fun g : congruenceSubgroup (Fin 3) m =>
      ((g : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) i l) h1
    simp only [u, elementary, transvection, Matrix.add_apply, single_apply_same,
      Matrix.one_apply_ne hil, Units.val_one, OneMemClass.coe_one, zero_add,
      Nat.cast_eq_zero] at h
    exact hm h

/--
**A non-right-orderable group that is residually $p$ for two primes (Linnell).** There exist a
group $G$ and distinct primes $p$ and $q$ such that $G$ is residually a finite $p$-group and
residually a finite $q$-group but is not right-orderable.

By Rhemtulla, a group that is residually a finite $p$-group for infinitely many primes $p$ is
orderable.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 10.30 (N. Ya. Medvedev); resolution: P. A. Linnell, J.
Algebra 248 (2002), 605-607, Kourovka Archive, Problem 10.30 ("Yes, there does").
-/
theorem residuallyTwoPrimesNotRightOrderable_holds : residuallyTwoPrimesNotRightOrderable :=
  ⟨congruenceSubgroup (Fin 3) 6, inferInstance, 2, 3, Nat.prime_two, Nat.prime_three, by decide,
    isResiduallyFiniteP_congruenceSubgroup Nat.prime_two (by norm_num),
    isResiduallyFiniteP_congruenceSubgroup Nat.prime_three (by norm_num),
    not_isRightOrderable_congruenceSubgroup (by norm_num)⟩

end MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted
