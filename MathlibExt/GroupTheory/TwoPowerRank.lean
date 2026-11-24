/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/

namespace AbelianGroup

/-- **The subgroup $2^kA$.** For an abelian group $A$, written additively, and a natural number
$k$, $2^kA$ is the subgroup $\{2^k a : a \in A\}$ of $A$, the image of multiplication by $2^k$. -/
def twoPowerImage (A : Type*) [AddCommGroup A] (k : ℕ) : Submodule ℤ A :=
  LinearMap.range (LinearMap.lsmul ℤ A (2 ^ k : ℤ))

theorem twoPowerImage_succ_le (A : Type*) [AddCommGroup A] (k : ℕ) :
    twoPowerImage A (k + 1) ≤ twoPowerImage A k := by
  rintro x ⟨a, rfl⟩
  refine ⟨2 • a, ?_⟩
  simp only [LinearMap.lsmul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rw [smul_smul]
  norm_num [pow_succ, mul_comm]

/-- **The two-power layer $2^{j-1}A / 2^jA$.** For an abelian group $A$, written additively, and a
natural number $j$, this is the quotient group $2^{j-1}A / 2^jA$, where $2^kA$ denotes the
subgroup $\{2^k a : a \in A\}$ and $2^jA \subseteq 2^{j-1}A$. For $j = 0$, where $j - 1$ is
read as $0$, it is the trivial quotient $A / A$. -/
abbrev higherTwoPowerLayer (A : Type*) [AddCommGroup A] (j : ℕ) : Type _ :=
  twoPowerImage A (j - 1) ⧸
    ((twoPowerImage A j).comap (twoPowerImage A (j - 1)).subtype).toAddSubgroup

noncomputable instance (A : Type*) [AddCommGroup A] (j : ℕ) [hj : Fact (0 < j)] :
    Module (ZMod 2) (higherTwoPowerLayer A j) := by
  let H := twoPowerImage A (j - 1)
  let K := ((twoPowerImage A j).comap H.subtype).toAddSubgroup
  apply QuotientAddGroup.zmodModule
  intro x
  change 2 • (x : A) ∈ twoPowerImage A j
  rcases x.property with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [LinearMap.lsmul_apply] at ha ⊢
  rw [← ha]
  rw [two_nsmul, ← add_zsmul]
  congr 1
  have hpow : 2 ^ j = 2 ^ (j - 1) + 2 ^ (j - 1) := by
    rw [← Nat.two_pow_pred_mul_two hj.out, mul_two]
  exact_mod_cast hpow

/-- **The $2^j$-rank of a finite abelian group.** Let $A$ be a finite abelian group, written
additively, and let $j \ge 1$ be an integer. Writing $2^kA$ for the subgroup
$\{2^k a : a \in A\}$, the $2^j$-rank of $A$ is the dimension over $\mathbb{F}_2$ of the
quotient $2^{j-1}A / 2^jA$, which is an $\mathbb{F}_2$-vector space because $2$ kills it. -/
noncomputable def higherTwoPowerRank (A : Type*) [AddCommGroup A] [Finite A]
    (j : ℕ) (hj : 0 < j) : ℕ :=
  letI : Fact (0 < j) := ⟨hj⟩
  Module.finrank (ZMod 2) (higherTwoPowerLayer A j)

/-- **The $4$-rank of a finite abelian group.** For a finite abelian group $A$, written
additively, the $4$-rank of $A$ is the dimension over $\mathbb{F}_2$ of the quotient $2A / 4A$,
where $2A = \{2a : a \in A\}$ and $4A = \{4a : a \in A\}$; it is the $2^j$-rank of $A$ for
$j = 2$. -/
noncomputable abbrev fourRank (A : Type*) [AddCommGroup A] [Finite A] : ℕ :=
  higherTwoPowerRank A 2 (by norm_num)

theorem higherTwoPowerRank_eq (A : Type*) [AddCommGroup A] [Finite A]
    (j : ℕ) (hj : 0 < j) :
    letI : Fact (0 < j) := ⟨hj⟩
    higherTwoPowerRank A j hj = Module.finrank (ZMod 2) (higherTwoPowerLayer A j) :=
  rfl

theorem fourRank_eq (A : Type*) [AddCommGroup A] [Finite A] :
    letI : Fact (0 < 2) := ⟨by norm_num⟩
    fourRank A = Module.finrank (ZMod 2) (higherTwoPowerLayer A 2) :=
  rfl

end AbelianGroup
