/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The second Wong sequence and shrunk subspaces

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. The sequence is increasing. Over a field with finite-dimensional W, its
dimension-th term W∞ is a fixed point. If V is also finite-dimensional and W∞ ⊆ im A, its
preimage has deficiency dim ker A. When A ∈ B, containment is equivalent to the existence of a
subspace with at least that deficiency and makes A a maximum-rank member of B.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Non-commutative Edmonds' problem and
matrix semi-invariants*, §2.2 and Fact 2.1. The stable-space branch is also used in their
*Constructive noncommutative rank computation in deterministic polynomial time over fields of
arbitrary characteristics*, Theorem 5.
-/

@[expose] public section

universe u v w

namespace LinearMap

section CommSemiring

variable {R : Type u} [CommSemiring R]
variable {V : Type v} {W : Type w}
variable [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]

/-- **The second Wong sequence.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. The inverse image A⁻¹Wⱼ is the linear preimage, including when A is singular.
-/
def secondWongSeq (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) : ℕ → Submodule R W
  | 0 => ⊥
  | j + 1 => Submodule.map₂ LinearMap.id B ((secondWongSeq A B j).comap A)

@[simp]
theorem secondWongSeq_zero (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) :
    secondWongSeq A B 0 = ⊥ := rfl

@[simp]
theorem secondWongSeq_succ (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) (j : ℕ) :
    secondWongSeq A B (j + 1) =
      Submodule.map₂ LinearMap.id B ((secondWongSeq A B j).comap A) := rfl

@[simp]
theorem secondWongSeq_one (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) :
    secondWongSeq A B 1 = Submodule.map₂ LinearMap.id B A.ker := by
  simp only [secondWongSeq_succ, secondWongSeq_zero, Submodule.comap_bot]

/-- **Monotonicity of the second Wong sequence.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. For every j ≥ 0, Wⱼ ⊆ Wⱼ₊₁.
-/
theorem secondWongSeq_le_succ (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) (j : ℕ) :
    secondWongSeq A B j ≤ secondWongSeq A B (j + 1) := by
  induction j with
  | zero => exact bot_le
  | succ j ih =>
    exact Submodule.map₂_le_map₂_right (Submodule.comap_mono ih)

theorem secondWongSeq_monotone (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W)) :
    Monotone (secondWongSeq A B) :=
  monotone_nat_of_le_succ (secondWongSeq_le_succ A B)

/-- **Monotonicity in the space of maps.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Let C be another submodule of maps V → W with B ⊆ C. The sequences
W₀(A,B) = 0 and Wⱼ₊₁(A,B) = B(A⁻¹Wⱼ(A,B)) satisfy Wⱼ(A,B) ⊆ Wⱼ(A,C) for every j.
-/
theorem secondWongSeq_le_of_le (A : V →ₗ[R] W) {B C : Submodule R (V →ₗ[R] W)}
    (hBC : B ≤ C) (j : ℕ) : secondWongSeq A B j ≤ secondWongSeq A C j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact Submodule.map₂_le_map₂ hBC (Submodule.comap_mono ih)

/-- **A subspace bounding the Wong sequence.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. If P ⊆ W satisfies B(A⁻¹P) ⊆ P, then Wⱼ ⊆ P for every j.
-/
theorem secondWongSeq_le_of_prefixed (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W))
    {P : Submodule R W} (hP : Submodule.map₂ LinearMap.id B (P.comap A) ≤ P) (j : ℕ) :
    secondWongSeq A B j ≤ P := by
  induction j with
  | zero => exact bot_le
  | succ j ih =>
    exact (Submodule.map₂_le_map₂_right (Submodule.comap_mono ih)).trans hP

/-- **Propagation of a Wong stabilization.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. If Wⱼ₊₁ = Wⱼ at some j, then Wⱼ₊ₖ = Wⱼ for every k ≥ 0.
-/
theorem secondWongSeq_add_eq_of_eq_succ (A : V →ₗ[R] W) (B : Submodule R (V →ₗ[R] W))
    {j : ℕ} (hj : secondWongSeq A B (j + 1) = secondWongSeq A B j) (k : ℕ) :
    secondWongSeq A B (j + k) = secondWongSeq A B j := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    simpa only [Nat.add_succ, secondWongSeq_succ, ih] using hj

@[simp]
theorem secondWongSeq_bot (A : V →ₗ[R] W) (j : ℕ) :
    secondWongSeq A ⊥ j = ⊥ := by
  cases j <;> simp only [secondWongSeq_zero, secondWongSeq_succ, Submodule.map₂_bot_left]

/-- **The Wong sequence of an injective starting map.**

Let R be a commutative semiring, V,W R-modules, A : V → W an R-linear map and B an R-submodule
of linear maps V → W. Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) for f
∈ B, u ∈ U. If ker A = 0, then Wⱼ = 0 for every j.
-/
theorem secondWongSeq_eq_bot_of_ker_eq_bot (A : V →ₗ[R] W)
    (B : Submodule R (V →ₗ[R] W)) (hA : A.ker = ⊥) (j : ℕ) :
    secondWongSeq A B j = ⊥ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [secondWongSeq_succ, ih, Submodule.comap_bot, hA, Submodule.map₂_bot_right]

end CommSemiring

section Field

variable {K : Type u} [Field K]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

section FiniteTarget

variable [FiniteDimensional K W]

/-- **A dimension bound for Wong stabilization.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Assume W is finite-dimensional. For W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), there exists j ≤ dim W with
Wⱼ₊₁ = Wⱼ.
-/
theorem exists_secondWongSeq_eq_succ (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) :
    ∃ j, j ≤ Module.finrank K W ∧ secondWongSeq A B (j + 1) = secondWongSeq A B j := by
  by_contra h
  have hne : ∀ j, j ≤ Module.finrank K W →
      secondWongSeq A B j ≠ secondWongSeq A B (j + 1) := by
    intro j hj heq
    exact h ⟨j, hj, heq.symm⟩
  have hdim : ∀ j, j ≤ Module.finrank K W + 1 →
      j ≤ Module.finrank K (secondWongSeq A B j) := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (secondWongSeq_le_succ A B j)
          (hne j (Nat.le_of_succ_le_succ hj)))
      exact (Nat.succ_le_succ (ih (Nat.le_of_succ_le hj))).trans (Nat.succ_le_of_lt hlt)
  exact Nat.not_succ_le_self (Module.finrank K W)
    ((hdim _ le_rfl).trans (secondWongSeq A B (Module.finrank K W + 1)).finrank_le)

/-- **The stable second Wong subspace.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
For finite-dimensional W, let W∞ = W_dim W for the sequence W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ), with B(U)
the span of f(u) for f ∈ B and u ∈ U. This dimension-th term is the stable value of the
increasing sequence.
-/
noncomputable def secondWongLimit (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) :
    Submodule K W :=
  secondWongSeq A B (Module.finrank K W)

theorem secondWongSeq_eq_limit (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) {j : ℕ}
    (hj : Module.finrank K W ≤ j) : secondWongSeq A B j = secondWongLimit A B := by
  obtain ⟨k, hk, heq⟩ := exists_secondWongSeq_eq_succ A B
  have hconst : ∀ m, k ≤ m → secondWongSeq A B m = secondWongSeq A B k := by
    intro m hm
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact secondWongSeq_add_eq_of_eq_succ A B heq t
  exact (hconst j (hk.trans hj)).trans (hconst (Module.finrank K W) hk).symm

theorem secondWongSeq_le_limit (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) (j : ℕ) :
    secondWongSeq A B j ≤ secondWongLimit A B := by
  rcases le_total j (Module.finrank K W) with hj | hj
  · exact secondWongSeq_monotone A B hj
  · exact (secondWongSeq_eq_limit A B hj).le

/-- **The stable Wong subspace is a fixed point.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
For finite-dimensional W, let W∞ = W_dim W for the sequence W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ), with B(U)
the span of f(u) for f ∈ B and u ∈ U. One has B(A⁻¹W∞) = W∞.
-/
theorem secondWongLimit_fixed (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) :
    Submodule.map₂ LinearMap.id B ((secondWongLimit A B).comap A) = secondWongLimit A B :=
  secondWongSeq_eq_limit A B (Nat.le_succ (Module.finrank K W))

theorem secondWongLimit_isLeast (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) :
    IsLeast {P : Submodule K W | Submodule.map₂ LinearMap.id B (P.comap A) ≤ P}
      (secondWongLimit A B) := by
  exact ⟨(secondWongLimit_fixed A B).le,
    fun _ hP => secondWongSeq_le_of_prefixed A B hP _⟩

end FiniteTarget

private theorem finrank_map_add_finrank_inf_ker (A : V →ₗ[K] W) (U : Submodule K V)
    [FiniteDimensional K U] :
    Module.finrank K (U.map A) + Module.finrank K (U ⊓ A.ker : Submodule K V) =
      Module.finrank K U := by
  have hd := (A.domRestrict U).finrank_range_add_finrank_ker
  rw [range_domRestrict, ker_domRestrict] at hd
  have hk := Submodule.finrank_map_subtype_eq U (A.ker.comap U.subtype)
  rw [Submodule.map_comap_subtype] at hk
  rwa [← hk] at hd

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- **The deficiency of the stable Wong preimage.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Assume V and W are finite-dimensional. Let W∞ be the stable value of W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ),
and suppose W∞ ⊆ im A. Then dim B(A⁻¹W∞) + dim ker A = dim(A⁻¹W∞).
-/
theorem secondWongLimit_deficiency (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W))
    (hW : secondWongLimit A B ≤ A.range) :
    Module.finrank K (Submodule.map₂ LinearMap.id B ((secondWongLimit A B).comap A)) +
      Module.finrank K A.ker = Module.finrank K ((secondWongLimit A B).comap A) := by
  have hker : A.ker ≤ (secondWongLimit A B).comap A := by
    intro x hx
    change A x ∈ secondWongLimit A B
    rw [mem_ker.mp hx]
    exact Submodule.zero_mem _
  have hmap : ((secondWongLimit A B).comap A).map A = secondWongLimit A B :=
    Submodule.map_comap_eq_of_le hW
  have hd := finrank_map_add_finrank_inf_ker A ((secondWongLimit A B).comap A)
  rw [hmap, inf_eq_right.mpr hker] at hd
  rwa [secondWongLimit_fixed]

/-- **A rank bound from a shrunk subspace.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Assume V and W are finite-dimensional. Let U ⊆ V satisfy dim B(U) + s ≤ dim U for s ∈ ℕ, where
B(U) is the span of f(u) with f ∈ B and u ∈ U. Then every C ∈ B satisfies rank C + s ≤ dim V.
-/
theorem finrank_range_add_le_of_shrunkSpace (B : Submodule K (V →ₗ[K] W))
    {U : Submodule K V} {s : ℕ}
    (hU : Module.finrank K (Submodule.map₂ LinearMap.id B U) + s ≤ Module.finrank K U)
    {C : V →ₗ[K] W} (hC : C ∈ B) :
    Module.finrank K C.range + s ≤ Module.finrank K V := by
  have hmap : U.map C ≤ Submodule.map₂ LinearMap.id B U := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.apply_mem_map₂ LinearMap.id hC hx
  have him := Submodule.finrank_mono hmap
  have hk := Submodule.finrank_mono (inf_le_right : U ⊓ C.ker ≤ C.ker)
  have hd := finrank_map_add_finrank_inf_ker C U
  have hr := C.finrank_range_add_finrank_ker
  omega

/-- **Shrunk subspaces and containment of the Wong limit.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Assume V,W are finite-dimensional and A ∈ B. Let W∞ be the stable value of W₀ = 0, Wⱼ₊₁ =
B(A⁻¹Wⱼ). There exists U ⊆ V with dim B(U) + dim ker A ≤ dim U if and only if W∞ ⊆ im A.
-/
theorem exists_shrunkSpace_iff_secondWongLimit_le_range (A : V →ₗ[K] W)
    (B : Submodule K (V →ₗ[K] W)) (hA : A ∈ B) :
    (∃ U : Submodule K V,
      Module.finrank K (Submodule.map₂ LinearMap.id B U) + Module.finrank K A.ker ≤
        Module.finrank K U) ↔ secondWongLimit A B ≤ A.range := by
  constructor
  · rintro ⟨U, hU⟩
    let P := Submodule.map₂ LinearMap.id B U
    have hmap : U.map A ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.apply_mem_map₂ LinearMap.id hA hx
    have him := Submodule.finrank_mono hmap
    have hk := Submodule.finrank_mono (inf_le_right : U ⊓ A.ker ≤ A.ker)
    have hd := finrank_map_add_finrank_inf_ker A U
    have hmapEq : U.map A = P :=
      Submodule.eq_of_le_of_finrank_eq hmap (by dsimp [P] at him ⊢; omega)
    have hkerEq : (U ⊓ A.ker : Submodule K V) = A.ker :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by dsimp [P] at him; omega)
    have hker : A.ker ≤ U := by
      rw [← hkerEq]
      exact inf_le_left
    have hP : Submodule.map₂ LinearMap.id B (P.comap A) ≤ P := by
      have hcomap : P.comap A = U := by
        rw [← hmapEq, Submodule.comap_map_eq_self hker]
      rw [hcomap]
    exact ((secondWongLimit_isLeast A B).2 hP).trans (by
      rw [← hmapEq]
      exact map_le_range)
  · intro hW
    exact ⟨(secondWongLimit A B).comap A, (secondWongLimit_deficiency A B hW).le⟩

/-- **The rank bound from a contained Wong limit.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Assume V,W are finite-dimensional. Let W∞ be the stable value of W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ), and
suppose W∞ ⊆ im A. Then rank C ≤ rank A for every C ∈ B.
-/
theorem finrank_range_le_of_secondWongLimit_le_range (A : V →ₗ[K] W)
    (B : Submodule K (V →ₗ[K] W)) (hW : secondWongLimit A B ≤ A.range)
    {C : V →ₗ[K] W} (hC : C ∈ B) :
    Module.finrank K C.range ≤ Module.finrank K A.range := by
  have hbound := finrank_range_add_le_of_shrunkSpace B
    (secondWongLimit_deficiency A B hW).le hC
  have hr := A.finrank_range_add_finrank_ker
  omega

end Field

end LinearMap
