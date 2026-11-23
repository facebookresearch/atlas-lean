/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section

/-!
# Herbrand quotient of Tate cohomology

For a finite group `G` and `M : Rep R G`, `h^n` is the cardinality of Tate
cohomology `tateCohomology M n`, and `h_n` the cardinality of Tate homology,
defined from cohomology by `H_hat_n = H_hat^(-n-1)`. When degrees `0` and
`-1` are finite, the Herbrand quotient is `h = h^0 / h_0` in `ℚ`.

The classical statement asks for finite *cyclic* `G`, but Mathlib's
`tateCohomology` (and hence everything here) needs only `[Group G]`
`[Fintype G]`; no cyclicity hypothesis is used.
-/

universe u

namespace TateCohomology

open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- **Cardinality of Tate cohomology.** Let $G$ be a finite group, $R$ a commutative ring, $M$ an
$R$-linear representation of $G$ and $n$ an integer. This is the cardinality of the Tate
cohomology group $\hat H^n(G, M)$, as a cardinal number (possibly infinite). -/
noncomputable def tateCohomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  Cardinal.mk ↥(tateCohomology M n)

/-- **Cardinality of Tate homology.** Let $G$ be a finite group, $R$ a commutative ring
and $M$ an $R$-linear representation of $G$. For an integer $n$, the cardinality $h_n(M)$
of the degree-$n$ Tate homology of $M$ is defined as the cardinal number of the Tate
cohomology group $\hat H^{-n-1}(G, M)$, following the convention $\hat H_n = \hat H^{-n-1}$. -/
noncomputable def tateHomologyCard (M : Rep R G) (n : ℤ) : Cardinal :=
  tateCohomologyCard M (-n - 1)

/-- **Cardinality of Tate homology in degree zero.** Let $G$ be a finite group, $R$ a commutative
ring and $M$ an $R$-linear representation of $G$. The cardinality of the degree-$0$ Tate homology
of $M$ equals the cardinality of the Tate cohomology group $\hat H^{-1}(G, M)$.

The cardinality of Tate homology in degree $n$ is defined as that of $\hat H^{-n-1}(G, M)$, so
this holds by definition. -/
@[simp] theorem tateHomologyCard_zero (M : Rep R G) :
    tateHomologyCard M 0 = tateCohomologyCard M (-1) := rfl

/-- **Cardinality of finite Tate cohomology as a natural number.** Let $G$ be a finite group, $R$
a commutative ring, $M$ an $R$-linear representation of $G$ and $n$ an integer such that the Tate
cohomology group $\hat H^n(G, M)$ is finite. Then the cardinality of $\hat H^n(G, M)$ equals its
number of elements, a natural number viewed as a cardinal number. -/
theorem tateCohomologyCard_eq_natCast (M : Rep R G) (n : ℤ)
    [Finite ↥(tateCohomology M n)] :
    tateCohomologyCard M n = Nat.card ↥(tateCohomology M n) :=
  Nat.cast_card.symm

/-- **Finiteness hypothesis for the Herbrand quotient.** Let $G$ be a finite group, $R$ a
commutative ring and $M$ an $R$-linear representation of $G$. The representation $M$ satisfies
the Herbrand finiteness hypothesis when its Tate cohomology groups $\hat H^0(G, M)$ and
$\hat H^{-1}(G, M)$ are both finite. -/
def HerbrandFinite (M : Rep R G) : Prop :=
  Finite ↥(tateCohomology M 0) ∧ Finite ↥(tateCohomology M (-1))

/-- **Herbrand quotient.** Let $G$ be a finite group, $R$ a commutative ring and $M$ an
$R$-linear representation of $G$ whose Tate cohomology groups $\hat H^0(G, M)$ and
$\hat H^{-1}(G, M)$ are finite. The Herbrand quotient of $M$ is the rational number
$h(M) = |\hat H^0(G, M)| / |\hat H^{-1}(G, M)|$, where $|X|$ is the number of elements of $X$. -/
noncomputable def herbrandQuotient (M : Rep R G) (h : HerbrandFinite M) : ℚ :=
  haveI := h.1
  haveI := h.2
  (Nat.card ↥(tateCohomology M 0) : ℚ) / Nat.card ↥(tateCohomology M (-1))

/-- **Herbrand quotient as a ratio of orders.** Let $G$ be a finite group, $R$ a commutative
ring and $M$ an $R$-linear representation of $G$ whose Tate cohomology groups $\hat H^0(G, M)$
and $\hat H^{-1}(G, M)$ are finite. Then the Herbrand quotient of $M$ equals the rational number
$|\hat H^0(G, M)| / |\hat H^{-1}(G, M)|$, where $|X|$ is the number of elements of $X$. -/
theorem herbrandQuotient_eq (M : Rep R G) (h : HerbrandFinite M) :
    herbrandQuotient M h = (Nat.card ↥(tateCohomology M 0) : ℚ) /
      Nat.card ↥(tateCohomology M (-1)) := rfl

/-- **The denominator of the Herbrand quotient is positive.** Let $G$ be a finite group, $R$ a
commutative ring and $M$ an $R$-linear representation of $G$ whose Tate cohomology groups
$\hat H^0(G, M)$ and $\hat H^{-1}(G, M)$ are finite. Then the number of elements of
$\hat H^{-1}(G, M)$ is positive. -/
theorem herbrandQuotient_den_pos (M : Rep R G) (h : HerbrandFinite M) :
    0 < Nat.card ↥(tateCohomology M (-1)) := by
  have := h.2
  exact Nat.card_pos

/-- **The denominator of the Herbrand quotient is nonzero.** Let $G$ be a finite group, $R$ a
commutative ring and $M$ an $R$-linear representation of $G$ whose Tate cohomology groups
$\hat H^0(G, M)$ and $\hat H^{-1}(G, M)$ are finite. Then the number of elements of
$\hat H^{-1}(G, M)$ is nonzero. -/
theorem herbrandQuotient_den_ne_zero (M : Rep R G) (h : HerbrandFinite M) :
    Nat.card ↥(tateCohomology M (-1)) ≠ 0 :=
  ne_of_gt (herbrandQuotient_den_pos M h)

/-- **Positivity of the Herbrand quotient.** Let $G$ be a finite group, $R$ a commutative ring
and $M$ an $R$-linear representation of $G$ whose Tate cohomology groups $\hat H^0(G, M)$ and
$\hat H^{-1}(G, M)$ are finite. Then the Herbrand quotient of $M$ is strictly positive. -/
theorem herbrandQuotient_pos (M : Rep R G) (h : HerbrandFinite M) :
    0 < herbrandQuotient M h := by
  have := h.1
  have := h.2
  rw [herbrandQuotient_eq]
  exact div_pos (Nat.cast_pos.mpr Nat.card_pos) (Nat.cast_pos.mpr Nat.card_pos)

/-- **Herbrand quotients agree when Tate cohomology in degrees $0$ and $-1$ is in bijection.**
Let $G$ be a finite group, $R$ a commutative ring and $M$, $N$ two $R$-linear representations
of $G$ whose Tate cohomology groups $\hat H^0(G, M)$, $\hat H^{-1}(G, M)$, $\hat H^0(G, N)$ and
$\hat H^{-1}(G, N)$ are finite. If there are bijections between the underlying sets of
$\hat H^0(G, M)$ and $\hat H^0(G, N)$ and between those of $\hat H^{-1}(G, M)$ and
$\hat H^{-1}(G, N)$, then the Herbrand quotients of $M$ and $N$ are equal. -/
theorem herbrandQuotient_congr {M N : Rep R G} {hM : HerbrandFinite M}
    {hN : HerbrandFinite N}
    (e₀ : ↥(tateCohomology M 0) ≃ ↥(tateCohomology N 0))
    (e₁ : ↥(tateCohomology M (-1)) ≃ ↥(tateCohomology N (-1))) :
    herbrandQuotient M hM = herbrandQuotient N hN := by
  rw [herbrandQuotient_eq, herbrandQuotient_eq, Nat.card_congr e₀,
    Nat.card_congr e₁]

end TateCohomology
