/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Projectivization.Independence

@[expose] public section

/-!
# General position

This file defines general position for indexed families of points in affine and projective spaces.
A family is in general position through dimension `d` when each subfamily of at most `d + 1`
points is independent.
-/

noncomputable section

open Function
open scoped Affine LinearAlgebra.Projectivization

universe u v w

variable {k : Type u} {V : Type v} {P : Type w} {ι ι' : Type*}

section Affine

/-- **General position of affine points.** Let $k$ be a division ring and $P$ an affine space over
$k$. A family $(p_i)_{i \in \iota}$ of points of $P$ is in general position through dimension
$d \in \mathbb{N}$ if for every finite set $S \subseteq \iota$ of at most $d + 1$ indices, the
subfamily $(p_i)_{i \in S}$ is affinely independent over $k$. -/
def IsGeneralPosition (k : Type u) [DivisionRing k] {V : Type v} {P : Type w} [AddCommGroup V]
    [Module k V] [AffineSpace V P] {ι : Type*} (d : ℕ) (p : ι → P) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → AffineIndependent k (s.restrict p)

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- **Affinely independent families are in general position.** If a family $(p_i)_{i \in \iota}$ of
points of an affine space over a division ring $k$ is affinely independent over $k$, then it is in
general position through dimension $d$ for every $d \in \mathbb{N}$. -/
theorem AffineIndependent.isGeneralPosition {p : ι → P} (hp : AffineIndependent k p) (d : ℕ) :
    IsGeneralPosition k d p :=
  fun s _ ↦ hp.subtype s

/-- **General position in affine space is monotone in the dimension.** Let $d \le e$ be natural
numbers. If a family of points of an affine space over a division ring $k$ is in general position
through dimension $e$, then it is in general position through dimension $d$. -/
theorem IsGeneralPosition.mono {d e : ℕ} {p : ι → P} (hp : IsGeneralPosition k e p)
    (hde : d ≤ e) : IsGeneralPosition k d p :=
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))

section Examples

/-- The empty family is in general position in every dimension. -/
example (p : Empty → P) (d : ℕ) : IsGeneralPosition k d p :=
  (affineIndependent_of_subsingleton k p).isGeneralPosition d

/-- Two distinct affine points are in general position through dimension one. -/
example (p q : P) (hpq : p ≠ q) : IsGeneralPosition k 1 ![p, q] :=
  (affineIndependent_of_ne k hpq).isGeneralPosition 1

end Examples

end Affine

namespace Projectivization

/-- **General position of projective points.** Let $k$ be a division ring and $V$ a vector space
over $k$, with projective space $\mathbb{P}(V)$. A family $(p_i)_{i \in \iota}$ of points of
$\mathbb{P}(V)$ is in general position through dimension $d \in \mathbb{N}$ if for every finite set
$S \subseteq \iota$ of at most $d + 1$ indices, the subfamily $(p_i)_{i \in S}$ is projectively
independent. -/
def IsGeneralPosition {k : Type u} [DivisionRing k] {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type*} (d : ℕ) (p : ι → ℙ k V) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → Independent (s.restrict p)

variable [DivisionRing k] [AddCommGroup V] [Module k V]

/-- **Projectively independent families are in general position.** If a family
$(p_i)_{i \in \iota}$ of points of the projective space $\mathbb{P}(V)$ of a vector space $V$ over a
division ring $k$ is projectively independent, then it is in general position through dimension $d$
for every $d \in \mathbb{N}$. -/
theorem Independent.isGeneralPosition {p : ι → ℙ k V} (hp : Independent p) (d : ℕ) :
    IsGeneralPosition d p := by
  intro s _
  rw [independent_iff] at hp ⊢
  simpa [Finset.restrict_def, Function.comp_def] using
    hp.comp (fun i : s ↦ (i : ι)) Subtype.val_injective

/-- **General position in projective space is monotone in the dimension.** Let $d \le e$ be
natural numbers. If a family of points of the projective space $\mathbb{P}(V)$ of a vector space
$V$ over a division ring $k$ is in general position through dimension $e$, then it is in general
position through dimension $d$. -/
theorem IsGeneralPosition.mono {d e : ℕ} {p : ι → ℙ k V} (hp : IsGeneralPosition e p)
    (hde : d ≤ e) : IsGeneralPosition d p :=
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))

section Examples

/-- Two distinct projective points are in general position through dimension one. -/
example (p q : ℙ k V) (hpq : p ≠ q) : IsGeneralPosition 1 ![p, q] :=
  ((independent_pair_iff_ne p q).2 hpq).isGeneralPosition 1

end Examples

end Projectivization
