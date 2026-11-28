/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kruskal's theorem and generic identifiability of latent class models

For a real matrix `M` with `r` rows, the Kruskal rank of `M` is the largest `I` such that every
set of `I` rows of `M` is linearly independent. Three matrices `M_1, M_2, M_3` with `r` rows (of
lengths `κ_1, κ_2, κ_3`) determine the tensor `[M_1, M_2, M_3]` with entries
`∑_i M_1(i, u) M_2(i, v) M_3(i, w)`.

**Theorem 1** (Kruskal 1977, as stated by Allman–Matias–Rhodes 2009). If the Kruskal ranks
`I_1, I_2, I_3` satisfy `I_1 + I_2 + I_3 ≥ 2r + 2`, then `[M_1, M_2, M_3]` determines the `M_j`
up to simultaneous permutation of the rows and rescaling of the rows: if
`[N_1, N_2, N_3] = [M_1, M_2, M_3]`, there are a permutation `σ` and scalars `c_j(i)` with
`c_1(i) c_2(i) c_3(i) = 1` and `N_j(i, ·) = c_j(i) M_j(σ i, ·)`.

The latent class model `M(r; k_1, …, k_p)` has a hidden variable with `r` classes and `p`
observed variables, conditionally independent given the class, with `k_j` states. Its parameters
are the class proportions `π` (a probability vector) and, for each `j`, an `r × k_j` matrix
`M_j` with stochastic rows; the joint distribution is
`P(x_1, …, x_p) = ∑_i π_i ∏_j M_j(i, x_j)`.

**Theorem 4** (Allman–Matias–Rhodes 2009). If the observed variables have a tripartition
`S_1 ⊔ S_2 ⊔ S_3` into nonempty parts with `κ_t = ∏_{j ∈ S_t} k_j` and
`min(r, κ_1) + min(r, κ_2) + min(r, κ_3) ≥ 2r + 2`, then the parameters of `M(r; k_1, …, k_p)`
are generically identifiable up to label swapping.

Generically identifiable means: identifiability holds outside the zero set of some polynomial in
the parameters that does not vanish identically on the parameter space. Theorem 4 is proved by
applying Theorem 1 to three agglomerated variables, so only Theorem 1 is stated here; the module
defines the latent class model, its coordinates and identifiability up to label swapping. The
paper's variant with fixed positive class proportions, its hidden Markov model result (Theorem 6,
whose treatment of the initial distribution is not reproduced here), and its results for random
graph mixtures and nonparametric mixtures (Theorems 7-9) are not stated.

Sources: E. S. Allman, C. Matias and J. A. Rhodes, "Identifiability of parameters in latent
structure models with many observed variables", Ann. Statist. 37(6A):3099-3132, 2009,
doi:10.1214/09-AOS689, Theorems 1 and 4; J. B. Kruskal, "Three-way arrays: rank and uniqueness
of trilinear decompositions", Linear Algebra Appl. 18 (1977) 95-138.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.KruskalIdentifiabilityWanted

variable {r : ℕ}

/-- The tensor `[M_1, M_2, M_3]`: entry `(u, v, w)` is `∑_i M_1(i, u) M_2(i, v) M_3(i, w)`. -/
noncomputable def tensorEntry {κ₁ κ₂ κ₃ : ℕ} (M₁ : Fin r → Fin κ₁ → ℝ)
    (M₂ : Fin r → Fin κ₂ → ℝ) (M₃ : Fin r → Fin κ₃ → ℝ)
    (u : Fin κ₁) (v : Fin κ₂) (w : Fin κ₃) : ℝ :=
  ∑ i, M₁ i u * M₂ i v * M₃ i w

/-- `M` (with `r` rows) has Kruskal rank exactly `I`: `I ≤ r`, every set of `I` rows is linearly
independent, and, if `I < r`, some set of `I + 1` rows is linearly dependent. -/
def IsKruskalRank {κ : ℕ} (M : Fin r → Fin κ → ℝ) (I : ℕ) : Prop :=
  I ≤ r ∧ (∀ s : Finset (Fin r), s.card = I → LinearIndependent ℝ fun i : s => M i) ∧
    (I < r → ∃ s : Finset (Fin r), s.card = I + 1 ∧ ¬ LinearIndependent ℝ fun i : s => M i)

/-- **Kruskal's theorem** (Allman–Matias–Rhodes 2009, Theorem 1). Let `M_1, M_2, M_3` be real
matrices with `r` rows and Kruskal ranks exactly `I_1, I_2, I_3`, with
`I_1 + I_2 + I_3 ≥ 2r + 2`. If real matrices `N_1, N_2, N_3` of the same shapes give the same
tensor, then there are a permutation `σ` of the rows and scalars `c_1, c_2, c_3` with
`c_1(i) c_2(i) c_3(i) = 1` and `N_j(i, ·) = c_j(i) M_j(σ i, ·)` for every row `i` and every `j`.

Source: E. S. Allman, C. Matias and J. A. Rhodes, Ann. Statist. 37 (2009) 3099-3132, Theorem 1
(Kruskal 1977). -/
theorem_wanted kruskal_theorem {κ₁ κ₂ κ₃ : ℕ} (M₁ : Fin r → Fin κ₁ → ℝ)
    (M₂ : Fin r → Fin κ₂ → ℝ) (M₃ : Fin r → Fin κ₃ → ℝ) {I₁ I₂ I₃ : ℕ}
    (h₁ : IsKruskalRank M₁ I₁) (h₂ : IsKruskalRank M₂ I₂) (h₃ : IsKruskalRank M₃ I₃)
    (hsum : 2 * r + 2 ≤ I₁ + I₂ + I₃) (N₁ : Fin r → Fin κ₁ → ℝ) (N₂ : Fin r → Fin κ₂ → ℝ)
    (N₃ : Fin r → Fin κ₃ → ℝ)
    (hsame : ∀ u v w, tensorEntry N₁ N₂ N₃ u v w = tensorEntry M₁ M₂ M₃ u v w) :
    ∃ σ : Equiv.Perm (Fin r), ∃ c₁ c₂ c₃ : Fin r → ℝ, (∀ i, c₁ i * c₂ i * c₃ i = 1) ∧
      ∀ i, (∀ u, N₁ i u = c₁ i * M₁ (σ i) u) ∧ (∀ v, N₂ i v = c₂ i * M₂ (σ i) v) ∧
        ∀ w, N₃ i w = c₃ i * M₃ (σ i) w

/-- A point of the parameter space of the latent class model `M(r; k_1, …, k_p)`: class
proportions `π` forming a probability vector, and for each observed variable `j` a matrix `M j`
with `r` stochastic rows of length `k j`. -/
structure LatentClassParams (r p : ℕ) (k : Fin p → ℕ) where
  /-- The class proportions. -/
  π : Fin r → ℝ
  /-- The conditional distribution of observed variable `j` given each class. -/
  M : (j : Fin p) → Fin r → Fin (k j) → ℝ
  π_nonneg : ∀ i, 0 ≤ π i
  π_sum : ∑ i, π i = 1
  M_nonneg : ∀ j i u, 0 ≤ M j i u
  M_sum : ∀ j i, ∑ u, M j i u = 1

namespace LatentClassParams

variable {p : ℕ} {k : Fin p → ℕ}

/-- The joint distribution `P(x) = ∑_i π_i ∏_j M_j(i, x_j)` of the observed variables. -/
noncomputable def joint (P : LatentClassParams r p k) (x : (j : Fin p) → Fin (k j)) : ℝ :=
  ∑ i, P.π i * ∏ j, P.M j i (x j)

/-- The coordinates of a parameter point: the class proportions and all conditional
probabilities. -/
def coords (P : LatentClassParams r p k) : Fin r ⊕ (Σ j : Fin p, Fin r × Fin (k j)) → ℝ :=
  Sum.elim P.π fun e => P.M e.1 e.2.1 e.2.2

/-- The parameters `P` are identifiable up to label swapping: every parameter point with the
same joint distribution is obtained from `P` by permuting the classes. -/
def IsIdentifiableAt (P : LatentClassParams r p k) : Prop :=
  ∀ P' : LatentClassParams r p k, P'.joint = P.joint →
    ∃ σ : Equiv.Perm (Fin r), ∀ i, P'.π i = P.π (σ i) ∧ ∀ j u, P'.M j i u = P.M j (σ i) u

end LatentClassParams

end WantedExt.Biology.ComputationalBiology.KruskalIdentifiabilityWanted
