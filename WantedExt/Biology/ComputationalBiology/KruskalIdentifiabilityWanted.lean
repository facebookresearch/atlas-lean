/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generic identifiability via Kruskal's theorem

For `r × κⱼ` matrices `Mⱼ`, write `[M₁,M₂,M₃]` for the three-way tensor with
`(u,v,w)` entry `∑ᵢ m₁ᵢ(u) m₂ᵢ(v) m₃ᵢ(w)`. The Kruskal rank of `M` is the
largest `I` with every `I` rows linearly independent. Kruskal's theorem
(Theorem 1): if `I₁ + I₂ + I₃ ≥ 2r + 2`, then `[M₁,M₂,M₃]` determines the
factors up to simultaneous row permutation and rescaling. Hence the latent
class model `M(r; k₁,…,kₚ)` with a tripartition `S₁,S₂,S₃` of the observed
variables (`κᵢ` the product of state counts on `Sᵢ`) is generically
identifiable up to label swapping when
`min(r,κ₁) + min(r,κ₂) + min(r,κ₃) ≥ 2r + 2` (Theorem 4): outside the zero
set of some nonzero parameter polynomial, equal distributions imply equal
parameters. An HMM with `r` hidden and `κ` observable states is generically
identifiable from `2k+1` consecutive variables when `C(k+κ-1,κ-1) ≥ r`
(Theorem 6).

Overlap: none found (no Kruskal-rank tensor identifiability; the MST
`Kruskal.lean` and matroid files are unrelated).

Sources: E. S. Allman, C. Matias and J. A. Rhodes, "Identifiability of
parameters in latent structure models with many observed variables", Ann.
Statist. 37(6A):3099-3132, 2009, doi:10.1214/09-AOS689, Theorems 1, 4, 6.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.KruskalIdentifiabilityWanted

open Classical

variable {r : ℕ}

/-- Tensor entry: `∑ᵢ m₁ᵢ(u) m₂ᵢ(v) m₃ᵢ(w)`. -/
noncomputable def tensorEntry {κ₁ κ₂ κ₃ : ℕ} (M₁ : Fin r → Fin κ₁ → ℝ)
    (M₂ : Fin r → Fin κ₂ → ℝ) (M₃ : Fin r → Fin κ₃ → ℝ)
    (u : Fin κ₁) (v : Fin κ₂) (w : Fin κ₃) : ℝ :=
  Finset.sum Finset.univ fun i => M₁ i u * M₂ i v * M₃ i w

/-- Kruskal rank property at level `I`: every `I` rows independent, and some
`I+1` rows dependent (vacuous maximality is fine for the statements). -/
def IsKruskalRank {κ : ℕ} (M : Fin r → Fin κ → ℝ) (I : ℕ) : Prop :=
  (∀ s : Finset (Fin r), s.card = I →
    LinearIndependent ℝ fun i : s => M i) ∧
    ∀ J : ℕ, I < J → J ≤ r →
      ∃ s : Finset (Fin r), s.card = J ∧
        ¬ LinearIndependent ℝ fun i : s => M i

/-- **Kruskal's theorem** (Allman-Matias-Rhodes 2009, Theorem 1): hypotheses
are three factor matrices with Kruskal ranks `I₁,I₂,I₃` (`hrank`) summing
to at least `2r+2` (`hsum`). Conclusion: any second factorization of the
same tensor agrees up to a common row permutation `σ` and nonzero
per-row rescalings multiplying to one.

Source: Allman-Matias-Rhodes (2009), Theorem 1. -/
theorem_wanted kruskal_theorem {κ₁ κ₂ κ₃ : ℕ}
    (M₁ : Fin r → Fin κ₁ → ℝ) (M₂ : Fin r → Fin κ₂ → ℝ)
    (M₃ : Fin r → Fin κ₃ → ℝ)
    (I₁ I₂ I₃ : ℕ)
    (hrank : IsKruskalRank M₁ I₁ ∧ IsKruskalRank M₂ I₂ ∧
      IsKruskalRank M₃ I₃)
    (hsum : I₁ + I₂ + I₃ ≥ 2 * r + 2)
    (N₁ : Fin r → Fin κ₁ → ℝ) (N₂ : Fin r → Fin κ₂ → ℝ)
    (N₃ : Fin r → Fin κ₃ → ℝ)
    (hsame : ∀ u v w, tensorEntry M₁ M₂ M₃ u v w =
      tensorEntry N₁ N₂ N₃ u v w) :
    ∃ σ : Equiv.Perm (Fin r), ∃ c₁ c₂ c₃ : Fin r → ℝ,
      (∀ i, c₁ i * c₂ i * c₃ i = 1) ∧
        ∀ i u v w, N₁ i u = c₁ i * M₁ (σ i) u ∧
          N₂ i v = c₂ i * M₂ (σ i) v ∧ N₃ i w = c₃ i * M₃ (σ i) w

/-- Latent-class parameters: mixing proportions on the simplex and three
conditional matrices with stochastic rows. -/
structure LatentParams (r κ₁ κ₂ κ₃ : ℕ) where
  pi : Fin r → ℝ
  M₁ : Fin r → Fin κ₁ → ℝ
  M₂ : Fin r → Fin κ₂ → ℝ
  M₃ : Fin r → Fin κ₃ → ℝ
  pi_nonneg : ∀ i, 0 ≤ pi i
  pi_sum : Finset.sum Finset.univ pi = 1
  stoch1 : ∀ i u, 0 ≤ M₁ i u
  stoch1sum : ∀ i, Finset.sum Finset.univ (M₁ i) = 1
  stoch2 : ∀ i v, 0 ≤ M₂ i v
  stoch2sum : ∀ i, Finset.sum Finset.univ (M₂ i) = 1
  stoch3 : ∀ i w, 0 ≤ M₃ i w
  stoch3sum : ∀ i, Finset.sum Finset.univ (M₃ i) = 1

/-- Flat parameter index: mixing weights plus all conditional entries. -/
abbrev PIdx (r κ₁ κ₂ κ₃ : ℕ) :=
  Fin r ⊕ (Fin r × Fin κ₁) ⊕ (Fin r × Fin κ₂) ⊕ (Fin r × Fin κ₃)

/-- Parameter valuation from structured parameters. -/
def valOf {κ₁ κ₂ κ₃ : ℕ} (P : LatentParams r κ₁ κ₂ κ₃) :
    PIdx r κ₁ κ₂ κ₃ → ℝ :=
  Sum.elim P.pi (Sum.elim (fun p => P.M₁ p.1 p.2)
    (Sum.elim (fun p => P.M₂ p.1 p.2) (fun p => P.M₃ p.1 p.2)))

/-- Joint distribution of the latent-class model (first factor reweighted
by the mixing proportions). -/
noncomputable def jointTensor {κ₁ κ₂ κ₃ : ℕ} (P : LatentParams r κ₁ κ₂ κ₃)
    (u : Fin κ₁) (v : Fin κ₂) (w : Fin κ₃) : ℝ :=
  Finset.sum Finset.univ fun i => P.pi i * P.M₁ i u * P.M₂ i v * P.M₃ i w

/-- **Generic identifiability of latent class models** (Allman-Matias-Rhodes
2009, Theorem 4): hypotheses are latent parameters with fixed positive
mixing proportions (`hpos`), a tripartition rank condition
(`htri`: `min(r,κ₁)+min(r,κ₂)+min(r,κ₃) ≥ 2r+2`), and a nonzero parameter
polynomial avoided by the parameters (`Q`, `hQ`, `hgen`). Conclusion: equal
joint distributions force equal parameters up to permuting hidden labels.

Source: Allman-Matias-Rhodes (2009), Theorem 4. -/
theorem_wanted latent_class_identifiable {κ₁ κ₂ κ₃ : ℕ}
    (P : LatentParams r κ₁ κ₂ κ₃)
    (hpos : ∀ i, 0 < P.pi i)
    (htri : min r κ₁ + min r κ₂ + min r κ₃ ≥ 2 * r + 2)
    (Q : MvPolynomial (PIdx r κ₁ κ₂ κ₃) ℝ)
    (hQ : Q ≠ 0)
    (hgen : MvPolynomial.eval (valOf P) Q ≠ 0)
    (P' : LatentParams r κ₁ κ₂ κ₃)
    (hsame : ∀ u v w, jointTensor P u v w = jointTensor P' u v w) :
    ∃ σ : Equiv.Perm (Fin r), (∀ i, P'.pi i = P.pi (σ i)) ∧
      (∀ i u, P'.M₁ i u = P.M₁ (σ i) u) ∧
        (∀ i v, P'.M₂ i v = P.M₂ (σ i) v) ∧
          ∀ i w, P'.M₃ i w = P.M₃ (σ i) w

/-- HMM window marginal: sum over hidden paths of initial-by-transition-by-
emission products. -/
noncomputable def hmmMarginal (r κ k : ℕ) (trans : Fin r → Fin r → ℝ)
    (emit : Fin r → Fin κ → ℝ) (pi0 : Fin r → ℝ)
    (w : Fin (2 * k + 1) → Fin κ) : ℝ :=
  Finset.sum Finset.univ fun h : Fin (2 * k + 1) → Fin r =>
    pi0 (h 0) *
      (Finset.prod Finset.univ fun t : Fin (2 * k) =>
        trans (h ⟨t.val, by omega⟩) (h ⟨t.val + 1, by omega⟩)) *
      Finset.prod Finset.univ fun t => emit (h t) (w t)

/-- **Generic identifiability of HMMs** (Allman-Matias-Rhodes 2009,
Theorem 6): hypotheses are `r` hidden states, `κ` observable states, a
window `2k+1` with `C(k+κ-1,κ-1) ≥ r` (`hwin`), positive transitions,
emissions, and initial distribution (`hpos`), and genericity via a nonzero
avoided polynomial (`Q`, `hQ`, `hgen`). Conclusion: equal window marginals
force equal parameters up to label swapping.

Source: Allman-Matias-Rhodes (2009), Theorem 6. -/
theorem_wanted hmm_identifiable (r κ k : ℕ)
    (trans : Fin r → Fin r → ℝ) (emit : Fin r → Fin κ → ℝ)
    (pi0 : Fin r → ℝ)
    (hwin : (k + κ - 1).choose (κ - 1) ≥ r)
    (hpos : (∀ i j, 0 < trans i j) ∧ (∀ i a, 0 < emit i a) ∧
      ∀ i, 0 < pi0 i)
    (Q : MvPolynomial (Fin r ⊕ (Fin r × Fin r) ⊕ (Fin r × Fin κ)) ℝ)
    (hQ : Q ≠ 0)
    (hgen : MvPolynomial.eval
      (Sum.elim pi0 (Sum.elim (fun p => trans p.1 p.2)
        (fun p => emit p.1 p.2))) Q ≠ 0)
    (trans' : Fin r → Fin r → ℝ) (emit' : Fin r → Fin κ → ℝ)
    (pi0' : Fin r → ℝ)
    (hsame : ∀ w : Fin (2 * k + 1) → Fin κ,
      hmmMarginal r κ k trans emit pi0 w =
        hmmMarginal r κ k trans' emit' pi0' w) :
    ∃ σ : Equiv.Perm (Fin r),
      (∀ i, pi0' i = pi0 (σ i)) ∧
        (∀ i j, trans' i j = trans (σ i) (σ j)) ∧
          ∀ i a, emit' i a = emit (σ i) a

end WantedExt.Biology.ComputationalBiology.KruskalIdentifiabilityWanted
