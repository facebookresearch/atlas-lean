/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Solvable
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
# Permutation stability of groups

Normalized and flexible Hamming distances between permutations, almost-homomorphisms,
and (flexible) permutation stability, following Kourovka Notebook 21.84.
-/

namespace PermutationStability

/-- **Normalized Hamming distance.** For a natural number $n$ and permutations $\sigma$, $\tau$ of
$\{0, \dots, n-1\}$, the normalized Hamming distance $d_n(\sigma, \tau)$ is the number of points
$i < n$ with $\sigma(i) \ne \tau(i)$, divided by $n$, as a real number. For $n = 0$ it is $0$;
this single value does not affect statements about limits as $n \to \infty$. -/
noncomputable def normalizedHammingDistance (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  (hammingDist (fun i => σ i) (fun i => τ i) : ℝ) / n

/-- **Almost-homomorphisms to symmetric groups.** Let $G$ be a group and, for each natural number
$n$, let $f_n \colon G \to S_n$ be an arbitrary map, where $S_n$ is the group of permutations of
$\{0, \dots, n-1\}$. The sequence $(f_n)$ is an almost-homomorphism when for all $g, h \in G$ the
normalized Hamming distance $d_n(f_n(g) f_n(h), f_n(gh))$ tends to $0$ as $n \to \infty$.

Following the source, no condition such as $f_n(1) = 1$ is imposed. -/
def IsAlmostHomomorphism {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∀ g h : G, Filter.Tendsto
    (fun n => normalizedHammingDistance n (f n g * f n h) (f n (g * h)))
    Filter.atTop (nhds 0)

/-- **Closeness to homomorphisms.** Let $G$ be a group and let $f_n \colon G \to S_n$
($n \in \mathbb{N}$) be maps into the symmetric groups $S_n$ of permutations of $\{0, \dots, n-1\}$.
The sequence $(f_n)$ is close to homomorphisms when there are group homomorphisms
$\rho_n \colon G \to S_n$ such that for every $g \in G$ the normalized Hamming distance
$d_n(\rho_n(g), f_n(g))$ tends to $0$ as $n \to \infty$. -/
def IsCloseToHomomorphisms {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∃ ρ : ∀ n : ℕ, G →* Equiv.Perm (Fin n), ∀ g : G, Filter.Tendsto
    (fun n => normalizedHammingDistance n (ρ n g) (f n g))
    Filter.atTop (nhds 0)

/-- **Permutation stability.** A group $G$ is permutation stable when every
almost-homomorphism $(f_n)$ from $G$ to the symmetric groups $S_n$ is close to
homomorphisms. -/
def PermutationStable (G : Type*) [Group G] : Prop :=
  ∀ f : ∀ n : ℕ, G → Equiv.Perm (Fin n),
    IsAlmostHomomorphism f → IsCloseToHomomorphisms f

/-- **Flexible Hamming distance.** Let $n \le m$ be natural numbers, $\sigma$ a permutation of
$\{0, \dots, n-1\}$ and $\tau$ a permutation of $\{0, \dots, m-1\}$. The flexible Hamming distance
of $\sigma$ and $\tau$ is the real number

$$
d^{\mathrm{flex}}_n(\sigma, \tau) = \frac{\#\{i < n : \sigma(i) \ne \tau(i)\} + (m - n)}{n}.
$$

For $n = 0$ this quotient is taken to be $0$; this single value does not affect statements about
limits as $n \to \infty$.

Source: Kourovka Notebook 21.84. The source is internally inconsistent about the argument order: it
first defines the distance with the small permutation first, `d_n^flex(σ, τ)` for `σ ∈ S_n`,
`τ ∈ S_m`, but later writes the convergence expression with `ρ_n(g)` first. This formalization
follows the definition site (small first), which is also the type-correct order for the embedding
`Fin n → Fin m`. -/
noncomputable def flexibleHammingDistance {n m : ℕ} (h : n ≤ m)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) : ℝ :=
  ((hammingDist (fun i => Fin.castLE h (σ i))
      (fun i => τ (Fin.castLE h i)) + (m - n) : ℕ) : ℝ) / n

/-- **Flexible closeness to homomorphisms.** Let $G$ be a group and let $f_n \colon G \to S_n$
($n \in \mathbb{N}$) be maps into the symmetric groups $S_n$ of permutations of $\{0, \dots, n-1\}$.
The sequence $(f_n)$ is flexibly close to homomorphisms when there are natural numbers $m_n \ge n$
and group homomorphisms $\rho_n \colon G \to S_{m_n}$ such that for every $g \in G$ the flexible
Hamming distance $d^{\mathrm{flex}}_n(f_n(g), \rho_n(g))$ tends to $0$ as $n \to \infty$. -/
def IsFlexiblyCloseToHomomorphisms {G : Type*} [Group G]
    (f : ∀ n : ℕ, G → Equiv.Perm (Fin n)) : Prop :=
  ∃ m : ℕ → ℕ, ∃ h : ∀ n : ℕ, n ≤ m n,
    ∃ ρ : ∀ n : ℕ, G →* Equiv.Perm (Fin (m n)), ∀ g : G, Filter.Tendsto
      (fun n => flexibleHammingDistance (h n) (f n g) (ρ n g))
      Filter.atTop (nhds 0)

/-- **Flexible permutation stability.** A group $G$ is flexibly permutation stable when every
almost-homomorphism $(f_n)$ from $G$ to the symmetric groups is flexibly close to homomorphisms. -/
def FlexiblePermutationStable (G : Type*) [Group G] : Prop :=
  ∀ f : ∀ n : ℕ, G → Equiv.Perm (Fin n),
    IsAlmostHomomorphism f → IsFlexiblyCloseToHomomorphisms f

/-- **Metabelian groups.** Let $G$ be a group and let $G' = [G, G]$ be its commutator subgroup.
Then $G$ is metabelian when its second derived subgroup $G'' = [G', G']$ is trivial. -/
def Metabelian (G : Type*) [Group G] : Prop :=
  derivedSeries G 2 = ⊥

theorem normalizedHammingDistance_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    normalizedHammingDistance n σ σ = 0 := by
  simp [normalizedHammingDistance]

theorem normalizedHammingDistance_nonneg (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    0 ≤ normalizedHammingDistance n σ τ := by
  unfold normalizedHammingDistance
  positivity

theorem normalizedHammingDistance_le_one {n : ℕ} (hn : 0 < n)
    (σ τ : Equiv.Perm (Fin n)) :
    normalizedHammingDistance n σ τ ≤ 1 := by
  unfold normalizedHammingDistance
  rw [div_le_one (Nat.cast_pos.mpr hn)]
  have h := hammingDist_le_card_fintype (x := fun i => σ i) (y := fun i => τ i)
  rw [Fintype.card_fin] at h
  exact Nat.cast_le.mpr h

theorem flexibleHammingDistance_self {n m : ℕ} (h : n ≤ m)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (hτ : ∀ i, τ (Fin.castLE h i) = Fin.castLE h (σ i)) :
    flexibleHammingDistance h σ τ = ((m - n : ℕ) : ℝ) / n := by
  have hfun : (fun i => τ (Fin.castLE h i)) = (fun i => Fin.castLE h (σ i)) :=
    funext hτ
  unfold flexibleHammingDistance
  rw [hfun, hammingDist_self, Nat.zero_add]

theorem flexibleHammingDistance_diagonal {n : ℕ} (h : n ≤ n)
    (σ τ : Equiv.Perm (Fin n)) :
    flexibleHammingDistance h σ τ = normalizedHammingDistance n σ τ := by
  have hfun : (fun i => Fin.castLE h (σ i)) = (fun i => σ i) :=
    funext fun i => Fin.ext rfl
  have hfun' : (fun i => τ (Fin.castLE h i)) = (fun i => τ i) :=
    funext fun i => congrArg (τ ·) (Fin.ext rfl)
  unfold flexibleHammingDistance normalizedHammingDistance
  rw [hfun, hfun', Nat.sub_self, Nat.add_zero]

end PermutationStability
