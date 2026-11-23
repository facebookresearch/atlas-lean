/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Monotone bounded sequences of positive semidefinite matrices converge

If `A : ℕ → Matrix m m ℝ` is Loewner-nondecreasing — every difference
`A j - A i` for `i ≤ j` is positive semidefinite — each `A n` is
symmetric (`IsHermitian`), and some matrix `B` Loewner-dominates every
term (`B - A n` positive semidefinite for all `n`), then `A` converges
entrywise to a symmetric limit `L` that still dominates every term:
`(L - A n).PosSemidef` for all `n`. This is the monotone-convergence
fact behind Riccati iteration arguments: for each fixed vector `x` the
quadratic forms `xᵀ(A n)x` form a monotone bounded real sequence, and
polarization recovers the entries. The symmetry hypothesis cannot be
dropped: positive semidefinite differences alone allow a constant
nonsymmetric sequence, whose limit is not symmetric. Loewner order is
expressed through `Matrix.PosSemidef` of differences because Mathlib
has no Loewner partial-order instance on matrices.

Provenance: the classical monotone convergence theorem for
Loewner-monotone matrix sequences; control-theory roadmap leaf
`SSC-G03.T08` (clause `SSC-G03.c04`).
-/

open Filter Topology Matrix

@[expose] public section

private lemma quad_single_single {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (a b : m) :
    Pi.single a (1 : ℝ) ⬝ᵥ (M *ᵥ Pi.single b 1) = M a b := by
  rw [single_one_dotProduct, Matrix.mulVec_single_one]
  rfl

private lemma quad_mono {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ}
    (hmono : ∀ i j : ℕ, i ≤ j → (A j - A i).PosSemidef)
    (x : m → ℝ) : Monotone (fun n : ℕ => star x ⬝ᵥ ((A n) *ᵥ x)) := by
  intro i j hij
  have h := (hmono i j hij).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  exact sub_nonneg.mp h

private lemma quad_bdd {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ} {B : Matrix m m ℝ}
    (hbdd : ∀ n : ℕ, (B - A n).PosSemidef)
    (x : m → ℝ) : BddAbove (Set.range (fun n : ℕ => star x ⬝ᵥ ((A n) *ᵥ x))) := by
  refine ⟨star x ⬝ᵥ (B *ᵥ x), ?_⟩
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  have h := (hbdd n).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  exact sub_nonneg.mp h

private lemma quad_tendsto_exists {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ} {B : Matrix m m ℝ}
    (hmono : ∀ i j : ℕ, i ≤ j → (A j - A i).PosSemidef)
    (hbdd : ∀ n : ℕ, (B - A n).PosSemidef)
    (x : m → ℝ) : ∃ l : ℝ, Tendsto (fun n : ℕ => star x ⬝ᵥ ((A n) *ᵥ x)) atTop (𝓝 l) :=
  ⟨_, tendsto_atTop_ciSup (quad_mono hmono x) (quad_bdd hbdd x)⟩

private lemma hermitian_symm_entry {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ}
    (hA : ∀ n : ℕ, (A n).IsHermitian) (n : ℕ) (i j : m) :
    A n i j = A n j i := by
  have h := (hA n).apply i j
  rw [star_trivial] at h
  exact h.symm

private lemma entry_eq_polar {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ}
    (hA : ∀ n : ℕ, (A n).IsHermitian) (n : ℕ) (i j : m) :
    A n i j = (star (Pi.single i 1 + Pi.single j 1) ⬝ᵥ
        ((A n) *ᵥ (Pi.single i 1 + Pi.single j 1))
      - star (Pi.single i (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single i 1)
      - star (Pi.single j (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single j 1)) / 2 := by
  have hsym : A n j i = A n i j := (hermitian_symm_entry hA n i j).symm
  have e1 : star (Pi.single i (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single i 1) = A n i i := by
    rw [star_trivial]
    exact quad_single_single _ _ _
  have e2 : star (Pi.single j (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single j 1) = A n j j := by
    rw [star_trivial]
    exact quad_single_single _ _ _
  have eS : star (Pi.single i 1 + Pi.single j 1) ⬝ᵥ
        ((A n) *ᵥ (Pi.single i 1 + Pi.single j 1))
      = (A n i i + A n j i) + (A n i j + A n j j) := by
    rw [star_trivial, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      quad_single_single, quad_single_single, quad_single_single, quad_single_single]
  rw [eS, e1, e2, hsym]
  ring

private lemma quad_expand {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (x : m → ℝ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ i, (x i * ∑ j, M i j * x j) := by
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Pi.star_apply, star_trivial]

/-- A Loewner-nondecreasing sequence of real symmetric matrices that is
bounded above converges entrywise to a symmetric limit dominating every
term (roadmap leaf `SSC-G03.T08`). Monotonicity and the bound are stated
with `Matrix.PosSemidef` differences: `A j - A i` is positive semidefinite
for `i ≤ j`, and `B - A n` is positive semidefinite for every `n`. -/
theorem Matrix.tendsto_of_monotone_loewner {m : Type*} [Fintype m] [DecidableEq m]
    {A : ℕ → Matrix m m ℝ} {B : Matrix m m ℝ}
    (hA : ∀ n : ℕ, (A n).IsHermitian)
    (hmono : ∀ i j : ℕ, i ≤ j → (A j - A i).PosSemidef)
    (hbdd : ∀ n : ℕ, (B - A n).PosSemidef) :
    ∃ L : Matrix m m ℝ, L.IsHermitian ∧ (∀ n : ℕ, (L - A n).PosSemidef) ∧
      ∀ i j : m, Tendsto (fun n : ℕ => A n i j) atTop (𝓝 (L i j)) := by
  have hentry : ∀ i j : m, ∃ l : ℝ, Tendsto (fun n : ℕ => A n i j) atTop (𝓝 l) := by
    intro i j
    obtain ⟨lS, hlS⟩ := quad_tendsto_exists hmono hbdd (Pi.single i 1 + Pi.single j 1)
    obtain ⟨li, hli⟩ := quad_tendsto_exists hmono hbdd (Pi.single i (1 : ℝ))
    obtain ⟨lj, hlj⟩ := quad_tendsto_exists hmono hbdd (Pi.single j (1 : ℝ))
    refine ⟨(lS - li - lj) / 2, ?_⟩
    have heq : (fun n : ℕ => A n i j) = fun n : ℕ =>
        (star (Pi.single i 1 + Pi.single j 1) ⬝ᵥ
          ((A n) *ᵥ (Pi.single i 1 + Pi.single j 1))
        - star (Pi.single i (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single i 1)
        - star (Pi.single j (1 : ℝ)) ⬝ᵥ ((A n) *ᵥ Pi.single j 1)) / 2 :=
      funext (fun n => entry_eq_polar hA n i j)
    rw [heq]
    exact ((hlS.sub hli).sub hlj).div_const 2
  have hchoose : ∃ L : Matrix m m ℝ,
      ∀ i j : m, Tendsto (fun n : ℕ => A n i j) atTop (𝓝 (L i j)) := by
    choose L hL using hentry
    exact ⟨L, hL⟩
  obtain ⟨L, hL⟩ := hchoose
  have hLsym : ∀ i j : m, L i j = L j i := fun i j =>
    tendsto_nhds_unique_of_forall (hL i j) (hL j i)
      (fun n => hermitian_symm_entry hA n i j)
  have hLherm : L.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    rw [star_trivial]
    exact hLsym j i
  have hdom : ∀ n : ℕ, (L - A n).PosSemidef := by
    intro n
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hLherm.sub (hA n))
    intro x
    have hquad : Tendsto (fun k : ℕ => star x ⬝ᵥ ((A k) *ᵥ x)) atTop
        (𝓝 (star x ⬝ᵥ (L *ᵥ x))) := by
      simp only [quad_expand]
      apply tendsto_finsetSum _ (fun i _ => ?_)
      apply Filter.Tendsto.const_mul
      apply tendsto_finsetSum _ (fun j _ => ?_)
      exact (hL i j).mul_const (x j)
    have hge : ∀ k : ℕ, n ≤ k → star x ⬝ᵥ ((A n) *ᵥ x) ≤ star x ⬝ᵥ ((A k) *ᵥ x) := by
      intro k hnk
      have h := (hmono n k hnk).dotProduct_mulVec_nonneg x
      rw [Matrix.sub_mulVec, dotProduct_sub] at h
      exact sub_nonneg.mp h
    have hlim := ge_of_tendsto hquad ((eventually_ge_atTop n).mono fun k hk => hge k hk)
    rw [Matrix.sub_mulVec, dotProduct_sub]
    exact sub_nonneg.mpr hlim
  exact ⟨L, hLherm, hdom, hL⟩
