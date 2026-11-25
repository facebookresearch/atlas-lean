/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Defs.Basic

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Scottish Book Problem 151 -/

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook151Wanted

/-- **The closed cube $[-1, 1]^3$.** The closed cube $[-1, 1]^3$ in $\mathbb{R}^3$: the set of
points of three-dimensional Euclidean space all of whose coordinates lie in $[-1, 1]$. -/
def Cube : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- **Edges of the cube $[-1, 1]^3$.** The union of the edges of the cube $[-1, 1]^3$ in
$\mathbb{R}^3$: the set of points $x$ with every coordinate in $[-1, 1]$ such that at least two
distinct coordinates $x_i$ and $x_j$ are each equal to $1$ or $-1$. -/
def CubeEdges : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∃ i j, i ≠ j ∧ (x i = 1 ∨ x i = -1) ∧ (x j = 1 ∨ x j = -1)}

private abbrev R3 := EuclideanSpace ℝ (Fin 3)

-- The three-dimensional Vandermonde in the squared coordinates, with the factors in cyclic order.
private noncomputable def cubePolynomial (x : R3) : ℝ :=
  (x 0 ^ 2 - x 1 ^ 2) * (x 1 ^ 2 - x 2 ^ 2) * (x 2 ^ 2 - x 0 ^ 2)

private theorem cubePolynomial_contDiff : ContDiff ℝ 2 cubePolynomial := by
  have sq (i : Fin 3) : ContDiff ℝ 2 (fun x : R3 ↦ x i ^ 2) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).contDiff).pow 2
  exact (((sq 0).sub (sq 1)).mul ((sq 1).sub (sq 2))).mul ((sq 2).sub (sq 0))

-- Restriction to a line computes the diagonal entry of the second Fréchet derivative.
private theorem secondAlongLine {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (x v : R3) :
    iteratedFDeriv ℝ 2 f x ![v, v] = iteratedDeriv 2 (fun t : ℝ ↦ f (t • v + x)) 0 := by
  let L : ℝ →L[ℝ] R3 := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have h : ContDiff ℝ 2 (fun y ↦ f (y + x)) := hf.comp (by fun_prop)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change _ = iteratedFDeriv ℝ 2 ((fun y ↦ f (y + x)) ∘ L) 0 (fun _ ↦ 1)
  rw [L.iteratedFDeriv_comp_right h 0 le_rfl, iteratedFDeriv_comp_add_right]
  have hvec : (fun _ : Fin 2 ↦ L 1) = ![v, v] := by
    ext i
    fin_cases i <;> simp [L]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, ← hvec]

-- With the other two squared coordinates fixed, the restriction is a quartic in one coordinate.
private theorem secondQuartic (a b s : ℝ) :
    iteratedDeriv 2 (fun t : ℝ ↦ (t ^ 2 - a) * (a - b) * (b - t ^ 2)) s =
      (a - b) * (2 * (a + b) - 12 * s ^ 2) := by
  have h : (fun t : ℝ ↦ (t ^ 2 - a) * (a - b) * (b - t ^ 2)) =
      (fun t : ℝ ↦ -(a - b) * t ^ 4 + ((a - b) * (a + b)) * t ^ 2 - (a - b) * a * b) := by
    funext t
    ring
  rw [h, iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  norm_num [iteratedDeriv_const, Nat.descFactorial]
  ring

open Laplacian in
private theorem cubePolynomial_laplacian (x : R3) : Δ cubePolynomial x = 0 := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have second (i : Fin 3) (a b : ℝ)
      (h : ∀ t : ℝ, cubePolynomial (t • e i + x) =
        ((t + x i) ^ 2 - a) * (a - b) * (b - (t + x i) ^ 2)) :
      iteratedFDeriv ℝ 2 cubePolynomial x ![e i, e i] =
        (a - b) * (2 * (a + b) - 12 * (x i) ^ 2) := by
    rw [secondAlongLine cubePolynomial_contDiff, funext h,
      iteratedDeriv_comp_add_const 2 (fun t ↦ (t ^ 2 - a) * (a - b) * (b - t ^ 2))]
    simpa only [zero_add] using secondQuartic a b (x i)
  have h₀ := second 0 (x 1 ^ 2) (x 2 ^ 2) (by
    intro t
    simp [e, cubePolynomial])
  have h₁ := second 1 (x 2 ^ 2) (x 0 ^ 2) (by
    intro t
    simp [e, cubePolynomial]
    ring)
  have h₂ := second 2 (x 0 ^ 2) (x 1 ^ 2) (by
    intro t
    simp [e, cubePolynomial]
    ring)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
  simp only [Fin.sum_univ_three, h₀, h₁, h₂]
  ring

private theorem cubePolynomial_harmonic :
    InnerProductSpace.HarmonicOnNhd cubePolynomial Set.univ := fun _ _ ↦
  ⟨cubePolynomial_contDiff.contDiffAt, Filter.Eventually.of_forall cubePolynomial_laplacian⟩

private theorem cubePolynomial_edge (x : R3) (hx : x ∈ CubeEdges) : cubePolynomial x = 0 := by
  obtain ⟨_, i, j, hij, hi, hj⟩ := hx
  have hi' : x i ^ 2 = 1 := by rcases hi with hi | hi <;> norm_num [hi]
  have hj' : x j ^ 2 = 1 := by rcases hj with hj | hj <;> norm_num [hj]
  have indices (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases indices i with rfl | rfl | rfl <;> rcases indices j with rfl | rfl | rfl <;> first
    | exact (hij rfl).elim
    | rw [cubePolynomial, hi', hj']; simp

private theorem cubePolynomial_sample : cubePolynomial !₂[0, 1 / 2, 1] = 3 / 16 := by
  change ((0 : ℝ) ^ 2 - (1 / 2) ^ 2) * ((1 / 2) ^ 2 - 1 ^ 2) * (1 ^ 2 - 0 ^ 2) = 3 / 16
  norm_num

/--
**Scottish Book Problem 151: a harmonic function vanishing on the edges of a cube.** There
exist a connected open set $U \subseteq \mathbb{R}^3$ whose interior contains the closed cube
$[-1, 1]^3$ and a function $f : \mathbb{R}^3 \to \mathbb{R}$ that is harmonic at every point of
$U$, vanishes at every point of the edges of the cube $[-1, 1]^3$, and satisfies $f(x) \neq 0$
for some $x \in U$.

Source: R. Wavre, Problem 151 of the Scottish Book; the affirmative answer
is given by I. Vasilyev, "On the zero sets of harmonic polynomials",
arXiv:2506.24116, Theorem 1, as reported in the 2026 survey "90+ years of
the Scottish Book" (arXiv:2603.27867). The typescript notes a prize of a
"fondue" in Geneva.
-/
theorem harmonicFunctionVanishesOnCubeEdges :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      IsOpen U ∧ IsConnected U ∧ Cube ⊆ interior U ∧ InnerProductSpace.HarmonicOnNhd f U ∧
        (∀ x ∈ CubeEdges, f x = 0) ∧ ∃ x ∈ U, f x ≠ 0 := by
  refine ⟨Set.univ, cubePolynomial, isOpen_univ, isConnected_univ, by simp, cubePolynomial_harmonic,
    cubePolynomial_edge, !₂[0, 1 / 2, 1], Set.mem_univ _, ?_⟩
  rw [cubePolynomial_sample]
  norm_num

end MathlibExt.Analysis.ScottishBook151Wanted
