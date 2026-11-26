/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.BruhatTitsTree
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.BruhatTits CerednikDrinfeld.Mumford LT.LatticeTree

universe u

/-- Consumer with the original binders: two vertices are adjacent in the tree iff they are
distinct and have adjacent representatives in one order or the other. -/
private theorem exactSource {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (x y : Vertex R K) :
    (tree R K).Adj x y ↔ x ≠ y ∧ (VertRel R K x y ∨ VertRel R K y x) :=
  tree_adj_iff x y

/-- Higher-universe consumer: `GL₂(K)` and `PGL₂(K)` act on the tree by graph automorphisms. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    [IsFractionRing R K] (g : GL (Fin 2) K) {x y : Vertex R K} (h : (tree R K).Adj x y) :
    (tree R K).Adj (g • x) (g • y) ∧
      (tree R K).Adj (Matrix.ProjGenLinGroup.mk g • x) (Matrix.ProjGenLinGroup.mk g • y) :=
  ⟨GraphAction.smul_adj g h, GraphAction.smul_adj (Matrix.ProjGenLinGroup.mk g) h⟩

/-- Scalars act trivially, so the `PGL₂` action is well defined. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] (c : Kˣ)
    (v : Vertex R K) : Matrix.GeneralLinearGroup.scalar (Fin 2) c • v = v :=
  scalar_smul_vertex c v

/-- For an irreducible `ϖ`, the standard vertex is adjacent to its `diag(1, ϖ)`-translate. -/
private theorem adj_stdVertex_diagSnd {R : Type u} [CommRing R] {K : Type u} [Field K]
    [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    (tree R K).Adj (stdVertex R K)
      (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero) • stdVertex R K) := by
  rw [tree_adj_iff]
  refine ⟨(stdVertex_ne_act_diagSnd hϖ).symm, Or.inl ?_⟩
  exact ⟨stdLattice R K, _, isFullLattice_stdLattice, IsFullLattice.map isFullLattice_stdLattice _,
    rfl, rfl, adjacentLattice_stdLattice_diagSnd hϖ⟩

/-- The `2`-adic tree has an edge at the standard vertex. -/
example : (tree ℤ_[2] ℚ_[2]).Adj (stdVertex ℤ_[2] ℚ_[2])
    (diagSnd (unitOfNeZero (K := ℚ_[2]) (PadicInt.irreducible_p (p := 2)).ne_zero) •
      stdVertex ℤ_[2] ℚ_[2]) :=
  adj_stdVertex_diagSnd PadicInt.irreducible_p

/-- Boundary: irreducibility matters. For the unit `ϖ = 1`, `diag(1, ϖ)` is the identity, so the
translate is the standard vertex itself, which is not adjacent to itself. -/
example {R : Type u} [CommRing R] [Nontrivial R] {K : Type u} [Field K] [Algebra R K]
    [IsFractionRing R K] :
    ¬ (tree R K).Adj (stdVertex R K)
      (diagSnd (unitOfNeZero (K := K) (one_ne_zero (α := R))) • stdVertex R K) := by
  have h1 : diagSnd (unitOfNeZero (K := K) (one_ne_zero (α := R))) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1, one_smul]
  exact (tree R K).irrefl
