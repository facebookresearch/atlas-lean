/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeOrbital
public import MathlibExt.Combinatorics.SimpleGraph.GraphAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The lattice graph and the Bruhat-Tits tree

Three cases, with increasing hypotheses:

* For a commutative ring `R` and any `R`-algebra field `K`, the homothety classes of full
  `R`-lattices in `K²` (`LT.LatticeTree.Vertex R K`) carry an action of `GL₂(K)`, which factors
  through `PGL₂(K)`.
* When `K` is the fraction field of `R`, `CerednikDrinfeld.BruhatTits.tree R K` is the simple graph
  on these classes whose edges join classes with adjacent representatives (`ϖ L < L' < L` for an
  irreducible `ϖ`), and both groups act on it by graph automorphisms
  (`CerednikDrinfeld.Mumford.GraphAction`).
* When `R` is moreover a discrete valuation ring, this graph is the Bruhat-Tits tree of `PGL₂(K)`
  (Serre, *Trees*, Chapter II, §1); for other rings it need not be a tree.
-/

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/-- `GL₂(K)` acts on the homothety classes of full lattices, for any `R`-algebra field `K`. -/
instance instMulActionGLVertex : MulAction (GL (Fin 2) K) (Vertex R K) where
  smul := Vertex.act
  one_smul := Vertex.act_one
  mul_smul := Vertex.act_mul

theorem gl_smul_def (g : GL (Fin 2) K) (v : Vertex R K) : g • v = Vertex.act g v := rfl

@[simp] theorem gl_smul_mk (g : GL (Fin 2) K) (L : Submodule R (Fin 2 → K))
    (hL : Submodule.IsFullLattice K L) :
    g • Vertex.mk R K L hL = Vertex.mk R K (latticeMap g L) (IsFullLattice.map hL g) := rfl

variable (R K) in
/-- The permutation representation of `GL₂(K)` on vertices. -/
def vertPermHom : GL (Fin 2) K →* Equiv.Perm (Vertex R K) :=
    MulAction.toPermHom (GL (Fin 2) K) (Vertex R K)

@[simp] theorem vertPermHom_apply (g : GL (Fin 2) K) (x : Vertex R K) :
    vertPermHom R K g x = g • x := rfl

theorem scalar_eq_scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) c = scalarGL c := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, scalarGL_coe, Matrix.one_apply, Matrix.diagonal_apply]

theorem scalar_smul_vertex (c : Kˣ) (v : Vertex R K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c • v = v := by
  rw [scalar_eq_scalarGL]
  exact isFixedVertex_scalarGL c v

/-- Scalar matrices act trivially on vertices. -/
theorem scalar_mem_ker_vertPermHom (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ (vertPermHom R K).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  simp [scalar_smul_vertex]

/-- The action of `GL₂(K)` on vertices descends to `PGL₂(K)`. -/
instance instMulActionPGLVertex : MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL fun c v => scalar_smul_vertex c v

@[simp] theorem pgl_mk_smul (g : GL (Fin 2) K) (v : Vertex R K) :
    Matrix.ProjGenLinGroup.mk g • v = g • v := rfl

variable [IsFractionRing R K]

/-- When `K` is the fraction field of `R`, `GL₂(K)` preserves adjacency of `R`-submodules of `K²`.
-/
theorem adjacentLattice_latticeMap (g : GL (Fin 2) K) {L L' : Submodule R (Fin 2 → K)}
    (h : AdjacentLattice L L') : AdjacentLattice (latticeMap g L) (latticeMap g L') := by
  obtain ⟨ϖ, hϖ, h₁, h₂⟩ := h
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff g).2 h₂⟩
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  exact (latticeMap_lt_latticeMap_iff g).2 h₁

variable (R K) in
/-- For `K` the fraction field of `R`, two vertices are related when they have adjacent
representatives. -/
def VertRel (x y : Vertex R K) : Prop :=
  ∃ (L L' : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L)
      (hL' : Submodule.IsFullLattice K L'),
    Vertex.mk R K L hL = x ∧ Vertex.mk R K L' hL' = y ∧ AdjacentLattice L L'

variable (R K) in
/-- For `K` the fraction field of `R`, the graph on vertices whose edges join classes with adjacent
representative lattices. When `R` is moreover a discrete valuation ring, it is the Bruhat-Tits tree
of `PGL₂(K)` (Serre, *Trees*, Chapter II, §1). -/
def tree : SimpleGraph (Vertex R K) := SimpleGraph.fromRel (VertRel R K)

theorem tree_adj_iff (x y : Vertex R K) :
    (tree R K).Adj x y ↔ x ≠ y ∧ (VertRel R K x y ∨ VertRel R K y x) :=
  SimpleGraph.fromRel_adj _ _ _

theorem VertRel.gl_smul (g : GL (Fin 2) K) {x y : Vertex R K} (h : VertRel R K x y) :
    VertRel R K (g • x) (g • y) := by
  obtain ⟨L, L', hL, hL', rfl, rfl, hLL'⟩ := h
  exact ⟨latticeMap g L, latticeMap g L', IsFullLattice.map hL g, IsFullLattice.map hL' g, rfl,
      rfl, adjacentLattice_latticeMap g hLL'⟩

/-- `GL₂(K)` acts on the graph `tree R K` by graph automorphisms. -/
instance instGraphActionGLTree : GraphAction (GL (Fin 2) K) (tree R K) where
  smul_adj g {x y} h := by
    rw [tree_adj_iff] at h ⊢
    refine ⟨fun hxy => h.1 (MulAction.injective g hxy), ?_⟩
    exact h.2.imp (VertRel.gl_smul g) (VertRel.gl_smul g)

/-- `PGL₂(K)` acts on the graph `tree R K` by graph automorphisms. -/
instance instGraphActionPGLTree : GraphAction (Matrix.ProjGenLinGroup (Fin 2) K) (tree R K) where
  smul_adj q {x y} h := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g => ?_
    rw [pgl_mk_smul, pgl_mk_smul]
    exact GraphAction.smul_adj g h

end BruhatTits
end CerednikDrinfeld

end
