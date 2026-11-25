/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeBaseChange

@[expose] public section

open LT.LatticeTree

universe u

/-- Consumer with the original binders: the orbital ball of depth `0` is the fixed-vertex set. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (c : Kˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) :
    orbitalBall (R := R) c 0 γ = fixedVertexSet γ :=
  orbitalBall_zero c γ

/-- Higher-universe consumer: vertices within depth `0` coincide, and depth is symmetric. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K] (c : Kˣ)
    (n : ℕ) (v w : Vertex R K) :
    (Vertex.IsWithin c 0 v w ↔ v = w) ∧ (Vertex.IsWithin c n v w ↔ Vertex.IsWithin c n w v) :=
  ⟨Vertex.isWithin_zero_iff c v w, Vertex.isWithin_comm c n v w⟩

/-- Base change along the identity is the identity on vertices, and base change is
`GL₂`-equivariant. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.baseChange (IntegralHom.refl R K) v = v ∧
      Vertex.baseChange (IntegralHom.refl R K) (Vertex.act g v) =
        Vertex.act ((IntegralHom.refl R K).mapGL g) (Vertex.baseChange (IntegralHom.refl R K) v) :=
  ⟨Vertex.baseChange_refl v, Vertex.baseChange_act _ g v⟩

/-- Boundary: for `c = 1` every vertex lies in every orbital ball of the identity. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] (n : ℕ) :
    orbitalBall (R := R) (1 : Kˣ) n 1 = Set.univ :=
  orbitalBall_one (fun L => by rw [scalarGL_one, latticeMap_one]) n
