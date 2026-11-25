/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeVertex
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open scoped Matrix
open LT.LatticeTree

universe u

/-- Consumer with the original binders: two full lattices give the same vertex iff they are
homothetic. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    {L L' : Submodule R (Fin 2 → K)} {hL : Submodule.IsFullLattice K L}
    {hL' : Submodule.IsFullLattice K L'} :
    Vertex.mk R K L hL = Vertex.mk R K L' hL' ↔ Homothetic L L' :=
  Vertex.mk_eq_mk_iff

/-- Higher-universe consumer: the stabilizer of the standard vertex. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    [IsFractionRing R K] (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.act g (stdVertex R K) = stdVertex R K ↔
      ∃ c : Kˣ, scalarGL c * g ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :=
  Vertex.act_stdVertex_eq_iff g

example : IsDiscreteValuationRing ℤ_[2] := inferInstance
example : IsFractionRing ℤ_[2] ℚ_[2] := inferInstance
example : Irreducible (2 : ℤ_[2]) := PadicInt.irreducible_p

example :
    Vertex.act (R := ℤ_[2]) (K := ℚ_[2])
        (diagSnd (unitOfNeZero (K := ℚ_[2]) (PadicInt.irreducible_p (p := 2)).ne_zero))
        (stdVertex ℤ_[2] ℚ_[2]) ≠
      stdVertex ℤ_[2] ℚ_[2] :=
  stdVertex_ne_act_diagSnd PadicInt.irreducible_p

/-- Boundary: over a field `R = K` there are no irreducibles, and every vertex is the standard
one up to `GL₂`; here the identity fixes the standard vertex. -/
example {K : Type u} [Field K] : Vertex.act 1 (stdVertex K K) = stdVertex K K :=
  Vertex.act_one _
