/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Carrier structures for concrete von Neumann algebras

Mathlib bundles a concrete von Neumann algebra as a star subalgebra but does
not expose the inherited algebraic and normed structures on its element type.
This file transports those canonical structures and supplies the full
operator algebra as the greatest concrete von Neumann algebra.
-/

@[expose] public section

namespace MathlibExt.Analysis.VonNeumannAlgebra

noncomputable section

noncomputable instance instSMulMemClass
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    SMulMemClass (VonNeumannAlgebra E) ℂ (E →L[ℂ] E) where
  smul_mem {A} c _ hx := A.toStarSubalgebra.smul_mem hx c

noncomputable instance instCarrierIsClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : VonNeumannAlgebra E) :
    IsClosed (A : Set (E →L[ℂ] E)) := by
  rw [← A.centralizer_centralizer]
  exact Set.isClosed_centralizer _

/-- Let `H` be a complete complex inner-product space. Concrete von Neumann algebras are star
subalgebras of `H →L[ℂ] H` equal to their double commutants; all operator norms and weak
operator topologies are the canonical ones.

For every concrete von Neumann algebra `M` on `H`, its carrier is a complex C*-algebra with the
inherited addition, multiplication, scalar action, involution and operator norm. -/
noncomputable instance instCarrierCStarAlgebra
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : VonNeumannAlgebra E) : CStarAlgebra A :=
  StarSubalgebra.cstarAlgebra A

/-- Let `H` be a complete complex inner-product space. Concrete von Neumann algebras are star
subalgebras of `H →L[ℂ] H` equal to their double commutants; all operator norms and weak
operator topologies are the canonical ones.

The full operator algebra is the greatest concrete von Neumann algebra. -/
noncomputable instance instOrderTop
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : OrderTop (VonNeumannAlgebra E) where
  top :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' := by
        change (Set.univ : Set (E →L[ℂ] E)).centralizer.centralizer = Set.univ
        exact Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer }
  le_top A := by
    intro x hx
    change x ∈ (⊤ : StarSubalgebra ℂ (E →L[ℂ] E))
    simp

end

end MathlibExt.Analysis.VonNeumannAlgebra
