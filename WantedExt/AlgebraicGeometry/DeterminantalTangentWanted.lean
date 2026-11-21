/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DeterminantalTangent

/-!
# Determinantal tangent and normal-dimension requests

At a matrix of rank exactly `r`, the first-order rank equations say that
the tangent matrix sends `ker A` into `im A`. This identifies the normal
directions and gives the expected tangent dimension over any field.

References:
* Bruns–Vetter, *Determinantal Rings*, Chapter 2,
  https://doi.org/10.1007/BFb0080378.
* Covered minor-polynomial identities: TauCetiProject/TauCeti at
  62bbc0596dc3539d488232e4e924a338548ea0a9,
  `TauCeti/RingTheory/MvPolynomial/DeterminantalIdeal.lean`.
* Covered algebraic rank operations: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/LinearAlgebra/Matrix/DeterminantalRank.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeterminantalTangentWanted

open MathlibExt.AlgebraicGeometry.DeterminantalTangent

variable {k : Type*} [Field k] {m n r : ℕ}

/-- The explicit kernel-to-image condition for first-order rank preservation. -/
theorem_wanted mem_tangent_iff (A B : Matrix (Fin m) (Fin n) k)
    (hA : Matrix.rank A = r) (hrm : r < m) (hrn : r < n) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r A ↔
      ∀ v : Fin n → k, (Matrix.toLin' A) v = 0 →
        (Matrix.toLin' B) v ∈ LinearMap.range (Matrix.toLin' A)

/-- The rank-exactly-`r` stratum has the expected tangent dimension. -/
theorem_wanted finrank_tangent (A : Matrix (Fin m) (Fin n) k)
    (hA : Matrix.rank A = r) (hrm : r < m) (hrn : r < n) :
    Module.finrank k (tangent r A) = r * (m + n - r)

end WantedExt.AlgebraicGeometry.DeterminantalTangentWanted
