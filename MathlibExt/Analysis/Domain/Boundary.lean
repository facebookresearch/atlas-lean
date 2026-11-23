/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 501, Analysis 506

open Metric Set

/-!
# C2 boundary; Lipschitz boundary

## References

* It is the C^2 analogue of https://en.wikipedia.org/wiki/Lipschitz_domain (for `HasC2Boundary`)
* https://en.wikipedia.org/wiki/Lipschitz_domain (for `HasLipschitzBoundary`)
-/

namespace MetaMathlibExt

-- Analysis 501: C2 boundary

/-- An open subset Ω⊂ ℝ² has C² boundary if for every x∈∂Ω there exists an r>0, a C² function φ: ℝ→
ℝ, and an isometry A, with Ax=(0,0), such that letting Ay=(u,v) for y∈ B(x,r) we have ∂Ω∩ B(x,r)={y∈
B(x,r): v=φ(u)} and Ω∩ B(x,r)={y∈ B(x,r): v<φ(u)}.
-/
def HasC2Boundary (Ω : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsOpen Ω ∧
  ∀ x ∈ frontier Ω, ∃ (r : ℝ) (_ : r > 0), ∃ (φ : ℝ → ℝ), ContDiff ℝ 2 φ ∧
    ∃ (A : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)), A x = 0 ∧
      (frontier Ω ∩ ball x r = { y ∈ ball x r | A y ⟨1, by simp⟩ = φ (A y ⟨0, by simp⟩) }) ∧
      (Ω ∩ ball x r = { y ∈ ball x r | A y ⟨1, by simp⟩ < φ (A y ⟨0, by simp⟩) })

-- Analysis 506: Lipschitz boundary

/-- An open subset Ω⊂ℝ² has Lipschitz boundary if for every x∈∂Ω there exists an r>0, a Lipschitz
function φ:ℝ→ℝ, and an isometry A, with Ax=(0,0), such that letting Ay=(u,v) we have ∂Ω∩ B(x,r)={y∈
B(x,r): v=φ(u)} and Ω∩ B(x,r)={y∈ B(x,r): v<φ(u)}.
-/
def HasLipschitzBoundary (Ω : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsOpen Ω ∧
  ∀ x ∈ frontier Ω, ∃ (r : ℝ) (_ : r > 0), ∃ (φ : ℝ → ℝ) (L : NNReal),
    LipschitzOnWith L φ Set.univ ∧
    ∃ (A : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)), A x = 0 ∧
      (frontier Ω ∩ ball x r = { y ∈ ball x r | A y ⟨1, by simp⟩ = φ (A y ⟨0, by simp⟩) }) ∧
      (Ω ∩ ball x r = { y ∈ ball x r | A y ⟨1, by simp⟩ < φ (A y ⟨0, by simp⟩) })

end MetaMathlibExt

end
