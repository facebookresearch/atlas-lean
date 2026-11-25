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

public import MathlibExt.Analysis.CStarAlgebra.BicommutantStrongClosure
public import MathlibExt.Analysis.CStarAlgebra.StrongCentralizer

/-!
# Actual full-H strong closure equals the original double commutant

The literal original source operators lie in their double centralizer,
which is strongly closed by fixed-operator vector equalizers. Conversely,
the proved finite-vector orbit construction places every original double
commutant operator in the strong closure. Their equality is required to
construct an exact von Neumann image carrier; no closure or bicommutant
certificate is supplied by a source theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Topology

namespace MathlibExt.Analysis.CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bicommutant theorem in strong topology.** Let `H` be a complete complex Hilbert space and `S` a
unital complex star subalgebra of the bounded operators on `H`. The strong operator closure of `S`
equals its bicommutant, where strong topology is uniform convergence on finite subsets of `H`. -/
theorem strongClosure_eq_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (Set.range fun a : S =>
      (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
        {s : Set H | Finite s} (a : H →L[ℂ] H) : H →Lₚₜ[ℂ] H)) =
    {q : H →Lₚₜ[ℂ] H |
      (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
        {s : Set H | Finite s}).symm q ∈
          Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))} := by
  let P := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {s : Set H | Finite s}
  change closure (Set.range fun a : S => P (a : H →L[ℂ] H)) =
    {q : H →Lₚₜ[ℂ] H | P.symm q ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))}
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (isClosed_strongCentralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    rintro q ⟨a, rfl⟩
    change P.symm (P (a : H →L[ℂ] H)) ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))
    rw [P.symm_apply_apply]
    exact Set.subset_centralizer_centralizer a.property
  · intro q hq
    change P.symm q ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) at hq
    have h := bicommutant_mem_strongClosure S (P.symm q) hq
    change P (P.symm q) ∈ closure (Set.range fun a : S => P (a : H →L[ℂ] H)) at h
    rw [P.apply_symm_apply] at h
    exact h

end

end MathlibExt.Analysis.CStarAlgebra
