/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MaschkeDecomposition
import Mathlib.Analysis.Complex.Polynomial.Basic

open Representation

open MathlibExt.GroupTheory.MaschkeDecomposition

namespace MathlibExtTest.GroupTheory.MaschkeDecomposition

/-- The direct sum of two copies of the trivial representation of
`Multiplicative (ZMod 2)` on `ℂ` decomposes into exactly two irreducible pieces.
Counting the pieces uses that every irreducible of an abelian group is
one-dimensional, so the piece count equals the dimension. -/
theorem maschke_two_trivial :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (T : ι → Subrepresentation
        (Representation.directSum (fun _ : Fin 2 =>
          Representation.trivial ℂ (Multiplicative (ZMod 2)) ℂ))),
      (∀ i, (T i).toRepresentation.IsIrreducible) ∧ Fintype.card ι = 2 := by
  classical
  obtain ⟨ι, hι, hdec, T, hirr, ⟨e⟩⟩ := maschke_decomposition
    (Representation.directSum (fun _ : Fin 2 =>
      Representation.trivial ℂ (Multiplicative (ZMod 2)) ℂ))
  haveI hι' : Fintype ι := hι
  haveI hdec' : DecidableEq ι := hdec
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) := ⟨⟨mul_comm⟩⟩
  refine ⟨ι, hι, hdec, T, hirr, ?_⟩
  have hone : ∀ i, Module.finrank ℂ ↥((T i).toSubmodule) = 1 := by
    intro i
    haveI : ((T i).toRepresentation).IsIrreducible := hirr i
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (T i).toRepresentation
  have hsum : ∑ i : ι, Module.finrank ℂ ↥((T i).toSubmodule) = 2 := by
    have h1 : Module.finrank ℂ (DirectSum ι (fun i => ↥((T i).toSubmodule)))
        = ∑ i : ι, Module.finrank ℂ ↥((T i).toSubmodule) := Module.finrank_directSum _ _
    have h2 : Module.finrank ℂ (DirectSum (Fin 2) (fun _ : Fin 2 => ℂ)) = 2 := by
      rw [Module.finrank_directSum]
      simp
    have h3 : Module.finrank ℂ (DirectSum (Fin 2) (fun _ : Fin 2 => ℂ)) =
        Module.finrank ℂ (DirectSum ι (fun i => ↥((T i).toSubmodule))) :=
      LinearEquiv.finrank_eq e.toLinearEquiv
    rw [← h1, ← h3]
    exact h2
  simp only [hone] at hsum
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [Subsingleton.elim hι' hι] at hsum
  exact hsum

/-- The trivial representation on `ℂ` decomposes into exactly one piece. -/
theorem maschke_trivial_one :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (T : ι → Subrepresentation (Representation.trivial ℂ (Multiplicative (ZMod 2)) ℂ)),
      (∀ i, (T i).toRepresentation.IsIrreducible) ∧ Fintype.card ι = 1 := by
  classical
  obtain ⟨ι, hι, hdec, T, hirr, ⟨e⟩⟩ := maschke_decomposition
    (Representation.trivial ℂ (Multiplicative (ZMod 2)) ℂ)
  haveI hι' : Fintype ι := hι
  haveI hdec' : DecidableEq ι := hdec
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) := ⟨⟨mul_comm⟩⟩
  refine ⟨ι, hι, hdec, T, hirr, ?_⟩
  have hone : ∀ i, Module.finrank ℂ ↥((T i).toSubmodule) = 1 := by
    intro i
    haveI : ((T i).toRepresentation).IsIrreducible := hirr i
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (T i).toRepresentation
  have hsum : ∑ i : ι, Module.finrank ℂ ↥((T i).toSubmodule) = 1 := by
    have h1 : Module.finrank ℂ (DirectSum ι (fun i => ↥((T i).toSubmodule)))
        = ∑ i : ι, Module.finrank ℂ ↥((T i).toSubmodule) := Module.finrank_directSum _ _
    have h2 : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
    have h3 : Module.finrank ℂ ℂ =
        Module.finrank ℂ (DirectSum ι (fun i => ↥((T i).toSubmodule))) :=
      LinearEquiv.finrank_eq e.toLinearEquiv
    rw [← h1, ← h3]
    exact h2
  simp only [hone] at hsum
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [Subsingleton.elim hι' hι] at hsum
  exact hsum

end MathlibExtTest.GroupTheory.MaschkeDecomposition
