/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow.lean`
and
`P2M/Sol/S_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open Polynomial Module

namespace LinearMap

private theorem trace_pow_restrict_maxGenEigenspace {E : Type*} [Field E] {W : Type*}
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] (S : Module.End E W) (μ : E) (n : ℕ) :
    LinearMap.trace E _ ((S ^ n).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ)) =
      μ ^ n * (finrank E (S.maxGenEigenspace μ) : E) := by
  have hS : Set.MapsTo S ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S) μ
  set Sμ : Module.End E (S.maxGenEigenspace μ) := S.restrict hS with hSμ
  have hnil := S.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hpow : ∀ k : ℕ, Sμ ^ k = (S ^ k).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right k) μ) := by
    intro k
    rw [hSμ]
    exact Module.End.pow_restrict k (fun x hx => hS hx)
  rw [← hpow n]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, LinearMap.trace_one]
  | succ k ih =>
    have hcomm : Commute (Sμ ^ k) Sμ := (Commute.refl Sμ).pow_left k
    have hk : Sμ ^ (k + 1) = (Sμ ^ k) ∘ₗ Sμ := by rw [pow_succ]; rfl
    rw [hk, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hcomm hnil, ih, ← mul_assoc,
      ← pow_succ']

private theorem sum_roots_pow_eq_trace_pow {E : Type*} [Field E] {W : Type*}
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] [IsAlgClosed E]
    (S : Module.End E W) (n : ℕ) :
    ((S.charpoly).roots.map (fun z => z ^ n)).sum = LinearMap.trace E W (S ^ n) := by
  classical
  have hind := S.independent_maxGenEigenspace
  have htop := S.iSup_maxGenEigenspace_eq_top
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have h_fin : {μ : E | S.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hf : ∀ μ : E, Set.MapsTo (S ^ n) ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    fun μ => S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hf]
  simp_rw [trace_pow_restrict_maxGenEigenspace]
  rw [Finset.sum_multiset_map_count]
  have hset : S.charpoly.roots.toFinset = h_fin.toFinset := by
    ext μ
    rw [Multiset.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      mem_roots (S.charpoly_monic).ne_zero, ne_eq, ← Submodule.finrank_eq_zero,
      LinearMap.finrank_maxGenEigenspace_eq, ← ne_eq, ← Nat.pos_iff_ne_zero, rootMultiplicity_pos']
    exact ⟨fun h => ⟨(S.charpoly_monic).ne_zero, h⟩, fun h => h.2⟩
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, nsmul_eq_mul, mul_comm]

/-- Newton identity form: the sum of the `n`-th powers of the roots of the
characteristic polynomial of `T` (counted with multiplicity, in an algebraic
closure) equals the trace of `T ^ n`. -/
public theorem sum_roots_charpoly_map_pow_eq_trace_pow {L : Type*} [Field L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E]
    [IsAlgClosed E] (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n)) := by
  rw [← LinearMap.charpoly_baseChange, sum_roots_pow_eq_trace_pow, ← LinearMap.baseChange_pow,
    LinearMap.trace_baseChange]

end LinearMap
