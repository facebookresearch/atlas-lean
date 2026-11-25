/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem.lean`
and
`P2M/Sol/S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem.lean`
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

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

universe u

namespace Ideal

/-- If every prime ideal misses some element satisfying `P`, then finitely
many elements satisfying `P` already span the unit ideal.

The witnesses are indexed by a finite type in the same universe as the ring,
namely a finite subset of the set of all elements satisfying `P`. -/
public theorem exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
    {B : Type u} [CommRing B] (P : B → Prop)
    (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → B),
      Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) := by
  classical
  have htop : Ideal.span {f : B | P f} = ⊤ := by
    by_contra h
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf𝔪, hPf⟩ := hloc 𝔪 h𝔪.isPrime
    exact hf𝔪 (hle (Ideal.subset_span hPf))
  have h1 : (1 : B) ∈ Ideal.span {f : B | P f} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨↥T, inferInstance, fun t => t.1, ?_, fun t => hTsub t.2⟩
  rw [Ideal.eq_top_iff_one]
  have hrange : Set.range (fun t : ↥T => (t.1 : B)) = (T : Set B) := by
    ext b; simp
  rw [hrange]
  exact h1T

end Ideal
