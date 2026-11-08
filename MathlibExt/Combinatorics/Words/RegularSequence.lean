/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import MathlibExt.Combinatorics.Words.Automatic
import Mathlib.RingTheory.Finiteness.Basic

/-! # `k`-regular sequences

Allouche and Shallit's `k`-regular integer sequences: the `ℤ`-span of the `k`-kernel
(`MetaMathlibExt.kKernel`) is finitely generated.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.4.1, Lemma 28 (`k`-regular sequences of Allouche and Shallit)
and Definition 1 (`k`-kernel).
-/

namespace MetaMathlibExt

@[expose] public section

/-- A `k`-regular integer sequence in the sense of Allouche and Shallit: the base satisfies
`k ≥ 2` and the `ℤ`-module spanned by its `k`-kernel `kKernel k f` is finitely generated.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28 (`k`-regular sequences of
Allouche and Shallit) and Definition 1 (`k`-kernel). -/
def IsKRegularSequence (k : ℕ) (f : ℕ → ℤ) : Prop :=
  2 ≤ k ∧ (Submodule.span ℤ (kKernel k f)).FG

/-- Constant sequences are `k`-regular for every base `k ≥ 2`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28. -/
theorem isKRegularSequence_const {k : ℕ} (hk : 2 ≤ k) (c : ℤ) :
    IsKRegularSequence k (fun _ => c) := by
  refine ⟨hk, ?_⟩
  apply Submodule.fg_span
  apply Set.Finite.subset (Set.finite_singleton (fun _ : ℕ => c))
  rintro g ⟨i, j, -, rfl⟩
  rfl

/-- A `k`-regular sequence has base `k ≥ 2`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28. -/
theorem IsKRegularSequence.two_le {k : ℕ} {f : ℕ → ℤ} (h : IsKRegularSequence k f) : 2 ≤ k :=
  h.1

end

end MetaMathlibExt
