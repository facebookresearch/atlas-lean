/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean`
and
`P2M/Sol/S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean`
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

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

namespace Algebra

/-- A finite extension `F/E`, with `F` of prime characteristic `p`, is
separable when `F` has degree `p` over its subfield `F^p` of `p`-th powers
(that is, `[F : F^p] = p`) and `E` contains an element whose image in `F`
does not lie in `F^p`.

The Kähler differentials of `F/E` vanish on `F^p` and on the image of `E`,
hence on the intermediate field they generate. That intermediate field is
either `F^p` or all of `F` by simplicity of the lattice in prime degree;
the witness rules out the first case, so every differential vanishes and
`F/E` is formally unramified, hence separable. -/
public theorem IsSeparable.of_finrank_fieldRange_frobenius_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hdeg : Module.finrank (frobenius F p).fieldRange F = p)
    (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) :
    Algebra.IsSeparable E F := by
  set S : Subfield F := (frobenius F p).fieldRange with hS
  haveI : IsSimpleOrder (IntermediateField S F) :=
    IntermediateField.isSimpleOrder_of_finrank_prime S F (by rw [hdeg]; exact Fact.out)
  set D := KaehlerDifferential.D E F with hD
  have hDS : ∀ s : F, s ∈ S → D s = 0 := by
    intro s hs
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp hs
    rw [frobenius_def, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hDy : D (algebraMap E F y) = 0 := D.map_algebraMap y
  let Z : IntermediateField S F :=
    { carrier := {z | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero D
      algebraMap_mem' := fun s => hDS _ s.2
      inv_mem' := by
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        rw [D.leibniz_inv, hz, smul_zero] }
  have hyZ : IntermediateField.adjoin S {algebraMap E F y} ≤ Z :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hDy)
  have hZ : Z = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin S {algebraMap E F y})
      with h | h
    · exfalso
      apply hy
      have hmem : algebraMap E F y ∈ (⊥ : IntermediateField S F) :=
        h ▸ IntermediateField.mem_adjoin_simple_self S (algebraMap E F y)
      obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp hmem
      rw [← hs]
      exact s.2
    · rw [h] at hyZ
      exact top_le_iff.mp hyZ
  have hD0 : ∀ z : F, D z = 0 := fun z => by
    have hz : z ∈ Z := hZ ▸ IntermediateField.mem_top
    exact hz
  haveI : Subsingleton (KaehlerDifferential E F) := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    have hω : ω ∈ Submodule.span F (Set.range D) := by
      rw [hD, KaehlerDifferential.span_range_derivation]
      trivial
    have hle : Submodule.span F (Set.range D) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      exact (Submodule.mem_bot F).mpr (hD0 z)
    exact (Submodule.mem_bot F).mp (hle hω)
  haveI : Algebra.FormallyUnramified E F := ⟨inferInstance⟩
  exact Algebra.FormallyUnramified.isSeparable E F

end Algebra
