/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Finiteness
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite generation of noncommutative bimodule tensors

Finite left S generators of an S–R bimodule and finite left R generators
of a module give finite left S generators of their balanced tensor.
Both acting semirings may be noncommutative. Scalar balance moves an R
coefficient to the right action on the first factor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open MulOpposite

universe uR uS uE uM

namespace TensorProduct.Balanced

variable (R : Type uR) (S : Type uS) (E : Type uE) (M : Type uM)
  [Semiring R] [Semiring S] [AddCommGroup E] [AddCommGroup M]
  [Module S E] [Module Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E] [Module R M]

/-- Ordered pure pairs of spanning sets span the whole original bimodule tensor over S. -/
theorem span_pure_eq_top (s : Set E) (t : Set M)
    (hs : Submodule.span S s = ⊤) (ht : Submodule.span R t = ⊤) :
    letI := leftModule ℤ R S E M
    Submodule.span S ((fun p : E × M => mk ℤ R E M p.1 p.2) '' (s ×ˢ t)) = ⊤ := by
  let := leftModule ℤ R S E M
  let L : Submodule S (Balanced ℤ R E M) :=
    Submodule.span S ((fun p : E × M => mk ℤ R E M p.1 p.2) '' (s ×ˢ t))
  have hpair : ∀ n ∈ Submodule.span R t, ∀ e : E, mk ℤ R E M e n ∈ L := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem n hn =>
      intro e
      have he : e ∈ Submodule.span S s := by rw [hs]; trivial
      induction he using Submodule.span_induction with
      | mem e he => exact Submodule.subset_span ⟨(e, n), ⟨he, hn⟩, rfl⟩
      | zero =>
        change (mk ℤ R E M 0) n ∈ L
        rw [map_zero, LinearMap.zero_apply]
        exact L.zero_mem
      | add e e' he he' ihe ihe' =>
        change (mk ℤ R E M (e + e')) n ∈ L
        rw [map_add, LinearMap.add_apply]
        exact L.add_mem ihe ihe'
      | smul a e he ihe =>
        rw [← leftModule_smul_mk ℤ R S E M]
        exact L.smul_mem a ihe
    | zero =>
      intro e
      rw [map_zero]
      exact L.zero_mem
    | add n n' hn hn' ihn ihn' =>
      intro e
      rw [map_add]
      exact L.add_mem (ihn e) (ihn' e)
    | smul r n hn ihn =>
      intro e
      rw [← balance ℤ R E M r e n]
      exact ihn (op r • e)
  apply top_unique
  intro x hx
  obtain ⟨u, hu⟩ := exists_finset ℤ R E M x
  rw [hu]
  apply Submodule.sum_mem L
  intro p hp
  apply hpair p.2
  rw [ht]
  trivial

/-- A finite left S bimodule tensored with a finite left R module is finite over S. -/
theorem finite_left [Module.Finite S E] [Module.Finite R M] :
    letI := leftModule ℤ R S E M
    Module.Finite S (Balanced ℤ R E M) := by
  let := leftModule ℤ R S E M
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := S) (M := E))
  obtain ⟨t, ht, hspan'⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := M))
  apply Module.Finite.of_fg_top
  exact Submodule.fg_def.mpr
    ⟨_, (hs.prod ht).image (fun p : E × M => mk ℤ R E M p.1 p.2),
      span_pure_eq_top R S E M s t hspan hspan'⟩

end TensorProduct.Balanced
