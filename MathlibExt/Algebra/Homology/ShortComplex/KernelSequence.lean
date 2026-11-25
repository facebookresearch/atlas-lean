/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.ShortComplex.ShortExactSequences

/-!
# Functorial kernel sequences

This module is the epi-map dual of the horizontal half of
`MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence`: for a short
exact sequence `S` of homological complexes over an abelian category, the
horizontal criterion `quasiIso_g_iff` says `S.g` is a quasi-isomorphism iff
`S.X₁` is acyclic, and `HomologicalComplex.quasiIso_iff_acyclic_kernel` says
an epimorphism `g` of complexes is a quasi-isomorphism iff its kernel is
acyclic. The latter is derived from the former applied to
`ShortComplex.kernelSequence`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}

/-- Horizontal criterion for a short exact sequence of homological complexes:
`S.g` is a quasi-isomorphism iff `S.X₁` is acyclic. Uses `homology_exact₂`
directly for monomorphy and `homology_exact₃` directly for epimorphy, with a
split on existence of a successor. -/
theorem quasiIso_g_iff (hS : S.ShortExact) :
    _root_.QuasiIso S.g ↔ S.X₁.Acyclic := by
  constructor
  · intro h
    exact hS.acyclic_X₁ h
  · intro hAcyc
    rw [_root_.quasiIso_iff]
    intro i
    rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
    have hMono : Mono (HomologicalComplex.homologyMap S.g i) := by
      have hZero : IsZero (S.X₁.homology i) := (hAcyc i).isZero_homology
      have hfZero : HomologicalComplex.homologyMap S.f i = 0 :=
        IsZero.eq_zero_of_src hZero _
      exact (hS.homology_exact₂ i).mono_g hfZero
    have hEpi : Epi (HomologicalComplex.homologyMap S.g i) := by
      by_cases hi : ∃ j, c.Rel i j
      · obtain ⟨j, hij⟩ := hi
        have hZeroJ : IsZero (S.X₁.homology j) := (hAcyc j).isZero_homology
        have hDeltaZero : hS.δ i j hij = 0 := IsZero.eq_zero_of_tgt hZeroJ _
        exact (hS.homology_exact₃ i j hij).epi_f hDeltaZero
      · have : Epi S.g := hS.epi_g
        have : Epi (S.g.f i) := inferInstance
        have hj : ∀ k, ¬ c.Rel i k := by
          intro k hk
          exact hi ⟨k, hk⟩
        exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g i hj
    have : IsIso (HomologicalComplex.homologyMap S.g i) := by
      have : Mono (HomologicalComplex.homologyMap S.g i) := hMono
      have : Epi (HomologicalComplex.homologyMap S.g i) := hEpi
      exact isIso_of_mono_of_epi _
    infer_instance

end CategoryTheory.ShortComplex.ShortExact

open CategoryTheory

namespace HomologicalComplex

section KernelCriterion

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
variable {K L : HomologicalComplex C c} (g : K ⟶ L) [Epi g]

/-- Horizontal criterion for an epimorphism of homological complexes: `g` is a
quasi-isomorphism iff its kernel is acyclic. Derived from
`ShortExact.quasiIso_g_iff` applied to `ShortComplex.kernelSequence`. -/
theorem quasiIso_iff_acyclic_kernel :
    QuasiIso g ↔ (Limits.kernel g).Acyclic := by
  have hShortExact : (ShortComplex.kernelSequence g).ShortExact :=
    ShortComplex.kernelSequence_shortExact g
  have hIff := hShortExact.quasiIso_g_iff
  have hG : (ShortComplex.kernelSequence g).g = g := rfl
  have hX₁ : (ShortComplex.kernelSequence g).X₁ = Limits.kernel g := rfl
  rw [hG] at hIff
  rw [hX₁] at hIff
  exact hIff

end KernelCriterion

end HomologicalComplex
