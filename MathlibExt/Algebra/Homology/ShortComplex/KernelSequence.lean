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
# Acyclic kernels and quasi-isomorphisms

For a short exact sequence 0 → A → B → D → 0 of complexes of any shape
in an abelian category, the map B → D is a quasi-isomorphism exactly
when A is acyclic. In particular, an epimorphism g:K → L of complexes
is a quasi-isomorphism if and only if its kernel complex is acyclic.
These criteria apply to arbitrary complex shapes, including those with
boundary degrees.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}

/-- Let C be abelian and 0 → A → B —g→ D → 0 a short exact sequence
of complexes of any shape c. The map g is a quasi-isomorphism if
and only if A is acyclic in every degree. -/
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

/-- For an epimorphism g:K → L of complexes of any shape c in an abelian
category, g is a quasi-isomorphism if and only if the kernel complex
Ker(g) is acyclic in every degree. -/
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
