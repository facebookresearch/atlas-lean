/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59
import Mathlib.Algebra.Field.ZMod

open MathlibExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59Wanted

example (G : Type) [Group G] (P : Type) [Field P] [CharP P 2] [Infinite P]
    (hperiodic : ∀ g : G, IsOfFinOrder g) (hi : ∃ i : G, orderOf i = 2)
    (hconj : ∀ i j : G, orderOf i = 2 → orderOf j = 2 → IsConj i j)
    (hP : IsLocallyFiniteField P)
    (hcentralizer : ∀ i : G, orderOf i = 2 →
      Nonempty (Subgroup.centralizer {i} ≃*
        (Subgroup.zpowers i × Matrix.ProjectiveSpecialLinearGroup (Fin 2) P))) : False :=
  periodicGroupWithPSLInvolutionCentralizers_refuted
    ⟨G, inferInstance, hperiodic, hi, hconj, P, inferInstance, inferInstance, inferInstance,
      hP, hcentralizer⟩

example : IsLocallyFiniteField (ZMod 2) := fun _ ↦ Finite.of_injective _ Subtype.val_injective
