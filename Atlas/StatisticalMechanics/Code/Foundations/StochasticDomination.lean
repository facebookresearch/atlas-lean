/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Inequalities.IncreasingEvent

open MeasureTheory

namespace StatMech

variable {E : Type*}



def StochasticallyDominated (μ ν : Measure (ConfigSpace E)) : Prop :=
  ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A → μ.real A ≤ ν.real A

@[inherit_doc]
scoped infix:50 " ≼ " => StochasticallyDominated


@[refl] theorem StochasticallyDominated.refl (μ : Measure (ConfigSpace E)) : μ ≼ μ :=
  fun _ _ _ => le_refl _


theorem StochasticallyDominated.trans {μ ν ρ : Measure (ConfigSpace E)}
    (h₁ : μ ≼ ν) (h₂ : ν ≼ ρ) : μ ≼ ρ :=
  fun A hA hAinc => (h₁ A hA hAinc).trans (h₂ A hA hAinc)

end StatMech
