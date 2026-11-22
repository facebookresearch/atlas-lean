/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Magnetization

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Magnetization`

* `magnetization d β` lies in `[-1, 1]`.
* `positiveMagnetizationSet d` consists of nonnegative inverse temperatures, so `betaC d ≥ 0`
  (including the convention `sInf ∅ = 0`).
* `betaC d` is a lower bound of the positive-magnetization set when that set is nonempty.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Magnetization

open _root_.StatMech _root_.StatMech.Ising

-- The spontaneous magnetization is a number in `[-1, 1]`.
example (d : ℕ) (β : ℝ) : magnetization d β ∈ Set.Icc (-1) 1 :=
  ⟨neg_one_le_magnetization d β, magnetization_le_one d β⟩

-- The critical inverse temperature is nonnegative.
example (d : ℕ) : 0 ≤ betaC d :=
  Real.sInf_nonneg fun _ hβ => hβ.1

-- If the magnetization is positive at `β ≥ 0`, then `betaC d ≤ β`.
example (d : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hm : 0 < magnetization d β) : betaC d ≤ β :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hβ, hm⟩

-- With an empty positive-magnetization set, `betaC d = 0` (the `sInf ∅` convention).
example (d : ℕ) (h : positiveMagnetizationSet d = ∅) : betaC d = 0 := by
  rw [betaC, h, Real.sInf_empty]

end PhyslibExtTest.CondensedMatter.IsingModel.Magnetization
