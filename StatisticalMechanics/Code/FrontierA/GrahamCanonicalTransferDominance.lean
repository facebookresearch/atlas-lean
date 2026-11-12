/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferComponentCut









open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalTransferStrictlyDominates
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b : ↑m -> Fin 4) : Prop :=
  CanonicalTransferWorks ends m k zero b a ∧
    ¬ CanonicalTransferWorks ends m k zero a b




theorem mem_canonicalCoverageExclusive_swap_of_strictDominance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hdom : CanonicalTransferStrictlyDominates
      ends m k zero a.1.1 b.1.1) :
    b ∈ canonicalCoverageExclusive ends m j k l zero p b a := by
  classical
  rw [canonicalCoverageExclusive, Finset.mem_sdiff]
  constructor
  · rw [mem_canonicalMaskOrbitCoverage_iff]
    exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p b,
      canonicalTransferWorks_self hloop hjk hkl hk0 b⟩
  · intro hb
    exact hdom.2 ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p a b).mp hb).2



theorem mem_canonicalMaskOrbitCoverage_inter_of_strictDominance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hdom : CanonicalTransferStrictlyDominates
      ends m k zero a.1.1 b.1.1) :
    a ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
      a ∈ canonicalMaskOrbitCoverage ends m j k l zero p b := by
  constructor
  · rw [mem_canonicalMaskOrbitCoverage_iff]
    exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p a,
      canonicalTransferWorks_self hloop hjk hkl hk0 a⟩
  · rw [mem_canonicalMaskOrbitCoverage_iff]
    exact ⟨canonicalMaskTransferOrbit_symm ends m j k l zero p hab,
      hdom.1⟩

end StatMech.GrahamGHS.FourColor
