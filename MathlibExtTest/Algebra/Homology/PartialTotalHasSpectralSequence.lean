/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalFirstPage
public import MathlibExt.Algebra.Homology.PartialTotalHasSpectralSequence

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq pq')
    (n : ℤ) (hn : n = (core).deg pq + 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₀_le r r' pq hrr' hr)))) :=
  B.partialTotalSpectralObject_isZero_i₀_le r r' pq hpq n hn hrr' hr

example (q : ℕ) :
    IsZero ((B.partialTotalSpectralObject.H ((core).deg (0, q) + 1)).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₀_le 1 2 (0, q)
          (hrr' := by omega) (hr := by omega))))) := by
  apply B.partialTotalSpectralObject_isZero_i₀_le 1 2 (0, q)
    (hrr' := by omega) (hr := by omega)
  · intro pq' hpq
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    omega
  · rfl

example (r r' : ℤ) (pq : ℕ × ℕ)
    (hpq : ∀ pq' : ℕ × ℕ,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq' pq)
    (n : ℤ) (hn : n = (core).deg pq - 1)
    (hrr' : r + 1 = r') (hr : 1 ≤ r) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₃_le r r' pq hrr' hr)))) :=
  B.partialTotalSpectralObject_isZero_i₃_le r r' pq hpq n hn hrr' hr

example :
    IsZero ((B.partialTotalSpectralObject.H ((core).deg (0, 0) - 1)).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE ((core).i₃_le 2 3 (0, 0)
          (hrr' := by omega) (hr := by omega))))) := by
  apply B.partialTotalSpectralObject_isZero_i₃_le 2 3 (0, 0)
    (hrr' := by omega) (hr := by omega)
  · intro pq' hpq
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    omega
  · rfl

example : B.partialTotalSpectralObject.HasSpectralSequence core :=
  inferInstance

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (0, q) ≅
      (B.totalRow 0).homology (0 + q) :=
  B.partialTotalSpectralSequenceFirstPageRowIso 0 q

example (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X
        (m + 1, q) ≅
      (B.totalRow (m + 1)).homology (m + 1 + q) :=
  B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q

end HomologicalComplex₂

end
