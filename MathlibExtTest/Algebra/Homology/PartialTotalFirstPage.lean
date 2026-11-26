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

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (p, q))))) ≅
      B.partialTotalStepE₁Homology p q :=
  B.partialTotalSpectralObjectHStepIso p q

section Page

variable [B.partialTotalSpectralObject.HasSpectralSequence core]

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (0, q) ≅
      (B.totalRow 0).homology (0 + q) :=
  B.partialTotalSpectralSequenceFirstPageRowIso 0 q

example (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X
        (m + 1, q) ≅
      (B.totalRow (m + 1)).homology (m + 1 + q) :=
  B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q

example (p q n : ℕ) (h : p + q = n) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology n :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt p q n h

example (p q n : ℕ) (h : p + q = n) :
    B.partialTotalSpectralSequenceFirstPageRowIsoAt p q n h =
      (B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core (p, q)
        ((core).i₁ (p, q)) ((core).i₂ (p, q)) rfl rfl
        ((core).deg (p, q)) rfl ≪≫
      B.partialTotalSpectralObjectHStepIso p q ≪≫
      B.partialTotalStepE₁HomologyIsoAt p q n h) := by
  rfl

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology (p + q) :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt p q (p + q) rfl

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology (q + p) :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt
    p q (q + p) (Nat.add_comm p q)

example (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X
        (m + 1, q) ≅
      (B.totalRow (m + 1)).homology (q + (m + 1)) :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt
    (m + 1) q (q + (m + 1)) (Nat.add_comm (m + 1) q)

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (0, q) ≅
      (B.totalRow 0).homology q :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt
    0 q q (Nat.zero_add q)

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, 0) ≅
      (B.totalRow p).homology p :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt
    p 0 p (Nat.add_zero p)

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, 1) ≅
      (B.totalRow p).homology (p + 1) :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt p 1 (p + 1) rfl

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (0, 0) ≅
      (B.totalRow 0).homology 0 :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt 0 0 0 rfl

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (0, 1) ≅
      (B.totalRow 0).homology 1 :=
  B.partialTotalSpectralSequenceFirstPageRowIsoAt 0 1 1 rfl

end Page

local notation "B₀" =>
  (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

section Zero

example
    (hSS : CategoryTheory.Abelian.SpectralObject.HasSpectralSequence
      (HomologicalComplex₂.partialTotalSpectralObject B₀) core)
    (p q n : ℕ) (h : p + q = n) := by
  letI := hSS
  exact HomologicalComplex₂.partialTotalSpectralSequenceFirstPageRowIsoAt
    (B := B₀) p q n h

end Zero

end HomologicalComplex₂

end
