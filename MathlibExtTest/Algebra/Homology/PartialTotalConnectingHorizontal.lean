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

public import MathlibExt.Algebra.Homology.PartialTotalConnectingHorizontal

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

example (m q : ℕ) :
    (B.partialTotalE₁ConnectingDifferential m q :
      (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
        (B.totalRow m).homology (m + q)) =
      B.partialTotalHorizontalRowHomology m q :=
  B.partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology m q

example (m q : ℕ) {Z : C}
    (f : (B.totalRow m).homology (m + q) ⟶ Z) :
    B.partialTotalE₁ConnectingDifferential m q ≫ f =
      B.partialTotalHorizontalRowHomology m q ≫ f :=
  B.partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology_assoc m q f

example :
    (B.partialTotalE₁ConnectingDifferential 0 0 :
      (B.totalRow 1).homology 1 ⟶ (B.totalRow 0).homology 0) =
      B.partialTotalHorizontalRowHomology 0 0 := by
  simpa using
    B.partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology 0 0

/-! ## Chosen total-degree characteristic -/

example (m q nPlus nZero : ℕ)
    (hPlus : (m + 1) + q = nPlus)
    (hZero : m + q = nZero) :
    let eNat := ComplexShape.embeddingDownNat
    let νPlus : ℤ := -((nPlus : ℕ) : ℤ)
    let νZero : ℤ := -((nZero : ℕ) : ℤ)
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let T := B.partialTotalStepCochainShortComplex m
    let hS : S.ShortExact :=
      B.partialTotalStepCochainShortExact (m + 1)
    let cAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
        hS.δ νPlus νZero (by
          have hPlusZ := congrArg (fun x : ℕ => (x : ℤ)) hPlus
          have hZeroZ := congrArg (fun x : ℕ => (x : ℤ)) hZero
          change -((nPlus : ℕ) : ℤ) + 1 = -((nZero : ℕ) : ℤ)
          rw [← hPlusZ, ← hZeroZ]
          omega) ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
        HomologicalComplex.homologyMap T.g νZero ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    let rAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift m)
            νPlus νZero (by
              have hPlusZ := congrArg (fun x : ℕ => (x : ℤ)) hPlus
              have hZeroZ := congrArg (fun x : ℕ => (x : ℤ)) hZero
              change 1 + -((nPlus : ℕ) : ℤ) = -((nZero : ℕ) : ℤ)
              rw [← hPlusZ, ← hZeroZ]
              omega) ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    cAt = rAt :=
  B.partialTotalE₁Connecting_eq_horizontalRowAt
    m q nPlus nZero hPlus hZero

example (m q : ℕ) :=
  B.partialTotalE₁Connecting_eq_horizontalRowAt
    m q (q + (m + 1)) (q + m) (by omega) (Nat.add_comm m q)

example (q : ℕ) :=
  B.partialTotalE₁Connecting_eq_horizontalRowAt
    0 q (q + 1) q (by omega) (Nat.zero_add q)

example (m : ℕ) :=
  B.partialTotalE₁Connecting_eq_horizontalRowAt
    m 0 (m + 1) m (by omega) (by omega)

example (m : ℕ) :=
  B.partialTotalE₁Connecting_eq_horizontalRowAt
    m 1 (m + 2) (m + 1) (by omega) (by omega)

end HomologicalComplex₂

end
