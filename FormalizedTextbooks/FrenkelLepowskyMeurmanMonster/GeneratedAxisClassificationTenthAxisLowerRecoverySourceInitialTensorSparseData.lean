/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceInitialSparseFormula

/-! Ungated exact initial Fifth tensor data: 64 paired atoms, with 128 signed coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A source atom retains its original column and original position in that column. -/
abbrev GeneratedTenthSourceInitialTensorSparseIndex := Fin 8 × Fin 8

/-- The original low spin label, without relabeling or choosing an inverse. -/
def generatedTenthSourceInitialTensorSparseLow
    (p : GeneratedTenthSourceInitialTensorSparseIndex) : Fin 4096 :=
  ⟨(generatedTwelfthTensorSourceInitialLabel p.1 p.2).val, by
    have h := (generatedTwelfthTensorSourceInitialLabel p.1 p.2).isLt
    omega⟩

/-- The complementary upper spin label has the opposite Omega coefficient. -/
def generatedTenthSourceInitialTensorSparseHigh
    (p : GeneratedTenthSourceInitialTensorSparseIndex) : Fin 4096 :=
  ⟨(generatedTwelfthTensorSourceInitialLabel p.1 p.2).val + 2048, by
    have h := (generatedTwelfthTensorSourceInitialLabel p.1 p.2).isLt
    omega⟩

/-- The physical coordinate is the genuine original coordinate unit vector's index. -/
def generatedTenthSourceInitialTensorSparseCoordinate
    (p : GeneratedTenthSourceInitialTensorSparseIndex) : Fin 24 :=
  generatedTwelfthTensorSourceCoordinate p.1

/-- This sign includes both the original Parker phase and the physical Golay code sign. -/
def generatedTenthSourceInitialTensorSparseSign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) : ℤ :=
  generatedTwelfthTensorSourceInitialCoefficient p.1 p.2

/-- Each of the 64 atoms includes both signed spin coordinates, rather than dropping Omega. -/
def generatedTenthSourceInitialTensorSparseIntegerAtom
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (k : Fin 4096) (i : Fin 24) : ℤ :=
  generatedTenthSourceInitialTensorSparseSign p *
    ((if k = generatedTenthSourceInitialTensorSparseLow p then 1 else 0) -
      (if k = generatedTenthSourceInitialTensorSparseHigh p then 1 else 0)) *
    generatedTwelfthTensorSourceSpatial p.1 i

/-- The real coefficient normalization is subsequently bound to the actual Fifth source. -/
def generatedTenthSourceInitialTensorSparseAtom
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (t : SpinIndex) (i : Fin 24) : ℝ :=
  (generatedTenthSourceInitialTensorSparseIntegerAtom p
    (generatedAxisGlobalSpinLabel t) i : ℝ) / Real.sqrt 2

/-- All original lower and upper coordinates, including every other coordinate as zero. -/
def generatedTenthSourceInitialTensorSparseInteger (k : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ r : Fin 8, ∑ n : Fin 8,
    generatedTenthSourceInitialTensorSparseIntegerAtom (r, n) k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

