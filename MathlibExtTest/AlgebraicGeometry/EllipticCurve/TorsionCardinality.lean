/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.TorsionCardinality
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

namespace MetaMathlibExt

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

/-- Consumer with the original binders, restated verbatim. -/
theorem exactSource {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed W hn

/-- Higher-universe consumer: the fields may live in any universe. -/
theorem exactSourceUniverse.{u} {F : Type u} {K : Type u} [Field F]
    [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed W hn

open scoped Classical in
open scoped Classical in
/-- The `1`-torsion is trivial: only the zero point. -/
example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Nat.card (Submodule.torsionBy ℤ
      (W⁄(AlgebraicClosure ℚ)).Point 1) = 1 := by
  have h : ((1 : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  simpa using WeierstrassCurve.card_torsion_of_isAlgClosed W h

open scoped Classical in
/-- The `2`-torsion over an algebraically closed field of characteristic
zero has four points. -/
example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Nat.card (Submodule.torsionBy ℤ
      (W⁄(AlgebraicClosure ℚ)).Point 2) = 4 := by
  have h : ((2 : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  simpa using WeierstrassCurve.card_torsion_of_isAlgClosed W h

end MetaMathlibExt
