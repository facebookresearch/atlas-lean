/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Exact-functor preservation of cofiber sequences

For an additive exact functor `F : C ⥤ D` between Quillen exact categories,
a cofibration sequence `f`, `g` in the standard structure
`ExactCategory.waldhausenCategory C` maps to a cofibration sequence
`F.map f`, `F.map g` in `ExactCategory.waldhausenCategory D`.

The proof goes through the existing admissible-exact bridge only:
`ExactCategory.isAdmissibleExact_of_isCofibrationSequence` turns the
hypothesis into `IsAdmissibleExact S` for `S := ShortComplex.mk f g w`
(with `w : f ≫ g = 0` read off the pushout `hPush.w` and the unique
legs `X ⟶ 0`, `0 ⟶ Z`), `Functor.map_admissibleExact` transports it to
`S.map F`, and `ExactCategory.isCofibrationSequence_of_isAdmissibleExact`
returns the target cofibration sequence (with legs reducing to `F.map f`
and `F.map g` via the `ShortComplex.map` computation rules).

Requires `[Preadditive] [HasZeroObject] [HasBinaryBiproducts] [ExactCategory]`
on each of `C`, `D`, plus `[F.Additive] [F.IsExact]`; no other hypotheses.

Nonclaims: no functor wrapper on cofiber sequences, no general Waldhausen
transport class, no `WaldhausenCategoryWithoutGluing (CofiberSequenceCategory _)` instance,
and no additivity claim.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- An additive exact functor sends a standard-structure cofibration sequence
to a cofibration sequence on the mapped arrows. -/
theorem isCofibrationSequence_map (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : @IsCofibrationSequence C _ _
      (ExactCategory.waldhausenCategory C) X Y Z f g) :
    @IsCofibrationSequence D _ _
      (ExactCategory.waldhausenCategory D) _ _ _ (F.map f) (F.map g) := by
  obtain ⟨hf, h, q, hPush⟩ := hSeq
  have hw : f ≫ g = h ≫ q := hPush.w.symm
  have h_eq : h = (0 : X ⟶ (0 : C)) :=
    (isZero_zero C).eq_of_tgt h 0
  have q_eq : q = (0 : (0 : C) ⟶ Z) :=
    (isZero_zero C).eq_of_src q 0
  have w : f ≫ g = 0 := by
    calc f ≫ g = h ≫ q := hw
      _ = (0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Z) := by
          rw [h_eq, q_eq]
      _ = 0 := by simp
  let S : ShortComplex C := ShortComplex.mk f g w
  have hS : ExactCategory.IsAdmissibleExact S :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence
      (S := S) ⟨hf, h, q, hPush⟩
  have hSMapped : ExactCategory.IsAdmissibleExact (S.map F) :=
    F.map_admissibleExact S hS
  have hSeqMapped : @IsCofibrationSequence D _ _
      (ExactCategory.waldhausenCategory D) _ _ _
      (S.map F).f (S.map F).g :=
    ExactCategory.isCofibrationSequence_of_isAdmissibleExact hSMapped
  simpa [S, ShortComplex.map] using hSeqMapped

end CategoryTheory.Waldhausen.SConstruction
