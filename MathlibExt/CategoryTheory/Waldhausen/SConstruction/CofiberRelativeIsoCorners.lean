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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeCofibrations

/-!
# Actual relative cofibration corners with an original isomorphic leg

An isomorphic original source component makes its pushout corner the
original source middle object. An isomorphic original cofiber inclusion
makes its pushout corner the original target source object. The two
original naturality equations give the corner maps and their cofibrations.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- If the original source component is an isomorphism and the original
middle component is a cofibration, the whole row map is a relative cofibration. -/
theorem relativeCofibrations_of_source_isIso {S T : CofiberSequenceCategory C} (φ : S ⟶ T)
    [IsIso ((source C).map φ)] (hMiddle : IsCofibration ((middle C).map φ)) :
    relativeCofibrations C φ := by
  let a := φ.hom.app (0 : Fin 3)
  let b := φ.hom.app (1 : Fin 3)
  let : IsIso a := inferInstanceAs (IsIso ((source C).map φ))
  change IsCofibration b at hMiddle
  have hNat : S.obj.map' 0 1 ≫ b = a ≫ T.obj.map' 0 1 :=
    φ.hom.naturality (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))
  have hPushout : IsPushout (S.obj.map' 0 1) a (𝟙 (S.obj.obj' 1))
      (inv a ≫ S.obj.map' 0 1) :=
    IsPushout.of_vert_isIso (by
      constructor
      simp only [Category.comp_id, IsIso.hom_inv_id_assoc])
  apply (mem_relativeCofibrations_raw_iff C φ).mpr
  refine ⟨(WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso a,
    S.obj.obj' 1, 𝟙 _, inv a ≫ S.obj.map' 0 1, b, hPushout,
    Category.id_comp b, ?_, hMiddle⟩
  rw [Category.assoc, hNat, IsIso.inv_hom_id_assoc]

/-- An original isomorphic source-row inclusion and a cofibration source
component give the actual relative corner for the entire cofiber-row map. -/
theorem relativeCofibrations_of_inclusion_isIso {S T : CofiberSequenceCategory C} (φ : S ⟶ T)
    [IsIso (S.obj.map' 0 1)] (hSource : IsCofibration ((source C).map φ)) :
    relativeCofibrations C φ := by
  let e : (0 : Fin 3) ⟶ 1 := homOfLE (show (0 : Fin 3) ≤ 1 from by decide)
  let s : S.obj.obj (0 : Fin 3) ⟶ S.obj.obj 1 := S.obj.map e
  let t : T.obj.obj (0 : Fin 3) ⟶ T.obj.obj 1 := T.obj.map e
  let a : S.obj.obj (0 : Fin 3) ⟶ T.obj.obj 0 := φ.hom.app 0
  let b : S.obj.obj (1 : Fin 3) ⟶ T.obj.obj 1 := φ.hom.app 1
  let : IsIso s := inferInstanceAs (IsIso (S.obj.map' 0 1))
  change IsCofibration a at hSource
  have hNat : s ≫ b = a ≫ t := φ.hom.naturality e
  have ht : IsCofibration t := T.property.1
  have hPushout : IsPushout s a (inv s ≫ a) (𝟙 (T.obj.obj (0 : Fin 3))) :=
    IsPushout.of_horiz_isIso (by
      constructor
      simp only [Category.comp_id, IsIso.hom_inv_id_assoc])
  apply (mem_relativeCofibrations_raw_iff C φ).mpr
  change IsCofibration a ∧
    ∃ (P : C) (inB : S.obj.obj (1 : Fin 3) ⟶ P) (inA : T.obj.obj (0 : Fin 3) ⟶ P)
      (d : P ⟶ T.obj.obj (1 : Fin 3)),
      IsPushout s a inB inA ∧ inB ≫ d = b ∧ inA ≫ d = t ∧ IsCofibration d
  refine ⟨hSource, T.obj.obj (0 : Fin 3), inv s ≫ a, 𝟙 _, t, hPushout,
    ?_, Category.id_comp t, ht⟩
  rw [Category.assoc, ← hNat, IsIso.inv_hom_id_assoc]

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
