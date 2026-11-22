/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# Intrinsic Dwyer–Kan equivalences of Segal spaces

For Reedy-fibrant Segal spaces, intrinsic Dwyer–Kan equivalence means weakness on every original
mapping fibre and essential surjectivity of the induced homotopy-category functor. The mapping-
fibre condition supplies full faithfulness, giving the equivalent criterion with a homotopy-
category equivalence. These equivalences are closed under composition, and two adjacent
Dwyer–Kan composite conditions imply essential surjectivity of the first functor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace.IntrinsicDK

/-- Original intrinsic DK: full weakness on EVERY mapping fibre and essential
surjectivity of the SAME original intrinsic Ho functor. -/
def isEquivalence {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) : Prop :=
  (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
    SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x) (y := y) rfl rfl)) ∧
    (SegalHomotopy.map f hW hV).EssSurj

/-- This definition retains Rezk's actual category-equivalence condition;
the full and faithful fields are DERIVED from the original full fibre maps. -/
theorem iff_mappingWeak_and_HoIsEquivalence {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    isEquivalence f hW hV ↔
      (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
        SSet.realizationWeakEquivalences
          (mappingFibre.map f (x := x) (y := y) rfl rfl)) ∧
        (SegalHomotopy.map f hW hV).IsEquivalence := by
  constructor
  · rintro ⟨hm, he⟩
    exact ⟨hm, SegalHomotopy.map_isEquivalence_of_mappingFibreWeak_of_essSurj
      f hW hV hm he⟩
  · rintro ⟨hm, he⟩
    exact ⟨hm, he.essSurj⟩

/-- Rezk7.5 composition keeps the whole original mapping-fibre maps and
the actual composite Ho functor, for RF Segal endpoints without completeness. -/
theorem comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (hW : segalSpaces W) (hV : segalSpaces V) (hU : segalSpaces U)
    (hf : isEquivalence f hW hV) (hg : isEquivalence g hV hU) :
    isEquivalence (f ≫ g) hW hU := by
  rcases hf with ⟨hfM, hfE⟩
  rcases hg with ⟨hgM, hgE⟩
  constructor
  · intro x y
    rw [← mappingFibre.map_comp f g rfl rfl rfl rfl]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ (hfM x y)
      (hgM (mappingVertexMap f x) (mappingVertexMap f y))
  · rw [SegalHomotopy.map_comp f g hW hV hU]
    let : (SegalHomotopy.map f hW hV).EssSurj := hfE
    let : (SegalHomotopy.map g hV hU).EssSurj := hgE
    infer_instance

/-- The original Ho essential-image witness for f is lifted through the
fully faithful SAME Ho(g≫h), from the actual Ho(f≫g) object witness. -/
theorem leftHoEssSurj_of_two_composites {A B C D : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hA : segalSpaces A) (hB : segalSpaces B)
    (hC : segalSpaces C) (hD : segalSpaces D)
    (hfg : isEquivalence (f ≫ g) hA hC)
    (hgh : isEquivalence (g ≫ h) hB hD) :
    (SegalHomotopy.map f hA hB).EssSurj := by
  let F := SegalHomotopy.map f hA hB
  let G := SegalHomotopy.map g hB hC
  let H := SegalHomotopy.map h hC hD
  let : (F ⋙ G).IsEquivalence := by
    change (SegalHomotopy.map f hA hB ⋙ SegalHomotopy.map g hB hC).IsEquivalence
    rw [← SegalHomotopy.map_comp f g hA hB hC]
    exact ((iff_mappingWeak_and_HoIsEquivalence _ _ _).mp hfg).2
  let : (G ⋙ H).IsEquivalence := by
    change (SegalHomotopy.map g hB hC ⋙ SegalHomotopy.map h hC hD).IsEquivalence
    rw [← SegalHomotopy.map_comp g h hB hC hD]
    exact ((iff_mappingWeak_and_HoIsEquivalence _ _ _).mp hgh).2
  refine ⟨fun b => ?_⟩
  let a := (F ⋙ G).objPreimage (G.obj b)
  let e : G.obj (F.obj a) ≅ G.obj b := (F ⋙ G).objObjPreimageIso (G.obj b)
  exact ⟨a, ⟨(G ⋙ H).preimageIso (H.mapIso e)⟩⟩

end SimplicialSpace.IntrinsicDK
