/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKComposition
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKTransport
import MathlibExt.AlgebraicTopology.SimplicialSpace.CategoricalHomotopyPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree

/-!
# Saturation and homotopy invariance of Dwyer–Kan equivalences

Intrinsic Dwyer–Kan equivalences between Reedy-fibrant Segal spaces satisfy two-out-of-six:
equivalence of f ≫ g and g ≫ h implies equivalence of f, g, h and the threefold composite.
Mapping-fibre weakness extends from an essential image to every object pair, and the Dwyer–Kan
predicate is invariant under the specified walking-isomorphism homotopies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

namespace SimplicialSpace.IntrinsicDK
open SegalHomotopy

/-- Every original f-fibre map is weak from the two original composite DK
premises, using the EXISTING scalar left-of-two-composites theorem. -/
theorem mappingFibreWeak_left_of_two_composites {A B C D : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hA : segalSpaces A) (hB : segalSpaces B)
    (hC : segalSpaces C) (hD : segalSpaces D)
    (hfg : isEquivalence (f ≫ g) hA hC)
    (hgh : isEquivalence (g ≫ h) hB hD)
    (x y : (A.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl) := by
  let mf := mappingFibre.map f (x := x) (y := y) rfl rfl
  let mg := mappingFibre.map g (x := mappingVertexMap f x) (y := mappingVertexMap f y) rfl rfl
  let mh := mappingFibre.map h (x := mappingVertexMap g (mappingVertexMap f x))
    (y := mappingVertexMap g (mappingVertexMap f y)) rfl rfl
  have h1 : SSet.realizationWeakEquivalences (mf ≫ mg) := by
    dsimp only [mf, mg]
    rw [mappingFibre.map_comp f g rfl rfl rfl rfl]
    exact hfg.1 x y
  have h2 : SSet.realizationWeakEquivalences (mg ≫ mh) := by
    dsimp only [mg, mh]
    rw [mappingFibre.map_comp g h rfl rfl rfl rfl]
    exact hgh.1 (mappingVertexMap f x) (mappingVertexMap f y)
  exact SSet.realizationWeakEquivalences.left_of_comp_comp h1 h2

/-- Cancellation on actual f-images is transported to EVERY original B
vertex pair by genuine original Ho essential-image Isos and full MF transport. -/
theorem mappingFibreWeak_of_essSurj_precomp {A B C : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C)
    (hA : segalSpaces A) (hB : segalSpaces B) (hC : segalSpaces C)
    (hf : isEquivalence f hA hB) (hfg : isEquivalence (f ≫ g) hA hC)
    (x' y' : (B.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map g (x := x') (y := y') rfl rfl) := by
  let F := SegalHomotopy.map f hA hB
  let : F.EssSurj := hf.2
  let x : Object A hA := F.objPreimage (⟨x'⟩ : Object B hB)
  let y : Object A hA := F.objPreimage (⟨y'⟩ : Object B hB)
  let ax : (⟨mappingVertexMap f x.vertex⟩ : Object B hB) ≅ (⟨x'⟩ : Object B hB) :=
    F.objObjPreimageIso (⟨x'⟩ : Object B hB)
  let ay : (⟨mappingVertexMap f y.vertex⟩ : Object B hB) ≅ (⟨y'⟩ : Object B hB) :=
    F.objObjPreimageIso (⟨y'⟩ : Object B hB)
  let mf := mappingFibre.map f (x := x.vertex) (y := y.vertex) rfl rfl
  let mg := mappingFibre.map g (x := mappingVertexMap f x.vertex)
    (y := mappingVertexMap f y.vertex) rfl rfl
  have hcomp : SSet.realizationWeakEquivalences (mf ≫ mg) := by
    dsimp only [mf, mg]
    rw [mappingFibre.map_comp f g rfl rfl rfl rfl]
    exact hfg.1 x.vertex y.vertex
  have hImage : SSet.realizationWeakEquivalences mg :=
    SSet.realizationWeakEquivalences.of_precomp mf mg (hf.1 x.vertex y.vertex) hcomp
  exact (mappingFibreWeak_iff_of_HoIsos g hB hC
    (mappingVertexMap f x.vertex) x' (mappingVertexMap f y.vertex) y' ax ay).mp hImage

/-- Rezk7.5 two-out-of-six: the original maps `f`, `g`, and `h`, and the
threefold composite `(f ≫ g) ≫ h`, are intrinsic DK equivalences, retaining
all original vertex pairs and Ho functors for the given Segal spaces. -/
theorem two_out_of_six {A B C D : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hA : segalSpaces A) (hB : segalSpaces B)
    (hC : segalSpaces C) (hD : segalSpaces D)
    (hfg : isEquivalence (f ≫ g) hA hC)
    (hgh : isEquivalence (g ≫ h) hB hD) :
    isEquivalence f hA hB ∧ isEquivalence g hB hC ∧ isEquivalence h hC hD ∧
      isEquivalence ((f ≫ g) ≫ h) hA hD := by
  have hf : isEquivalence f hA hB :=
    ⟨mappingFibreWeak_left_of_two_composites f g h hA hB hC hD hfg hgh,
      leftHoEssSurj_of_two_composites f g h hA hB hC hD hfg hgh⟩
  let F := SegalHomotopy.map f hA hB
  let G := SegalHomotopy.map g hB hC
  let H := SegalHomotopy.map h hC hD
  let : F.IsEquivalence := ((iff_mappingWeak_and_HoIsEquivalence _ _ _).mp hf).2
  let : (F ⋙ G).IsEquivalence := by
    change (SegalHomotopy.map f hA hB ⋙ SegalHomotopy.map g hB hC).IsEquivalence
    rw [← SegalHomotopy.map_comp f g hA hB hC]
    exact ((iff_mappingWeak_and_HoIsEquivalence _ _ _).mp hfg).2
  let : G.IsEquivalence := Functor.isEquivalence_of_comp_left F G
  have hg : isEquivalence g hB hC :=
    ⟨mappingFibreWeak_of_essSurj_precomp f g hA hB hC hf hfg, inferInstance⟩
  let : (G ⋙ H).IsEquivalence := by
    change (SegalHomotopy.map g hB hC ⋙ SegalHomotopy.map h hC hD).IsEquivalence
    rw [← SegalHomotopy.map_comp g h hB hC hD]
    exact ((iff_mappingWeak_and_HoIsEquivalence _ _ _).mp hgh).2
  let : H.IsEquivalence := Functor.isEquivalence_of_comp_left G H
  have hh : isEquivalence h hC hD :=
    ⟨mappingFibreWeak_of_essSurj_precomp g h hB hC hD hg hgh, inferInstance⟩
  exact ⟨hf, hg, hh, IntrinsicDK.comp (f ≫ g) h hA hC hD hfg hh⟩

/-- Actual categorical-E homotopies preserve both parts of intrinsic DK,
using the independently proved FULL fibre and Ho naturality prism kernels. -/
theorem categorical_homotopy_iff {U V : SimplicialSpace.{u}} (f0 f1 : U ⟶ V)
    (hU : segalSpaces U) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ V.diagram)
    (h0 : CategoricalHomotopyPrism.tensorEndpoint U SSet.coherentIso.x₀ ≫ H = f0.hom)
    (h1 : CategoricalHomotopyPrism.tensorEndpoint U SSet.coherentIso.x₁ ≫ H = f1.hom) :
    isEquivalence f0 hU hV ↔ isEquivalence f1 hU hV := by
  constructor
  · rintro ⟨hm, he⟩
    exact ⟨fun x y => (CategoricalHomotopyPrism.mappingFibreWeak_iff
      f0 f1 hV H h0 h1 x y).mp (hm x y),
      (CategoricalHomotopyPrism.homotopyHoEssSurj_iff f0 f1 hU hV H h0 h1).mp he⟩
  · rintro ⟨hm, he⟩
    exact ⟨fun x y => (CategoricalHomotopyPrism.mappingFibreWeak_iff
      f0 f1 hV H h0 h1 x y).mpr (hm x y),
      (CategoricalHomotopyPrism.homotopyHoEssSurj_iff f0 f1 hU hV H h0 h1).mpr he⟩

/-- FULL Rezk13.8 retains two DIFFERENT inverse candidates and two
independent original E homotopies. The full MF/Ho conclusion is derived. -/
theorem of_categorical_equivalence {U V : SimplicialSpace.{u}}
    (g : U ⟶ V) (f h : V ⟶ U) (hU : segalSpaces U) (hV : segalSpaces V)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj V.diagram ⟶ V.diagram)
    (K : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj U.diagram ⟶ U.diagram)
    (hH0 : CategoricalHomotopyPrism.tensorEndpoint V SSet.coherentIso.x₀ ≫ H = (f ≫ g).hom)
    (hH1 : CategoricalHomotopyPrism.tensorEndpoint V SSet.coherentIso.x₁ ≫ H = (𝟙 V : V ⟶ V).hom)
    (hK0 : CategoricalHomotopyPrism.tensorEndpoint U SSet.coherentIso.x₀ ≫ K = (g ≫ h).hom)
    (hK1 : CategoricalHomotopyPrism.tensorEndpoint U SSet.coherentIso.x₁ ≫ K = (𝟙 U : U ⟶ U).hom) :
    isEquivalence g hU hV := by
  have hiU : isEquivalence (𝟙 U) hU hU := by
    constructor
    · intro x y
      rw [mappingFibre.map_id]
      exact SSet.realizationWeakEquivalences.id_mem _
    · rw [SegalHomotopy.map_id]
      infer_instance
  have hiV : isEquivalence (𝟙 V) hV hV := by
    constructor
    · intro x y
      rw [mappingFibre.map_id]
      exact SSet.realizationWeakEquivalences.id_mem _
    · rw [SegalHomotopy.map_id]
      infer_instance
  have hfg : isEquivalence (f ≫ g) hV hV :=
    (categorical_homotopy_iff (f ≫ g) (𝟙 V) hV hV H hH0 hH1).mpr hiV
  have hgh : isEquivalence (g ≫ h) hU hU :=
    (categorical_homotopy_iff (g ≫ h) (𝟙 U) hU hU K hK0 hK1).mpr hiU
  exact (two_out_of_six f g h hV hU hV hU hfg hgh).2.1

end SimplicialSpace.IntrinsicDK
