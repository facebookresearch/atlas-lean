/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Original localizing-map monomorphisms

Every original Segal/full-E localizing map is monic, both as a raw simplicial
space map and under the actual designated carrier functor. The completeness
map retains the full walking-isomorphism nerve and selected source vertex.
Its monicity uses only its actual terminal zero-simplex source; no target
quasicategory, Kan, model, nonemptiness or finite-dimensional hypothesis occurs.

Source: Rezk, *A model for the homotopy theory of homotopy theory*, §§4 and 6.
The generic terminal-source/constant-whiskering facts are existing native APIs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SSet.Rezk

private theorem mono_discrete {X Y : SSet.{u}} (f : X ⟶ Y) (hf : Mono f) :
    Mono (SSet.simplicialSpaceDiscrete.map f) := by
  let _ : Mono f := hf
  let _ : (SimplicialObject.const (Type u)).PreservesMonomorphisms := inferInstance
  change Mono (((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
    (SimplicialObject.const (Type u))).map f)
  infer_instance

/-- Every original Segal/full-E localizing map is monic, without model or QC input. -/
theorem localizingMap_mono (i : LocalizingIndex) : Mono (localizingMap.{u} i).hom := by
  cases i with
  | inl n =>
      exact mono_discrete (spineSubcomplex.{u} n.1).ι inferInstance
  | inr p =>
      have hT : IsTerminal (Δ[0] : SSet.{u}) := by
        change IsTerminal ((uliftYoneda : SimplexCategory ⥤ SSet.{u}).obj ⦋0⦌)
        exact SimplexCategory.isTerminalZero.isTerminalObj
          (uliftYoneda : SimplexCategory ⥤ SSet.{u}) _
      exact mono_discrete (SSet.yonedaEquiv.symm SSet.coherentIso.x₀)
        (hT.mono_from _)

end SSet.Rezk

namespace SimplicialSpace

/-- The SAME original localizing arrow is monic in the designated carrier. -/
theorem localizingMap_mono (i : SSet.Rezk.LocalizingIndex) :
    Mono (ofSimplicialObject.mapArrow.obj (SSet.Rezk.localizingMap.{u} i)).hom := by
  let _ : Mono (SSet.Rezk.localizingMap.{u} i).hom := SSet.Rezk.localizingMap_mono i
  change Mono (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} i).hom)
  infer_instance

end SimplicialSpace
