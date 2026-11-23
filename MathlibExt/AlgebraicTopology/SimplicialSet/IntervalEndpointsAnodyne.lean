/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# Anodyne endpoints of the actual simplicial interval

The canonical face/horn calculation is moved once from the finite Joyal
interval consumer. Both original zero-face maps are anodyne over every
simplicial universe, with no interval replacement or type-transparency option.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet

/-- A face of the one-simplex is a one-dimensional horn up to its face iso. -/
public theorem anodyneExtensions_stdSimplex_endpoint (i : Fin 2) :
    anodyneExtensions (stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h : (stdSimplex.face {i}ᶜ : (Δ[1] : SSet.{u}).Subcomplex) = horn 1 i.rev := by
    fin_cases i
    all_goals
      ext m x
      simp [horn_eq_iSup]
  have hι : anodyneExtensions (stdSimplex.face {i}ᶜ :
      (Δ[1] : SSet.{u}).Subcomplex).ι := by
    rw [h]
    exact anodyneExtensions.horn_ι i.rev
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using
    anodyneExtensions.comp_mem (stdSimplex.faceSingletonComplIso.{u} i).hom
      (stdSimplex.face {i}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι
      (anodyneExtensions.of_isIso _) hι

end SSet

end
