/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AbelianImagesUltraproducts
import Mathlib.Algebra.Group.Pi.Hom

open MathlibExt.GroupTheory.AbelianImagesUltraproductsKourovka20Problem13Wanted

-- A principal ultrafilter detects exactly one coordinate, even for nonabelian factors.
example (k : ℕ) (G : ℕ → Type) [∀ i, Group (G i)] :
    ultraproductKernel (pure k) G = (Pi.evalMonoidHom G k).ker := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    change ∀ᶠ i in ((pure k : Ultrafilter ℕ) : Filter ℕ), x i = 1 at hx
    simpa using hx
  · intro x hx
    apply Subgroup.subset_normalClosure
    change ∀ᶠ i in ((pure k : Ultrafilter ℕ) : Filter ℕ), x i = 1
    simpa using hx

-- A nonprincipal ultrafilter ignores every finite set of changed coordinates.
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : ℕ → Type) [∀ i, Group (G i)] (x y : ∀ i, G i) (h : {i | x i ≠ y i}.Finite) :
    (QuotientGroup.mk x : Ultraproduct U G) = QuotientGroup.mk y := by
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  have hxy : ∀ᶠ i in (U : Filter ℕ), x i = y i := hU (Filter.eventually_cofinite.mpr h)
  exact hxy.mono fun i hi => show (x i)⁻¹ * y i = 1 by simp [hi]
