/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import MathlibExt.Algebra.Homology.Functor

/-!
# Applying a homology-preserving functor to a spectral sequence

The pages are the mapped original complexes. The successor isomorphisms use
the canonical homology comparison followed by the mapped original
isomorphism. No new choice of page homology data is made.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe vC uC vD uD uκ

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]

/-- Apply a homology-preserving functor to all pages and the actual
successor homology isomorphisms of a spectral sequence. -/
def mapSpectralSequence (X : SpectralSequence C c r₀) : SpectralSequence D c r₀ where
  page r hr := (F.mapHomologicalComplex (c r)).obj (X.page r hr)
  iso r r' x hrr' hr :=
    (HomologicalComplex.mapHomologyFunctorIso x F).app (X.page r hr) ≪≫
      F.mapIso (X.iso r r' x hrr' hr)

/-- The mapped page is the original page with the functor applied degreewise. -/
@[simp]
theorem mapSpectralSequence_page (X : SpectralSequence C c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    (F.mapSpectralSequence X).page r hr =
      (F.mapHomologicalComplex (c r)).obj (X.page r hr) := rfl

/-- The successor comparison retains the canonical homology-preservation
isomorphism and the original successor map. -/
@[simp]
theorem mapSpectralSequence_iso (X : SpectralSequence C c r₀)
    (r r' : ℤ) (x : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) :
    (F.mapSpectralSequence X).iso r r' x hrr' hr =
      (HomologicalComplex.mapHomologyFunctorIso x F).app (X.page r hr) ≪≫
        F.mapIso (X.iso r r' x hrr' hr) := rfl

end CategoryTheory.Functor

end
