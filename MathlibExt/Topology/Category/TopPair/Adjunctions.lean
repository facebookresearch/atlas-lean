/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

module

public import Mathlib.Topology.Category.TopPair

/-!
# Diagonal adjunction for topological pairs

This file provides the adjunction `TopPair.diag ⊣ TopPair.proj₂`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopPair

/-- The diagonal functor is left adjoint to the second projection. -/
noncomputable def diagAdjProj₂ : diag ⊣ proj₂ where
  unit.app X := 𝟙 X
  counit :=
    { app X := TopPair.ofHom X.map (𝟙 X.snd)
      naturality X Y f := by
        apply MorphismProperty.Arrow.Hom.ext
        · rfl
        · exact f.w }

end TopPair
