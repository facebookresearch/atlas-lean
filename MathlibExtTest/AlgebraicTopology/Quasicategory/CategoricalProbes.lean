/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.Quasicategory.CategoricalProbes

/-!
# Clients for categorical equivalences on arbitrary probes

The probe below is an arbitrary simplicial set. Ordinary full faithfulness
provides an actual preimage morphism with its image equation, and essential
surjectivity provides an object with an isomorphism to a specified vertex.
-/

open CategoryTheory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example [Quasicategory X] [Quasicategory Y]
    (hf : categoricalEquivalences f) (K : SSet.{u})
    (a b : ((ihom K).obj X).HomotopyCategory)
    (φ : (mapHomotopyCategory ((ihom K).map f)).obj a ⟶
      (mapHomotopyCategory ((ihom K).map f)).obj b) :
    ∃ ψ : a ⟶ b, (mapHomotopyCategory ((ihom K).map f)).map ψ = φ := by
  let := hf.isEquivalence_mapHomotopyCategory_ihomMap K
  exact ⟨(mapHomotopyCategory ((ihom K).map f)).preimage φ,
    Functor.map_preimage _ φ⟩

example [Quasicategory X] [Quasicategory Y]
    (hf : categoricalEquivalences f) (K : SSet.{u})
    (v : ((ihom K).obj Y) _⦋0⦌) :
    ∃ a : ((ihom K).obj X).HomotopyCategory,
      Nonempty ((mapHomotopyCategory ((ihom K).map f)).obj a ≅
        HomotopyCategory.mk v) := by
  let := hf.isEquivalence_mapHomotopyCategory_ihomMap K
  exact Functor.EssSurj.mem_essImage (mapHomotopyCategory ((ihom K).map f))
    (HomotopyCategory.mk v)

end SSet
