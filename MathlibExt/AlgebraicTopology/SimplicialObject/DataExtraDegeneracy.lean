/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmented

/-!
# Data-level left extra degeneracy

Left-handed extra-degeneracy structure on augmented simplicial `Data`: a section
`s'` and extra degeneracies `s n` with distinguished face-`0` identity
`s n ≫ δ 0 = 𝟙`. Positive faces and degeneracies commute via `Fin.succ`.
This is the `Data`-level analogue of Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy`, transported by
`ExtraDegeneracy.toSimplicial`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Data
namespace Augmented

variable {C : Type u} [Category.{v} C]

/--
Left-handed extra-degeneracy structure for augmented simplicial data,
mirroring `SimplicialObject.Augmented.ExtraDegeneracy` with natural-number
degrees and `Data.δ`/`Data.σ`.
-/
@[ext]
structure ExtraDegeneracy (X : Augmented C) where
  /-- A section from the augmentation point to degree zero -/
  s' : X.right ⟶ X.left.obj 0
  /-- Extra degeneracies `X_n ⟶ X_{n+1}` -/
  s : ∀ n : ℕ, X.left.obj n ⟶ X.left.obj (n + 1)
  /-- Section / augmentation identity -/
  s'_comp_ε : s' ≫ X.hom.app 0 = 𝟙 X.right := by cat_disch
  /-- Degree-zero compatibility with face `1` -/
  s₀_comp_δ₁ : s 0 ≫ X.left.δ (1 : Fin 2) = X.hom.app 0 ≫ s' := by cat_disch
  /-- Distinguished face-`0` identity -/
  s_comp_δ₀ : ∀ n : ℕ, s n ≫ X.left.δ (0 : Fin (n + 2)) = 𝟙 _ := by cat_disch
  /-- Compatibility with all positive faces -/
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.succ = X.left.δ i ≫ s n := by
    cat_disch
  /-- Compatibility with all positive degeneracies -/
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.succ = X.left.σ i ≫ s (n + 1) := by
    cat_disch

namespace ExtraDegeneracy

attribute [reassoc] s₀_comp_δ₁ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ₀

end ExtraDegeneracy

end Augmented
end Data
end SimplicialObject
end CategoryTheory

end
