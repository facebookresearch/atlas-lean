/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.FiberReflection

/-!
# Ordinary clients of the full extension fiber reflection

The clients retain independent object and Hom universes, arbitrary raw
representatives, the actual kernel comparison and the literal target identity.
The standard inverse and isomorphism APIs require only the exact-category
structures and the original fiber arrow.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory Limits AlgebraicKTheory
open scoped ZeroObject

universe u v

namespace AlgebraicKTheory.ExtensionFiberReflectionTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  (X : C)
  {a b : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
  (f : a ⟶ b)

example : IsIso f := inferInstance

example : a ≅ b := asIso f

example : f ≫ inv f = 𝟙 a := IsIso.hom_inv_id f

example : inv f ≫ f = 𝟙 b := IsIso.inv_hom_id f

example : Functor.IsHomLift (ExtensionCategory.target (C := C))
    (𝟙 (⟨X⟩ : QuillenQ C)) (inv f).val :=
  (inv f).property

example (d : ExtensionDiagram a.val b.val) (hd : ExtensionCategory.mkHom d = f.val) :
    d.lambda ≫ eqToHom (congrArg QuillenQ.obj a.property) =
      d.mu ≫ eqToHom (congrArg QuillenQ.obj b.property) :=
  (ExtensionCategory.fiber_identity_span_reflection X f d hd).1

example (d : ExtensionDiagram a.val b.val) (hd : ExtensionCategory.mkHom d = f.val) :
    IsIso d.lambda ∧ IsIso d.mu ∧ IsIso d.alpha ∧ IsIso d.beta := by
  obtain ⟨_, hl, hm, ha, hb, _⟩ := ExtensionCategory.fiber_identity_span_reflection X f d hd
  exact ⟨hl, hm, ha, hb⟩

example (d : ExtensionDiagram a.val b.val) (hd : ExtensionCategory.mkHom d = f.val) :
    ∃ e : b.val.row.X₁ ≅ a.val.row.X₁,
      e.hom = d.alpha ∧ e.inv ≫ d.j = a.val.row.f := by
  obtain ⟨_, _, _, _, _, e, di, g, he, hk, _⟩ :=
    ExtensionCategory.fiber_identity_span_reflection X f d hd
  exact ⟨e, he, hk⟩

example (d : ExtensionDiagram a.val b.val) (hd : ExtensionCategory.mkHom d = f.val) :
    ∃ (di : ExtensionDiagram b.val a.val) (g : b ⟶ a),
      g.val = ExtensionCategory.mkHom di ∧
      ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom di = 𝟙 a.val ∧
      ExtensionCategory.mkHom di ≫ ExtensionCategory.mkHom d = 𝟙 b.val ∧
      Functor.IsHomLift (ExtensionCategory.target (C := C))
        (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom di) ∧
      f ≫ g = 𝟙 a ∧ g ≫ f = 𝟙 b := by
  obtain ⟨_, _, _, _, _, e, di, g, _, _, hg, hleft, hright, hlift, hfg, hgf⟩ :=
    ExtensionCategory.fiber_identity_span_reflection X f d hd
  exact ⟨di, g, hg, hleft, hright, hlift, hfg, hgf⟩

example {a₀ b₀ : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨(0 : C)⟩ : QuillenQ C)}
    (f₀ : a₀ ⟶ b₀) : f₀ ≫ inv f₀ = 𝟙 a₀ := IsIso.hom_inv_id f₀

end AlgebraicKTheory.ExtensionFiberReflectionTests

end
