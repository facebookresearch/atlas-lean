/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.MappedCoproducts
public import Batteries.Tactic.Lint

/-!
# Generic clients of mapped coproducts

Use arbitrary source and target category universes, literal original arrows,
and caller-supplied cofans. The output includes a whole Arrow comparison to
a map of an arrow satisfying the original source property.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w u v uD vD

open CategoryTheory Limits MorphismProperty

namespace MappedCoproductsTest

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  (P : MorphismProperty C) (F : C ⥤ D)
  [HasCoproducts.{w} C] [PreservesColimitsOfSize.{w, w} F]
  [P.IsStableUnderCoproducts.{w}]

/-- Arbitrary coproduct cofans of literal images retain a source-arrow representative. -/
theorem originalImages_have_representative {I : Type w} {A B : I → C}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, P (f i))
    (c₁ : Cocone (Discrete.functor (fun i => F.obj (A i))))
    (c₂ : Cocone (Discrete.functor (fun i => F.obj (B i))))
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    ∃ (X Y : C) (g : X ⟶ Y), P g ∧
      Nonempty (Arrow.mk (F.map g) ≅
        Arrow.mk (hc₁.desc (Cocone.mk _
          (Discrete.natTrans
            (F := Discrete.functor (fun i => F.obj (A i)))
            (G := Discrete.functor (fun i => F.obj (B i)))
            (fun i => F.map (f i.as)) ≫ c₂.ι)))) := by
  let α : Discrete.functor (fun i => F.obj (A i)) ⟶
      Discrete.functor (fun i => F.obj (B i)) :=
    Discrete.natTrans (fun i => F.map (f i.as))
  let q := hc₁.desc (Cocone.mk _ (α ≫ c₂.ι))
  have hq : (P.strictMap F).coproducts.{w} q := by
    apply (coproducts_iff _ q).mpr
    exact ⟨I, _, _, c₁, c₂, hc₁, hc₂, α, fun i => P.map_mem_strictMap F (f i.as) (hf i.as)⟩
  obtain ⟨X, Y, g, hg, hχ⟩ := (coproducts_strictMap_le_map P F) q hq
  exact ⟨X, Y, g, hg, hχ⟩

end MappedCoproductsTest

#print axioms CategoryTheory.MorphismProperty.coproducts_strictMap_le_map
#print axioms MappedCoproductsTest.originalImages_have_representative
#lint only unusedArguments in MathlibExt.CategoryTheory.MorphismProperty.MappedCoproducts
#lint only unusedArguments in MathlibExtTest.CategoryTheory.MorphismProperty.MappedCoproducts
