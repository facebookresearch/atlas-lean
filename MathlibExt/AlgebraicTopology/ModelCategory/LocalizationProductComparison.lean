/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Literal product and terminal readbacks in model localization

The proved original fibrant product cone identifies the actual product
comparison map with a genuine isomorphism. Both full projection legs
and both-variable naturality retain the SAME original maps. The original
terminal object gives its actual terminal comparison isomorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v uH vH
open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.ModelLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]
  [HasBinaryProducts H]

/-- The actual original limiting cone identifies the SAME projected fibrant product with the
localized product. -/
def productIso (Y Z : C) [IsFibrant Y] [IsFibrant Z] : Q.obj (Y ⨯ Z) ≅ Q.obj Y ⨯ Q.obj Z where
  hom := Limits.prodComparison Q Y Z
  inv := productLift Q Y Z prod.fst prod.snd
  hom_inv_id := by
    apply product_hom_ext Q Y Z
    · rw [Category.assoc, productLift_fst, Limits.prodComparison_fst, Category.id_comp]
    · rw [Category.assoc, productLift_snd, Limits.prodComparison_snd, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, Limits.prodComparison_fst, productLift_fst, Category.id_comp]
    · rw [Category.assoc, Limits.prodComparison_snd, productLift_snd, Category.id_comp]

/-- The entire first original product projection is the first leg of the SAME actual product
isomorphism. -/
@[reassoc] theorem productIso_hom_fst (Y Z : C) [IsFibrant Y] [IsFibrant Z] :
    (productIso Q Y Z).hom ≫ prod.fst = Q.map (prod.fst : Y ⨯ Z ⟶ Y) :=
  Limits.prodComparison_fst Q Y Z

/-- The entire second original product projection is the second leg of the SAME actual product
isomorphism. -/
@[reassoc] theorem productIso_hom_snd (Y Z : C) [IsFibrant Y] [IsFibrant Z] :
    (productIso Q Y Z).hom ≫ prod.snd = Q.map (prod.snd : Y ⨯ Z ⟶ Z) :=
  Limits.prodComparison_snd Q Y Z

/-- The SAME complete isomorphism map is the literal original product comparison. -/
theorem productIso_hom (Y Z : C) [IsFibrant Y] [IsFibrant Z] :
    (productIso Q Y Z).hom = Limits.prodComparison Q Y Z := rfl

/-- The literal original product comparison is invertible at every genuine fibrant pair. -/
theorem prodComparison_isIso_of_fibrant (Y Z : C) [IsFibrant Y] [IsFibrant Z] :
    IsIso (Limits.prodComparison Q Y Z) := by
  rw [← productIso_hom Q Y Z]
  infer_instance

/-- Both original target maps retain the full SAME product-comparison naturality square. -/
@[reassoc] theorem productIso_hom_natural {Y Y' Z Z' : C}
    [IsFibrant Y] [IsFibrant Y'] [IsFibrant Z] [IsFibrant Z'] (f : Y ⟶ Y') (g : Z ⟶ Z') :
    Q.map (prod.map f g) ≫ (productIso Q Y' Z').hom =
      (productIso Q Y Z).hom ≫ prod.map (Q.map f) (Q.map g) := by
  rw [productIso_hom, productIso_hom]
  exact Limits.prodComparison_natural Q f g

/-- The complete inverse product maps preserve the SAME original two-variable naturality square. -/
@[reassoc] theorem productIso_inv_natural {Y Y' Z Z' : C}
    [IsFibrant Y] [IsFibrant Y'] [IsFibrant Z] [IsFibrant Z'] (f : Y ⟶ Y') (g : Z ⟶ Z') :
    prod.map (Q.map f) (Q.map g) ≫ (productIso Q Y' Z').inv =
      (productIso Q Y Z).inv ≫ Q.map (prod.map f g) := by
  apply (cancel_epi (productIso Q Y Z).hom).mp
  calc
    _ = ((productIso Q Y Z).hom ≫ prod.map (Q.map f) (Q.map g)) ≫
        (productIso Q Y' Z').inv := (Category.assoc _ _ _).symm
    _ = (Q.map (prod.map f g) ≫ (productIso Q Y' Z').hom) ≫
        (productIso Q Y' Z').inv :=
      congrArg (fun k => k ≫ (productIso Q Y' Z').inv) (productIso_hom_natural Q f g).symm
    _ = Q.map (prod.map f g) := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable [HasTerminal H]

omit [HasBinaryProducts H] in
/-- The SAME actual projected original terminal object is the chosen localized terminal object. -/
def terminalIso : Q.obj (⊤_ C) ≅ ⊤_ H :=
  (terminalIsTerminal Q).uniqueUpToIso CategoryTheory.Limits.terminalIsTerminal

omit [HasBinaryProducts H] in
/-- The entire terminal isomorphism map is the literal original terminal comparison. -/
theorem terminalIso_hom : (terminalIso Q).hom = Limits.terminalComparison Q := Subsingleton.elim _ _

omit [HasBinaryProducts H] in
/-- The literal original terminal comparison is genuinely invertible in the given model
localization. -/
theorem terminalComparison_isIso : IsIso (Limits.terminalComparison Q) := by
  rw [← terminalIso_hom Q]
  infer_instance

end HomotopicalAlgebra.ModelLocalization
