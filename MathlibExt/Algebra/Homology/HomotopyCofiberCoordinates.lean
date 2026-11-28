/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomotopyCofiberProjection
public import MathlibExt.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Signed differential of a homotopy cofiber

Let C be preadditive, c a complex shape with decidable differential relation,
and φ:F → G have a homotopy cofiber. For c.Rel(i,j) and c.Rel(j,k),
assume the biproducts Fⱼ ⊞ Gᵢ and Fₖ ⊞ Gⱼ exist.
The canonical charts identify the cofiber differential from degree i to j
with the block map

(Fⱼ ⊞ Gᵢ) → (Fₖ ⊞ Gⱼ),
(x,y) ↦ (−d_F(j,k)(x), φⱼ(x)+d_G(i,j)(y)).

Thus the shifted-source differential has a negative sign, the cross term
is φⱼ, and the target differential has a positive sign. The statement
requires only these two degree biproducts.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Preadditive

namespace HomologicalComplex.homotopyCofiber

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G : HomologicalComplex C c} (φ : F ⟶ G) [HasHomotopyCofiber φ]

/-- Let C be preadditive, c a complex shape with decidable relation,
and φ:F → G have a homotopy cofiber. Suppose c.Rel(i,j), c.Rel(j,k),
and the biproducts Fⱼ ⊞ Gᵢ and Fₖ ⊞ Gⱼ exist.
Under the canonical cofiber term charts, the differential from i to j
is the block matrix
[[−d_F(j,k),0],[φⱼ,d_G(i,j)]]. -/
theorem XIsoBiprod_inv_d_hom (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)
    [HasBinaryBiproduct (F.X j) (G.X i)] [HasBinaryBiproduct (F.X k) (G.X j)] :
    (XIsoBiprod φ i j hij).inv ≫ (homotopyCofiber φ).d i j ≫
        (XIsoBiprod φ j k hjk).hom =
      biprod.desc (biprod.lift (-F.d j k) (φ.f j))
        (biprod.lift 0 (G.d i j)) := by
  apply biprod.hom_ext _ _
  · simp only [Category.assoc, biprod.desc_comp, biprod.lift_fst]
    change (XIsoBiprod φ i j hij).inv ≫ (d φ i j ≫ fstX φ j k hjk) =
      biprod.desc (-F.d j k) 0
    rw [d_fstX φ i j k hij hjk]
    simp only [fstX, Preadditive.comp_neg,
      biprod.desc_eq, comp_zero, add_zero, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  · simp only [Category.assoc, biprod.desc_comp, biprod.lift_snd]
    rw [← sndX_eq_XIsoBiprod φ j k hjk]
    change (XIsoBiprod φ i j hij).inv ≫ (d φ i j ≫ sndX φ j) =
      biprod.desc (φ.f j) (G.d i j)
    rw [d_sndX φ i j hij, sndX_eq_XIsoBiprod φ i j hij]
    simp only [fstX, biprod.desc_eq, Preadditive.comp_add,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end HomologicalComplex.homotopyCofiber
