/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Actual partial attachments of the SAME finite original cell family

Each finite subfamily uses its entire original domain and target
coproducts and SAME original attaching maps. The actual partial pushout
retains the original root and every complete cell. Its genuine descender
and uniqueness keep arbitrary category object, Hom and cell universes.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} {A B : I → C} (g : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)

/-- The complete original domain coproduct of the SAME selected finite occurrences. -/
abbrev domain (s : Finset I) : C := ∐ (fun i : s => A i.1)

/-- The complete original target coproduct of the SAME selected finite occurrences. -/
abbrev target (s : Finset I) : C := ∐ (fun i : s => B i.1)

/-- The SAME entire original cell maps on the actual finite-subfamily coproducts. -/
abbrev coproductMap (s : Finset I) : domain (A := A) s ⟶ target (B := B) s :=
  Limits.Sigma.map (fun i : s => g i.1)

/-- The complete original attaching map on the actual selected domain coproduct. -/
abbrev attaching (s : Finset I) : domain (A := A) s ⟶ X := Sigma.desc (fun i : s => a i.1)

/-- The actual finite original attachment pushout retaining both entire original coproducts. -/
abbrev object (s : Finset I) : C := pushout (attaching a s) (coproductMap g s)

/-- The SAME entire original root inclusion of the actual partial pushout. -/
abbrev root (s : Finset I) : X ⟶ object g a s := pushout.inl _ _

/-- Every selected original cell has its SAME full inclusion into the actual partial attachment. -/
abbrev cell (s : Finset I) (i : s) : B i.1 ⟶ object g a s :=
  Sigma.ι (fun j : s => B j.1) i ≫ pushout.inr (attaching a s) (coproductMap g s)

/-- Each whole original cell boundary is glued by precisely the SAME original attaching map. -/
theorem boundary (s : Finset I) (i : s) : g i.1 ≫ cell g a s i = a i.1 ≫ root g a s := by
  calc
    g i.1 ≫ cell g a s i =
        Sigma.ι (fun j : s => A j.1) i ≫ coproductMap g s ≫
          pushout.inr (attaching a s) (coproductMap g s) :=
      (Sigma.ι_map_assoc (fun j : s => g j.1) i
        (pushout.inr (attaching a s) (coproductMap g s))).symm
    _ = Sigma.ι (fun j : s => A j.1) i ≫ attaching a s ≫ root g a s := by
      rw [← pushout.condition]
    _ = a i.1 ≫ root g a s := Sigma.ι_comp_desc_assoc _ i _

/-- The genuine original partial pushout is determined by the SAME root and all its complete
selected cells. -/
theorem hom_ext (s : Finset I) {Z : C} {f h : object g a s ⟶ Z}
    (hr : root g a s ≫ f = root g a s ≫ h)
    (hc : ∀ i : s, cell g a s i ≫ f = cell g a s i ≫ h) : f = h := by
  apply pushout.hom_ext hr
  apply Sigma.hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans ((hc i).trans (Category.assoc _ _ _))

/-- The SAME supplied root/cell maps give the actual full original partial-pushout descender. -/
def desc (s : Finset I) {Z : C} (r : X ⟶ Z) (b : ∀ i : s, B i.1 ⟶ Z)
    (hb : ∀ i : s, g i.1 ≫ b i = a i.1 ≫ r) : object g a s ⟶ Z :=
  pushout.desc r (Sigma.desc b) (by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
    exact (hb i).symm)

/-- The actual original descender retains the SAME full root map. -/
theorem root_desc (s : Finset I) {Z : C} (r : X ⟶ Z) (b : ∀ i : s, B i.1 ⟶ Z)
    (hb : ∀ i : s, g i.1 ≫ b i = a i.1 ≫ r) : root g a s ≫ desc g a s r b hb = r :=
  pushout.inl_desc _ _ _

/-- The actual original descender retains every SAME complete original cell map. -/
theorem cell_desc (s : Finset I) {Z : C} (r : X ⟶ Z) (b : ∀ i : s, B i.1 ⟶ Z)
    (hb : ∀ i : s, g i.1 ≫ b i = a i.1 ≫ r) (i : s) :
    cell g a s i ≫ desc g a s r b hb = b i := by
  change (Sigma.ι (fun j : s => B j.1) i ≫ pushout.inr _ _) ≫ pushout.desc r (Sigma.desc b) _ = _
  rw [Category.assoc, pushout.inr_desc, Sigma.ι_comp_desc]

/-- The original full descender is uniquely determined by exactly the SAME root and all
original cells. -/
theorem desc_unique (s : Finset I) {Z : C} (r : X ⟶ Z) (b : ∀ i : s, B i.1 ⟶ Z)
    (hb : ∀ i : s, g i.1 ≫ b i = a i.1 ≫ r) (f : object g a s ⟶ Z)
    (hr : root g a s ≫ f = r) (hc : ∀ i : s, cell g a s i ≫ f = b i) :
    f = desc g a s r b hb :=
  hom_ext g a s (hr.trans (root_desc g a s r b hb).symm)
    (fun i => (hc i).trans (cell_desc g a s r b hb i).symm)

end HomotopicalAlgebra.FinitePartialAttachment
