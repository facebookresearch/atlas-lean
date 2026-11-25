/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail

/-!
# The actual stage-zero comparison for the SAME Nat group quotient

Genuine Iso successor maps make every actual zero-to-stage map an Iso.
Their actual inverses form a full cocone at the SAME original stage
zero. Its complete universal property uses each competing cocone's
original zero leg. The resulting chosen Group colimit Iso has ENTIRE
hom equal to the actual original zero leg, and ENTIRE inverse equal
to the genuine quotient descent. All finite maps and input diagrams
are retained. Native callers must prove their original successor Isos;
no native stable-model, telescope, or colimit comparison law is data.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v uC vC
open CategoryTheory CategoryTheory.Limits

private theorem originalInverseTransition
    {C : Type uC} [Category.{vC} C] {A B D : C}
    (a : A ⟶ B) (b : A ⟶ D) (f : B ⟶ D) [IsIso a] [IsIso b]
    (h : a ≫ f = b) : f ≫ inv b = inv a := by
  apply (cancel_mono b).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← h,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

private theorem originalInverseIsoSquare
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (e : A ≅ D) (f : B ≅ E) (a : A ⟶ B) (b : D ⟶ E)
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

namespace GrpCat.FilteredColimits.ConstantSource

/-- The actual original zero-to-stage index map keeps the SAME Nat order category. -/
def zeroTo (n : ℕ) : (0 : ℕ) ⟶ n := homOfLE (Nat.zero_le n)

/-- The actual original zero-to-zero index map is the SAME identity map. -/
theorem zeroTo_zero : zeroTo 0 = 𝟙 (0 : ℕ) := Subsingleton.elim _ _

/-- Every original finite index map retains the actual original zero-to-stage association. -/
theorem zeroTo_comp (i j : ℕ) (f : i ⟶ j) : zeroTo i ≫ f = zeroTo j :=
  Subsingleton.elim _ _

/-- Proved original successor Isos make EVERY actual original zero-to-stage map an Iso. -/
theorem map_zeroTo_isIso (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (homOfLE (Nat.le_succ n)))) (n : ℕ) : IsIso (D.map (zeroTo n)) := by
  induction n with
  | zero =>
    rw [zeroTo_zero, D.map_id]
    infer_instance
  | succ n hn =>
    let _ : IsIso (D.map (zeroTo n)) := hn
    let _ : IsIso (D.map (homOfLE (Nat.le_succ n))) := h n
    have hm : D.map (zeroTo (n + 1)) =
        D.map (zeroTo n) ≫ D.map (homOfLE (Nat.le_succ n)) :=
      (D.congr_map (zeroTo_comp n (n + 1) (homOfLE (Nat.le_succ n)))).symm.trans
        (D.map_comp _ _)
    rw [hm]
    infer_instance

/-- The complete original zero-to-stage inverse is the actual inverse of that SAME map. -/
def zeroMapInverse (D : ℕ ⥤ GrpCat.{v}) (h : ∀ n, IsIso (D.map (zeroTo n))) (n : ℕ) :
    D.obj n ⟶ D.obj 0 := by
  let _ : IsIso (D.map (zeroTo n)) := h n
  exact inv (D.map (zeroTo n))

/-- The entire actual original inverse followed by its map is the SAME target identity. -/
theorem zeroMapInverse_hom_id (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) (n : ℕ) :
    zeroMapInverse D h n ≫ D.map (zeroTo n) = 𝟙 (D.obj n) := by
  let _ : IsIso (D.map (zeroTo n)) := h n
  exact IsIso.inv_hom_id _

/-- The entire actual original map followed by its inverse is the SAME source identity. -/
theorem zeroMapInverse_id_hom (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) (n : ℕ) :
    D.map (zeroTo n) ≫ zeroMapInverse D h n = 𝟙 (D.obj 0) := by
  let _ : IsIso (D.map (zeroTo n)) := h n
  exact IsIso.hom_inv_id _

/-- The full actual original zero-stage inverse is precisely the original identity function. -/
theorem zeroMapInverse_zero (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) : zeroMapInverse D h 0 = 𝟙 (D.obj 0) := by
  have hm : D.map (zeroTo 0) = 𝟙 (D.obj 0) := (D.congr_map zeroTo_zero).trans (D.map_id 0)
  exact (Category.comp_id (zeroMapInverse D h 0)).symm.trans
    ((congrArg (fun f => zeroMapInverse D h 0 ≫ f) hm).symm.trans
      (zeroMapInverse_hom_id D h 0))

/-- The complete actual original inverse maps form a cocone at the SAME original stage zero. -/
def constantSourceCocone (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) : Cocone D where
  pt := D.obj 0
  ι :=
    { app := zeroMapInverse D h
      naturality := fun {i j} f => by
        let _ : IsIso (D.map (zeroTo i)) := h i
        let _ : IsIso (D.map (zeroTo j)) := h j
        have hm : D.map (zeroTo i) ≫ D.map f = D.map (zeroTo j) :=
          (D.map_comp _ _).symm.trans (D.congr_map (zeroTo_comp i j f))
        exact (originalInverseTransition (D.map (zeroTo i)) (D.map (zeroTo j))
          (D.map f) hm).trans (Category.comp_id _).symm }

/-- The actual original inverse cocone has the full genuine stage-zero universal property. -/
def constantSourceCoconeIsColimit (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) : IsColimit (constantSourceCocone D h) where
  desc c := c.ι.app 0
  fac c n := by
    have hw := c.w (zeroTo n)
    have hi := zeroMapInverse_hom_id D h n
    exact (congrArg (fun f => zeroMapInverse D h n ≫ f) hw.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ c.ι.app n) hi).trans (Category.id_comp _)))
  uniq c m hm :=
    (Category.id_comp m).symm.trans
      ((congrArg (fun f => f ≫ m) (zeroMapInverse_zero D h).symm).trans (hm 0))

/-- BOTH full actual stage-zero colimit Iso functions use the SAME original group quotient. -/
def constantSourceColimitIso (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) : D.obj 0 ≅ GrpCat.FilteredColimits.colimit D :=
  (constantSourceCoconeIsColimit D h).coconePointUniqueUpToIso
    (GrpCat.FilteredColimits.colimitCoconeIsColimit D)

/-- The ENTIRE actual source-colimit Iso hom is the SAME original chosen stage-zero leg. -/
theorem constantSourceColimitIso_hom (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) :
    (constantSourceColimitIso D h).hom = (GrpCat.FilteredColimits.colimitCocone D).ι.app 0 := rfl

/-- The ENTIRE inverse is the genuine original quotient descent to the original zero stage. -/
theorem constantSourceColimitIso_inv (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) :
    (constantSourceColimitIso D h).inv =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit D).desc (constantSourceCocone D h) := rfl

/-- Every original chosen quotient leg retains its actual original zero-to-stage inverse. -/
theorem constantSourceColimitIso_inv_leg (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) (n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone D).ι.app n ≫ (constantSourceColimitIso D h).inv =
      zeroMapInverse D h n :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit D).fac (constantSourceCocone D h) n

/-- The SAME actual original chosen stage-zero colimit leg is genuinely an Iso. -/
theorem constantSource_zero_leg_isIso (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) :
    IsIso ((GrpCat.FilteredColimits.colimitCocone D).ι.app 0) :=
  (constantSourceColimitIso_hom D h) ▸ (constantSourceColimitIso D h).isIso_hom

/-- Every full original diagram map preserves the ENTIRE actual source-colimit hom function. -/
theorem constantSourceColimitIso_hom_naturality {D E : ℕ ⥤ GrpCat.{v}}
    (hD : ∀ n, IsIso (D.map (zeroTo n))) (hE : ∀ n, IsIso (E.map (zeroTo n))) (a : D ⟶ E) :
    a.app 0 ≫ (constantSourceColimitIso E hE).hom =
      (constantSourceColimitIso D hD).hom ≫ ((GrpCat.FilteredColimits.colimitCoconeIsColimit D).map
        (GrpCat.FilteredColimits.colimitCocone E) a) :=
  ((GrpCat.FilteredColimits.colimitCoconeIsColimit D).ι_map
    (GrpCat.FilteredColimits.colimitCocone E) a 0).symm

/-- Every full original diagram map preserves the ENTIRE actual source-colimit inv function. -/
theorem constantSourceColimitIso_inv_naturality {D E : ℕ ⥤ GrpCat.{v}}
    (hD : ∀ n, IsIso (D.map (zeroTo n))) (hE : ∀ n, IsIso (E.map (zeroTo n))) (a : D ⟶ E) :
    ((GrpCat.FilteredColimits.colimitCoconeIsColimit D).map
        (GrpCat.FilteredColimits.colimitCocone E) a) ≫ (constantSourceColimitIso E hE).inv =
      (constantSourceColimitIso D hD).inv ≫ a.app 0 :=
  originalInverseIsoSquare (constantSourceColimitIso D hD) (constantSourceColimitIso E hE)
    (a.app 0) (((GrpCat.FilteredColimits.colimitCoconeIsColimit D).map
        (GrpCat.FilteredColimits.colimitCocone E) a))
    (constantSourceColimitIso_hom_naturality hD hE a)

end GrpCat.FilteredColimits.ConstantSource
