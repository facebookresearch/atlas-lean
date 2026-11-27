/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Actual coequalizer splittings and their original commuting maps

The given actual idempotent is split using its chosen original
coequalizer with the identity. The inclusion and its retraction equation are
Mathlib's `splitEpiOfIdempotentOfIsColimitCofork` for that coequalizer, read
as a cofork of the identity and the idempotent. Every induced map is its
actual descender.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

namespace CategoryTheory.SmallObject.IdempotentCoequalizerSplit

open Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}
  (e : X ⟶ X) (he : e ≫ e = e) [HasCoequalizer e (𝟙 X)]

/-- The actual split object is the chosen coequalizer of the original e and identity. -/
abbrev obj : C := coequalizer e (𝟙 X)

/-- The actual original projection into this same selected coequalizer. -/
abbrev projection : X ⟶ obj e := coequalizer.π e (𝟙 X)

/-- The chosen coequalizer of `e` and `𝟙 X`, as a cofork of `𝟙 X` and `e`. -/
def cofork : Cofork (𝟙 X) e :=
  Cofork.ofπ (projection e) (coequalizer.condition e (𝟙 X)).symm

/-- That cofork is a colimit, by the universal property of the chosen coequalizer. -/
def isColimitCofork : IsColimit (cofork e) :=
  Cofork.IsColimit.mk _
    (fun s => coequalizer.desc s.π s.condition.symm)
    (fun s => coequalizer.π_desc s.π s.condition.symm)
    (fun s _ h => coequalizer.hom_ext (h.trans (coequalizer.π_desc s.π s.condition.symm).symm))

/-- Mathlib's splitting of the idempotent through the chosen coequalizer. -/
def split : SplitEpi (projection e) :=
  splitEpiOfIdempotentOfIsColimitCofork C he (isColimitCofork e)

/-- The actual inclusion back into X is the section of that splitting. -/
def inclusion : obj e ⟶ X := (split e he).section_

/-- The whole projection/inclusion composite retains the actual original idempotent. -/
theorem projection_inclusion : projection e ≫ inclusion e he = e :=
  Cofork.IsColimit.π_desc (isColimitCofork e)

/-- The original idempotent fixes the actual chosen projection. -/
theorem idempotent_projection : e ≫ projection e = projection e := by
  simpa only [Category.id_comp] using coequalizer.condition e (𝟙 X)

/-- The actual selected split maps form a retraction. -/
theorem inclusion_projection : inclusion e he ≫ projection e = 𝟙 (obj e) :=
  (split e he).id

/-- Actual coequalizer hom_ext retains this same projection function. -/
theorem hom_ext {W : C} {f g : obj e ⟶ W}
    (h : projection e ≫ f = projection e ≫ g) : f = g :=
  coequalizer.hom_ext h

variable (d : Y ⟶ Y) (hd : d ≫ d = d) [HasCoequalizer d (𝟙 Y)]
  (m : X ⟶ Y) (hm : e ≫ m = m ≫ d)

/-- A commuting original map descends through the same actual selected coequalizers. -/
def map : obj e ⟶ obj d :=
  coequalizer.desc (m ≫ projection d) (by
    rw [← Category.assoc, hm, Category.assoc, idempotent_projection, Category.id_comp])

/-- Every induced map retains precisely its actual original projection equation. -/
theorem projection_map : projection e ≫ map e d m hm = m ≫ projection d :=
  coequalizer.π_desc (m ≫ projection d) _

/-- Let `e : X ⟶ X` and `d : Y ⟶ Y` be idempotents with chosen
coequalizers of `(e, 𝟙 X)` and `(d, 𝟙 Y)`. For `m : X ⟶ Y` satisfying
`e ≫ m = m ≫ d`, the induced coequalizer map satisfies
`map e d m hm ≫ inclusion d hd = inclusion e he ≫ m`.
These inclusions are the sections of the chosen idempotent splittings. -/
theorem map_inclusion : map e d m hm ≫ inclusion d hd = inclusion e he ≫ m := by
  apply hom_ext e
  rw [← Category.assoc, projection_map, Category.assoc, projection_inclusion,
    ← Category.assoc, projection_inclusion]
  exact hm.symm

omit hd in
/-- Descending the original identity retains the actual selected split-object identity. -/
theorem map_id : map e e (𝟙 X) (by simp only [Category.comp_id, Category.id_comp]) =
    𝟙 (obj e) := by
  apply hom_ext e
  rw [projection_map, Category.id_comp, Category.comp_id]

variable (k : Z ⟶ Z) [HasCoequalizer k (𝟙 Z)] (n : Y ⟶ Z)
  (hn : d ≫ n = n ≫ k)

/-- Descending a composite retains both actual original selected induced maps. -/
theorem map_comp :
    map e d m hm ≫ map d k n hn =
      map e k (m ≫ n) (by rw [← Category.assoc, hm, Category.assoc, hn, Category.assoc]) := by
  apply hom_ext e
  rw [← Category.assoc, projection_map, Category.assoc, projection_map, projection_map,
    Category.assoc]

end CategoryTheory.SmallObject.IdempotentCoequalizerSplit
