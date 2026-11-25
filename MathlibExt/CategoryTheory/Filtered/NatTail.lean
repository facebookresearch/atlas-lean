/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.CategoryTheory.Filtered.Final

/-!
# Natural-number tails and Type colimits

The natural-number index shift is final. Its Type-colimit comparison keeps
the selected colimit cocones, both full maps, every shifted leg and both
naturality squares for arbitrary diagram transformations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.NatTail

/-- The actual original Nat shift keeps every ordered-index map. -/
def tailFunctor (r : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ => r + n) from fun _ _ h => Nat.add_le_add_left h r).functor

/-- Every full actual source index is the original shifted Nat index. -/
theorem tailFunctor_obj (r n : ℕ) : (tailFunctor r).obj n = r + n := rfl

/-- Every actual shifted index map retains its complete original order proof. -/
theorem tailFunctor_map (r : ℕ) {i j : ℕ} (f : i ⟶ j) :
    (tailFunctor r).map f = homOfLE (Nat.add_le_add_left (leOfHom f) r) := rfl

/-- The SAME original positive-tail shift is genuinely final at every finite offset. -/
theorem tailFunctor_final (r : ℕ) : (tailFunctor r).Final := by
  apply (Monotone.final_functor_iff
    (show Monotone (fun n : ℕ => r + n) from fun _ _ h => Nat.add_le_add_left h r)).mpr
  intro n
  exact ⟨n, Nat.le_add_left n r⟩

/-- The complete actual Type tail has the same selected original full colimit cocone. -/
def typeTailCocone (D : ℕ ⥤ Type v) (r : ℕ) : Cocone (tailFunctor r ⋙ D) :=
  (colimit.cocone D).whisker (tailFunctor r)

/-- Genuine Nat tail finality gives the original whole Type cocone's colimit property. -/
def typeTailIsColimit (D : ℕ ⥤ Type v) (r : ℕ) : IsColimit (typeTailCocone D r) := by
  let _ : (tailFunctor r).Final := tailFunctor_final r
  exact (Functor.Final.isColimitWhiskerEquiv (tailFunctor r) (colimit.cocone D)).symm
    (colimit.isColimit D)

/-- Both Type tail functions come from the actual original selected colimit and full finality. -/
def typeTailIso (D : ℕ ⥤ Type v) (r : ℕ) :
    colimit (tailFunctor r ⋙ D) ≅ colimit D :=
  by
    let _ : (tailFunctor r).Final := tailFunctor_final r
    exact Functor.Final.colimitIso (tailFunctor r) D

/-- The full forward Type tail function is the original actual cocone descent. -/
theorem typeTailIso_hom (D : ℕ ⥤ Type v) (r : ℕ) :
    (typeTailIso D r).hom = (colimit.isColimit (tailFunctor r ⋙ D)).desc (typeTailCocone D r) :=
  rfl

/-- The full inverse Type tail function is the actual original final cocone descent. -/
theorem typeTailIso_inv (D : ℕ ⥤ Type v) (r : ℕ) :
    (typeTailIso D r).inv = (typeTailIsColimit D r).desc (colimit.cocone (tailFunctor r ⋙ D)) :=
  by
    let _ : (tailFunctor r).Final := tailFunctor_final r
    apply (typeTailIsColimit D r).hom_ext
    intro n
    exact (Functor.Final.ι_colimitIso_inv (tailFunctor r) D n).trans
      ((typeTailIsColimit D r).fac (colimit.cocone (tailFunctor r ⋙ D)) n).symm

/-- Every entire forward Type tail leg keeps the literal selected predecessor index. -/
theorem typeTailIso_hom_ι (D : ℕ ⥤ Type v) (r n : ℕ) :
    colimit.ι (tailFunctor r ⋙ D) n ≫ (typeTailIso D r).hom = colimit.ι D (r + n) :=
  by
    let _ : (tailFunctor r).Final := tailFunctor_final r
    exact Functor.Final.ι_colimitIso_hom (tailFunctor r) D n

/-- Every entire inverse Type tail leg keeps the same original shifted Type colimit. -/
theorem typeTailIso_inv_ι (D : ℕ ⥤ Type v) (r n : ℕ) :
    colimit.ι D (r + n) ≫ (typeTailIso D r).inv = colimit.ι (tailFunctor r ⋙ D) n :=
  by
    let _ : (tailFunctor r).Final := tailFunctor_final r
    exact Functor.Final.ι_colimitIso_inv (tailFunctor r) D n

/-- Every full actual diagram map retains the original forward Type tail square. -/
theorem typeTailIso_hom_naturality (r : ℕ) {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    colim.map (Functor.whiskerLeft (tailFunctor r) a) ≫ (typeTailIso E r).hom =
      (typeTailIso D r).hom ≫ colim.map a := by
  apply colimit.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro q
  let t := Functor.whiskerLeft (tailFunctor r) a
  have h := ConcreteCategory.congr_hom (colimit.ι_map t n) q
  have he := ConcreteCategory.congr_hom (typeTailIso_hom_ι E r n) (a.app (r + n) q)
  have hd := ConcreteCategory.congr_hom (typeTailIso_hom_ι D r n) q
  have hm := ConcreteCategory.congr_hom (colimit.ι_map a (r + n)) q
  change (typeTailIso E r).hom (colim.map t (colimit.ι (tailFunctor r ⋙ D) n q)) =
    colim.map a ((typeTailIso D r).hom (colimit.ι (tailFunctor r ⋙ D) n q))
  exact (congrArg (typeTailIso E r).hom h).trans
    (he.trans (hm.symm.trans (congrArg (colim.map a) hd.symm)))

/-- The entire inverse Type tail square follows from the same actual two inverse maps. -/
theorem typeTailIso_inv_naturality (r : ℕ) {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    colim.map a ≫ (typeTailIso E r).inv =
      (typeTailIso D r).inv ≫ colim.map (Functor.whiskerLeft (tailFunctor r) a) :=
  (CommSq.vert_inv (g := typeTailIso D r) (h := typeTailIso E r)
    ⟨typeTailIso_hom_naturality r a⟩).w

/-- The full Type tail diagram functor retains every actual original input transformation. -/
def typeTailDiagramFunctor (r : ℕ) : (ℕ ⥤ Type v) ⥤ (ℕ ⥤ Type v) :=
  (Functor.whiskeringLeft ℕ ℕ (Type v)).obj (tailFunctor r)

/-- Both full Type tail colimit functions are naturally the original selected colimit. -/
def typeTailColimitNatIso (r : ℕ) : typeTailDiagramFunctor.{v} r ⋙ colim ≅ colim :=
  NatIso.ofComponents (fun D => typeTailIso D r) (fun a => typeTailIso_hom_naturality r a)

/-- The whole Type tail component family keeps the actual same complete Iso record. -/
theorem typeTailColimitNatIso_app (r : ℕ) (D : ℕ ⥤ Type v) :
    (typeTailColimitNatIso r).app D = typeTailIso D r := rfl

end CategoryTheory.NatTail
