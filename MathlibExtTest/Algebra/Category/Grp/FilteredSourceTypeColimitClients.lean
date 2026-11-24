/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.Algebra.Category.Grp.FilteredSourceTypeColimit

/-!
# Public filtered group and Type colimit clients

Use the actual underlying group functor as the source diagram, checking the
original colimit legs, naturality, and isomorphism transport on diagram maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v

open CategoryTheory Limits
open GrpCat.FilteredColimits

namespace MathlibExtTest.FilteredSourceTypeColimitClients

/-- The public source comparison carries the chosen Type leg to the original group leg. -/
theorem source_leg (D : ℕ ⥤ GrpCat.{v}) (n : ℕ) :
    colimit.ι (D ⋙ forget GrpCat.{v}) n ≫
        (sourceTypeColimitIso (𝟭 GrpCat.{v}) (forget GrpCat.{v})
          (Functor.leftUnitor (forget GrpCat.{v})) D).hom =
      (forget GrpCat.{v}).map ((colimitCocone (D ⋙ 𝟭 GrpCat.{v})).ι.app n) := by
  simpa using sourceTypeColimitIso_ι_hom (𝟭 GrpCat.{v}) (forget GrpCat.{v})
    (Functor.leftUnitor (forget GrpCat.{v})) D n

/-- An arbitrary diagram-map square retains its entire public colimit comparison. -/
theorem input_square {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E) :
    colim.map (Functor.whiskerRight α (forget GrpCat.{v})) ≫
        (sourceTypeColimitIso (𝟭 GrpCat.{v}) (forget GrpCat.{v})
          (Functor.leftUnitor (forget GrpCat.{v})) E).hom =
      (sourceTypeColimitIso (𝟭 GrpCat.{v}) (forget GrpCat.{v})
          (Functor.leftUnitor (forget GrpCat.{v})) D).hom ≫
        (forget GrpCat.{v}).map
          ((colimitCoconeIsColimit (D ⋙ 𝟭 GrpCat.{v})).map
            (colimitCocone (E ⋙ 𝟭 GrpCat.{v})) (Functor.whiskerRight α (𝟭 GrpCat.{v}))) :=
  sourceTypeColimitIso_hom_naturality (𝟭 GrpCat.{v}) (forget GrpCat.{v})
    (Functor.leftUnitor (forget GrpCat.{v})) α

/-- A genuine group-colimit isomorphism is transported to the complete underlying Type map. -/
theorem iso_transport {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E)
    [IsIso ((colimitCoconeIsColimit (D ⋙ 𝟭 GrpCat.{v})).map
      (colimitCocone (E ⋙ 𝟭 GrpCat.{v})) (Functor.whiskerRight α (𝟭 GrpCat.{v})))] :
    IsIso (colim.map (Functor.whiskerRight α (forget GrpCat.{v}))) :=
  sourceTypeColimitMap_isIso (𝟭 GrpCat.{v}) (forget GrpCat.{v})
    (Functor.leftUnitor (forget GrpCat.{v})) α

end MathlibExtTest.FilteredSourceTypeColimitClients
