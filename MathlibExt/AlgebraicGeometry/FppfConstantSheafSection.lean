/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit.lean`
and
`P2M/Sol/S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Int.Cast.Lemmas

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A morphism from an fppf sheaf of abelian groups to the constant sheaf
on `ULift ℤ` splits as soon as one preimage of `1` exists over `Spec ℤ`:
the element over the terminal scheme determines a section through the
constant-sheaf adjunction, since every integral multiple is forced. -/
theorem fppf_exists_section_of_map_eq_unit
    {E : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
    (g : E ⟶ (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
      (.of (ULift.{1} ℤ)))
    (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
    (he : g.hom.app (op (Spec (.of ℤ))) e =
      (constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
          specZIsTerminal).unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)) :
    ∃ s : (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by
  let adj := constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
    specZIsTerminal
  let φ : (AddCommGrpCat.of (ULift.{1} ℤ)) ⟶ E.obj.obj (op (Spec (.of ℤ))) :=
    AddCommGrpCat.ofHom
      ((zmultiplesHom (E.obj.obj (op (Spec (.of ℤ)))) e).comp
        AddEquiv.ulift.toAddMonoidHom)
  have hφ : φ (ULift.up 1) = e := by
    change (AddEquiv.ulift (ULift.up (1 : ℤ))) • e = e
    exact one_zsmul e
  refine ⟨(adj.homEquiv _ E).symm φ, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_id]
  ext x
  obtain ⟨n⟩ := x
  have hx : (ULift.up n : ULift.{1} ℤ) = n • ULift.up 1 := by
    ext
    simp
  rw [hx, map_zsmul, map_zsmul]
  congr 1
  change g.hom.app (op (Spec (.of ℤ))) (φ (ULift.up 1)) =
    adj.unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)
  rw [hφ]
  exact he

end AlgebraicGeometry
