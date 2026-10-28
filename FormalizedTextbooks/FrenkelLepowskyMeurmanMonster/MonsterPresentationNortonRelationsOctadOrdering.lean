/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Identify finite octad position tables by strict order and membership. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates
public import Mathlib.Order.Preorder.Finite

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A strictly increasing table of eight octad positions is its actual ordered dictionary. -/
theorem monsterNortonOctadIndex_coordinate_of_strictMono (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (p : Fin 8 → Fin 24)
    (hm : ∀ k, (golayEncodedMask a.val).testBit (p k).val = true)
    (hs : StrictMono p) (k : Fin 8) :
    golayOctadCoordinate (monsterNortonOctadIndex a ha) k = p k := by
  let d := monsterNortonOctadIndex a ha
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)
  let e := t.orderIsoOfFin (golayOctad_support_card d)
  let v : Fin 8 → t := fun j => ⟨p j, by
    simp only [t, d, monsterNortonOctadIndex_label, golayMaskSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact hm j⟩
  let f : Fin 8 →o Fin 8 :=
    { toFun := fun j => e.symm (v j)
      monotone' := by
        intro i j hij
        apply e.symm.monotone
        change p i ≤ p j
        exact hs.monotone hij }
  have hf : Function.Injective f := by
    intro i j hij
    apply hs.injective
    have hv := e.symm.injective hij
    exact congrArg Subtype.val hv
  have hfk : f k = k := DFunLike.congr_fun (OrderHom.eq_id_of_injective f hf) k
  have hev : e k = v k :=
    (congrArg e hfk.symm).trans (e.apply_symm_apply (v k))
  exact congrArg Subtype.val hev

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
