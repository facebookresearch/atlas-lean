/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory

/-!
# Actual enriched Hom transport through isomorphic Hom maps

An actual enriched functor whose supplied Hom maps are isomorphisms lets
another actual enriched functor act on those same target Hom objects.
The transported maps preserve the whole original identity and
composition. The isomorphism hypotheses concern actual Hom maps; no
transported-functor or coherence outcome is supplied as data.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.HomTransport
variable {A B C : Carrier.{u}} (E : A ⟶ B) (F : A ⟶ C)

/-- The actual whole Hom map transported through the inverse of the supplied original Hom
isomorphism. -/
def map (a b : A) [IsIso (E.map a b)] :
    (E.obj a ⟶[SSet.{u}] E.obj b) ⟶ (F.obj a ⟶[SSet.{u}] F.obj b) :=
  inv (E.map a b) ≫ F.map a b

/-- Transport reads back the entire original enriched functor Hom map. -/
theorem map_readback (a b : A) [IsIso (E.map a b)] : E.map a b ≫ map E F a b = F.map a b := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ F.map a b) (IsIso.hom_inv_id (E.map a b))).trans (Category.id_comp _))

/-- The transported Hom map preserves the original enriched identity at that supplied object. -/
theorem map_id (a : A) [IsIso (E.map a a)] :
    eId SSet.{u} (E.obj a) ≫ map E F a a = eId SSet.{u} (F.obj a) := by
  exact (congrArg (fun h => h ≫ map E F a a) (E.map_id a).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun h => eId SSet.{u} a ≫ h) (map_readback E F a a)).trans (F.map_id a)))

/-- The transported maps preserve the actual whole enriched composition at the same three
supplied objects. -/
theorem map_comp (a b c : A) [IsIso (E.map a b)] [IsIso (E.map b c)] [IsIso (E.map a c)] :
    eComp SSet.{u} (E.obj a) (E.obj b) (E.obj c) ≫ map E F a c =
      (map E F a b ⊗ₘ map E F b c) ≫ eComp SSet.{u} (F.obj a) (F.obj b) (F.obj c) := by
  apply (cancel_epi (E.map a b ⊗ₘ E.map b c)).mp
  have hL : (E.map a b ⊗ₘ E.map b c) ≫
      (eComp SSet.{u} (E.obj a) (E.obj b) (E.obj c) ≫ map E F a c) =
      eComp SSet.{u} a b c ≫ F.map a c :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ map E F a c) (E.map_comp a b c).symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun h => eComp SSet.{u} a b c ≫
          h) (map_readback E F a c))))
  have hT : (E.map a b ⊗ₘ E.map b c) ≫ (map E F a b ⊗ₘ map E F b c) =
      F.map a b ⊗ₘ F.map b c :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (map_readback E F a b) (map_readback E F b c))
  have hR : (E.map a b ⊗ₘ E.map b c) ≫
      ((map E F a b ⊗ₘ map E F b c) ≫ eComp SSet.{u} (F.obj a) (F.obj b) (F.obj c)) =
      eComp SSet.{u} a b c ≫ F.map a c :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ eComp SSet.{u} (F.obj a) (F.obj b) (F.obj c)) hT).trans
        (F.map_comp a b c).symm)
  exact hL.trans hR.symm

end CategoryTheory.SimplicialEnrichment.HomTransport
