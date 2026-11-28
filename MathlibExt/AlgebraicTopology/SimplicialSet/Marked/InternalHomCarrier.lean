/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterForget
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingNaturality

/-!
# The original marked internal-Hom carrier

Its underlying simplicial set is the actual minimally parameter-marked
mapping complex. An edge is marked precisely when its same entire prism
preserves the maximal parameter marking. Original pre- and postcomposition
preserve this condition. No marked model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The actual marked function carrier retains its entire original minimal mapping complex. -/
def internalHom (X Y : Marked.{u}) : Marked.{u} where
  toSSet := mappingComplex .minimal X Y
  marking := Set.range ((mappingComplexMaxToMin X Y).app (op ⦋1⦌))
  degenerate_mem v := by
    let w := mappingZeroPromote X Y v
    refine ⟨(mappingComplex .maximal X Y).σ (0 : Fin 1) w, ?_⟩
    have h := NatTrans.naturality_apply (mappingComplexMaxToMin X Y)
      (SimplexCategory.σ (0 : Fin 1)).op w
    change (mappingComplexMaxToMin X Y).app (op ⦋1⦌)
      ((mappingComplex .maximal X Y).σ (0 : Fin 1) w) =
        (mappingComplex .minimal X Y).σ (0 : Fin 1)
          ((mappingComplexMaxToMin X Y).app (op ⦋0⦌) w) at h
    rw [h, mappingComplexMaxToMin_zero_promote]

/-- The original internal-Hom vertices are exactly the same actual marked maps. -/
def internalHomZeroEquiv (X Y : Marked.{u}) : (internalHom X Y).toSSet _⦋0⦌ ≃ (X ⟶ Y) :=
  mappingComplexZeroEquiv .minimal X Y

/-- An internal-Hom edge is marked precisely when its same prism has maximal parameter marking. -/
theorem internalHom_marking_iff (X Y : Marked.{u})
    (e : (mappingComplex .minimal X Y) _⦋1⦌) :
    e ∈ (internalHom X Y).marking ↔
      ∃ f : (mappingComplex .maximal X Y) _⦋1⦌,
        (mappingComplexMaxToMin X Y).app (op ⦋1⦌) f = e := Iff.rfl

/-- The original target map gives its actual marked internal-Hom postcomposition. -/
def internalHomPost (X : Marked.{u}) {Y Z : Marked.{u}} (p : Y ⟶ Z) :
    internalHom X Y ⟶ internalHom X Z where
  hom := mappingComplexPost .minimal X p
  preserve {e} he := by
    obtain ⟨f, rfl⟩ := he
    refine ⟨(mappingComplexPost .maximal X p).app (op ⦋1⦌) f, ?_⟩
    exact (congrArg (fun q => q.app (op ⦋1⦌) f) (mappingComplexMaxToMin_post X p)).symm

/-- The original source map gives the marked contravariant internal-Hom map. -/
def internalHomPre {X X' : Marked.{u}} (p : X' ⟶ X) (Y : Marked.{u}) :
    internalHom X Y ⟶ internalHom X' Y where
  hom := mappingComplexPre .minimal p Y
  preserve {e} he := by
    obtain ⟨f, rfl⟩ := he
    refine ⟨(mappingComplexPre .maximal p Y).app (op ⦋1⦌) f, ?_⟩
    exact (congrArg (fun q => q.app (op ⦋1⦌) f) (mappingComplexMaxToMin_pre p Y)).symm

/-- Postcomposition on the actual marked internal-Hom carriers is a genuine functor. -/
def internalHomFunctor (X : Marked.{u}) : Marked.{u} ⥤ Marked.{u} where
  obj Y := internalHom X Y
  map p := internalHomPost X p
  map_id Y := Hom.ext (mappingComplexPost_id .minimal X Y)
  map_comp p q := Hom.ext (mappingComplexPost_comp .minimal X p q)

end SSet.Marked
