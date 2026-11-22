/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFlagEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjacentHom

/-!
# The literal degree-zero coherent flag isomorphism

The original degree-zero flag map identifies the standard zero simplex
with the actual adjacent zero-to-one coherent Hom. Both endpoints and
its unique whole original path are retained; no mapping-space or Kan
comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ZeroFlagIso
open HomFlagEvaluation PathLastMaximum AdjacentHom

private theorem path_unique (p q : LastPath.{u} (0 : Fin 1)) : p = q :=
  (path_eq (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide)
    (fun k _ _ => finTwo_vertices k) p).trans
    (path_eq (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide)
      (fun k _ _ => finTwo_vertices k) q).symm

/-- The actual original degree-zero flag map is an isomorphism on the entire simplicial Hom. -/
theorem flag_isIso : IsIso (flagMap.{u} (n := 0)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    induction q using Opposite.rec with
    | _ q =>
      induction q using SimplexCategory.rec with
      | _ d =>
        apply SSet.stdSimplex.ext
        intro j
        exact @Subsingleton.elim (Fin 1) inferInstance _ _
  · intro p
    let z : (Δ[0] : SSet.{u}).obj q := SSet.stdSimplex.objEquiv.symm (SimplexCategory.const q.unop ⦋0⦌ 0)
    refine ⟨z, ?_⟩
    refine Functor.ext (fun j => path_unique _ (p.obj j)) ?_
    intro j k f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The whole actual degree-zero flag isomorphism, with the original flag map as forward map. -/
def iso : (Δ[0] : SSet.{u}) ≅ nerve (LastPath.{u} (0 : Fin 1)) := by
  letI := flag_isIso.{u}
  exact asIso (flagMap.{u} (n := 0))

/-- The whole forward map remains exactly the supplied original flag. -/
theorem iso_hom : iso.{u}.hom = flagMap.{u} (n := 0) := rfl

end CategoryTheory.CoherentRealization.ZeroFlagIso
