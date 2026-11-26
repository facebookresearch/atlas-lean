/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadOuterOperator

/-!
# Original epimorphic bead operators

The native ordinal epimorphism retains both original endpoints. Its
whole original direct-image map retains the entire full terminal flag,
with the actual target vertex range proved from native surjectivity.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.OuterOperator

open TerminalFlag

variable {n m : ℕ}

/-- Every actual native epi sends the original zero endpoint to the original zero endpoint. -/
theorem zero_of_epi (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : f.toOrderHom 0 = 0 := by
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective (f := f)).mp inferInstance
    (0 : Fin (m + 1))
  apply le_antisymm
  · exact (f.toOrderHom.monotone (Fin.zero_le i)).trans (le_of_eq hi)
  · exact Fin.zero_le _

/-- Every actual native epi sends the original last endpoint to the original last endpoint. -/
theorem last_of_epi (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] :
    f.toOrderHom (Fin.last n) = Fin.last m := by
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective (f := f)).mp inferInstance (Fin.last m)
  apply le_antisymm
  · exact Fin.le_last _
  · exact (le_of_eq hi.symm).trans (f.toOrderHom.monotone (Fin.le_last i))

/-- The whole native epi is genuinely onto in the same original coefficient universe. -/
theorem lifted_surjective (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] :
    Function.Surjective (f.toOrderHom.uliftMap :
      ULift.{u} (Fin (n + 1)) → ULift.{u} (Fin (m + 1))) := by
  intro j
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective (f := f)).mp inferInstance j.down
  exact ⟨ULift.up i, ULift.ext hi⟩

/-- Every entire original full terminal flag stays full under the same native epi. -/
theorem map_last_full (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    {q : SimplexCategoryᵒᵖ} (p : (coefficientObject.{u} n).obj q)
    (hp : (p.obj (Fin.last q.unop.len)).I = Set.univ) :
    (((map f (zero_of_epi f) (last_of_epi f)).app q p).obj
      (Fin.last q.unop.len)).I = Set.univ := by
  have h := map_flags f (zero_of_epi f) (last_of_epi f) p (Fin.last q.unop.len)
  exact h.trans ((congrArg (fun S => f.toOrderHom.uliftMap '' S) hp).trans
    ((Set.image_univ).trans (Set.range_eq_univ.mpr (lifted_surjective f))))

/-- Every entire original endpoint-only first flag retains its exact two original images. -/
theorem map_first_endpoints (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    {q : SimplexCategoryᵒᵖ} (p : (coefficientObject.{u} n).obj q)
    (hp : (p.obj 0).I =
      {ULift.up.{u} (0 : Fin (n + 1)), ULift.up.{u} (Fin.last n)}) :
    (((map f (zero_of_epi f) (last_of_epi f)).app q p).obj 0).I =
      {ULift.up.{u} (0 : Fin (m + 1)), ULift.up.{u} (Fin.last m)} := by
  have h := map_flags f (zero_of_epi f) (last_of_epi f) p 0
  rw [hp, Set.image_pair] at h
  exact h.trans (congrArg₂ (fun i j => ({i, j} : Set (ULift.{u} (Fin (m + 1)))))
    (lifted_zero f (zero_of_epi f)) (lifted_last f (last_of_epi f)))

end CategoryTheory.CoherentRealization.OriginalBead.OuterOperator
