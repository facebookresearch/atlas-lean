/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BaerSuzukiBinaryFinite
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace MathlibExt.GroupTheory.BaerSuzukiPeriodicBinaryFiniteKourovka11Problem11Wanted

open Equiv Equiv.Perm Subgroup

/-- The constant three-cycle in an infinite product of symmetric groups lies in a normal
3-subgroup. A pair of sequences generates a finite subgroup because its coordinates take
only finitely many pairs of values. -/
example : ∃ N : Subgroup (ℕ → Perm (Fin 3)), N.Normal ∧ IsPGroup 3 N ∧
    (fun _ ↦ finRotate 3) ∈ N := by
  let D := Perm (Fin 3)
  refine baerSuzukiBinaryFinite_holds 3 (by decide) (ℕ → D) ?_ (fun _ ↦ finRotate 3) ?_
  · intro x y
    let eval : ((D × D) → D) →* ℕ → D :=
      MonoidHom.pi fun i ↦ Pi.evalMonoidHom (fun _ ↦ D) (x i, y i)
    apply (Set.finite_range eval).subset
    exact (closure_le eval.range).2 (Set.pair_subset ⟨Prod.fst, rfl⟩ ⟨Prod.snd, rfl⟩)
  · intro x y hx hy
    let A := (sign (α := Fin 3) |>.compLeft ℕ).ker
    have ha : (fun _ : ℕ ↦ finRotate 3) ∈ A :=
      funext fun _ ↦ mem_alternatingGroup.mp (finRotate_bit1_mem_alternatingGroup (n := 1))
    have memA (z : ℕ → D) (hz : IsConj (fun _ ↦ finRotate 3) z) : z ∈ A := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hz
      exact (inferInstance : A.Normal).conj_mem _ ha g
    have hA : IsPGroup 3 A := by
      intro z
      refine ⟨1, Subtype.ext (funext fun i ↦ ?_)⟩
      have hz : z.val i ∈ alternatingGroup (Fin 3) := mem_alternatingGroup.mpr (congrFun z.2 i)
      have hc : Fintype.card (alternatingGroup (Fin 3)) = 3 := by
        rw [card_alternatingGroup, Fintype.card_fin]
        decide
      have hpow := pow_card_eq_one (x := (⟨z.val i, hz⟩ : alternatingGroup (Fin 3)))
      rw [hc] at hpow
      exact congrArg Subtype.val hpow
    exact hA.to_le ((closure_le A).2 (Set.pair_subset (memA x hx) (memA y hy)))

end MathlibExt.GroupTheory.BaerSuzukiPeriodicBinaryFiniteKourovka11Problem11Wanted
