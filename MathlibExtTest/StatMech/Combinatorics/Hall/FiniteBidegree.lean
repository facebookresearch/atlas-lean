/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Hall.FiniteBidegree
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.Hall.FiniteBidegree`

* `finiteRelationHall_of_bidegree` for the equality relation on `Fin 3` with degree `1`.
* `finiteRelationHall_of_certificateEmbeddings` and
  `finiteRelation_exists_injective_of_certificateEmbeddings` for the equality relation on `Fin 2`
  with explicit one-element certificates.
-/

@[expose] public section


namespace MathlibExtTest.StatMech.Combinatorics.Hall.FiniteBidegree

example : ∀ sources : Finset (Fin 3), sources.card ≤
    (Finset.univ.filter fun target => ∃ source ∈ sources, source = target).card := by
  have h := finiteRelationHall_of_bidegree (Source := Fin 3) (Target := Fin 3) (· = ·) 1 one_pos
      (fun s => Finset.card_pos.mpr ⟨s, by simp⟩) (fun t => Finset.card_le_one.mpr fun a ha b hb => by
        simp only [Finset.mem_filter] at ha hb; rw [ha.2, hb.2])
  convert h

/-- One-element source certificates for equality. -/
def srcCert (s : Fin 2) : Fin 1 ↪ {t : Fin 2 // s = t} :=
  ⟨fun _ => ⟨s, rfl⟩, fun a b _ => Subsingleton.elim a b⟩

/-- One-element target codes for equality. -/
def tgtCode (t : Fin 2) : {s : Fin 2 // s = t} ↪ Fin 1 :=
  ⟨fun _ => 0, fun a b _ => Subtype.ext (a.2.trans b.2.symm)⟩

example : ∃ matching : Fin 2 → Fin 2,
    Function.Injective matching ∧ ∀ s, s = matching s :=
  finiteRelation_exists_injective_of_certificateEmbeddings (· = ·) 1 one_pos srcCert tgtCode

end MathlibExtTest.StatMech.Combinatorics.Hall.FiniteBidegree
