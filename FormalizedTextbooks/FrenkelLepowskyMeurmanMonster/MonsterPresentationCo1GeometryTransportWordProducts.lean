/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked intermediate matrices retain the original literal actual lattice transport words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportMatrices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitSpan

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A source word is evaluated in the actual Leech group before taking its actual Conway class. -/
def monsterCo1GeometryTransportWord (w : List (Fin 5)) : Co1 :=
  (QuotientGroup.mk' signsSubgroup) (omegaOrbitWordIsometry w)

/-- Appending the next source letter preserves the original left-action lattice word order. -/
theorem monsterCo1GeometryTransportWordIsometry_append (w : List (Fin 5)) (k : Fin 5) :
    omegaOrbitWordIsometry (w ++ [k]) = omegaOrbitIsometry k * omegaOrbitWordIsometry w := by
  induction w with
  | nil => simp [omegaOrbitWordIsometry]
  | cons j w ih =>
      simp only [List.cons_append, omegaOrbitWordIsometry]
      rw [ih, mul_assoc]

/-- Original word concatenation commutes with taking the actual Conway quotient. -/
theorem monsterCo1GeometryTransportWord_append (w : List (Fin 5)) (k : Fin 5) :
    monsterCo1GeometryTransportWord (w ++ [k]) =
      monsterCo1FiveGenerator k * monsterCo1GeometryTransportWord w := by
  rw [monsterCo1GeometryTransportWord, monsterCo1GeometryTransportWordIsometry_append,
    map_mul]
  rfl

/-- The empty literal actual source word acts by the identity matrix. -/
theorem monsterCo1GeometryTransportWord_nil_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction (monsterCo1GeometryTransportWord []) v =
      (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := by
  simp [monsterCo1GeometryTransportWord, omegaOrbitWordIsometry, Matrix.one_mulVec]

/-- One complete finite product certificate advances the same literal actual word. -/
theorem monsterCo1GeometryTransportWord_append_binary (w : List (Fin 5)) (k : Fin 5)
    (A B : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hw : ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord w) v = A *ᵥ v)
    (hB : omegaOrbitBinaryMatrices k * A = B) :
    ∀ v, co1BinaryAction (monsterCo1GeometryTransportWord (w ++ [k])) v = B *ᵥ v := by
  rw [monsterCo1GeometryTransportWord_append]
  exact monsterCo1GeometryTransport_matrix_mul (monsterCo1FiveGenerator k)
    (monsterCo1GeometryTransportWord w) (omegaOrbitBinaryMatrices k) A B
    (fun v => omegaOrbitIsometry_binary k v) hw hB

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
