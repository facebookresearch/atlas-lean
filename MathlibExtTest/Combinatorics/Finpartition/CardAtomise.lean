/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Finpartition.Card
public import MathlibExt.Combinatorics.Finpartition.Atomise

/-!
# Consumer tests for the Finpartition cardinality and atomisation APIs

These examples exercise `Finpartition.cardProd` on empty, bottom, and top
partitions, its interaction with monoid homomorphisms, and both public
atomisation part formulas on concrete finsets.
-/

open Finset Finpartition

namespace FinpartitionCardAtomiseTest

/-- `cardProd` over the empty carrier is `1`. -/
example : (⊥ : Finpartition (∅ : Finset (Fin 3))).cardProd (fun _ => (2 : ℕ)) = 1 :=
  Finpartition.cardProd_empty _

/-- `cardProd` over the bottom partition of `Fin 3` with constant weight `2`. -/
example : (⊥ : Finpartition (Finset.univ : Finset (Fin 3))).cardProd (fun _ => (2 : ℕ)) = 8 := by
  rw [Finpartition.cardProd_bot, Finset.card_univ, Fintype.card_fin]
  decide

/-- `cardProd` over the top partition reads the weight at the carrier card. -/
example : (⊤ : Finpartition (Finset.univ : Finset (Fin 3))).cardProd (fun n => n) = 3 := by
  rw [Finpartition.cardProd_top Finset.univ_nonempty]
  simp

/-- `cardProd` commutes with monoid homomorphisms. -/
example (P : Finpartition (Finset.univ : Finset (Fin 3))) (f : ℕ → ℕ) :
    (MonoidHom.id ℕ) (P.cardProd f) = P.cardProd ((MonoidHom.id ℕ) ∘ f) :=
  Finpartition.cardProd_mapMonoidHom P f _

/-- Every block of a finite-set partition is bounded by the carrier card. -/
example (P : Finpartition (Finset.univ : Finset (Fin 3))) {B : Finset (Fin 3)} (hB : B ∈ P.parts) :
    B.card ≤ 3 := by
  have h := Finpartition.card_le_of_mem_parts P hB
  simpa using h

/-- Atomising `Fin 3` at the singleton `{0}` leaves `{0}` and its complement. -/
example :
    (Finpartition.atomise (Finset.univ : Finset (Fin 3)) ({{0}} : Finset (Finset (Fin 3)))).parts =
      {{0}, Finset.univ \ {0}} :=
  Finpartition.atomise_singleton_parts (by decide) (by decide) (by decide)

/-- Atomising `Fin 3` at the complement singletons of `{0}`. -/
example :
    (Finpartition.atomise (Finset.univ : Finset (Fin 3))
      ((Finset.univ \ {0}).map (⟨singleton, singleton_injective⟩ : Fin 3 ↪ Finset (Fin 3)))).parts =
      insert {0} ((Finset.univ \ {0}).map (⟨singleton, singleton_injective⟩ : Fin 3 ↪ Finset (Fin 3))) :=
  Finpartition.atomise_compl_singletons_parts (by decide) (by decide)

end FinpartitionCardAtomiseTest
