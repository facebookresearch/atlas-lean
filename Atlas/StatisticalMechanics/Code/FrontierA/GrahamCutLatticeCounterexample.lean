/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib















open Finset

namespace StatMech.FrontierA


def grahamC4Adj (u v : Fin 4) : Prop :=
  (u = 0 /\ v = 1) \/ (u = 1 /\ v = 0) \/
  (u = 1 /\ v = 3) \/ (u = 3 /\ v = 1) \/
  (u = 3 /\ v = 2) \/ (u = 2 /\ v = 3) \/
  (u = 2 /\ v = 0) \/ (u = 0 /\ v = 2)

instance grahamC4Adj_decidable (u v : Fin 4) :
    Decidable (grahamC4Adj u v) := by
  unfold grahamC4Adj
  infer_instance



def grahamC4ReachWithin (C : Finset (Fin 4)) (u v : Fin 4) : Prop :=
  u ∈ C /\ v ∈ C /\
    (u = v \/ grahamC4Adj u v \/
      (∃ a ∈ C, grahamC4Adj u a /\ grahamC4Adj a v) \/
      (∃ a ∈ C, ∃ b ∈ C,
        grahamC4Adj u a /\ grahamC4Adj a b /\ grahamC4Adj b v))

instance grahamC4ReachWithin_decidable
    (C : Finset (Fin 4)) (u v : Fin 4) :
    Decidable (grahamC4ReachWithin C u v) := by
  unfold grahamC4ReachWithin
  infer_instance



def GrahamC4RootCutSupported (S : Finset (Fin 4)) : Prop :=
  let C := Finset.univ \ S
  (3 : Fin 4) ∈ C /\ ∀ v ∈ C, grahamC4ReachWithin C 3 v

instance grahamC4RootCutSupported_decidable (S : Finset (Fin 4)) :
    Decidable (GrahamC4RootCutSupported S) := by
  unfold GrahamC4RootCutSupported
  infer_instance

theorem grahamC4RootCutSupported_empty :
    GrahamC4RootCutSupported ∅ := by decide

theorem grahamC4RootCutSupported_one :
    GrahamC4RootCutSupported {1} := by decide

theorem grahamC4RootCutSupported_two :
    GrahamC4RootCutSupported {2} := by decide

theorem not_grahamC4RootCutSupported_one_two :
    ¬ GrahamC4RootCutSupported {1, 2} := by decide



theorem grahamC4_rootCutSupport_not_unionClosed :
    ∃ A B : Finset (Fin 4),
      GrahamC4RootCutSupported A /\
      GrahamC4RootCutSupported B /\
      GrahamC4RootCutSupported (A ∩ B) /\
      ¬ GrahamC4RootCutSupported (A ∪ B) := by
  refine ⟨{1}, {2}, grahamC4RootCutSupported_one,
    grahamC4RootCutSupported_two, ?_, ?_⟩
  · simpa using grahamC4RootCutSupported_empty
  · simpa using not_grahamC4RootCutSupported_one_two



theorem grahamC4_not_latticeCondition_of_exact_cutSupport
    (mu : Finset (Fin 4) -> Real)
    (hmu : ∀ S, 0 <= mu S)
    (hsupport : ∀ S, 0 < mu S <-> GrahamC4RootCutSupported S) :
    ¬ ∀ A B : Finset (Fin 4),
      mu A * mu B <= mu (A ∩ B) * mu (A ∪ B) := by
  intro hlattice
  have h1 : 0 < mu {1} :=
    (hsupport {1}).2 grahamC4RootCutSupported_one
  have h2 : 0 < mu {2} :=
    (hsupport {2}).2 grahamC4RootCutSupported_two
  have huNotPos : ¬ 0 < mu {1, 2} := by
    intro hu
    exact not_grahamC4RootCutSupported_one_two ((hsupport {1, 2}).1 hu)
  have hu : mu {1, 2} = 0 := by
    exact le_antisymm (le_of_not_gt huNotPos) (hmu {1, 2})
  have h := hlattice {1} {2}
  have hi : ({1} ∩ {2} : Finset (Fin 4)) = ∅ := by decide
  have huu : ({1} ∪ {2} : Finset (Fin 4)) = {1, 2} := by decide
  rw [hi, huu, hu, mul_zero] at h
  exact (not_lt_of_ge h) (mul_pos h1 h2)





def grahamK23Adj (u v : Fin 5) : Prop :=
  ((u = 0 \/ u = 1) /\ (v = 2 \/ v = 3 \/ v = 4)) \/
    ((v = 0 \/ v = 1) /\ (u = 2 \/ u = 3 \/ u = 4))

instance grahamK23Adj_decidable (u v : Fin 5) :
    Decidable (grahamK23Adj u v) := by
  unfold grahamK23Adj
  infer_instance



def grahamK23ReachWithin (C : Finset (Fin 5)) (u v : Fin 5) : Prop :=
  u ∈ C /\ v ∈ C /\
    (u = v \/ grahamK23Adj u v \/
      (∃ a ∈ C, grahamK23Adj u a /\ grahamK23Adj a v) \/
      (∃ a ∈ C, ∃ b ∈ C,
        grahamK23Adj u a /\ grahamK23Adj a b /\ grahamK23Adj b v) \/
      (∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C,
        grahamK23Adj u a /\ grahamK23Adj a b /\
          grahamK23Adj b c /\ grahamK23Adj c v))

instance grahamK23ReachWithin_decidable
    (C : Finset (Fin 5)) (u v : Fin 5) :
    Decidable (grahamK23ReachWithin C u v) := by
  unfold grahamK23ReachWithin
  infer_instance


def GrahamK23RootCutSupported (S : Finset (Fin 5)) : Prop :=
  let C := Finset.univ \ S
  (4 : Fin 5) ∈ C /\ ∀ v ∈ C, grahamK23ReachWithin C 4 v

instance grahamK23RootCutSupported_decidable (S : Finset (Fin 5)) :
    Decidable (GrahamK23RootCutSupported S) := by
  unfold GrahamK23RootCutSupported
  infer_instance

theorem grahamK23RootCutSupported_zero_two :
    GrahamK23RootCutSupported {0, 2} := by decide

theorem grahamK23RootCutSupported_one_two :
    GrahamK23RootCutSupported {1, 2} := by decide

theorem grahamK23RootCutSupported_two :
    GrahamK23RootCutSupported {2} := by decide

theorem not_grahamK23RootCutSupported_zero_one_two :
    ¬ GrahamK23RootCutSupported {0, 1, 2} := by decide

theorem grahamK23_pair_reaches_in_left_cut :
    grahamK23ReachWithin {0, 2} 0 2 := by decide

theorem grahamK23_pair_reaches_in_right_cut :
    grahamK23ReachWithin {1, 2} 2 1 := by decide





theorem grahamK23_not_rawCutFourFunctions_of_exactSupport
    (mu f g : Finset (Fin 5) -> Real)
    (hmu : ∀ S, 0 <= mu S)
    (hsupport : ∀ S, 0 < mu S <-> GrahamK23RootCutSupported S)
    (hf : 0 < f {0, 2}) (hg : 0 < g {1, 2}) :
    ¬ ∀ A B : Finset (Fin 5),
      (mu A * f A) * (mu B * g B) <=
        mu (A ∩ B) * (mu (A ∪ B) * (f (A ∪ B) * g (A ∪ B))) := by
  intro hfour
  have hA : 0 < mu {0, 2} :=
    (hsupport {0, 2}).2 grahamK23RootCutSupported_zero_two
  have hB : 0 < mu {1, 2} :=
    (hsupport {1, 2}).2 grahamK23RootCutSupported_one_two
  have huNotPos : ¬ 0 < mu {0, 1, 2} := by
    intro hu
    exact not_grahamK23RootCutSupported_zero_one_two
      ((hsupport {0, 1, 2}).1 hu)
  have hu : mu {0, 1, 2} = 0 :=
    le_antisymm (le_of_not_gt huNotPos) (hmu {0, 1, 2})
  have h := hfour {0, 2} {1, 2}
  have hi : ({0, 2} ∩ {1, 2} : Finset (Fin 5)) = {2} := by decide
  have huu : ({0, 2} ∪ {1, 2} : Finset (Fin 5)) = {0, 1, 2} := by decide
  rw [hi, huu, hu, zero_mul, mul_zero] at h
  exact (not_lt_of_ge h) (mul_pos (mul_pos hA hf) (mul_pos hB hg))

end StatMech.FrontierA
