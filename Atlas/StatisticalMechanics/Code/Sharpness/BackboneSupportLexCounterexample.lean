/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















import Code.Sharpness.BackboneP3Domain

open Finset

namespace StatMech.Sharpness


inductive shbK4Edge
  | e01 | e02 | e03 | e12 | e13 | e23
  deriving DecidableEq, Fintype

namespace shbK4Edge


def Incident : shbK4Edge → Fin 4 → Prop
  | e01, v => v = 0 ∨ v = 1
  | e02, v => v = 0 ∨ v = 2
  | e03, v => v = 0 ∨ v = 3
  | e12, v => v = 1 ∨ v = 2
  | e13, v => v = 1 ∨ v = 3
  | e23, v => v = 2 ∨ v = 3

instance (e : shbK4Edge) : DecidablePred e.Incident := by
  intro v
  unfold Incident
  split <;> infer_instance

end shbK4Edge


def shbK4Boundary (A : Finset shbK4Edge) : Finset (Fin 4) :=
  Finset.univ.filter fun v => Odd ((A.filter fun e => e.Incident v).card)


def shbK4Configs (E : Finset shbK4Edge) : Finset (Finset shbK4Edge) :=
  E.powerset


def shbK4H : Finset shbK4Edge :=
  {shbK4Edge.e01, shbK4Edge.e02, shbK4Edge.e03,
    shbK4Edge.e13, shbK4Edge.e23}


def shbK4G : Finset shbK4Edge := Finset.univ



inductive shbK4Path03
  | p0123 | p013 | p0213 | p023 | p03
  deriving DecidableEq, Fintype


def shbK4Path03.edges : shbK4Path03 → Finset shbK4Edge
  | p0123 => {shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23}
  | p013 => {shbK4Edge.e01, shbK4Edge.e13}
  | p0213 => {shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13}
  | p023 => {shbK4Edge.e02, shbK4Edge.e23}
  | p03 => {shbK4Edge.e03}


def shbK4SupportsPath (A : Finset shbK4Edge) (p : shbK4Path03) : Prop :=
  p.edges ⊆ A

instance (A : Finset shbK4Edge) (p : shbK4Path03) :
    Decidable (shbK4SupportsPath A p) := by
  unfold shbK4SupportsPath
  infer_instance





def shbK4SelectsDirect03 (A : Finset shbK4Edge) : Prop :=
  shbK4Boundary A = {0, 3} ∧
    shbK4Edge.e03 ∈ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e13} : Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e23} : Finset shbK4Edge) ⊆ A

instance (A : Finset shbK4Edge) : Decidable (shbK4SelectsDirect03 A) := by
  unfold shbK4SelectsDirect03
  infer_instance



theorem shbK4_selectsDirect03_iff_pathEnumeration
    (A : Finset shbK4Edge) :
    shbK4SelectsDirect03 A ↔
      shbK4Boundary A = {0, 3} ∧
        shbK4SupportsPath A shbK4Path03.p03 ∧
        ∀ p, p ≠ shbK4Path03.p03 → ¬ shbK4SupportsPath A p := by
  decide +revert +kernel


def shbK4DirectFiberMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4SelectsDirect03 A then t ^ A.card else 0


def shbK4VacuumMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4Boundary A = ∅ then t ^ A.card else 0


def shbK4DirectRho (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  shbK4DirectFiberMass E t / shbK4VacuumMass E t


theorem shbK4H_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4H (2 / 3) = 2 / 3 ∧
      shbK4VacuumMass shbK4H (2 / 3) = 145 / 81 := by
  decide +kernel


theorem shbK4G_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4G (2 / 3) = 86 / 81 ∧
      shbK4VacuumMass shbK4G (2 / 3) = 25 / 9 := by
  decide +kernel


theorem shbK4_rhos_at_two_thirds :
    shbK4DirectRho shbK4H (2 / 3) = 54 / 145 ∧
      shbK4DirectRho shbK4G (2 / 3) = 86 / 225 := by
  constructor
  · unfold shbK4DirectRho
    rw [shbK4H_masses_at_two_thirds.1, shbK4H_masses_at_two_thirds.2]
    norm_num
  · unfold shbK4DirectRho
    rw [shbK4G_masses_at_two_thirds.1, shbK4G_masses_at_two_thirds.2]
    norm_num




theorem shb_supportLex_edgeDomain_P3_counterexample :
    shbK4DirectRho shbK4H (2 / 3) < shbK4DirectRho shbK4G (2 / 3) := by
  rw [shbK4_rhos_at_two_thirds.1, shbK4_rhos_at_two_thirds.2]
  norm_num


theorem shbK4H_ssubset_shbK4G : shbK4H ⊂ shbK4G := by
  decide +kernel

end StatMech.Sharpness
