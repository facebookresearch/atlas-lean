/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Short signed-monomial certificate plans for literal source permutation words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsSpin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A compact model contains the binary pullback matrix and its full quadratic sign. -/
structure RepresentativeSpinModel where
  /-- The binary matrix acting by pullback on the twelve spin coordinates. -/
  coordinate : Matrix (Fin 12) (Fin 12) (ZMod 2)
  /-- All quadratic coefficients, including the diagonal linear sign. -/
  phase : Matrix (Fin 12) (Fin 12) (ZMod 2)
  deriving DecidableEq

/-- A small edge check compares the coordinate matrix and basis/pair phase values. -/
def representativeSpinEdge (a b c : RepresentativeSpinModel) : Prop :=
  c.coordinate = b.coordinate * a.coordinate ∧
  (∀ i : Fin 12, monsterMonomialQuadratic a.phase (Pi.single i 1) +
    monsterMonomialQuadratic b.phase (a.coordinate.col i) =
      monsterMonomialQuadratic c.phase (Pi.single i 1)) ∧
  (∀ i j : Fin 12, monsterMonomialQuadratic a.phase (Pi.single i 1 + Pi.single j 1) +
    monsterMonomialQuadratic b.phase
      (a.coordinate.col i + a.coordinate.col j) =
        monsterMonomialQuadratic c.phase (Pi.single i 1 + Pi.single j 1))

/-- An edge check extends an actual full spin certificate through multiplication. -/
theorem representativeSpinEdge_certificate (g h : SpinHolomorph)
    (a b c : RepresentativeSpinModel)
    (hg : representativeSpinCertificate g a.coordinate a.phase)
    (hh : representativeSpinCertificate h b.coordinate b.phase)
    (he : representativeSpinEdge a b c) :
    representativeSpinCertificate (g * h) c.coordinate c.phase := by
  rcases he with ⟨hP, hb, hp⟩
  have hv (t : SpinIndex) :
      monsterMonomialQuadratic (a.phase + a.coordinateᵀ * b.phase * a.coordinate) t =
        monsterMonomialQuadratic c.phase t := by
    apply representativeQuadratic_basis_pairs
    · intro i
      simpa only [representativeQuadratic_add_matrix, representativeQuadratic_pullback,
        Matrix.mulVec_add, Matrix.mulVec_single_one]
        using hb i
    · intro i j
      simpa only [representativeQuadratic_add_matrix, representativeQuadratic_pullback,
        Matrix.mulVec_add, Matrix.mulVec_single_one]
        using hp i j
  intro f t
  rw [hP, representativeSpinCertificate_mul g h _ _ _ _ hg hh f t, hv]

/-- A certificate plan records a generator reference and the explicit model after that edge. -/
abbrev RepresentativeSpinPlan (ι : Type) := List (ι × RepresentativeSpinModel)

/-- Each consecutive edge of a plan must pass its finite coordinate/sign check. -/
def representativeSpinPlanValid {ι : Type} (models : ι → RepresentativeSpinModel) :
    RepresentativeSpinModel → RepresentativeSpinPlan ι → Prop
  | _, [] => True
  | a, (letter, next) :: rest =>
      representativeSpinEdge a (models letter) next ∧ representativeSpinPlanValid models next rest

/-- The final model of a plan, computed without expanding any group word. -/
def representativeSpinPlanEnd {ι : Type} :
    RepresentativeSpinModel → RepresentativeSpinPlan ι → RepresentativeSpinModel
  | a, [] => a
  | _, (_, next) :: rest => representativeSpinPlanEnd next rest

/-- Evaluation of a plan multiplies only actual spin holomorphs. -/
noncomputable def representativeSpinPlanEvaluate {ι : Type} (generators : ι → SpinHolomorph) :
    SpinHolomorph → RepresentativeSpinPlan ι → SpinHolomorph
  | g, [] => g
  | g, (letter, _) :: rest => representativeSpinPlanEvaluate generators (g * generators letter) rest

/-- Finite edge checks and actual generator certificates prove the entire actual word action. -/
theorem representativeSpinPlan_certificate {ι : Type}
    (generators : ι → SpinHolomorph) (models : ι → RepresentativeSpinModel)
    (plan : RepresentativeSpinPlan ι) (g : SpinHolomorph) (a : RepresentativeSpinModel)
    (hg : representativeSpinCertificate g a.coordinate a.phase)
    (hletters : ∀ step ∈ plan, representativeSpinCertificate (generators step.1)
      (models step.1).coordinate (models step.1).phase)
    (hvalid : representativeSpinPlanValid models a plan) :
    representativeSpinCertificate (representativeSpinPlanEvaluate generators g plan)
      (representativeSpinPlanEnd a plan).coordinate (representativeSpinPlanEnd a plan).phase := by
  induction plan generalizing g a with
  | nil => exact hg
  | cons step rest ih =>
    rcases step with ⟨letter, next⟩
    exact ih (g * generators letter) next
      (representativeSpinEdge_certificate g (generators letter) a (models letter) next hg
        (hletters (letter, next) (List.mem_cons_self ..)) hvalid.1)
      (fun step hstep => hletters step (List.mem_cons_of_mem _ hstep)) hvalid.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
