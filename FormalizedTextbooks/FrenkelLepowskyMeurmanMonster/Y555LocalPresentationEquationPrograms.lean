/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite acyclic derivations from explicit source equations and literal substitutions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A derivation uses only free cancellation, supplied source equations, or earlier equations. -/
inductive Y322EquationJustification (alphabet source : Type*) (earlier : ℕ)
  | source (reference : source)
  | substitutions (moves : List (Y322EquationMove earlier))
  | freely
  | context (reference : Fin earlier) (backward inverted : Bool)
      (before after : List (alphabet × Bool))
  | transitive (first second : Fin earlier)

/-- A literal claimed equation together with its finite acyclic derivation instruction. -/
structure Y322EquationCertificate (alphabet source : Type*) (earlier : ℕ) where
  /-- The literal equation claimed by this certificate. -/
  equation : Y322WordEquation alphabet
  /-- Its source or derivation using strictly earlier equations. -/
  justification : Y322EquationJustification alphabet source earlier

/-- A finite table of equation certificates with only strictly earlier proof references. -/
abbrev Y322EquationProgram (alphabet source : Type*) (size : ℕ) :=
  (i : Fin size) → Y322EquationCertificate alphabet source i.val

/-- Two literal equations have the same sides after exact free cancellation. -/
def y322EquationsSameReduction {alphabet : Type*} [DecidableEq alphabet]
    (first second : Y322WordEquation alphabet) : Prop :=
  FreeGroup.reduce first.left = FreeGroup.reduce second.left ∧
    FreeGroup.reduce first.right = FreeGroup.reduce second.right

/-- Check one certificate using exact free cancellation and earlier literal equations. -/
def Y322EquationCertificate.Checked {alphabet source : Type*} [DecidableEq alphabet]
    {earlier : ℕ} (sources : source → Y322WordEquation alphabet)
    (prior : Fin earlier → Y322WordEquation alphabet)
    (certificate : Y322EquationCertificate alphabet source earlier) : Prop :=
  match certificate.justification with
  | .source reference => y322EquationsSameReduction certificate.equation (sources reference)
  | .substitutions moves =>
      y322EquationRun prior moves certificate.equation.left = some certificate.equation.right
  | .freely =>
      FreeGroup.reduce certificate.equation.left = FreeGroup.reduce certificate.equation.right
  | .context reference backward inverted before after =>
      y322EquationsSameReduction certificate.equation
        (y322EquationContext (y322EquationOrient (prior reference) backward inverted) before after)
  | .transitive first second =>
      FreeGroup.reduce (prior first).right = FreeGroup.reduce (prior second).left ∧
        y322EquationsSameReduction certificate.equation ⟨(prior first).left, (prior second).right⟩

/-- A checked certificate is valid whenever its explicit sources and earlier equations are valid. -/
theorem y322EquationCertificate_checked_valid {alphabet source G : Type*}
    [DecidableEq alphabet] [Group G] {earlier : ℕ} (values : alphabet → G)
    (sources : source → Y322WordEquation alphabet) (hs : ∀ s, (sources s).Valid values)
    (prior : Fin earlier → Y322WordEquation alphabet) (hp : ∀ i, (prior i).Valid values)
    (certificate : Y322EquationCertificate alphabet source earlier)
    (h : certificate.Checked sources prior) : certificate.equation.Valid values := by
  cases hj : certificate.justification with
  | source reference =>
    simp only [Y322EquationCertificate.Checked, hj, y322EquationsSameReduction] at h
    exact y322WordEquation_transport values _ _ (hs reference) h.1 h.2
  | substitutions moves =>
    simp only [Y322EquationCertificate.Checked, hj] at h
    exact y322EquationRun_valid values prior hp moves _ _ h
  | freely =>
    simp only [Y322EquationCertificate.Checked, hj] at h
    exact y322EquationWordValue_eq_of_reduce values _ _ h
  | context reference backward inverted before after =>
    simp only [Y322EquationCertificate.Checked, hj, y322EquationsSameReduction] at h
    exact y322WordEquation_transport values _ _
      (y322EquationContext_valid values _
        (y322EquationOrient_valid values _ (hp reference) backward inverted) before after) h.1 h.2
  | transitive first second =>
    simp only [Y322EquationCertificate.Checked, hj, y322EquationsSameReduction] at h
    have ht : (Y322WordEquation.mk (prior first).left (prior second).right).Valid values :=
      (hp first).trans ((y322EquationWordValue_eq_of_reduce values _ _ h.1).trans (hp second))
    exact y322WordEquation_transport values _ _ ht h.2.1 h.2.2

/-- Every equation of a completely checked finite acyclic table holds in the actual group. -/
theorem y322EquationProgram_valid {alphabet source G : Type*} [DecidableEq alphabet] [Group G]
    {size : ℕ} (values : alphabet → G) (sources : source → Y322WordEquation alphabet)
    (hs : ∀ s, (sources s).Valid values) (program : Y322EquationProgram alphabet source size)
    (h : ∀ i, (program i).Checked sources
      (fun a => (program (y322ProgramPrior i a)).equation)) (i : Fin size) :
    (program i).equation.Valid values := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    exact y322EquationCertificate_checked_valid values sources hs _
      (fun a => ih (y322ProgramPrior i a) a.isLt) (program i) (h i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
