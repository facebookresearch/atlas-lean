/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteEntropy
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Order.LiminfLimsup

/-!
# Finite-law optimization for one-shot channel simulation

Auxiliary laws preserve the given XY marginal and range over every positive
finite alphabet. Independence is the zero-mutual-information condition. The
limsup optimizer and the uniform alpha/beta optimizer are separate definitions;
their equality is not assumed by this reusable API.
-/

@[expose] public section

namespace InformationTheory

/-- A joint probability law on two positive finite labeled alphabets. -/
structure FiniteJointLaw where
  nx : ℕ
  ny : ℕ
  nx_pos : 0 < nx
  ny_pos : 0 < ny
  law : PMF (Fin nx × Fin ny)

/-- The actual X marginal of the joint law. -/
noncomputable def FiniteJointLaw.inputLaw (p : FiniteJointLaw) : PMF (Fin p.nx) :=
  p.law.map Prod.fst

/-- The actual Y marginal of the joint law. -/
noncomputable def FiniteJointLaw.outputLaw (p : FiniteJointLaw) : PMF (Fin p.ny) :=
  p.law.map Prod.snd

/-- Mutual information in bits, using the exact finite entropy identity. -/
noncomputable def FiniteJointLaw.mutualInformation (p : FiniteJointLaw) : ℝ :=
  shannonEntropy p.inputLaw + shannonEntropy p.outputLaw - shannonEntropy p.law

/-- A finite auxiliary extension with exactly the specified XY marginal. -/
structure FiniteExtension (p : FiniteJointLaw) where
  ns : ℕ
  ns_pos : 0 < ns
  law : PMF ((Fin p.nx × Fin p.ny) × Fin ns)
  marginal_eq : law.map Prod.fst = p.law

/-- Appending a singleton auxiliary alphabet preserves every given joint law. -/
noncomputable def FiniteExtension.trivial (p : FiniteJointLaw) : FiniteExtension p where
  ns := 1
  ns_pos := Nat.zero_lt_succ 0
  law := p.law.map (fun z => (z, (0 : Fin 1)))
  marginal_eq := by
    rw [PMF.map_comp]
    exact PMF.map_id p.law

/-- The actual S marginal of a finite extension. -/
noncomputable def FiniteExtension.auxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin q.ns) :=
  q.law.map Prod.snd

/-- The actual XS marginal of a finite extension. -/
noncomputable def FiniteExtension.inputAuxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin p.nx × Fin q.ns) :=
  q.law.map (fun z => (z.1.1, z.2))

/-- The actual YS marginal of a finite extension. -/
noncomputable def FiniteExtension.outputAuxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin p.ny × Fin q.ns) :=
  q.law.map (fun z => (z.1.2, z.2))

/-- Mutual information between X and S in the actual extension. -/
noncomputable def FiniteExtension.auxiliaryInformation {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy p.inputLaw + shannonEntropy q.auxiliaryLaw -
    shannonEntropy q.inputAuxiliaryLaw

/-- Conditional entropy H(Y|S) in bits, using the exact entropy identity. -/
noncomputable def FiniteExtension.conditionalEntropy {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy q.outputAuxiliaryLaw - shannonEntropy q.auxiliaryLaw

/-- Conditional entropy `H(Y | X, S)` of the output given the input and
auxiliary in an extension: `H(X, Y, S) - H(X, S)`. It vanishes exactly
when `Y` is recoverable from `(X, S)` (a deterministic function of the
pair, almost surely). -/
noncomputable def FiniteExtension.outputGivenInputAuxiliaryEntropy {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy q.law - shannonEntropy q.inputAuxiliaryLaw

/-- A singleton output is always recoverable: `H(Y | X, S) = 0` for every
actual extension. -/
theorem FiniteExtension.outputGivenInputAuxiliaryEntropy_eq_zero_of_output_subsingleton
    {p : FiniteJointLaw} [Subsingleton (Fin p.ny)] (q : FiniteExtension p) :
    q.outputGivenInputAuxiliaryEntropy = 0 := by
  let e : (Fin p.nx × Fin p.ny) × Fin q.ns ≃ Fin p.nx × Fin q.ns :=
    ⟨fun z => (z.1.1, z.2), fun z => ((z.1, ⟨0, p.ny_pos⟩), z.2),
      fun z => Prod.ext (Prod.ext rfl (Subsingleton.elim _ _)) rfl,
      fun z => Prod.ext rfl rfl⟩
  have hm : q.law.map e = q.inputAuxiliaryLaw := rfl
  unfold FiniteExtension.outputGivenInputAuxiliaryEntropy
  rw [← hm, shannonEntropy_map_equiv]
  exact sub_self _

/-- The constructed singleton auxiliary has its actual deterministic law. -/
@[simp] theorem FiniteExtension.trivial_auxiliaryLaw (p : FiniteJointLaw) :
    (FiniteExtension.trivial p).auxiliaryLaw = PMF.pure (0 : Fin 1) := by
  change (p.law.map (fun z => (z, (0 : Fin 1)))).map Prod.snd = PMF.pure 0
  rw [PMF.map_comp]
  exact PMF.map_const p.law (0 : Fin 1)

/-- The constructed singleton auxiliary is independent of the actual input. -/
@[simp] theorem FiniteExtension.trivial_auxiliaryInformation (p : FiniteJointLaw) :
    (FiniteExtension.trivial p).auxiliaryInformation = 0 := by
  change shannonEntropy p.inputLaw +
    shannonEntropy ((p.law.map (fun z => (z, (0 : Fin 1)))).map Prod.snd) -
    shannonEntropy ((p.law.map (fun z => (z, (0 : Fin 1)))).map
      (fun z => (z.1.1, z.2))) = 0
  have h : (p.law.map (fun z => (z, (0 : Fin 1)))).map
      (fun z => (z.1.1, z.2)) = p.inputLaw.map (fun a => (a, (0 : Fin 1))) := by
    simp [FiniteJointLaw.inputLaw, PMF.map_comp, Function.comp_def]
  rw [h, shannonEntropy_map_prod_singleton, PMF.map_comp]
  change shannonEntropy p.inputLaw +
    shannonEntropy (p.law.map (Function.const _ (0 : Fin 1))) -
      shannonEntropy p.inputLaw = 0
  rw [shannonEntropy_map_const]
  simp

/-- A singleton auxiliary leaves the actual output entropy unchanged. -/
@[simp] theorem FiniteExtension.trivial_conditionalEntropy (p : FiniteJointLaw) :
    (FiniteExtension.trivial p).conditionalEntropy = shannonEntropy p.outputLaw := by
  change shannonEntropy ((p.law.map (fun z => (z, (0 : Fin 1)))).map
    (fun z => (z.1.2, z.2))) -
      shannonEntropy ((p.law.map (fun z => (z, (0 : Fin 1)))).map Prod.snd) =
        shannonEntropy p.outputLaw
  have h : (p.law.map (fun z => (z, (0 : Fin 1)))).map
      (fun z => (z.1.2, z.2)) = p.outputLaw.map (fun a => (a, (0 : Fin 1))) := by
    simp [FiniteJointLaw.outputLaw, PMF.map_comp, Function.comp_def]
  rw [h, shannonEntropy_map_prod_singleton, PMF.map_comp]
  change shannonEntropy p.outputLaw -
    shannonEntropy (p.law.map (Function.const _ (0 : Fin 1))) =
      shannonEntropy p.outputLaw
  rw [shannonEntropy_map_const]
  simp

/-- The XS marginal has precisely the specified X law. -/
@[simp] theorem FiniteExtension.inputAuxiliaryLaw_map_fst {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.inputAuxiliaryLaw.map Prod.fst = p.inputLaw := by
  change (q.law.map (fun z => (z.1.1, z.2))).map Prod.fst = p.law.map Prod.fst
  rw [PMF.map_comp]
  simpa [PMF.map_comp, Function.comp_def] using congrArg (PMF.map Prod.fst) q.marginal_eq

/-- The YS marginal has precisely the specified Y law. -/
@[simp] theorem FiniteExtension.outputAuxiliaryLaw_map_fst {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.outputAuxiliaryLaw.map Prod.fst = p.outputLaw := by
  change (q.law.map (fun z => (z.1.2, z.2))).map Prod.fst = p.law.map Prod.snd
  rw [PMF.map_comp]
  simpa [PMF.map_comp, Function.comp_def] using congrArg (PMF.map Prod.snd) q.marginal_eq

/-- The two pair marginals have the same actual auxiliary law. -/
@[simp] theorem FiniteExtension.inputAuxiliaryLaw_map_snd {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.inputAuxiliaryLaw.map Prod.snd = q.auxiliaryLaw := by
  simp [FiniteExtension.inputAuxiliaryLaw, FiniteExtension.auxiliaryLaw,
    PMF.map_comp, Function.comp_def]

/-- The output/auxiliary pair has the actual auxiliary marginal. -/
@[simp] theorem FiniteExtension.outputAuxiliaryLaw_map_snd {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.outputAuxiliaryLaw.map Prod.snd = q.auxiliaryLaw := by
  simp [FiniteExtension.outputAuxiliaryLaw, FiniteExtension.auxiliaryLaw,
    PMF.map_comp, Function.comp_def]

/-- A singleton output has zero conditional entropy for every actual extension. -/
theorem FiniteExtension.conditionalEntropy_eq_zero_of_output_subsingleton
    {p : FiniteJointLaw} [Subsingleton (Fin p.ny)] (q : FiniteExtension p) :
    q.conditionalEntropy = 0 := by
  let e : Fin q.ns ≃ Fin p.ny × Fin q.ns :=
    ⟨fun s => (⟨0, p.ny_pos⟩, s), Prod.snd, fun _ => rfl,
      fun z => Prod.ext (Subsingleton.elim _ _) rfl⟩
  have hm : q.auxiliaryLaw.map e = q.outputAuxiliaryLaw := by
    change (q.law.map Prod.snd).map e = q.law.map (fun z => (z.1.2, z.2))
    rw [PMF.map_comp]
    congr 1
    funext z
    exact Prod.ext (Subsingleton.elim _ _) rfl
  unfold FiniteExtension.conditionalEntropy
  rw [← hm, shannonEntropy_map_equiv]
  exact sub_self _

/-- The fixed-law conditional-prefix entropy optimum, preserving empty-infimum infinity.
Source: Li, arXiv:2501.13736v4, equation cs_h_c. -/
noncomputable def conditionalPrefixOptimum (p : FiniteJointLaw) : EReal :=
  sInf {h | ∃ q : FiniteExtension p, q.auxiliaryInformation = 0 ∧
    q.outputGivenInputAuxiliaryEntropy = 0 ∧
    h = (q.conditionalEntropy : EReal)}

/-- Worst-case optimum at exactly the prescribed finite mutual information. -/
noncomputable def worstCaseOptimum (t : ℝ) : EReal :=
  sSup {h | ∃ p : FiniteJointLaw, p.mutualInformation = t ∧ h = conditionalPrefixOptimum p}

/-- The worst-case one-shot conditional-prefix asymptotic constant term.
Source: Li, arXiv:2501.13736v4, definition of c_c*. -/
noncomputable def channelSimulationConstant : EReal :=
  Filter.limsup (fun t : ℝ => worstCaseOptimum t - (t : EReal) -
    (Real.log t / Real.log 2 : EReal)) Filter.atTop

/-- A uniform additive outer constant with one positive inner constant. -/
def HasUniformOuterConstant (α : ℝ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ p : FiniteJointLaw, ∃ q : FiniteExtension p,
    q.auxiliaryInformation = 0 ∧ q.outputGivenInputAuxiliaryEntropy = 0 ∧
    q.conditionalEntropy ≤ p.mutualInformation +
      Real.log (p.mutualInformation + β) / Real.log 2 + α

/-- The infimum of uniformly admissible real outer constants, preserving infinity. -/
noncomputable def uniformOuterConstantInfimum : EReal :=
  sInf {h | ∃ α : ℝ, HasUniformOuterConstant α ∧ h = (α : EReal)}

/-- Every actual admissible extension bounds the fixed-law infimum from above. -/
theorem conditionalPrefixOptimum_le {p : FiniteJointLaw} (q : FiniteExtension p)
    (hq : q.auxiliaryInformation = 0)
    (hqrec : q.outputGivenInputAuxiliaryEntropy = 0) :
    conditionalPrefixOptimum p ≤ (q.conditionalEntropy : EReal) := by
  exact sInf_le ⟨q, hq, hqrec, rfl⟩

/-- The actual fixed-law infimum of every singleton-output law is exactly zero. -/
theorem conditionalPrefixOptimum_eq_zero_of_output_subsingleton
    (p : FiniteJointLaw) [Subsingleton (Fin p.ny)] :
    conditionalPrefixOptimum p = 0 := by
  apply le_antisymm ?_ ?_
  · simpa only [FiniteExtension.conditionalEntropy_eq_zero_of_output_subsingleton,
      EReal.coe_zero] using conditionalPrefixOptimum_le (FiniteExtension.trivial p)
        (FiniteExtension.trivial_auxiliaryInformation p)
        (FiniteExtension.outputGivenInputAuxiliaryEntropy_eq_zero_of_output_subsingleton (FiniteExtension.trivial p))
  · apply le_sInf
    rintro h ⟨q, _, _, rfl⟩
    simp [FiniteExtension.conditionalEntropy_eq_zero_of_output_subsingleton]

/-- Every actual information-slice member contributes to the worst-case supremum. -/
theorem conditionalPrefixOptimum_le_worstCaseOptimum (p : FiniteJointLaw) :
    conditionalPrefixOptimum p ≤ worstCaseOptimum p.mutualInformation := by
  exact le_sSup ⟨p, rfl, rfl⟩

end InformationTheory
