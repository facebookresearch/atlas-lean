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

/-- **Finite joint law.** A finite joint law consists of positive integers $n_X$ and $n_Y$
and a probability distribution on $\{0, \dots, n_X - 1\} \times \{0, \dots, n_Y - 1\}$. -/
structure FiniteJointLaw where
  nx : ℕ
  ny : ℕ
  nx_pos : 0 < nx
  ny_pos : 0 < ny
  law : PMF (Fin nx × Fin ny)

/-- **Input law.** The input law of a finite joint law $p$ on
$\{0, \dots, n_X - 1\} \times \{0, \dots, n_Y - 1\}$ is its first marginal: the law on
$\{0, \dots, n_X - 1\}$ that is the image of $p$ under $(x, y) \mapsto x$. -/
noncomputable def FiniteJointLaw.inputLaw (p : FiniteJointLaw) : PMF (Fin p.nx) :=
  p.law.map Prod.fst

/-- **Output law.** The output law of a finite joint law $p$ of an input $X$ and an output $Y$
is the law of $Y$: the marginal of $p$ on the output alphabet, obtained by pushing $p$ forward
along the projection onto the second coordinate. -/
noncomputable def FiniteJointLaw.outputLaw (p : FiniteJointLaw) : PMF (Fin p.ny) :=
  p.law.map Prod.snd

/-- **Mutual information.** The mutual information of a finite joint law $p$ of $(X, Y)$ is
$I(X; Y) = H(X) + H(Y) - H(X, Y)$, where $H(X)$ and $H(Y)$ are the Shannon entropies in bits
of the input and output laws of $p$, and $H(X, Y)$ is the Shannon entropy in bits of $p$. -/
noncomputable def FiniteJointLaw.mutualInformation (p : FiniteJointLaw) : ℝ :=
  shannonEntropy p.inputLaw + shannonEntropy p.outputLaw - shannonEntropy p.law

/-- **Finite extension of a joint law.** A finite extension of a finite joint law $p$ on
$\{0, \dots, n_X - 1\} \times \{0, \dots, n_Y - 1\}$ consists of a positive integer $n_S$ and a
probability law on triples $(x, y, s)$ with $s \in \{0, \dots, n_S - 1\}$ whose marginal on the
pairs $(x, y)$ is exactly $p$. -/
structure FiniteExtension (p : FiniteJointLaw) where
  ns : ℕ
  ns_pos : 0 < ns
  law : PMF ((Fin p.nx × Fin p.ny) × Fin ns)
  marginal_eq : law.map Prod.fst = p.law

/-- **Trivial extension.** The trivial extension of a finite joint law $p$ of an input $X$ and an
output $Y$ has the one-letter auxiliary alphabet $\{0\}$ and, as its law, the law of
$((X, Y), 0)$ for $(X, Y)$ distributed according to $p$; its $(X, Y)$ marginal is $p$. -/
noncomputable def FiniteExtension.trivial (p : FiniteJointLaw) : FiniteExtension p where
  ns := 1
  ns_pos := Nat.zero_lt_succ 0
  law := p.law.map (fun z => (z, (0 : Fin 1)))
  marginal_eq := by
    rw [PMF.map_comp]
    exact PMF.map_id p.law

/-- **Auxiliary marginal of an extension.** For a finite extension $q$ of a finite joint law $p$,
viewed as the law of a triple $(X, Y, S)$ with $S$ taking values in $\{0, \dots, n_S - 1\}$, the
auxiliary law is the marginal law of $S$ under $q$. -/
noncomputable def FiniteExtension.auxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin q.ns) :=
  q.law.map Prod.snd

/-- **Input-auxiliary law.** Let $q$ be a finite extension of a finite joint law of $(X, Y)$,
that is, a law of $((X, Y), S)$ with an auxiliary variable $S$. Its input-auxiliary law is the
joint law of $(X, S)$: the image of the law of $q$ under $((x, y), s) \mapsto (x, s)$. -/
noncomputable def FiniteExtension.inputAuxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin p.nx × Fin q.ns) :=
  q.law.map (fun z => (z.1.1, z.2))

/-- **Output-auxiliary law.** Let $q$ be a finite extension of a finite joint law of $(X, Y)$,
that is, a law of $((X, Y), S)$ with an auxiliary variable $S$. Its output-auxiliary law is the
joint law of $(Y, S)$: the image of the law of $q$ under $((x, y), s) \mapsto (y, s)$. -/
noncomputable def FiniteExtension.outputAuxiliaryLaw {p : FiniteJointLaw}
    (q : FiniteExtension p) : PMF (Fin p.ny × Fin q.ns) :=
  q.law.map (fun z => (z.1.2, z.2))

/-- **Mutual information between the input and the auxiliary.** For a finite extension $q$ of a
finite joint law $p$, viewed as the law of a triple $(X, Y, S)$ whose $(X, Y)$ marginal is $p$,
this is $I(X; S) = H(X) + H(S) - H(X, S)$, where $H(X)$ is the Shannon entropy in bits of the
$X$ marginal of $p$, and $H(S)$ and $H(X, S)$ are the Shannon entropies in bits of the $S$ and
$(X, S)$ marginals of $q$. -/
noncomputable def FiniteExtension.auxiliaryInformation {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy p.inputLaw + shannonEntropy q.auxiliaryLaw -
    shannonEntropy q.inputAuxiliaryLaw

/-- **Conditional entropy of the output given the auxiliary.** For a finite extension $q$ of a
finite joint law $p$, viewed as the law of a triple $(X, Y, S)$ whose $(X, Y)$ marginal is $p$,
this is $H(Y \mid S) = H(Y, S) - H(S)$, where $H(Y, S)$ and $H(S)$ are the Shannon entropies in
bits of the $(Y, S)$ and $S$ marginals of $q$. -/
noncomputable def FiniteExtension.conditionalEntropy {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy q.outputAuxiliaryLaw - shannonEntropy q.auxiliaryLaw

/-- **Conditional entropy of the output given the input and the auxiliary.** For a finite
extension of a finite joint law, with input $X$, output $Y$ and auxiliary $S$, the conditional
entropy of $Y$ given $(X, S)$ is $H(Y \mid X, S) = H(X, Y, S) - H(X, S)$, where $H$ denotes
Shannon entropy in bits, $H(X, Y, S)$ is the entropy of the law of the extension and $H(X, S)$
is the entropy of its $(X, S)$ marginal.

It vanishes exactly when $Y$ is almost surely a deterministic function of $(X, S)$. -/
noncomputable def FiniteExtension.outputGivenInputAuxiliaryEntropy {p : FiniteJointLaw}
    (q : FiniteExtension p) : ℝ :=
  shannonEntropy q.law - shannonEntropy q.inputAuxiliaryLaw

/-- **Zero output entropy given input and auxiliary for a one-letter output.** Let $p$ be a
finite joint law of an input $X$ and an output $Y$ whose output alphabet has exactly one letter.
Then for every finite extension of $p$ by an auxiliary $S$, the conditional entropy
$H(Y \mid X, S)$ of the output given the input and the auxiliary is $0$. -/
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

/-- **Auxiliary law of the trivial extension.** For every finite joint law $p$, the auxiliary law
of the trivial extension of $p$ is the point mass at $0$, the only letter of its one-letter
auxiliary alphabet $\{0\}$. -/
@[simp] theorem FiniteExtension.trivial_auxiliaryLaw (p : FiniteJointLaw) :
    (FiniteExtension.trivial p).auxiliaryLaw = PMF.pure (0 : Fin 1) := by
  change (p.law.map (fun z => (z, (0 : Fin 1)))).map Prod.snd = PMF.pure 0
  rw [PMF.map_comp]
  exact PMF.map_const p.law (0 : Fin 1)

/-- **The trivial extension has zero auxiliary information.** For every finite joint law $p$, the
mutual information $I(X; S)$ between the input $X$ and the auxiliary $S$ in the trivial extension
of $p$, whose auxiliary alphabet has a single letter, is $0$. -/
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

/-- **Conditional entropy in the trivial extension.** For every finite joint law $p$ of an input
$X$ and an output $Y$, the conditional entropy $H(Y \mid S)$ of the output given the auxiliary
$S$ in the trivial extension of $p$ equals the Shannon entropy $H(Y)$ of the output law of $p$. -/
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

/-- **Input marginal of the input-auxiliary law.** Let $q$ be a finite extension of a finite
joint law $p$ of $(X, Y)$ by an auxiliary variable $S$. Then the marginal of $X$ under the
joint law of $(X, S)$ in $q$ equals the law of $X$ under $p$. -/
@[simp] theorem FiniteExtension.inputAuxiliaryLaw_map_fst {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.inputAuxiliaryLaw.map Prod.fst = p.inputLaw := by
  change (q.law.map (fun z => (z.1.1, z.2))).map Prod.fst = p.law.map Prod.fst
  rw [PMF.map_comp]
  simpa [PMF.map_comp, Function.comp_def] using congrArg (PMF.map Prod.fst) q.marginal_eq

/-- **Output marginal of the output-auxiliary law.** Let $q$ be a finite extension of a finite
joint law $p$ of $(X, Y)$ by an auxiliary variable $S$. Then the marginal of $Y$ under the
joint law of $(Y, S)$ in $q$ equals the law of $Y$ under $p$. -/
@[simp] theorem FiniteExtension.outputAuxiliaryLaw_map_fst {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.outputAuxiliaryLaw.map Prod.fst = p.outputLaw := by
  change (q.law.map (fun z => (z.1.2, z.2))).map Prod.fst = p.law.map Prod.snd
  rw [PMF.map_comp]
  simpa [PMF.map_comp, Function.comp_def] using congrArg (PMF.map Prod.snd) q.marginal_eq

/-- **Auxiliary marginal of the input-auxiliary law.** Let $q$ be a finite extension of a
finite joint law of $(X, Y)$ by an auxiliary variable $S$. Then the marginal of $S$ under the
joint law of $(X, S)$ in $q$ equals the law of $S$ in $q$. -/
@[simp] theorem FiniteExtension.inputAuxiliaryLaw_map_snd {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.inputAuxiliaryLaw.map Prod.snd = q.auxiliaryLaw := by
  simp [FiniteExtension.inputAuxiliaryLaw, FiniteExtension.auxiliaryLaw,
    PMF.map_comp, Function.comp_def]

/-- **Auxiliary marginal of the output-auxiliary law.** Let $q$ be a finite extension of a
finite joint law of $(X, Y)$ by an auxiliary variable $S$. Then the marginal of $S$ under the
joint law of $(Y, S)$ in $q$ equals the law of $S$ in $q$. -/
@[simp] theorem FiniteExtension.outputAuxiliaryLaw_map_snd {p : FiniteJointLaw}
    (q : FiniteExtension p) : q.outputAuxiliaryLaw.map Prod.snd = q.auxiliaryLaw := by
  simp [FiniteExtension.outputAuxiliaryLaw, FiniteExtension.auxiliaryLaw,
    PMF.map_comp, Function.comp_def]

/-- **Conditional entropy vanishes for a one-letter output.** If the output alphabet of a finite
joint law $p$ of $(X, Y)$ has exactly one element, then for every finite extension of $p$ by an
auxiliary variable $S$, the conditional entropy $H(Y \mid S)$ is $0$. -/
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

/-- **Conditional-prefix optimum of a joint law.** For a finite joint law $p$ of $(X, Y)$, this
is the infimum in the extended reals of the conditional entropy $H(Y \mid S)$ in bits over all
finite extensions of $p$ by an auxiliary variable $S$ such that $I(X; S) = 0$ and
$H(Y \mid X, S) = 0$. The infimum of the empty set is $+\infty$.

Source: Li, arXiv:2501.13736v4, equation cs_h_c. -/
noncomputable def conditionalPrefixOptimum (p : FiniteJointLaw) : EReal :=
  sInf {h | ∃ q : FiniteExtension p, q.auxiliaryInformation = 0 ∧
    q.outputGivenInputAuxiliaryEntropy = 0 ∧
    h = (q.conditionalEntropy : EReal)}

/-- **Worst-case conditional-prefix optimum.** For a real number $t$, the worst-case optimum at
$t$ is the supremum, taken in the extended reals, of the conditional-prefix optimum of $p$ over
all finite joint laws $p$ of an input $X$ and an output $Y$ whose mutual information $I(X; Y)$,
in bits, equals $t$; it is $-\infty$ when no such law exists. -/
noncomputable def worstCaseOptimum (t : ℝ) : EReal :=
  sSup {h | ∃ p : FiniteJointLaw, p.mutualInformation = t ∧ h = conditionalPrefixOptimum p}

/-- **Channel simulation constant.** The constant $c_c^*$ is the limit superior in the extended
reals, as the real number $t$ tends to $+\infty$, of $W(t) - t - \log_2 t$, where $W(t)$ is the
worst-case optimum at $t$: the supremum of the conditional-prefix optimum over all finite joint
laws whose mutual information in bits is exactly $t$.

Source: Li, arXiv:2501.13736v4, definition of c_c*. -/
noncomputable def channelSimulationConstant : EReal :=
  Filter.limsup (fun t : ℝ => worstCaseOptimum t - (t : EReal) -
    (Real.log t / Real.log 2 : EReal)) Filter.atTop

/-- **Uniform outer constant for channel simulation.** A real number $\alpha$ is a uniform
outer constant when there is a real $\beta > 0$ such that for every finite joint law $p$ of
$(X, Y)$ there is a finite extension of $p$ by an auxiliary variable $S$ with $I(X; S) = 0$
and $H(Y \mid X, S) = 0$ and
$$H(Y \mid S) \le I(X; Y) + \log_2\bigl(I(X; Y) + \beta\bigr) + \alpha,$$
where all entropies and mutual informations are in bits and are computed from the law of
$(X, Y, S)$ in the extension. -/
def HasUniformOuterConstant (α : ℝ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ p : FiniteJointLaw, ∃ q : FiniteExtension p,
    q.auxiliaryInformation = 0 ∧ q.outputGivenInputAuxiliaryEntropy = 0 ∧
    q.conditionalEntropy ≤ p.mutualInformation +
      Real.log (p.mutualInformation + β) / Real.log 2 + α

/-- **Infimum of the uniform outer constants.** Call a real number $\alpha$ a uniform outer
constant when there is a real $\beta > 0$ such that every finite joint law $p$ of an input $X$
and an output $Y$ has a finite extension by an auxiliary $S$ with $I(X; S) = 0$,
$H(Y \mid X, S) = 0$ and $H(Y \mid S) \le I(X; Y) + \log_2(I(X; Y) + \beta) + \alpha$, where
entropies and mutual informations are in bits. This is the infimum of the set of uniform outer
constants, taken in the extended reals, so it is $+\infty$ when there is none. -/
noncomputable def uniformOuterConstantInfimum : EReal :=
  sInf {h | ∃ α : ℝ, HasUniformOuterConstant α ∧ h = (α : EReal)}

/-- **Each admissible extension bounds the conditional-prefix optimum.** Let $p$ be a finite
joint law of $(X, Y)$ and let $q$ be a finite extension of $p$ by an auxiliary variable $S$ with
$I(X; S) = 0$ and $H(Y \mid X, S) = 0$. Then the conditional-prefix optimum of $p$ is at most
the conditional entropy $H(Y \mid S)$ of $q$. -/
theorem conditionalPrefixOptimum_le {p : FiniteJointLaw} (q : FiniteExtension p)
    (hq : q.auxiliaryInformation = 0)
    (hqrec : q.outputGivenInputAuxiliaryEntropy = 0) :
    conditionalPrefixOptimum p ≤ (q.conditionalEntropy : EReal) := by
  exact sInf_le ⟨q, hq, hqrec, rfl⟩

/-- **The conditional-prefix optimum vanishes for a one-letter output.** If the output alphabet
of a finite joint law $p$ has exactly one element, then the conditional-prefix optimum of $p$
equals $0$. -/
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

/-- **The worst-case optimum dominates each conditional-prefix optimum.** For every finite joint
law $p$ of $(X, Y)$, the conditional-prefix optimum of $p$ is at most the worst-case optimum at
$t = I(X; Y)$, the mutual information of $p$ in bits. -/
theorem conditionalPrefixOptimum_le_worstCaseOptimum (p : FiniteJointLaw) :
    conditionalPrefixOptimum p ≤ worstCaseOptimum p.mutualInformation := by
  exact le_sSup ⟨p, rfl, rfl⟩

end InformationTheory
