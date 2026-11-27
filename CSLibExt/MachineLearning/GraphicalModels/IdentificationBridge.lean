/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import MathlibExt.Probability.WeightLaw
public import MathlibExt.Probability.Statistics.Identifiability

/-!
# The identification bridge: `IdentifiedOn` versus `IsIdentifiedBy`

`IdentifiedOn C obs Q` (in `Identifiability.lean`) says a functional `Q` is
determined by the observation `obs` on a model class `C`;
`MathlibExt.Probability.Statistics.IsIdentifiedBy P τ` says a real-valued
estimand `τ` is determined by the observation law `P`. This file transports
identification results between the two notions:

* on the full parameter space the two are equivalent
  (`identifiedOn_univ_iff_isIdentifiedBy`);
* a class `C` is the full space of its subtype, and post-composing the
  observation with a map injective on the observed values preserves
  identification (`identifiedOn_iff_univ_subtype`, `identifiedOn_comp_iff`);
* combining the two transports identification on `C` to
  `IsIdentifiedBy` on the subtype (`identifiedOn_iff_isIdentifiedBy_subtype`);
* for Bayesian networks the observation is the joint law, encoded as a
  measure by `weightLaw`, which is injective on nonnegative weights
  (`weightLaw_injOn_nonneg`), so the back-door and front-door criteria of
  `Identifiability.lean` yield `IsIdentifiedBy` statements
  (`BayesNet.isIdentifiedBy_backdoorClass`,
  `BayesNet.isIdentifiedBy_frontdoorClass`).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels
open MeasureTheory Finset
open MathlibExt.Probability (weightLaw)
open MathlibExt.Probability.Statistics (IsIdentifiedBy)

/-- On the full parameter space, `IdentifiedOn` is `IsIdentifiedBy`: the two trivial
membership premises in `IdentifiedOn Set.univ P τ` carry no content. -/
theorem identifiedOn_univ_iff_isIdentifiedBy {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) :
    IdentifiedOn (Set.univ : Set Θ) P τ ↔ IsIdentifiedBy P τ := by
  constructor
  · intro h θ θ' hθ
    exact h θ (Set.mem_univ θ) θ' (Set.mem_univ θ') hθ
  · intro h m _ m' _ hP
    exact h m m' hP

/-- A class is the full parameter space of its subtype, with the observation and the
functional restricted along the subtype coercion. -/
theorem identifiedOn_iff_univ_subtype {M O R : Type*} (C : Set M) (obs : M → O) (Q : M → R) :
    IdentifiedOn C obs Q ↔
      IdentifiedOn (Set.univ : Set C) (fun m : C => obs m) (fun m : C => Q m) := by
  constructor
  · intro h m _ m' _ hobs
    exact h m.1 m.2 m'.1 m'.2 hobs
  · intro h m hm m' hm' hobs
    exact h ⟨m, hm⟩ (Set.mem_univ _) ⟨m', hm'⟩ (Set.mem_univ _) hobs

/-- Post-composing the observation with a map injective on the observed values of the
class does not change identification. -/
theorem identifiedOn_comp_iff {M O O' R : Type*} {C : Set M} {obs : M → O} {e : O → O'}
    (he : Set.InjOn e (obs '' C)) (Q : M → R) :
    IdentifiedOn C (fun m => e (obs m)) Q ↔ IdentifiedOn C obs Q := by
  constructor
  · intro h m hm m' hm' hobs
    exact h m hm m' hm' (congrArg e hobs)
  · intro h m hm m' hm' hcomp
    exact h m hm m' hm' (he ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩ hcomp)

/-- Identification on a class `C` by an observation `obs` is identification on the subtype
`↥C` by the encoded observation `e ∘ obs`, when the encoding `e` into measures is injective
on the observed values. -/
theorem identifiedOn_iff_isIdentifiedBy_subtype {M O X : Type*} [MeasurableSpace X]
    {C : Set M} {obs : M → O} {e : O → Measure X} (he : Set.InjOn e (obs '' C)) (Q : M → ℝ) :
    IdentifiedOn C obs Q ↔ IsIdentifiedBy (fun m : C => e (obs m)) (fun m : C => Q m) := by
  constructor
  · intro h m m' hcomp
    exact h m.1 m.2 m'.1 m'.2 (he ⟨m.1, m.2, rfl⟩ ⟨m'.1, m'.2, rfl⟩ hcomp)
  · intro h m hm m' hm' hobs
    exact h ⟨m, hm⟩ ⟨m', hm'⟩ (congrArg e hobs)

/-- For Bayesian networks on the full model space, identification by the joint weight is
identification by the encoded joint law `weightLaw b.joint`. -/
theorem BayesNet.identifiedOn_univ_joint_iff_isIdentifiedBy {α : Type*} [Fintype α]
    [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (Q : BayesNet α n → ℝ) :
    IdentifiedOn (Set.univ : Set (BayesNet α n)) (fun b => b.joint) Q ↔
      IsIdentifiedBy (fun b : BayesNet α n => weightLaw b.joint) Q := by
  have he : Set.InjOn weightLaw ((fun b : BayesNet α n => b.joint) '' Set.univ) := by
    intro g hg g' hg' hgg
    obtain ⟨b, -, rfl⟩ := hg
    obtain ⟨b', -, rfl⟩ := hg'
    have hb : ∀ x, 0 ≤ b.joint x := fun x => b.toChain.joint_nonneg n x
    have hb' : ∀ x, 0 ≤ b'.joint x := fun x => b'.toChain.joint_nonneg n x
    show b.joint = b'.joint
    funext x
    have h : (weightLaw b.joint).real {x} = (weightLaw b'.joint).real {x} := by rw [hgg]
    rwa [MathlibExt.Probability.measureReal_weightLaw_singleton hb x,
      MathlibExt.Probability.measureReal_weightLaw_singleton hb' x] at h
  exact (identifiedOn_comp_iff he Q).symm.trans (identifiedOn_univ_iff_isIdentifiedBy _ _)

/-- `weightLaw` is injective on the image of BayesNet joints, since joints are
nonnegative. -/
theorem weightLaw_injOn_joint_image {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {n : ℕ} (C : Set (BayesNet α n)) :
    Set.InjOn weightLaw ((fun b : BayesNet α n => b.joint) '' C) := by
  intro g hg g' hg' hgg
  obtain ⟨b, -, rfl⟩ := hg
  obtain ⟨b', -, rfl⟩ := hg'
  exact MathlibExt.Probability.weightLaw_injOn_nonneg (fun x => b.toChain.joint_nonneg n x)
    (fun x => b'.toChain.joint_nonneg n x) hgg

namespace BayesNet
/-- The back-door criterion of `Identifiability.lean` as an `IsIdentifiedBy` statement on
the back-door model class, with networks observed through the encoded joint law. -/
theorem isIdentifiedBy_backdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (Z : Finset (Fin n)) (a v : α)
    (hky : k ≠ y) (hyZ : y ∉ Z) :
    IsIdentifiedBy
      (fun b : backdoorClass pa k y Z a => weightLaw (b : BayesNet α n).joint)
      (fun b => ∑ x with x y = v, ((b : BayesNet α n).intervene k a).joint x) := by
  have he := weightLaw_injOn_joint_image (backdoorClass pa k y Z a)
  exact (identifiedOn_iff_isIdentifiedBy_subtype he _).mp
    (BayesNet.identifiedOn_backdoorClass pa k y Z a v hky hyZ)

-- `(α := α)` pins the value type, which no argument of `frontdoorClass` mentions.
/-- The front-door criterion of `Identifiability.lean` as an `IsIdentifiedBy` statement on
the front-door model class, with networks observed through the encoded joint law. -/
theorem isIdentifiedBy_frontdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (M : Finset (Fin n)) (a v : α)
    (hky : k ≠ y) (hkM : k ∉ M) (hyM : y ∉ M) :
    IsIdentifiedBy
      (fun b : frontdoorClass (α := α) pa k y M => weightLaw (b : BayesNet α n).joint)
      (fun b => ∑ x with x y = v, ((b : BayesNet α n).intervene k a).joint x) := by
  have he := weightLaw_injOn_joint_image (frontdoorClass (α := α) pa k y M)
  exact (identifiedOn_iff_isIdentifiedBy_subtype he _).mp
    (BayesNet.identifiedOn_frontdoorClass pa k y M a v hky hkM hyM)
end BayesNet

end Cslib.MachineLearning.GraphicalModels
