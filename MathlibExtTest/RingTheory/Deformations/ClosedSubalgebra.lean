/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Deformations.ClosedSubalgebra
import MathlibExt.RingTheory.Deformations.ConjQuotSubfunctor

universe u

open CategoryTheory IsLocalRing Deformation ProartinianCat

/-! ### Closed subalgebras, with the original binders -/

-- `exactSource` consumer: a unit of `A` lying in a closed subalgebra is a unit there.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A : ProartinianCat 𝓞}
    (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))
    [CompactSpace A.carrier] (x : S) (hx : IsUnit (x : A.carrier)) : IsUnit x :=
  isUnit_of_isUnit_val S hS x hx

-- The inverse of `1 - m` for `m` in the maximal ideal lies in any closed set containing the
-- partial geometric sums.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A : ProartinianCat 𝓞}
    [CompactSpace A.carrier] {T : Set A.carrier} (hT : IsClosed T) {m : A.carrier}
    (hm : m ∈ maximalIdeal A) (hmem : ∀ N, (∑ i ∈ Finset.range N, m ^ i) ∈ T) :
    ∃ s ∈ T, s * (1 - m) = 1 :=
  exists_mul_one_sub_eq_one_of_isClosed hT hm hmem

-- The maximal ideal of a closed subalgebra is its intersection with that of `A`.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A : ProartinianCat 𝓞}
    [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))
    (x : S) :
    letI := ClosedSubalgebra.isLocalRing S hS
    x ∈ maximalIdeal S ↔ (x : A.carrier) ∈ maximalIdeal A :=
  ClosedSubalgebra.mem_maximalIdeal_iff_val S hS x

-- A closed subalgebra is a local proartinian algebra, with an injective inclusion.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A : ProartinianCat 𝓞}
    [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier)) :
    IsLocalProartinianAlgebra 𝓞 S ∧ Function.Injective (closedSubalgebraι S hS).hom :=
  ⟨ClosedSubalgebra.isLocalProartinianAlgebra S hS, closedSubalgebraι_injective S hS⟩

example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {A : ProartinianCat 𝓞}
    [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))
    (x : S) : (closedSubalgebraι S hS).hom x = (x : A.carrier) := by
  simp

-- The trace algebra of a representation maps to `A` with image the trace subalgebra.
example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
    {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) (g : G) :
    ∃ t : TraceAlgebra.obj ρ,
      (TraceAlgebra.ι ρ).hom t = Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier) :=
  ⟨⟨_, trace_mem_traceSubalgebra ρ g⟩, rfl⟩

/-! ### Images of lifting conditions, with the original binders -/

example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} (q : (repnQuotFunctor n G 𝓞).obj R) :
    q ∈ (conjQuotSubfunctor n F).obj R ↔
      ∃ ρ' ∈ F.obj R, (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) = q :=
  mem_conjQuotSubfunctor_obj_iff n q

example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {F F' : Subfunctor (repnFunctor n G 𝓞)}
    (h : F ≤ F') : conjQuotSubfunctor n F ≤ conjQuotSubfunctor n F' :=
  conjQuotSubfunctor_mono n h

example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] (F : Subfunctor (repnFunctor n G 𝓞))
    (R : ProartinianCat 𝓞) :
    Function.Surjective ((condLiftToDeformation n F).app R) :=
  condLiftToDeformation_surjective n F R

-- The whole representation functor is stable under strict equivalence and reflected by
-- injective morphisms.
example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] :
    ConjStable n (⊤ : Subfunctor (repnFunctor n G 𝓞)) ∧
      ReflectedByInjective n (⊤ : Subfunctor (repnFunctor n G 𝓞)) :=
  ⟨fun _ _ _ ↦ trivial, fun _ _ _ _ ↦ trivial⟩

-- Traces are invariant under conjugation.
example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] {A : ProartinianCat 𝓞} (γ : ConjAct (GL n A.carrier))
    (ρ : G →ₜ* GL n A) (g : G) :
    Matrix.trace (((γ • ρ) g : GL n A.carrier) : Matrix n n A.carrier) =
      Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier) :=
  trace_smul_eq γ ρ g

/-! ### Higher-universe consumers -/

example {n : Type 2} [Fintype n] [DecidableEq n] {G : Type 1} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] (F : Subfunctor (repnFunctor n G 𝓞))
    (R : ProartinianCat 𝓞) :
    Function.Surjective ((condLiftToDeformation n F).app R) :=
  condLiftToDeformation_surjective n F R

noncomputable example {n : Type 2} [Fintype n] [DecidableEq n] {G : Type 1} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
    {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) :
    TraceAlgebra.obj ρ ⟶ A :=
  TraceAlgebra.ι ρ

/-! ### Residue fields -/

-- For a finite field `K`, the residue field object is terminal and compact; its topology is
-- discrete, so every subalgebra is closed and `closedSubalgebraObj` applies to `⊤`.
noncomputable example {K : Type u} [Field K] : Limits.IsTerminal (residueField (𝓞 := K)) :=
  isTerminalResidueField

example {K : Type u} [Field K] [Finite K] : CompactSpace (residueField (𝓞 := K)) := by
  have : Finite (ResidueField K) := .of_surjective _ residue_surjective
  infer_instance

noncomputable example {K : Type u} [Field K] [Finite K] : ProartinianCat K :=
  haveI : Finite (ResidueField K) := .of_surjective _ residue_surjective
  closedSubalgebraObj (⊤ : Subalgebra K (residueField (𝓞 := K))) (isClosed_discrete _)
