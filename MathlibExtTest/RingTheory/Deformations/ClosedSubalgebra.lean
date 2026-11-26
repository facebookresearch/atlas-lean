/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Deformations.ClosedSubalgebra
import MathlibExt.RingTheory.Deformations.ConjQuotSubfunctor
import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Topology.Instances.ZMod

universe u

open CategoryTheory IsLocalRing Deformation ProartinianCat

/-! ### Proartinian rings, residue algebras and finiteness -/

example {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] : IsProartinian R ↔ IsArtinianRing R :=
  isProartinian_iff_isArtinianRing

-- Every open ideal contains a power of the maximal ideal.
example {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsProartinian R] (I : Ideal R) (hI : IsOpen (X := R) I) :
    ∃ n, maximalIdeal R ^ n ≤ I :=
  exists_maximalIdeal_pow_le_of_isProartinian I hI

-- Continuous ring maps between proartinian local rings are local.
example {R S : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsProartinian R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S]
    [IsProartinian S] (f : R →+* S) (hf : Continuous f) : IsLocalHom f :=
  isLocalHom_of_isContinuous_of_isProartinian f hf

-- An artinian local ring with finite residue field is finite.
example (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    [Finite (ResidueField R)] : Finite R :=
  IsArtinianRing.finite_of_finite_residueField R

-- The residue fields of `𝓞` and of a local proartinian `𝓞`-algebra `A` are isomorphic, through
-- the map induced by `algebraMap 𝓞 A`.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] (A : ProartinianCat 𝓞) (x : 𝓞) :
    IsResidueAlgebra.algEquiv 𝓞 A (residue 𝓞 x) = residue A (algebraMap 𝓞 A x) :=
  rfl

/-! ### A concrete coefficient ring: `ZMod 4` with the discrete topology

`ZMod 4` is written `ZMod (2 ^ 2)`, so that Mathlib's local-ring instance for `ZMod (p ^ r)`
applies. It is a proartinian local ring that is not a field. -/

private theorem two_mem_maximalIdeal_zmod_four : (2 : ZMod (2 ^ 2)) ∈ maximalIdeal _ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_exists_inv]
  rintro ⟨b, hb⟩
  revert b
  decide

example : (2 : ZMod (2 ^ 2)) ≠ 0 := by decide

example : IsProartinian (ZMod (2 ^ 2)) :=
  isProartinian_iff_isArtinianRing.mpr inferInstance

-- Its maximal ideal is nilpotent, since `⊥` is open.
example : ∃ n, maximalIdeal (ZMod (2 ^ 2)) ^ n ≤ ⊥ :=
  exists_maximalIdeal_pow_le_of_isProartinian ⊥ (isOpen_discrete _)

-- The reduction map `ZMod 4 → ZMod 2` is local.
example : IsLocalHom (ZMod.castHom (show 2 ∣ 2 ^ 2 by norm_num) (ZMod 2)) :=
  isLocalHom_of_isContinuous_of_isProartinian _ continuous_of_discreteTopology

-- `ZMod 4` is a local proartinian algebra over itself, and its reduction to the residue field
-- kills `2`.
private instance isLocalProartinianAlgebra_zmod_four :
    IsLocalProartinianAlgebra (ZMod (2 ^ 2)) (ZMod (2 ^ 2)) := {}

-- `ZMod 4` as an object of `ProartinianCat (ZMod 4)`, and its residue field.
private abbrev R₄ : ProartinianCat (ZMod (2 ^ 2)) := ProartinianCat.of (ZMod (2 ^ 2)) (ZMod (2 ^ 2))

private abbrev K₂ : Type := (residueField (𝓞 := ZMod (2 ^ 2))).carrier

private theorem reduce_two : (toResidueField R₄).hom 2 = 0 := by
  rw [← RingHom.mem_ker, ker_toResidueField]
  exact two_mem_maximalIdeal_zmod_four

private theorem two_eq_zero_residue : (2 : K₂) = 0 := by
  have h := reduce_two
  rwa [map_ofNat] at h

/-! ### Strict equivalence over `ZMod 4`

Strict equivalence is conjugation by a matrix that reduces to the identity. The representations
below are of `Multiplicative ℤ`, sending its generator to a given matrix over `ZMod 4`:
* `S = !![0, 1; 1, 0]` and `U * S * U⁻¹ = !![2, 1; 1, 2]`, with `U = !![1, 2; 0, 1]` reducing to
  the identity, are distinct order-two matrices that give the same strict equivalence class;
* the trivial and the sign character in rank one have the same reduction, but are not strictly
  equivalent;
* `S` and `V * S * V⁻¹ = !![3, 1; 0, 1]`, with `V = !![1, 0; 1, 1]`, are conjugate in `GL₂`, but
  their reductions differ, so they are not strictly equivalent either. -/

private def glS : GL (Fin 2) R₄ := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

private def glU : GL (Fin 2) R₄ := ⟨!![1, 2; 0, 1], !![1, 2; 0, 1], by decide, by decide⟩

private def glUSU : GL (Fin 2) R₄ := ⟨!![2, 1; 1, 2], !![2, 1; 1, 2], by decide, by decide⟩

private def glV : GL (Fin 2) R₄ := ⟨!![1, 0; 1, 1], !![1, 0; 3, 1], by decide, by decide⟩

private def glVSV : GL (Fin 2) R₄ := ⟨!![3, 1; 0, 1], !![3, 1; 0, 1], by decide, by decide⟩

private def rep₂ (M : GL (Fin 2) R₄) : Multiplicative ℤ →ₜ* GL (Fin 2) R₄ :=
  ⟨zpowersHom _ M, continuous_of_discreteTopology⟩

private theorem rep₂_apply (M : GL (Fin 2) R₄) (x : Multiplicative ℤ) :
    rep₂ M x = M ^ Multiplicative.toAdd x :=
  rfl

private theorem conj_rep₂ (γ M M' : GL (Fin 2) R₄) (h : γ * M * γ⁻¹ = M') :
    ConjAct.toConjAct γ • rep₂ M = rep₂ M' := by
  ext1 x
  rw [conjAct_smul_apply, ConjAct.ofConjAct_toConjAct, rep₂_apply, rep₂_apply, ← conj_zpow, h]

example : glS * glS = 1 ∧ glUSU * glUSU = 1 ∧ glS ≠ glUSU := by
  refine ⟨Units.ext (by decide), Units.ext (by decide), fun h => ?_⟩
  have := congrArg (fun g : GL (Fin 2) R₄ => (g : Matrix (Fin 2) (Fin 2) R₄) 0 0) h
  exact absurd this (by decide)

private theorem glU_mem_conjKer : ConjAct.toConjAct glU ∈ conjKer (n := Fin 2) R₄ := by
  rw [mem_conjKer_iff, ConjAct.ofConjAct_toConjAct]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, glU]
  exact reduce_two

-- Conjugation by `U` identifies the representations given by `S` and `U * S * U⁻¹`.
example : (Quotient.mk'' (rep₂ glS) :
      (repnQuotFunctor (Fin 2) (Multiplicative ℤ) (ZMod (2 ^ 2))).obj R₄) =
    Quotient.mk'' (rep₂ glUSU) := by
  change (Quotient.mk'' (rep₂ glS) : MulAction.orbitRel.Quotient (conjKer (n := Fin 2) R₄) _) =
    Quotient.mk'' (rep₂ glUSU)
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨⟨_, glU_mem_conjKer⟩, conj_rep₂ glU glUSU glS (Units.ext (by decide))⟩))

private def sign₁ : Multiplicative ℤ →ₜ* GL (Fin 1) R₄ :=
  ⟨zpowersHom _ (-1), continuous_of_discreteTopology⟩

private theorem map_neg_one :
    Matrix.GeneralLinearGroup.map (toResidueField R₄).hom.toRingHom (-1 : GL (Fin 1) R₄) = 1 := by
  ext i j
  fin_cases i; fin_cases j
  rw [Matrix.GeneralLinearGroup.map_apply]
  change (toResidueField R₄).hom (-1) = (1 : K₂)
  rw [map_neg, map_one, neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_eq_zero_residue]

-- The trivial and the sign character have the same reduction.
example : (repnFunctor (Fin 1) (Multiplicative ℤ) (ZMod (2 ^ 2))).map (toResidueField R₄) sign₁ =
    (repnFunctor (Fin 1) (Multiplicative ℤ) (ZMod (2 ^ 2))).map (toResidueField R₄)
      (1 : Multiplicative ℤ →ₜ* GL (Fin 1) R₄) := by
  refine ContinuousMonoidHom.ext fun x => ?_
  rw [repnFunctor_map, repnFunctor_map, ContinuousMonoidHom.coe_one, Pi.one_apply, map_one]
  change Matrix.GeneralLinearGroup.map _ ((-1 : GL (Fin 1) R₄) ^ Multiplicative.toAdd x) = 1
  rw [map_zpow, map_neg_one, one_zpow]

-- They are not strictly equivalent: conjugation fixes the trivial character.
example : (Quotient.mk'' sign₁ :
      (repnQuotFunctor (Fin 1) (Multiplicative ℤ) (ZMod (2 ^ 2))).obj R₄) ≠
    Quotient.mk'' 1 := by
  change (Quotient.mk'' sign₁ : MulAction.orbitRel.Quotient (conjKer (n := Fin 1) R₄) _) ≠
    Quotient.mk'' 1
  intro h
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  have h1 : ConjAct.ofConjAct (γ : ConjAct (GL (Fin 1) R₄)) *
      (1 : Multiplicative ℤ →ₜ* GL (Fin 1) R₄) (Multiplicative.ofAdd 1) *
      (ConjAct.ofConjAct (γ : ConjAct (GL (Fin 1) R₄)))⁻¹ = sign₁ (Multiplicative.ofAdd 1) :=
    (conjAct_smul_apply (γ : ConjAct (GL (Fin 1) R₄)) 1 _).symm.trans
      (congrArg (fun ρ => ρ (Multiplicative.ofAdd 1)) hγ)
  have hs : sign₁ (Multiplicative.ofAdd 1) = -1 := zpow_one _
  rw [ContinuousMonoidHom.coe_one, Pi.one_apply, mul_one, mul_inv_cancel, hs] at h1
  have h2 := congrArg (fun g : GL (Fin 1) R₄ => (g : Matrix (Fin 1) (Fin 1) R₄) 0 0) h1
  change (1 : R₄) = -1 at h2
  exact absurd h2 (by decide)

-- `V` conjugates `S` to `V * S * V⁻¹`, but does not reduce to the identity.
example : ConjAct.toConjAct glV • rep₂ glS = rep₂ glVSV :=
  conj_rep₂ glV glS glVSV (Units.ext (by decide))

example : ConjAct.toConjAct glV ∉ conjKer (n := Fin 2) R₄ := by
  rw [mem_conjKer_iff, ConjAct.ofConjAct_toConjAct]
  intro h
  have h10 := congrArg (fun g : GL (Fin 2) K₂ => (g : Matrix (Fin 2) (Fin 2) K₂) 1 0) h
  simp [Matrix.GeneralLinearGroup.map_apply, glV] at h10

-- The representations given by `S` and `V * S * V⁻¹` are not strictly equivalent: strict
-- equivalence preserves the reduction, and their reductions differ in the top left entry.
example : (Quotient.mk'' (rep₂ glS) :
      (repnQuotFunctor (Fin 2) (Multiplicative ℤ) (ZMod (2 ^ 2))).obj R₄) ≠
    Quotient.mk'' (rep₂ glVSV) := by
  change (Quotient.mk'' (rep₂ glS) : MulAction.orbitRel.Quotient (conjKer (n := Fin 2) R₄) _) ≠
    Quotient.mk'' (rep₂ glVSV)
  intro h
  obtain ⟨⟨γ, hγ⟩, hγρ⟩ :=
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  have hx : ConjAct.ofConjAct γ * rep₂ glVSV (Multiplicative.ofAdd 1) * (ConjAct.ofConjAct γ)⁻¹ =
      rep₂ glS (Multiplicative.ofAdd 1) :=
    (conjAct_smul_apply γ (rep₂ glVSV) _).symm.trans
      (congrArg (fun ρ => ρ (Multiplicative.ofAdd 1)) hγρ)
  have hy := congrArg (Matrix.GeneralLinearGroup.map (toResidueField R₄).hom.toRingHom) hx
  rw [map_mul, map_mul, map_inv, (mem_conjKer_iff _ _).mp hγ, one_mul, inv_one, mul_one] at hy
  have h00 := congrArg (fun g : GL (Fin 2) K₂ => (g : Matrix (Fin 2) (Fin 2) K₂) 0 0) hy
  change (toResidueField R₄).hom 3 = (toResidueField R₄).hom 0 at h00
  rw [map_ofNat, map_zero, show (3 : K₂) = 2 + 1 by norm_num, two_eq_zero_residue, zero_add] at h00
  exact one_ne_zero h00

/-! ### Closed subalgebras, with the original binders -/

-- A unit of `A` lying in a closed subalgebra is a unit there.
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

-- A rank-one representation descends to its trace subalgebra, with `γ = 1`: its only matrix
-- entry is its trace.
example {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {G : Type u} [Group G] [TopologicalSpace G]
    {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL (Fin 1) A) : TraceAlgebra.Descends ρ := by
  refine ⟨1, one_mem _, fun g i j => ?_⟩
  fin_cases i; fin_cases j
  rw [one_smul]
  simpa [Matrix.trace_fin_one] using trace_mem_traceSubalgebra ρ g

/-! ### Images of representation conditions, with the original binders -/

-- The representation functor pushes the matrix entries along the coefficient map.
example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {R S : ProartinianCat 𝓞} (f : R ⟶ S)
    (ρ : G →ₜ* GL n R) (g : G) (i j : n) :
    ((DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) g : GL n S) :
      Matrix n n S) i j = f.hom (((ρ g : GL n R) : Matrix n n R) i j) :=
  rfl

-- `conjQuotSubfunctor` is Mathlib's image of a subfunctor along the quotient map.
example {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] (F : Subfunctor (repnFunctor n G 𝓞)) :
    conjQuotSubfunctor n F = F.image (toRepnQuot n G 𝓞) :=
  rfl

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
