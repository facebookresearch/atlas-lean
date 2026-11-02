/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open LinearMap (BilinForm)
open Module

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]

/-- **Double dual of a reflexive lattice.** Let $A$ be an integral domain with fraction field $K$,
let $V$ be a finite-dimensional $K$-vector space, viewed as an $A$-module through $A \subseteq K$,
and let $B$ be a nondegenerate bilinear form on $V$. Let $M$ be an $A$-lattice in $V$, that is, a
finitely generated $A$-submodule that spans $V$ over $K$, and suppose that $M$ is reflexive as an
$A$-module. Let $M^\vee = \{x \in V : B(x, y) \in A \text{ for all } y \in M\}$. Then
$\{x \in V : B(y, x) \in A \text{ for all } y \in M^\vee\} = M$.

This is the lattice analogue of the corresponding statement for the $A$-span of a $K$-basis of
$V$: no basis is needed when $M$ is reflexive as an $A$-module. -/
theorem LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isLattice
    [FiniteDimensional K V] [IsDomain A]
    (B : BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    [Submodule.IsLattice K M] [Module.IsReflexive A M] :
    B.flip.dualSubmodule (B.dualSubmodule M) = M := by
  apply le_antisymm
  · intro x hx
    -- Identify `D(M)` with the module dual via the pairing.
    let e : (B.dualSubmodule M) ≃ₗ[A] Module.Dual A M :=
      B.dualSubmoduleLinearEquiv hB M Submodule.IsLattice.span_eq_top
    -- The functional on `D(M)` cut out by `x` against `B.flip`.
    let φ : Module.Dual A (B.dualSubmodule M) :=
      B.flip.dualSubmoduleToDual (B.dualSubmodule M) ⟨x, hx⟩
    -- Transport it to the double dual and recover a lattice element by reflexivity.
    obtain ⟨m, hm⟩ :=
      (Module.bijective_dual_eval A M).2 (φ.comp e.symm.toLinearMap)
    have key : ∀ g : Module.Dual A M, φ (e.symm g) = g m := fun g => by
      have hgm := LinearMap.congr_fun hm g
      rw [Module.Dual.eval_apply, LinearMap.comp_apply] at hgm
      exact hgm.symm
    -- It suffices to show `x = m`, comparing in the flip-double dual.
    have hspan₂ : Submodule.span K (B.dualSubmodule M : Set V) = ⊤ :=
      B.dualSubmodule_span_eq_top M Submodule.IsLattice.fg
    have hinj := B.flip.dualSubmoduleToDual_injective hB.flip
      (B.dualSubmodule M) hspan₂
    have hme : (m : V) ∈ B.flip.dualSubmodule (B.dualSubmodule M) :=
      (BilinForm.le_flip_dualSubmodule (B := B)).mpr le_rfl m.2
    have hfun : (B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨x, hx⟩ =
        (B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨(m : V), hme⟩ := by
      apply LinearMap.ext
      intro z
      have h1 : φ z = (e z) m := by
        have h := key (e z)
        rw [LinearEquiv.symm_apply_apply] at h
        exact h
      have h2 : (e z) m =
          B.flip.dualSubmodulePairing ⟨(m : V), hme⟩ z := by
        apply FaithfulSMul.algebraMap_injective A K
        change algebraMap A K (B.dualSubmodulePairing z m) = _
        rw [BilinForm.dualSubmodulePairing_spec, BilinForm.dualSubmodulePairing_spec,
          BilinForm.flip_apply]
      have h3 : ((B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨x, hx⟩) z =
          φ z := rfl
      have h4 : ((B.flip.dualSubmoduleToDual (B.dualSubmodule M)) ⟨(m : V), hme⟩) z =
          B.flip.dualSubmodulePairing ⟨(m : V), hme⟩ z := rfl
      rw [h3, h4, h1, h2]
    have hveq : x = (m : V) := congrArg Subtype.val (hinj hfun)
    rw [hveq]
    exact m.2
  · exact (BilinForm.le_flip_dualSubmodule (B := B)).mpr le_rfl

/-- **Double dual of a lattice over a Dedekind domain.** Let $A$ be a Dedekind domain with
fraction field $K$, let $V$ be a finite-dimensional $K$-vector space, viewed as an $A$-module
through $A \subseteq K$, and let $B$ be a nondegenerate symmetric bilinear form on $V$. For an
$A$-submodule $N$ of $V$ write $N^\vee = \{x \in V : B(x, y) \in A \text{ for all } y \in N\}$.
If $M$ is an $A$-lattice in $V$, that is, a finitely generated $A$-submodule that spans $V$ over
$K$, then $(M^\vee)^\vee = M$.

No reflexivity hypothesis on $M$ is needed: over a Dedekind domain a finitely generated
torsion-free module is flat, hence projective, hence reflexive.

Source: ATLAS NumberTheoryI, Proposition 5.16. -/
theorem LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice
    [FiniteDimensional K V] [IsDedekindDomain A]
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    (M : Submodule A V) [Submodule.IsLattice K M] :
    B.dualSubmodule (B.dualSubmodule M) = M := by
  have : Module.IsTorsionFree A V :=
    Module.IsTorsionFree.trans_faithfulSMul A K V
  have : Module.FinitePresentation A M :=
    Module.finitePresentation_of_finite A M
  have : Module.Projective A M :=
    Module.Flat.projective_of_finitePresentation
  have hflip : B.flip = B := BilinForm.isSymm_iff_flip.mp hBsymm
  have h := B.dualSubmodule_flip_dualSubmodule_of_isLattice hB M
  rwa [hflip] at h
