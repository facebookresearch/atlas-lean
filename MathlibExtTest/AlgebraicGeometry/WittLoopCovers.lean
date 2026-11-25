/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.WittLoopGroups
import MathlibExt.AlgebraicGeometry.RelativeWittLoopTests

/-!
Tests of the Witt test topologies: finite families whose product map is bijective, such as the two
components of a product of perfect algebras, are covering families, and the empty family covers
the zero algebra. Single faithfully flat maps alone would generate neither.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

/-- A finite decomposition `R ≅ ∏ Sᵢ` is a covering family. -/
example (R : (WittLatticeFamilies.PerfectAlgebra p)ᵒᵖ) (J : Type) [Finite J]
    (S : J → WittLatticeFamilies.PerfectAlgebra p) (f : ∀ i, R.unop ⟶ S i)
    (h : Function.Bijective (RingHom.pi fun i ↦ (f i).hom.hom.toRingHom)) :
    Sieve.generate (Presieve.ofArrows (fun i ↦ op (S i)) fun i ↦ (f i).op) ∈
      WittLoopGroups.fpqcTopology p R :=
  Precoverage.generate_mem_toGrothendieck (J := WittLoopGroups.fpqcPrecoverage p)
    (Set.mem_ofPred.mpr ⟨J, inferInstance, S, f, .of_bijective h, rfl⟩)

/-- The empty family covers the zero algebra. -/
example (R : (WittLatticeFamilies.PerfectAlgebra p)ᵒᵖ) [Subsingleton R.unop.obj]
    (S : Empty → WittLatticeFamilies.PerfectAlgebra p) (f : ∀ i, R.unop ⟶ S i) :
    Sieve.generate (Presieve.ofArrows (fun i ↦ op (S i)) fun i ↦ (f i).op) ∈
      WittLoopGroups.fpqcTopology p R :=
  Precoverage.generate_mem_toGrothendieck (J := WittLoopGroups.fpqcPrecoverage p)
    (Set.mem_ofPred.mpr ⟨Empty, inferInstance, S, f,
      .of_bijective ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩,
      rfl⟩)

/-- The relative Witt test topology has the same finite decomposition covers. -/
example (k : Type) [CommRing k] (R : (RelativeWittLoopTests.PerfectAlgebra p k)ᵒᵖ) (J : Type)
    [Finite J] (S : J → RelativeWittLoopTests.PerfectAlgebra p k) (f : ∀ i, R.unop ⟶ S i)
    (h : Function.Bijective (RingHom.pi fun i ↦ (f i).hom.hom.toRingHom)) :
    Sieve.generate (Presieve.ofArrows (fun i ↦ op (S i)) fun i ↦ (f i).op) ∈
      RelativeWittLoopTests.fpqcTopology p k R :=
  Precoverage.generate_mem_toGrothendieck (J := RelativeWittLoopTests.fpqcPrecoverage p k)
    (Set.mem_ofPred.mpr ⟨J, inferInstance, S, f, .of_bijective h, rfl⟩)
