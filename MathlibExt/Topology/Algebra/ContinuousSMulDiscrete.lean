/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_ContinuousSMulDiscrete.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The cited upstream file is adapted from a file of the Imperial College London FLT project
(https://github.com/ImperialCollegeLondon/FLT, branch `main` as of 2026-05-21, as the
upstream `ATTRIBUTION.md` records; header checked at commit
`a7dbce8494c29858093974a612a72b6454fc5cba`). The portions of this file that come from it
are adapted from:

`FLT/Deformations/RepresentationTheory/ContinuousSMulDiscrete.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang
-/

module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

/-- An action of a topological space `G` on a set `M` is continuous for the
discrete topology on `M` if every fibre `{g | g • x = y}` is open in `G`.

This class does not assume a topology on `M`; when `M` carries the discrete
topology it is equivalent to `ContinuousSMul G M`. -/
class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  /-- Every fibre of the action map is open. -/
  isOpen_smul_eq (G) (x y : M) : IsOpen {g : G | g • x = y}

/-- With the discrete topology on `M`, `ContinuousSMulDiscrete G M` is
equivalent to joint continuity of the action. -/
public theorem continuousSMulDiscrete_iff {G M : Type*} [TopologicalSpace G] [SMul G M]
    [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, {g : G | g • x = y} ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage
      (Continuous.prodMk_left x)

instance (priority := low) {G M : Type*} [TopologicalSpace G] [SMul G M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMulDiscrete G M] :
    ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

/-- Joint continuity for the discrete topology gives `ContinuousSMulDiscrete`. -/
public theorem ContinuousSMulDiscrete.of_continuousSMul {G M : Type*}
    [TopologicalSpace G] [SMul G M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

/-- For a group action, `ContinuousSMulDiscrete` is equivalent to every
stabilizer being open. -/
public theorem continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*}
    [TopologicalSpace G] [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔
      ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _,
    fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

/-- Every stabilizer of a `ContinuousSMulDiscrete` group action is open. -/
public theorem ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*}
    [TopologicalSpace G] [Group G] [MulAction G M] [ContinuousSMulDiscrete G M]
    (x : M) : IsOpen (MulAction.stabilizer G x : Set G) :=
  ContinuousSMulDiscrete.isOpen_smul_eq _ _ _
