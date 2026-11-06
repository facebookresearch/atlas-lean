/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentation
public import Mathlib.Algebra.Module.ZMod

/-! The genuine Conway universal group's abelianization is naturally a binary module. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every source word has square one after passage to the actual commutator quotient. -/
theorem co1UniversalAbelianization_square_word (x : Co1UniversalPresentation) :
    (Abelianization.of x) ^ 2 = 1 := by
  have hx : x ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : MonsterCo1GeometryPoint → Co1UniversalPresentation)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      rw [← map_pow, co1UniversalPoint_square, map_one]
  | one => rw [map_one, one_pow]
  | mul x y hx hy ihx ihy => rw [map_mul, mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [map_inv, inv_pow, ih, inv_one]

/-- Every element of the independently defined abelianization has exponent dividing two. -/
theorem co1UniversalAbelianization_square (x : Abelianization Co1UniversalPresentation) :
    x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H x => exact co1UniversalAbelianization_square_word x

/-- The source abelianization's additive form has its induced binary scalar structure. -/
instance co1UniversalAbelianizationModule :
    Module (ZMod 2) (Additive (Abelianization Co1UniversalPresentation)) :=
  AddCommGroup.zmodModule (fun x => by
    change x.toMul ^ 2 = 1
    exact co1UniversalAbelianization_square x.toMul)

/-- Actual point generators in the commutator quotient, regarded as binary vectors. -/
def co1UniversalAbelianPoint (p : MonsterCo1GeometryPoint) :
    Additive (Abelianization Co1UniversalPresentation) :=
  Additive.ofMul (Abelianization.of (PresentedGroup.of p))

/-- The original genuine line relation persists in the commutator quotient. -/
theorem co1UniversalAbelianPoint_line (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) :
    co1UniversalAbelianPoint p + co1UniversalAbelianPoint q +
      co1UniversalAbelianPoint r = 0 := by
  change Abelianization.of (PresentedGroup.of p) * Abelianization.of (PresentedGroup.of q) *
    Abelianization.of (PresentedGroup.of r) = 1
  rw [← map_mul, ← map_mul, co1UniversalPoint_line p q r h, map_one]

/-- The free binary point module maps to the independently defined source abelianization. -/
def co1UniversalFreeIntoAbelianization : MonsterCo1GeometryFreeModule →ₗ[ZMod 2]
    Additive (Abelianization Co1UniversalPresentation) :=
  Finsupp.linearCombination (ZMod 2) co1UniversalAbelianPoint

/-- All imposed genuine line sums are killed by this free-module map. -/
theorem co1UniversalFreeIntoAbelianization_relations :
    monsterCo1GeometryLineSubmodule ≤ co1UniversalFreeIntoAbelianization.ker := by
  rw [monsterCo1GeometryLineSubmodule, Submodule.span_le]
  rintro v ⟨p, q, r, h, rfl⟩
  change co1UniversalFreeIntoAbelianization
    (Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1) = 0
  simpa only [map_add, co1UniversalFreeIntoAbelianization,
    Finsupp.linearCombination_single, one_smul] using co1UniversalAbelianPoint_line p q r h

/-- The genuine universal binary module maps naturally to the source abelianization. -/
def co1UniversalModuleIntoAbelianization : MonsterCo1GeometryUniversalModule →ₗ[ZMod 2]
    Additive (Abelianization Co1UniversalPresentation) :=
  monsterCo1GeometryLineSubmodule.liftQ co1UniversalFreeIntoAbelianization
    co1UniversalFreeIntoAbelianization_relations

/-- The natural module-to-abelianization map preserves each original point generator. -/
theorem co1UniversalModuleIntoAbelianization_point (p : MonsterCo1GeometryPoint) :
    co1UniversalModuleIntoAbelianization (monsterCo1GeometryUniversalPoint p) =
      co1UniversalAbelianPoint p := by
  change co1UniversalFreeIntoAbelianization (Finsupp.single p 1) = _
  simp only [co1UniversalFreeIntoAbelianization, Finsupp.linearCombination_single, one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
