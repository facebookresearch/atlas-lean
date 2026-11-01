/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Statement skeleton for the FLM Monster finite-group milestones (T1–T6).

Status: all shared construction definitions are implemented, with proved laws.
The six endpoint theorems live in `Milestones.lean`; this file holds the
shared construction interfaces they all refer to. The subgroup closure and
normality laws (former `F-*` holes) are proved, and `Q` is a genuine
concrete plus-type coordinate model (not the audited FLM group: the
model-to-FLM comparison is pending). No endpoint theorem is proved.

The Griess space is `Fin 196884 → ℝ`, in the dictionary coordinates of
Seysen §8.1. Its form and extra triality are explicit, with proved linearity
and inverse laws. The Leech lattice uses explicit Golay congruences, with
proved rank 24 and an actual quotient by twice the lattice. The coordinate
Schrödinger action is proved faithful and orthogonal. The
independent reference model uses the Ivanov–Norton bimonster presentation.
The local extension is the explicit normalizer/Co₀ fiber product modulo
simultaneous signs. The Griess product is given by Conway’s six rules
in the fixed dictionary.
The local action is the descended matrix, signed-short, and spin-tensor action,
transported through the explicit dictionary linear equivalence.
Comparison with the primary FLM source is pending.

Proof status:
* Every shared construction is implemented without `sorry` or custom axioms.
* Historical comparison and recognition results remain proof obligations.
* `sorry` bodies on the six milestone theorems in `Milestones.lean`: proof holes.
* Former framework-law sorries (`F-*`): all discharged; the closure/normality
  proofs below are complete.
* The carriers of `leechIsomSubgroup` and `signsSubgroup` are genuine
  definitions (no `sorry` in the carrier data), and their closure/normality
  proofs are now proved as well.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.Algebra.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Logic.Equiv.Fin.Basic
public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Triality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayCode

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct

/-! ## The dictionary Griess space and form -/

/-- Real 196884-dimensional coordinate space. The dictionary basis and pairing
are fixed below and in `Triality.lean`; the product is constructed after the local group. -/
abbrev GriessSpace : Type := Fin 196884 → ℝ

/-- Squared norms in the dictionary basis of Seysen §8.1, Table 5,
using the pairing of §7.4. Coordinates 0–23 are `(ii)₁`; the next 828
coordinates are the A/B/C blocks `(ij)₁`, `Xᵢⱼ - Xᵢⱼ⁺`, and `Xᵢⱼ + Xᵢⱼ⁺`.
Each of these dictionary vectors has squared norm 2. The remaining octad
and signed X/Y/Z dictionary vectors have squared norm 1. -/
def griessBasisWeight (i : Fin 196884) : ℝ := if 24 ≤ i.val ∧ i.val < 852 then 2 else 1
/-- The explicit diagonal pairing in the source-normalized basis. -/
def griessFormFun (x y : GriessSpace) : ℝ := ∑ i, griessBasisWeight i * x i * y i
/-- Bilinear form from Seysen, arXiv:2002.10921v3, §7.4 (paragraph preceding
Table 3), expressed in the dictionary basis of §8.1, Table 5.
Bilinearity is proved; invariance under the remaining source-bound
actions and comparison with FLM are separate obligations. -/
noncomputable def griessForm : GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ griessFormFun
    (by intros; simp [griessFormFun, mul_add, add_mul, Finset.sum_add_distrib])
    (by intros; simp only [griessFormFun, Pi.smul_apply, smul_eq_mul];
        simp_rw [show ∀ w c x y : ℝ, w * (c * x) * y = c * (w * x * y) by intros; ring];
        rw [Finset.mul_sum])
    (by intros; simp [griessFormFun, mul_add, Finset.sum_add_distrib])
    (by intros; simp only [griessFormFun, Pi.smul_apply, smul_eq_mul];
        simp_rw [show ∀ w c x y : ℝ, w * x * (c * y) = c * (w * x * y) by intros; ring];
        rw [Finset.mul_sum])

/-! ## Explicit Golay-coordinate Leech lattice and Co1 -/





/-- Integral Leech congruences: coordinate residues modulo 4 come from a common
integer `m` plus twice a Golay word, and the coordinate sum is `4m` modulo 8.
Source: Seysen, *A computer-friendly construction of the monster*,
arXiv:2002.10921v3, §6.1. Integer coefficients represent code coefficients modulo 2.
Allowing arbitrary `m` is equivalent to restricting it to 0 or 1: shifting `m`
by 2 is absorbed by generator 11, the all-one word. -/
def LeechCongruences (u : Fin 24 → ℤ) (m : ℤ) (a : Fin 12 → ℤ) : Prop :=
  (∀ i, (u i : ZMod 4) = (m : ZMod 4) +
    2 * ∑ j, (a j : ZMod 4) * (golayGeneratorBit j i : ZMod 4)) ∧
  ((∑ i, u i : ℤ) : ZMod 8) = 4 * (m : ZMod 8)

/-- The integral-coordinate Leech module, with its closure laws proved from
the source congruences. Lattice rank and minimum norm are separate theorems. -/
def leechIntegral : Submodule ℤ (Fin 24 → ℤ) where
  carrier := {u | ∃ m a, LeechCongruences u m a}
  zero_mem' := by
    refine ⟨0, 0, ?_⟩
    simp [LeechCongruences]
  add_mem' := by
    rintro u v ⟨m, a, hu, hs⟩ ⟨n, b, hv, ht⟩
    refine ⟨m + n, a + b, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Int.cast_add, hu i, hv i, add_mul,
        Finset.sum_add_distrib, mul_add]
      ring
    · simp only [Pi.add_apply, Finset.sum_add_distrib, Int.cast_add, hs, ht, mul_add]
  smul_mem' := by
    rintro k u ⟨m, a, hu, hs⟩
    refine ⟨k * m, k • a, ?_, ?_⟩
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hu i]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Int.cast_mul, hs]
      ring

/-- Generator 11 is the all-one word, as in the published basis table. -/
theorem golayGeneratorBit_all_one (i : Fin 24) : golayGeneratorBit 11 i = 1 := by
  fin_cases i <;> decide

/-- The integral witness can be normalized to the parity convention of Seysen §6.1. -/
theorem leechCongruences_normalize (u : Fin 24 → ℤ) (m : ℤ) (a : Fin 12 → ℤ)
    (h : LeechCongruences u m a) :
    ∃ n : ℤ, (n = 0 ∨ n = 1) ∧ ∃ b, LeechCongruences u n b := by
  let k : ℤ := m / 2
  let b : Fin 12 → ℤ := fun j => a j + if j = 11 then k else 0
  have hm : m = m % 2 + 2 * k := by dsimp [k]; omega
  have hn : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hb (i : Fin 24) :
      (∑ j, (b j : ZMod 4) * (golayGeneratorBit j i : ZMod 4)) =
      (∑ j, (a j : ZMod 4) * (golayGeneratorBit j i : ZMod 4)) + (k : ZMod 4) := by
    simp [b, Int.cast_add, add_mul, Finset.sum_add_distrib, golayGeneratorBit_all_one]
  refine ⟨m % 2, hn, b, ?_, ?_⟩
  · intro i
    rw [h.1 i, hb]
    conv_lhs => rw [hm]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  · rw [h.2]
    conv_lhs => rw [hm]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring_nf
    simp [show (8 : ZMod 8) = 0 by decide]


/-- Twice an integer modulo 4 depends only on its residue modulo 2. -/
theorem golay_double_lift (z : ℤ) :
    (2 : ZMod 4) * ((z : ZMod 2).val : ZMod 4) = 2 * (z : ZMod 4) := by
  have hz : z = z % 2 + 2 * (z / 2) := by omega
  rw [← Int.cast_natCast, ZMod.val_intCast]
  conv_rhs => rw [hz]
  push_cast
  ring_nf
  simp [show (4 : ZMod 4) = 0 by decide]

/-- Reducing the integral encoding modulo 2 gives the binary encoding. -/
theorem golayEncoder_int (a : Fin 12 → ℤ) (i : Fin 24) :
    golayEncoder (fun j => (a j : ZMod 2)) i =
      ((∑ j, a j * golayGeneratorBit j i : ℤ) : ZMod 2) := by
  simp [golayEncoder]

/-- Doubling binary code coordinates gives their residues modulo 4. -/
theorem golayEncoder_double (a : Fin 12 → ℤ) (i : Fin 24) :
    (2 : ZMod 4) * ((golayEncoder (fun j => (a j : ZMod 2)) i).val : ZMod 4) =
    2 * ∑ j, (a j : ZMod 4) * (golayGeneratorBit j i : ZMod 4) := by
  rw [golayEncoder_int, golay_double_lift]
  simp

/-- Seysen §6.1 verbatim congruence conditions, with an actual binary codeword
and the common parity explicitly restricted to 0 or 1. -/
def LeechSourceCongruences (u : Fin 24 → ℤ) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ c ∈ golayCode,
    (∀ i, (u i : ZMod 4) = (m : ZMod 4) + 2 * ((c i).val : ZMod 4)) ∧
    ((∑ i, u i : ℤ) : ZMod 8) = 4 * (m : ZMod 8)

/-- The implemented integral module has exactly the source membership condition. -/
theorem mem_leechIntegral_iff_source (u : Fin 24 → ℤ) :
    u ∈ leechIntegral ↔ LeechSourceCongruences u := by
  constructor
  · rintro ⟨m, a, h⟩
    obtain ⟨n, hn, b, hb⟩ := leechCongruences_normalize u m a h
    refine ⟨n, hn, golayEncoder (fun j => (b j : ZMod 2)), ⟨_, rfl⟩, ?_, hb.2⟩
    intro i
    rw [golayEncoder_double, hb.1 i]
  · rintro ⟨m, hm, c, ⟨a, rfl⟩, hu, hs⟩
    let b : Fin 12 → ℤ := fun j => (a j).val
    have hb : (fun j => (b j : ZMod 2)) = a := by
      ext j
      simp [b]
    refine ⟨m, b, ?_, hs⟩
    intro i
    rw [← golayEncoder_double, hb]
    exact hu i

/-- Map integral coordinates into standard Euclidean coordinates. The factor
`1 / sqrt 8` is the normalization in Seysen §6.1; it gives minimum squared norm 4.
The minimum-norm bound is proved below from the Golay weights. -/
noncomputable def leechCoordinateEmbedding : (Fin 24 → ℤ) →ₗ[ℤ] (Fin 24 → ℝ) where
  toFun u i := (u i : ℝ) / Real.sqrt 8
  map_add' u v := by ext i; simp [add_div]
  map_smul' k u := by ext i; simp [mul_div_assoc]

/-- Explicit Golay-coordinate Leech lattice in the standard real 24-space,
using the congruences and scale from Seysen §6.1. This definition has no holes;
comparison of the complete FLM construction with these coordinates is pending. -/
noncomputable def LeechLattice : Submodule ℤ (Fin 24 → ℝ) :=
  leechIntegral.map leechCoordinateEmbedding

/-! ### Integral basis and actual quotient by twice the lattice -/

/-- Integral Golay coefficients witnessing the residues of each basis candidate. -/
def leechBasisResidueCoefficients (j : Fin 24) : Fin 12 → ℤ :=
  fun k => if (leechBasisCodeMasks j).testBit k.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Checking all 24 columns unfolds their finite coordinate congruences.
/-- Each supplied column satisfies the actual lattice congruences, with its
specified Golay witness. This is checked independently of the Hermite computation. -/
theorem leechBasisMatrix_congruences : ∀ j : Fin 24,
    LeechCongruences (fun i => leechBasisMatrix i j) (if j = 23 then 1 else 0)
      (leechBasisResidueCoefficients j) := by
  unfold LeechCongruences
  decide +kernel

/-- Every proposed basis column belongs to the actual integral Leech module. -/
theorem leechBasisMatrix_mem (j : Fin 24) : (fun i => leechBasisMatrix i j) ∈ leechIntegral :=
  ⟨_, _, leechBasisMatrix_congruences j⟩



/-- Every multiple of 8 in the ambient integer module satisfies the Leech congruences. -/
theorem leechIntegral_eight_smul (u : Fin 24 → ℤ) : (8 : ℤ) • u ∈ leechIntegral := by
  refine ⟨0, 0, ?_, ?_⟩
  · intro i
    change ((8 * u i : ℤ) : ZMod 4) = _
    simp [show (8 : ZMod 4) = 0 by decide]
  · change ((∑ i, 8 * u i : ℤ) : ZMod 8) = _
    simp [← Finset.mul_sum, show (8 : ZMod 8) = 0 by decide]

/-- Multiplication by 8 embeds the ambient integer coordinate module in the lattice. -/
def leechEightEmbedding : (Fin 24 → ℤ) →ₗ[ℤ] leechIntegral where
  toFun u := ⟨8 • u, leechIntegral_eight_smul u⟩
  map_add' u v := by apply Subtype.ext; exact smul_add 8 u v
  map_smul' k u := by apply Subtype.ext; exact smul_comm 8 k u

/-- The integer coordinate embedding is injective. -/
theorem leechEightEmbedding_injective : Function.Injective leechEightEmbedding := by
  intro u v h
  have he := congrArg Subtype.val h
  funext i
  have hi := congrFun he i
  change 8 * u i = 8 * v i at hi
  omega

/-- The integral Leech module is free over the principal ideal domain ℤ. -/
noncomputable instance leechIntegralFree : Module.Free ℤ leechIntegral := inferInstance
/-- The integral Leech module is finitely generated. -/
noncomputable instance leechIntegralFinite : Module.Finite ℤ leechIntegral := inferInstance

/-- The lattice rank is exactly 24, bounded by its ambient module and its embedded
copy of that same module. This does not assert minimum norm or unimodularity. -/
theorem leechIntegral_finrank : Module.finrank ℤ leechIntegral = 24 := by
  have h₁ := LinearMap.finrank_le_finrank_of_injective leechIntegral.subtype_injective
  have h₂ := LinearMap.finrank_le_finrank_of_injective leechEightEmbedding_injective
  have ha : Module.finrank ℤ (Fin 24 → ℤ) = 24 := by simp
  rw [ha] at h₁ h₂
  omega

/-! ### Explicit integer lattice basis

The congruences give 37 natural generators. Their exact coordinates in
`leechBasisMatrix` prove that its columns span the lattice. Upper triangularity
and its nonzero diagonal prove independence over the integers.
-/

/-- The natural 37 integral generators read directly from the congruence conditions. -/
def leechCongruenceGenerators : Fin 37 → (Fin 24 → ℤ) := fun j i =>
  if j = 0 then (if i = 0 then 8 else 0)
  else if h : j.val < 24 then 4 * ((if i.val = j.val then 1 else 0) - (if i = 0 then 1 else 0))
  else if h' : j.val < 36 then
    2 * golayGeneratorBit ⟨j.val - 24, by omega⟩ i
  else if i = 0 then -3 else 1

def leechGeneratorWitness (j : Fin 37) : Fin 12 → ℤ := fun k =>
  if 24 ≤ j.val ∧ j.val < 36 ∧ k.val = j.val - 24 then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- All generators are checked against 24 finite congruences.
theorem leechCongruenceGenerators_congruences : ∀ j : Fin 37,
    LeechCongruences (leechCongruenceGenerators j) (if j = 36 then 1 else 0)
      (leechGeneratorWitness j) := by
  unfold LeechCongruences
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The exact 24-by-37 integer identity verifies the supplied generator coordinates.
theorem leechCongruenceGenerators_coordinates : ∀ j : Fin 37,
    leechCongruenceGenerators j =
      fun i => ∑ k, leechBasisMatrix i k * leechGeneratorCoordinates k j := by
  decide +kernel

theorem integral_four_decomposition (u : Fin 24 → ℤ)
    (hfour : ∀ i, 4 ∣ u i) (height : 8 ∣ ∑ i, u i) :
    ∃ k : ℤ, ∃ w : Fin 24 → ℤ,
      u = k • (Pi.single 0 8) +
        ∑ i, w i • ((4 : ℤ) • (Pi.single i 1 - Pi.single 0 1)) := by
  classical
  choose w hw using hfour
  obtain ⟨k, hk⟩ := height
  have hs : 4 * (∑ i, w i) = 8 * k := by
    rw [Finset.mul_sum]
    simp_rw [← hw]
    exact hk
  refine ⟨k, w, ?_⟩
  funext j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.single_apply]
  by_cases hj : j = 0
  · subst j
    simp only [Fin.isValue, ↓reduceIte, mul_sub, mul_ite, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, mul_one, mul_zero]
    rw [← Finset.sum_mul]
    rw [hw]
    linarith
  · simp [hj, mul_ite]
    simpa [mul_comm] using hw j


def leechOddGenerator : Fin 24 → ℤ := fun i => if i = 0 then -3 else 1

theorem leechOddGenerator_residue : ∀ i, (leechOddGenerator i : ZMod 4) = 1 := by
  decide +kernel

theorem leechOddGenerator_sum : (∑ i, leechOddGenerator i : ℤ) = 20 := by
  decide +kernel

theorem golayTwice_sum_residue : ∀ j, (2 : ZMod 8) * ∑ i, (golayGeneratorBit j i : ZMod 8) = 0 := by
  decide +kernel

def leechCongruenceRepresentative (m : ℤ) (a : Fin 12 → ℤ) : Fin 24 → ℤ :=
  m • leechOddGenerator + ∑ j, a j • (fun i => 2 * golayGeneratorBit j i)

theorem leechCongruenceRepresentative_congruences (m : ℤ) (a : Fin 12 → ℤ) :
    LeechCongruences (leechCongruenceRepresentative m a) m a := by
  constructor
  · intro i
    simp only [leechCongruenceRepresentative, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply, Int.cast_add, Int.cast_mul, Int.cast_sum,
      leechOddGenerator_residue, mul_one, Int.cast_ofNat]
    rw [Finset.mul_sum]
    apply congrArg (fun z : ZMod 4 => (m : ZMod 4) + z)
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [leechCongruenceRepresentative, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, leechOddGenerator_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, golayTwice_sum_residue,
      mul_zero, Finset.sum_const_zero, add_zero, Int.cast_ofNat]
    have h : (20 : ZMod 8) = 4 := by decide
    rw [h, mul_comm]

theorem leech_residue_remainder (u : Fin 24 → ℤ) (m : ℤ) (a : Fin 12 → ℤ)
    (hu : LeechCongruences u m a) :
    (∀ i, 4 ∣ (u - leechCongruenceRepresentative m a) i) ∧
      8 ∣ ∑ i, (u - leechCongruenceRepresentative m a) i := by
  have hb := leechCongruenceRepresentative_congruences m a
  constructor
  · intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Pi.sub_apply, Int.cast_sub, hu.1 i, hb.1 i, sub_self]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Int.cast_sub, hu.2, hb.2, sub_self]


def leechColumnSpan : Submodule ℤ (Fin 24 → ℤ) :=
  Submodule.span ℤ (Set.range fun j => fun i => leechBasisMatrix i j)

theorem leechCongruenceGenerators_mem_columnSpan (j : Fin 37) :
    leechCongruenceGenerators j ∈ leechColumnSpan := by
  rw [leechCongruenceGenerators_coordinates j]
  have h : (fun i => ∑ k, leechBasisMatrix i k * leechGeneratorCoordinates k j) =
      ∑ k, leechGeneratorCoordinates k j • (fun i => leechBasisMatrix i k) := by
    ext i
    simp [mul_comm]
  rw [h]
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨k, rfl⟩

theorem leech_eight_mem_columnSpan : Pi.single (0 : Fin 24) (8 : ℤ) ∈ leechColumnSpan := by
  have h : leechCongruenceGenerators 0 = Pi.single 0 8 := by
    ext i
    simp [leechCongruenceGenerators, Pi.single_apply]
  rw [← h]
  exact leechCongruenceGenerators_mem_columnSpan 0

theorem leech_four_difference_mem_columnSpan (i : Fin 24) :
    (4 : ℤ) • (Pi.single i 1 - Pi.single 0 1) ∈ leechColumnSpan := by
  by_cases hi : i = 0
  · subst i; simp
  · have h : ∀ i : Fin 24, i ≠ 0 →
        leechCongruenceGenerators ⟨i.val, by omega⟩ =
          (4 : ℤ) • (Pi.single i 1 - Pi.single 0 1) := by
      decide +kernel
    rw [← h i hi]
    exact leechCongruenceGenerators_mem_columnSpan _

theorem leech_twice_golay_mem_columnSpan (j : Fin 12) :
    (fun i => 2 * golayGeneratorBit j i) ∈ leechColumnSpan := by
  have h : ∀ j : Fin 12, leechCongruenceGenerators ⟨24 + j.val, by omega⟩ =
      fun i => 2 * golayGeneratorBit j i := by
    decide +kernel
  rw [← h j]
  exact leechCongruenceGenerators_mem_columnSpan _

theorem leech_odd_mem_columnSpan : leechOddGenerator ∈ leechColumnSpan := by
  have h : leechCongruenceGenerators 36 = leechOddGenerator := by rfl
  rw [← h]
  exact leechCongruenceGenerators_mem_columnSpan 36

theorem leechCongruenceRepresentative_mem_columnSpan (m : ℤ) (a : Fin 12 → ℤ) :
    leechCongruenceRepresentative m a ∈ leechColumnSpan := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ leech_odd_mem_columnSpan
  · apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (leech_twice_golay_mem_columnSpan j)

theorem leechIntegral_le_columnSpan : leechIntegral ≤ leechColumnSpan := by
  rintro u ⟨m, a, hu⟩
  have hd := leech_residue_remainder u m a hu
  obtain ⟨k, w, hw⟩ := integral_four_decomposition _ hd.1 hd.2
  have hr : u - leechCongruenceRepresentative m a ∈ leechColumnSpan := by
    rw [hw]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ leech_eight_mem_columnSpan
    · apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (leech_four_difference_mem_columnSpan i)
  have := Submodule.add_mem leechColumnSpan hr
    (leechCongruenceRepresentative_mem_columnSpan m a)
  simpa using this


theorem leechColumnSpan_eq : leechColumnSpan = leechIntegral := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact leechBasisMatrix_mem j
  · exact leechIntegral_le_columnSpan

theorem leechBasisMatrix_upper : leechBasisMatrix.IsUpperTriangular := by
  decide +kernel

theorem leechBasisMatrix_diagonal_ne_zero : ∀ i, leechBasisMatrix i i ≠ 0 := by
  decide +kernel

theorem leechBasisMatrix_det_ne_zero : leechBasisMatrix.det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular leechBasisMatrix_upper]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => leechBasisMatrix_diagonal_ne_zero i)

theorem leechBasisMatrix_injective : Function.Injective leechBasisMatrix.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  by_contra h
  exact leechBasisMatrix_det_ne_zero (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, h, hv⟩)

noncomputable def leechExplicitCoordinateMap : (Fin 24 → ℤ) →ₗ[ℤ] leechIntegral :=
  leechBasisMatrix.mulVecLin.codRestrict leechIntegral (by
    intro u
    have h : leechBasisMatrix.mulVecLin u ∈ leechColumnSpan := by
      change leechBasisMatrix.mulVecLin u ∈ Submodule.span ℤ (Set.range leechBasisMatrix.col)
      rw [← Matrix.range_mulVecLin]
      exact ⟨u, rfl⟩
    rwa [leechColumnSpan_eq] at h)

theorem leechExplicitCoordinateMap_bijective : Function.Bijective leechExplicitCoordinateMap := by
  constructor
  · intro u v h
    exact leechBasisMatrix_injective (congrArg Subtype.val h)
  · intro u
    have h : u.val ∈ leechBasisMatrix.mulVecLin.range := by
      rw [Matrix.range_mulVecLin]
      change u.val ∈ leechColumnSpan
      rw [leechColumnSpan_eq]
      exact u.property
    obtain ⟨v, hv⟩ := h
    exact ⟨v, Subtype.ext hv⟩

noncomputable def leechExplicitCoordinates : leechIntegral ≃ₗ[ℤ] (Fin 24 → ℤ) :=
  (LinearEquiv.ofBijective leechExplicitCoordinateMap leechExplicitCoordinateMap_bijective).symm


/-- The explicit integer basis given by the columns of `leechBasisMatrix`.
Its reduction modulo 2 supplies the coordinates for the binary matrix below. -/
noncomputable def leechIntegralBasis : Module.Basis (Fin 24) ℤ leechIntegral :=
  Module.Basis.ofEquivFun leechExplicitCoordinates

/-- Reduction modulo 2 of integer coordinate vectors. -/
def integerParity : (Fin 24 → ℤ) →+ (Fin 24 → ZMod 2) where
  toFun u i := (u i : ZMod 2)
  map_zero' := by ext i; simp
  map_add' u v := by ext i; simp

/-- Every binary vector is the reduction of its integer 0/1 lift. -/
theorem integerParity_surjective : Function.Surjective integerParity := by
  intro u
  refine ⟨fun i => (u i).val, ?_⟩
  ext i
  simp [integerParity]

/-- A coordinate vector reduces to zero exactly when all coordinates are doubles. -/
theorem integerParity_eq_zero_iff (u : Fin 24 → ℤ) :
    integerParity u = 0 ↔ ∃ v : Fin 24 → ℤ, 2 • v = u := by
  constructor
  · intro h
    have hd (i : Fin 24) : 2 ∣ u i := by
      have hi := congrFun h i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (u i) 2).mp hi
    choose v hv using hd
    refine ⟨v, ?_⟩
    funext i
    exact (hv i).symm
  · rintro ⟨v, rfl⟩
    ext i
    change ((2 * v i : ℤ) : ZMod 2) = 0
    simp [show (2 : ZMod 2) = 0 by decide]

/-- Reduce coordinates in an actual integer lattice basis modulo 2. -/
noncomputable def leechBasisParity : leechIntegral →+ (Fin 24 → ZMod 2) :=
  integerParity.comp leechIntegralBasis.equivFun.toAddEquiv.toAddMonoidHom

/-- Doubling inside the integral lattice, not in the ambient real vector space. -/
noncomputable def leechDouble : leechIntegral →+ leechIntegral where
  toFun u := (2 : ℕ) • u
  map_zero' := by simp
  map_add' u v := nsmul_add u v 2

/-- The subgroup consisting of twice an integral lattice vector. -/
noncomputable def twiceLeechIntegral : AddSubgroup leechIntegral := leechDouble.range

/-- The actual quotient Λ/2Λ in integral coordinates. Ambient coordinate reduction
modulo 2 would give a different quotient and is not used. -/
noncomputable abbrev LeechModTwo := leechIntegral ⧸ twiceLeechIntegral

/-- The natural additive quotient map to Λ/2Λ. -/
noncomputable def leechReduction : leechIntegral →+ LeechModTwo :=
  QuotientAddGroup.mk' twiceLeechIntegral

/-- The actual lattice quotient has characteristic two and therefore is an F₂-module. -/
noncomputable instance leechModTwoModule : Module (ZMod 2) LeechModTwo :=
  QuotientAddGroup.zmodModule (n := 2) (fun u => ⟨u, rfl⟩)

/-- Every binary lattice-coordinate vector has an integral lattice lift. -/
theorem leechBasisParity_surjective : Function.Surjective leechBasisParity :=
  integerParity_surjective.comp leechIntegralBasis.equivFun.surjective

/-- Reducing integer lattice-basis coordinates forgets exactly twice the lattice. -/
theorem twiceLeechIntegral_eq_ker : twiceLeechIntegral = leechBasisParity.ker := by
  ext u
  change (∃ v : leechIntegral, (2 : ℕ) • v = u) ↔
    integerParity (leechIntegralBasis.equivFun u) = 0
  rw [integerParity_eq_zero_iff]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨leechIntegralBasis.equivFun v, ?_⟩
    exact (map_nsmul leechIntegralBasis.equivFun 2 v).symm
  · rintro ⟨v, hv⟩
    refine ⟨leechIntegralBasis.equivFun.symm v, ?_⟩
    apply leechIntegralBasis.equivFun.injective
    rw [map_nsmul, leechIntegralBasis.equivFun.apply_symm_apply]
    exact hv

/-- The first-isomorphism-theorem equivalence from Λ/2Λ to binary basis coordinates. -/
noncomputable def leechModTwoEquiv : LeechModTwo ≃+ (Fin 24 → ZMod 2) :=
  (QuotientAddGroup.quotientAddEquivOfEq twiceLeechIntegral_eq_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective leechBasisParity leechBasisParity_surjective)

/-- The additive quotient equivalence is F₂-linear. Compatibility with the
quadratic form and the fixed hyperbolic coordinates of Q remains to be constructed. -/
noncomputable def leechModTwoLinearEquiv : LeechModTwo ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  { leechModTwoEquiv with map_smul' := ZMod.map_smul leechModTwoEquiv }


/-- Genuine definition (no hole): the fixed standard Euclidean pairing on
`Fin 24 → ℝ`, the sum of coordinate products. -/
def stdPairingFun (x y : Fin 24 → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => x i * y i)

/-- Genuine definition (no hole): a Leech isometry is an ambient real linear
equivalence preserving the standard coordinate pairing AND carrying
`LeechLattice` onto itself (membership equivalence for every vector). -/
def IsLeechIsom (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) : Prop :=
  (∀ x y, stdPairingFun (e x) (e y) = stdPairingFun x y) ∧
  (∀ x, x ∈ LeechLattice ↔ e x ∈ LeechLattice)

/-- The lattice-isometry subgroup of the ambient general linear group.
Carrier data are genuine (no `sorry`): pairing preservation plus
onto-`LeechLattice` membership. Closure laws are proved (former framework
holes F-LeechIsom*), now applied to the explicit Golay-coordinate lattice.
Comparison with the FLM lattice remains to be proved. -/
noncomputable def leechIsomSubgroup :
    Subgroup ((Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) :=
  { carrier := { e | IsLeechIsom e },
    one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩,
    mul_mem' := by
      intro a b ha hb
      obtain ⟨hpa, haa⟩ := ha
      obtain ⟨hpb, hab⟩ := hb
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hpa, hpb]
      · rw [LinearEquiv.mul_apply]
        exact (hab x).trans (haa (b x))
    inv_mem' := by
      intro a ha
      obtain ⟨hpa, haa⟩ := ha
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · have h := hpa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        exact h.symm
      · change x ∈ LeechLattice ↔ a.symm x ∈ LeechLattice
        simpa using (haa (a.symm x)).symm }

/-! ## The actual lattice action on the quotient by twice the lattice

The normalization identifies the integer congruence lattice with its real image.
Every lattice isometry therefore acts on the integer lattice and its quotient;
these actions use the actual lattice, rather than reduction of ambient coordinates.
-/


theorem leechCoordinateEmbedding_injective : Function.Injective leechCoordinateEmbedding := by
  intro u v h
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  funext i
  have hi := congrFun h i
  change (u i : ℝ) / Real.sqrt 8 = (v i : ℝ) / Real.sqrt 8 at hi
  exact_mod_cast (div_left_inj' hs).mp hi

noncomputable def leechNormalizedMap : leechIntegral →ₗ[ℤ] LeechLattice :=
  (leechCoordinateEmbedding.comp leechIntegral.subtype).codRestrict LeechLattice
    (fun u => Submodule.mem_map.mpr ⟨u.val, u.property, rfl⟩)

theorem leechNormalizedMap_bijective : Function.Bijective leechNormalizedMap := by
  constructor
  · intro u v h
    apply Subtype.ext
    exact leechCoordinateEmbedding_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp x.property
    exact ⟨⟨u, hu⟩, Subtype.ext he⟩

noncomputable def leechNormalization : leechIntegral ≃ₗ[ℤ] LeechLattice :=
  LinearEquiv.ofBijective leechNormalizedMap leechNormalizedMap_bijective

noncomputable def leechRealActionEquiv (e : leechIsomSubgroup) :
    LeechLattice ≃ₗ[ℤ] LeechLattice where
  toFun u := ⟨e.val u.val, (e.property.2 u.val).mp u.property⟩
  invFun u := ⟨e.val.symm u.val, (e.property.2 (e.val.symm u.val)).mpr
    (by simpa only [LinearEquiv.apply_symm_apply] using u.property)⟩
  left_inv u := by apply Subtype.ext; exact e.val.symm_apply_apply u.val
  right_inv u := by apply Subtype.ext; exact e.val.apply_symm_apply u.val
  map_add' u v := by apply Subtype.ext; exact map_add e.val u.val v.val
  map_smul' k u := by apply Subtype.ext; exact (e.val.restrictScalars ℤ).map_smul k u.val

noncomputable def leechRealAction : leechIsomSubgroup →* (LeechLattice ≃ₗ[ℤ] LeechLattice) where
  toFun := leechRealActionEquiv
  map_one' := by apply LinearEquiv.ext; intro u; rfl
  map_mul' e f := by apply LinearEquiv.ext; intro u; rfl

noncomputable def leechIntegralActionEquiv (e : leechIsomSubgroup) :
    leechIntegral ≃ₗ[ℤ] leechIntegral :=
  leechNormalization.trans ((leechRealAction e).trans leechNormalization.symm)

noncomputable def leechIntegralAction : leechIsomSubgroup →*
    (leechIntegral ≃ₗ[ℤ] leechIntegral) where
  toFun := leechIntegralActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro u
    exact leechNormalization.symm_apply_apply u
  map_mul' e f := by
    apply LinearEquiv.ext
    intro u
    simp [leechIntegralActionEquiv, LinearEquiv.trans_apply]

theorem leechDouble_map (e : leechIntegral ≃ₗ[ℤ] leechIntegral) :
    twiceLeechIntegral.map e.toAddEquiv.toAddMonoidHom = twiceLeechIntegral := by
  ext u
  constructor
  · rintro ⟨v, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    exact (map_nsmul e 2 w).symm
  · rintro ⟨w, rfl⟩
    refine ⟨(2 : ℕ) • e.symm w, ⟨e.symm w, rfl⟩, ?_⟩
    change e ((2 : ℕ) • e.symm w) = (2 : ℕ) • w
    rw [map_nsmul, e.apply_symm_apply]

noncomputable def leechQuotientAut (e : leechIntegral ≃ₗ[ℤ] leechIntegral) :
    LeechModTwo ≃ₗ[ZMod 2] LeechModTwo :=
  let a := QuotientAddGroup.congr twiceLeechIntegral twiceLeechIntegral
    e.toAddEquiv (leechDouble_map e)
  { a with map_smul' := ZMod.map_smul a }

@[simp] theorem leechQuotientAut_reduce (e : leechIntegral ≃ₗ[ℤ] leechIntegral)
    (u : leechIntegral) : leechQuotientAut e (leechReduction u) = leechReduction (e u) := rfl

noncomputable def leechModTwoAction : leechIsomSubgroup →*
    (LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) where
  toFun e := leechQuotientAut (leechIntegralAction e)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective twiceLeechIntegral x
    change leechQuotientAut (leechIntegralAction 1) (leechReduction u) = leechReduction u
    rw [leechQuotientAut_reduce, leechIntegralAction.map_one]
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective twiceLeechIntegral x
    change leechQuotientAut (leechIntegralAction (e * f)) (leechReduction u) =
      leechQuotientAut (leechIntegralAction e)
        (leechQuotientAut (leechIntegralAction f) (leechReduction u))
    simp only [leechQuotientAut_reduce, leechIntegralAction.map_mul, LinearEquiv.mul_apply]


/-- Genuine definition (no hole): the signs predicate inside the actual
isometry group. The first case is the underlying transformation `= 1`; the
second case sends every vector `x` to `-x` (stated pointwise to avoid any
negative-equiv API). -/
def IsSign (g : ↥leechIsomSubgroup) : Prop :=
  g.val = 1 ∨ ∀ x, g.val x = -x

/-- The `{±1}` subgroup of the actual isometry group. Carrier data are
genuine (no `sorry`): exactly the identity or the pointwise negative
identity. Closure proofs are proved (former framework holes F-signs*). -/
noncomputable def signsSubgroup : Subgroup ↥leechIsomSubgroup :=
  { carrier := { g | IsSign g },
    one_mem' := Or.inl rfl,
    mul_mem' := by
      intro a b ha hb
      obtain ha | ha := ha <;> obtain hb | hb := hb
      · refine Or.inl ?_
        change a.val * b.val = 1
        rw [ha, hb, mul_one]
      · refine Or.inr ?_
        intro x
        change (a.val * b.val) x = -x
        rw [ha, one_mul]
        exact hb x
      · refine Or.inr ?_
        intro x
        change (a.val * b.val) x = -x
        rw [hb, mul_one]
        exact ha x
      · refine Or.inl ?_
        change a.val * b.val = 1
        apply LinearEquiv.ext
        intro x
        rw [LinearEquiv.mul_apply, hb x, map_neg, ha x, neg_neg]
        simp only [LinearEquiv.coe_one, id_eq]
    inv_mem' := by
      intro a ha
      obtain ha | ha := ha
      · refine Or.inl ?_
        change (a.val)⁻¹ = 1
        rw [ha, inv_one]
      · refine Or.inr ?_
        intro x
        change a.val.symm x = -x
        have h1 : a.val (a.val.symm x) = a.val (-x) := by
          rw [LinearEquiv.apply_symm_apply, map_neg, ha x, neg_neg]
        exact a.val.injective h1 }

/-- Normality of the signs subgroup (former framework hole F-signsNormal),
discharged by direct conjugation computation: conjugating the identity or
the pointwise negative identity stays in `{±1}`. -/
noncomputable instance signsNormal : signsSubgroup.Normal := by
  constructor
  intro n hn g
  obtain hn | hn := hn
  · refine Or.inl ?_
    change g.val * n.val * (g.val)⁻¹ = 1
    rw [hn, mul_one, mul_inv_cancel]
  · refine Or.inr ?_
    intro x
    change (g.val * n.val * g.val.symm) x = -x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hn,
      map_neg, LinearEquiv.apply_symm_apply]

/-- The Conway quotient `Co1 = Isom(Λ)/{±1}`, using the explicit
Golay-coordinate lattice and the proved normal signs subgroup. -/
abbrev Co1 : Type := ↥leechIsomSubgroup ⧸ signsSubgroup

/-! ## Local subgroup data (FLM construction formulas pending) -/

/-! ### Concrete plus-type extraspecial coordinate model for `Q`

The FLM extraspecial group itself (hole S-Q) is still unaudited. What is
genuine here is a standard coordinate MODEL of shape `2₊^{1+24}`: the
normalized-cocycle extension of `F₂^24` by `F₂` seeded by the explicit
bilinear pairing `qBeta` below. Group laws come from the proved
`NormalizedCocycleExtension` instance, not from new proofs. The center, its
coefficient homomorphism, quotient isomorphism,
squares link, and hyperbolic coordinate split are defined and proved below.
The comparison isomorphism between this model and the FLM group is PENDING
(part of S-Q); T1's claims about `Q` are claims about the coordinate model. -/

/-- Additive coordinate pairing `β(v,w) = Σ_{i < 12} vᵢ * w_{i+12}` on
`F₂^24`: the first block is indexed by `Fin.castAdd`, the second by
`Fin.natAdd`. The bilinear seed of the plus-type cocycle. -/
def qBeta (v w : Fin 24 → ZMod 2) : ZMod 2 :=
  Finset.sum Finset.univ (fun i : Fin 12 => v (Fin.castAdd 12 i) * w (Fin.natAdd 12 i))

theorem qBeta_add_left (u v w : Fin 24 → ZMod 2) :
    qBeta (u + v) w = qBeta u w + qBeta v w := by
  simp [qBeta, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem qBeta_add_right (u v w : Fin 24 → ZMod 2) :
    qBeta u (v + w) = qBeta u v + qBeta u w := by
  simp [qBeta, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem qBeta_cocycle (u v w : Fin 24 → ZMod 2) :
    qBeta u v + qBeta (u + v) w = qBeta u (v + w) + qBeta v w := by
  rw [qBeta_add_left, qBeta_add_right, add_assoc]

theorem qBeta_zero_left (w : Fin 24 → ZMod 2) : qBeta 0 w = 0 := by
  simp [qBeta]

theorem qBeta_zero_right (v : Fin 24 → ZMod 2) : qBeta v 0 = 0 := by
  simp [qBeta]

theorem qBeta_smul_left (c : ZMod 2) (u w : Fin 24 → ZMod 2) :
    qBeta (c • u) w = c • qBeta u w := by
  have atom : ∀ i : Fin 12, ((c • u) (Fin.castAdd 12 i)) * w (Fin.natAdd 12 i)
      = c * (u (Fin.castAdd 12 i) * w (Fin.natAdd 12 i)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [qBeta, atom, ← Finset.mul_sum, smul_eq_mul]

theorem qBeta_smul_right (c : ZMod 2) (u w : Fin 24 → ZMod 2) :
    qBeta u (c • w) = c • qBeta u w := by
  have atom : ∀ i : Fin 12, u (Fin.castAdd 12 i) * ((c • w) (Fin.natAdd 12 i))
      = c * (u (Fin.castAdd 12 i) * w (Fin.natAdd 12 i)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  simp only [qBeta, atom, ← Finset.mul_sum, smul_eq_mul]

/-- The coordinate pairing as a genuine `F₂`-bilinear map. -/
def qBilin : LinearMap.BilinMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) where
  toFun v :=
    { toFun := qBeta v
      map_add' := fun w w' => qBeta_add_right v w w'
      map_smul' := fun c w => qBeta_smul_right c v w }
  map_add' := fun u v => LinearMap.ext fun w => qBeta_add_left u v w
  map_smul' := fun c u => LinearMap.ext fun w => qBeta_smul_left c u w

/-- Normalized 2-cocycle seeding the extraspecial extension: the `qBeta`
values written multiplicatively. Normalization and the cocycle identity are
the additive abelian-group laws transported through `qBeta`-bilinearity. -/
def qCocycle : NormalizedCocycleExtension.NormalizedCocycle
    (Multiplicative (Fin 24 → ZMod 2)) (Multiplicative (ZMod 2)) where
  cocycle v w :=
    Multiplicative.ofAdd (qBeta (Multiplicative.toAdd v) (Multiplicative.toAdd w))
  one_left := by
    intro g
    rw [toAdd_one, qBeta_zero_left, ofAdd_zero]
  one_right := by
    intro g
    rw [toAdd_one, qBeta_zero_right, ofAdd_zero]
  cocycle_assoc := by
    intro v w z
    have h := qBeta_cocycle (Multiplicative.toAdd v) (Multiplicative.toAdd w)
      (Multiplicative.toAdd z)
    exact congrArg Multiplicative.ofAdd h

/-- Concrete plus-type extraspecial coordinate model: the normalized-cocycle
extension on `F₂^24` by `F₂`. The comparison with the FLM extraspecial
group is pending (part of S-Q) and is NOT proved here. -/
def Q : Type := NormalizedCocycleExtension.Extension qCocycle

/-- Group laws for the coordinate model, from the proved
`NormalizedCocycleExtension` instance. -/
instance instGroupQ : Group Q :=
  NormalizedCocycleExtension.instGroupExtension qCocycle

/-- Genuine: the center of `Q`, as a subgroup. -/
noncomputable def centerQ : Subgroup Q := Subgroup.center Q

/-- Normality of `centerQ` (former framework hole F-centerNormal), via the
Mathlib normal-center instance; this instance only fixes the name used by
the quotient below. -/
noncomputable instance centerQNormal : centerQ.Normal := Subgroup.instNormalCenter

/-! ## Coordinate center, quotient, and squares-induced quadratic form -/

/-- The coordinate projection `Q → F₂^24`, from the proved `projHom` of
the coordinate model. Its kernel and range are proved below, not assumed
as input. The identification of the FLM quotient with this projection is
pending (part of S-qQuotHom). -/
def qQuotHom : Q →* Multiplicative (Fin 24 → ZMod 2) :=
  NormalizedCocycleExtension.projHom qCocycle

section QCoordinates

open NormalizedCocycleExtension Multiplicative

/-- Two coordinate-model elements commute exactly when the cocycle pairing is symmetric on their
base vectors. -/
theorem q_mul_comm_iff (g h : Q) :
    g * h = h * g ↔
      qBeta (toAdd g.base) (toAdd h.base) = qBeta (toAdd h.base) (toAdd g.base) := by
  constructor
  · intro heq
    have hc := congrArg (fun x : Q => toAdd x.coeff) heq
    change (toAdd g.coeff + toAdd h.coeff) + qBeta (toAdd g.base) (toAdd h.base) =
      (toAdd h.coeff + toAdd g.coeff) + qBeta (toAdd h.base) (toAdd g.base) at hc
    rw [add_comm (toAdd h.coeff) (toAdd g.coeff)] at hc
    exact add_left_cancel hc
  · intro hb
    apply Extension.ext
    · exact mul_comm _ _
    · change g.coeff * h.coeff * ofAdd (qBeta (toAdd g.base) (toAdd h.base)) =
        h.coeff * g.coeff * ofAdd (qBeta (toAdd h.base) (toAdd g.base))
      rw [hb, mul_comm g.coeff h.coeff]

/-- Pairing with a unit vector in the second block extracts the corresponding first-block
coordinate. -/
theorem qBeta_single_second (v : Fin 24 → ZMod 2) (i : Fin 12) :
    qBeta v (Pi.single (Fin.natAdd 12 i) 1) = v (Fin.castAdd 12 i) := by
  unfold qBeta
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, mul_one]
  · intro j _ hji
    have hne : Fin.natAdd 12 j ≠ Fin.natAdd 12 i := by
      intro h
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    simp only [Pi.single_apply, ite_eq_right hne, mul_zero]
  · simp

/-- Pairing a first-block unit vector with a vector extracts its second-block coordinate. -/
theorem qBeta_single_first (v : Fin 24 → ZMod 2) (i : Fin 12) :
    qBeta (Pi.single (Fin.castAdd 12 i) 1) v = v (Fin.natAdd 12 i) := by
  unfold qBeta
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
  · intro j _ hji
    have hne : Fin.castAdd 12 j ≠ Fin.castAdd 12 i := by
      intro h
      apply hji
      exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
    simp only [Pi.single_apply, ite_eq_right hne, zero_mul]
  · simp

/-- A first-block unit vector in the right argument contributes zero to the coordinate pairing. -/
theorem qBeta_right_single_first (v : Fin 24 → ZMod 2) (i : Fin 12) :
    qBeta v (Pi.single (Fin.castAdd 12 i) 1) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hne : Fin.natAdd 12 j ≠ Fin.castAdd 12 i := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  simp only [Pi.single_apply, ite_eq_right hne, mul_zero]

/-- A second-block unit vector in the left argument contributes zero to the coordinate pairing. -/
theorem qBeta_left_single_second (v : Fin 24 → ZMod 2) (i : Fin 12) :
    qBeta (Pi.single (Fin.natAdd 12 i) 1) v = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hne : Fin.castAdd 12 j ≠ Fin.natAdd 12 i := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  simp only [Pi.single_apply, ite_eq_right hne, zero_mul]

/-- The center of the coordinate model consists exactly of elements with trivial base coordinate.
This is proved from commutation with all coordinate unit vectors. -/
theorem q_mem_center_iff_base_eq_one (g : Q) : g ∈ centerQ ↔ g.base = 1 := by
  constructor
  · intro hg
    have hb (w : Fin 24 → ZMod 2) :
        qBeta (toAdd g.base) w = qBeta w (toAdd g.base) := by
      have hc := Subgroup.mem_center_iff.mp hg (⟨ofAdd w, 1⟩ : Q)
      exact ((q_mul_comm_iff _ _).mp hc).symm
    have hl (i : Fin 12) : toAdd g.base (Fin.castAdd 12 i) = 0 := by
      simpa only [qBeta_single_second, qBeta_left_single_second]
        using hb (Pi.single (Fin.natAdd 12 i) 1)
    have hr (i : Fin 12) : toAdd g.base (Fin.natAdd 12 i) = 0 := by
      simpa only [qBeta_single_first, qBeta_right_single_first]
        using (hb (Pi.single (Fin.castAdd 12 i) 1)).symm
    apply Multiplicative.toAdd.injective
    funext i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective i
    cases j with
    | inl j => exact hl j
    | inr j => exact hr j
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply (q_mul_comm_iff _ _).mpr
    simp [hg, qBeta_zero_left, qBeta_zero_right]

/-- The coordinate projection forgets exactly the center of the coordinate model. -/
theorem qQuotHom_ker : qQuotHom.ker = centerQ := by
  ext g
  change g.base = 1 ↔ g ∈ centerQ
  exact (q_mem_center_iff_base_eq_one g).symm

/-- Every base vector has a lift with trivial central coefficient. -/
theorem qQuotHom_surjective : Function.Surjective qQuotHom := by
  intro v
  exact ⟨⟨v, 1⟩, rfl⟩

/-- The coordinate projection reaches the entire base group. -/
theorem qQuotHom_range : qQuotHom.range = ⊤ :=
  MonoidHom.range_eq_top.mpr qQuotHom_surjective

/-- The actual quotient isomorphism induced by the coordinate projection. Compatibility with the
FLM quotient remains pending under S-qQuotHom. -/
noncomputable def qQuotientEquiv :
    (Q ⧸ centerQ) ≃* Multiplicative (Fin 24 → ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq qQuotHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qQuotHom qQuotHom_surjective)

/-- The central coefficient of a central element in the concrete coordinate model. The homomorphism
law follows from its trivial base coordinate; bijectivity is proved below, not assumed in this
definition. Compatibility with FLM remains part of the model comparison S-Q. -/
def centerMap : ↥centerQ →* Multiplicative (ZMod 2) where
  toFun g := g.val.coeff
  map_one' := rfl
  map_mul' g h := by
    change g.val.coeff * h.val.coeff * qCocycle.cocycle g.val.base h.val.base =
      g.val.coeff * h.val.coeff
    rw [(q_mem_center_iff_base_eq_one g.val).mp g.property]
    simp

/-- Include a central bit in the coordinate model, with a proved center-membership property. -/
noncomputable def qCenterHom : Multiplicative (ZMod 2) →* ↥centerQ :=
  (inlHom qCocycle).codRestrict centerQ fun _c =>
    (q_mem_center_iff_base_eq_one _).mpr rfl

/-- Reading the central coefficient after including a bit returns that bit. -/
theorem centerMap_left_inverse :
    Function.LeftInverse centerMap qCenterHom := by
  intro c
  rfl

/-- Every central element is recovered from its central coefficient. -/
theorem centerMap_right_inverse :
    Function.RightInverse centerMap qCenterHom := by
  intro g
  apply Subtype.ext
  apply Extension.ext
  · exact ((q_mem_center_iff_base_eq_one _).mp g.property).symm
  · rfl

/-- The concrete central-coefficient homomorphism is bijective, using its explicitly constructed
inverse. -/
theorem centerMap_bijective : Function.Bijective centerMap :=
  ⟨centerMap_right_inverse.injective,
    centerMap_left_inverse.surjective⟩

/-- The plus-type coordinate quadratic form: the diagonal `v ↦ β(v, v)` of
the coordinate pairing, as a genuine `QuadraticMap` via
`BilinMap.toQuadraticMap`. The squares link is proved below in
`squareQuad_eq_centerMap_square` for this coordinate model. Its comparison
with the FLM squares-induced form remains part of S-Q. -/
def squareQuad :
    QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) :=
  LinearMap.BilinMap.toQuadraticMap qBilin

/-- Genuine definition (no hole): the fixed hyperbolic plus-type model
`q(a,b) = Σᵢ aᵢ * bᵢ` on `F₂^12 ⊕ F₂^12`. -/
def hyperbolicFun (p : (Fin 12 → ZMod 2) × (Fin 12 → ZMod 2)) : ZMod 2 :=
  Finset.sum Finset.univ (fun i => p.1 i * p.2 i)

/-- The square of a coordinate-model element has trivial base, since the base has characteristic
two. -/
theorem q_square_base (g : Q) : (g * g).base = 1 := by
  apply Multiplicative.toAdd.injective
  exact ZModModule.add_self (toAdd g.base)

/-- Every group square in the coordinate model lies in its actual center. -/
theorem q_square_mem_center (g : Q) : g * g ∈ centerQ :=
  (q_mem_center_iff_base_eq_one _).mpr (q_square_base g)

/-- The coordinate quadratic form equals the central coefficient of the group square. This proves
the squares link for this model without using any FLM source-data placeholder. -/
theorem squareQuad_eq_centerMap_square (g : Q) :
    squareQuad (toAdd (qQuotHom g)) =
      toAdd (centerMap ⟨g * g, q_square_mem_center g⟩) := by
  change qBeta (toAdd g.base) (toAdd g.base) =
    (toAdd g.coeff + toAdd g.coeff) + qBeta (toAdd g.base) (toAdd g.base)
  rw [ZModModule.add_self, zero_add]

/-- Split the 24 coordinates into their first and second blocks of 12, as an explicit linear
equivalence over F₂. -/
def qHyperbolicEquiv :
    (Fin 24 → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin 12 → ZMod 2) × (Fin 12 → ZMod 2)) :=
  { (Fin.appendEquiv 12 12).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The explicit block split carries the coordinate quadratic form to the stated hyperbolic form. -/
theorem qHyperbolicEquiv_form (v : Fin 24 → ZMod 2) :
    squareQuad v = hyperbolicFun (qHyperbolicEquiv v) := rfl

end QCoordinates

/-! ## Schrödinger representation and orthogonal normalizer

The representation is explicit in the fixed hyperbolic coordinates of Q. Its
linearity, multiplication, inverses, faithfulness, and pairing invariance are
proved independently of the pending Griess multiplication and local group.
-/

section SpinCoordinates

open Multiplicative

/-- Binary labels for the Schrödinger basis of the plus-type coordinate model. -/
abbrev SpinIndex := Fin 12 → ZMod 2
/-- The real Schrödinger representation space: functions on 4096 binary labels. -/
abbrev SpinSpace := SpinIndex → ℝ

/-- The characteristic-two additive character, with values in the real signs. -/
def qSign (c : ZMod 2) : ℝ := if c = 0 then 1 else -1
@[simp] theorem qSign_zero : qSign 0 = 1 := by simp [qSign]
@[simp] theorem qSign_one : qSign 1 = -1 := by norm_num [qSign]
theorem qSign_add (a b : ZMod 2) : qSign (a + b) = qSign a * qSign b := by
  have h (c : ZMod 2) : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
  all_goals
    simp only [zero_add, add_zero, show (1 : ZMod 2) + 1 = 0 by decide, qSign_zero, qSign_one]
    norm_num
@[simp] theorem qSign_sq (a : ZMod 2) : qSign a * qSign a = 1 := by
  rw [← qSign_add, ZModModule.add_self, qSign_zero]
@[simp] theorem qSign_eq_one_iff (a : ZMod 2) : qSign a = 1 ↔ a = 0 := by
  fin_cases a <;> norm_num [qSign]

/-- The binary dot product used in the modulation signs. -/
def spinDot (b t : SpinIndex) : ZMod 2 := ∑ i, b i * t i
theorem spinDot_add_left (b c t : SpinIndex) :
    spinDot (b + c) t = spinDot b t + spinDot c t := by
  simp [spinDot, add_mul, Finset.sum_add_distrib]
theorem spinDot_add_right (b t u : SpinIndex) :
    spinDot b (t + u) = spinDot b t + spinDot b u := by
  simp [spinDot, mul_add, Finset.sum_add_distrib]
@[simp] theorem spinDot_zero_left (t : SpinIndex) : spinDot 0 t = 0 := by simp [spinDot]
@[simp] theorem spinDot_zero_right (b : SpinIndex) : spinDot b 0 = 0 := by simp [spinDot]

/-- The first twelve base coordinates act by translating the binary labels. -/
def spinTranslation (g : Q) : SpinIndex := fun i => toAdd g.base (Fin.castAdd 12 i)
/-- The last twelve base coordinates specify the modulation character. -/
def spinModulation (g : Q) : SpinIndex := fun i => toAdd g.base (Fin.natAdd 12 i)
/-- The central sign plus the modulation character at a basis label. -/
def spinPhase (g : Q) (t : SpinIndex) : ZMod 2 := toAdd g.coeff + spinDot (spinModulation g) t

/-- Explicit Schrödinger operator: `f(t) ↦ (-1)^(c + b·t) f(t + a)`.
The multiplication law uses exactly the previously defined cocycle `a·b′`. -/
def spinOperator (g : Q) : SpinSpace →ₗ[ℝ] SpinSpace where
  toFun f t := qSign (spinPhase g t) * f (t + spinTranslation g)
  map_add' f h := by ext t; simp [mul_add]
  map_smul' c f := by ext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem spinOperator_one : spinOperator 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext t
  change qSign (0 + spinDot 0 t) * f (t + 0) = f t
  simp

theorem spinTranslation_mul (g h : Q) :
    spinTranslation (g * h) = spinTranslation g + spinTranslation h := rfl

theorem spinModulation_mul (g h : Q) :
    spinModulation (g * h) = spinModulation g + spinModulation h := rfl

theorem spinPhase_mul (g h : Q) (t : SpinIndex) :
    spinPhase (g * h) t = spinPhase g t + spinPhase h (t + spinTranslation g) := by
  change (toAdd g.coeff + toAdd h.coeff + qBeta (toAdd g.base) (toAdd h.base)) +
    spinDot (spinModulation (g * h)) t = _
  rw [spinModulation_mul, spinDot_add_left]
  simp only [spinPhase, spinDot_add_right]
  have hd : qBeta (toAdd g.base) (toAdd h.base) =
      spinDot (spinModulation h) (spinTranslation g) := by
    simp only [qBeta, spinDot, spinModulation, spinTranslation, mul_comm]
  rw [hd]
  ring

theorem spinOperator_mul (g h : Q) :
    spinOperator (g * h) = (spinOperator g).comp (spinOperator h) := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [spinOperator, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    spinTranslation_mul, spinPhase_mul, qSign_add]
  rw [add_assoc]
  ring

/-- The operator is invertible, with inverse the operator of the group inverse. -/
noncomputable def spinEquiv (g : Q) : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  { spinOperator g with
    invFun := spinOperator g⁻¹
    left_inv := by
      intro f
      have h := congrArg (fun e : SpinSpace →ₗ[ℝ] SpinSpace => e f) (spinOperator_mul g⁻¹ g)
      simpa using h.symm
    right_inv := by
      intro f
      have h := congrArg (fun e : SpinSpace →ₗ[ℝ] SpinSpace => e f) (spinOperator_mul g g⁻¹)
      simpa using h.symm }

/-- The concrete 4096-dimensional real representation of the coordinate model Q.
This realizes the faithful representation described in Seysen §9.1; compatibility
with the code-loop basis of §7.2 and the FLM basis remains to be proved. -/
noncomputable def spinRepresentation : Q →* (SpinSpace ≃ₗ[ℝ] SpinSpace) where
  toFun := spinEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro f
    exact DFunLike.congr_fun spinOperator_one f
  map_mul' g h := by
    apply LinearEquiv.ext
    intro f
    exact DFunLike.congr_fun (spinOperator_mul g h) f

/-- The operator determines the central sign, modulation, and translation coordinates. -/
theorem spinRepresentation_eq_one_iff (g : Q) : spinRepresentation g = 1 ↔ g = 1 := by
  constructor
  · intro hg
    have hp (t : SpinIndex) : qSign (spinPhase g t) = 1 := by
      have ht := congrArg (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace => e (fun _ => 1) t) hg
      change qSign (spinPhase g t) * 1 = 1 at ht
      simpa using ht
    have hc : toAdd g.coeff = 0 := by
      have ht := (qSign_eq_one_iff _).mp (hp 0)
      simpa [spinPhase] using ht
    have hb : spinModulation g = 0 := by
      funext i
      have ht := (qSign_eq_one_iff _).mp (hp (Pi.single i 1))
      simpa [spinPhase, hc, spinDot, Pi.single_apply, mul_ite] using ht
    have ha : spinTranslation g = 0 := by
      have ht := congrArg (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace =>
        e (fun t => if t = 0 then 1 else 0) 0) hg
      change qSign (spinPhase g 0) * (if 0 + spinTranslation g = 0 then 1 else 0) = 1 at ht
      rw [hp 0, one_mul, zero_add] at ht
      by_contra hn
      simp [hn] at ht
    apply NormalizedCocycleExtension.Extension.ext
    · apply Multiplicative.toAdd.injective
      funext i
      obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective i
      cases j with
      | inl j => exact congrFun ha j
      | inr j => exact congrFun hb j
    · exact Multiplicative.toAdd.injective hc
  · rintro rfl
    exact spinRepresentation.map_one

/-- Faithfulness follows from the proved trivial-kernel computation. -/
theorem spinRepresentation_injective : Function.Injective spinRepresentation :=
  (MonoidHom.ker_eq_bot_iff spinRepresentation).mp <| by
    ext g
    exact spinRepresentation_eq_one_iff g

/-- The Euclidean pairing in the Schrödinger basis. -/
def spinPairing (f h : SpinSpace) : ℝ := ∑ t, f t * h t

/-- Every coordinate-model operator preserves the Euclidean pairing. -/
theorem spinRepresentation_pairing (g : Q) (f h : SpinSpace) :
    spinPairing (spinRepresentation g f) (spinRepresentation g h) = spinPairing f h := by
  change (∑ t, (qSign (spinPhase g t) * f (t + spinTranslation g)) *
    (qSign (spinPhase g t) * h (t + spinTranslation g))) = _
  calc
    _ = ∑ t, f (t + spinTranslation g) * h (t + spinTranslation g) := by
      apply Finset.sum_congr rfl
      intro t ht
      calc
        _ = (qSign (spinPhase g t) * qSign (spinPhase g t)) *
            (f (t + spinTranslation g) * h (t + spinTranslation g)) := by ring
        _ = _ := by rw [qSign_sq, one_mul]
    _ = _ := (Equiv.addRight (spinTranslation g)).sum_comp Finset.univ
      (fun t => f t * h t) (by simp)

/-- There are exactly 4096 binary Schrödinger labels. -/
theorem spinIndex_card : Fintype.card SpinIndex = 4096 := by
  simp [ZMod.card]

/-- The orthogonal subgroup of the real Schrödinger space, with closure laws proved. -/
noncomputable def spinOrthogonalSubgroup : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) where
  carrier := {e | ∀ f h, spinPairing (e f) (e h) = spinPairing f h}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb f h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha f h
    have hp := ha (a.symm f) (a.symm h)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hp
    exact hp.symm

/-- The actual image of Q under its proved faithful representation. -/
noncomputable def spinImage : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) := spinRepresentation.range

/-- Orthogonal operators normalizing the extraspecial image. This is the coordinate
normalizer realization of the standard holomorph in Seysen §9.1. The local group H
additionally requires compatibility with the Leech action and a central quotient. -/
noncomputable def spinHolomorphSubgroup : Subgroup (SpinSpace ≃ₗ[ℝ] SpinSpace) :=
  Subgroup.normalizer (spinImage : Set (SpinSpace ≃ₗ[ℝ] SpinSpace)) ⊓ spinOrthogonalSubgroup

/-- The carrier of the coordinate orthogonal normalizer. -/
noncomputable abbrev SpinHolomorph := spinHolomorphSubgroup

/-- The faithful representation identifies Q with its actual image. -/
noncomputable def spinImageEquiv : Q ≃* spinImage :=
  MonoidHom.ofInjective spinRepresentation_injective

/-- The concrete inclusion of Q in its coordinate orthogonal normalizer. -/
noncomputable def spinHolomorphIncl : Q →* SpinHolomorph :=
  spinRepresentation.codRestrict spinHolomorphSubgroup fun g =>
    ⟨spinImage.le_normalizer ⟨g, rfl⟩, spinRepresentation_pairing g⟩

/-- The actual conjugation action of the orthogonal normalizer on Q, transported
through the proved image equivalence. No automorphism action is supplied as data. -/
noncomputable def spinConjugation : SpinHolomorph →* MulAut Q :=
  (MulAut.congr spinImageEquiv.symm).toMonoidHom.comp <|
    spinImage.normalizerMonoidHom.comp <|
      Subgroup.inclusion (show spinHolomorphSubgroup ≤
        Subgroup.normalizer (spinImage : Set (SpinSpace ≃ₗ[ℝ] SpinSpace)) from inf_le_left)

end SpinCoordinates

/-! ## Concrete local extension

Conjugation gives the normalizer action on Q and hence on its center quotient.
The explicit binary matrix identifies that quotient with the actual Λ/2Λ.
The source fiber product and its simultaneous central-sign quotient therefore
have their group laws and natural maps constructed without data holes.
-/


open Multiplicative

noncomputable def qCenterQuotientAut (a : MulAut Q) : (Q ⧸ centerQ) ≃* (Q ⧸ centerQ) :=
  QuotientGroup.congr centerQ centerQ a (Subgroup.map_center_eq a)

@[simp] theorem qCenterQuotientAut_mk (a : MulAut Q) (g : Q) :
    qCenterQuotientAut a (QuotientGroup.mk g) = QuotientGroup.mk (a g) := rfl

noncomputable def qCenterQuotientAction : MulAut Q →* MulAut (Q ⧸ centerQ) where
  toFun := qCenterQuotientAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective centerQ x
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective centerQ x
    rfl

noncomputable def qBinaryMulAction : MulAut Q →* MulAut (Multiplicative (Fin 24 → ZMod 2)) :=
  (MulAut.congr qQuotientEquiv).toMonoidHom.comp qCenterQuotientAction

noncomputable def binaryMulAutLinearEquiv (a : MulAut (Multiplicative (Fin 24 → ZMod 2))) :
    (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  let e : (Fin 24 → ZMod 2) ≃+ (Fin 24 → ZMod 2) :=
    { toFun v := toAdd (a (ofAdd v))
      invFun v := toAdd (a.symm (ofAdd v))
      left_inv v := a.symm_apply_apply v
      right_inv v := a.apply_symm_apply v
      map_add' u v := a.map_mul u v }
  { e with map_smul' := ZMod.map_smul e }

noncomputable def binaryMulAutLinear : MulAut (Multiplicative (Fin 24 → ZMod 2)) →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) where
  toFun := binaryMulAutLinearEquiv
  map_one' := by apply LinearEquiv.ext; intro v; rfl
  map_mul' a b := by apply LinearEquiv.ext; intro v; rfl

noncomputable def qBinaryAction : MulAut Q →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :=
  binaryMulAutLinear.comp qBinaryMulAction

noncomputable def spinBinaryAction : SpinHolomorph →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :=
  qBinaryAction.comp spinConjugation

noncomputable def leechBinaryBasisEquiv :
    (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := leechHyperbolicMatrix.mulVecLin
  invFun := leechHyperbolicInverse.mulVecLin
  left_inv v := by
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, leechHyperbolicMatrix_inverse.2,
      Matrix.mulVecLin_one, LinearMap.id_apply]
  right_inv v := by
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, leechHyperbolicMatrix_inverse.1,
      Matrix.mulVecLin_one, LinearMap.id_apply]
  map_add' := leechHyperbolicMatrix.mulVecLin.map_add
  map_smul' := leechHyperbolicMatrix.mulVecLin.map_smul

noncomputable def leechHyperbolicCoordinates : LeechModTwo ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  leechModTwoLinearEquiv.trans leechBinaryBasisEquiv.symm

noncomputable def leechBinaryAction : leechIsomSubgroup →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) where
  toFun e := leechHyperbolicCoordinates.symm.trans
    ((leechModTwoAction e).trans leechHyperbolicCoordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.trans_apply]

noncomputable def localFiberSubgroup : Subgroup (SpinHolomorph × leechIsomSubgroup) where
  carrier := {g | spinBinaryAction g.1 = leechBinaryAction g.2}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ha hb
    change spinBinaryAction (a.1 * b.1) = leechBinaryAction (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change spinBinaryAction a.1⁻¹ = leechBinaryAction a.2⁻¹
    rw [map_inv, map_inv, ha]


theorem spinConjugation_incl (g k : Q) :
    spinConjugation (spinHolomorphIncl g) k = g * k * g⁻¹ := by
  apply spinRepresentation_injective
  change spinRepresentation (spinImageEquiv.symm _) = _
  have h (e : spinImage) : spinRepresentation (spinImageEquiv.symm e) = e.val :=
    MonoidHom.apply_ofInjective_symm spinRepresentation_injective e
  rw [h]
  change spinRepresentation g * spinRepresentation k * (spinRepresentation g)⁻¹ = _
  rw [map_mul, map_mul, map_inv]

@[simp] theorem qQuotientEquiv_mk (g : Q) :
    qQuotientEquiv (QuotientGroup.mk g) = qQuotHom g := rfl

theorem qBinaryAction_apply (a : MulAut Q) (g : Q) :
    qBinaryAction a (toAdd (qQuotHom g)) = toAdd (qQuotHom (a g)) := by
  change toAdd (qQuotientEquiv (qCenterQuotientAut a
    (qQuotientEquiv.symm (qQuotHom g)))) = _
  rw [← qQuotientEquiv_mk, qQuotientEquiv.symm_apply_apply]
  rfl

theorem spinBinaryAction_incl (g : Q) : spinBinaryAction (spinHolomorphIncl g) = 1 := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨k, hk⟩ := qQuotHom_surjective (ofAdd v)
  change qBinaryAction (spinConjugation (spinHolomorphIncl g)) v = v
  rw [← show toAdd (qQuotHom k) = v from congrArg toAdd hk]
  rw [qBinaryAction_apply, spinConjugation_incl]
  simp only [map_mul, map_inv]
  simp

noncomputable def localFiberIncl : Q →* localFiberSubgroup :=
  ((spinHolomorphIncl.prod (1 : Q →* leechIsomSubgroup))).codRestrict localFiberSubgroup
    (fun g => by
      change spinBinaryAction (spinHolomorphIncl g) = leechBinaryAction 1
      simp [spinBinaryAction_incl])


noncomputable def localDiagonalSubgroup : Subgroup localFiberSubgroup where
  carrier := {g | ∃ c : ZMod 2,
    (∀ u, g.val.1.val u = qSign c • u) ∧
    (∀ x, g.val.2.val x = qSign c • x)}
  one_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> intro u <;> simp
  mul_mem' := by
    rintro a b ⟨c, hc, hc'⟩ ⟨d, hd, hd'⟩
    refine ⟨c + d, ?_, ?_⟩
    · intro u
      change (a.val.1.val * b.val.1.val) u = _
      rw [LinearEquiv.mul_apply, hd, map_smul, hc, smul_smul, qSign_add, mul_comm]
    · intro u
      change (a.val.2.val * b.val.2.val) u = _
      rw [LinearEquiv.mul_apply, hd', map_smul, hc', smul_smul, qSign_add, mul_comm]
  inv_mem' := by
    rintro a ⟨c, hc, hc'⟩
    refine ⟨c, ?_, ?_⟩
    · intro u
      change a.val.1.val.symm u = _
      apply a.val.1.val.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_smul, qSign_sq, one_smul]
    · intro u
      change a.val.2.val.symm u = _
      apply a.val.2.val.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hc', smul_smul, qSign_sq, one_smul]

noncomputable instance localDiagonalNormal : localDiagonalSubgroup.Normal := by
  constructor
  rintro n ⟨c, hc, hc'⟩ g
  refine ⟨c, ?_, ?_⟩
  · intro u
    change (g.val.1.val * n.val.1.val * g.val.1.val.symm) u = _
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, map_smul,
      LinearEquiv.apply_symm_apply]
  · intro u
    change (g.val.2.val * n.val.2.val * g.val.2.val.symm) u = _
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc', map_smul,
      LinearEquiv.apply_symm_apply]

noncomputable def localFiberProjection : localFiberSubgroup →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp
    ((MonoidHom.snd SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype)

theorem localDiagonal_le_projection_ker : localDiagonalSubgroup ≤ localFiberProjection.ker := by
  rintro g ⟨c, _, hc⟩
  change QuotientGroup.mk' signsSubgroup g.val.2 = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  by_cases h : c = 0
  · left
    apply LinearEquiv.ext
    intro x
    simpa [h] using hc x
  · right
    intro x
    simpa [qSign, h] using hc x

/-- Conway's local group: the fiber product of the real orthogonal normalizer
of Q with Co₀ over their actions on Λ/2Λ, divided by the simultaneous signs.
Source: Conway, Invent. Math. 79 (1985), §§9–11; Seysen §9.3. The fiber uses
the explicit integer basis and binary change of basis, with no projection
surjectivity or recognition theorem assumed. -/
noncomputable def H : Type := localFiberSubgroup ⧸ localDiagonalSubgroup
noncomputable instance instGroupH : Group H := by
  unfold H
  infer_instance

/-- The inclusion induced by q ↦ (ρ₄₀₉₆(q), 1) in the fiber product. -/
noncomputable def inclQ : Q →* H :=
  (QuotientGroup.mk' localDiagonalSubgroup).comp localFiberIncl

/-- Projection to Co₀/{±1}; simultaneous signs are proved to lie in its kernel. -/
noncomputable def projH : H →* Co1 :=
  QuotientGroup.lift localDiagonalSubgroup localFiberProjection localDiagonal_le_projection_ker


/-! ## Short-vector geometry for the local action

The three explicit families lie in the lattice and have integer squared norm
32 (real squared norm 4). The Golay weight constraints give the minimum
norm bound. Short vectors in one class of Λ/2Λ differ only by a global sign;
Co₀ preserves their squared norms by its defining Euclidean isometry law.
-/

def leechSquareSum (u : Fin 24 → ℤ) : ℤ := ∑ i, u i ^ 2

theorem leechResidue_dvd (u : Fin 24 → ℤ) (m : ℤ) (c : Fin 24 → ZMod 2)
    (h : ∀ i, (u i : ZMod 4) = (m : ZMod 4) + 2 * ((c i).val : ZMod 4)) (i : Fin 24) :
    4 ∣ u i - m - 2 * ((c i).val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  push_cast
  rw [h i]
  ring

theorem leechEvenCode_square_lower (u : Fin 24 → ℤ) (c : Fin 24 → ZMod 2)
    (h : ∀ i, (u i : ZMod 4) = 2 * ((c i).val : ZMod 4)) :
    (4 : ℤ) * (∑ i, (c i).val : ℕ) ≤ leechSquareSum u := by
  have hi (i : Fin 24) : (4 : ℤ) * (c i).val ≤ u i ^ 2 := by
    have hdiv : 4 ∣ u i - 2 * ((c i).val : ℤ) := by
      simpa using leechResidue_dvd u 0 c (by simpa using h) i
    have hc : (c i).val = 0 ∨ (c i).val = 1 := by
      have := ZMod.val_lt (c i)
      omega
    rcases hc with hc | hc
    · simp [hc, sq_nonneg]
    · rw [hc] at hdiv ⊢
      norm_num at hdiv ⊢
      obtain ⟨k, hk⟩ := hdiv
      have hu : u i ≤ -2 ∨ 2 ≤ u i := by omega
      rcases hu with hu | hu <;> nlinarith [sq_nonneg (u i + 2), sq_nonneg (u i - 2)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [leechSquareSum, Nat.cast_sum, Finset.mul_sum] using hs

theorem integral_four_square_lower (u : Fin 24 → ℤ) (hfour : ∀ i, 4 ∣ u i)
    (height : 8 ∣ ∑ i, u i) (hn : u ≠ 0) : 32 ≤ leechSquareSum u := by
  by_contra h
  have hsmall : leechSquareSum u ≤ 31 := by omega
  have hcoord (i : Fin 24) : u i = -4 ∨ u i = 0 ∨ u i = 4 := by
    have hs : u i ^ 2 ≤ leechSquareSum u :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    have hb : -5 ≤ u i ∧ u i ≤ 5 := by
      constructor <;> nlinarith [sq_nonneg (u i + 6), sq_nonneg (u i - 6)]
    obtain ⟨k, hk⟩ := hfour i
    omega
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    exact funext h
  have hjs : u j ^ 2 = 16 := by rcases hcoord j with hj' | hj' | hj' <;> simp_all
  have hz (k : Fin 24) (hk : k ≠ j) : u k = 0 := by
    by_contra hkn
    have hks : u k ^ 2 = 16 := by rcases hcoord k with hk' | hk' | hk' <;> simp_all
    have hl (i : Fin 24) : (if i = j then 16 else 0) + (if i = k then 16 else 0) ≤ u i ^ 2 := by
      by_cases hij : i = j
      · subst i
        simp [hk.symm, hjs]
      · by_cases hik : i = k
        · subst i; simp [hk, hks]
        · simp [hij, hik, sq_nonneg]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    have hs' : 32 ≤ leechSquareSum u := by
      simpa [leechSquareSum, Finset.sum_add_distrib] using hs
    omega
  have hu : u = Pi.single j (u j) := by
    ext i
    by_cases hi : i = j
    · subst i; simp
    · simp [hi, hz i hi]
  have hs : (∑ i, u i) = u j := by rw [hu]; simp
  rw [hs] at height
  rcases hcoord j with hj' | hj' | hj'
  · rw [hj'] at height; norm_num at height
  · exact hj hj'
  · rw [hj'] at height; norm_num at height


theorem leechOddCode_square_lower (u : Fin 24 → ℤ) (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode)
    (h : ∀ i, (u i : ZMod 4) = 1 + 2 * ((c i).val : ZMod 4))
    (hs : ((∑ i, u i : ℤ) : ZMod 8) = 4) : 32 ≤ leechSquareSum u := by
  by_contra hn
  have hsmall : leechSquareSum u ≤ 31 := by omega
  have hdiv (i : Fin 24) : 4 ∣ u i - 1 - 2 * ((c i).val : ℤ) :=
    leechResidue_dvd u 1 c h i
  have hodd (i : Fin 24) : u i % 2 = 1 := by
    obtain ⟨k, hk⟩ := hdiv i
    omega
  have hpos (i : Fin 24) : 1 ≤ u i ^ 2 := by
    have hzero : u i ≠ 0 := by intro h0; have := hodd i; simp [h0] at this
    have hl : u i ≤ -1 ∨ 1 ≤ u i := by omega
    rcases hl with hl | hl <;> nlinarith [sq_nonneg (u i + 1), sq_nonneg (u i - 1)]
  have hunit (j : Fin 24) : u j = -1 ∨ u j = 1 := by
    have hl (i : Fin 24) : 1 + (if i = j then u j ^ 2 - 1 else 0) ≤ u i ^ 2 := by
      by_cases hij : i = j
      · subst i; simp
      · simpa [hij] using hpos i
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    have hlower : 24 + (u j ^ 2 - 1) ≤ leechSquareSum u := by
      simpa [leechSquareSum, Finset.sum_add_distrib] using hsum
    have hb : u j ^ 2 ≤ 8 := by linarith
    have hbounds : -2 ≤ u j ∧ u j ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg (u j + 3), sq_nonneg (u j - 3)]
    have := hodd j
    omega
  have hform (i : Fin 24) : u i = 1 - 2 * ((c i).val : ℤ) := by
    obtain ⟨k, hk⟩ := hdiv i
    have hval := ZMod.val_lt (c i)
    have hu := hunit i
    omega
  have hsum : (∑ i, u i) = 24 - 2 * (∑ i, (c i).val : ℕ) := by
    simp_rw [hform]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.cast_sum]
    norm_num
  obtain ⟨k, hk⟩ := golayCode_weight_four c hc
  have hz : ((∑ i, u i : ℤ) : ZMod 8) = 0 := by
    rw [hsum, hk]
    push_cast
    ring_nf
    rw [show (24 : ZMod 8) = 0 by decide, show (8 : ZMod 8) = 0 by decide,
      mul_zero, sub_zero]
  rw [hz] at hs
  exact (by decide : (0 : ZMod 8) ≠ 4) hs

theorem leechIntegral_minimum (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral)
    (hn : u ≠ 0) : 32 ≤ leechSquareSum u := by
  obtain ⟨m, hm, c, hc, h, hs⟩ := (mem_leechIntegral_iff_source u).mp hu
  rcases hm with rfl | rfl
  · by_cases hc0 : c = 0
    · subst c
      have hfour (i : Fin 24) : 4 ∣ u i := by
        simpa using leechResidue_dvd u 0 0 h i
      have height : 8 ∣ ∑ i, u i := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
        simpa using hs
      exact integral_four_square_lower u hfour height hn
    · have hw := golayCode_weight_ge_eight c hc hc0
      have hw' : (8 : ℤ) ≤ (∑ i, (c i).val : ℕ) := by exact_mod_cast hw
      have hl := leechEvenCode_square_lower u c (by simpa using h)
      linarith
  · exact leechOddCode_square_lower u c hc h (by simpa using hs)


theorem griessOctadSignMask_weight (d : Fin 759) (e : Fin 64) :
    golayMaskWeight (griessOctadSignMask d e) = trialityBitWeight8 (trialityEvenMask e) := by
  have heq : golayMaskSupport (griessOctadSignMask d e) =
      (Finset.univ.filter (fun k : Fin 8 => (trialityEvenMask e).testBit k.val)).image
        (golayOctadCoordinate d) := by
    ext i
    simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [griessOctadSignMask_testBit]
  rw [← golayMaskSupport_card, heq,
    Finset.card_image_of_injective _ (golayOctadCoordinate_injective d), Finset.card_filter]
  rfl

theorem griessOctadSignMask_subset (d : Fin 759) (e : Fin 64) (i : Fin 24)
    (hi : (griessOctadSignMask d e).testBit i.val = true) :
    (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true := by
  obtain ⟨k, _, rfl⟩ := (griessOctadSignMask_testBit d e i).mp hi
  exact golayOctadCoordinate_mem d k

theorem griessOctad_squareSum (d : Fin 759) (e : Fin 64) :
    leechSquareSum (griessShortIntegral (Sum.inr (Sum.inl (d, e)))) = 32 := by
  have hpoint (i : Fin 24) : griessShortIntegral (Sum.inr (Sum.inl (d, e))) i ^ 2 =
      4 * (if (golayEncodedMask (golayOctadLabel d).val).testBit i.val then 1 else 0) := by
    unfold griessShortIntegral
    split_ifs <;> simp_all
  unfold leechSquareSum
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  have hweight : golayMaskWeight (golayEncodedMask (golayOctadLabel d).val) = 8 := by
    simpa only [golayMaskSupport_card] using golayOctad_support_card d
  have hw : (∑ i : Fin 24, if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      then (1 : ℤ) else 0) = 8 := by
    exact_mod_cast hweight
  rw [hw]
  norm_num

theorem griessOdd_squareSum (d : Fin 2048) (j : Fin 24) :
    leechSquareSum (griessShortIntegral (Sum.inr (Sum.inr (d, j)))) = 32 := by
  have hpoint (i : Fin 24) : griessShortIntegral (Sum.inr (Sum.inr (d, j))) i ^ 2 =
      1 + (if i = j then 8 else 0) := by
    unfold griessShortIntegral
    split_ifs <;> simp_all
  unfold leechSquareSum
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib]


theorem griessOctad_integral_sum (d : Fin 759) (e : Fin 64) :
    (∑ i, griessShortIntegral (Sum.inr (Sum.inl (d, e))) i) =
      16 - 4 * (trialityBitWeight8 (trialityEvenMask e) : ℤ) := by
  have hpoint (i : Fin 24) : griessShortIntegral (Sum.inr (Sum.inl (d, e))) i =
      2 * (if (golayEncodedMask (golayOctadLabel d).val).testBit i.val then 1 else 0) -
        4 * (if (griessOctadSignMask d e).testBit i.val then 1 else 0) := by
    by_cases hm : (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true
    · by_cases hd : (griessOctadSignMask d e).testBit i.val = true
      · simp [griessShortIntegral, hm, hd]
      · simp [griessShortIntegral, hm, hd]
    · have hd : (griessOctadSignMask d e).testBit i.val ≠ true :=
        fun hi => hm (griessOctadSignMask_subset d e i hi)
      simp [griessShortIntegral, hm, hd]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hw : (∑ i : Fin 24, if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      then (1 : ℤ) else 0) = 8 := by
    have h : golayMaskWeight (golayEncodedMask (golayOctadLabel d).val) = 8 := by
      simpa only [golayMaskSupport_card] using golayOctad_support_card d
    exact_mod_cast h
  have he : (∑ i : Fin 24, if (griessOctadSignMask d e).testBit i.val
      then (1 : ℤ) else 0) = trialityBitWeight8 (trialityEvenMask e) := by
    exact_mod_cast griessOctadSignMask_weight d e
  rw [hw, he]
  norm_num

theorem griessOctad_mem_leech (d : Fin 759) (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, golayEncoder (golayLabelCoefficients (golayOctadLabel d)),
    ⟨_, rfl⟩, ?_, ?_⟩
  · intro i
    change ((if (golayEncodedMask (golayOctadLabel d).val).testBit i.val then
      if (griessOctadSignMask d e).testBit i.val then -2 else 2 else 0 : ℤ) : ZMod 4) =
        0 + 2 * ((golayEncoder (golayLabelCoefficients (golayOctadLabel d)) i).val : ZMod 4)
    rw [golayLabelEncoder_match]
    have hneg : ((-2 : ℤ) : ZMod 4) = 2 := by decide
    cases hm : (golayEncodedMask (golayOctadLabel d).val).testBit i.val <;>
      cases hd : (griessOctadSignMask d e).testBit i.val <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, zero_add, Nat.cast_zero,
          Nat.cast_one, mul_zero, mul_one, Int.cast_zero, Int.cast_ofNat, hneg]
  · have height : 8 ∣ ∑ i, griessShortIntegral (Sum.inr (Sum.inl (d, e))) i := by
      obtain ⟨k, hk⟩ := trialityEvenMask_even e
      refine ⟨2 - (k : ℤ), ?_⟩
      rw [griessOctad_integral_sum, hk]
      push_cast
      ring
    simpa only [Int.cast_zero, mul_zero] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr height


theorem griessCoordinatePair_ne (p : Fin 276) :
    (griessCoordinatePair p).1 ≠ (griessCoordinatePair p).2 :=
  ne_of_lt (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

theorem griessPair_squareSum (s : Fin 2) (p : Fin 276) :
    leechSquareSum (griessShortIntegral (Sum.inl (s, p))) = 32 := by
  have hne := griessCoordinatePair_ne p
  have hpoint (i : Fin 24) : griessShortIntegral (Sum.inl (s, p)) i ^ 2 =
      (if i = (griessCoordinatePair p).1 then 16 else 0) +
        (if i = (griessCoordinatePair p).2 then 16 else 0) := by
    unfold griessShortIntegral
    split_ifs <;> simp_all
  unfold leechSquareSum
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib]

theorem griessPair_mem_leech (s : Fin 2) (p : Fin 276) :
    griessShortIntegral (Sum.inl (s, p)) ∈ leechIntegral := by
  refine ⟨0, 0, ?_, ?_⟩
  · intro i
    change ((4 * (if i = (griessCoordinatePair p).1 then 1 else 0) +
      (if s = 0 then -4 else 4) * (if i = (griessCoordinatePair p).2 then 1 else 0) : ℤ) :
        ZMod 4) = 0 + 2 * ∑ j, ((0 : ℤ) : ZMod 4) * (golayGeneratorBit j i : ZMod 4)
    have h4 : (4 : ZMod 4) = 0 := by decide
    push_cast
    simp only [h4, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, zero_add]
    split_ifs <;> simp
  · have hs : (∑ i, griessShortIntegral (Sum.inl (s, p)) i) =
        4 + (if s = 0 then -4 else 4) := by
      simp [griessShortIntegral, Finset.sum_add_distrib, mul_ite]
    change ((∑ i, griessShortIntegral (Sum.inl (s, p)) i : ℤ) : ZMod 8) = 0
    rw [hs]
    fin_cases s <;> decide

theorem griessOdd_integral_sum (d : Fin 2048) (j : Fin 24) :
    (∑ i, griessShortIntegral (Sum.inr (Sum.inr (d, j))) i) =
      20 - 2 * (golayMaskWeight (golayEncodedMask d.val) : ℤ) +
        8 * (if (golayEncodedMask d.val).testBit j.val then 1 else 0) := by
  have hpoint (i : Fin 24) : griessShortIntegral (Sum.inr (Sum.inr (d, j))) i =
      1 - 2 * (if (golayEncodedMask d.val).testBit i.val then 1 else 0) -
        4 * (if i = j then (if (golayEncodedMask d.val).testBit j.val then -1 else 1) else 0) := by
    unfold griessShortIntegral
    split_ifs <;> simp_all
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hw : (∑ i : Fin 24, if (golayEncodedMask d.val).testBit i.val then (1 : ℤ) else 0) =
      golayMaskWeight (golayEncodedMask d.val) := by
    exact_mod_cast (rfl : (∑ i : Fin 24, if (golayEncodedMask d.val).testBit i.val
      then (1 : ℕ) else 0) = golayMaskWeight (golayEncodedMask d.val))
  rw [hw]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases hb : (golayEncodedMask d.val).testBit j.val <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

theorem griessOdd_mem_leech (d : Fin 2048) (j : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (d, j))) ∈ leechIntegral := by
  let dl : Fin 4096 := ⟨d.val, by omega⟩
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨1, Or.inr rfl, golayEncoder (golayLabelCoefficients dl), ⟨_, rfl⟩, ?_, ?_⟩
  · intro i
    change (((if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
      (if i = j then -3 else 1) : ℤ) : ZMod 4) =
        1 + 2 * ((golayEncoder (golayLabelCoefficients dl) i).val : ZMod 4)
    rw [golayLabelEncoder_match]
    change _ = 1 + 2 * ((if (golayEncodedMask d.val).testBit i.val then 1 else 0 : ℕ) : ZMod 4)
    by_cases hi : i = j <;> cases hb : (golayEncodedMask d.val).testBit i.val
    all_goals simp only [hi, Bool.false_eq_true, ite_false, ite_true]
    all_goals decide
  · have hw : 4 ∣ golayMaskWeight (golayEncodedMask d.val) := by
      have h := golayEncodedMask_weights dl
      change golayMaskWeight (golayEncodedMask d.val) ∈ ([0, 8, 12, 16, 24] : List ℕ) at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h <;> rw [h] <;> norm_num
    obtain ⟨k, hk⟩ := hw
    have height : 8 ∣ (∑ i, griessShortIntegral (Sum.inr (Sum.inr (d, j))) i) - 4 := by
      refine ⟨2 - (k : ℤ) + (if (golayEncodedMask d.val).testBit j.val then 1 else 0), ?_⟩
      rw [griessOdd_integral_sum, hk]
      push_cast
      ring
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr height
    simp only [Int.cast_sub, Int.cast_ofNat] at hc
    have he := sub_eq_zero.mp hc
    simpa only [Int.cast_one, mul_one] using he

theorem griessShortIntegral_mem (r : GriessShortIndex) : griessShortIntegral r ∈ leechIntegral := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · exact griessPair_mem_leech s p
  · exact griessOctad_mem_leech d e
  · exact griessOdd_mem_leech d j

theorem griessShortIntegral_squareSum (r : GriessShortIndex) :
    leechSquareSum (griessShortIntegral r) = 32 := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · exact griessPair_squareSum s p
  · exact griessOctad_squareSum d e
  · exact griessOdd_squareSum d j

theorem leechSquareSum_nonneg (u : Fin 24 → ℤ) : 0 ≤ leechSquareSum u :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (u i))

theorem leechSquareSum_eq_zero (u : Fin 24 → ℤ) (h : leechSquareSum u = 0) : u = 0 := by
  funext i
  have hi : u i ^ 2 ≤ leechSquareSum u :=
    Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  change u i = 0
  nlinarith [sq_nonneg (u i)]

theorem leechSquareSum_parallelogram (u v : Fin 24 → ℤ) :
    leechSquareSum (u - v) + leechSquareSum (u + v) =
      2 * leechSquareSum u + 2 * leechSquareSum v := by
  simp only [leechSquareSum, Pi.sub_apply, Pi.add_apply, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem leechShort_same_class (u v : leechIntegral)
    (hu : leechSquareSum u.val = 32) (hv : leechSquareSum v.val = 32)
    (h : leechReduction u = leechReduction v) : u = v ∨ u = -v := by
  have hm : u - v ∈ twiceLeechIntegral :=
    QuotientAddGroup.eq_iff_sub_mem.mp h
  obtain ⟨w, hw⟩ := hm
  have hwv : (u - v).val = (fun i => 2 * w.val i) := by
    have hh := congrArg Subtype.val hw
    funext i
    have hi := congrFun hh i
    change ((2 : ℕ) • w).val i = (u - v).val i at hi
    simpa only [two_nsmul, Submodule.coe_add, Pi.add_apply, two_mul] using hi.symm
  have hsq : leechSquareSum (u.val - v.val) = 4 * leechSquareSum w.val := by
    change leechSquareSum (u - v).val = _
    rw [hwv]
    simp only [leechSquareSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  by_cases hz : w.val = 0
  · left
    apply sub_eq_zero.mp
    apply Subtype.ext
    rw [hwv, hz]
    rfl
  · right
    have hmin := leechIntegral_minimum w.val w.property hz
    have hp := leechSquareSum_parallelogram u.val v.val
    rw [hu, hv, hsq] at hp
    have hn := leechSquareSum_nonneg (u.val + v.val)
    have hzero : leechSquareSum (u.val + v.val) = 0 := by omega
    have he := leechSquareSum_eq_zero (u.val + v.val) hzero
    apply eq_neg_of_add_eq_zero_left
    apply Subtype.ext
    exact he

theorem leechEmbedding_pairing (u : Fin 24 → ℤ) :
    stdPairingFun (leechCoordinateEmbedding u) (leechCoordinateEmbedding u) =
      (leechSquareSum u : ℝ) / 8 := by
  have hs : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  simp only [stdPairingFun, leechCoordinateEmbedding, leechSquareSum,
    Int.cast_sum, Int.cast_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change ((u i : ℝ) / Real.sqrt 8) * ((u i : ℝ) / Real.sqrt 8) = (u i : ℝ) ^ 2 / 8
  rw [← pow_two, div_pow, hs]

theorem leechIntegralAction_embedding (e : leechIsomSubgroup) (u : leechIntegral) :
    leechCoordinateEmbedding (leechIntegralAction e u).val =
      e.val (leechCoordinateEmbedding u.val) := by
  have h := leechNormalization.apply_symm_apply
    (leechRealAction e (leechNormalization u))
  exact congrArg Subtype.val h

theorem leechIntegralAction_squareSum (e : leechIsomSubgroup) (u : leechIntegral) :
    leechSquareSum (leechIntegralAction e u).val = leechSquareSum u.val := by
  have h := e.property.1 (leechCoordinateEmbedding u.val) (leechCoordinateEmbedding u.val)
  rw [← leechIntegralAction_embedding, leechEmbedding_pairing, leechEmbedding_pairing] at h
  have hh := (div_left_inj' (by norm_num : (8 : ℝ) ≠ 0)).mp h
  exact_mod_cast hh

/-! ### Exhaustiveness of the three short-vector families

Classify integer squared norm 32 with the Golay source congruences: the even
case has code weight zero or eight, and the odd case has one coordinate of
absolute value three. Fixing the all-one coefficient or the last octad sign
then gives exactly the chosen representatives, up to global sign.
-/

theorem odd_short_coordinates (u : Fin 24 → ℤ) (h : leechSquareSum u = 32)
    (ho : ∀ i, Odd (u i)) : ∃ j : Fin 24,
      (u j = -3 ∨ u j = 3) ∧ ∀ i, i ≠ j → u i = -1 ∨ u i = 1 := by
  have hlow (i : Fin 24) : 1 ≤ u i ^ 2 := by
    obtain ⟨k, hk⟩ := ho i
    have hn : u i ≠ 0 := by omega
    have hb : u i ≤ -1 ∨ 1 ≤ u i := by omega
    rcases hb with hb | hb <;> nlinarith [sq_nonneg (u i + 1), sq_nonneg (u i - 1)]
  have hcoord (j : Fin 24) : u j = -3 ∨ u j = -1 ∨ u j = 1 ∨ u j = 3 := by
    have hp : (24 : ℤ) - 1 + u j ^ 2 ≤ leechSquareSum u := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        show (if i = j then u j ^ 2 else 1) ≤ u i ^ 2 by
          split_ifs with he
          · subst i; rfl
          · exact hlow i)
      have he : (∑ i : Fin 24, if i = j then u j ^ 2 else (1 : ℤ)) = 23 + u j ^ 2 := by
        have ht (i : Fin 24) : (if i = j then u j ^ 2 else (1 : ℤ)) =
            1 + (if i = j then u j ^ 2 - 1 else 0) := by split_ifs <;> ring
        simp_rw [ht]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
      rw [he] at hh
      exact hh
    have hb : -3 ≤ u j ∧ u j ≤ 3 := by
      constructor <;> nlinarith [sq_nonneg (u j + 4), sq_nonneg (u j - 4)]
    obtain ⟨k, hk⟩ := ho j
    omega
  obtain ⟨j, hj⟩ : ∃ j, u j = -3 ∨ u j = 3 := by
    by_contra hn
    push Not at hn
    have hp (i : Fin 24) : u i ^ 2 = 1 := by
      rcases hcoord i with hi | hi | hi | hi <;> simp_all
    have hs : leechSquareSum u = 24 := by simp [leechSquareSum, hp]
    omega
  refine ⟨j, hj, ?_⟩
  have hjs : u j ^ 2 = 9 := by rcases hj with hj | hj <;> rw [hj] <;> norm_num
  intro i hij
  rcases hcoord i with hi | hi | hi | hi
  · exfalso
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      show (if k = i then 9 else if k = j then 9 else (1 : ℤ)) ≤ u k ^ 2 by
        split_ifs with hk hk
        · subst k; rw [hi]; norm_num
        · subst k; rw [hjs]
        · exact hlow k)
    have he : (∑ k : Fin 24, if k = i then 9 else if k = j then 9 else (1 : ℤ)) = 40 := by
      have ht (k : Fin 24) : (if k = i then 9 else if k = j then 9 else (1 : ℤ)) =
          1 + (if k = i then 8 else 0) + (if k = j then 8 else 0) := by
        split_ifs <;> simp_all
      simp_rw [ht]
      simp [Finset.sum_add_distrib]
    rw [he] at hs
    change 40 ≤ leechSquareSum u at hs
    omega
  · exact Or.inl hi
  · exact Or.inr hi
  · exfalso
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      show (if k = i then 9 else if k = j then 9 else (1 : ℤ)) ≤ u k ^ 2 by
        split_ifs with hk hk
        · subst k; rw [hi]; norm_num
        · subst k; rw [hjs]
        · exact hlow k)
    have he : (∑ k : Fin 24, if k = i then 9 else if k = j then 9 else (1 : ℤ)) = 40 := by
      have ht (k : Fin 24) : (if k = i then 9 else if k = j then 9 else (1 : ℤ)) =
          1 + (if k = i then 8 else 0) + (if k = j then 8 else 0) := by
        split_ifs <;> simp_all
      simp_rw [ht]
      simp [Finset.sum_add_distrib]
    rw [he] at hs
    change 40 ≤ leechSquareSum u at hs
    omega

theorem odd_short_source_formula (u : Fin 24 → ℤ) (c : Fin 24 → ZMod 2)
    (h : leechSquareSum u = 32)
    (hr : ∀ i, (u i : ZMod 4) = 1 + 2 * ((c i).val : ZMod 4)) :
    ∃ j : Fin 24, ∀ i,
      u i = (if c i = 1 then -1 else 1) * (if i = j then -3 else 1) := by
  have ho (i : Fin 24) : Odd (u i) := by
    have hd : 4 ∣ u i - 1 - 2 * ((c i).val : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      push_cast
      rw [hr i]
      ring
    obtain ⟨k, hk⟩ := hd
    exact ⟨(c i).val + 2 * k, by omega⟩
  obtain ⟨j, hj, hother⟩ := odd_short_coordinates u h ho
  refine ⟨j, ?_⟩
  intro i
  have hc : (c i).val = 0 ∨ (c i).val = 1 := by have hh := ZMod.val_lt (c i); omega
  have hdiv : 4 ∣ u i - 1 - 2 * ((c i).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
    push_cast
    rw [hr i]
    ring
  by_cases hi : i = j
  · subst i
    rcases hc with hc | hc
    · have he : c j = 0 := (ZMod.val_eq_zero _).mp hc
      simp only [he, zero_ne_one, ite_false, ite_true, one_mul]
      rcases hj with hj | hj
      · exact hj
      · rw [hj, hc] at hdiv; norm_num at hdiv
    · have he : c j = 1 := (ZMod.val_injective 2) (by
        simpa only [show (1 : ZMod 2).val = 1 by decide] using hc)
      simp only [he, ite_true, neg_one_mul, neg_neg]
      rcases hj with hj | hj
      · rw [hj, hc] at hdiv; norm_num at hdiv
      · exact hj
  · rcases hc with hc | hc
    · have he : c i = 0 := (ZMod.val_eq_zero _).mp hc
      simp only [he, zero_ne_one, hi, ite_false, one_mul]
      rcases hother i hi with hui | hui
      · rw [hui, hc] at hdiv; norm_num at hdiv
      · exact hui
    · have he : c i = 1 := (ZMod.val_injective 2) (by
        simpa only [show (1 : ZMod 2).val = 1 by decide] using hc)
      simp only [he, hi, ite_true, ite_false, mul_one]
      rcases hother i hi with hui | hui
      · exact hui
      · rw [hui, hc] at hdiv; norm_num at hdiv

theorem four_short_pair (u : Fin 24 → ℤ) (h : leechSquareSum u = 32)
    (hf : ∀ i, 4 ∣ u i) : ∃ s : Fin 2, ∃ p : Fin 276,
      u = griessShortIntegral (Sum.inl (s, p)) ∨
      u = -griessShortIntegral (Sum.inl (s, p)) := by
  have hcoord (i : Fin 24) : u i = -4 ∨ u i = 0 ∨ u i = 4 := by
    have hs : u i ^ 2 ≤ leechSquareSum u :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    have hb : -5 ≤ u i ∧ u i ≤ 5 := by
      constructor <;> nlinarith [sq_nonneg (u i + 6), sq_nonneg (u i - 6)]
    obtain ⟨k, hk⟩ := hf i
    omega
  let S : Finset (Fin 24) := Finset.univ.filter (fun i => u i ≠ 0)
  have hs : leechSquareSum u = 16 * (S.card : ℤ) := by
    have hp (i : Fin 24) : u i ^ 2 = if i ∈ S then 16 else 0 := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hcoord i with hi | hi | hi <;> rw [hi] <;> norm_num
    simp only [leechSquareSum, hp, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    simp only [S, Finset.inter_filter, Finset.univ_inter]
    ring
  have hc : S.card = 2 := by omega
  obtain ⟨i, j, hij, hsij⟩ := Finset.card_eq_two.mp hc
  have hui : u i = -4 ∨ u i = 4 := by
    have hi : i ∈ S := by rw [hsij]; simp
    have hn : u i ≠ 0 := (Finset.mem_filter.mp hi).2
    rcases hcoord i with he | he | he <;> simp_all
  have huj : u j = -4 ∨ u j = 4 := by
    have hj : j ∈ S := by rw [hsij]; simp
    have hn : u j ≠ 0 := (Finset.mem_filter.mp hj).2
    rcases hcoord j with he | he | he <;> simp_all
  have hzero (k : Fin 24) (hki : k ≠ i) (hkj : k ≠ j) : u k = 0 := by
    by_contra hn
    have hk : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hn⟩
    rw [hsij] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    exact hk.elim hki hkj
  have hsorted (i j : Fin 24) (hlt : i < j)
      (hui : u i = -4 ∨ u i = 4) (huj : u j = -4 ∨ u j = 4)
      (hz : ∀ k, k ≠ i → k ≠ j → u k = 0) :
      ∃ s : Fin 2, ∃ p : Fin 276,
        u = griessShortIntegral (Sum.inl (s, p)) ∨
        u = -griessShortIntegral (Sum.inl (s, p)) := by
    let p := griessCoordinatePairEquiv.symm ⟨(i, j), by
      simp only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt⟩
    have hp : griessCoordinatePair p = (i, j) :=
      congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)
    have hne : i ≠ j := ne_of_lt hlt
    rcases hui with hui | hui <;> rcases huj with huj | huj
    · refine ⟨1, p, Or.inr ?_⟩
      funext k
      simp only [griessShortIntegral, hp, Pi.neg_apply]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
    · refine ⟨0, p, Or.inr ?_⟩
      funext k
      simp only [griessShortIntegral, hp, Pi.neg_apply]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
    · refine ⟨0, p, Or.inl ?_⟩
      funext k
      simp only [griessShortIntegral, hp]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
    · refine ⟨1, p, Or.inl ?_⟩
      funext k
      simp only [griessShortIntegral, hp]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hsorted i j hlt hui huj hzero
  · exact hsorted j i hlt huj hui (fun k hk hk' => hzero k hk' hk)

theorem odd_short_catalog (u : Fin 24 → ℤ) (h : leechSquareSum u = 32)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hr : ∀ i, (u i : ZMod 4) = 1 + 2 * ((c i).val : ZMod 4)) :
    ∃ d : Fin 2048, ∃ j : Fin 24,
      u = griessShortIntegral (Sum.inr (Sum.inr (d, j))) ∨
      u = -griessShortIntegral (Sum.inr (Sum.inr (d, j))) := by
  obtain ⟨a, ha⟩ := hc
  let a0 := a - Pi.single 11 (a 11)
  have ha0 : a0 11 = 0 := by simp [a0]
  obtain ⟨dl, hdl⟩ := golayLabelCoefficients_bijective.2 a0
  have hdlo : dl.val < 2048 := (golayLabel_last_zero dl).mp (by rw [hdl]; exact ha0)
  let d : Fin 2048 := ⟨dl.val, hdlo⟩
  have he (i : Fin 24) : (golayEncoder a0 i = 1) ↔
      (golayEncodedMask d.val).testBit i.val = true := by
    rw [← hdl]
    have hv := golayLabelEncoder_match dl i
    change (golayEncoder (golayLabelCoefficients dl) i = 1) ↔
      (golayEncodedMask dl.val).testBit i.val = true
    cases hb : (golayEncodedMask dl.val).testBit i.val
    · rw [hb] at hv
      have hz : golayEncoder (golayLabelCoefficients dl) i = 0 := (ZMod.val_eq_zero _).mp hv
      simp [hz]
    · rw [hb] at hv
      have hz : golayEncoder (golayLabelCoefficients dl) i = 1 :=
        (ZMod.val_injective 2) (by
          simpa only [ite_true, show (1 : ZMod 2).val = 1 by decide] using hv)
      simp [hz]
  have hab : a 11 = 0 ∨ a 11 = 1 := by
    have hv := ZMod.val_lt (a 11)
    have hv' : (a 11).val = 0 ∨ (a 11).val = 1 := by omega
    rcases hv' with hv' | hv'
    · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
    · exact Or.inr ((ZMod.val_injective 2) (by
        simpa only [show (1 : ZMod 2).val = 1 by decide] using hv'))
  rcases hab with hab | hab
  · have heq : golayEncoder a0 = c := by simp only [a0, hab, Pi.single_zero, sub_zero]; exact ha
    obtain ⟨j, hj⟩ := odd_short_source_formula u (golayEncoder a0) h (by rw [heq]; exact hr)
    refine ⟨d, j, Or.inl ?_⟩
    funext i
    rw [hj i]
    simp only [griessShortIntegral, he i]
  · have heq : golayEncoder a0 = c - (fun _ => 1) := by
      simp only [a0, hab, map_sub, golay_all_one, ha]
    have hflip : ∀ z : ZMod 2,
        -(1 + 2 * (z.val : ZMod 4)) = 1 + 2 * ((z - 1).val : ZMod 4) := by decide +kernel
    have hn : leechSquareSum (-u) = 32 := by
      simpa only [leechSquareSum, Pi.neg_apply, neg_sq] using h
    have hrn (i : Fin 24) : ((-u) i : ZMod 4) =
        1 + 2 * ((golayEncoder a0 i).val : ZMod 4) := by
      simp only [Pi.neg_apply, Int.cast_neg, hr i, heq, Pi.sub_apply, hflip]
    obtain ⟨j, hj⟩ := odd_short_source_formula (-u) (golayEncoder a0) hn hrn
    refine ⟨d, j, Or.inr ?_⟩
    have hneg : -u = griessShortIntegral (Sum.inr (Sum.inr (d, j))) := by
      funext i
      rw [hj i]
      simp only [griessShortIntegral, he i]
    exact neg_eq_iff_eq_neg.mp hneg

theorem golayOctadCoordinate_surjective (d : Fin 759) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true) :
    ∃ k : Fin 8, golayOctadCoordinate d k = i := by
  let S := golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)
  let e := S.orderIsoOfFin (golayOctad_support_card d)
  let x : S := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  exact ⟨e.symm x, congrArg Subtype.val (e.apply_symm_apply x)⟩

theorem leechEvenCode_short_equality (u : Fin 24 → ℤ) (c : Fin 24 → ZMod 2)
    (h : leechSquareSum u = 32) (hw : (∑ i, (c i).val) = 8)
    (hr : ∀ i, (u i : ZMod 4) = 2 * ((c i).val : ZMod 4)) :
    ∀ i, u i ^ 2 = 4 * (c i).val := by
  have hlow (i : Fin 24) : 4 * ((c i).val : ℤ) ≤ u i ^ 2 := by
    have hd : 4 ∣ u i - 2 * ((c i).val : ℤ) := by
      simpa using leechResidue_dvd u 0 c (by simpa using hr) i
    have hv : (c i).val = 0 ∨ (c i).val = 1 := by have hh := ZMod.val_lt (c i); omega
    rcases hv with hv | hv
    · simp [hv, sq_nonneg]
    · rw [hv] at hd ⊢
      norm_num at hd ⊢
      obtain ⟨k, hk⟩ := hd
      have he : u i ≤ -2 ∨ 2 ≤ u i := by omega
      rcases he with he | he <;> nlinarith [sq_nonneg (u i + 2), sq_nonneg (u i - 2)]
  have hz : (∑ i, (u i ^ 2 - 4 * ((c i).val : ℤ))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    change leechSquareSum u - 4 * (∑ i, ((c i).val : ℤ)) = 0
    rw [h, ← Nat.cast_sum, hw]
    norm_num
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.mpr (hlow k))).mp hz
  exact sub_eq_zero.mp (hi i (Finset.mem_univ i))

theorem octad_short_sign_pattern (d : Fin 759) (u : Fin 24 → ℤ)
    (hu : ∀ i, if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      then u i = -2 ∨ u i = 2 else u i = 0)
    (height : 8 ∣ ∑ i, u i) :
    2 ∣ (∑ k : Fin 8, if u (golayOctadCoordinate d k) = -2 then (1 : ℕ) else 0) := by
  let N : Finset (Fin 24) := Finset.univ.filter (fun i => u i = -2)
  let B : Finset (Fin 8) := Finset.univ.filter (fun k => u (golayOctadCoordinate d k) = -2)
  have hN : N = B.image (golayOctadCoordinate d) := by
    ext i
    simp only [N, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      have hbit : (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true := by
        have hh := hu i
        cases hb : (golayEncodedMask (golayOctadLabel d).val).testBit i.val <;> simp_all
      obtain ⟨k, hk⟩ := golayOctadCoordinate_surjective d i hbit
      exact ⟨k, by rw [hk]; exact hi, hk⟩
    · rintro ⟨k, hk, rfl⟩
      exact hk
  have hpoint (i : Fin 24) : u i =
      2 * (if (golayEncodedMask (golayOctadLabel d).val).testBit i.val then 1 else 0) -
        4 * (if i ∈ N then 1 else 0) := by
    have hh := hu i
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hb : (golayEncodedMask (golayOctadLabel d).val).testBit i.val
    · simp only [hb, Bool.false_eq_true, ite_false] at hh ⊢
      rw [hh]
      norm_num
    · simp only [hb, ite_true] at hh ⊢
      rcases hh with hh | hh <;> rw [hh] <;> norm_num
  have hs : (∑ i, u i) = 16 - 4 * (B.card : ℤ) := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hw : (∑ i : Fin 24, if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
        then (1 : ℤ) else 0) = 8 := by
      exact_mod_cast (by simpa only [golayMaskSupport_card] using golayOctad_support_card d :
        golayMaskWeight (golayEncodedMask (golayOctadLabel d).val) = 8)
    have hn : (∑ i : Fin 24, if i ∈ N then (1 : ℤ) else 0) = N.card := by simp
    rw [hw, hn, hN, Finset.card_image_of_injective _ (golayOctadCoordinate_injective d)]
    ring
  rw [hs] at height
  obtain ⟨k, hk⟩ := height
  have hcard : 2 ∣ B.card := by omega
  simpa only [B, Finset.card_filter] using hcard

theorem octad_short_catalog (d : Fin 759) (u : Fin 24 → ℤ)
    (hu : ∀ i, if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      then u i = -2 ∨ u i = 2 else u i = 0)
    (height : 8 ∣ ∑ i, u i) : ∃ e : Fin 64,
      u = griessShortIntegral (Sum.inr (Sum.inl (d, e))) ∨
      u = -griessShortIntegral (Sum.inr (Sum.inl (d, e))) := by
  let v := if u (golayOctadCoordinate d 7) = 2 then u else -u
  have hlast : u (golayOctadCoordinate d 7) = -2 ∨ u (golayOctadCoordinate d 7) = 2 := by
    simpa only [golayOctadCoordinate_mem, ite_true] using hu (golayOctadCoordinate d 7)
  have hvlast : v (golayOctadCoordinate d 7) = 2 := by
    rcases hlast with hh | hh <;> simp [v, hh]
  have hv (i : Fin 24) : if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      then v i = -2 ∨ v i = 2 else v i = 0 := by
    have hh := hu i
    by_cases hflip : u (golayOctadCoordinate d 7) = 2
    · simpa only [v, hflip, ite_true] using hh
    · simp only [v, hflip, ite_false, Pi.neg_apply]
      cases hb : (golayEncodedMask (golayOctadLabel d).val).testBit i.val
      · simp only [hb, Bool.false_eq_true, ite_false] at hh ⊢
        simp only [hh, neg_zero]
      · simp only [hb, ite_true] at hh ⊢
        rcases hh with hh | hh <;> rw [hh] <;> norm_num
  have hheight : 8 ∣ ∑ i, v i := by
    by_cases hflip : u (golayOctadCoordinate d 7) = 2
    · simpa only [v, hflip, ite_true] using height
    · simpa only [v, hflip, ite_false, Pi.neg_apply, Finset.sum_neg_distrib] using
        dvd_neg.mpr height
  let b : Fin 8 → Bool := fun k => decide (v (golayOctadCoordinate d k) = -2)
  have hb7 : b 7 = false := by simp [b, hvlast]
  have hbeven : 2 ∣ ∑ k, if b k then (1 : ℕ) else 0 := by
    simpa only [b, decide_eq_true_eq] using octad_short_sign_pattern d v hv hheight
  obtain ⟨e, he⟩ := trialityEvenMask_complete b hb7 hbeven
  have hsign (i : Fin 24)
      (hi : (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true) :
      (griessOctadSignMask d e).testBit i.val = true ↔ v i = -2 := by
    rw [griessOctadSignMask_testBit]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa only [he k, b, decide_eq_true_eq] using hk
    · intro hvi
      obtain ⟨k, hk⟩ := golayOctadCoordinate_surjective d i hi
      refine ⟨k, ?_, hk⟩
      simp only [he k, b, decide_eq_true_eq, hk, hvi]
  have hrepr : v = griessShortIntegral (Sum.inr (Sum.inl (d, e))) := by
    funext i
    have hh := hv i
    cases hm : (golayEncodedMask (golayOctadLabel d).val).testBit i.val
    · simp only [hm, Bool.false_eq_true, ite_false] at hh
      simp only [griessShortIntegral, hm, Bool.false_eq_true, ite_false, hh]
    · simp only [hm, ite_true] at hh
      rcases hh with hh | hh
      · have hs := (hsign i hm).mpr hh
        simp only [griessShortIntegral, hm, hs, ite_true, hh]
      · have hs : (griessOctadSignMask d e).testBit i.val ≠ true := by
          intro hs
          have hx := (hsign i hm).mp hs
          omega
        simp only [griessShortIntegral, hm, hs, ite_true, Bool.false_eq_true, ite_false, hh]
  refine ⟨e, ?_⟩
  by_cases hflip : u (golayOctadCoordinate d 7) = 2
  · left
    simpa only [v, hflip, ite_true] using hrepr
  · right
    have hn : -u = griessShortIntegral (Sum.inr (Sum.inl (d, e))) := by
      simpa only [v, hflip, ite_false] using hrepr
    exact neg_eq_iff_eq_neg.mp hn

theorem leechShort_catalog (u : leechIntegral) (h : leechSquareSum u.val = 32) :
    ∃ r : GriessShortIndex, u.val = griessShortIntegral r ∨ u.val = -griessShortIntegral r := by
  obtain ⟨m, hm, c, hc, hr, hs⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  rcases hm with hm | hm
  · subst m
    have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_zero, zero_add] using hr
    have hb := leechEvenCode_square_lower u.val c hr0
    have hw := golayCode_weights c hc
    have hweight : (∑ i, (c i).val) = 0 ∨ (∑ i, (c i).val) = 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [h] at hb
      omega
    have height : 8 ∣ ∑ i, u.val i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      simpa only [Int.cast_zero, mul_zero] using hs
    rcases hweight with hweight | hweight
    · have hz : c = 0 := by
        funext i
        apply (ZMod.val_eq_zero _).mp
        have hci := Finset.single_le_sum (fun j _ => Nat.zero_le (c j).val) (Finset.mem_univ i)
        omega
      have hf (i : Fin 24) : 4 ∣ u.val i := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
        simpa only [hz, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero] using hr0 i
      obtain ⟨s, p, hp⟩ := four_short_pair u.val h hf
      exact ⟨Sum.inl (s, p), hp⟩
    · obtain ⟨a, ha⟩ := hc
      obtain ⟨dl, hdl⟩ := golayLabelCoefficients_bijective.2 a
      have he : golayEncoder (golayLabelCoefficients dl) = c := by rw [hdl]; exact ha
      have hw : golayMaskWeight (golayEncodedMask dl.val) = 8 := by
        rw [← he] at hweight
        simpa only [golayMaskWeight, golayLabelEncoder_match] using hweight
      have hd : dl ∈ golayOctads := Finset.mem_filter.mpr ⟨Finset.mem_univ dl, hw⟩
      let d := (golayOctads.orderIsoOfFin golayOctads_card).symm ⟨dl, hd⟩
      have hlabel : golayOctadLabel d = dl :=
        congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)
      have hcoord := leechEvenCode_short_equality u.val c h hweight hr0
      have hu (i : Fin 24) : if (golayEncodedMask (golayOctadLabel d).val).testBit i.val
          then u.val i = -2 ∨ u.val i = 2 else u.val i = 0 := by
        have hi := hcoord i
        rw [← he, golayLabelEncoder_match] at hi
        rw [hlabel]
        cases hm : (golayEncodedMask dl.val).testBit i.val
        · simp only [hm, Bool.false_eq_true, ite_false, Nat.cast_zero, mul_zero] at hi ⊢
          nlinarith [sq_nonneg (u.val i)]
        · simp only [hm, ite_true, Nat.cast_one, mul_one] at hi ⊢
          have hb : -2 ≤ u.val i ∧ u.val i ≤ 2 := by
            constructor <;> nlinarith [sq_nonneg (u.val i + 3), sq_nonneg (u.val i - 3)]
          obtain ⟨hbl, hbu⟩ := hb
          interval_cases hci : u.val i <;> simp_all
      obtain ⟨e, he⟩ := octad_short_catalog d u.val hu height
      exact ⟨Sum.inr (Sum.inl (d, e)), he⟩
  · subst m
    obtain ⟨d, j, he⟩ := odd_short_catalog u.val h c hc (by
      simpa only [Int.cast_one] using hr)
    exact ⟨Sum.inr (Sum.inr (d, j)), he⟩

/-! ### Unique labels and the actual Co₀ permutation action

Distinct preferred short vectors represent distinct classes modulo 2Λ.
Their complete catalog therefore gives a bijection, and the lattice action
induces a permutation of the dictionary's 98280 short-vector labels.
-/

theorem griessPair_coordinate_nonzero (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    griessShortIntegral (Sum.inl (s, p)) i ≠ 0 ↔
      i = (griessCoordinatePair p).1 ∨ i = (griessCoordinatePair p).2 := by
  have hne := griessCoordinatePair_ne p
  simp only [griessShortIntegral]
  split_ifs <;> simp_all

theorem griessPair_first (s : Fin 2) (p : Fin 276) :
    griessShortIntegral (Sum.inl (s, p)) (griessCoordinatePair p).1 = 4 := by
  have hne := griessCoordinatePair_ne p
  simp only [griessShortIntegral, ite_true, hne, ite_false, mul_zero, add_zero, mul_one]

theorem griessPair_second (s : Fin 2) (p : Fin 276) :
    griessShortIntegral (Sum.inl (s, p)) (griessCoordinatePair p).2 =
      if s = 0 then -4 else 4 := by
  have hne := (griessCoordinatePair_ne p).symm
  simp only [griessShortIntegral, hne, ite_false, ite_true, mul_zero, mul_one, zero_add]

theorem griessPair_label_unique (s t : Fin 2) (p q : Fin 276)
    (h : griessShortIntegral (Sum.inl (s, p)) = griessShortIntegral (Sum.inl (t, q)) ∨
      griessShortIntegral (Sum.inl (s, p)) = -griessShortIntegral (Sum.inl (t, q))) :
    s = t ∧ p = q := by
  have hpq : ({(griessCoordinatePair p).1, (griessCoordinatePair p).2} : Set (Fin 24)) =
      {(griessCoordinatePair q).1, (griessCoordinatePair q).2} := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← griessPair_coordinate_nonzero s p i, ← griessPair_coordinate_nonzero t q i]
    rcases h with h | h
    · rw [h]
    · rw [h]
      simp
  have hp : p = q := by
    have hlp := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
    have hlq := (Finset.mem_filter.mp (griessCoordinatePairEquiv q).property).2
    change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hlp
    change (griessCoordinatePair q).1 < (griessCoordinatePair q).2 at hlq
    rcases Set.pair_eq_pair_iff.mp hpq with he | he
    · apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      exact Prod.ext he.1 he.2
    · rw [he.1, he.2] at hlp
      exact False.elim (not_lt_of_ge (le_of_lt hlq) hlp)
  subst q
  refine ⟨?_, rfl⟩
  rcases h with h | h
  · have hi := congrFun h (griessCoordinatePair p).2
    rw [griessPair_second, griessPair_second] at hi
    fin_cases s <;> fin_cases t <;> simp_all
  · have hi := congrFun h (griessCoordinatePair p).1
    simp only [Pi.neg_apply, griessPair_first] at hi
    omega

theorem golayLabel_mask_injective (d e : Fin 4096)
    (h : ∀ i : Fin 24, (golayEncodedMask d.val).testBit i.val =
      (golayEncodedMask e.val).testBit i.val) : d = e := by
  apply golayLabelCoefficients_bijective.1
  apply golayEncoder_injective
  ext i
  apply ZMod.val_injective 2
  rw [golayLabelEncoder_match, golayLabelEncoder_match, h i]

theorem golayOctadLabel_injective : Function.Injective golayOctadLabel := by
  intro d e h
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  exact Subtype.ext h

theorem griessOctad_coordinate_nonzero (d : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) i ≠ 0 ↔
      (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true := by
  simp only [griessShortIntegral]
  cases hb : (golayEncodedMask (golayOctadLabel d).val).testBit i.val <;>
    cases hs : (griessOctadSignMask d e).testBit i.val <;> norm_num

theorem griessOctadSignMask_local (d : Fin 759) (e : Fin 64) (k : Fin 8) :
    (griessOctadSignMask d e).testBit (golayOctadCoordinate d k).val =
      (trialityEvenMask e).testBit k.val := by
  have hiff := griessOctadSignMask_testBit d e (golayOctadCoordinate d k)
  have he : (∃ l : Fin 8, (trialityEvenMask e).testBit l.val = true ∧
      golayOctadCoordinate d l = golayOctadCoordinate d k) ↔
      (trialityEvenMask e).testBit k.val = true := by
    constructor
    · rintro ⟨l, hl, hlk⟩
      have hkl := golayOctadCoordinate_injective d hlk
      simpa only [hkl] using hl
    · intro hk
      exact ⟨k, hk, rfl⟩
  rw [he] at hiff
  cases hs : (griessOctadSignMask d e).testBit (golayOctadCoordinate d k).val <;>
    cases ht : (trialityEvenMask e).testBit k.val <;> simp_all

theorem griessOctad_last (d : Fin 759) (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) (golayOctadCoordinate d 7) = 2 := by
  simp only [griessShortIntegral, golayOctadCoordinate_mem, ite_true,
    griessOctadSignMask_local]
  change (if (trialityEvenMask e).testBit 7 then (-2 : ℤ) else 2) = 2
  rw [trialityEvenMask_last]
  rfl

theorem griessOctad_label_unique (d f : Fin 759) (e g : Fin 64)
    (h : griessShortIntegral (Sum.inr (Sum.inl (d, e))) =
        griessShortIntegral (Sum.inr (Sum.inl (f, g))) ∨
      griessShortIntegral (Sum.inr (Sum.inl (d, e))) =
        -griessShortIntegral (Sum.inr (Sum.inl (f, g)))) : d = f ∧ e = g := by
  have hd : d = f := by
    apply golayOctadLabel_injective
    apply golayLabel_mask_injective
    intro i
    have hn : (golayEncodedMask (golayOctadLabel d).val).testBit i.val = true ↔
        (golayEncodedMask (golayOctadLabel f).val).testBit i.val = true := by
      rw [← griessOctad_coordinate_nonzero d e i, ← griessOctad_coordinate_nonzero f g i]
      rcases h with h | h
      · rw [h]
      · rw [h]; simp
    cases hb : (golayEncodedMask (golayOctadLabel d).val).testBit i.val <;>
      cases hc : (golayEncodedMask (golayOctadLabel f).val).testBit i.val <;> simp_all
  subst f
  refine ⟨rfl, ?_⟩
  rcases h with h | h
  · apply trialityEvenMask_injective
    funext k
    have hi := congrFun h (golayOctadCoordinate d k)
    simp only [griessShortIntegral, golayOctadCoordinate_mem, ite_true,
      griessOctadSignMask_local] at hi
    cases hb : (trialityEvenMask e).testBit k.val <;>
      cases hc : (trialityEvenMask g).testBit k.val <;> simp_all
  · have hi := congrFun h (golayOctadCoordinate d 7)
    simp only [Pi.neg_apply, griessOctad_last] at hi
    omega

theorem griessOdd_coordinate_square (d : Fin 2048) (j i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (d, j))) i ^ 2 = if i = j then 9 else 1 := by
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

theorem golayLabelEncoder_boolean (d : Fin 4096) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients d) i =
      golayBooleanCast ((golayEncodedMask d.val).testBit i.val) := by
  apply ZMod.val_injective 2
  rw [golayLabelEncoder_match]
  cases hb : (golayEncodedMask d.val).testBit i.val <;> rfl

theorem griessOdd_label_unique (d e : Fin 2048) (j k : Fin 24)
    (h : griessShortIntegral (Sum.inr (Sum.inr (d, j))) =
        griessShortIntegral (Sum.inr (Sum.inr (e, k))) ∨
      griessShortIntegral (Sum.inr (Sum.inr (d, j))) =
        -griessShortIntegral (Sum.inr (Sum.inr (e, k)))) : d = e ∧ j = k := by
  have hj : j = k := by
    have hs : griessShortIntegral (Sum.inr (Sum.inr (d, j))) j ^ 2 =
        griessShortIntegral (Sum.inr (Sum.inr (e, k))) j ^ 2 := by
      rcases h with h | h
      · rw [h]
      · rw [h]; simp only [Pi.neg_apply, neg_sq]
    rw [griessOdd_coordinate_square, griessOdd_coordinate_square, ite_eq_left rfl] at hs
    by_contra hj
    rw [ite_eq_right hj] at hs
    omega
  subst k
  refine ⟨?_, rfl⟩
  let dl : Fin 4096 := ⟨d.val, by omega⟩
  let el : Fin 4096 := ⟨e.val, by omega⟩
  rcases h with h | h
  · have heq : dl = el := by
      apply golayLabel_mask_injective
      intro i
      have hi := congrFun h i
      change _ = _ at hi
      simp only [griessShortIntegral] at hi
      by_cases hij : i = j <;>
        cases hd : (golayEncodedMask d.val).testBit i.val <;>
        cases he : (golayEncodedMask e.val).testBit i.val <;> simp_all
    have hv : d.val = e.val := congrArg (fun x : Fin 4096 => x.val) heq
    exact Fin.ext hv
  · have hdiff (i : Fin 24) : (golayEncodedMask d.val).testBit i.val ≠
        (golayEncodedMask e.val).testBit i.val := by
      have hi := congrFun h i
      simp only [griessShortIntegral, Pi.neg_apply] at hi
      by_cases hij : i = j <;>
        cases hd : (golayEncodedMask d.val).testBit i.val <;>
        cases he : (golayEncodedMask e.val).testBit i.val <;> simp_all
    have hones : golayEncoder (golayLabelCoefficients dl + golayLabelCoefficients el) =
        golayEncoder (Pi.single 11 1) := by
      rw [map_add, golay_all_one]
      ext i
      rw [Pi.add_apply, golayLabelEncoder_boolean, golayLabelEncoder_boolean]
      have hh : ∀ a b : Bool, a ≠ b → golayBooleanCast a + golayBooleanCast b = 1 := by
        decide +kernel
      exact hh _ _ (hdiff i)
    have hcoeff := golayEncoder_injective hones
    have hc11 := congrFun hcoeff 11
    have hd11 : golayLabelCoefficients dl 11 = 0 := (golayLabel_last_zero dl).mpr d.isLt
    have he11 : golayLabelCoefficients el 11 = 0 := (golayLabel_last_zero el).mpr e.isLt
    simp only [Pi.add_apply, hd11, he11, zero_add, Pi.single_eq_same] at hc11
    exact False.elim (zero_ne_one hc11)

theorem griessOctad_coordinate_square_le (d : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) i ^ 2 ≤ 4 := by
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

theorem griessOdd_coordinate_square_le (d : Fin 2048) (j i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (d, j))) i ^ 2 ≤ 9 := by
  rw [griessOdd_coordinate_square]
  split_ifs <;> norm_num

theorem griessOctad_coordinate_square_local (d : Fin 759) (e : Fin 64) (k : Fin 8) :
    griessShortIntegral (Sum.inr (Sum.inl (d, e))) (golayOctadCoordinate d k) ^ 2 = 4 := by
  simp only [griessShortIntegral, golayOctadCoordinate_mem, ite_true]
  split_ifs <;> norm_num

theorem griessShort_label_unique (r s : GriessShortIndex)
    (h : griessShortIntegral r = griessShortIntegral s ∨
      griessShortIntegral r = -griessShortIntegral s) : r = s := by
  have hsquare (i : Fin 24) : griessShortIntegral r i ^ 2 = griessShortIntegral s i ^ 2 := by
    rcases h with h | h
    · rw [h]
    · rw [h]; simp only [Pi.neg_apply, neg_sq]
  rcases r with ⟨a, p⟩ | (⟨d, e⟩ | ⟨f, i⟩) <;>
    rcases s with ⟨b, q⟩ | (⟨g, k⟩ | ⟨l, j⟩)
  · obtain ⟨ha, hp⟩ := griessPair_label_unique a b p q h
    rw [ha, hp]
  · have hh := hsquare (griessCoordinatePair p).1
    rw [griessPair_first] at hh
    have hl := griessOctad_coordinate_square_le g k (griessCoordinatePair p).1
    nlinarith
  · have hh := hsquare (griessCoordinatePair p).1
    rw [griessPair_first] at hh
    have hl := griessOdd_coordinate_square_le l j (griessCoordinatePair p).1
    nlinarith
  · have hh := hsquare (griessCoordinatePair q).1
    rw [griessPair_first] at hh
    have hl := griessOctad_coordinate_square_le d e (griessCoordinatePair q).1
    nlinarith
  · obtain ⟨hd, he⟩ := griessOctad_label_unique d g e k h
    rw [hd, he]
  · have hh := hsquare (golayOctadCoordinate d 0)
    rw [griessOctad_coordinate_square_local, griessOdd_coordinate_square] at hh
    split_ifs at hh <;> norm_num at hh
  · have hh := hsquare (griessCoordinatePair q).1
    rw [griessPair_first] at hh
    have hl := griessOdd_coordinate_square_le f i (griessCoordinatePair q).1
    nlinarith
  · have hh := hsquare (golayOctadCoordinate g 0)
    rw [griessOctad_coordinate_square_local, griessOdd_coordinate_square] at hh
    split_ifs at hh <;> norm_num at hh
  · obtain ⟨hd, hi⟩ := griessOdd_label_unique f l i j h
    rw [hd, hi]

noncomputable def griessShortLatticeVector (r : GriessShortIndex) : leechIntegral :=
  ⟨griessShortIntegral r, griessShortIntegral_mem r⟩

noncomputable def griessShortClass (r : GriessShortIndex) : LeechModTwo :=
  leechReduction (griessShortLatticeVector r)

theorem griessShortClass_injective : Function.Injective griessShortClass := by
  intro r s h
  have he := leechShort_same_class (griessShortLatticeVector r) (griessShortLatticeVector s)
    (griessShortIntegral_squareSum r) (griessShortIntegral_squareSum s) h
  apply griessShort_label_unique
  rcases he with he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (congrArg Subtype.val he)

theorem leechReduction_neg (u : leechIntegral) : leechReduction (-u) = leechReduction u := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨-u, ?_⟩
  change (2 : ℕ) • (-u) = -u - u
  simp only [two_nsmul, sub_eq_add_neg]

/-- Lattice quotient classes that admit a vector of squared norm four. -/
def IsLeechShortClass (v : LeechModTwo) : Prop :=
  ∃ u : leechIntegral, leechReduction u = v ∧ leechSquareSum u.val = 32

abbrev LeechShortClasses := {v : LeechModTwo // IsLeechShortClass v}

noncomputable def griessShortClassMap (r : GriessShortIndex) : LeechShortClasses :=
  ⟨griessShortClass r, griessShortLatticeVector r, rfl, griessShortIntegral_squareSum r⟩

theorem griessShortClassMap_bijective : Function.Bijective griessShortClassMap := by
  constructor
  · intro r s h
    exact griessShortClass_injective (congrArg Subtype.val h)
  · rintro ⟨v, u, hu, hs⟩
    obtain ⟨r, hr⟩ := leechShort_catalog u hs
    refine ⟨r, Subtype.ext ?_⟩
    change griessShortClass r = v
    rw [← hu]
    rcases hr with hr | hr
    · have he : u = griessShortLatticeVector r := Subtype.ext hr
      rw [he]
      rfl
    · have he : u = -griessShortLatticeVector r := Subtype.ext hr
      rw [he, leechReduction_neg]
      rfl

/-- The explicit dictionary catalog enumerates the actual short lattice classes. -/
noncomputable def griessShortClassEquiv : GriessShortIndex ≃ LeechShortClasses :=
  Equiv.ofBijective griessShortClassMap griessShortClassMap_bijective

theorem leechShortClass_preserved (e : leechIsomSubgroup) (v : LeechModTwo)
    (hv : IsLeechShortClass v) : IsLeechShortClass (leechModTwoAction e v) := by
  obtain ⟨u, hu, hs⟩ := hv
  refine ⟨leechIntegralAction e u, ?_, ?_⟩
  · rw [← hu]
    rfl
  · rw [leechIntegralAction_squareSum, hs]

noncomputable def leechShortClassAction (e : leechIsomSubgroup) :
    Equiv.Perm LeechShortClasses :=
  (leechModTwoAction e).toEquiv.subtypeEquiv (by
    intro v
    constructor
    · exact leechShortClass_preserved e v
    · intro hv
      have h := leechShortClass_preserved e⁻¹ (leechModTwoAction e v) hv
      simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h)

noncomputable def griessShortPermutation : leechIsomSubgroup →* Equiv.Perm GriessShortIndex where
  toFun e := griessShortClassEquiv.trans
    ((leechShortClassAction e).trans griessShortClassEquiv.symm)
  map_one' := by
    apply Equiv.ext
    intro r
    apply griessShortClassEquiv.injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    change leechModTwoAction 1 (griessShortClass r) = griessShortClass r
    rw [map_one]
    rfl
  map_mul' e f := by
    apply Equiv.ext
    intro r
    apply griessShortClassEquiv.injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.Perm.mul_apply]
    apply Subtype.ext
    change leechModTwoAction (e * f) (griessShortClass r) =
      leechModTwoAction e (leechModTwoAction f (griessShortClass r))
    rw [map_mul]
    rfl

theorem griessShortPermutation_class (e : leechIsomSubgroup) (r : GriessShortIndex) :
    griessShortClass (griessShortPermutation e r) = leechModTwoAction e (griessShortClass r) := by
  have h := griessShortClassEquiv.apply_symm_apply
    (leechShortClassAction e (griessShortClassEquiv r))
  exact congrArg Subtype.val h

/-! ## Concrete Conway Griess multiplication

Conway's symmetric-matrix, signed-short-vector, and spin-tensor rules are
converted to the fixed dictionary basis. Finite structure constants extend
them bilinearly; no algebra, action, or recognition theorem is supplied as data.
-/


/-- The preferred short lift in the source hyperbolic coordinates of Λ/2Λ.
The modified code/cocode frame fixes the binary coordinates; the preferred
signed-short section has central coefficient zero. Using the actual lattice
class makes the normalizer/Co₀ compatibility intrinsic. -/
noncomputable def griessShortQ (r : GriessShortIndex) : Q where
  base := ofAdd (leechHyperbolicCoordinates (griessShortClass r))
  coeff := 1

/-! ### Signed short-vector representation

The spin normalizer fixes the central signs. Its conjugation of each preferred
short lift therefore has a unique central phase and the actual Co₀-permuted
short base. Those phases compose by the group law, giving a signed permutation
representation with proved inverses.
-/

def qCentral (c : ZMod 2) : Q := ⟨1, ofAdd c⟩

theorem spinRepresentation_central (c : ZMod 2) (f : SpinSpace) :
    spinRepresentation (qCentral c) f = qSign c • f := by
  funext t
  change qSign (c + spinDot 0 t) * f (t + 0) = qSign c * f t
  simp only [spinDot_zero_left, add_zero]

theorem spinConjugation_representation (s : SpinHolomorph) (q : Q) :
    spinRepresentation (spinConjugation s q) = s.val * spinRepresentation q * s.val⁻¹ := by
  change spinRepresentation (spinImageEquiv.symm _) = _
  have h (e : spinImage) : spinRepresentation (spinImageEquiv.symm e) = e.val :=
    MonoidHom.apply_ofInjective_symm spinRepresentation_injective e
  rw [h]
  rfl

theorem spinConjugation_central (s : SpinHolomorph) (c : ZMod 2) :
    spinConjugation s (qCentral c) = qCentral c := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  apply LinearEquiv.ext
  intro f
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, spinRepresentation_central,
    map_smul, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, spinRepresentation_central]

theorem qCentral_mul_coeff (c : ZMod 2) (q : Q) :
    toAdd (qCentral c * q).coeff = c + toAdd q.coeff := by
  change c + toAdd q.coeff + qBeta 0 (toAdd q.base) = _
  rw [qBeta_zero_left, add_zero]

theorem qCentral_mul_base (c : ZMod 2) (q : Q) : (qCentral c * q).base = q.base := by
  change 1 * q.base = q.base
  rw [one_mul]

theorem leechBinaryAction_coordinates (e : leechIsomSubgroup) (v : LeechModTwo) :
    leechBinaryAction e (leechHyperbolicCoordinates v) =
      leechHyperbolicCoordinates (leechModTwoAction e v) := by
  change leechHyperbolicCoordinates
    (leechModTwoAction e (leechHyperbolicCoordinates.symm (leechHyperbolicCoordinates v))) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem griessShortQ_coeff (r : GriessShortIndex) : toAdd (griessShortQ r).coeff = 0 := rfl

theorem griessShortQ_image_base (f : localFiberSubgroup) (r : GriessShortIndex) :
    (spinConjugation f.val.1 (griessShortQ r)).base =
      (griessShortQ (griessShortPermutation f.val.2 r)).base := by
  apply Multiplicative.toAdd.injective
  have h := qBinaryAction_apply (spinConjugation f.val.1) (griessShortQ r)
  change spinBinaryAction f.val.1 (leechHyperbolicCoordinates (griessShortClass r)) = _ at h
  rw [f.property] at h
  rw [leechBinaryAction_coordinates] at h
  rw [← griessShortPermutation_class] at h
  exact h.symm

noncomputable def localShortPhase (f : localFiberSubgroup) (r : GriessShortIndex) : ZMod 2 :=
  toAdd (spinConjugation f.val.1 (griessShortQ r)).coeff

theorem griessShortQ_image (f : localFiberSubgroup) (r : GriessShortIndex) :
    spinConjugation f.val.1 (griessShortQ r) =
      qCentral (localShortPhase f r) * griessShortQ (griessShortPermutation f.val.2 r) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    exact griessShortQ_image_base f r
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff]
    change localShortPhase f r = localShortPhase f r + 0
    rw [add_zero]

@[simp] theorem localShortPhase_one (r : GriessShortIndex) : localShortPhase 1 r = 0 := by
  change toAdd (spinConjugation 1 (griessShortQ r)).coeff = 0
  rw [map_one]
  rfl

theorem localShortPhase_mul (f g : localFiberSubgroup) (r : GriessShortIndex) :
    localShortPhase (f * g) r = localShortPhase g r +
      localShortPhase f (griessShortPermutation g.val.2 r) := by
  have he : spinConjugation (f * g).val.1 (griessShortQ r) =
      qCentral (localShortPhase g r) *
        (qCentral (localShortPhase f (griessShortPermutation g.val.2 r)) *
          griessShortQ (griessShortPermutation (f * g).val.2 r)) := by
    change (spinConjugation (f.val.1 * g.val.1)) (griessShortQ r) = _
    rw [map_mul, MulAut.mul_apply, griessShortQ_image g r, map_mul,
      spinConjugation_central, griessShortQ_image f]
    rw [show (f * g).val.2 = f.val.2 * g.val.2 from rfl, map_mul, Equiv.Perm.mul_apply]
  have hc := congrArg (fun q : Q => toAdd q.coeff) he
  simpa only [localShortPhase, qCentral_mul_coeff, griessShortQ_coeff, add_zero] using hc

noncomputable def localShortOperator (f : localFiberSubgroup) :
    (GriessShortIndex → ℝ) →ₗ[ℝ] (GriessShortIndex → ℝ) where
  toFun x r := qSign (localShortPhase f ((griessShortPermutation f.val.2).symm r)) *
    x ((griessShortPermutation f.val.2).symm r)
  map_add' x y := by funext r; simp only [Pi.add_apply, mul_add]
  map_smul' c x := by funext r; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem localShortOperator_image (f : localFiberSubgroup) (x : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    localShortOperator f x (griessShortPermutation f.val.2 r) =
      qSign (localShortPhase f r) * x r := by
  change qSign (localShortPhase f ((griessShortPermutation f.val.2).symm
    (griessShortPermutation f.val.2 r))) *
      x ((griessShortPermutation f.val.2).symm (griessShortPermutation f.val.2 r)) = _
  rw [Equiv.symm_apply_apply]

theorem localShortOperator_one : localShortOperator 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext r
  have h := localShortOperator_image 1 x r
  change localShortOperator 1 x (griessShortPermutation 1 r) =
    qSign (localShortPhase 1 r) * x r at h
  rw [map_one, Equiv.Perm.one_apply, localShortPhase_one, qSign_zero, one_mul] at h
  exact h

theorem localShortOperator_mul (f g : localFiberSubgroup) :
    localShortOperator (f * g) = (localShortOperator f).comp (localShortOperator g) := by
  apply LinearMap.ext
  intro x
  funext r
  obtain ⟨t, rfl⟩ := (griessShortPermutation (f * g).val.2).surjective r
  rw [localShortOperator_image, localShortPhase_mul, qSign_add]
  change _ = localShortOperator f (localShortOperator g x)
    (griessShortPermutation (f.val.2 * g.val.2) t)
  rw [map_mul, Equiv.Perm.mul_apply, localShortOperator_image, localShortOperator_image]
  ring

noncomputable def localShortEquiv (f : localFiberSubgroup) :
    (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ) :=
  LinearEquiv.ofLinearMap (localShortOperator f) (localShortOperator f⁻¹)
    (by rw [← localShortOperator_mul, mul_inv_cancel, localShortOperator_one])
    (by rw [← localShortOperator_mul, inv_mul_cancel, localShortOperator_one])

noncomputable def localShortRepresentation : localFiberSubgroup →*
    ((GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ)) where
  toFun := localShortEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun localShortOperator_one x
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun (localShortOperator_mul f g) x

abbrev ConwayRawSpace := Matrix (Fin 24) (Fin 24) ℝ ×
  ((GriessShortIndex → ℝ) × (SpinIndex → Fin 24 → ℝ))

noncomputable def conwayShortPairing (a : Matrix (Fin 24) (Fin 24) ℝ)
    (r : GriessShortIndex) : ℝ :=
  ∑ i, ∑ j, a i j * griessShortVector r i * griessShortVector r j

noncomputable def conwayTensorCoefficient (r : GriessShortIndex) (i j : Fin 24) : ℝ :=
  (if i = j then 1 else 0) - 2 * griessShortVector r i * griessShortVector r j

/-- Conway §12's six multiplication rules, extended bilinearly to the three
blocks: symmetric matrices, signed short vectors, and spin tensors. -/
noncomputable def conwayRawProduct (x y : ConwayRawSpace) : ConwayRawSpace :=
  (fun i j =>
      2 * ∑ k, (x.1 i k * y.1 k j + y.1 i k * x.1 k j) +
      (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = 1 then
        qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x.2.1 r * y.2.1 s *
          griessShortVector r i * griessShortVector r j else 0) +
      (∑ t, ((∑ k, x.2.2 t k * y.2.2 t k) * (if i = j then 1 else 0) +
        4 * x.2.2 t i * y.2.2 t j + 4 * y.2.2 t i * x.2.2 t j)),
    ((fun u =>
      conwayShortPairing x.1 u * y.2.1 u + conwayShortPairing y.1 u * x.2.1 u +
      (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
        qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x.2.1 r * y.2.1 s else 0) +
      (∑ t, ∑ i, ∑ j,
        spinOperator (griessShortQ u) (fun v => x.2.2 v i) t * y.2.2 t j *
          conwayTensorCoefficient u i j) / 2),
    (fun t i =>
      (∑ j, (x.1 j i * y.2.2 t j + y.1 j i * x.2.2 t j)) +
      Matrix.trace x.1 / 8 * y.2.2 t i + Matrix.trace y.1 / 8 * x.2.2 t i +
      (∑ r, ∑ j, (x.2.1 r * spinOperator (griessShortQ r) (fun v => y.2.2 v j) t +
        y.2.1 r * spinOperator (griessShortQ r) (fun v => x.2.2 v j) t) *
          conwayTensorCoefficient r j i) / 8)))

noncomputable def griessPairIndex (i j : Fin 24) (h : i ≠ j) : Fin 276 :=
  griessCoordinatePairEquiv.symm ⟨if i < j then (i, j) else (j, i), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    split_ifs with hij
    · exact hij
    · exact lt_of_le_of_ne (le_of_not_gt hij) h.symm⟩

noncomputable def spinDictionaryLabel (t : SpinIndex) : Fin 4096 :=
  (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).symm t

noncomputable def spinDictionaryCode (t : SpinIndex) : Fin 2048 :=
  ⟨(spinDictionaryLabel t).val % 2048, Nat.mod_lt _ (by decide)⟩

/-- The physical triple corresponding to the source's dictionary coordinates.
The partial Fourier transform in coefficient eleven converts the Schrödinger
basis to d⁺ and d⁻. The Y and Z signs are exactly those in Seysen Table 5. -/
noncomputable def griessConwayEncode (x : GriessSpace) : ConwayRawSpace :=
  let b := trialityBlocksEquiv x
  (fun i j => if h : i = j then b.1 i else b.2.1 0 (griessPairIndex i j h),
    ((fun r => match r with
      | Sum.inl (s, p) => if s = 0 then b.2.1 1 p + b.2.1 2 p
        else b.2.1 2 p - b.2.1 1 p
      | Sum.inr (Sum.inl (d, e)) => b.2.2.1 d e
      | Sum.inr (Sum.inr (d, i)) => b.2.2.2 0 (finProdFinEquiv (d, i))),
    (fun t i =>
      let d := spinDictionaryCode t
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          b.2.2.2 2 (finProdFinEquiv (d, i)) +
        qSign (t 11) * (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
          b.2.2.2 1 (finProdFinEquiv (d, i))) / Real.sqrt 2)))

/-- Recover the dictionary coordinates from a symmetric-matrix/short/spin triple. -/
noncomputable def griessConwayDecode (x : ConwayRawSpace) : GriessSpace :=
  trialityBlocksEquiv.symm
    ((fun i => x.1 i i),
      ((fun s p => if s = 0 then
          x.1 (griessCoordinatePair p).1 (griessCoordinatePair p).2
        else if s = 1 then (x.2.1 (Sum.inl (0, p)) - x.2.1 (Sum.inl (1, p))) / 2
        else (x.2.1 (Sum.inl (0, p)) + x.2.1 (Sum.inl (1, p))) / 2),
      ((fun d e => x.2.1 (Sum.inr (Sum.inl (d, e)))),
      (fun s k =>
        let d := (finProdFinEquiv.symm k : Fin 2048 × Fin 24).1
        let i := (finProdFinEquiv.symm k : Fin 2048 × Fin 24).2
        if s = 0 then x.2.1 (Sum.inr (Sum.inr (d, i)))
        else if s = 1 then
          (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
            (x.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
              x.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2
        else qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (x.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
            x.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2))))

/-! ## The local action and its coordinate transport

The explicit Conway dictionary conversion is a linear equivalence onto the
symmetric-matrix/short/spin subspace. Each block has its actual local action,
with group laws and inverses proved. The diagonal signs act trivially, giving
the quotient homomorphism rhoLocal without an action or endpoint assumption.
-/

theorem griessPairIndex_pair (p : Fin 276) :
    griessPairIndex (griessCoordinatePair p).1 (griessCoordinatePair p).2
      (griessCoordinatePair_ne p) = p := by
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change (griessCoordinatePairEquiv (griessCoordinatePairEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  change (if (griessCoordinatePair p).1 < (griessCoordinatePair p).2 then
    ((griessCoordinatePair p).1, (griessCoordinatePair p).2) else
    ((griessCoordinatePair p).2, (griessCoordinatePair p).1)) = _
  rw [ite_eq_left hl]
  rfl

theorem griessPairIndex_swap (i j : Fin 24) (h : i ≠ j) :
    griessPairIndex i j h = griessPairIndex j i h.symm := by
  unfold griessPairIndex
  congr 1
  apply Subtype.ext
  change (if i < j then (i, j) else (j, i)) = (if j < i then (j, i) else (i, j))
  rcases lt_or_gt_of_ne h with hl | hl
  · simp only [hl, not_lt_of_ge (le_of_lt hl), ite_true, ite_false]
  · simp only [hl, not_lt_of_ge (le_of_lt hl), ite_true, ite_false]

@[simp] theorem spinDictionaryLabel_coeff (d : Fin 4096) :
    spinDictionaryLabel (golayLabelCoefficients d) = d :=
  (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).symm_apply_apply d

@[simp] theorem spinDictionaryCode_low (d : Fin 2048) :
    spinDictionaryCode (golayLabelCoefficients ⟨d.val, by omega⟩) = d := by
  apply Fin.ext
  change (spinDictionaryLabel (golayLabelCoefficients ⟨d.val, by omega⟩)).val % 2048 = d.val
  rw [spinDictionaryLabel_coeff, Nat.mod_eq_of_lt d.isLt]

@[simp] theorem spinDictionaryCode_high (d : Fin 2048) :
    spinDictionaryCode (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) = d := by
  apply Fin.ext
  change (spinDictionaryLabel (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)).val % 2048 = d.val
  rw [spinDictionaryLabel_coeff]
  change (d.val + 2048) % 2048 = d.val
  omega

@[simp] theorem golayLabel_low_last (d : Fin 2048) :
    golayLabelCoefficients ⟨d.val, by omega⟩ 11 = 0 :=
  (golayLabel_last_zero _).mpr d.isLt

@[simp] theorem golayLabel_high_last (d : Fin 2048) :
    golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11 = 1 := by
  have hz : golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11 ≠ 0 := by
    intro hn
    have hh := (golayLabel_last_zero _).mp hn
    change d.val + 2048 < 2048 at hh
    omega
  have hv := ZMod.val_lt (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11)
  apply ZMod.val_injective 2
  have hn : (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11).val ≠ 0 :=
    fun h => hz ((ZMod.val_eq_zero _).mp h)
  have hone : (1 : ZMod 2).val = 1 := by decide
  rw [hone]
  omega

theorem spinDictionaryIndex_cases (t : SpinIndex) :
    t = golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩ ∨
      t = golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩ := by
  let d := spinDictionaryLabel t
  have hd : golayLabelCoefficients d = t :=
    (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).apply_symm_apply t
  have hc : (spinDictionaryCode t).val = d.val % 2048 := rfl
  by_cases hlo : d.val < 2048
  · left
    have he : d = ⟨(spinDictionaryCode t).val, by omega⟩ := Fin.ext (by
      change d.val = (spinDictionaryCode t).val
      omega)
    rw [← he, hd]
  · right
    have he : d = ⟨(spinDictionaryCode t).val + 2048, by omega⟩ := Fin.ext (by
      change d.val = (spinDictionaryCode t).val + 2048
      omega)
    rw [← he, hd]

set_option backward.isDefEq.respectTransparency false in
noncomputable def griessConwayEncodeLinear : GriessSpace →ₗ[ℝ] ConwayRawSpace where
  toFun := griessConwayEncode
  map_add' x y := by
    simp only [griessConwayEncode, map_add]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    all_goals dsimp only
    · funext i j
      simp only [Matrix.add_apply, Pi.add_apply, Prod.fst_add, Prod.snd_add]
      split_ifs <;> rfl
    · funext r
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
      rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
      · dsimp only
        split_ifs <;> ring
      · rfl
      · rfl
    · funext t i
      simp only [Pi.add_apply, Prod.snd_add]
      ring
  map_smul' c x := by
    simp only [griessConwayEncode, map_smul, RingHom.id_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    all_goals dsimp only
    all_goals simp only [Prod.smul_fst, Prod.smul_snd]
    · funext i j
      simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> rfl
    · funext r
      simp only [Pi.smul_apply, smul_eq_mul]
      rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
      · dsimp only
        split_ifs <;> ring
      · rfl
      · rfl
    · funext t i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

set_option backward.isDefEq.respectTransparency false in
theorem griessConwayDecode_encode (x : GriessSpace) :
    griessConwayDecode (griessConwayEncode x) = x := by
  apply trialityBlocksEquiv.injective
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, griessConwayEncode]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals dsimp only
  · funext i
    simp only [dite_true]
  · funext s p
    have hn := griessCoordinatePair_ne p
    fin_cases s <;> norm_num [hn, griessPairIndex_pair] <;> ring
  · funext s k
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hq (c : ZMod 2) : qSign c ^ 2 = 1 := by simpa only [pow_two] using qSign_sq c
    have hsi : (Real.sqrt 2)⁻¹ ^ 2 = (1 : ℝ) / 2 := by
      rw [inv_pow, hs2]
      norm_num
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
    · simp only [ite_true, finProdFinEquiv.apply_symm_apply]
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true,
        spinDictionaryCode_low, spinDictionaryCode_high, golayLabel_low_last,
        golayLabel_high_last, qSign_zero, qSign_one, one_mul, neg_one_mul,
        finProdFinEquiv.apply_symm_apply]
      cases hb : (golayEncodedMask (finProdFinEquiv.symm k : Fin 2048 × Fin 24).1.val).testBit
        (finProdFinEquiv.symm k : Fin 2048 × Fin 24).2.val <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul]
      all_goals ring_nf
      all_goals rw [hsi]
      all_goals ring
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        ite_false, spinDictionaryCode_low, spinDictionaryCode_high, golayLabel_low_last,
        golayLabel_high_last, qSign_zero, qSign_one, one_mul, neg_one_mul,
        finProdFinEquiv.apply_symm_apply]
      ring_nf
      rw [hq, hsi]
      ring

theorem griessPairIndex_coordinates (i j : Fin 24) (h : i ≠ j) :
    griessCoordinatePair (griessPairIndex i j h) = if i < j then (i, j) else (j, i) := by
  exact congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem griessConwayEncode_symmetric (x : GriessSpace) :
    ∀ i j, (griessConwayEncode x).1 i j = (griessConwayEncode x).1 j i := by
  intro i j
  change (if h : i = j then (trialityBlocksEquiv x).1 i
    else (trialityBlocksEquiv x).2.1 0 (griessPairIndex i j h)) =
      (if h : j = i then (trialityBlocksEquiv x).1 j
        else (trialityBlocksEquiv x).2.1 0 (griessPairIndex j i h))
  by_cases h : i = j
  · subst j
    rfl
  · rw [dite_eq_right h, dite_eq_right (Ne.symm h), griessPairIndex_swap]

set_option backward.isDefEq.respectTransparency false in
theorem griessConwayEncode_decode (x : ConwayRawSpace)
    (hx : ∀ i j, x.1 i j = x.1 j i) : griessConwayEncode (griessConwayDecode x) = x := by
  simp only [griessConwayEncode, griessConwayDecode, LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · funext i j
    by_cases h : i = j
    · subst j
      simp only [dite_true]
    · simp only [h, dite_false, ite_true, griessPairIndex_coordinates]
      by_cases hl : i < j
      · simp only [hl, ite_true]
      · simp only [hl, ite_false]
        exact hx j i
  · funext r
    rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
    · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> norm_num <;> ring
    · rfl
    · simp only [finProdFinEquiv.symm_apply_apply, ite_true]
  · funext t i
    have ht := spinDictionaryIndex_cases t
    let d := spinDictionaryCode t
    change t = golayLabelCoefficients ⟨d.val, by omega⟩ ∨
      t = golayLabelCoefficients ⟨d.val + 2048, by omega⟩ at ht
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsi : (Real.sqrt 2)⁻¹ ^ 2 = (1 : ℝ) / 2 := by rw [inv_pow, hs2]; norm_num
    have hq (c : ZMod 2) : qSign c ^ 2 = 1 := by simpa only [pow_two] using qSign_sq c
    rcases ht with ht | ht
    · rw [ht]
      simp only [spinDictionaryCode_low, golayLabel_low_last, qSign_zero, one_mul,
        finProdFinEquiv.symm_apply_apply, ite_false,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        show (1 : Fin 3) ≠ 0 by decide, ite_true]
      cases hb : (golayEncodedMask d.val).testBit i.val <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul]
      all_goals
        set a : ℝ := x.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i
        set b : ℝ := x.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
        ring_nf
        rw [hq, hsi]
      all_goals ring
    · rw [ht]
      simp only [spinDictionaryCode_high, golayLabel_high_last, qSign_one, neg_one_mul,
        finProdFinEquiv.symm_apply_apply, ite_false,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        show (1 : Fin 3) ≠ 0 by decide, ite_true]
      cases hb : (golayEncodedMask d.val).testBit i.val <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul]
      all_goals
        set a : ℝ := x.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i
        set b : ℝ := x.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
        ring_nf
        rw [hq, hsi]
      all_goals ring

noncomputable def conwaySymmetricSpace : Submodule ℝ ConwayRawSpace where
  carrier := {x | ∀ i j, x.1 i j = x.1 j i}
  zero_mem' := by
    intro i j
    rfl
  add_mem' := by
    intro a b ha hb i j
    simp only [Prod.fst_add, Matrix.add_apply, ha i j, hb i j]
  smul_mem' := by
    intro c x hx i j
    simp only [Prod.smul_fst, Matrix.smul_apply, hx i j]

noncomputable def griessConwayLinear : GriessSpace →ₗ[ℝ] conwaySymmetricSpace :=
  griessConwayEncodeLinear.codRestrict conwaySymmetricSpace griessConwayEncode_symmetric

theorem griessConwayLinear_bijective : Function.Bijective griessConwayLinear := by
  constructor
  · intro x y h
    have he := congrArg griessConwayDecode (congrArg Subtype.val h)
    change griessConwayDecode (griessConwayEncode x) =
      griessConwayDecode (griessConwayEncode y) at he
    simpa only [griessConwayDecode_encode] using he
  · intro x
    refine ⟨griessConwayDecode x.val, Subtype.ext ?_⟩
    exact griessConwayEncode_decode x.val x.property

noncomputable def griessConwayEquiv : GriessSpace ≃ₗ[ℝ] conwaySymmetricSpace :=
  LinearEquiv.ofBijective griessConwayLinear griessConwayLinear_bijective


noncomputable def conwayTensorFlip : (Fin 24 → SpinSpace) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) where
  toFun x t i := x i t
  invFun x i t := x t i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def conwayTensorCoordinates :
    (SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  (TensorProduct.piScalarRight ℝ ℝ SpinSpace (Fin 24)).trans conwayTensorFlip

noncomputable def localTensorAction : localFiberSubgroup →*
    ((SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) ≃ₗ[ℝ] (SpinSpace ⊗[ℝ] (Fin 24 → ℝ))) where
  toFun f := TensorProduct.congr f.val.1.val f.val.2.val
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [TensorProduct.congr_tmul]; rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  map_mul' f g := TensorProduct.congr_mul _ _ _ _

noncomputable def coordinateGLTransport {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V]
    (e : U ≃ₗ[ℝ] V) : (U ≃ₗ[ℝ] U) →* (V ≃ₗ[ℝ] V) where
  toFun a := e.symm.trans (a.trans e)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_one, id_eq,
      LinearEquiv.apply_symm_apply]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

noncomputable def localTensorRepresentation : localFiberSubgroup →*
    ((SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ)) :=
  (coordinateGLTransport conwayTensorCoordinates).comp localTensorAction

theorem localTensorAction_diagonal (f : localFiberSubgroup) (hf : f ∈ localDiagonalSubgroup) :
    localTensorAction f = 1 := by
  obtain ⟨c, hc, he⟩ := hf
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change TensorProduct.congr f.val.1.val f.val.2.val (a ⊗ₜ[ℝ] b) = a ⊗ₜ[ℝ] b
    rw [TensorProduct.congr_tmul, hc, he, TensorProduct.smul_tmul_smul, qSign_sq, one_smul]
  | add a b ha hb => simp only [map_add, ha, hb]


abbrev ConwayBilin := LinearMap.BilinForm ℝ (Fin 24 → ℝ)

noncomputable def conwayBilinPullback (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) :
    ConwayBilin ≃ₗ[ℝ] ConwayBilin where
  toFun b := b.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  invFun b := b.compl₁₂ e.toLinearMap e.toLinearMap
  left_inv b := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change b (e.symm (e x)) (e.symm (e y)) = b x y
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv b := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change b (e (e.symm x)) (e (e.symm y)) = b x y
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  map_add' b c := by ext x y; rfl
  map_smul' r b := by ext x y; rfl

noncomputable def conwayMatrixAction : leechIsomSubgroup →*
    (Matrix (Fin 24) (Fin 24) ℝ ≃ₗ[ℝ] Matrix (Fin 24) (Fin 24) ℝ) where
  toFun e := Matrix.toBilin'.trans ((conwayBilinPullback e.val).trans Matrix.toBilin'.symm)
  map_one' := by
    apply LinearEquiv.ext
    intro a
    apply Matrix.toBilin'.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro a
    apply Matrix.toBilin'.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Matrix.toBilin' a ((e.val * f.val).symm x) ((e.val * f.val).symm y) =
      Matrix.toBilin' a (f.val.symm (e.val.symm x)) (f.val.symm (e.val.symm y))
    rfl

theorem conwayMatrixAction_pairing (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (x y : Fin 24 → ℝ) :
    Matrix.toBilin' (conwayMatrixAction e a) x y =
      Matrix.toBilin' a (e.val.symm x) (e.val.symm y) := by
  have hh := Matrix.toBilin'.apply_symm_apply (conwayBilinPullback e.val (Matrix.toBilin' a))
  exact congrFun (congrArg DFunLike.coe hh) x ▸ rfl

theorem conwayMatrix_symmetric_pairing (a : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, a i j = a j i) (x y : Fin 24 → ℝ) :
    Matrix.toBilin' a x y = Matrix.toBilin' a y x := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha i j]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem conwayMatrixAction_symmetric (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (ha : ∀ i j, a i j = a j i) :
    ∀ i j, conwayMatrixAction e a i j = conwayMatrixAction e a j i := by
  intro i j
  rw [← Matrix.toBilin'_single (conwayMatrixAction e a) i j,
    ← Matrix.toBilin'_single (conwayMatrixAction e a) j i,
    conwayMatrixAction_pairing, conwayMatrixAction_pairing]
  exact conwayMatrix_symmetric_pairing a ha _ _

theorem conwayMatrixAction_scalar (e : leechIsomSubgroup) (c : ZMod 2)
    (he : ∀ x : Fin 24 → ℝ, e.val x = qSign c • x) : conwayMatrixAction e = 1 := by
  have hinv (x : Fin 24 → ℝ) : e.val.symm x = qSign c • x := by
    apply e.val.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, he, smul_smul, qSign_sq, one_smul]
  apply LinearEquiv.ext
  intro a
  apply Matrix.toBilin'.injective
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [conwayMatrixAction_pairing, hinv, hinv]
  change Matrix.toBilin' a (qSign c • x) (qSign c • y) = Matrix.toBilin' a x y
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← mul_assoc, qSign_sq, one_mul]


theorem spinConjugation_scalar (s : SpinHolomorph) (c : ZMod 2)
    (hs : ∀ x : SpinSpace, s.val x = qSign c • x) : spinConjugation s = 1 := by
  have hinv (x : SpinSpace) : s.val.symm x = qSign c • x := by
    apply s.val.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hs, smul_smul, qSign_sq, one_smul]
  apply MulEquiv.ext
  intro q
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  apply LinearEquiv.ext
  intro x
  change s.val (spinRepresentation q (s.val.symm x)) = spinRepresentation q x
  rw [hinv, hs, map_smul, smul_smul, qSign_sq, one_smul]

theorem localShortRepresentation_diagonal (f : localFiberSubgroup)
    (hf : f ∈ localDiagonalSubgroup) : localShortRepresentation f = 1 := by
  obtain ⟨c, hc, _⟩ := hf
  have ha := spinConjugation_scalar f.val.1 c hc
  have hp (r : GriessShortIndex) : griessShortPermutation f.val.2 r = r := by
    apply griessShortClass_injective
    apply leechHyperbolicCoordinates.injective
    have hb := griessShortQ_image_base f r
    rw [ha] at hb
    have he := congrArg Multiplicative.toAdd hb
    exact he.symm
  have hphase (r : GriessShortIndex) : localShortPhase f r = 0 := by
    change toAdd (spinConjugation f.val.1 (griessShortQ r)).coeff = 0
    rw [ha]
    rfl
  apply LinearEquiv.ext
  intro x
  funext r
  have h := localShortOperator_image f x r
  rw [hp, hphase, qSign_zero, one_mul] at h
  exact h


noncomputable def localMatrixRepresentation : localFiberSubgroup →*
    (Matrix (Fin 24) (Fin 24) ℝ ≃ₗ[ℝ] Matrix (Fin 24) (Fin 24) ℝ) :=
  conwayMatrixAction.comp
    ((MonoidHom.snd SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype)

noncomputable def coordinateProdGLHom {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V] :
    ((U ≃ₗ[ℝ] U) × (V ≃ₗ[ℝ] V)) →* ((U × V) ≃ₗ[ℝ] (U × V)) where
  toFun a := a.1.prodCongr a.2
  map_one' := by apply LinearEquiv.ext; intro x; rfl
  map_mul' a b := by apply LinearEquiv.ext; intro x; rfl

noncomputable def localConwayRawRepresentation : localFiberSubgroup →*
    (ConwayRawSpace ≃ₗ[ℝ] ConwayRawSpace) :=
  coordinateProdGLHom.comp
    (localMatrixRepresentation.prod
      (coordinateProdGLHom.comp (localShortRepresentation.prod localTensorRepresentation)))

noncomputable def localConwayEquiv (f : localFiberSubgroup) :
    conwaySymmetricSpace ≃ₗ[ℝ] conwaySymmetricSpace where
  toFun x := ⟨localConwayRawRepresentation f x.val,
    conwayMatrixAction_symmetric f.val.2 x.val.1 x.property⟩
  invFun x := ⟨localConwayRawRepresentation f⁻¹ x.val,
    conwayMatrixAction_symmetric f⁻¹.val.2 x.val.1 x.property⟩
  left_inv x := by
    apply Subtype.ext
    change localConwayRawRepresentation f⁻¹ (localConwayRawRepresentation f x.val) = x.val
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change localConwayRawRepresentation f (localConwayRawRepresentation f⁻¹ x.val) = x.val
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext
    exact (localConwayRawRepresentation f).map_add x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact (localConwayRawRepresentation f).map_smul c x.val

noncomputable def localConwayRepresentation : localFiberSubgroup →*
    (conwaySymmetricSpace ≃ₗ[ℝ] conwaySymmetricSpace) where
  toFun := localConwayEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change localConwayRawRepresentation 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change localConwayRawRepresentation (f * g) x.val =
      localConwayRawRepresentation f (localConwayRawRepresentation g x.val)
    rw [map_mul]
    rfl

noncomputable def localGriessRepresentation : localFiberSubgroup →*
    (GriessSpace ≃ₗ[ℝ] GriessSpace) where
  toFun f := griessConwayEquiv.trans ((localConwayRepresentation f).trans griessConwayEquiv.symm)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, map_one, LinearEquiv.coe_one, id_eq,
      LinearEquiv.symm_apply_apply]
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

theorem localTensorRepresentation_diagonal (f : localFiberSubgroup)
    (hf : f ∈ localDiagonalSubgroup) : localTensorRepresentation f = 1 := by
  change coordinateGLTransport conwayTensorCoordinates (localTensorAction f) = 1
  rw [localTensorAction_diagonal f hf, map_one]

theorem localConwayRawRepresentation_diagonal (f : localFiberSubgroup)
    (hf : f ∈ localDiagonalSubgroup) : localConwayRawRepresentation f = 1 := by
  have hdiag := hf
  obtain ⟨c, hc, he⟩ := hdiag
  have hm : localMatrixRepresentation f = 1 := conwayMatrixAction_scalar f.val.2 c he
  have hs := localShortRepresentation_diagonal f hf
  have ht := localTensorRepresentation_diagonal f hf
  change coordinateProdGLHom (localMatrixRepresentation f,
    coordinateProdGLHom (localShortRepresentation f, localTensorRepresentation f)) = 1
  rw [hm, hs, ht]
  have hinner : coordinateProdGLHom
      ((1 : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ)),
        (1 : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))) = 1 :=
    coordinateProdGLHom.map_one
  rw [hinner]
  exact coordinateProdGLHom.map_one

theorem localConwayRepresentation_diagonal (f : localFiberSubgroup)
    (hf : f ∈ localDiagonalSubgroup) : localConwayRepresentation f = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  change localConwayRawRepresentation f x.val = x.val
  rw [localConwayRawRepresentation_diagonal f hf]
  rfl

theorem localGriessRepresentation_diagonal (f : localFiberSubgroup)
    (hf : f ∈ localDiagonalSubgroup) : localGriessRepresentation f = 1 := by
  apply LinearEquiv.ext
  intro x
  change griessConwayEquiv.symm (localConwayRepresentation f (griessConwayEquiv x)) = x
  rw [localConwayRepresentation_diagonal f hf]
  exact griessConwayEquiv.symm_apply_apply x

theorem localDiagonal_le_griess_ker : localDiagonalSubgroup ≤ localGriessRepresentation.ker := by
  intro f hf
  exact localGriessRepresentation_diagonal f hf

/-- The source local action on the fixed Griess dictionary coordinates.
Conway's symmetric-matrix, signed-short, and spin-tensor actions are transported
through the explicit coordinate equivalence. Simultaneous central signs are
proved to act trivially, so the action descends to H. Faithfulness and
preservation of the product and form are the separate conclusions of T1. -/
noncomputable def rhoLocal : H →* (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  QuotientGroup.lift localDiagonalSubgroup localGriessRepresentation localDiagonal_le_griess_ker

/-- Concrete dictionary structure constants, derived from Conway's six rules. -/
noncomputable def griessStructureConstant (i j k : Fin 196884) : ℝ :=
  griessConwayDecode (conwayRawProduct (griessConwayEncode (Pi.single i 1))
    (griessConwayEncode (Pi.single j 1))) k

noncomputable def griessProductFun (x y : GriessSpace) : GriessSpace :=
  fun k => ∑ i, ∑ j, x i * y j * griessStructureConstant i j k

set_option maxRecDepth 10000 in
-- The nested finite-coordinate bilinear map exceeds the default elaboration recursion depth.
/-- The Griess product in the fixed dictionary basis, from Conway §12.
Structure constants are computed from the source's six rules and explicit
Golay/Parker, short-vector, and Schrödinger coordinates. Bilinearity follows
by extending those constants over the real coordinate space. -/
noncomputable def griessProd :
    GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace :=
  LinearMap.mk₂ ℝ griessProductFun
    (by intros; ext k; simp [griessProductFun, add_mul, Finset.sum_add_distrib])
    (by
      intros c x y
      ext k
      simp only [griessProductFun, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum])
    (by intros; ext k; simp [griessProductFun, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intros c x y
      ext k
      simp only [griessProductFun, Pi.smul_apply, smul_eq_mul]
      simp_rw [show ∀ a b d : ℝ, a * (c * b) * d = c * (a * b * d) by intros; ring]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum])


/-- Genuine definition (no hole): a Griess automorphism is a linear
equivalence preserving BOTH the specified product and the specified form. -/
def IsGriessAuto (e : GriessSpace ≃ₗ[ℝ] GriessSpace) : Prop :=
  (∀ x y, e (griessProd x y) = griessProd (e x) (e y)) ∧
  (∀ x y, griessForm (e x) (e y) = griessForm x y)

set_option maxRecDepth 10000 in
-- Reducing the identity automorphism through the concrete product has deeply nested coordinates.
/-- The product-and-form preserving subgroup of the ambient general linear
group. Genuine definition with proved closure laws (former framework holes
F-Aut*); the laws hold for the specified product/form ahead of source
binding. -/
noncomputable def griessAutSubgroup : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  { carrier := { e | IsGriessAuto e },
    one_mem' := by
      constructor <;> intro x y <;> simp only [LinearEquiv.coe_one, id_eq],
    mul_mem' := by
      intro a b ha hb
      obtain ⟨hpa, hfa⟩ := ha
      obtain ⟨hpb, hfb⟩ := hb
      refine ⟨fun x y => ?_, fun x y => ?_⟩
      · change (a * b) (griessProd x y) = griessProd ((a * b) x) ((a * b) y)
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          hpb, hpa]
      · change griessForm ((a * b) x) ((a * b) y) = griessForm x y
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfa, hfb]
    inv_mem' := by
      intro a ha
      obtain ⟨hpa, hfa⟩ := ha
      refine ⟨fun x y => ?_, fun x y => ?_⟩
      · have h := hpa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        calc a.symm (griessProd x y)
            = a.symm (a (griessProd (a.symm x) (a.symm y))) := by rw [h]
          _ = griessProd (a.symm x) (a.symm y) :=
            LinearEquiv.symm_apply_apply a _
      · have h := hfa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        exact h.symm }


/-- Explicit source triality from Seysen §8.1 in the dictionary basis fixed
by `griessBasisWeight` and `trialityBlocksEquiv`. Linearity and inverse laws
are complete; comparison with the FLM symmetry and product preservation
remain to be proved. -/
noncomputable def sExtra : GriessSpace ≃ₗ[ℝ] GriessSpace := griessTriality

/-- Genuine definition (no endpoint conclusions built in): the concrete group
under study, generated by the local image and the extra symmetry. -/
noncomputable def G : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  Subgroup.closure (Set.range ⇑rhoLocal ∪ { sExtra })


/-! ## Independent presentation reference model -/


/-- Vertices of the Y₅₅₅ tree: a central vertex and three arms of length five.
Source: Basak, arXiv:0811.0062v2, §1.1, Ivanov–Norton presentation theorem
(the paper calls this sixteen-vertex diagram M₆₆₆). -/
abbrev Y555Vertex := Option (Fin 3 × Fin 5)

/-- The edges join the central vertex to the first vertex of each arm and
successive vertices on the same arm. -/
def y555Adjacent : Y555Vertex → Y555Vertex → Prop
  | none, some v => v.2.val = 0
  | some u, none => u.2.val = 0
  | some u, some v => u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)
  | none, none => False
instance instDecidableY555Adjacent (u v : Y555Vertex) : Decidable (y555Adjacent u v) := by
  cases u <;> cases v <;> simp only [y555Adjacent] <;> infer_instance

/-- The spider word `a b₁ c₁ a b₂ c₂ a b₃ c₃` in the published presentation. -/
def y555Spider : FreeGroup Y555Vertex :=
  FreeGroup.of none * FreeGroup.of (some (0, 0)) * FreeGroup.of (some (0, 1)) *
  FreeGroup.of none * FreeGroup.of (some (1, 0)) * FreeGroup.of (some (1, 1)) *
  FreeGroup.of none * FreeGroup.of (some (2, 0)) * FreeGroup.of (some (2, 1))

/-- The complete relator set: involutions, Coxeter edge/nonedge relations,
and the tenth power of the spider word. No Monster group properties are
assumed in the construction of this quotient. -/
def y555Relations : Set (FreeGroup Y555Vertex) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y555Adjacent u v then 3 else 2 : ℕ)) ∨ w = y555Spider ^ 10}

/-- The bimonster presentation, as the free group modulo the normal closure
of the explicit relators. The source identification theorem is not used as
an axiom here. -/
abbrev BimonsterPresentation : Type := PresentedGroup y555Relations

/-- The central tree generator, an outer involution in the bimonster model.
This source identification is a separate recognition theorem. -/
def bimonsterSwap : BimonsterPresentation := PresentedGroup.of none

/-- Centralizer of the chosen involution in the presented group. -/
def bimonsterSwapCentralizer : Subgroup BimonsterPresentation :=
  Subgroup.centralizer {bimonsterSwap}

/-- The involution belongs to its own centralizer. -/
def bimonsterSwapInCentralizer : bimonsterSwapCentralizer :=
  ⟨bimonsterSwap, by
    change bimonsterSwap ∈ Subgroup.centralizer {bimonsterSwap}
    rw [Subgroup.mem_centralizer_singleton_iff]⟩

/-- Cyclic subgroup generated by the involution, inside its centralizer. -/
def bimonsterSwapPowers : Subgroup bimonsterSwapCentralizer :=
  Subgroup.zpowers bimonsterSwapInCentralizer

instance bimonsterSwapPowersNormal : bimonsterSwapPowers.Normal := by
  apply Subgroup.normal_of_le_center
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp g.property

/-- An independent presentation reference model for the classical Monster:
centralize an outer involution in the bimonster presentation, then quotient
by that involution. For a wreath product `M ≀ C₂`, this yields the diagonal
copy of `M`. Identifying the presented group with the bimonster, and this
quotient with the historical Monster, requires the source recognition theorem
and the wreath-product centralizer argument; neither is assumed as an axiom.
This definition is independent of `G` and of the FLM construction placeholders. -/
def classicalMonster : Type := bimonsterSwapCentralizer ⧸ bimonsterSwapPowers
instance instGroupClassical : Group classicalMonster :=
  inferInstanceAs (Group (bimonsterSwapCentralizer ⧸ bimonsterSwapPowers))


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
