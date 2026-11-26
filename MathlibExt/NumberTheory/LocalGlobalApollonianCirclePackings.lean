/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The local-global conjecture for Apollonian circle packings is false

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.NumberTheory.LocalGlobalApollonianCirclePackings` —
annals_local_global_apollonian_circle_packings (manifest
`manifests/problems/annals_local_global_apollonian_circle_packings.toml`, rev 1, submitter
Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the
`MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted` namespace. Mathematical
statements are unchanged. Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A primitive Apollonian circle packing with no square curvatures

The shared Descartes and packing model below is moved from the wanted module. The proof of
Theorem 1.6 uses the quadratic obstruction of Haag, Kertzer, Rickards, and Stange, §§1.3 and 4.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted

set_option autoImplicit false

namespace LocalGlobalApollonianCirclePackings

open Matrix

/-- The action of the general linear group on quadruples of integers. -/
instance : MulAction (GL (Fin 4) ℤ) (Fin 4 → ℤ) where
  smul X v := X.1 *ᵥ v
  one_smul v := one_mulVec v
  mul_smul X Y v := (mulVec_mulVec v X.1 Y.1).symm

@[simp]
lemma GeneralLinearGroup.smul_def (X : GL (Fin 4) ℤ) (v : Fin 4 → ℤ) :
    X • v = X.1 *ᵥ v :=
  rfl

/-- **General linear group action on primitive vectors.** Call $v \in \mathbb{Z}^4$ primitive
when the greatest common divisor of its four entries is $1$. For every
$X \in \mathrm{GL}_4(\mathbb{Z})$ and every primitive $v$, the vector $Xv$ is primitive, so
$\mathrm{GL}_4(\mathbb{Z})$ acts on the primitive vectors of $\mathbb{Z}^4$ by $v \mapsto Xv$. -/
def GeneralLinearGroupAction : SubMulAction (GL (Fin 4) ℤ) (Fin 4 → ℤ) where
  carrier := { v | Finset.univ.gcd v = 1}
  smul_mem' X v hv := by
    rw [Set.mem_ofPred_eq] at hv ⊢
    apply Int.eq_one_of_dvd_one
    · rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
      apply abs_nonneg
    · rw [← hv, Finset.dvd_gcd_iff]
      intro i _
      have key : v i = ((X⁻¹).1 *ᵥ (X.1 *ᵥ v)) i := by simp
      rw [key, mulVec_eq_sum (X.1 *ᵥ v) (X⁻¹).1]
      simp only [op_smul_eq_smul, Finset.sum_apply]
      apply Finset.dvd_sum
      intro i hi
      apply dvd_mul_of_dvd_left
      apply Finset.gcd_dvd hi

/-- **Descartes matrix.** The Descartes matrix is the $4 \times 4$ integer matrix $M$ with
$M_{ii} = 1$ for every $i$ and $M_{ij} = -1$ for $i \ne j$. It is the matrix of the Descartes
form: for $v = (a, b, c, d) \in \mathbb{Z}^4$ one has
$v^{\mathsf T} M v = 2(a^2 + b^2 + c^2 + d^2) - (a + b + c + d)^2$. -/
def DescartesMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, -1, -1;
     -1, 1, -1, -1;
     -1, -1, 1, -1;
     -1, -1, -1, 1]

/-- **Descartes orthogonal group.** Let $M$ be the Descartes matrix. The Descartes orthogonal
group is the subgroup of $\mathrm{GL}_4(\mathbb{Z})$ consisting of the matrices $X$ with
$X^{\mathsf T} M X = M$, that is, the invertible integer matrices that preserve the Descartes
form $2(a^2 + b^2 + c^2 + d^2) - (a + b + c + d)^2$. -/
def DescartesOrthogonalGroup : Subgroup (GL (Fin 4) ℤ) where
  carrier := {X | star X * DescartesMatrix * X = DescartesMatrix}
  one_mem' := by simp
  inv_mem' hX := by grind [star_inv, Units.inv_mul_cancel_left, Units.mul_inv]
  mul_mem' hX hY := by grind [Units.val_mul, StarMul.star_mul]

theorem mem_descartesOrthogonalGroup_iff {X : GL (Fin 4) ℤ} :
    X ∈ DescartesOrthogonalGroup ↔ star X * DescartesMatrix * X = DescartesMatrix :=
  Iff.rfl

instance (X : GL (Fin 4) ℤ) : Decidable (X ∈ DescartesOrthogonalGroup) :=
  decidable_of_iff (star X * DescartesMatrix * X = DescartesMatrix) mem_descartesOrthogonalGroup_iff

theorem descartes_iff {v : Fin 4 → ℤ} :
    (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ↔ v ᵥ* DescartesMatrix ⬝ᵥ v = 0 := by
  simp [DescartesMatrix, vecMul_eq_sum, dotProduct, Fin.sum_univ_four]
  grind

/-- **Descartes orthogonal group action.** Let $Q$ be the set of vectors
$(a, b, c, d) \in \mathbb{Z}^4$ with $(a + b + c + d)^2 = 2(a^2 + b^2 + c^2 + d^2)$ and
$\gcd(a, b, c, d) = 1$. For every matrix $X$ in the Descartes orthogonal group and every $v \in Q$,
the vector $Xv$ lies in $Q$, so the Descartes orthogonal group acts on $Q$ by $v \mapsto Xv$. -/
def DescartesOrthogonalGroupAction : SubMulAction DescartesOrthogonalGroup (Fin 4 → ℤ) where
  carrier := { v | (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1}
  smul_mem' := by
    rintro ⟨X, hX⟩ v ⟨hv1, hv2⟩
    rw [mem_descartesOrthogonalGroup_iff, Units.coe_star,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hX
    refine ⟨?_, GeneralLinearGroupAction.smul_mem X hv2⟩
    rw [descartes_iff] at hv1 ⊢
    rwa [Subgroup.mk_smul, GeneralLinearGroup.smul_def,
      vecMul_mulVec, dotProduct_mulVec, vecMul_vecMul, hX]

/-- **Integral primitive Descartes quadruple.** An integral primitive Descartes quadruple is a
vector $(a, b, c, d) \in \mathbb{Z}^4$ such that $a + b + c + d > 0$, the Descartes equation
$(a + b + c + d)^2 = 2(a^2 + b^2 + c^2 + d^2)$ holds, and $\gcd(a, b, c, d) = 1$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for
Apollonian circle packings is false`, Annals of Math, 200 (2) 2024, Section 1.1. -/
def integralPrimitiveDescartesQuadruple : Set (Fin 4 → ℤ) :=
  { v | ∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1}

theorem mem_integralPrimitiveDescartesQuadruple_iff {v : Fin 4 → ℤ} :
    v ∈ integralPrimitiveDescartesQuadruple ↔
      ∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1 :=
  Iff.rfl

instance (v : Fin 4 → ℤ) : Decidable (v ∈ integralPrimitiveDescartesQuadruple) :=
  decidable_of_iff
    (∑ i, v i > 0 ∧ (∑ i, v i) ^ 2 = 2 * ∑ i, v i ^ 2 ∧ Finset.univ.gcd v = 1)
    mem_integralPrimitiveDescartesQuadruple_iff

/-- **The Apollonian generator $S_1$.** $S_1$ is the element of $\mathrm{GL}_4(\mathbb{Z})$ given
by the $4 \times 4$ integer matrix whose first row is $(-1, 2, 2, 2)$ and whose other rows are
those of the identity matrix; it is its own inverse. Acting on column vectors, it sends
$(a, b, c, d)$ to $(-a + 2b + 2c + 2d, b, c, d)$.

It is one of the four generators of the Apollonian group defined at the start of Section 3 of
Haag, Kertzer, Rickards and Stange. -/
abbrev S₁ : GL (Fin 4) ℤ :=
  ⟨!![-1, 2, 2, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![-1, 2, 2, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    by decide, by decide⟩

/-- **The Apollonian generator $S_2$.** $S_2$ is the element of $\mathrm{GL}_4(\mathbb{Z})$ given
by the $4 \times 4$ integer matrix whose second row is $(2, -1, 2, 2)$ and whose other rows are
those of the identity matrix; it is its own inverse. Acting on column vectors, it sends
$(a, b, c, d)$ to $(a, 2a - b + 2c + 2d, c, d)$.

It is one of the four generators of the Apollonian group defined at the start of Section 3 of
Haag, Kertzer, Rickards and Stange. -/
abbrev S₂ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 2, -1, 2, 2; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 2, -1, 2, 2; 0, 0, 1, 0; 0, 0, 0, 1],
    by decide, by decide⟩

/-- **The Apollonian generator $S_3$.** $S_3$ is the element of $\mathrm{GL}_4(\mathbb{Z})$ given
by the $4 \times 4$ integer matrix whose third row is $(2, 2, -1, 2)$ and whose other rows are
those of the identity matrix; it is its own inverse. Acting on column vectors, it sends
$(a, b, c, d)$ to $(a, b, 2a + 2b - c + 2d, d)$.

It is one of the four generators of the Apollonian group defined at the start of Section 3 of
Haag, Kertzer, Rickards and Stange. -/
abbrev S₃ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 2, 2, -1, 2; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 2, 2, -1, 2; 0, 0, 0, 1],
    by decide, by decide⟩

/-- **The Apollonian generator $S_4$.** $S_4$ is the element of $\mathrm{GL}_4(\mathbb{Z})$ given
by the $4 \times 4$ integer matrix whose fourth row is $(2, 2, 2, -1)$ and whose other rows are
those of the identity matrix; it is its own inverse. Acting on column vectors, it sends
$(a, b, c, d)$ to $(a, b, c, 2a + 2b + 2c - d)$.

It is one of the four generators of the Apollonian group defined at the start of Section 3 of
Haag, Kertzer, Rickards and Stange. -/
abbrev S₄ : GL (Fin 4) ℤ :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 2, -1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 2, -1],
    by decide, by decide⟩

/-- **Apollonian group.** The Apollonian group is the subgroup of $\mathrm{GL}_4(\mathbb{Z})$
generated by the four matrices $S_1, S_2, S_3, S_4$, where $S_i$ agrees with the $4 \times 4$
identity matrix except in row $i$, which has entry $-1$ in column $i$ and entry $2$ in each of
the other three columns.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for
Apollonian circle packings is false`, Annals of Math, 200 (2) 2024, start of Section 3. -/
def ApollonianGroup : Subgroup (GL (Fin 4) ℤ) := Subgroup.closure {S₁, S₂, S₃, S₄}

theorem apollonianGroup_le_descartesOrthogonalGroup :
    ApollonianGroup ≤ DescartesOrthogonalGroup := by
  simp +decide [ApollonianGroup, Set.insert_subset_iff]

/-- **The transformation group.** The transformation group is the subgroup of
$\mathrm{GL}_4(\mathbb{Z})$ generated by the Apollonian group together with all $4 \times 4$
permutation matrices. -/
def TransformationGroup : Subgroup (GL (Fin 4) ℤ) :=
  ApollonianGroup ⊔ permMatrixHom.toHomUnits.range

open scoped Pointwise

/-- **The transformation group preserves integral primitive Descartes quadruples.**
For every $g$ in the transformation group, $g$ maps the set of integral primitive Descartes
quadruples into itself: if $v \in \mathbb{Z}^4$ is an integral primitive Descartes quadruple,
then so is $g v$. -/
theorem transformationGroup_smul_integralPrimitiveDescartesQuadruple
    (g : GL (Fin 4) ℤ) (hg : g ∈ TransformationGroup) :
    g • integralPrimitiveDescartesQuadruple ⊆ integralPrimitiveDescartesQuadruple := by
  revert g
  rw [← MulAction.le_stabilizer_iff_smul_le]
  apply sup_le
  · suffices h1 : ∀ X ∈ ({S₁, S₂, S₃, S₄} : Set (GL (Fin 4) ℤ)),
        X • integralPrimitiveDescartesQuadruple ⊆ integralPrimitiveDescartesQuadruple by
      rw [ApollonianGroup, Subgroup.closure_le]
      simp_rw [Set.subset_def, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Set.Subset.antisymm_iff, forall_and, Set.subset_smul_set_iff, and_iff_right h1]
      rw [show ({S₁, S₂, S₃, S₄} : Set (GL (Fin 4) ℤ)) = {S₁, S₂, S₃, S₄}⁻¹ by simp]
      simpa only [Set.mem_inv, Set.forall_inv_mem]
    simp only [Set.smul_set_subset_iff]
    rintro X hX v ⟨hv1, hv2⟩
    refine ⟨?_, DescartesOrthogonalGroupAction.smul_mem
      ⟨X, apollonianGroup_le_descartesOrthogonalGroup (Subgroup.subset_closure hX)⟩ hv2⟩
    simp only [Fin.sum_univ_four] at hv1 hv2
    rcases hX with rfl | rfl | rfl | rfl <;> simp [Fin.sum_univ_four, mulVec_eq_sum] <;> nlinarith
  · rw [MulAction.le_stabilizer_iff_smul_le]
    simp only [Set.smul_set_subset_iff]
    rintro X ⟨σ, rfl⟩ v ⟨hv1, hv2, hv3⟩
    simp only [GeneralLinearGroup.smul_def, MonoidHom.coe_toHomUnits, permMatrixHom_apply,
      permMatrix_mulVec, Equiv.Perm.coe_inv, mem_integralPrimitiveDescartesQuadruple_iff,
      Function.comp_apply, Equiv.sum_comp, gt_iff_lt]
    refine ⟨hv1, ?_, ?_⟩
    · refine hv2.trans ?_
      congr 1
      exact (Equiv.sum_comp _ _).symm
    · rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
      apply Int.eq_one_of_dvd_one (abs_nonneg _)
      rw [Int.abs_eq_normalize, Finset.normalize_gcd, ← hv3, Finset.dvd_gcd_iff]
      exact fun i hi ↦ (Finset.gcd_dvd (Finset.mem_univ (σ i))).trans (by simp)

/-- **Action of the transformation group on integral primitive Descartes quadruples.** Each
element $g$ of the transformation group sends an integral primitive Descartes quadruple $v$ to
$g v$, by matrix–vector multiplication: this is the restriction of the action of the
transformation group on $\mathbb{Z}^4$ to the set of integral primitive Descartes quadruples,
which is closed under the action. -/
def TransformationGroupAction : SubMulAction TransformationGroup (Fin 4 → ℤ) where
  carrier := integralPrimitiveDescartesQuadruple
  smul_mem' X v hv :=
    transformationGroup_smul_integralPrimitiveDescartesQuadruple X X.2 ⟨v, hv, rfl⟩

instance : MulAction TransformationGroup integralPrimitiveDescartesQuadruple :=
  TransformationGroupAction.mulAction

/-- **Primitive Apollonian circle packing.** A primitive Apollonian circle packing is an orbit of
the transformation group acting on the set of integral primitive Descartes quadruples. -/
def PrimitiveApollonianCirclePacking :=
  MulAction.orbitRel.Quotient TransformationGroup integralPrimitiveDescartesQuadruple

/-- **Curvature set.** Let $A$ be a primitive Apollonian circle packing, viewed as an orbit of
integral primitive Descartes quadruples. The curvature set of $A$ is the set of all integers
that occur as an entry of some quadruple in $A$. -/
def curvatureSet (A : PrimitiveApollonianCirclePacking) : Set ℤ :=
  ⋃ v ∈ A.orbit, Set.range v.1

open scoped NumberTheorySymbols

-- On a coprime edge there is an odd endpoint congruent to 5 modulo 8.
-- Its supplementary symbol at 2 is -1, so the 2-part of the other
-- denominator contributes one minus sign for each factor of 2.
private def twoPartSign (n : ℕ) : ℤ :=
  if 0 < n ∧ n % 2 = 0 then -twoPartSign (n / 2) else 1
termination_by n
decreasing_by omega

private def edgeChar (a z : ℤ) : ℤ :=
  twoPartSign a.natAbs * J(z | a.natAbs)

private lemma natAbs_mod_eight {b : ℤ} (hb : b % 8 = 5) :
    b.natAbs % 8 = if b < 0 then 3 else 5 := by
  split <;> omega

private lemma jacobi_nat_odd_reciprocity {b : ℤ} (hb : b % 8 = 5) {n : ℕ} (hn : 0 < n) :
    J((n : ℤ) | b.natAbs) = twoPartSign n * J(b | n) := by
  have hb8 := natAbs_mod_eight hb
  have hb2 : b.natAbs % 2 = 1 := by split at hb8 <;> omega
  have hodd := Nat.odd_iff.mpr hb2
  have htwo : J(2 | b.natAbs) = -1 := by
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight, hb2, hb8]
    by_cases h : b < 0 <;> simp [h]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn2 : n % 2 = 0
    · have heq : 2 * (n / 2) = n := by omega
      have hj2 : J(b | 2) = 1 := by
        rw [jacobiSym.mod_left, show b % ((2 : ℕ) : ℤ) = 1 by omega, jacobiSym.one_left]
      have hj := jacobiSym.mul_right' b (by decide : (2 : ℕ) ≠ 0)
        (show n / 2 ≠ 0 by omega)
      rw [heq, hj2, one_mul] at hj
      have hcast : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) := by exact_mod_cast heq.symm
      rw [twoPartSign, ite_eq_left ⟨hn, hn2⟩]
      conv_lhs => arg 1; rw [hcast]
      rw [jacobiSym.mul_left, htwo, ih (n / 2) (by omega) (by omega), hj]
      ring
    · have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
      rw [twoPartSign, ite_eq_right (fun h ↦ hn2 h.2), one_mul]
      by_cases hbneg : b < 0
      · have hb4 : b.natAbs % 4 = 3 := by rw [ite_eq_left hbneg] at hb8; omega
        have hcast : b = -(b.natAbs : ℤ) := by omega
        conv_rhs => rw [hcast]
        rw [jacobiSym.neg _ hnodd, jacobiSym.quadratic_reciprocity' hnodd hodd,
          qrSign, ZMod.χ₄_nat_three_mod_four hb4, jacobiSym.at_neg_one hnodd]
      · have hb4 : b.natAbs % 4 = 1 := by rw [ite_eq_right hbneg] at hb8; omega
        conv_rhs => rw [← Int.natAbs_of_nonneg (by omega : 0 ≤ b)]
        exact jacobiSym.quadratic_reciprocity_one_mod_four' hnodd hb4

private lemma edgeChar_odd_reciprocity {a b : ℤ} (ha : a ≠ 0) (hb : b % 8 = 5)
    (hs : 0 ≤ a + b) : edgeChar a b = edgeChar b a := by
  have hb2 : b.natAbs % 2 = 1 := by have := natAbs_mod_eight hb; split at this <;> omega
  have hbSign : twoPartSign b.natAbs = 1 := by rw [twoPartSign, ite_eq_right (by omega)]
  have hr := jacobi_nat_odd_reciprocity hb (n := a.natAbs) (by omega)
  unfold edgeChar
  rw [hbSign, one_mul, ← hr]
  by_cases ha0 : 0 ≤ a
  · rw [Int.natAbs_of_nonneg ha0]
  · have hb0 : 0 ≤ b := by omega
    have hb4 : b.natAbs % 4 = 1 := by omega
    have haAbs : a = -(a.natAbs : ℤ) := by omega
    conv_rhs => rw [haAbs]
    rw [jacobiSym.neg _ (Nat.odd_iff.mpr hb2), ZMod.χ₄_nat_one_mod_four hb4, one_mul]

private lemma edgeChar_reciprocity {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hodd : a % 8 = 5 ∨ b % 8 = 5) (hs : 0 ≤ a + b) : edgeChar a b = edgeChar b a := by
  rcases hodd with ho | ho
  · exact (edgeChar_odd_reciprocity hb ho (by omega)).symm
  · exact edgeChar_odd_reciprocity ha ho hs

private lemma jacobi_mod {a b m : ℤ} (h : a ≡ b [ZMOD m]) :
    J(a | m.natAbs) = J(b | m.natAbs) :=
  jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (Int.natAbs_dvd.mpr (Int.modEq_iff_dvd.mp h)))

private lemma gcd_mod {a b m : ℤ} (h : a ≡ b [ZMOD m]) : a.gcd m = b.gcd m := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
  have he : b = a + m * t := by omega
  rw [he, Int.gcd_add_mul_left_left]

private lemma edgeChar_mod {a z w : ℤ} (h : z ≡ w [ZMOD a]) :
    edgeChar a z = edgeChar a w := by
  rw [edgeChar, edgeChar, jacobi_mod h]

private lemma jacobi_eq_of_prod_mod_sq {a u v w : ℤ}
    (hu : u.gcd a = 1) (hv : v.gcd a = 1) (h : u * v ≡ w ^ 2 [ZMOD a]) :
    J(u | a.natAbs) = J(v | a.natAbs) := by
  have hcop : (u * v).gcd a = 1 := by
    simp only [Int.gcd_eq_natAbs] at hu hv ⊢
    simpa only [Int.natAbs_mul] using Nat.Coprime.mul_left hu hv
  have hcop' : (w ^ 2).gcd a = 1 := (gcd_mod h).symm.trans hcop
  have hg : w.gcd a = 1 := Int.gcd_eq_one_iff.mpr fun p hp ha ↦
    Int.gcd_eq_one_iff.mp hcop' p (dvd_pow hp (by decide)) ha
  have hnat (x : ℤ) : x.gcd (a.natAbs : ℤ) = x.gcd a := by
    simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  have hj := jacobi_mod h
  rw [jacobiSym.mul_left, jacobiSym.sq_one' ((hnat w).trans hg)] at hj
  rcases jacobiSym.eq_one_or_neg_one ((hnat u).trans hu) with h1 | h1 <;>
    rw [h1] at hj ⊢ <;> linarith

-- A scalar presentation of the arithmetic of a Descartes quadruple.
private def descartes (a b c d : ℤ) : Prop :=
  (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)

private def primitive (a b c d : ℤ) : Prop :=
  ∀ p : ℤ, p ∣ a → p ∣ b → p ∣ c → p ∣ d → p ∣ 1

private def seedResidue (a : ℤ) : Prop := a % 4 = 0 ∨ a % 8 = 5

private structure SeedResidues (a b c d : ℤ) : Prop where
  first : seedResidue a
  second : seedResidue b
  third : seedResidue c
  fourth : seedResidue d
  two_odd : a % 2 + b % 2 + c % 2 + d % 2 = 2

private lemma seedResidues_replace {a b c d : ℤ} (h : SeedResidues a b c d) :
    SeedResidues a b c (2 * (a + b + c) - d) := by
  obtain ⟨ha, hb, hc, hd, hn⟩ := h
  refine ⟨ha, hb, hc, ?_, by omega⟩
  unfold seedResidue at ha hb hc hd ⊢
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd <;> omega

private lemma pair_sum_nonneg {a b c d : ℤ} (h : descartes a b c d)
    (hs : 0 < a + b + c + d) : 0 ≤ a + b := by
  unfold descartes at h
  by_contra! hn
  have hr : 0 < c + d := by omega
  nlinarith [mul_neg_of_neg_of_pos hn hr, sq_nonneg (a - b), sq_nonneg (c - d)]

private lemma pair_sum_pos {a b c d : ℤ} (h : descartes a b c d)
    (hs : 0 < a + b + c + d) (ha : a ≠ 0) : 0 < a + b := by
  have hn := pair_sum_nonneg h hs
  by_contra! h'
  have hb : b = -a := by omega
  subst b
  unfold descartes at h
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  nlinarith [sq_nonneg (c - d)]

private def middle (a b c d : ℤ) : ℤ := (a + b + c - d) / 2

private lemma twice_middle {a b c d : ℤ} (h : SeedResidues a b c d) :
    2 * middle a b c d = a + b + c - d := by
  have hn := h.two_odd
  unfold middle
  omega

private lemma determinant {a b c d : ℤ} (h : descartes a b c d) (hr : SeedResidues a b c d) :
    (a + b) * (a + c) - middle a b c d ^ 2 = a ^ 2 := by
  unfold descartes at h
  have he := twice_middle hr
  have h4 : 4 * ((a + b) * (a + c) - middle a b c d ^ 2 - a ^ 2) = 0 := by
    linear_combination h - (2 * middle a b c d + (a + b + c - d)) * he
  omega

-- The double-replacement family of Lemma 4.5, including its first three values.
private def bridgePoly (a b c d x : ℤ) : ℤ :=
  (a + b) * x ^ 2 - (a + b + c - d) * x + c

private lemma bridge_zero (a b c d : ℤ) : bridgePoly a b c d 0 = c := by simp [bridgePoly]

private lemma bridge_one (a b c d : ℤ) : bridgePoly a b c d 1 = d := by
  unfold bridgePoly
  ring

private lemma bridge_add_two (a b c d x : ℤ) :
    bridgePoly a b c d (x + 2) =
      2 * (a + b + bridgePoly a b c d (x + 1)) - bridgePoly a b c d x := by
  unfold bridgePoly
  ring

private lemma bridge_residues {a b c d : ℤ} (h : SeedResidues a b c d) (k : ℕ) :
    SeedResidues a b (bridgePoly a b c d k) (bridgePoly a b c d ((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa [bridge_zero, bridge_one] using h
  | succ k ih =>
    have hswap : SeedResidues a b (bridgePoly a b c d ((k : ℤ) + 1)) (bridgePoly a b c d k) :=
      ⟨ih.first, ih.second, ih.fourth, ih.third, by have := ih.two_odd; omega⟩
    simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two, bridge_add_two] using
      seedResidues_replace hswap

private lemma bridge_mod {a b c d x y p : ℤ} (h : x ≡ y [ZMOD p]) :
    bridgePoly a b c d x ≡ bridgePoly a b c d y [ZMOD p] := by
  unfold bridgePoly
  exact ((Int.ModEq.refl (a + b)).mul (h.pow 2)).sub
    ((Int.ModEq.refl (a + b + c - d)).mul h) |>.add (Int.ModEq.refl c)

private lemma prime_not_dvd_one {p : ℕ} (hp : p.Prime) : ¬ ((p : ℤ) ∣ 1) := by
  intro hd
  have h : p ∣ (1 : ℕ) := by exact_mod_cast hd
  exact hp.ne_one (Nat.dvd_one.mp h)

private lemma bridge_avoids_prime {a b c d : ℤ} (hr : SeedResidues a b c d)
    (hpv : primitive a b c d) {p : ℕ} (hp : p.Prime) (hab : (p : ℤ) ∣ a * b) :
    ∃ k : ℕ, ¬ (p : ℤ) ∣ bridgePoly a b c d k := by
  by_contra! h
  have hc : (p : ℤ) ∣ c := by simpa [bridge_zero] using h 0
  have hd : (p : ℤ) ∣ d := by simpa [bridge_one] using h 1
  by_cases hp2 : p = 2
  · subst p
    have hab2 : (a * b) % 2 = 0 := Int.emod_eq_zero_of_dvd hab
    rw [Int.mul_emod] at hab2
    have hco : c % 2 = 0 := Int.emod_eq_zero_of_dvd hc
    have hdo : d % 2 = 0 := Int.emod_eq_zero_of_dvd hd
    have hn := hr.two_odd
    have ha : a % 2 = 1 := by omega
    have hb : b % 2 = 1 := by omega
    simp [ha, hb] at hab2
  · have hpz : Prime (p : ℤ) := by simpa [Int.prime_iff_natAbs_prime] using hp
    have hf2 := h 2
    push_cast at hf2
    rw [show (2 : ℤ) = 0 + 2 by decide, bridge_add_two, zero_add, bridge_one, bridge_zero] at hf2
    have h2 : (p : ℤ) ∣ 2 * (a + b) := by
      convert Int.dvd_sub (Int.dvd_add hf2 hc) (dvd_mul_of_dvd_right hd 2) using 1
      ring
    have hnd : ¬ (p : ℤ) ∣ 2 := by
      intro hh
      have hh' : p ∣ 2 := by exact_mod_cast hh
      exact hp2 ((Nat.dvd_prime_two_le Nat.prime_two hp.two_le).mp hh')
    have hs := (hpz.dvd_mul.mp h2).resolve_left hnd
    rcases hpz.dvd_mul.mp hab with ha | hb
    · exact prime_not_dvd_one hp (hpv p ha (by simpa using Int.dvd_sub hs ha) hc hd)
    · exact prime_not_dvd_one hp (hpv p (by simpa using Int.dvd_sub hs hb) hb hc hd)

private lemma exists_bridge {a b c d : ℤ} (hr : SeedResidues a b c d) (hpv : primitive a b c d)
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ k : ℕ, (bridgePoly a b c d k).gcd (a * b) = 1 := by
  classical
  let s := (a * b).natAbs.primeFactors
  have hs (p : ℕ) (hp : p ∈ s) := Nat.mem_primeFactors.mp hp
  have cast_dvd {p : ℕ} {z : ℤ} (h : p ∣ z.natAbs) : (p : ℤ) ∣ z :=
    Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using h)
  have hx (p : ℕ) (hp : p ∈ s) : ∃ k : ℕ, ¬ (p : ℤ) ∣ bridgePoly a b c d k :=
    bridge_avoids_prime hr hpv (hs p hp).1 (cast_dvd (hs p hp).2.1)
  let r (p : ℕ) : ℕ := if hp : p ∈ s then (hx p hp).choose else 0
  have hr' (p : ℕ) (hp : p ∈ s) : ¬ (p : ℤ) ∣ bridgePoly a b c d (r p) := by
    simpa only [r, dite_eq_left hp] using (hx p hp).choose_spec
  have hs0 : ∀ p ∈ s, p ≠ 0 := fun p hp ↦ (hs p hp).1.ne_zero
  have hsp : Set.Pairwise (↑s : Set ℕ) Nat.Coprime := by
    intro p hp q hq hne
    exact ((hs p hp).1.coprime_iff_not_dvd).mpr fun hdiv ↦
      hne ((Nat.dvd_prime_two_le (hs q hq).1 (hs p hp).1.two_le).mp hdiv)
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset r id s hs0 hsp
  refine ⟨k, ?_⟩
  rw [Int.gcd_eq_natAbs, ← Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hf, hab⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hp_mem : p ∈ s := Nat.mem_primeFactors.mpr ⟨hp, hab, by simpa using mul_ne_zero ha hb⟩
  have hmod : bridgePoly a b c d k ≡ bridgePoly a b c d (r p) [ZMOD (p : ℤ)] :=
    bridge_mod (Int.natCast_modEq_iff.mpr (hk p hp_mem))
  exact hr' p hp_mem (hmod.dvd_iff.mp (cast_dvd hf))

private lemma square_of_coprime_product {m n r : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (he : m * n = r ^ 2) : ∃ s : ℕ, m = s ^ 2 := by
  have hfact := congrArg Nat.factorization he
  rw [Nat.factorization_mul hm hn, Nat.factorization_pow] at hfact
  have heven (p : ℕ) (hp : p ∈ m.factorization.support) :
      m.factorization p = 2 * (r.factorization p) := by
    have hpm := Nat.mem_primeFactors.mp (by simpa using hp : p ∈ m.primeFactors)
    have hpn : ¬p ∣ n := fun hd ↦
      Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpm.1, hpm.2.1, hd⟩ hcop
    have hh := congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfact
    simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hpn, add_zero] using hh
  refine ⟨∏ p ∈ m.factorization.support, p ^ (r.factorization p), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  apply Finset.prod_congr rfl
  intro p hp
  change p ^ (m.factorization p) = (p ^ (r.factorization p)) ^ 2
  rw [heven p hp, mul_comm 2, pow_mul]

private lemma square_mod_eight (n : ℤ) : (n ^ 2) % 8 = 0 ∨ (n ^ 2) % 8 = 1 ∨ (n ^ 2) % 8 = 4 := by
  rw [pow_two, Int.mul_emod]
  have hlo : 0 ≤ n % 8 := Int.emod_nonneg _ (by decide)
  have hhi : n % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  interval_cases n % 8 <;> decide

-- If the first curvature is zero, the determinant is a square product of the two odd curvatures.
-- They are coprime by primitivity, so their absolute values are squares, contrary to their residue.
private lemma zero_impossible_of_odd_pair {b c d : ℤ} (h : descartes 0 b c d)
    (hr : SeedResidues 0 b c d) (hprim : primitive 0 b c d)
    (hb : b % 8 = 5) (hc : c % 8 = 5) : False := by
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  let t := middle 0 b c d
  have hprod : b * c = t ^ 2 := by
    have he := determinant h hr
    simp only [zero_add, zero_pow (by decide : 2 ≠ 0)] at he
    change b * c - t ^ 2 = 0 at he
    omega
  have hcop : b.natAbs.Coprime c.natAbs := by
    by_contra hnc
    obtain ⟨p, hp, hpb, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have cast_dvd {z : ℤ} (hh : p ∣ z.natAbs) : (p : ℤ) ∣ z :=
      Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using hh)
    have hpz : Prime (p : ℤ) := by simpa [Int.prime_iff_natAbs_prime] using hp
    have hpt : (p : ℤ) ∣ t := by
      apply hpz.dvd_of_dvd_pow (n := 2)
      rw [← hprod]
      exact dvd_mul_of_dvd_left (cast_dvd hpb) c
    have hd : (p : ℤ) ∣ d := by
      have htwo : 2 * t = b + c - d := by simpa only [zero_add] using twice_middle hr
      have hd' : d = b + c - 2 * t := by omega
      rw [hd']
      exact Int.dvd_sub (Int.dvd_add (cast_dvd hpb) (cast_dvd hpc)) (dvd_mul_of_dvd_right hpt 2)
    exact prime_not_dvd_one hp (hprim _ (dvd_zero _) (cast_dvd hpb) (cast_dvd hpc) hd)
  have he : b.natAbs * c.natAbs = t.natAbs ^ 2 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hprod
  obtain ⟨s, hs⟩ := square_of_coprime_product (by simpa using hb0) (by simpa using hc0) hcop he
  have hm := natAbs_mod_eight hb
  rw [hs] at hm
  have hsq := square_mod_eight (s : ℤ)
  norm_cast at hsq
  split at hm <;> omega

private lemma first_ne_zero {a b c d : ℤ} (h : descartes a b c d)
    (hr : SeedResidues a b c d) (hprim : primitive a b c d) : a ≠ 0 := by
  rintro rfl
  obtain ⟨ha, hb, hc, hd, ho⟩ := hr
  unfold seedResidue at hb hc hd
  rcases hb with hb | hb <;> rcases hc with hc | hc <;> rcases hd with hd | hd
  all_goals try omega
  · apply zero_impossible_of_odd_pair (b := c) (c := d) (d := b) _ _ _ hc hd
    · unfold descartes at h ⊢
      linear_combination h
    · exact ⟨ha, Or.inr hc, Or.inr hd, Or.inl hb, by omega⟩
    · exact fun p hp0 hpc hpd hpb ↦ hprim p hp0 hpb hpc hpd
  · apply zero_impossible_of_odd_pair (b := b) (c := d) (d := c) _ _ _ hb hd
    · unfold descartes at h ⊢
      linear_combination h
    · exact ⟨ha, Or.inr hb, Or.inr hd, Or.inl hc, by omega⟩
    · exact fun p hp0 hpb hpd hpc ↦ hprim p hp0 hpb hpc hpd
  · exact zero_impossible_of_odd_pair h ⟨ha, Or.inr hb, Or.inr hc, Or.inl hd, ho⟩ hprim hb hc

-- The form associated to the first entry. Its determinant is a², so over ℤ/aℤ
-- the product of two represented values is a square (the Gram determinant vanishes).
private def tangentForm (a b c d x y : ℤ) : ℤ :=
  (a + b) * x ^ 2 + 2 * middle a b c d * x * y + (a + c) * y ^ 2

private lemma form_char_eq {a b c d x y u v : ℤ} (h : descartes a b c d)
    (hr : SeedResidues a b c d) (hx : (tangentForm a b c d x y).gcd a = 1)
    (hu : (tangentForm a b c d u v).gcd a = 1) :
    edgeChar a (tangentForm a b c d x y) = edgeChar a (tangentForm a b c d u v) := by
  let g := (a + b) * x * u + middle a b c d * (x * v + y * u) + (a + c) * y * v
  have hmod : tangentForm a b c d x y * tangentForm a b c d u v ≡ g ^ 2 [ZMOD a] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-a * (x * v - y * u) ^ 2, ?_⟩
    dsimp only [g, tangentForm]
    linear_combination -(x * v - y * u) ^ 2 * determinant h hr
  unfold edgeChar
  rw [jacobi_eq_of_prod_mod_sq hx hu hmod]

private def negativeClass (a b c d : ℤ) : Prop :=
  ∃ x y : ℤ, (tangentForm a b c d x y).gcd a = 1 ∧
    edgeChar a (tangentForm a b c d x y) = -1

private lemma negativeClass_congr {a b c d b' c' d' : ℤ}
    (h : ∀ x y, ∃ u v, tangentForm a b' c' d' u v = tangentForm a b c d x y) :
    negativeClass a b c d → negativeClass a b' c' d' := by
  rintro ⟨x, y, hx, hy⟩
  obtain ⟨u, v, huv⟩ := h x y
  exact ⟨u, v, huv ▸ hx, huv ▸ hy⟩

private lemma negativeClass_swap_middle {a b c d : ℤ} :
    negativeClass a b c d ↔ negativeClass a c b d := by
  constructor <;> apply negativeClass_congr <;> intro x y <;> refine ⟨y, x, ?_⟩ <;>
    simp only [tangentForm, middle, add_right_comm a] <;> ring

private lemma negativeClass_swap_last {a b c d : ℤ} (hr : SeedResidues a b c d) :
    negativeClass a b c d ↔ negativeClass a b d c := by
  have hr' : SeedResidues a b d c :=
    ⟨hr.first, hr.second, hr.fourth, hr.third, by have := hr.two_odd; omega⟩
  have h := twice_middle hr
  have h' := twice_middle hr'
  constructor <;> apply negativeClass_congr <;> intro x y <;> refine ⟨x + y, -y, ?_⟩ <;>
    simp only [tangentForm, h, h'] <;> ring

private lemma negativeClass_replace_last {a b c d : ℤ} (hr : SeedResidues a b c d) :
    negativeClass a b c d ↔ negativeClass a b c (2 * (a + b + c) - d) := by
  have h := twice_middle hr
  have h' := twice_middle (seedResidues_replace hr)
  have he : middle a b c (2 * (a + b + c) - d) = -middle a b c d := by omega
  constructor <;> apply negativeClass_congr <;> intro x y <;> refine ⟨x, -y, ?_⟩ <;>
    simp only [tangentForm, he] <;> ring

private lemma bridge_descartes {a b c d : ℤ} (h : descartes a b c d) (k : ℕ) :
    descartes a b (bridgePoly a b c d k) (bridgePoly a b c d ((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa [bridge_zero, bridge_one] using h
  | succ k ih =>
    simp only [Nat.cast_succ, add_assoc, one_add_one_eq_two, bridge_add_two]
    unfold descartes at ih ⊢
    linear_combination ih

private lemma tangentForm_bridge {a b c d : ℤ} (hr : SeedResidues a b c d) (x : ℤ) :
    tangentForm a b c d x (-1) = a + bridgePoly a b c d x := by
  unfold tangentForm bridgePoly
  linear_combination -x * twice_middle hr

private lemma bridge_pair_pos {a b c d : ℤ} (h : descartes a b c d)
    (hr : SeedResidues a b c d) (hab : 0 < a + b) (ha : a ≠ 0) (x : ℤ) :
    0 < a + bridgePoly a b c d x := by
  have he : (a + b) * (a + bridgePoly a b c d x) =
      ((a + b) * x - middle a b c d) ^ 2 + a ^ 2 := by
    unfold bridgePoly
    linear_combination determinant h hr + (a + b) * x * twice_middle hr
  have hprod : 0 < (a + b) * (a + bridgePoly a b c d x) := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ha)
  exact pos_of_mul_pos_right hprod hab.le

private lemma odd_endpoint {a b : ℤ} (ha : seedResidue a) (hb : seedResidue b)
    (hc : a.gcd b = 1) : a % 8 = 5 ∨ b % 8 = 5 := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · have hda : (2 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero (by omega)
      have hdb : (2 : ℤ) ∣ b := Int.dvd_of_emod_eq_zero (by omega)
      exact False.elim ((by decide : ¬ (2 : ℤ) ∣ 1) (Int.gcd_eq_one_iff.mp hc _ hda hdb))
    · exact Or.inr hb
  · exact Or.inl ha

private lemma residue_natAbs_ne_one {a : ℤ} (ha : seedResidue a) : a.natAbs ≠ 1 := by
  intro h
  rcases Int.natAbs_eq_iff.mp h with h | h <;> subst a <;> rcases ha with ha | ha <;> omega

private lemma negativeClass_swap_first_imp {a b c d : ℤ} (h : descartes a b c d)
    (hs : 0 < a + b + c + d) (hr : SeedResidues a b c d) (hp : primitive a b c d) :
    negativeClass a b c d → negativeClass b a c d := by
  rintro ⟨x, y, hxy, hneg⟩
  have h' : descartes b a c d := by unfold descartes at h ⊢; linear_combination h
  have hr' : SeedResidues b a c d :=
    ⟨hr.second, hr.first, hr.third, hr.fourth, by have := hr.two_odd; omega⟩
  have hp' : primitive b a c d := fun p hb ha ↦ hp p ha hb
  have ha := first_ne_zero h hr hp
  have hb := first_ne_zero h' hr' hp'
  have hab := pair_sum_pos h hs ha
  obtain ⟨k, hk⟩ := exists_bridge hr hp ha hb
  let f := bridgePoly a b c d k
  let g := bridgePoly a b c d ((k : ℤ) + 1)
  have hswap (z : ℤ) : bridgePoly b a c d z = bridgePoly a b c d z := by
    simp only [bridgePoly, add_comm b a]
  have hrfg : SeedResidues a b f g := bridge_residues hr k
  have hdfg : descartes f a b g := by
    have hd := bridge_descartes h k
    change descartes a b f g at hd
    unfold descartes at hd ⊢
    linear_combination hd
  have hrfg' : SeedResidues f a b g :=
    ⟨hrfg.third, hrfg.first, hrfg.second, hrfg.fourth, by have := hrfg.two_odd; omega⟩
  have hfa : f.gcd a = 1 := Int.gcd_eq_one_iff.mpr fun p hf ha' ↦
    Int.gcd_eq_one_iff.mp hk p hf (dvd_mul_of_dvd_left ha' b)
  have hfb : f.gcd b = 1 := Int.gcd_eq_one_iff.mpr fun p hf hb' ↦
    Int.gcd_eq_one_iff.mp hk p hf (dvd_mul_of_dvd_right hb' a)
  have hf : f ≠ 0 := by
    intro h0
    rw [h0, Int.gcd_zero_left] at hfa
    exact residue_natAbs_ne_one hr.first hfa
  have hfa_sum := bridge_pair_pos h hr hab ha (k : ℤ)
  have hfb_sum := bridge_pair_pos h' hr' (by omega) hb (k : ℤ)
  rw [hswap] at hfb_sum
  have eq_a : tangentForm a b c d k (-1) = a + f := tangentForm_bridge hr k
  have eq_b : tangentForm b a c d k (-1) = b + f := by rw [tangentForm_bridge hr', hswap]
  have mod_a : a + f ≡ f [ZMOD a] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have mod_b : b + f ≡ f [ZMOD b] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have mod_fa : f + a ≡ a [ZMOD f] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have mod_fb : f + b ≡ b [ZMOD f] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have haEval : (tangentForm a b c d k (-1)).gcd a = 1 := by
    rw [eq_a, gcd_mod mod_a, hfa]
  have hbEval : (tangentForm b a c d k (-1)).gcd b = 1 := by
    rw [eq_b, gcd_mod mod_b, hfb]
  have hfLeft : (tangentForm f a b g 1 0).gcd f = 1 := by
    simpa [tangentForm, gcd_mod mod_fa, Int.gcd_comm a f] using hfa
  have hfRight : (tangentForm f a b g 0 1).gcd f = 1 := by
    simpa [tangentForm, gcd_mod mod_fb, Int.gcd_comm b f] using hfb
  have h_mid := form_char_eq hdfg hrfg' hfLeft hfRight
  simp only [tangentForm, one_pow, zero_pow (by decide : 2 ≠ 0), mul_one,
    mul_zero, zero_add, add_zero, edgeChar_mod mod_fa, edgeChar_mod mod_fb] at h_mid
  have haChar := form_char_eq h hr hxy haEval
  rw [hneg, eq_a, edgeChar_mod mod_a] at haChar
  refine ⟨k, -1, hbEval, ?_⟩
  rw [eq_b, edgeChar_mod mod_b]
  calc
    edgeChar b f = edgeChar f b := edgeChar_reciprocity hb hf
      ((odd_endpoint hrfg.third hr.second hfb).symm) hfb_sum.le
    _ = edgeChar f a := h_mid.symm
    _ = edgeChar a f := edgeChar_reciprocity hf ha
      (odd_endpoint hrfg.third hr.first hfa) (by omega : 0 ≤ f + a)
    _ = -1 := haChar.symm

private structure Obstructed (a b c d : ℤ) : Prop where
  eqn : descartes a b c d
  pos : 0 < a + b + c + d
  prim : primitive a b c d
  res : SeedResidues a b c d
  negClass : negativeClass a b c d

private lemma Obstructed.swap01 {a b c d : ℤ} (h : Obstructed a b c d) : Obstructed b a c d := by
  refine ⟨?_, by have := h.pos; omega, fun p hb ha ↦ h.prim p ha hb,
    ⟨h.res.second, h.res.first, h.res.third, h.res.fourth, by have := h.res.two_odd; omega⟩,
    negativeClass_swap_first_imp h.eqn h.pos h.res h.prim h.negClass⟩
  have he := h.eqn
  unfold descartes at he ⊢
  linear_combination he

private lemma Obstructed.swap12 {a b c d : ℤ} (h : Obstructed a b c d) : Obstructed a c b d := by
  refine ⟨?_, by have := h.pos; omega, fun p ha hc hb ↦ h.prim p ha hb hc,
    ⟨h.res.first, h.res.third, h.res.second, h.res.fourth, by have := h.res.two_odd; omega⟩,
    negativeClass_swap_middle.mp h.negClass⟩
  have he := h.eqn
  unfold descartes at he ⊢
  linear_combination he

private lemma Obstructed.swap23 {a b c d : ℤ} (h : Obstructed a b c d) : Obstructed a b d c := by
  refine ⟨?_, by have := h.pos; omega, fun p ha hb hd hc ↦ h.prim p ha hb hc hd,
    ⟨h.res.first, h.res.second, h.res.fourth, h.res.third, by have := h.res.two_odd; omega⟩,
    (negativeClass_swap_last h.res).mp h.negClass⟩
  have he := h.eqn
  unfold descartes at he ⊢
  linear_combination he

private lemma Obstructed.flipLast {a b c d : ℤ} (h : Obstructed a b c d) :
    Obstructed a b c (2 * (a + b + c) - d) := by
  refine ⟨?_, ?_, ?_, seedResidues_replace h.res, (negativeClass_replace_last h.res).mp h.negClass⟩
  · have he := h.eqn
    unfold descartes at he ⊢
    linear_combination he
  · have he := h.eqn
    unfold descartes at he
    have hs := h.pos
    by_contra! hn
    have hdiff : 0 ≤ 4 * d - 3 * (a + b + c + d) := by omega
    have hsum : 0 ≤ 4 * d + 3 * (a + b + c + d) := by omega
    nlinarith [mul_nonneg hdiff hsum, sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_pos_of_pos hs]
  · intro p ha hb hc hd
    have hdiv : p ∣ 2 * (a + b + c) := dvd_mul_of_dvd_right (Int.dvd_add (Int.dvd_add ha hb) hc) _
    apply h.prim p ha hb hc
    convert Int.dvd_sub hdiv hd using 1
    ring

private def obstructedVec (v : Fin 4 → ℤ) : Prop := Obstructed (v 0) (v 1) (v 2) (v 3)

private lemma obstructedVec_swap (v : Fin 4 → ℤ) (h : obstructedVec v) (i j : Fin 4) :
    obstructedVec (v ∘ Equiv.swap i j) := by
  have hv : Obstructed (v 0) (v 1) (v 2) (v 3) := h
  fin_cases i <;> fin_cases j <;>
    simp only [obstructedVec, Function.comp_apply, Equiv.swap_apply_def, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ite_true, ite_false] <;>
    first
    | exact hv
    | exact hv.swap01
    | exact hv.swap12
    | exact hv.swap23
    | exact hv.swap01.swap12.swap01
    | exact hv.swap12.swap23.swap12
    | exact hv.swap01.swap12.swap23.swap12.swap01

private lemma obstructedVec_perm (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (h : obstructedVec v) :
    obstructedVec (v ∘ σ) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => exact h
  | swap_mul f i j _ ih => exact ih _ (obstructedVec_swap v h i j)

private lemma obstructedVec_gen {X : GL (Fin 4) ℤ} (hX : X ∈ ({S₁, S₂, S₃, S₄} : Set _))
    (v : Fin 4 → ℤ) (h : obstructedVec v) : obstructedVec (X • v) := by
  have hv : Obstructed (v 0) (v 1) (v 2) (v 3) := h
  rcases hX with rfl | rfl | rfl | rfl
  · simpa [obstructedVec, mulVec_eq_sum, Fin.sum_univ_four, mul_add, sub_eq_add_neg,
      mul_comm, add_comm, add_left_comm, add_assoc] using
      hv.swap01.swap12.swap23.flipLast.swap23.swap12.swap01
  · simpa [obstructedVec, mulVec_eq_sum, Fin.sum_univ_four, mul_add, sub_eq_add_neg,
      mul_comm, add_comm, add_left_comm, add_assoc] using hv.swap12.swap23.flipLast.swap23.swap12
  · simpa [obstructedVec, mulVec_eq_sum, Fin.sum_univ_four, mul_add, sub_eq_add_neg,
      mul_comm, add_comm, add_left_comm, add_assoc] using hv.swap23.flipLast.swap23
  · simpa [obstructedVec, mulVec_eq_sum, Fin.sum_univ_four, mul_add, sub_eq_add_neg,
      mul_comm, add_comm, add_left_comm, add_assoc] using hv.flipLast

open scoped Pointwise

private lemma transformation_preserves_obstructed (X : GL (Fin 4) ℤ) (hX : X ∈ TransformationGroup)
    {v : Fin 4 → ℤ} (hv : obstructedVec v) : obstructedVec (X • v) := by
  let V : Set (Fin 4 → ℤ) := {v | obstructedVec v}
  have hle : TransformationGroup ≤ MulAction.stabilizer (GL (Fin 4) ℤ) V := by
    unfold TransformationGroup
    apply sup_le
    · rw [ApollonianGroup, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.Subset.antisymm_iff,
        Set.subset_smul_set_iff]
      have hginv : g⁻¹ ∈ ({S₁, S₂, S₃, S₄} : Set (GL (Fin 4) ℤ)) := by
        rcases hg with rfl | rfl | rfl | rfl <;> simp
      exact ⟨Set.smul_set_subset_iff.mpr (obstructedVec_gen hg),
        Set.smul_set_subset_iff.mpr (obstructedVec_gen hginv)⟩
    · rw [MulAction.le_stabilizer_iff_smul_le]
      simp only [Set.smul_set_subset_iff]
      rintro g ⟨σ, rfl⟩ w hw
      simpa only [V, Set.mem_ofPred_eq, GeneralLinearGroup.smul_def, MonoidHom.coe_toHomUnits,
        permMatrixHom_apply, permMatrix_mulVec, Equiv.Perm.coe_inv] using
        obstructedVec_perm σ⁻¹ w hw
  exact (Set.smul_set_subset_iff.mp ((MulAction.le_stabilizer_iff_smul_le V _).mp hle X hX)) hv

private lemma twoPartSign_odd {n : ℕ} (h : n % 2 = 1) : twoPartSign n = 1 := by
  rw [twoPartSign, ite_eq_right (by omega)]

private lemma twoPartSign_double {n : ℕ} (h : 0 < n) : twoPartSign (2 * n) = -twoPartSign n := by
  rw [twoPartSign, ite_eq_left (by omega), show 2 * n / 2 = n by omega]

private lemma twoPartSign_square (n : ℕ) : twoPartSign (n ^ 2) = 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases eq_zero_or_pos n with rfl | hn
    · rw [show (0 : ℕ) ^ 2 = 0 by decide, twoPartSign, ite_eq_right (by decide)]
    · by_cases h : n % 2 = 0
      · let m := n / 2
        have hm : 0 < m := by dsimp [m]; omega
        have hmlt : m < n := by dsimp [m]; omega
        have he : n ^ 2 = 2 * (2 * m ^ 2) := by
          have hnm : n = 2 * m := by dsimp [m]; omega
          rw [hnm]
          ring
        rw [he, twoPartSign_double (by positivity), twoPartSign_double (by positivity),
          neg_neg, ih m hmlt]
      · apply twoPartSign_odd
        rw [pow_two, Nat.mul_mod]
        have ho : n % 2 = 1 := by omega
        rw [ho]

private lemma Obstructed.first_not_square {a b c d : ℤ} (h : Obstructed a b c d) (n : ℤ) :
    a ≠ n ^ 2 := by
  intro hsq
  subst a
  rcases eq_or_ne n 0 with rfl | _
  · exact first_ne_zero h.eqn h.res h.prim (by simp)
  obtain ⟨x, y, hcop, hneg⟩ := h.negClass
  let z := tangentForm (n ^ 2) b c d x y
  have hcop' : z.gcd (n.natAbs : ℤ) = 1 := by
    apply Int.gcd_eq_one_iff.mpr
    intro p hpz hpn
    have hpn' : p ∣ n := Int.natAbs_dvd_natAbs.mp (Int.dvd_natCast.mp hpn)
    exact Int.gcd_eq_one_iff.mp hcop p hpz (dvd_pow hpn' (by decide))
  change edgeChar (n ^ 2) z = -1 at hneg
  unfold edgeChar at hneg
  rw [Int.natAbs_pow, twoPartSign_square, one_mul, jacobiSym.pow_right,
    jacobiSym.sq_one hcop'] at hneg
  norm_num at hneg

private lemma obstruction_for_seed : obstructedVec ![-3, 5, 8, 8] := by
  change Obstructed (-3) 5 8 8
  apply Obstructed.swap01
  refine ⟨by unfold descartes; decide, by decide, ?_, ?_, ?_⟩
  · intro p hp5 hp3 _ _
    convert Int.dvd_add (dvd_mul_of_dvd_right hp5 2) (dvd_mul_of_dvd_right hp3 3) using 1
    norm_num
  · refine ⟨?_, ?_, ?_, ?_, by decide⟩ <;> unfold seedResidue <;> decide
  · refine ⟨0, 1, by decide, ?_⟩
    change twoPartSign 5 * J(13 | 5) = -1
    rw [twoPartSign_odd (by decide : (5 : ℕ) % 2 = 1), one_mul,
      jacobiSym.mod_left' (show (13 : ℤ) % 5 = 8 % 5 by decide),
      show (8 : ℤ) = 2 ^ 3 by decide, jacobiSym.pow_left,
      jacobiSym.at_two (by decide : Odd (5 : ℕ))]
    decide

/--
**A packing with no square curvatures.** Let $\mathcal{A}$ be the primitive Apollonian circle
packing generated by the integral primitive Descartes quadruple $(-3, 5, 8, 8)$. For every
integer $n$, $n^2$ does not belong to the curvature set of $\mathcal{A}$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
theorem theorem_1_6 : ∀ n, n ^ 2 ∉ curvatureSet ⟦⟨![-3, 5, 8, 8], by decide⟩⟧ := by
  intro n hn
  simp only [curvatureSet, Set.mem_iUnion, Set.mem_range] at hn
  obtain ⟨v, hv, i, hi⟩ := hn
  rw [MulAction.orbitRel.Quotient.orbit_mk] at hv
  obtain ⟨X, hX⟩ := hv
  have h := transformation_preserves_obstructed X.1 X.2 obstruction_for_seed
  have he : X.1 • (![-3, 5, 8, 8] : Fin 4 → ℤ) = v.1 := congrArg Subtype.val hX
  rw [he] at h
  have hp : Obstructed ((v.1 ∘ Equiv.swap 0 i) 0) ((v.1 ∘ Equiv.swap 0 i) 1)
      ((v.1 ∘ Equiv.swap 0 i) 2) ((v.1 ∘ Equiv.swap 0 i) 3) := obstructedVec_swap v.1 h 0 i
  exact hp.first_not_square n (by simpa using hi)

end LocalGlobalApollonianCirclePackings

end MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
