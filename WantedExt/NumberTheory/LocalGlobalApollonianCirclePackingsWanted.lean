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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.LocalGlobalApollonianCirclePackings` — annals_local_global_apollonian_circle_packings (manifest `manifests/problems/annals_local_global_apollonian_circle_packings.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted` namespace. Mathematical
statements are unchanged. Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

namespace MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
/-!
# Main Statements from The local-global conjecture for Apollonian circle packings is false

We formalise the statements of the main results from S. Haag, C. Kertzer, J. Rickards, and
K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`,
Annals of Math, 200 (2) 2024.
-/

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

/--
**A packing with no square curvatures.** Let $\mathcal{A}$ be the primitive Apollonian circle
packing generated by the integral primitive Descartes quadruple $(-3, 5, 8, 8)$. For every
integer $n$, $n^2$ does not belong to the curvature set of $\mathcal{A}$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
public theorem_wanted theorem_1_6 : ∀ n, n ^ 2 ∉ curvatureSet ⟦⟨![-3, 5, 8, 8], by decide⟩⟧

/-- **Missing curvature set.** Let $A$ be a primitive Apollonian circle packing. The missing
curvature set of $A$ is the set of positive integers $n$ that do not lie in the curvature set
of $A$ but are congruent modulo $24$ to some element of the curvature set of $A$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for
Apollonian circle packings is false`, Annals of Math, 200 (2) 2024, start of Section 1.2. -/
def missingCurvatureSet (A : PrimitiveApollonianCirclePacking) : Set ℤ :=
  {n | n > 0 ∧ n ∉ curvatureSet A ∧ ∃ k ∈ curvatureSet A, k ≡ n [ZMOD 24]}

/-- **Number of missing curvatures.** For a primitive Apollonian circle packing $A$ and a real
number $N$, the number of missing curvatures of $A$ up to $N$ is the number of elements $n$ of
the missing curvature set of $A$ with $n \le N$, regarded as a real number. -/
noncomputable def missingCurvatures (A : PrimitiveApollonianCirclePacking) (N : ℝ) : ℝ :=
  (missingCurvatureSet A ∩ {x | x ≤ N}).ncard

/--
**Infinitely many packings with many missing curvatures.** For a primitive Apollonian circle
packing $\mathcal{A}$ and a real number $N$, let $M_{\mathcal{A}}(N)$ be the number of missing
curvatures of $\mathcal{A}$ up to $N$. There are infinitely many primitive Apollonian circle
packings $\mathcal{A}$ such that $\sqrt{N} = O(M_{\mathcal{A}}(N))$ as $N$ tends to infinity.
In other words, for these packings the number of missing curvatures up to $N$ is
$\Omega(\sqrt{N})$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
public theorem_wanted theorem_1_3 : {A : PrimitiveApollonianCirclePacking |
    Real.sqrt =O[Filter.atTop] missingCurvatures A}.Infinite

end LocalGlobalApollonianCirclePackings

end MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
