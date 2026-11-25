/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/RepresentationTheory/FrobeniusDeterminant.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `frobenius_group_determinant`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/frobenius_group_determinant.toml`, rev 1, submitter Kim Morrison, status
archived): the definitions `groupMatrix` and `groupDeterminant` and the statement of
`frobenius_group_determinant`, with the docstrings they had in the former wanted module
`WantedExt/GroupTheory/FrobeniusDeterminantWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.GroupTheory.FrobeniusDeterminantWanted` namespace. Mathematical statements are
unchanged. Source: Knill, *Some fundamental theorems in mathematics*, §171. Later change (ATLAS,
2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/GroupTheory/FrobeniusDeterminantWanted.lean` to this `MathlibExt` module with unchanged
names, statements and docstrings, and the import of `Batteries.Util.ProofWanted` was replaced by
the Mathlib imports the proof uses.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`frobenius_group_determinant`, the private definitions and lemmas it uses, and the module
documentation.
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import MathlibExt.GroupTheory.ClassFunction

/-!
# Frobenius determinant theorem (Dedekind's group determinant)

`frobenius_group_determinant`: the group determinant `Θ(G) = det(A)` of the
group matrix `A_{gh} = x_{gh}` factors into irreducible polynomials, each to the
power of its own total degree, with the factors pairwise non-associated and
their number equal to the number of conjugacy classes of `G`. Trusted helpers
`groupMatrix`, `groupDeterminant` (non-holes). Category-(b) candidate from §171
of the Knill survey.

## Proof outline

Write `R = ℂ[x_g : g ∈ G]`. By Maschke's theorem and the Wedderburn–Artin theorem over the
algebraically closed field `ℂ`, there is an algebra isomorphism
`φ : ℂ[G] ≃ Π i : Fin n, Mat_{d i}(ℂ)` with every `d i ≠ 0`; write `ρ_i(g)` for the `i`-th
component of `φ g`. Let `Q_i = ∑_g x_g ρ_i(g)`, a `d i × d i` matrix of linear forms, and
`p_i = det Q_i`.

* The matrix `A_{gh} = x_{gh}` is the matrix `L_{gh} = x_{gh⁻¹}` of left multiplication by
  `∑_g x_g g` on `R[G]`, with its columns permuted by `h ↦ h⁻¹`; so `det A = ± det L`.
* Transporting `L` along `φ` gives the block diagonal matrix with blocks `Q_i ⊗ 1`, the matrix of
  left multiplication by `Q_i` on `d i × d i` matrices; so `det L = ∏ i, p_i ^ d i`. The sign is a
  `d i`-th power in `ℂ`, so it is absorbed into one factor.
* The coefficients of the linear forms `(Q_i)_{ab}`, for all `i, a, b`, are the coordinates of
  the linear isomorphism `φ`, so substituting them for independent variables `y_{iab}` is an
  algebra automorphism of the polynomial ring. It maps the generic determinant `det (y_{iab})_{ab}`
  to `p_i`, and the generic determinant is irreducible (by induction on its size, expanding along
  the first row), so each `p_i` is irreducible. Each `p_i` is homogeneous of degree `d i`.
* Evaluating at the coordinates of `φ⁻¹ c`, where `c` has the zero block at `j` and identity
  blocks elsewhere, gives `p_j ↦ 0` and `p_i ↦ 1` for `i ≠ j`, so `p_i` and `p_j` are not
  associated.
* The centre of `ℂ[G]` consists of the class functions, so its dimension is the number of
  conjugacy classes, while the centre of `Π i, Mat_{d i}(ℂ)` consists of the families of scalar
  matrices and has dimension `n`.

## References

* Knill, *Some fundamental theorems in mathematics*, §171. This is the source cited by problem
  `frobenius_group_determinant` of the lean-eval benchmark (leanprover/lean-eval), from which the
  definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusDeterminantWanted
namespace RepresentationTheory.FrobeniusDeterminant

open MvPolynomial Matrix

/-- **Group matrix.** For a finite group $G$, the group matrix of Dedekind and Frobenius is the
$G \times G$ matrix over the polynomial ring $\mathbb{C}[x_g : g \in G]$ whose entry at $(g, h)$ is
the variable $x_{gh}$. -/
noncomputable def groupMatrix (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Matrix G G (MvPolynomial G ℂ) :=
  fun g h => MvPolynomial.X (g * h)

/-- **Group determinant.** For a finite group $G$, the group determinant $\Theta(G)$ is the
determinant of the group matrix of $G$, the $G \times G$ matrix over $\mathbb{C}[x_g : g \in G]$
whose entry at $(g, h)$ is the variable $x_{gh}$; it is a polynomial in these variables. -/
noncomputable def groupDeterminant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    MvPolynomial G ℂ :=
  (groupMatrix G).det

/-! ### Irreducibility of the generic determinant -/

/-- Renaming the variables along an injective map preserves irreducibility. -/
private theorem irreducible_rename {σ τ K : Type*} [Field K] {e : σ → τ}
    (he : Function.Injective e) {p : MvPolynomial σ K} (hp : Irreducible p) :
    Irreducible (rename e p) := by
  classical
  have h1 : rename e p =
      rename ((↑) : Set.range e → τ) (renameEquiv K (Equiv.ofInjective e he) p) := by
    rw [renameEquiv_apply, rename_rename]
    rfl
  rw [h1]
  refine ((MvPolynomial.prime_rename_iff (Set.range e)).2 ?_).irreducible
  exact (MulEquiv.prime_iff (renameEquiv K (Equiv.ofInjective e he))).2 hp.prime

/-- A variable is irreducible. -/
private theorem irreducible_X_of_field {σ K : Type*} [Field K] (i : σ) :
    Irreducible (X i : MvPolynomial σ K) := by
  simpa using irreducible_mul_X_add (1 : MvPolynomial σ K) 0 i one_ne_zero (by simp) (by simp)
    isRelPrime_one_left

/-- A minor of the generic matrix omitting the first row is a renamed generic determinant. -/
private theorem det_submatrix_succ_mvPolynomialX (K : Type*) [Field K] (m : ℕ)
    (c : Fin (m + 1) → Fin (m + 2)) :
    ((mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) K).submatrix Fin.succ c).det =
      rename (Prod.map Fin.succ c) (mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) K).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp [mvPolynomialX_apply]

/-- The generic determinant of size `m + 1` is irreducible. -/
private theorem irreducible_det_mvPolynomialX_succ (K : Type*) [Field K] (m : ℕ) :
    Irreducible (mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) K).det := by
  induction m with
  | zero =>
    rw [det_fin_one, mvPolynomialX_apply]
    exact irreducible_X_of_field _
  | succ m ih =>
    classical
    set N := mvPolynomialX (Fin (m + 2)) (Fin (m + 2)) K with hN
    set D := (mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) K).det with hD
    have hminor := det_submatrix_succ_mvPolynomialX K m
    -- expand along the first row: `det N = f * X (0, 0) + g`
    set f := rename (Prod.map Fin.succ Fin.succ) D with hf
    set g := ∑ j : Fin (m + 1), (-1) ^ ((j.succ : Fin (m + 2)) : ℕ) * X (0, j.succ) *
      rename (Prod.map Fin.succ (j.succ.succAbove)) D with hg
    have hdet : N.det = f * X (0, 0) + g := by
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hminor, hN,
        mvPolynomialX_apply]
      rw [mul_comm]
    have hf_irr : Irreducible f := irreducible_rename
      (Prod.map_injective.2 ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih
    rw [hdet]
    refine irreducible_mul_X_add f g (0, 0) hf_irr.ne_zero ?_ ?_ ?_
    · intro hmem
      obtain ⟨v, -, hv⟩ := Finset.mem_image.1 (vars_rename _ _ hmem)
      exact Fin.succ_ne_zero _ (congrArg Prod.fst hv)
    · intro hmem
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (vars_sum_subset _ _ hmem)
      rcases Finset.mem_union.1 (vars_mul _ _ hj) with h | h
      · rcases Finset.mem_union.1 (vars_mul _ _ h) with h' | h'
        · have := vars_pow (-1 : MvPolynomial (Fin (m + 2) × Fin (m + 2)) K) _ h'
          simp at this
        · rw [vars_X, Finset.mem_singleton] at h'
          exact Fin.succ_ne_zero _ (congrArg Prod.snd h').symm
      · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 (vars_rename _ _ h)
        exact Fin.succ_ne_zero _ (congrArg Prod.fst hv)
    · -- `f` does not divide `det N`: evaluate at the permutation matrix of `swap 0 1`
      refine hf_irr.isRelPrime_iff_not_dvd.2 fun hfg => ?_
      have hdvd : f ∣ N.det := hdet ▸ dvd_add (dvd_mul_right f _) hfg
      let s : Fin (m + 2) × Fin (m + 2) → K := fun v => (Equiv.swap 0 1).permMatrix K v.1 v.2
      have h1 : eval s N.det = -1 := by
        rw [hN, eval_det_mvPolynomialX]
        have : (Matrix.of fun i j : Fin (m + 2) => s (i, j)) =
            (Equiv.swap 0 1).permMatrix K := by
          ext i j; rfl
        rw [this, det_permutation, Equiv.Perm.sign_swap (by simp)]
        simp
      have h2 : eval s f = 0 := by
        rw [hf, hD, ← hminor, RingHom.map_det]
        refine det_eq_zero_of_row_eq_zero 0 fun j => ?_
        simp [s, mvPolynomialX_apply, PEquiv.toMatrix_apply, (Fin.succ_ne_zero j).symm]
      have := map_dvd (eval s) hdvd
      rw [h1, h2, zero_dvd_iff] at this
      simp at this

/-- The generic determinant of positive size is irreducible. -/
private theorem irreducible_det_mvPolynomialX (K : Type*) [Field K] {m : ℕ} (hm : m ≠ 0) :
    Irreducible (mvPolynomialX (Fin m) (Fin m) K).det := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact irreducible_det_mvPolynomialX_succ K k

/-! ### Linear changes of variables -/

section ChangeOfVariables

variable {α β K : Type*} [Field K] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype β] [DecidableEq β] in
/-- A linear map between coordinate spaces in terms of its values on the standard basis. -/
private theorem linearMap_apply_eq_sum (T : (α → K) →ₗ[K] (β → K)) (y : α → K) (b : β) :
    T y b = ∑ a, T (Pi.single a 1) b * y a := by
  rw [← LinearMap.toMatrix'_mulVec T y]
  simp [Matrix.mulVec, dotProduct]

omit [Fintype β] [DecidableEq β] in
/-- The substitution of variables given by a linear map: `X b ↦ ∑ a, T (e_a) b • X a`. -/
private noncomputable def linSubst (T : (α → K) →ₗ[K] (β → K)) :
    MvPolynomial β K →ₐ[K] MvPolynomial α K :=
  aeval fun b => ∑ a, C (T (Pi.single a 1) b) * X a

omit [Fintype β] [DecidableEq β] in
private theorem linSubst_X (T : (α → K) →ₗ[K] (β → K)) (b : β) :
    linSubst T (X b) = ∑ a, C (T (Pi.single a 1) b) * X a := by
  simp [linSubst]

omit [Fintype α] in
private theorem sum_symm_mul (T : (α → K) ≃ₗ[K] (β → K)) (a a' : α) :
    ∑ b, T.symm (Pi.single b 1) a * T (Pi.single a' 1) b = if a' = a then 1 else 0 := by
  have := linearMap_apply_eq_sum (T.symm : (β → K) →ₗ[K] (α → K)) (T (Pi.single a' 1)) a
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  rw [← this, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

private theorem linSubst_comp_linSubst_symm (T : (α → K) ≃ₗ[K] (β → K)) :
    (linSubst (T : (α → K) →ₗ[K] (β → K))).comp
      (linSubst (T.symm : (β → K) →ₗ[K] (α → K))) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [AlgHom.comp_apply, linSubst_X, map_sum, AlgHom.id_apply]
  simp only [map_mul, linSubst_X, algHom_C, algebraMap_eq, LinearEquiv.coe_coe]
  calc ∑ b, C (T.symm (Pi.single b 1) a) * ∑ a', C (T (Pi.single a' 1) b) * X a'
      = ∑ a', C (∑ b, T.symm (Pi.single b 1) a * T (Pi.single a' 1) b) * X a' := by
        simp only [Finset.mul_sum, map_sum, map_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => by ring
    _ = X a := by simp [sum_symm_mul]

/-- A linear change of variables, as an algebra isomorphism of polynomial rings. -/
private noncomputable def linSubstEquiv (T : (α → K) ≃ₗ[K] (β → K)) :
    MvPolynomial β K ≃ₐ[K] MvPolynomial α K :=
  AlgEquiv.ofAlgHom (linSubst (T : (α → K) →ₗ[K] (β → K)))
    (linSubst (T.symm : (β → K) →ₗ[K] (α → K)))
    (linSubst_comp_linSubst_symm T) (by simpa using linSubst_comp_linSubst_symm T.symm)

private theorem linSubstEquiv_apply (T : (α → K) ≃ₗ[K] (β → K)) (p : MvPolynomial β K) :
    linSubstEquiv T p = linSubst (T : (α → K) →ₗ[K] (β → K)) p := rfl

omit [Fintype β] in
/-- The matrices of a linear isomorphism and of its inverse are inverse to each other. -/
private theorem mul_matrix_symm (T : (α → K) ≃ₗ[K] (β → K)) {R : Type*} [CommRing R]
    [Algebra K R] :
    (Matrix.of fun b a => algebraMap K R (T (Pi.single a 1) b)) *
      (Matrix.of fun a b => algebraMap K R (T.symm (Pi.single b 1) a)) = 1 := by
  ext b b'
  rw [Matrix.mul_apply]
  simp only [of_apply, ← map_mul, ← map_sum]
  have := sum_symm_mul T.symm b b'
  simp only [LinearEquiv.symm_symm] at this
  rw [this, Matrix.one_apply]
  by_cases h : b = b'
  · subst h; simp
  · simp [h, Ne.symm h]

end ChangeOfVariables

/-! ### Determinants of homogeneous and of block diagonal matrices -/

/-- A determinant of linear forms is homogeneous of degree the size of the matrix. -/
private theorem isHomogeneous_det {ι σ K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (M : Matrix ι ι (MvPolynomial σ K)) (hM : ∀ a b, (M a b).IsHomogeneous 1) :
    M.det.IsHomogeneous (Fintype.card ι) := by
  rw [det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have h := IsHomogeneous.prod Finset.univ (fun i => M (τ i) i) (fun _ => 1)
    fun i _ => hM (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  have h' := (isHomogeneous_C σ ((Equiv.Perm.sign τ : ℤ) : K)).mul h
  rw [zero_add, map_intCast] at h'
  rw [Units.smul_def, zsmul_eq_mul]
  exact h'

/-- The determinant of a block diagonal matrix with nonempty blocks of possibly different
sizes. -/
private theorem det_blockDiagonal'_of_nonempty {o R : Type*} [CommRing R] [Fintype o]
    [DecidableEq o] [LinearOrder o] {m' : o → Type*} [∀ i, Fintype (m' i)]
    [∀ i, DecidableEq (m' i)] [∀ i, Nonempty (m' i)] (M : ∀ i, Matrix (m' i) (m' i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  rw [(blockTriangular_blockDiagonal' M).det]
  have himage : Finset.univ.image (Sigma.fst : (Σ i, m' i) → o) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun i => Finset.mem_image.2 ?_
    exact ⟨⟨i, Classical.arbitrary _⟩, Finset.mem_univ _, rfl⟩
  rw [himage]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← det_reindex_self (Equiv.sigmaSubtype i)]
  congr 1
  ext x y
  simp only [reindex_apply, submatrix_apply, toSquareBlock_def, of_apply]
  rw [show ((Equiv.sigmaSubtype i).symm x : Σ i, m' i) = ⟨i, x⟩ from rfl,
    show ((Equiv.sigmaSubtype i).symm y : Σ i, m' i) = ⟨i, y⟩ from rfl,
    blockDiagonal'_apply_eq]

/-! ### Centres -/

/-- The centre of the complex group algebra has dimension the number of conjugacy classes. -/
private theorem finrank_center_monoidAlgebra (G : Type*) [Group G] [Finite G] :
    Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = Nat.card (ConjClasses G) := by
  classical
  have := Fintype.ofFinite G
  let E : (G → ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ G :=
    (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm ≪≫ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  have hE : ∀ z : MonoidAlgebra ℂ G, ∀ g, E.symm z g = z.coeff g := fun z g => rfl
  have hsub : Subalgebra.toSubmodule (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) =
      (MathlibExt.GroupTheory.ClassFunctionWanted.classFunctions G ℂ).map
        (E : (G → ℂ) →ₗ[ℂ] MonoidAlgebra ℂ G) := by
    ext z
    rw [Submodule.mem_map_equiv, Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
    change _ ↔ ∀ g h : G, E.symm z (h * g * h⁻¹) = E.symm z g
    simp only [hE]
    constructor
    · intro hz g h
      have := congrArg (fun w => MonoidAlgebra.coeff w (h * g)) (hz (MonoidAlgebra.single h 1))
      simpa using this.symm
    · intro hz b
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | single h r =>
        ext x
        rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply]
        have := hz (h⁻¹ * x) h
        rw [show h * (h⁻¹ * x) * h⁻¹ = x * h⁻¹ by group] at this
        rw [← this, mul_comm]
  calc Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G))
      = Module.finrank ℂ
          (Subalgebra.toSubmodule (Subalgebra.center ℂ (MonoidAlgebra ℂ G))) := rfl
    _ = _ := by rw [hsub, LinearEquiv.finrank_map_eq]
    _ = Nat.card (ConjClasses G) :=
      MathlibExt.GroupTheory.ClassFunctionWanted.finrank_classFunctions_eq_card_conjClasses G ℂ

/-- The centre of a product of `n` nonzero complex matrix algebras has dimension `n`. -/
private theorem finrank_center_pi_matrix {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    Module.finrank ℂ (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) = n := by
  classical
  let Λ : (Fin n → ℂ) →ₗ[ℂ] (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
    { toFun := fun c i => c i • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)
      map_add' := fun c c' => by ext i : 1; simp [add_smul]
      map_smul' := fun a c => by ext i : 1; simp [mul_smul] }
  have hΛ : Function.Injective Λ := by
    intro c c' h
    ext i
    have := congrArg (fun M : Matrix (Fin (d i)) (Fin (d i)) ℂ => M 0 0) (congrFun h i)
    simpa [Λ] using this
  have hrange : LinearMap.range Λ =
      Subalgebra.toSubmodule (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
    ext z
    rw [LinearMap.mem_range, Subalgebra.mem_toSubmodule, Subalgebra.center_pi]
    simp only [Subalgebra.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨c, rfl⟩ i
      rw [Subalgebra.mem_center_iff]
      intro b
      simp [Λ]
    · intro hz
      have : ∀ i, ∃ c : ℂ, scalar (Fin (d i)) c = z i := by
        intro i
        have hzi : z i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) ℂ) := hz i
        rw [center_eq_range] at hzi
        exact hzi
      choose c hc using this
      refine ⟨c, funext fun i => ?_⟩
      rw [← hc i]
      ext a b
      simp [Λ, scalar_apply, diagonal, Matrix.one_apply]
  calc Module.finrank ℂ (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ))
      = Module.finrank ℂ (LinearMap.range Λ) := by rw [hrange]; rfl
    _ = Module.finrank ℂ (Fin n → ℂ) := LinearMap.finrank_range_of_inj hΛ
    _ = n := by simp

/-! ### The Wedderburn blocks of the group determinant -/

section Wedderburn

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {d : Fin n → ℕ}

/-- Coordinates on the complex group algebra. -/
private noncomputable def toGroupAlgebra (G : Type*) [Group G] [Fintype G] :
    (G → ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ G :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm ≪≫ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).symm

private theorem toGroupAlgebra_single [DecidableEq G] (g : G) :
    toGroupAlgebra G (Pi.single g 1) = MonoidAlgebra.of ℂ G g := by
  simp [toGroupAlgebra, Finsupp.linearEquivFunOnFinite_symm_single, MonoidAlgebra.of_apply]

/-- Coordinates on a product of matrix algebras. -/
private def flattenPi (d : Fin n → ℕ) :
    (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ] ((Σ i, Fin (d i) × Fin (d i)) → ℂ) where
  toFun B j := B j.1 j.2.1 j.2.2
  invFun y i := Matrix.of fun a b => y ⟨i, a, b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)

/-- The isomorphism `φ` in coordinates. -/
private noncomputable def wedderburnCoord :
    (G → ℂ) ≃ₗ[ℂ] ((Σ i, Fin (d i) × Fin (d i)) → ℂ) :=
  toGroupAlgebra G ≪≫ₗ φ.toLinearEquiv ≪≫ₗ flattenPi d

private theorem wedderburnCoord_apply (x : G → ℂ) (j : Σ i, Fin (d i) × Fin (d i)) :
    wedderburnCoord φ x j = φ (toGroupAlgebra G x) j.1 j.2.1 j.2.2 := rfl

/-- The `i`-th block `∑ g, x_g φ(g)_i` of the generic element of the group algebra. -/
private noncomputable def blockMatrix (i : Fin n) :
    Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial G ℂ) :=
  Matrix.of fun a b => ∑ g, C (φ (MonoidAlgebra.of ℂ G g) i a b) * X g

private theorem eval_blockMatrix (x : G → ℂ) (i : Fin n) :
    (blockMatrix φ i).map (eval x) = φ (toGroupAlgebra G x) i := by
  classical
  ext a b
  have := linearMap_apply_eq_sum
    (wedderburnCoord φ : (G → ℂ) →ₗ[ℂ] ((Σ i, Fin (d i) × Fin (d i)) → ℂ)) x ⟨i, (a, b)⟩
  simp only [LinearEquiv.coe_coe, wedderburnCoord_apply, toGroupAlgebra_single] at this
  simp only [map_apply, blockMatrix, of_apply, map_sum, map_mul, eval_C, eval_X, this]

private theorem linSubstEquiv_wedderburnCoord_X [DecidableEq G]
    (j : Σ i, Fin (d i) × Fin (d i)) :
    linSubstEquiv (wedderburnCoord φ) (X j) = blockMatrix φ j.1 j.2.1 j.2.2 := by
  simp [linSubstEquiv_apply, linSubst_X, wedderburnCoord_apply, toGroupAlgebra_single,
    blockMatrix]

private theorem det_blockMatrix_eq [DecidableEq G] (i : Fin n) :
    (blockMatrix φ i).det = linSubstEquiv (wedderburnCoord φ)
      (rename (fun ab : Fin (d i) × Fin (d i) => (⟨i, ab⟩ : Σ i, Fin (d i) × Fin (d i)))
        (mvPolynomialX (Fin (d i)) (Fin (d i)) ℂ).det) := by
  rw [AlgHom.map_det, AlgEquiv.map_det]
  congr 1
  ext a b
  simp [mvPolynomialX_apply, linSubstEquiv_wedderburnCoord_X]

private theorem irreducible_det_blockMatrix [∀ i, NeZero (d i)] (i : Fin n) :
    Irreducible (blockMatrix φ i).det := by
  classical
  rw [det_blockMatrix_eq, MulEquiv.irreducible_iff]
  refine irreducible_rename (fun x y h => ?_) (irreducible_det_mvPolynomialX ℂ (NeZero.ne (d i)))
  simpa using h

private theorem isHomogeneous_det_blockMatrix (i : Fin n) :
    (blockMatrix φ i).det.IsHomogeneous (d i) := by
  have := isHomogeneous_det (blockMatrix φ i) fun a b =>
    IsHomogeneous.sum _ _ _ fun g _ => isHomogeneous_C_mul_X _ _
  simpa using this

private theorem not_associated_det_blockMatrix [∀ i, NeZero (d i)] {i j : Fin n} (hij : i ≠ j) :
    ¬ Associated (blockMatrix φ i).det (blockMatrix φ j).det := by
  classical
  intro hassoc
  let target : Π k, Matrix (Fin (d k)) (Fin (d k)) ℂ := fun k => if k = j then 0 else 1
  let x : G → ℂ := (toGroupAlgebra G).symm (φ.symm target)
  have hx : ∀ k, eval x (blockMatrix φ k).det = (target k).det := by
    intro k
    rw [RingHom.map_det, RingHom.mapMatrix_apply, eval_blockMatrix]
    simp [x]
  have hdvd := map_dvd (eval x) hassoc.symm.dvd
  rw [hx, hx] at hdvd
  simp [target, hij] at hdvd

/-- The matrix `x_{k h⁻¹}` of left multiplication by `∑ g, x_g g` on the group algebra. -/
private noncomputable def leftRegularMatrix (G : Type*) [Group G] :
    Matrix G G (MvPolynomial G ℂ) :=
  Matrix.of fun k h => X (k * h⁻¹)

private theorem groupDeterminant_eq [DecidableEq G] : groupDeterminant G =
    ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : MvPolynomial G ℂ) * (leftRegularMatrix G).det := by
  rw [groupDeterminant, ← det_permute']
  congr 1
  ext g h
  simp [groupMatrix, leftRegularMatrix]

private theorem leftRegularMatrix_intertwine [DecidableEq G] :
    (Matrix.of fun j g =>
        algebraMap ℂ (MvPolynomial G ℂ) (wedderburnCoord φ (Pi.single g 1) j) :
        Matrix (Σ i, Fin (d i) × Fin (d i)) G (MvPolynomial G ℂ)) * leftRegularMatrix G =
      blockDiagonal' (fun i => kroneckerMap (· * ·) (blockMatrix φ i)
        (1 : Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial G ℂ))) *
      (Matrix.of fun j g =>
        algebraMap ℂ (MvPolynomial G ℂ) (wedderburnCoord φ (Pi.single g 1) j)) := by
  refine Matrix.ext fun j h => ?_
  obtain ⟨i, a, b⟩ := j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i (fun i' _ hi' => Finset.sum_eq_zero fun p _ => by
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hi'), zero_mul]) (by simp)]
  simp only [of_apply, wedderburnCoord_apply, toGroupAlgebra_single, leftRegularMatrix,
    blockDiagonal'_apply_eq, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    algebraMap_eq]
  rw [← Equiv.sum_comp (Equiv.mulRight h)]
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right, map_mul, Pi.mul_apply, Matrix.mul_apply,
    map_sum, blockMatrix, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun g _ => by ring

private theorem det_leftRegularMatrix [DecidableEq G] [∀ i, NeZero (d i)] :
    (leftRegularMatrix G).det = ∏ i, (blockMatrix φ i).det ^ d i := by
  classical
  set P : Matrix (Σ i, Fin (d i) × Fin (d i)) G (MvPolynomial G ℂ) :=
    Matrix.of fun j g => algebraMap ℂ _ (wedderburnCoord φ (Pi.single g 1) j) with hP
  set P' : Matrix G (Σ i, Fin (d i) × Fin (d i)) (MvPolynomial G ℂ) :=
    Matrix.of fun g j => algebraMap ℂ _ ((wedderburnCoord φ).symm (Pi.single j 1) g) with hP'
  have h1 : P * P' = 1 := mul_matrix_symm (wedderburnCoord φ)
  have h2 : P' * P = 1 := by simpa using mul_matrix_symm (wedderburnCoord φ).symm
  set L' := blockDiagonal' fun i => kroneckerMap (· * ·) (blockMatrix φ i)
    (1 : Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial G ℂ)) with hL'
  have hint : P * leftRegularMatrix G = L' * P := leftRegularMatrix_intertwine φ
  let e : (G → MvPolynomial G ℂ) ≃ₗ[MvPolynomial G ℂ]
      ((Σ i, Fin (d i) × Fin (d i)) → MvPolynomial G ℂ) :=
    LinearEquiv.ofLinearMap (toLin' P) (toLin' P') (by rw [← toLin'_mul, h1, toLin'_one])
      (by rw [← toLin'_mul, h2, toLin'_one])
  have hconj : (e : _ →ₗ[MvPolynomial G ℂ] _) ∘ₗ toLin' (leftRegularMatrix G) ∘ₗ
      (e.symm : _ →ₗ[MvPolynomial G ℂ] _) = toLin' L' := by
    change toLin' P ∘ₗ toLin' (leftRegularMatrix G) ∘ₗ toLin' P' = toLin' L'
    rw [← toLin'_mul, ← toLin'_mul, ← Matrix.mul_assoc, hint, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  calc (leftRegularMatrix G).det
      = LinearMap.det (toLin' (leftRegularMatrix G)) := (LinearMap.det_toLin' _).symm
    _ = LinearMap.det (toLin' L') := by rw [← hconj, LinearMap.det_conj]
    _ = L'.det := LinearMap.det_toLin' _
    _ = ∏ i, (kroneckerMap (· * ·) (blockMatrix φ i)
        (1 : Matrix (Fin (d i)) (Fin (d i)) (MvPolynomial G ℂ))).det :=
      det_blockDiagonal'_of_nonempty _
    _ = ∏ i, (blockMatrix φ i).det ^ d i := by simp [det_kronecker]

include φ in
omit [Fintype G] in
private theorem card_conjClasses_eq [Finite G] [∀ i, NeZero (d i)] :
    Nat.card (ConjClasses G) = n := by
  rw [← finrank_center_monoidAlgebra G, ← finrank_center_pi_matrix d,
    ← Subalgebra.map_center_eq φ]
  exact (φ.subalgebraMap _).toLinearEquiv.finrank_eq

end Wedderburn

/-- **Frobenius determinant theorem.** Let $G$ be a finite group and let $r$ be the number of
conjugacy classes of $G$. Then there exist polynomials $p_1, \dots, p_r$ in
$\mathbb{C}[x_g : g \in G]$ such that each $p_j$ is irreducible, $p_i$ and $p_j$ are not associated
for $i \neq j$, and the group determinant of $G$ equals $\prod_{j=1}^{r} p_j^{\deg p_j}$, where
$\deg p_j$ is the total degree of $p_j$.

Source: Knill, *Some fundamental theorems in mathematics*, §171. Via leanprover/lean-eval@38361be,
problem `frobenius_group_determinant`.
-/
theorem frobenius_group_determinant
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (r : ℕ) (p : Fin r → MvPolynomial G ℂ),
      r = Nat.card (ConjClasses G) ∧
      (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, (p j) ^ (p j).totalDegree := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  have hn : n = Nat.card (ConjClasses G) := (card_conjClasses_eq φ).symm
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  have hn0 : 0 < n := hn ▸ Nat.card_pos
  set i₀ : Fin n := ⟨0, hn0⟩
  -- the sign `±1` relating `groupDeterminant G` to the left regular determinant
  set u : ℂ := ((Equiv.Perm.sign (Equiv.inv G) : ℤ) : ℂ) with hu_def
  have hu : u ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv G)) with h | h <;> simp [u, h]
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (Nat.pos_of_ne_zero (NeZero.ne (d i₀)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne (d i₀))] at hc
    exact hu hc.symm
  -- absorb the sign into the factor of index `i₀`
  let q : Fin n → MvPolynomial G ℂ := fun i => (blockMatrix φ i).det
  let a : Fin n → MvPolynomial G ℂ := fun i => if i = i₀ then C c else 1
  let p : Fin n → MvPolynomial G ℂ := fun i => a i * q i
  have ha : ∀ i, IsUnit (a i) := by
    intro i
    by_cases h : i = i₀
    · simp only [a, h, ite_true]
      exact (Ne.isUnit hc0).map C
    · simp [a, h]
  have hpq : ∀ i, Associated (q i) (p i) := fun i =>
    ⟨(ha i).unit, by simp [p, mul_comm]⟩
  have hdeg : ∀ i, (p i).totalDegree = d i := by
    intro i
    have hai : (a i).IsHomogeneous 0 := by
      by_cases h : i = i₀
      · simp only [a, h, ite_true]; exact isHomogeneous_C _ _
      · simp only [a, h, ite_false]; exact isHomogeneous_one _ _
    have hhom : (p i).IsHomogeneous (d i) := by
      simpa using hai.mul (isHomogeneous_det_blockMatrix φ i)
    exact hhom.totalDegree ((hpq i).irreducible (irreducible_det_blockMatrix φ i)).ne_zero
  refine ⟨n, p, hn, fun i => (hpq i).irreducible (irreducible_det_blockMatrix φ i),
    fun i j hij h => not_associated_det_blockMatrix φ hij
      ((hpq i).trans (h.trans (hpq j).symm)), ?_⟩
  rw [groupDeterminant_eq, det_leftRegularMatrix φ]
  simp only [hdeg]
  have hsplit : ∏ i, p i ^ d i = (∏ i, a i ^ d i) * ∏ i, q i ^ d i := by
    simp only [p, mul_pow, Finset.prod_mul_distrib]
  rw [hsplit]
  congr 1
  simp only [a, ite_pow, one_pow, Finset.prod_ite_eq', Finset.mem_univ, ite_true, ← map_pow, hc]
  simp [u]

end RepresentationTheory.FrobeniusDeterminant

end MathlibExt.GroupTheory.FrobeniusDeterminantWanted
