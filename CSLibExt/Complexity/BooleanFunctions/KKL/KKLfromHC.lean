/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Hypercontractivity.VectorTwoPoint
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence

/-!
# Walsh–Fourier analysis on the uniform cube and the KKL reduction

Walsh–Fourier compatibility API on `{0, 1}^ι`, for an arbitrary finite index type `ι`.
The legacy convention `false ↦ 1`, `true ↦ -1` is retained for KKL consumers. Fourier
inversion, Parseval, variance, influence and noise identities reuse the canonical proofs in
`BooleanCube`: reindex coordinates with `Fintype.equivFin`, then use the parity bridge
`(-1)^{|S|}`. No finiteness or nonemptiness hypotheses are added to the basic characters.
The Bonami–Beckner inequality is transported from `Fin n` in the same way.

For Boolean functions, the canonical influence uses quarter squared flip differences.
`khc_infl_eq_four_boolInfluence` accounts for the factor `4` in event influence before
transporting the canonical Fourier weights. These weights reduce KKL at `p = 1/2` to
`khc_LogSobolevStep`.

## Main definitions

* `StatMech.Probability.khc_walshChar`: the Walsh character `χ_S`.
* `StatMech.Probability.khc_fourierCoeff`: the Fourier coefficient `f̂(S) = 𝔼[f χ_S]`.
* `StatMech.Probability.khc_reindex`: transport of a function along a bijection of index types.
* `StatMech.Probability.khc_LogSobolevStep`: the Fourier form of the KKL inequality at
  `p = 1/2`.

## Main results

* `StatMech.Probability.khc_fourier_expansion`, `StatMech.Probability.khc_parseval`: Fourier
  inversion and Parseval's identity.
* `StatMech.Probability.khc_hypercontractivity_general`: the Bonami–Beckner inequality on
  `{0, 1}^ι`.
* `StatMech.Probability.khc_var_eq_fourierWeight`,
  `StatMech.Probability.khc_totalInfl_eq_fourierWeight`: `Var(f) = ∑_{S ≠ ∅} f̂(S)²` and
  `∑ₑ Infₑ(1_A) = ∑_S 4 |S| f̂(S)²`.
* `StatMech.Probability.khc_KKL`: the Fourier form implies `KKLHypercontractive (1/2) c`.
* `StatMech.Probability.khc_walshChar_eq_cubeChi`,
  `StatMech.Probability.khc_fourierCoeff_eq_boolFourierCoeff`,
  `StatMech.Probability.khc_var_half_eq_boolVariance`: on `Fin n` these notions agree with
  `BooleanCube.cubeChi`, `BooleanCube.boolFourierCoeff` and `BooleanCube.boolVariance` (up to
  the sign `(-1)^{|S|}`, since `BooleanCube.cubeVal` sends `true` to `1`).

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014, Chapters 1,
  2 and 9.
* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech
namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **$\pm 1$ value of a bit.** The `±1` value of a bit: `false ↦ 1`, `true ↦ -1`. -/
def khc_sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem khc_sign_false : khc_sign false = 1 := rfl
@[simp] theorem khc_sign_true : khc_sign true = -1 := rfl

theorem khc_sign_sq (b : Bool) : khc_sign b * khc_sign b = 1 := by
  cases b <;> simp [khc_sign]

/-- **Walsh character on the Boolean cube.**
The Walsh character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}` on `{0, 1}^ι`.

  This legacy sign convention is retained for KKL consumers; its proofs use
  `BooleanCube.cubeChi` through `khc_walshChar_eq_cubeChi`. -/
noncomputable def khc_walshChar (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, khc_sign (x i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem khc_walshChar_empty (x : ι → Bool) :
    khc_walshChar (∅ : Finset ι) x = 1 := by
  simp [khc_walshChar]

omit [Fintype ι] [DecidableEq ι] in
theorem khc_walshChar_sq (S : Finset ι) (x : ι → Bool) :
    (khc_walshChar S x) ^ 2 = 1 := by
  unfold khc_walshChar
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one (fun i _ => by rw [sq]; exact khc_sign_sq (x i))

omit [Fintype ι] in
theorem khc_walshChar_mul (S T : Finset ι) (x : ι → Bool) :
    khc_walshChar S x * khc_walshChar T x = khc_walshChar (symmDiff S T) x := by
  have key : ∀ V : Finset ι, V ⊆ S ∪ T →
      khc_walshChar V x = ∏ i ∈ S ∪ T, (if i ∈ V then khc_sign (x i) else 1) := fun V hV => by
    unfold khc_walshChar; rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hV]
  rw [key S Finset.subset_union_left, key T Finset.subset_union_right,
    key _ Finset.symmDiff_subset_union, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, khc_sign_sq]

/-- **Fourier–Walsh coefficient under the uniform measure.**
The Fourier–Walsh coefficient `f̂(S) = 𝔼[f χ_S]` under the uniform measure.

  This retains the legacy signs; `khc_fourierCoeff_eq_boolFourierCoeff` transports
  the canonical Fourier identities used below. -/
noncomputable def khc_fourierCoeff (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  bnt_uexp (fun x => f x * khc_walshChar S x)

/-- **Reindexing a cube function along an index bijection.**
The function `f` on `{0, 1}^ι` transported to `{0, 1}^κ` along the bijection `e : κ ≃ ι`. -/
noncomputable def khc_reindex {κ : Type*} (e : κ ≃ ι) (f : (ι → Bool) → ℝ) :
    (κ → Bool) → ℝ :=
  fun y => f (fun i => y (e.symm i))

/-- **Cube bijection induced by an index bijection.**
The bijection `{0, 1}^ι ≃ {0, 1}^κ` induced by `e : κ ≃ ι`. -/
def khc_cubeEquiv {κ : Type*} (e : κ ≃ ι) : (ι → Bool) ≃ (κ → Bool) :=
  Equiv.arrowCongr e.symm (Equiv.refl Bool)

theorem khc_uexp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (f : (ι → Bool) → ℝ) :
    bnt_uexp (khc_reindex e f) = bnt_uexp f := by
  unfold bnt_uexp khc_reindex
  rw [Fintype.card_congr e]
  congr 1
  symm
  apply Fintype.sum_equiv (khc_cubeEquiv e)
  intro x
  unfold khc_cubeEquiv
  congr 1
  funext i
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp,
    Equiv.symm_symm, id_eq, Equiv.apply_symm_apply]

theorem khc_qnorm_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (q : ℝ)
    (f : (ι → Bool) → ℝ) :
    bnt_qnorm q (khc_reindex e f) = bnt_qnorm q f := by
  unfold bnt_qnorm bnt_qnormPow
  congr 2
  rw [show (fun y => |khc_reindex e f y| ^ q) = khc_reindex e (fun x => |f x| ^ q) from rfl]
  rw [khc_uexp_reindex]

theorem khc_noiseOp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (ρ : ℝ)
    (f : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (khc_reindex e f) = khc_reindex e (bnt_noiseOp ρ f) := by
  funext y
  unfold bnt_noiseOp khc_reindex bnt_noiseKernel
  symm
  apply Fintype.sum_equiv (khc_cubeEquiv e)
  intro w
  unfold khc_cubeEquiv
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq]
  congr 1
  · rw [← Equiv.prod_comp e (fun j => if (fun i => y (e.symm i)) j = w j then (1 + ρ) / 2 else
      (1 - ρ) / 2)]
    apply Finset.prod_congr rfl
    intro i _; simp [Equiv.symm_apply_apply]
  · congr 1; funext j; simp [Equiv.apply_symm_apply]

/-- **Walsh character agrees with the canonical cube character up to sign.**
On `Fin n`, the Walsh character is `BooleanCube.cubeChi` up to the sign `(-1)^{|S|}`:
`BooleanCube.cubeVal` sends `true` to `1`, while `khc_sign` sends it to `-1`. -/
theorem khc_walshChar_eq_cubeChi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    khc_walshChar S x = (-1) ^ S.card * BooleanCube.cubeChi n S x := by
  unfold khc_walshChar BooleanCube.cubeChi
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases x i <;> simp [khc_sign, BooleanCube.cubeVal]

/-- **Walsh coefficient is the canonical Fourier coefficient up to sign.**
On `Fin n`, the Fourier coefficient is `BooleanCube.boolFourierCoeff` up to the sign
`(-1)^{|S|}`. -/
theorem khc_fourierCoeff_eq_boolFourierCoeff {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    khc_fourierCoeff f S = (-1) ^ S.card * BooleanCube.boolFourierCoeff n f S := by
  unfold khc_fourierCoeff bnt_uexp BooleanCube.boolFourierCoeff
  rw [BooleanCube.card_boolCube, Fintype.card_fin, mul_div_assoc', Finset.mul_sum]
  simp only [khc_walshChar_eq_cubeChi, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Reindexing a Walsh character reindexes its coordinate set.**
Reindexing a Walsh character reindexes its finite set of coordinates. -/
theorem khc_walshChar_reindex {κ : Type*} (e : ι ≃ κ) (S : Finset ι) :
    khc_reindex e.symm (khc_walshChar S) = khc_walshChar (e.finsetCongr S) := by
  funext x
  simp [khc_reindex, khc_walshChar, Equiv.finsetCongr_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- **Reindexing preserves values at corresponding cube points.**
Reindexing back at the corresponding cube point recovers the original value. -/
theorem khc_reindex_cubeEquiv {κ : Type*} (e : κ ≃ ι) (f : (ι → Bool) → ℝ)
    (x : ι → Bool) : khc_reindex e f (khc_cubeEquiv e x) = f x := by
  simp [khc_reindex, khc_cubeEquiv, Equiv.arrowCongr_apply, Function.comp_def]

/-- **Fourier coefficients are invariant under reindexing.**
Fourier coefficients are unchanged when both the function and its index are reindexed. -/
theorem khc_fourierCoeff_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    khc_fourierCoeff (khc_reindex e.symm f) (e.finsetCongr S) = khc_fourierCoeff f S := by
  unfold khc_fourierCoeff
  rw [← khc_walshChar_reindex]
  exact khc_uexp_reindex e.symm (fun x => f x * khc_walshChar S x)

private theorem khc_phase_mul (k : ℕ) (a b : ℝ) :
    ((-1 : ℝ) ^ k * a) * ((-1) ^ k * b) = a * b := by
  rw [mul_mul_mul_comm, ← sq, ← pow_mul, mul_comm k 2, pow_mul]
  norm_num

private theorem khc_coeff_char_product {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) (x : Fin n → Bool) :
    khc_fourierCoeff f S * khc_walshChar S x =
      BooleanCube.boolFourierCoeff n f S * BooleanCube.cubeChi n S x := by
  rw [khc_fourierCoeff_eq_boolFourierCoeff, khc_walshChar_eq_cubeChi, khc_phase_mul]

private theorem khc_coeff_product {n : ℕ} (f g : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    khc_fourierCoeff f S * khc_fourierCoeff g S =
      BooleanCube.boolFourierCoeff n f S * BooleanCube.boolFourierCoeff n g S := by
  rw [khc_fourierCoeff_eq_boolFourierCoeff, khc_fourierCoeff_eq_boolFourierCoeff,
    khc_phase_mul]

theorem khc_uexp_walshChar (S : Finset ι) :
    bnt_uexp (khc_walshChar S) = if S = ∅ then 1 else 0 := by
  let e := Fintype.equivFin ι
  rw [← khc_uexp_reindex e.symm, khc_walshChar_reindex]
  unfold bnt_uexp
  simp_rw [khc_walshChar_eq_cubeChi]
  rw [← Finset.mul_sum, BooleanCube.sum_cubeChi_eq_ite]
  by_cases hS : S = ∅ <;>
    simp [Equiv.finsetCongr_apply, hS]

theorem khc_orthonormal (S T : Finset ι) :
    bnt_uexp (fun x => khc_walshChar S x * khc_walshChar T x) = if S = T then 1 else 0 := by
  simp_rw [khc_walshChar_mul]
  rw [khc_uexp_walshChar]
  by_cases h : S = T
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    intro hsd
    exact h (symmDiff_eq_bot.mp (by simpa using hsd))

omit [DecidableEq ι] in
theorem khc_sum_walshChar_mul (x y : ι → Bool) :
    (∑ S : Finset ι, khc_walshChar S x * khc_walshChar S y)
      = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
  classical
  let e := Fintype.equivFin ι
  calc
    _ = ∑ S : Finset (Fin (Fintype.card ι)),
        khc_walshChar S (khc_cubeEquiv e.symm x) *
          khc_walshChar S (khc_cubeEquiv e.symm y) := by
      apply Fintype.sum_equiv e.finsetCongr
      intro S
      rw [← khc_walshChar_reindex, khc_reindex_cubeEquiv, khc_reindex_cubeEquiv]
    _ = _ := by
      simp_rw [khc_walshChar_eq_cubeChi, khc_phase_mul]
      rw [BooleanCube.sum_cubeChi_apply_mul_cubeChi_apply_eq_ite]
      simp only [Equiv.apply_eq_iff_eq]

/-- **Fourier inversion on the Boolean cube.** Fourier inversion: `f = ∑_S f̂(S) χ_S`. -/
theorem khc_fourier_expansion (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) = f x := by
  let e := Fintype.equivFin ι
  calc
    _ = ∑ S : Finset (Fin (Fintype.card ι)),
        khc_fourierCoeff (khc_reindex e.symm f) S *
          khc_walshChar S (khc_cubeEquiv e.symm x) := by
      apply Fintype.sum_equiv e.finsetCongr
      intro S
      rw [khc_fourierCoeff_reindex e, ← khc_walshChar_reindex e,
        khc_reindex_cubeEquiv]
    _ = f x := by
      simp_rw [khc_coeff_char_product]
      rw [BooleanCube.sum_boolFourierCoeff_mul_cubeChi, khc_reindex_cubeEquiv]

theorem khc_uexp_finset_sum {κ : Type*} (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_uexp (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, bnt_uexp (g k) := by
  unfold bnt_uexp; simp_rw [Finset.sum_div]; rw [Finset.sum_comm]

theorem khc_uexp_const_mul (c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => c * g x) = c * bnt_uexp g := by
  unfold bnt_uexp; rw [← Finset.mul_sum, mul_div_assoc]

/-- **Parseval's identity on the Boolean cube.** Parseval's identity: `𝔼[f g] = ∑_S f̂(S) ĝ(S)`.

  Transported from `BooleanCube.expect_mul_eq_sum_boolFourierCoeff_mul`. -/
theorem khc_parseval (f g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => f x * g x)
      = ∑ S : Finset ι, khc_fourierCoeff f S * khc_fourierCoeff g S := by
  let e := Fintype.equivFin ι
  rw [← khc_uexp_reindex e.symm, bnt_uexp_eq_expect]
  change (𝔼 x, khc_reindex e.symm f x * khc_reindex e.symm g x) = _
  rw [BooleanCube.expect_mul_eq_sum_boolFourierCoeff_mul]
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  rw [← khc_coeff_product, khc_fourierCoeff_reindex e,
    khc_fourierCoeff_reindex e]

theorem khc_parseval_sq (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (f x) ^ 2) = ∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2 := by
  have h := khc_parseval f f
  simp_rw [← sq] at h
  exact h

theorem khc_noiseOp_const_mul (ρ c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => c * g x) = fun x => c * bnt_noiseOp ρ g x := by
  funext x; unfold bnt_noiseOp; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _; ring

theorem khc_noiseOp_walshChar_apply (ρ : ℝ) (S : Finset ι) (x : ι → Bool) :
    bnt_noiseOp ρ (khc_walshChar S) x = ρ ^ S.card * khc_walshChar S x := by
  let e := Fintype.equivFin ι
  let T := e.finsetCongr S
  have hchar : khc_walshChar T =
      fun y => (-1) ^ T.card * BooleanCube.cubeChi (Fintype.card ι) T y :=
    funext (khc_walshChar_eq_cubeChi T)
  rw [← khc_reindex_cubeEquiv e.symm (bnt_noiseOp ρ (khc_walshChar S)) x,
    ← khc_noiseOp_reindex, khc_walshChar_reindex]
  change bnt_noiseOp ρ (khc_walshChar T) (khc_cubeEquiv e.symm x) = _
  rw [hchar, khc_noiseOp_const_mul, bnt_noiseOp_eq_boolNoiseOp,
    BooleanCube.boolNoiseOp_cubeChi]
  calc
    _ = ρ ^ T.card *
        ((-1) ^ T.card * BooleanCube.cubeChi (Fintype.card ι) T
          (khc_cubeEquiv e.symm x)) := by ring
    _ = _ := by
      rw [← khc_walshChar_eq_cubeChi]
      change ρ ^ (e.finsetCongr S).card *
        khc_walshChar (e.finsetCongr S) (khc_cubeEquiv e.symm x) = _
      rw [← khc_walshChar_reindex, khc_reindex_cubeEquiv]
      simp only [Equiv.finsetCongr_apply, Finset.card_map]

theorem khc_noiseOp_finset_sum {κ : Type*} (ρ : ℝ) (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, bnt_noiseOp ρ (g k) x := by
  funext x; unfold bnt_noiseOp; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

/-- **Noise operator is diagonal in the Walsh basis.**
The noise operator acts diagonally on the Walsh basis: `T_ρ f = ∑_S ρ^{|S|} f̂(S) χ_S`.

  Transported from `BooleanCube.boolNoiseOp_eq_sum`, for every real `ρ`. -/
theorem khc_noiseOp_fourier (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ f
      = fun x => ∑ S : Finset ι, (ρ ^ S.card * khc_fourierCoeff f S) * khc_walshChar S x := by
  let e := Fintype.equivFin ι
  funext x
  rw [← khc_reindex_cubeEquiv e.symm (bnt_noiseOp ρ f) x,
    ← khc_noiseOp_reindex, bnt_noiseOp_eq_boolNoiseOp, BooleanCube.boolNoiseOp_eq_sum]
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [mul_assoc]
  rw [← khc_coeff_char_product, khc_fourierCoeff_reindex,
    ← khc_walshChar_reindex, khc_reindex_cubeEquiv]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

theorem khc_noiseOp_l2sq (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (bnt_noiseOp ρ f x) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
  let e := Fintype.equivFin ι
  rw [← khc_uexp_reindex e.symm, bnt_uexp_eq_expect]
  change (𝔼 x, (khc_reindex e.symm (bnt_noiseOp ρ f) x) ^ 2) = _
  rw [← khc_noiseOp_reindex, bnt_noiseOp_eq_boolNoiseOp,
    BooleanCube.expect_sq_eq_sum_boolFourierCoeff_sq]
  simp_rw [BooleanCube.boolFourierCoeff_boolNoiseOp, mul_pow]
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  have hc := khc_coeff_product (khc_reindex e.symm f) (khc_reindex e.symm f)
    (e.finsetCongr S)
  rw [khc_fourierCoeff_reindex] at hc
  simp only [← sq] at hc
  rw [← hc]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

/-- **Bonami–Beckner hypercontractive inequality** (A. Bonami, *Étude des coefficients de Fourier
  des fonctions de Lᵖ(G)*, Ann. Inst. Fourier 1970; W. Beckner, *Inequalities in Fourier
  analysis*, Ann. of Math. 1975): `‖T_ρ g‖₂ ≤ ‖g‖_{1+ρ²}` on `{0, 1}^ι` for `0 ≤ ρ ≤ 1`. -/
theorem khc_hypercontractivity_general {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (g : (ι → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ g) ≤ bnt_qnorm (1 + ρ ^ 2) g := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hHC := bnt_hypercontractivity (vtp_vectorTwoPoint h0 h1) (Fintype.card ι)
    (khc_reindex e.symm g)
  rw [khc_noiseOp_reindex e.symm ρ g, khc_qnorm_reindex e.symm 2 (bnt_noiseOp ρ g),
      khc_qnorm_reindex e.symm (1 + ρ ^ 2) g] at hHC
  exact hHC

/-- **Hypercontractivity in Fourier form.**
Hypercontractivity in Fourier form: `∑_S ρ^{2|S|} f̂(S)² ≤ ‖f‖²_{1+ρ²}`. -/
theorem khc_lowDegreeWeight_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 := by
  have hhc : bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f :=
    khc_hypercontractivity_general h0 h1 f
  have hlhs : 0 ≤ bnt_qnorm 2 (bnt_noiseOp ρ f) := bnt_qnorm_nonneg 2 _
  have hsq : (bnt_qnorm 2 (bnt_noiseOp ρ f)) ^ 2 ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 := by
    have hrhs : 0 ≤ bnt_qnorm (1 + ρ ^ 2) f := bnt_qnorm_nonneg _ _
    nlinarith [hhc, hlhs, hrhs]
  rw [vtp_qnorm2_sq, vtp_qnormPow2_eq_uexp_sq, khc_noiseOp_l2sq] at hsq
  exact hsq

theorem khc_lowDegreeWeight_fluct_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      ≤ (bnt_qnorm (1 + ρ ^ 2) f) ^ 2 - (khc_fourierCoeff f ∅) ^ 2 := by
  have hfull := khc_lowDegreeWeight_le h0 h1 f
  have hsplit : (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2)
      = (ρ ^ (∅ : Finset ι).card) ^ 2 * (khc_fourierCoeff f ∅) ^ 2
        + ∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ (∅ : Finset ι))]
  rw [hsplit] at hfull
  simp only [Finset.card_empty, pow_zero, one_pow, one_mul] at hfull
  linarith

open StatMech.OSSS in
omit [DecidableEq ι] in
theorem khc_bernoulliWeight_half (ω : ConfigSpace ι) :
    OSSS.weight (OSSS.bernoulliWeight (1 / 2 : ℝ)) ω = 1 / (2 ^ Fintype.card ι) := by
  unfold OSSS.weight OSSS.bernoulliWeight
  have hfac : ∀ e : ι, (if ω e then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
    intro e; cases ω e <;> norm_num
  simp_rw [hfac]
  rw [Finset.prod_const, Finset.card_univ, div_pow, one_pow]

open StatMech.OSSS in
theorem khc_expect_half (g : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) g = bnt_uexp g := by
  unfold OSSS.expect bnt_uexp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [khc_bernoulliWeight_half, one_div, div_eq_mul_inv, ← div_eq_mul_inv]
  ring

theorem khc_uexp_eq_coeff_empty (g : ConfigSpace ι → ℝ) :
    bnt_uexp g = khc_fourierCoeff g ∅ := by
  unfold khc_fourierCoeff
  congr 1; funext x; rw [khc_walshChar_empty, mul_one]

open StatMech.OSSS in
/-- **Variance as Fourier weight off the empty set.**
Variance under the uniform measure is the Fourier weight off the empty set. -/
theorem khc_var_eq_fourierWeight (g : ConfigSpace ι → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) g
      = ∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff g S) ^ 2 := by
  let e := Fintype.equivFin ι
  have hv : OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) g =
      BooleanCube.boolVariance (khc_reindex e.symm g) := by
    rw [BooleanCube.boolVariance_eq_expect_sq_sub_sq,
      ← bnt_uexp_eq_expect, ← bnt_uexp_eq_expect]
    unfold OSSS.var OSSS.cov
    rw [khc_expect_half, khc_expect_half]
    change _ = bnt_uexp (khc_reindex e.symm (fun x => (g x) ^ 2)) -
      (bnt_uexp (khc_reindex e.symm g)) ^ 2
    rw [khc_uexp_reindex, khc_uexp_reindex]
    simp only [sq]
  rw [hv, BooleanCube.boolVariance_eq_sum_sq]
  symm
  apply Finset.sum_equiv e.finsetCongr
  · intro S
    simp [Equiv.finsetCongr_apply, Finset.nonempty_iff_ne_empty]
  · intro S _
    rw [sq, sq, ← khc_coeff_product, khc_fourierCoeff_reindex]

omit [Fintype ι] in
theorem khc_walshChar_setOpen_sub_setClosed (S : Finset ι) (e : ι) (ω : ConfigSpace ι) :
    khc_walshChar S (StatMech.setOpen e ω) - khc_walshChar S (StatMech.setClosed e ω)
      = if e ∈ S then (-2 : ℝ) * khc_walshChar (S.erase e) ω else 0 := by
  by_cases he : e ∈ S
  · rw [ite_eq_left he]
    unfold khc_walshChar
    rw [← Finset.prod_erase_mul S _ he, ← Finset.prod_erase_mul S _ he]
    have hprodO : (∏ i ∈ S.erase e, khc_sign (StatMech.setOpen e ω i))
        = ∏ i ∈ S.erase e, khc_sign (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setOpen_of_ne (Finset.ne_of_mem_erase hi)]
    have hprodC : (∏ i ∈ S.erase e, khc_sign (StatMech.setClosed e ω i))
        = ∏ i ∈ S.erase e, khc_sign (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi; rw [StatMech.setClosed_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hprodO, hprodC, StatMech.setOpen_self, StatMech.setClosed_self]
    simp only [khc_sign_true, khc_sign_false]; ring
  · rw [ite_eq_right he]
    unfold khc_walshChar
    have : (∏ i ∈ S, khc_sign (StatMech.setOpen e ω i))
        = ∏ i ∈ S, khc_sign (StatMech.setClosed e ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ e := fun h => he (h ▸ hi)
      rw [StatMech.setOpen_of_ne hie, StatMech.setClosed_of_ne hie]
    rw [this, sub_self]

theorem khc_deriv_fourier (g : ConfigSpace ι → ℝ) (e : ι) (ω : ConfigSpace ι) :
    g (StatMech.setOpen e ω) - g (StatMech.setClosed e ω)
      = ∑ S ∈ univ.filter (fun S => e ∈ S),
          ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω := by
  have hO : g (StatMech.setOpen e ω)
      = ∑ S : Finset ι, khc_fourierCoeff g S * khc_walshChar S (StatMech.setOpen e ω) := by
    rw [khc_fourier_expansion]
  have hC : g (StatMech.setClosed e ω)
      = ∑ S : Finset ι, khc_fourierCoeff g S * khc_walshChar S (StatMech.setClosed e ω) := by
    rw [khc_fourier_expansion]
  rw [hO, hC, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset ι,
      khc_fourierCoeff g S * khc_walshChar S (StatMech.setOpen e ω)
        - khc_fourierCoeff g S * khc_walshChar S (StatMech.setClosed e ω)
        = if e ∈ S then ((-2 : ℝ) * khc_fourierCoeff g S) * khc_walshChar (S.erase e) ω else 0 := by
    intro S; rw [← mul_sub, khc_walshChar_setOpen_sub_setClosed]
    by_cases he : e ∈ S
    · rw [ite_eq_left he, ite_eq_left he]; ring
    · rw [ite_eq_right he, ite_eq_right he, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_filter]

theorem khc_uexp_sum_walsh_sq (s : Finset (Finset ι)) (a : Finset ι → ℝ)
    (T : Finset ι → Finset ι) (hTinj : Set.InjOn T s) :
    bnt_uexp (fun x => (∑ S ∈ s, a S * khc_walshChar (T S) x) ^ 2)
      = ∑ S ∈ s, (a S) ^ 2 := by
  rw [show (fun x => (∑ S ∈ s, a S * khc_walshChar (T S) x) ^ 2)
      = (fun x => ∑ S ∈ s, ∑ U ∈ s,
          (a S * a U) * (khc_walshChar (T S) x * khc_walshChar (T U) x)) from ?_]
  · rw [khc_uexp_finset_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [khc_uexp_finset_sum]
    have hterm : ∀ U ∈ s,
        bnt_uexp (fun x => a S * a U * (khc_walshChar (T S) x * khc_walshChar (T U) x))
          = a S * a U * (if T S = T U then 1 else 0) := by
      intro U _; rw [khc_uexp_const_mul, khc_orthonormal]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S hS]
    · rw [ite_eq_left rfl, mul_one, sq]
    · intro U hU hUS
      have hne : T S ≠ T U := fun h => hUS (hTinj hU hS h.symm)
      rw [ite_eq_right hne, mul_zero]
  · funext x; rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro U _; ring

theorem khc_erase_injOn (e : ι) :
    Set.InjOn (fun S => Finset.erase S e) ↑(univ.filter (fun S : Finset ι => e ∈ S)) := by
  intro S hS U hU h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hS hU
  simp only at h
  rw [← Finset.insert_erase hS, ← Finset.insert_erase hU, h]

omit [Fintype ι] in
theorem khc_abs_diff_indicator (φ : ConfigSpace ι → Bool) (e : ι) (ω : ConfigSpace ι) :
    |(fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)|
      = ((fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setOpen e ω)
        - (fun ω => if φ ω then (1 : ℝ) else 0) (StatMech.setClosed e ω)) ^ 2 := by
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC]

/-- **Event influence is four times the canonical influence.**
Event influence is four times canonical quarter-square influence after reindexing. -/
theorem khc_infl_eq_four_boolInfluence {n : ℕ} (e : ι ≃ Fin n)
    (φ : ConfigSpace ι → Bool) (i : ι) :
    OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
        (fun x => if φ x then (1 : ℝ) else 0) i =
      4 * BooleanCube.boolInfluence
        (khc_reindex e.symm (fun x => if φ x then (1 : ℝ) else 0)) (e i) := by
  rw [OSSS.infl, khc_expect_half, ← khc_uexp_reindex e.symm, bnt_uexp_eq_expect,
    BooleanCube.boolInfluence, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro y _
  let x : ι → Bool := fun j => y (e j)
  have hflip : (fun j => BooleanCube.flipCoord y (e i) (e j)) =
      Function.update x i (!x i) := by
    simpa [BooleanCube.flipCoord, Function.comp_def, x] using
      Function.update_comp_equiv y e (e i) (!y (e i))
  simp only [khc_reindex, Equiv.symm_symm, hflip]
  change |(if φ (setOpen i x) then (1 : ℝ) else 0) -
      (if φ (setClosed i x) then (1 : ℝ) else 0)| = _
  rw [khc_abs_diff_indicator]
  cases hx : x i
  · have hC : setClosed i x = x := by
      unfold setClosed
      rw [← hx, Function.update_eq_self]
    simp only [Bool.not_false]
    change ((if φ (setOpen i x) then (1 : ℝ) else 0) -
      (if φ (setClosed i x) then (1 : ℝ) else 0)) ^ 2 =
      4 * (((if φ x then (1 : ℝ) else 0) -
        (if φ (setOpen i x) then (1 : ℝ) else 0)) / 2) ^ 2
    rw [hC]
    ring
  · have hO : setOpen i x = x := by
      unfold setOpen
      rw [← hx, Function.update_eq_self]
    simp only [Bool.not_true]
    change ((if φ (setOpen i x) then (1 : ℝ) else 0) -
      (if φ (setClosed i x) then (1 : ℝ) else 0)) ^ 2 =
      4 * (((if φ x then (1 : ℝ) else 0) -
        (if φ (setClosed i x) then (1 : ℝ) else 0)) / 2) ^ 2
    rw [hO]
    ring

open StatMech.OSSS in
/-- **Influence of a coordinate as Fourier weight.**
The influence of `e` on a Boolean function is `∑_{S ∋ e} 4 f̂(S)²`. -/
theorem khc_infl_eq_fourierWeight (φ : ConfigSpace ι → Bool) (e : ι) :
    OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e
      = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  let e' := Fintype.equivFin ι
  rw [khc_infl_eq_four_boolInfluence e', BooleanCube.boolInfluence_eq_sum_sq,
    Finset.mul_sum]
  symm
  apply Finset.sum_equiv e'.finsetCongr
  · intro S
    simp [Equiv.finsetCongr_apply]
  · intro S _
    rw [sq, sq, ← khc_coeff_product, khc_fourierCoeff_reindex]

open StatMech.OSSS in
/-- **Total influence as Fourier weight.**
The total influence of a Boolean function is `∑_S 4 |S| f̂(S)²`. -/
theorem khc_totalInfl_eq_fourierWeight (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      = ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  let e := Fintype.equivFin ι
  rw [totalInfl]
  simp_rw [khc_infl_eq_four_boolInfluence e]
  rw [← Finset.mul_sum, e.sum_comp, ← BooleanCube.boolTotalInfluence,
    BooleanCube.boolTotalInfluence_eq_sum_card_mul_sq, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  rw [sq, sq, ← khc_coeff_product, khc_fourierCoeff_reindex]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  ring

/-- **Fourier-form KKL inequality given the hypercontractive bound.**
The KKL inequality at `p = 1/2` in Fourier form, with the hypercontractive bound as a
  hypothesis: for every Boolean `φ`, if `∑_S ρ^{2|S|} f̂(S)² ≤ ‖f‖²_{1+ρ²}` for all `ρ ∈ [0, 1]`,
  then `c · ∑_{S ≠ ∅} f̂(S)² · log (1 / maxₑ Infₑ(f)) ≤ ∑_S 4 |S| f̂(S)²`, where `f = 1_φ`. The
  hypothesis always holds (`khc_lowDegreeWeight_le`). -/
def khc_LogSobolevStep (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        (∑ S : Finset E, (ρ ^ S.card) ^ 2
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (bnt_qnorm (1 + ρ ^ 2) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2

/-- **Hypercontractive form of KKL with constant 0 holds trivially.**
`khc_LogSobolevStep 0` holds trivially. -/
theorem khc_logSobolevStep_zero : khc_LogSobolevStep 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  rw [← khc_totalInfl_eq_fourierWeight φ]
  exact kkl_totalInfl_nonneg
    (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) _

/-- **Hypercontractive form of KKL implies the KKL inequality at $p = 1/2$.**
The Fourier form `khc_LogSobolevStep c` implies the KKL inequality `KKLHypercontractive (1/2)
  c`. -/
theorem khc_KKL {c : ℝ} (H : khc_LogSobolevStep c) :
    KKLHypercontractive (1 / 2 : ℝ) c := by
  intro E _ _ _ φ
  rw [show OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_var_eq_fourierWeight _]
  rw [show totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_totalInfl_eq_fourierWeight _]
  exact H φ (fun ρ h0 h1 => khc_lowDegreeWeight_le h0 h1 _)

/-! ### Comparison with `BooleanCube` on `Fin n` -/

/-- **Uniform variance agrees with the canonical Boolean variance.**
On `Fin n`, the variance under the uniform product weight is `BooleanCube.boolVariance`. -/
theorem khc_var_half_eq_boolVariance {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) f = BooleanCube.boolVariance f := by
  rw [BooleanCube.boolVariance_eq_expect_sq_sub_sq, BooleanCube.expect_eq_sum_div_two_pow,
    BooleanCube.expect_eq_sum_div_two_pow]
  unfold OSSS.var OSSS.cov
  rw [khc_expect_half, khc_expect_half]
  unfold bnt_uexp
  simp only [Fintype.card_fin, sq]

end Probability
end StatMech
