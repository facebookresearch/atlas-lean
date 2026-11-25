/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Order.ProjIcc

/-! # An orthogonal polynomial Hilbert basis on a closed interval -/

@[expose] public section

open MeasureTheory Set Polynomial Submodule InnerProductSpace
open scoped ENNReal InnerProductSpace

noncomputable section

namespace MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasisWanted

private abbrev interval : Set ℝ := Icc (-1 : ℝ) 1
private abbrev μ : Measure ℝ := volume.restrict interval
private abbrev H := Lp ℝ 2 μ

private def clamp : C(ℝ, interval) :=
  ⟨Set.projIcc (-1 : ℝ) 1 (by norm_num), continuous_projIcc⟩

/-- Extend continuously by constant values on either side of the interval. -/
private def extendInterval : C(interval, ℝ) →L[ℝ] BoundedContinuousFunction ℝ ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => (BoundedContinuousFunction.mkOfCompact f).compContinuous clamp
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro c f; ext x; rfl }
    1 (fun f => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun x =>
        ContinuousMap.norm_coe_le_norm f (clamp x))

private def intervalLp : C(interval, ℝ) →L[ℝ] H :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).comp extendInterval

private theorem ae_intervalLp (f : C(interval, ℝ)) :
    ∀ᵐ x ∂μ, ∀ hx : x ∈ interval, (intervalLp f) x = f ⟨x, hx⟩ := by
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (extendInterval f)] with x hx hxi
  change ((BoundedContinuousFunction.toLp 2 μ ℝ (extendInterval f) : H) x) = f ⟨x, hxi⟩
  rw [hx]
  change f (clamp x) = f ⟨x, hxi⟩
  rw [show clamp x = ⟨x, hxi⟩ from Set.projIcc_of_mem (by norm_num) hxi]

/-- Every bounded continuous function on the line agrees a.e. with the extension of its
restriction to the interval. -/
private theorem dense_intervalLp : DenseRange intervalLp := by
  have h := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (p := 2) (by norm_num)
  apply h.mono
  rintro v ⟨f, rfl⟩
  use f.toContinuousMap.restrict interval
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ ℝ f,
    ae_intervalLp (f.toContinuousMap.restrict interval),
    ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))]
    with x hfx hL hxi
  exact (hL hxi).trans hfx.symm

private def polynomialLp : Polynomial ℝ →ₗ[ℝ] H :=
  intervalLp.toLinearMap.comp (Polynomial.toContinuousMapOnAlgHom interval).toLinearMap

private theorem ae_polynomialLp (p : Polynomial ℝ) :
    (fun x => (polynomialLp p) x) =ᵐ[μ] fun x => p.eval x := by
  filter_upwards [ae_intervalLp (Polynomial.toContinuousMapOnAlgHom interval p),
    ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))]
    with x hx hxi
  exact hx hxi

private theorem dense_polynomialLp : DenseRange polynomialLp := by
  have hd : DenseRange (Polynomial.toContinuousMapOnAlgHom (R := ℝ) interval) := by
    rw [DenseRange, ← polynomialFunctions_coe]
    intro f
    have htop := polynomialFunctions_closure_eq_top (-1 : ℝ) 1
    change f ∈ (polynomialFunctions interval).topologicalClosure
    rw [htop]
    trivial
  exact dense_intervalLp.comp hd intervalLp.continuous

/-- A polynomial representing zero vanishes on the open interval, and so is zero. -/
private theorem injective_polynomialLp : Function.Injective polynomialLp := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  have heq : (fun x => p.eval x) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    have h₁ := (ae_polynomialLp p).symm
    have hp' : polynomialLp p = polynomialLp 0 := by simpa only [map_zero] using hp
    have h₂ : (fun x => p.eval x) =ᵐ[μ] (fun x => (polynomialLp 0) x) := by
      simpa only [hp'] using h₁
    simpa only [Polynomial.eval_zero] using h₂.trans (ae_polynomialLp 0)
  have hsmall : (fun x => p.eval x) =ᵐ[(volume : Measure ℝ).restrict (Ioo (-1) 1)] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq
  have hz : EqOn (fun x => p.eval x) (fun _ => 0) (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hsmall isOpen_Ioo p.continuous.continuousOn
      continuous_const.continuousOn
  by_contra hne
  exact (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num))
    ((Polynomial.finite_setOfPred_isRoot hne).subset fun x hx => hz hx)

private def monomialFamily {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Polynomial ℝ →ₗ[ℝ] E) (n : ℕ) : E := A (X ^ n)

private theorem monomialFamily_as_basis {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Polynomial ℝ →ₗ[ℝ] E) :
    monomialFamily A = A ∘ Polynomial.basisMonomials ℝ := by
  funext n
  simp only [monomialFamily, Polynomial.X_pow_eq_monomial, Function.comp_apply,
    Polynomial.coe_basisMonomials]

private theorem span_monomialFamily {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Polynomial ℝ →ₗ[ℝ] E) :
    span ℝ (range (monomialFamily A)) = LinearMap.range A := by
  rw [monomialFamily_as_basis, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq,
    Submodule.map_top]

/-- Subtracting earlier projections from `X ^ n` leaves degree `n`. -/
private theorem exists_poly_gramSchmidt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : Polynomial ℝ →ₗ[ℝ] E) (n : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = n ∧ A p = gramSchmidt ℝ (monomialFamily A) n := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    let q (i : ℕ) : Polynomial ℝ := if hi : i < n then Classical.choose (ih i hi) else 0
    let w := gramSchmidt ℝ (monomialFamily A)
    let c (i : ℕ) : ℝ := ⟪w i, monomialFamily A n⟫_ℝ / ‖w i‖ ^ 2
    let S : Polynomial ℝ := ∑ i ∈ Finset.Iio n, c i • q i
    have hdeg (i : ℕ) (hi : i < n) : (q i).natDegree = i := by
      simpa only [q, dite_eq_left hi] using (Classical.choose_spec (ih i hi)).1
    have him (i : ℕ) (hi : i < n) : A (q i) = w i := by
      simpa only [q, dite_eq_left hi, w] using (Classical.choose_spec (ih i hi)).2
    have hS (m : ℕ) (hm : n ≤ m) : S.coeff m = 0 := by
      simp only [S, finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      have hin := Finset.mem_Iio.mp hi
      apply coeff_eq_zero_of_natDegree_lt
      exact (natDegree_smul_le _ _).trans_lt (by rw [hdeg i hin]; omega)
    refine ⟨X ^ n - S, le_antisymm ?_ ?_, ?_⟩
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      simp [coeff_X_pow, hS m hm.le, ne_of_gt hm]
    · apply le_natDegree_of_ne_zero
      simp [coeff_X_pow, hS n le_rfl]
    · simp only [map_sub, S, map_sum, map_smul]
      have heq := gramSchmidt_def'' ℝ (monomialFamily A) n
      change monomialFamily A n = w n + ∑ i ∈ Finset.Iio n, c i • w i at heq
      change monomialFamily A n - ∑ i ∈ Finset.Iio n, c i • A (q i) = w n
      rw [show (∑ i ∈ Finset.Iio n, c i • A (q i)) = ∑ i ∈ Finset.Iio n, c i • w i from
        Finset.sum_congr rfl fun i hi => by rw [him i (Finset.mem_Iio.mp hi)]]
      exact (eq_sub_of_add_eq heq.symm).symm

private theorem exists_poly_gramSchmidtNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : Polynomial ℝ →ₗ[ℝ] E) (hA : Function.Injective A) (n : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = n ∧ A p = gramSchmidtNormed ℝ (monomialFamily A) n := by
  have hind : LinearIndependent ℝ (monomialFamily A) := by
    rw [monomialFamily_as_basis]
    exact (Polynomial.basisMonomials ℝ).linearIndependent.map' A (LinearMap.ker_eq_bot.mpr hA)
  obtain ⟨p, hp, hAp⟩ := exists_poly_gramSchmidt A n
  let c : ℝ := ‖gramSchmidt ℝ (monomialFamily A) n‖⁻¹
  have hc : c ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero n hind))
  refine ⟨c • p, (natDegree_smul p hc).trans hp, ?_⟩
  rw [map_smul, hAp, gramSchmidtNormed]
  simp only [c, RCLike.ofReal_real_eq_id, id_eq]

/-- **Hilbert basis of orthogonal polynomials on $[-1, 1]$.** Let $L^2([-1, 1])$ be the real
Hilbert space of square-integrable real-valued functions on $[-1, 1]$ with respect to
Lebesgue measure. There is a Hilbert basis $(b_n)_{n \in \mathbb{N}}$ of $L^2([-1, 1])$ such
that for every $n \in \mathbb{N}$ there is a real polynomial $q_n$ of degree exactly $n$ (for
$n = 0$, a constant polynomial) with $b_n(x) = q_n(x)$ for almost every $x \in [-1, 1]$.

The normalized Legendre polynomials form such a basis.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Topology / Hilbert spaces", entry
  "example, classical Hilbert bases of orthogonal polynomials" (currently
  missing: empty entry, no Mathlib declaration).
- NIST Digital Library of Mathematical Functions, §18.3, Table 18.3.1 (Legendre polynomials:
  weight `1` on `(-1, 1)`, `∫ P_n ^ 2 = 2 / (2n + 1)`).
- E. Kreyszig, *Introductory Functional Analysis with Applications*, Wiley, 1978, §3.6
  ("Total Orthonormal Sets and Sequences") and §3.7 ("Legendre, Hermite and Laguerre
  Polynomials": the normalized Legendre polynomials are a total orthonormal sequence in
  `L²[-1, 1]`).
- https://en.wikipedia.org/wiki/Legendre_polynomials#Orthogonality_and_completeness
-/
public theorem orthogonalPolynomial_hilbertBasis :
    ∃ B : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))),
      ∀ n : ℕ, ∃ q : Polynomial ℝ, q.natDegree = n ∧
        ∀ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)),
          (B n) x = Polynomial.aeval x q := by
  let v := monomialFamily polynomialLp
  have hlin : LinearIndependent ℝ v := by
    dsimp only [v]
    rw [monomialFamily_as_basis]
    exact (Polynomial.basisMonomials ℝ).linearIndependent.map' polynomialLp
      (LinearMap.ker_eq_bot.mpr injective_polynomialLp)
  have hon := gramSchmidtNormed_orthonormal hlin
  have hspan : ⊤ ≤ (span ℝ (range (gramSchmidtNormed ℝ v))).topologicalClosure := by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt]
    change ⊤ ≤ (span ℝ (range (monomialFamily polynomialLp))).topologicalClosure
    rw [span_monomialFamily]
    intro x _
    change x ∈ closure (Set.range polynomialLp)
    exact dense_polynomialLp x
  refine ⟨HilbertBasis.mk hon hspan, fun n => ?_⟩
  obtain ⟨p, hp, hEq⟩ := exists_poly_gramSchmidtNormed polynomialLp injective_polynomialLp n
  refine ⟨p, hp, ?_⟩
  have hB : (HilbertBasis.mk hon hspan) n = polynomialLp p := by
    rw [show (HilbertBasis.mk hon hspan) n = gramSchmidtNormed ℝ v n from
      congrFun (HilbertBasis.coe_mk hon hspan) n]
    exact hEq.symm
  rw [hB]
  exact ae_polynomialLp p

end MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasisWanted
