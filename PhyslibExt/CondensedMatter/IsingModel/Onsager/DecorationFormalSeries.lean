/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationTransitionWeights
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!

# The formal Kac-Ward series in decorated edge variables

The Kac-Ward root as a multivariate formal power series in one variable per decorated edge, and the
formal Kac-Ward identity.

## i. Overview

Each Kac-Ward transition is a monomial: the product of the variables of the decorated edges it
traverses, times its turning and boundary phase. A closed walk contributes the product of its
transition monomials, and the formal logarithm is
`-(1/2) ∑ₙ (∑ closed walks of length n + 1) / (n + 1)`, organized by monomial (each coefficient is a
finite sum since every transition has positive degree). Its formal exponential is the formal
Kac-Ward root. The decorated spin polynomial `∑_D χ(D) x^D` lists the decorated even subgraphs, and
the formal Kac-Ward identity states that the formal root equals that polynomial for every spin
structure. Formal series are evaluated at weights by `ons_mvSeriesEval`.

## ii. Key results

- `ons_decFormalTransition` : the monomial of a transition
- `ons_decFormalLog` : the formal logarithm of the Kac-Ward root
- `ons_decFormalRoot` : the formal Kac-Ward root
- `ons_decoratedSpinPolynomial` : the decorated spin polynomial
- `ons_mvSeriesEval` : evaluation of a formal series at weights
- `ons_decoratedFormalKacWardIdentity` : the formal Kac-Ward identity

## iii. Table of contents

- A. Transition monomials
- B. Total degree
- C. The formal logarithm and root
- D. The decorated spin polynomial
- E. Evaluation

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators Finset

/-! ## A. Transition monomials -/

/-- Decorated edges, used as the variables of the formal series. -/
abbrev ons_DecEdge (L : ℕ) := Sym2 (ons_Dart L)

/-- The exponent of a transition: one for the external edge at `d₁` and one for each internal edge
on the path at the site of `d₂`. -/
noncomputable def ons_decTransitionExponent
    (L : ℕ) (d₂ d₁ : ons_Dart L) : ons_DecEdge L →₀ ℕ := by
  classical
  exact Finsupp.single s(d₁, ons_dartRev L d₁) 1 +
    ∑ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
      Finsupp.single (ons_decChainEdge d₂.1 i) 1

/-- The scalar of a transition: its boundary phase times its turn weight, or `0` if `d₂` does not
start at the head of `d₁`. -/
noncomputable def ons_decTransitionScalar
    (L : ℕ) (omega u v : ℂ) (d₂ d₁ : ons_Dart L) : ℂ :=
  if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
    ons_dirPhase u v d₁.2 * ons_turnW omega d₁.2 d₂.2
  else 0

/-- The monomial of the transition from `d₁` to `d₂`. -/
noncomputable def ons_decFormalTransition
    (L : ℕ) (omega u v : ℂ) (d₂ d₁ : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  MvPowerSeries.monomial (ons_decTransitionExponent L d₂ d₁)
    (ons_decTransitionScalar L omega u v d₂ d₁)

/-- The exponent of a closed walk: the sum of the exponents of its transitions. -/
noncomputable def ons_decLoopExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, ons_decTransitionExponent L (d k) (d (k + 1))

/-- The scalar of a closed walk: the product of the scalars of its transitions. -/
noncomputable def ons_decLoopScalar
    (L : ℕ) (omega u v : ℂ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) : ℂ :=
  ∏ k, ons_decTransitionScalar L omega u v (d k) (d (k + 1))

/-! ## B. Total degree -/

/-- The total degree `∑ m e` of an exponent; this is `Finsupp.degree`. -/
def ons_finsuppTotalDegree {E : Type*} (m : E →₀ ℕ) : ℕ :=
  m.sum fun _ n ↦ n

/-- `ons_finsuppTotalDegree` agrees with Mathlib's `Finsupp.degree`. -/
lemma ons_finsuppTotalDegree_eq_degree {E : Type*} (m : E →₀ ℕ) :
    ons_finsuppTotalDegree m = m.degree :=
  rfl

lemma ons_finsuppTotalDegree_add
    {E : Type*} [DecidableEq E] (m n : E →₀ ℕ) :
    ons_finsuppTotalDegree (m + n) =
      ons_finsuppTotalDegree m + ons_finsuppTotalDegree n := by
  unfold ons_finsuppTotalDegree
  rw [Finsupp.sum_add_index]
  · simp
  · simp

@[simp] lemma ons_finsuppTotalDegree_single
    {E : Type*} [DecidableEq E] (edge : E) (n : ℕ) :
    ons_finsuppTotalDegree (Finsupp.single edge n) = n := by
  unfold ons_finsuppTotalDegree
  rw [Finsupp.sum_single_index]
  simp

lemma ons_finsuppTotalDegree_finset_sum
    {I E : Type*} [Fintype I] [DecidableEq E] (m : I → E →₀ ℕ) :
    ons_finsuppTotalDegree (∑ i, m i) =
      ∑ i, ons_finsuppTotalDegree (m i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [ons_finsuppTotalDegree]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ons_finsuppTotalDegree_add, ih]

lemma ons_decTransitionExponent_totalDegree_pos
    (L : ℕ) (d₂ d₁ : ons_Dart L) :
    0 < ons_finsuppTotalDegree
      (ons_decTransitionExponent L d₂ d₁) := by
  unfold ons_decTransitionExponent
  rw [ons_finsuppTotalDegree_add,
    ons_finsuppTotalDegree_single]
  omega

lemma ons_decLoopExponent_length_le
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    n ≤ ons_finsuppTotalDegree (ons_decLoopExponent L d) := by
  unfold ons_decLoopExponent
  rw [ons_finsuppTotalDegree_finset_sum]
  calc
    n = ∑ _k : Fin n, 1 := by simp
    _ ≤ ∑ k : Fin n,
        ons_finsuppTotalDegree
          (ons_decTransitionExponent L (d k) (d (k + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact ons_decTransitionExponent_totalDegree_pos L _ _

/-! ## C. The formal logarithm and root -/

/-- The coefficient of `x^m` in the formal logarithm: minus one half of the sum over closed walks of
length `r + 1 ≤ deg m` with exponent `m` of their scalars divided by `r + 1`. -/
noncomputable def ons_decFormalLogCoeff
    (L : ℕ) [NeZero L] (omega u v : ℂ)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) / ((r : ℂ) + 1)) / 2

/-- The formal logarithm of the Kac-Ward root. -/
noncomputable def ons_decFormalLog
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalLogCoeff L omega u v

lemma ons_decFormalLogCoeff_eq_tsum
    (L : ℕ) [NeZero L] (omega u v : ℂ)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalLogCoeff L omega u v m =
      -(∑' r : ℕ,
        (∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L omega u v d
          else 0) / ((r : ℂ) + 1)) / 2 := by
  unfold ons_decFormalLogCoeff
  congr 2
  symm
  apply tsum_eq_sum
  intro r hr
  rw [Finset.mem_range, not_lt] at hr
  have hsum :
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [ite_eq_right]
    intro heq
    have hlen := ons_decLoopExponent_length_le L d
    rw [heq] at hlen
    omega
  rw [hsum, zero_div]

lemma ons_decFormalLog_constantCoeff
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries.constantCoeff
      (ons_decFormalLog L omega u v) = 0 := by
  change ons_decFormalLogCoeff L omega u v 0 = 0
  simp [ons_decFormalLogCoeff,
    ons_finsuppTotalDegree]

lemma ons_decFormalLog_hasSubst
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    PowerSeries.HasSubst (ons_decFormalLog L omega u v) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalLog_constantCoeff L omega u v)

/-- The formal Kac-Ward root: the formal exponential of `ons_decFormalLog`. -/
noncomputable def ons_decFormalRoot
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  PowerSeries.subst (ons_decFormalLog L omega u v)
    (PowerSeries.exp ℂ)

/-! ## D. The decorated spin polynomial -/

/-- The squarefree exponent `∑_{e ∈ S} single e 1` of a set of variables. -/
noncomputable def ons_finsetExponent
    {E : Type*} [DecidableEq E] (S : Finset E) : E →₀ ℕ :=
  ∑ edge ∈ S, Finsupp.single edge 1

lemma ons_finsetExponent_insert
    {E : Type*} [DecidableEq E] (S : Finset E) (edge : E)
    (hedge : edge ∉ S) :
    ons_finsetExponent (insert edge S) =
      Finsupp.single edge 1 + ons_finsetExponent S := by
  classical
  simp [ons_finsetExponent, Finset.sum_insert hedge]

lemma ons_finsetExponent_image
    {E F : Type*} [DecidableEq E] [DecidableEq F]
    (S : Finset E) (f : E → F) (hf : Set.InjOn f S) :
    ons_finsetExponent (S.image f) =
      ∑ edge ∈ S, Finsupp.single (f edge) 1 := by
  classical
  unfold ons_finsetExponent
  rw [Finset.sum_image]
  exact hf

@[simp] lemma ons_finsetExponent_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (edge : E) :
    ons_finsetExponent S edge = if edge ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_finsetExponent]
  | @insert e S he ih =>
      have hexp : ons_finsetExponent (insert e S) =
          Finsupp.single e 1 + ons_finsetExponent S := by
        exact ons_finsetExponent_insert S e he
      rw [hexp, Finsupp.add_apply, ih]
      by_cases hedge : edge = e
      · subst edge
        simp [he]
      · simp [hedge]

lemma ons_finsetExponent_injective
    {E : Type*} [DecidableEq E] :
    Function.Injective (ons_finsetExponent : Finset E → E →₀ ℕ) := by
  intro S T h
  ext edge
  constructor
  · intro hS
    have happ := DFunLike.congr_fun h edge
    rw [ons_finsetExponent_apply, ons_finsetExponent_apply,
      ite_eq_left hS] at happ
    by_contra hT
    rw [ite_eq_right hT] at happ
    omega
  · intro hT
    have happ := DFunLike.congr_fun h edge
    rw [ons_finsetExponent_apply, ons_finsetExponent_apply,
      ite_eq_left hT] at happ
    by_contra hS
    rw [ite_eq_right hS] at happ
    omega

lemma ons_finsetExponent_prod
    {E R : Type*} [DecidableEq E] [CommMonoid R]
    (S : Finset E) (weight : E → R) :
    (ons_finsetExponent S).prod (fun edge n ↦ weight edge ^ n) =
      ∏ edge ∈ S, weight edge := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_finsetExponent]
  | @insert edge S hedge ih =>
      have hexp : ons_finsetExponent (insert edge S) =
          Finsupp.single edge 1 + ons_finsetExponent S := by
        exact ons_finsetExponent_insert S edge hedge
      rw [hexp, Finsupp.prod_add_index]
      · rw [Finsupp.prod_single_index]
        · simp [ih, hedge]
        · simp
      · intro e he
        simp
      · intro e he n₁ n₂
        simp [pow_add]

/-- The decorated spin polynomial `∑_D χ_{a,b}(hom D) ∏_{e ∈ D} x_e` over decorated even subgraphs.
-/
noncomputable def ons_decoratedSpinPolynomial
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) :
    MvPolynomial (ons_DecEdge L) ℂ :=
  ∑ D : ons_DecoratedEvenSubgraph L,
    MvPolynomial.monomial (ons_finsetExponent D.1)
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ)

lemma ons_decoratedSpinPolynomial_eval
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (decWeight : ons_DecEdge L → ℂ) :
    MvPolynomial.eval decWeight (ons_decoratedSpinPolynomial L a b) =
      ons_decoratedFullWeightedSpinSum L decWeight a b := by
  classical
  unfold ons_decoratedSpinPolynomial ons_decoratedFullWeightedSpinSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]

lemma ons_decoratedSpinPolynomial_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) :
    (ons_decoratedSpinPolynomial L a b).coeff
        (ons_finsetExponent D.1) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
  classical
  unfold ons_decoratedSpinPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [Fintype.sum_eq_single D]
  · rw [MvPolynomial.coeff_monomial]
    simp
  · intro D' hne
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · have hval : D'.1 = D.1 :=
        ons_finsetExponent_injective heq
      exact (hne (Subtype.ext hval)).elim
    · rfl

/-! ## E. Evaluation -/

/-- Evaluation of a multivariate formal power series at weights, as the sum
`∑_m coeff_m · weight^m`. -/
noncomputable def ons_mvSeriesEval
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) : ℂ :=
  ∑' m : E →₀ ℕ,
    MvPowerSeries.coeff m series *
      m.prod (fun edge n ↦ weight edge ^ n)

lemma ons_mvSeriesEval_coe
    {E : Type*} (p : MvPolynomial E ℂ) (weight : E → ℂ) :
    ons_mvSeriesEval (p : MvPowerSeries E ℂ) weight =
      MvPolynomial.eval weight p := by
  classical
  unfold ons_mvSeriesEval
  rw [tsum_eq_sum (s := p.support)]
  · rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.coeff_coe, Finsupp.prod]
  · intro m hm
    rw [MvPolynomial.coeff_coe]
    have hcoeff : p.coeff m = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    rw [hcoeff, zero_mul]

/-- The formal Kac-Ward identity on the `L × L` torus: for every spin structure, the formal Kac-Ward
root equals the decorated spin polynomial. -/
def ons_decoratedFormalKacWardIdentity
    (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ a b : Fin 2,
    ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      (ons_decoratedSpinPolynomial L a b :
        MvPowerSeries (ons_DecEdge L) ℂ)

lemma ons_decoratedFormalKacWardIdentity_eval
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L)
    (a b : Fin 2) (decWeight : ons_DecEdge L → ℂ) :
    ons_mvSeriesEval
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) decWeight =
      ons_decoratedFullWeightedSpinSum L decWeight a b := by
  rw [hformal a b, ons_mvSeriesEval_coe,
    ons_decoratedSpinPolynomial_eval]

end StatMech.Onsager
