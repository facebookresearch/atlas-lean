/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Section_1_Introduction.A_EvolutionAlgebra
import Section_2_Preliminaries.A_Preliminaries
import Section_3_SolvableAlgebras.A_Lemma_3_1_Theorem_3_2_SolvableIff
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Remark 3.6: the stabilized term, when an evolution algebra, has trivial `N`

Paper Remark `implicationremark`: let `𝓔` be a finite-dimensional evolution
algebra with `𝓔^(∞)` itself an evolution algebra. Then `N(𝓔^(∞)) = {0}`.

The statement matches the paper, including the ambient evolution-algebra
hypothesis. (The proof uses a natural basis only for the stabilized subtype
`𝓔^(∞)`; on `𝓔` it needs only the structures required to form the derived
series and its induced multiplication.)

Indeed, by Lemma `einftyisidempotent`
`(𝓔^(∞))² = 𝓔^(∞)`, so the squares `{e₁², …, eₙ²}` of a natural basis span
`𝓔^(∞)`; `n` spanning vectors in an `n`-dimensional space are independent.
For `x = ∑ xᵢeᵢ`, cross terms vanish, so `x² = ∑ xᵢ²eᵢ²`; then `x² = 0`
forces `xᵢ² = 0`, hence `xᵢ = 0`.

This discharges the `N(𝓔^(∞)) = 0` hypothesis of paper Corollary 3.4
(`SolvableCorollary.isSolvable_of_no_nonzero_idempotent`) in the case that
the stabilized term is an evolution algebra.

Since the `EvolutionAlgebra` class needs an algebra on the subtype, this
file builds the algebra structure on `↥(derivedSeriesInf K E)` from scratch:
idempotence is exactly closure under multiplication. The module structure
comes solely from the ambient algebra (so the scalar-compatibility
instances are derived, not assumed), and `einfty_is_idempotent` — which
requires an ambient evolution algebra, as in the paper — applies directly.

## Main results

* `EvolutionAlgebras.einfty_absNilpotent_eq_zero`: paper Remark
  `implicationremark` — `N(𝓔^(∞)) = {0}` when `𝓔^(∞)` is an evolution algebra.
-/

namespace EvolutionAlgebras

universe u v

/- `Field` supplies the scalar side and `NonUnitalNonAssocRing` the additive
side; the module structure and scalar compatibility come solely from the
ambient algebra, and every declaration shares the paper's hypotheses
(finite-dimensional evolution algebra). -/
section MainResult
variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
  [NonUnitalNonAssocAlgebra K E] [EvolutionAlgebra K E] [FiniteDimensional K E]

/-- **Helper.** Multiplication on `𝓔^(∞)`: idempotence (`einfty_is_idempotent`) says
`𝓔^(∞)` is closed under `*`, so the product of `E` descends to the subtype.
The basis for the algebra structure below. -/
instance einfMul : Mul ↥(derivedSeriesInf K E) where
  mul x y :=
    ⟨x.1 * y.1, by
      have hmem : x.1 * y.1 ∈ square K E (derivedSeriesInf K E) :=
        Submodule.subset_span ⟨x.1, x.2, y.1, y.2, rfl⟩
      rwa [(einfty_is_idempotent K E).1] at hmem⟩

/-- Helper result: coercion unfolds the product on `𝓔^(∞)` definitionally (it holds by
`rfl`). -/
@[simp]
theorem einf_coe_mul (x y : ↥(derivedSeriesInf K E)) :
    ((x * y : ↥(derivedSeriesInf K E)) : E) = x.1 * y.1 :=
  rfl

/-- Helper result: `𝓔^(∞)` as a non-associative semiring: additive structure from the
submodule API, multiplication from `einfMul`. -/
instance einfSemiring :
    NonUnitalNonAssocSemiring ↥(derivedSeriesInf K E) where
  toAddCommMonoid := inferInstance
  toMul := inferInstance
  left_distrib := by
    intro a b c
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_add, mul_add]
  right_distrib := by
    intro a b c
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_add, add_mul]
  zero_mul := by
    intro a
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_zero, zero_mul]
  mul_zero := by
    intro a
    apply Subtype.ext
    simp only [einf_coe_mul, Submodule.coe_zero, mul_zero]

/-- Helper result: scalar associativity descends to `𝓔^(∞)` (coercion is `rfl`). -/
instance einfTower :
    IsScalarTower K ↥(derivedSeriesInf K E) ↥(derivedSeriesInf K E) :=
  ⟨fun x y z => Subtype.ext (smul_assoc x y.1 z.1)⟩

/-- Helper result: scalar commutativity descends to `𝓔^(∞)` (coercion is `rfl`). -/
instance einfComm :
    SMulCommClass K ↥(derivedSeriesInf K E) ↥(derivedSeriesInf K E) :=
  ⟨fun x y z => Subtype.ext (smul_comm x y.1 z.1)⟩

/-- Helper result: the algebra bundle on `𝓔^(∞)`, assembled from the structures above
(cf. the bundle instance for `Counterexample`). -/
instance einfAlgebra : NonUnitalNonAssocAlgebra K ↥(derivedSeriesInf K E) where
  toModule := inferInstance
  toIsScalarTower := inferInstance
  toSMulCommClass := inferInstance

/-- **Paper Remark 3.6.** Paper Remark `implicationremark`: for a finite-dimensional
evolution algebra `𝓔` whose stabilized term `𝓔^(∞)` is itself an evolution
algebra, `N(𝓔^(∞)) = {0}`.

Proof (paper): by Lemma `einftyisidempotent`, `(𝓔^(∞))² = 𝓔^(∞)`, so the
squares of a natural basis span `𝓔^(∞)` (`hspan`); `n` spanning vectors in an
`n`-dimensional space are independent (`hsq_indep`). For `x = ∑ xᵢeᵢ`, cross
terms vanish (`expand`), so `x² = ∑ xᵢ²eᵢ²`; `x² = 0` forces each `xᵢ² = 0`,
hence `xᵢ = 0`.

Scalar compatibility is supplied by the ambient algebra structure. -/
theorem einfty_absNilpotent_eq_zero
    [EvolutionAlgebra K ↥(derivedSeriesInf K E)] :
    absNilpotent K E (derivedSeriesInf K E) = {0} := by
  -- The natural basis of `𝓔^(∞)`, viewed in the subtype.
  obtain ⟨n, b, horth⟩ :=
    EvolutionAlgebra.exists_orthogonal_basis K ↥(derivedSeriesInf K E)
  -- Squares of the basis vectors.
  set sq : Fin n → ↥(derivedSeriesInf K E) := fun i => b i * b i
  -- Products expand diagonally: cross terms vanish by orthogonality
  -- (`smul_mul_smul` computation, as in `IdempotentIff.smul_mul_smul`).
  have expand : ∀ u w : ↥(derivedSeriesInf K E),
      u * w = ∑ i, ((b.repr u i * b.repr w i) • sq i) := by
    intro u w
    conv_lhs => rw [← b.sum_repr u, ← b.sum_repr w, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    · intro j _ hji
      have hne : i ≠ j := fun h => hji h.symm
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, horth i j hne, smul_zero]
    · intro hcon
      exact (hcon (Finset.mem_univ i)).elim
  -- The squares span `𝓔^(∞)`: every vector is a combination of products
  -- (idempotence), and every product expands in the squares.
  have hspan : Submodule.span K (Set.range sq) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hmem : (v : E) ∈ square K E (derivedSeriesInf K E) :=
      (einfty_is_idempotent K E).1.symm ▸ v.2
    have lift : ∀ z : E, z ∈ square K E (derivedSeriesInf K E) →
        ∃ w : ↥(derivedSeriesInf K E), (w : E) = z ∧
          w ∈ Submodule.span K (Set.range sq) := by
      intro z hz
      unfold square at hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, w, hw, rfl⟩ := hx
        refine ⟨⟨u, hu⟩ * ⟨w, hw⟩, rfl, ?_⟩
        rw [expand]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      | zero => exact ⟨0, rfl, Submodule.zero_mem _⟩
      | add x y _ _ ihx ihy =>
        obtain ⟨wx, rfl, hwx⟩ := ihx
        obtain ⟨wy, rfl, hwy⟩ := ihy
        exact ⟨wx + wy, rfl, Submodule.add_mem _ hwx hwy⟩
      | smul a x _ ih =>
        obtain ⟨w, rfl, hw⟩ := ih
        exact ⟨a • w, rfl, Submodule.smul_mem _ _ hw⟩
    obtain ⟨w, hw, hws⟩ := lift _ hmem
    have hvw : w = v := Subtype.ext hw
    rwa [hvw] at hws
  -- `n` spanning vectors in an `n`-dimensional space are independent.
  have hcard : Fintype.card (Fin n) =
      Module.finrank K ↥(derivedSeriesInf K E) := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsq_indep : LinearIndependent K sq :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [hspan]) hcard
  -- Coordinates: `x² = 0` forces every coordinate square to `0`.
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · -- `0 ∈ N(𝓔^(∞))`.
    simp only [absNilpotent, Set.mem_ofPred_eq]
    refine ⟨Submodule.zero_mem _, ?_⟩
    change (0 : E) * (0 : E) = (0 : E)
    exact mul_zero _
  · -- Every `y ∈ N(𝓔^(∞))` is `0`.
    intro y hy
    simp only [absNilpotent, Set.mem_ofPred_eq] at hy
    obtain ⟨hmem, habs⟩ := hy
    have habs0 : y * y = 0 := habs
    have hw0 : (⟨y, hmem⟩ : ↥(derivedSeriesInf K E)) * ⟨y, hmem⟩ = 0 := by
      apply Subtype.ext
      exact habs0
    rw [expand] at hw0
    have hcoord : ∀ j, b.repr (⟨y, hmem⟩ : ↥(derivedSeriesInf K E)) j *
        b.repr ⟨y, hmem⟩ j = 0 :=
      fun j => (linearIndependent_iff'.mp hsq_indep) Finset.univ _ hw0 j
        (Finset.mem_univ j)
    have hrep : ∀ j, b.repr (⟨y, hmem⟩ : ↥(derivedSeriesInf K E)) j = 0 :=
      fun j => mul_self_eq_zero.mp (hcoord j)
    have hww : (⟨y, hmem⟩ : ↥(derivedSeriesInf K E)) = 0 := by
      conv_lhs => rw [← b.sum_repr ⟨y, hmem⟩]
      simp [hrep]
    exact congrArg Subtype.val hww

end MainResult

end EvolutionAlgebras
