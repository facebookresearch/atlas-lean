/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Laurent
public import MathlibExt.NumberTheory.Padics.ComplexInvariants
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-!
# The Hodge–Tate ring `B_HT`

Let `K` be a finite extension of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`, let `ℂ_p` be the completion of
`ℚ̄_p`, `G = Gal(ℚ̄_p / ℚ_p)` and `G_K = Gal(ℚ̄_p / K)` (`K.fixingSubgroup`). The **Hodge–Tate
ring** is the graded ring `B_HT = ⨁_{i ∈ ℤ} ℂ_p(i) = ℂ_p[t, t⁻¹]`, where `t` stands for a basis of
`ℤ_p(1)`: here Mathlib's ring `LaurentPolynomial ℂ_[p]` of Laurent polynomials over `ℂ_p`, graded
by the degree in `t` (`AddMonoidAlgebra.grade`). The group `G` acts on it by `ℚ_p`-algebra
automorphisms, `σ (c tⁱ) = σ(c) χ(σ)ⁱ tⁱ`, where `σ(c) = completionGalois p σ c` and
`χ(σ) = cyclotomicScalar p σ` is the `p`-adic cyclotomic character
(`PadicComplex.hodgeTateAction`, a homomorphism `G →* (B_HT →ₐ[ℚ_p] B_HT)`). This is
J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §6.1, Definition 6.1, and
J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.5 p. 73.

## Main results

* `PadicComplex.coeff_hodgeTateAction`: the coefficient of `tⁿ` in `σ f` is `χ(σ)ⁿ σ(fₙ)`; so the
  action preserves the grading (`PadicComplex.hodgeTateAction_mem_grade_iff`).
* `PadicComplex.fixedSubalgebra_hodgeTateAction`: `B_HT^{G_K} = K` (J.-M. Fontaine,
  *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §3.5 p. 141), with
  the isomorphism `PadicComplex.hodgeTateFixedSubalgebraEquiv : K ≃ B_HT^{G_K}`; similarly
  `ℂ_p^{G_K} = K` (`PadicComplex.fixedSubalgebra_galoisAlgHom`).
* `PadicComplex.isRegularPeriodRing_hodgeTateAction`: `B_HT` is `(ℚ_p, G_K)`-regular in the sense of
  `Representation.IsRegularPeriodRing` (Fontaine–Ouyang, Proposition 6.2; Fontaine, *op. cit.*,
  Exposé III, Proposition 3.6 p. 141).

## Proof

Everything comes from Tate's theorems `ℂ_p^{G_K} = K` and `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`
(`PadicComplex.fixedPoints_eq_range`, `PadicComplex.fixedPoints_twist_eq_singleton_zero`),
applied to the coefficients of elements of `B_HT`:

* (i) `B_HT` is a domain, by Mathlib's instance for Laurent polynomials over a field.
* (iii) If `b ≠ 0` spans a `G_K`-stable line, then for nonzero coefficients `bₙ` and `b_k` the
  ratio `bₙ / b_k` lies in `ℂ_p(n - k)^{G_K}`, so `n = k`: `b = b_k tᵏ` is a monomial, hence a unit
  (`PadicComplex.eq_single_of_forall_exists_smul_eq`).
* (ii) Fontaine embeds `B_HT` in the field `ℂ_p((t))`, whose invariants are `K`. We argue instead
  in the fraction field of `B_HT`, by induction on the number of nonzero coefficients of a
  denominator (`PadicComplex.mem_range_of_forall_fractionRingAction_eq`), using the monomial
  lemma of (iii).

As in `MathlibExt.RepresentationTheory.AdmissibleRepresentation`, the actions are abstract group
actions: no topology on `G` or on `B_HT` is involved.
-/

@[expose] public noncomputable section

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- **The Galois action on `ℂ_p` by algebra maps**: `σ ↦ completionGalois p σ`, as a homomorphism
from `Gal(ℚ̄_p / ℚ_p)` to the monoid of `ℚ_p`-algebra endomorphisms of `ℂ_p`. -/
def galoisAlgHom : Galois p →* (ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p]) :=
  (Units.coeHom _).comp
    ((AlgEquiv.algHomUnitsEquiv ℚ_[p] ℂ_[p]).symm.toMonoidHom.comp (completionGaloisHom p))

/-- `galoisAlgHom p σ` acts on `ℂ_p` by `completionGalois p σ`. -/
@[simp]
theorem galoisAlgHom_apply (σ : Galois p) (x : ℂ_[p]) :
    galoisAlgHom p σ x = completionGalois p σ x :=
  rfl

/-- **The Galois action on the Hodge–Tate ring `B_HT = ℂ_p[t, t⁻¹]`** (Fontaine–Ouyang,
Definition 6.1): `σ ∈ Gal(ℚ̄_p / ℚ_p)` acts on `LaurentPolynomial ℂ_[p]` by the `ℚ_p`-algebra map
`c tⁿ ↦ σ(c) χ(σ)ⁿ tⁿ`, where `σ(c) = completionGalois p σ c` and `χ(σ) = cyclotomicScalar p σ` is
the `p`-adic cyclotomic character. -/
def hodgeTateAction : Galois p →* (ℂ_[p][T;T⁻¹] →ₐ[ℚ_[p]] ℂ_[p][T;T⁻¹]) :=
  let f : Galois p → ℂ_[p][T;T⁻¹] →ₐ[ℚ_[p]] ℂ_[p][T;T⁻¹] := fun σ =>
    ((AddMonoidAlgebra.lift ℂ_[p] ℂ_[p][T;T⁻¹] ℤ
      { toFun := fun n => cyclotomicScalar p σ ^ n.toAdd • T n.toAdd
        map_one' := by simp
        map_mul' := fun m n => by
          rw [toAdd_mul, zpow_add₀ (cyclotomicScalar_ne_zero p σ), T_add, smul_mul_smul_comm] }
      ).restrictScalars ℚ_[p]).comp
      (AddMonoidAlgebra.mapAlgHom ℤ (completionGalois p σ).toAlgHom)
  have hf (σ : Galois p) (n : ℤ) (c : ℂ_[p]) :
      f σ (AddMonoidAlgebra.single n c) =
        AddMonoidAlgebra.single n (cyclotomicScalar p σ ^ n • completionGalois p σ c) := by
    simp only [f, AlgHom.comp_apply, AddMonoidAlgebra.mapAlgHom_single,
      AlgHom.restrictScalars_apply, AddMonoidAlgebra.lift_single, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd, T, AddMonoidAlgebra.smul_single, AlgEquiv.coe_toAlgHom]
    rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm]
  { toFun := f
    map_one' := AlgHom.ext fun x => by
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | single n c =>
        rw [hf, AlgHom.one_apply, completionGalois_one_apply, cyclotomicScalar_one, one_zpow,
          one_smul]
    map_mul' := fun σ τ => AlgHom.ext fun x => by
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | single n c =>
        rw [AlgHom.mul_apply, hf, hf, hf, completionGalois_mul_apply, cyclotomicScalar_mul,
          mul_zpow, Algebra.smul_def (cyclotomicScalar p τ ^ n), map_mul, AlgEquiv.commutes,
          ← Algebra.smul_def, smul_smul] }

/-- `σ (c tⁿ) = χ(σ)ⁿ σ(c) tⁿ`, for the monomial `c tⁿ = AddMonoidAlgebra.single n c`. -/
@[simp]
theorem hodgeTateAction_single (σ : Galois p) (n : ℤ) (c : ℂ_[p]) :
    hodgeTateAction p σ (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n (cyclotomicScalar p σ ^ n • completionGalois p σ c) := by
  simp only [hodgeTateAction, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.comp_apply,
    AddMonoidAlgebra.mapAlgHom_single, AlgHom.restrictScalars_apply, AddMonoidAlgebra.lift_single,
    toAdd_ofAdd, T, AddMonoidAlgebra.smul_single, AlgEquiv.coe_toAlgHom]
  rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm]

/-- `σ (c tⁿ) = χ(σ)ⁿ σ(c) tⁿ`. -/
theorem hodgeTateAction_C_mul_T (σ : Galois p) (c : ℂ_[p]) (n : ℤ) :
    hodgeTateAction p σ (C c * T n) =
      C (cyclotomicScalar p σ ^ n • completionGalois p σ c) * T n := by
  rw [← single_eq_C_mul_T, hodgeTateAction_single, single_eq_C_mul_T]

/-- `σ` acts on the constants `ℂ_p ⊆ B_HT` by `completionGalois p σ`. -/
@[simp]
theorem hodgeTateAction_C (σ : Galois p) (c : ℂ_[p]) :
    hodgeTateAction p σ (C c) = C (completionGalois p σ c) := by
  rw [← single_eq_C, hodgeTateAction_single, zpow_zero, one_smul, single_eq_C]

/-- `σ (tⁿ) = χ(σ)ⁿ tⁿ`. -/
@[simp]
theorem hodgeTateAction_T (σ : Galois p) (n : ℤ) :
    hodgeTateAction p σ (T n) = cyclotomicScalar p σ ^ n • T n := by
  rw [T, hodgeTateAction_single, map_one, AddMonoidAlgebra.smul_single]

/-- **The coefficients of `σ f`**: the coefficient of `tⁿ` in `σ f` is `χ(σ)ⁿ σ(fₙ)`, where `fₙ` is
the coefficient of `tⁿ` in `f`. -/
theorem coeff_hodgeTateAction (σ : Galois p) (f : ℂ_[p][T;T⁻¹]) (n : ℤ) :
    (hodgeTateAction p σ f).coeff n =
      cyclotomicScalar p σ ^ n • completionGalois p σ (f.coeff n) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, smul_add]
  | single m c =>
    rw [hodgeTateAction_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · simp

/-- The coefficient of `tⁿ` in `σ f` vanishes if and only if the coefficient of `tⁿ` in `f`
vanishes. -/
theorem coeff_hodgeTateAction_eq_zero_iff (σ : Galois p) (f : ℂ_[p][T;T⁻¹]) (n : ℤ) :
    (hodgeTateAction p σ f).coeff n = 0 ↔ f.coeff n = 0 := by
  rw [coeff_hodgeTateAction, smul_eq_zero, map_eq_zero_iff _ (completionGalois p σ).injective,
    or_iff_right (zpow_ne_zero n (cyclotomicScalar_ne_zero p σ))]

/-- `σ f` and `f` have the same nonzero coefficients: the supports of their coefficient
functions agree. -/
theorem support_coeff_hodgeTateAction (σ : Galois p) (f : ℂ_[p][T;T⁻¹]) :
    (hodgeTateAction p σ f).coeff.support = f.coeff.support := by
  ext n
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, Ne, Ne,
    coeff_hodgeTateAction_eq_zero_iff]

/-- **The action preserves the grading** `B_HT = ⨁ᵢ ℂ_p tⁱ`: `σ f` is homogeneous of degree `i`,
that is, lies in `AddMonoidAlgebra.grade ℂ_[p] i = ℂ_p tⁱ`, if and only if `f` is. -/
theorem hodgeTateAction_mem_grade_iff (σ : Galois p) (f : ℂ_[p][T;T⁻¹]) (i : ℤ) :
    hodgeTateAction p σ f ∈ AddMonoidAlgebra.grade ℂ_[p] i ↔
      f ∈ AddMonoidAlgebra.grade ℂ_[p] i := by
  rw [AddMonoidAlgebra.mem_grade_iff, AddMonoidAlgebra.mem_grade_iff,
    support_coeff_hodgeTateAction]

/-! ### The invariants of `B_HT` -/

/-- Tate's theorem `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`, elementwise. -/
private theorem eq_zero_of_twist_fixed (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {i : ℤ} (hi : i ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ ∈ K.fixingSubgroup, cyclotomicScalar p σ ^ i • completionGalois p σ x = x) :
    x = 0 :=
  eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    p K hi hx

/-- **`B_HT^{G_K} = K`, elementwise**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, an element
`f ∈ B_HT` is fixed by every `σ ∈ Gal(ℚ̄_p / K)` if and only if `f` is a constant `c ∈ ℂ_p` with
`c` the image of an element of `K`. The coefficients `fₙ` of an invariant `f` satisfy
`χ(σ)ⁿ σ(fₙ) = fₙ`, so `fₙ = 0` for `n ≠ 0` (Tate) and `f₀ ∈ K` (Ax–Sen–Tate). -/
theorem forall_hodgeTateAction_eq_self_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (f : ℂ_[p][T;T⁻¹]) :
    (∀ σ ∈ K.fixingSubgroup, hodgeTateAction p σ f = f) ↔
      f ∈ Set.range fun y : K => C ((y : PadicAlgCl p) : ℂ_[p]) := by
  constructor
  · intro hf
    have hcoeff (σ : Galois p) (hσ : σ ∈ K.fixingSubgroup) (n : ℤ) :
        cyclotomicScalar p σ ^ n • completionGalois p σ (f.coeff n) = f.coeff n := by
      rw [← coeff_hodgeTateAction, hf σ hσ]
    obtain ⟨y, hy⟩ := (forall_completionGalois_eq_self_iff_mem_range p K (f.coeff 0)).1
      fun σ hσ => by simpa using hcoeff σ hσ 0
    refine ⟨y, LaurentPolynomial.ext fun n => ?_⟩
    rw [C_apply]
    split_ifs with hn
    · rw [hn]
      exact hy
    · exact (eq_zero_of_twist_fixed p K hn fun σ hσ => hcoeff σ hσ n).symm
  · rintro ⟨y, rfl⟩ σ hσ
    rw [hodgeTateAction_C, (forall_completionGalois_eq_self_iff_mem_range p K _).2 ⟨y, rfl⟩ σ hσ]

/-- **`ℂ_p^{G_K} = K`** as `ℚ_p`-subalgebras of `ℂ_p`: the ring of invariants of `Gal(ℚ̄_p / K)`
acting on `ℂ_p` by `galoisAlgHom p` is the image of `K`, for `K` finite over `ℚ_p` inside `ℚ̄_p`
(the Ax–Sen–Tate theorem `PadicComplex.fixedPoints_eq_range`). -/
theorem fixedSubalgebra_galoisAlgHom (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    Representation.fixedSubalgebra ℂ_[p] (galoisAlgHom p) K.fixingSubgroup =
      ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp K.val).range := by
  ext x
  rw [Representation.mem_fixedSubalgebra, AlgHom.mem_range]
  simp only [galoisAlgHom_apply]
  rw [forall_completionGalois_eq_self_iff_mem_range p K x]
  simp [PadicComplex.coe_eq]

/-- **`B_HT^{G_K} = K`** (Fontaine, Astérisque 223, Exposé III, §3.5 p. 141, and Exposé II,
§1.5.7 p. 74): the ring of invariants of `Gal(ℚ̄_p / K)` acting on `B_HT = ℂ_p[t, t⁻¹]` by
`hodgeTateAction p` is the image of `K` under `K ⊆ ℚ̄_p ⊆ ℂ_p ⊆ B_HT`, for `K` finite over `ℚ_p`
inside `ℚ̄_p`. -/
theorem fixedSubalgebra_hodgeTateAction (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    Representation.fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup =
      ((IsScalarTower.toAlgHom ℚ_[p] ℂ_[p] ℂ_[p][T;T⁻¹]).comp
        ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp K.val)).range := by
  ext f
  rw [Representation.mem_fixedSubalgebra, forall_hodgeTateAction_eq_self_iff, AlgHom.mem_range]
  simp only [Set.mem_range, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    IntermediateField.coe_val, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, PadicComplex.coe_eq]

/-- **`ℂ_p^{G_K} ≅ K`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, the inclusion `K ⊆ ℚ̄_p ⊆ ℂ_p`
induces an isomorphism of `ℚ_p`-algebras from `K` onto the ring of invariants of `Gal(ℚ̄_p / K)`
in `ℂ_p`. -/
def galoisFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    K ≃ₐ[ℚ_[p]] Representation.fixedSubalgebra ℂ_[p] (galoisAlgHom p) K.fixingSubgroup :=
  (AlgEquiv.ofInjective _ (RingHom.injective _)).trans
    (Subalgebra.equivOfEq _ _ (fixedSubalgebra_galoisAlgHom p K).symm)

/-- `galoisFixedSubalgebraEquiv p K y` is the image of `y` in `ℂ_p`. -/
@[simp]
theorem coe_galoisFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (y : K) :
    (galoisFixedSubalgebraEquiv p K y : ℂ_[p]) = ((y : PadicAlgCl p) : ℂ_[p]) := by
  simp [galoisFixedSubalgebraEquiv, PadicComplex.coe_eq]

/-- **`B_HT^{G_K} ≅ K`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, the inclusion
`K ⊆ ℚ̄_p ⊆ ℂ_p ⊆ B_HT` induces an isomorphism of `ℚ_p`-algebras from `K` onto the ring of
invariants of `Gal(ℚ̄_p / K)` in `B_HT`. -/
def hodgeTateFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    K ≃ₐ[ℚ_[p]]
      Representation.fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup :=
  (AlgEquiv.ofInjective _ (RingHom.injective _)).trans
    (Subalgebra.equivOfEq _ _ (fixedSubalgebra_hodgeTateAction p K).symm)

/-- `hodgeTateFixedSubalgebraEquiv p K y` is the constant `y` of `B_HT`. -/
@[simp]
theorem coe_hodgeTateFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (y : K) :
    (hodgeTateFixedSubalgebraEquiv p K y : ℂ_[p][T;T⁻¹]) = C ((y : PadicAlgCl p) : ℂ_[p]) := by
  simp only [hodgeTateFixedSubalgebraEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    AlgEquiv.ofInjective_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    IntermediateField.coe_val, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, PadicComplex.coe_eq]

/-! ### Regularity -/

/-- **A vector spanning a `Gal(ℚ̄_p / K)`-stable line of `B_HT` over `ℂ_p` is a monomial**, for
`K` finite over `ℚ_p` inside `ℚ̄_p`: if `b ∈ B_HT` has a nonzero coefficient `b_k` and
`σ b ∈ ℂ_p b` for every `σ ∈ Gal(ℚ̄_p / K)`, then `b = b_k t^k`. Indeed, for `n ≠ k` the ratio
`bₙ / b_k` is an invariant of `ℂ_p(n - k)`, so it vanishes (Tate). -/
theorem eq_single_of_forall_exists_smul_eq (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {b : ℂ_[p][T;T⁻¹]} {k : ℤ} (hk : b.coeff k ≠ 0)
    (h : ∀ σ ∈ K.fixingSubgroup, ∃ u : ℂ_[p], hodgeTateAction p σ b = u • b) :
    b = AddMonoidAlgebra.single k (b.coeff k) := by
  refine LaurentPolynomial.ext fun n => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hkn
  · rw [hkn]
  · have hq : b.coeff n / b.coeff k = 0 := by
      refine eq_zero_of_twist_fixed p K (sub_ne_zero.2 (Ne.symm hkn)) fun σ hσ => ?_
      obtain ⟨u, hu⟩ := h σ hσ
      have hn := congrArg (fun f => f.coeff n) hu
      have hk' := congrArg (fun f => f.coeff k) hu
      simp only [coeff_hodgeTateAction, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hn hk'
      rw [Algebra.smul_def, map_zpow₀] at hn hk'
      have ha : algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) ≠ 0 :=
        (map_ne_zero _).2 (cyclotomicScalar_ne_zero p σ)
      have hσk : completionGalois p σ (b.coeff k) ≠ 0 := (map_ne_zero _).2 hk
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hk'
        exact mul_ne_zero (zpow_ne_zero k ha) hσk hk'
      rw [Algebra.smul_def, map_zpow₀, map_div₀, zpow_sub₀ ha, div_mul_div_comm, hn, hk',
        mul_div_mul_left _ _ hu0]
    rwa [div_eq_zero_iff, or_iff_left hk] at hq

/-- A nonzero element of `B_HT` has a nonzero coefficient. -/
private theorem exists_coeff_ne_zero {b : ℂ_[p][T;T⁻¹]} (hb : b ≠ 0) : ∃ k, b.coeff k ≠ 0 := by
  by_contra! h
  exact hb (LaurentPolynomial.ext fun n => by rw [h n]; rfl)

/-- A monomial `c tᵏ` with `c ≠ 0` is a unit of `B_HT`. -/
private theorem isUnit_single {k : ℤ} {c : ℂ_[p]} (hc : c ≠ 0) :
    IsUnit (AddMonoidAlgebra.single k c : ℂ_[p][T;T⁻¹]) := by
  rw [single_eq_C_mul_T]
  exact ((isUnit_iff_ne_zero.2 hc).map C).mul (isUnit_T k)

/-- **Condition (ii) for `B_HT`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, an element of the
fraction field of `B_HT` fixed by every `σ ∈ Gal(ℚ̄_p / K)` lies in `B_HT`. If `x = a / s`, then
`(s_k σ(s) - χ(σ)ᵏ σ(s_k) s) x` also lies in `B_HT`, and its coefficient of `tᵏ` vanishes; so by
induction on the number of nonzero coefficients of `s`, either `x ∈ B_HT` or every `σ s` is a
multiple of `s`, and then `s` is a monomial, hence a unit. -/
theorem mem_range_of_forall_fractionRingAction_eq (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (x : FractionRing ℂ_[p][T;T⁻¹])
    (hx : ∀ σ ∈ K.fixingSubgroup, Representation.fractionRingAction (hodgeTateAction p) σ x = x) :
    x ∈ (algebraMap ℂ_[p][T;T⁻¹] (FractionRing ℂ_[p][T;T⁻¹])).range := by
  set ι := algebraMap ℂ_[p][T;T⁻¹] (FractionRing ℂ_[p][T;T⁻¹])
  have hσ (σ : Galois p) (hσ : σ ∈ K.fixingSubgroup) (s a : ℂ_[p][T;T⁻¹]) (h : ι a = ι s * x) :
      ι (hodgeTateAction p σ a) = ι (hodgeTateAction p σ s) * x := by
    have := congrArg (Representation.fractionRingAction (hodgeTateAction p) σ) h
    rwa [map_mul, hx σ hσ, Representation.fractionRingAction_algebraMap,
      Representation.fractionRingAction_algebraMap] at this
  suffices H : ∀ (n : ℕ) (s : ℂ_[p][T;T⁻¹]), s.coeff.support.card ≤ n → s ≠ 0 →
      ι s * x ∈ ι.range → x ∈ ι.range by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors ℂ_[p][T;T⁻¹]) x
    exact H _ s le_rfl (nonZeroDivisors.coe_ne_zero s) ⟨a, by rw [mul_comm]; exact hs.symm⟩
  intro n
  induction n with
  | zero =>
    intro s hs hs0
    obtain ⟨k, hk⟩ := exists_coeff_ne_zero p hs0
    have := Finset.card_pos.2 ⟨k, Finsupp.mem_support_iff.2 hk⟩
    omega
  | succ n ih =>
    rintro s hs hs0 ⟨a, ha⟩
    obtain ⟨k, hk⟩ := exists_coeff_ne_zero p hs0
    by_cases hall : ∀ σ ∈ K.fixingSubgroup, ∃ u : ℂ_[p], hodgeTateAction p σ s = u • s
    · obtain ⟨u, hu⟩ : IsUnit s := by
        rw [eq_single_of_forall_exists_smul_eq p K hk hall]
        exact isUnit_single p hk
      refine ⟨↑u⁻¹ * a, ?_⟩
      rw [map_mul, ha, ← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · push Not at hall
      obtain ⟨σ, hσK, hne⟩ := hall
      set w := cyclotomicScalar p σ ^ k • completionGalois p σ (s.coeff k)
      have hd0 : s.coeff k • hodgeTateAction p σ s - w • s ≠ 0 := by
        intro h0
        apply hne ((s.coeff k)⁻¹ * w)
        rw [mul_smul, ← sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hk, one_smul]
      have hsupp : (s.coeff k • hodgeTateAction p σ s - w • s).coeff.support ⊆
          s.coeff.support.erase k := by
        intro m hm
        rw [Finsupp.mem_support_iff] at hm
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul, Finsupp.sub_apply,
          Finsupp.smul_apply, smul_eq_mul, coeff_hodgeTateAction] at hm
        refine ⟨?_, fun hm0 => hm ?_⟩
        · rintro rfl
          exact hm (by rw [mul_comm]; exact sub_self _)
        · rw [hm0, map_zero, smul_zero, mul_zero, mul_zero, sub_zero]
      have hcard := Finset.card_le_card hsupp
      rw [Finset.card_erase_of_mem (Finsupp.mem_support_iff.2 hk)] at hcard
      refine ih _ (by omega) hd0
        ⟨s.coeff k • hodgeTateAction p σ a - w • a, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, map_sub, map_sub, map_mul,
        map_mul, map_mul, map_mul, hσ σ hσK s a ha, ha, sub_mul, mul_assoc, mul_assoc]

/-- **`B_HT` is `(ℚ_p, Gal(ℚ̄_p / K))`-regular** (Fontaine–Ouyang, Proposition 6.2; Fontaine,
Astérisque 223, Exposé III, Proposition 3.6 p. 141), for `K` finite over `ℚ_p` inside `ℚ̄_p`:
`B_HT = ℂ_p[t, t⁻¹]` is a domain; an element of its fraction field fixed by `Gal(ℚ̄_p / K)` lies
in `B_HT` (`PadicComplex.mem_range_of_forall_fractionRingAction_eq`); and a nonzero `b ∈ B_HT`
spanning a `Gal(ℚ̄_p / K)`-stable `ℚ_p`-line is a monomial `c tᵏ`
(`PadicComplex.eq_single_of_forall_exists_smul_eq`), hence a unit. -/
theorem isRegularPeriodRing_hodgeTateAction (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    Representation.IsRegularPeriodRing (hodgeTateAction p) K.fixingSubgroup where
  mem_range_of_forall_eq := mem_range_of_forall_fractionRingAction_eq p K
  isUnit_of_forall_mem_span b hb h := by
    obtain ⟨k, hk⟩ := exists_coeff_ne_zero p hb
    rw [eq_single_of_forall_exists_smul_eq p K hk fun σ hσ => by
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (h σ hσ)
      exact ⟨algebraMap ℚ_[p] ℂ_[p] r, by rw [← hr, algebraMap_smul]⟩]
    exact isUnit_single p hk

end PadicComplex
