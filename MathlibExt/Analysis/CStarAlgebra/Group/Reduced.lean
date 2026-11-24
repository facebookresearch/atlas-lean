/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.OperatorBidual
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.DenseEmbedding

/-!
# Reduced group C-star algebras

This file constructs the reduced group C-star algebra of an arbitrary group.
The construction starts with the left regular representation on `ℓ²(G)`,
integrates it on the complex group algebra, and takes the norm closure of the
resulting star subalgebra of bounded operators.

The canonical trace is the vector state at the identity basis vector.  Group
equivalences act by reindexing `ℓ²`; no map is declared for a general group
homomorphism, since such a homomorphism need not induce a map of reduced group
C-star algebras.
-/

@[expose] public section

open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal ENNReal

namespace MathlibExt.Analysis.CStarAlgebra.Group

open MathlibExt.Analysis.InnerProductSpace

noncomputable section

universe u v w

/-! ## The left regular representation -/

/-- The Hilbert space `ℓ²(G)` used by the left regular representation. -/
abbrev GroupL2 (G : Type u) := lp (fun _ : G => ℂ) 2

def leftTranslate
    {G : Type u} [Group G] (g : G) (xi : GroupL2 G) (h : G) : ℂ :=
  xi (g⁻¹ * h)

theorem leftTranslate_mem
    {G : Type u} [Group G] (g : G) (xi : GroupL2 G) :
    Memℓp (leftTranslate g xi) 2 := by
  have hxi := lp.memℓp xi
  rw [memℓp_gen_iff (by norm_num)] at hxi ⊢
  change Summable ((fun i : G => ‖xi i‖ ^ (2 : ℝ≥0∞).toReal) ∘
    (Equiv.mulLeft g⁻¹))
  exact (Equiv.mulLeft g⁻¹).summable_iff.mpr hxi

theorem leftTranslate_norm
    {G : Type u} [Group G] (g : G) (xi : GroupL2 G) :
    ‖(⟨leftTranslate g xi, leftTranslate_mem g xi⟩ : GroupL2 G)‖ = ‖xi‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  simpa only [leftTranslate, Equiv.coe_mulLeft] using
    (Equiv.mulLeft g⁻¹).tsum_eq (fun h : G => ‖xi h‖ ^ (2 : ℝ≥0∞).toReal)

/-- Left translation by `g`, as a linear isometric equivalence of `ℓ²(G)`. -/
noncomputable def leftRegularLinearIsometryEquiv
    {G : Type u} [Group G] (g : G) : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 G where
  toFun xi := ⟨leftTranslate g xi, leftTranslate_mem g xi⟩
  invFun xi := ⟨leftTranslate g⁻¹ xi, leftTranslate_mem g⁻¹ xi⟩
  left_inv xi := by
    ext h
    simp [leftTranslate]
  right_inv xi := by
    ext h
    simp [leftTranslate]
  map_add' xi eta := by
    ext h
    rfl
  map_smul' c xi := by
    ext h
    rfl
  norm_map' xi := leftTranslate_norm g xi

@[simp]
theorem leftRegularLinearIsometryEquiv_apply
    {G : Type u} [Group G] (g h : G) (xi : GroupL2 G) :
    leftRegularLinearIsometryEquiv g xi h = xi (g⁻¹ * h) :=
  rfl

/-- The left regular unitary associated to a group element. -/
noncomputable def leftRegularUnitary
    {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (leftRegularLinearIsometryEquiv g)

@[simp]
theorem leftRegularUnitary_apply
    {G : Type u} [Group G] (g h : G) (xi : GroupL2 G) :
    ((leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) xi) h =
      xi (g⁻¹ * h) :=
  rfl

/-- The left regular representation as a group homomorphism into the unitary
group of bounded operators. -/
noncomputable def leftRegularUnitaryHom
    (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    apply Subtype.ext
    ext xi h
    simp
  map_mul' g k := by
    apply Subtype.ext
    ext xi h
    simp [mul_assoc]

@[simp]
theorem leftRegularUnitaryHom_apply
    {G : Type u} [Group G] (g : G) :
    leftRegularUnitaryHom G g = leftRegularUnitary g :=
  rfl

/-- The left regular representation with the unitary subtype forgotten. -/
noncomputable def leftRegularOperatorHom
    (G : Type u) [Group G] : G →* (GroupL2 G →L[ℂ] GroupL2 G) :=
  (unitary (GroupL2 G →L[ℂ] GroupL2 G)).subtype.comp
    (leftRegularUnitaryHom G)

@[simp]
theorem leftRegularOperatorHom_apply
    {G : Type u} [Group G] (g h : G) (xi : GroupL2 G) :
    (leftRegularOperatorHom G g xi) h = xi (g⁻¹ * h) :=
  rfl

@[simp]
theorem star_leftRegularOperatorHom
    {G : Type u} [Group G] (g : G) :
    star (leftRegularOperatorHom G g) = leftRegularOperatorHom G g⁻¹ := by
  change star
      ((leftRegularUnitaryHom G g : unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
        GroupL2 G →L[ℂ] GroupL2 G) =
    ((leftRegularUnitaryHom G g⁻¹ : unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
      GroupL2 G →L[ℂ] GroupL2 G)
  rw [← Unitary.coe_star, Unitary.star_eq_inv, ← map_inv]

/-- The standard basis vector at `g`. -/
noncomputable def delta
    {G : Type u} (g : G) : GroupL2 G := by
  classical
  exact lp.single 2 g 1

/-- The scalar Kronecker delta, without exposing decidable equality as an API
parameter. -/
noncomputable def kroneckerDelta {G : Type u} (g h : G) : ℂ :=
  by
    classical
    exact if g = h then 1 else 0

@[simp]
theorem delta_apply
    {G : Type u} (g h : G) : delta g h = kroneckerDelta g h := by
  classical
  simp [delta, kroneckerDelta, Pi.single_apply, eq_comm]

@[simp]
theorem norm_delta
    {G : Type u} (g : G) : ‖delta g‖ = 1 := by
  classical
  simp [delta]

@[simp]
theorem leftRegularLinearIsometryEquiv_delta
    {G : Type u} [Group G] (g h : G) :
    leftRegularLinearIsometryEquiv g (delta h) = delta (g * h) := by
  classical
  ext k
  simp [leftRegularLinearIsometryEquiv_apply, kroneckerDelta,
    eq_inv_mul_iff_mul_eq]

@[simp]
theorem leftRegularUnitary_delta
    {G : Type u} [Group G] (g h : G) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) (delta h) =
      delta (g * h) := by
  classical
  ext k
  simp [leftRegularUnitary_apply, kroneckerDelta, eq_inv_mul_iff_mul_eq]

/-! ## The complex group star algebra -/

/-- The complex group algebra as a genuine distinct type.  Its algebraic
operations are transported from `MonoidAlgebra ℂ G`, while its star below is
the group involution rather than the coefficientwise Finsupp star. -/
def ComplexGroupAlgebra (G : Type u) := MonoidAlgebra ℂ G

namespace ComplexGroupAlgebra

/-- The transparent carrier equivalence with Mathlib's monoid algebra. -/
def toMonoidAlgebraEquiv (G : Type u) :
    ComplexGroupAlgebra G ≃ MonoidAlgebra ℂ G where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instRing
    {G : Type u} [Group G] : Ring (ComplexGroupAlgebra G) :=
  (toMonoidAlgebraEquiv G).ring

noncomputable instance instAlgebra
    {G : Type u} [Group G] : Algebra ℂ (ComplexGroupAlgebra G) :=
  Equiv.algebra ℂ (toMonoidAlgebraEquiv G)

/-- The transported ring equivalence. -/
noncomputable def toMonoidAlgebraRingEquiv
    (G : Type u) [Group G] :
    ComplexGroupAlgebra G ≃+* MonoidAlgebra ℂ G :=
  Equiv.ringEquiv (toMonoidAlgebraEquiv G)

/-- The transported complex-algebra equivalence. -/
noncomputable def toMonoidAlgebraAlgEquiv
    (G : Type u) [Group G] :
    ComplexGroupAlgebra G ≃ₐ[ℂ] MonoidAlgebra ℂ G :=
  Equiv.algEquiv ℂ (toMonoidAlgebraEquiv G)

theorem toMonoidAlgebraRingEquiv_apply
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    toMonoidAlgebraRingEquiv G a = toMonoidAlgebraEquiv G a :=
  rfl

theorem toMonoidAlgebraAlgEquiv_apply
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    toMonoidAlgebraAlgEquiv G a = toMonoidAlgebraEquiv G a :=
  rfl

@[simp]
theorem toMonoidAlgebraAlgEquiv_apply_eq_ringEquiv
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    toMonoidAlgebraAlgEquiv G a = toMonoidAlgebraRingEquiv G a :=
  rfl

/-- Coefficients of a complex group-algebra element. -/
def coeff
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) : G →₀ ℂ :=
  (toMonoidAlgebraRingEquiv G a).coeff

theorem coeff_eq_ringEquiv_coeff
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    a.coeff = (toMonoidAlgebraRingEquiv G a).coeff :=
  rfl

@[ext]
theorem ext
    {G : Type u} [Group G] {a b : ComplexGroupAlgebra G}
    (h : ∀ g, a.coeff g = b.coeff g) : a = b := by
  apply (toMonoidAlgebraRingEquiv G).injective
  apply MonoidAlgebra.coeff_injective
  ext g
  exact h g

@[simp]
theorem coeff_zero
    {G : Type u} [Group G] : (0 : ComplexGroupAlgebra G).coeff = 0 := by
  change (toMonoidAlgebraRingEquiv G (0 : ComplexGroupAlgebra G)).coeff = 0
  simp

@[simp]
theorem coeff_add
    {G : Type u} [Group G] (a b : ComplexGroupAlgebra G) :
    (a + b).coeff = a.coeff + b.coeff := by
  change (toMonoidAlgebraRingEquiv G (a + b)).coeff =
    (toMonoidAlgebraRingEquiv G a).coeff +
      (toMonoidAlgebraRingEquiv G b).coeff
  rw [map_add]
  rfl

@[simp]
theorem coeff_smul
    {G : Type u} [Group G] (c : ℂ) (a : ComplexGroupAlgebra G) :
    (c • a).coeff = c • a.coeff := by
  change (toMonoidAlgebraRingEquiv G (c • a)).coeff =
    c • (toMonoidAlgebraRingEquiv G a).coeff
  congr 1

/-- A single group element with a complex coefficient. -/
noncomputable def single
    {G : Type u} [Group G] (g : G) (c : ℂ) : ComplexGroupAlgebra G :=
  (toMonoidAlgebraRingEquiv G).symm (MonoidAlgebra.single g c)

@[simp]
theorem toMonoidAlgebraRingEquiv_single
    {G : Type u} [Group G] (g : G) (c : ℂ) :
    toMonoidAlgebraRingEquiv G (single g c) = MonoidAlgebra.single g c :=
  (toMonoidAlgebraRingEquiv G).apply_symm_apply _

@[simp]
theorem toMonoidAlgebraAlgEquiv_symm_apply
    {G : Type u} [Group G] (a : MonoidAlgebra ℂ G) :
    (toMonoidAlgebraAlgEquiv G).symm a =
      (toMonoidAlgebraRingEquiv G).symm a :=
  rfl

@[simp]
theorem coeff_single
    {G : Type u} [Group G] [DecidableEq G] (g h : G) (c : ℂ) :
    (single g c).coeff h = if g = h then c else 0 := by
  classical
  simp [single, coeff, Finsupp.single_apply]

@[simp]
theorem single_mul_single
    {G : Type u} [Group G] (g h : G) (c d : ℂ) :
    single g c * single h d = single (g * h) (c * d) := by
  apply (toMonoidAlgebraRingEquiv G).injective
  simp [single]

@[simp]
theorem single_one_one
    {G : Type u} [Group G] : single (1 : G) 1 = 1 := by
  apply (toMonoidAlgebraRingEquiv G).injective
  simp [single, MonoidAlgebra.one_def]

@[simp]
theorem smul_single
    {G : Type u} [Group G] (c d : ℂ) (g : G) :
    c • single g d = single g (c * d) := by
  apply (toMonoidAlgebraAlgEquiv G).injective
  simp [single]

@[elab_as_elim]
theorem induction_linear
    {G : Type u} [Group G] {motive : ComplexGroupAlgebra G → Prop}
    (a : ComplexGroupAlgebra G)
    (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (single_case : ∀ g c, motive (single g c)) : motive a := by
  let e := toMonoidAlgebraRingEquiv G
  rw [← e.symm_apply_apply a]
  refine MonoidAlgebra.induction_linear
    (motive := fun x => motive (e.symm x)) (e a) ?_ ?_ ?_
  · simpa using zero
  · intro x y hx hy
    simpa using add (e.symm x) (e.symm y) hx hy
  · intro g c
    simpa [single, e] using single_case g c

end ComplexGroupAlgebra

/-- The inversion-conjugation operation on the underlying monoid algebra. -/
def monoidAlgebraGroupStar
    {G : Type u} [Group G]
    (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff <|
    Finsupp.equivMapDomain (Equiv.inv G)
      (a.coeff.mapRange (star : ℂ → ℂ) (star_zero ℂ))

def groupAlgebraStar
    {G : Type u} [Group G]
    (a : ComplexGroupAlgebra G) : ComplexGroupAlgebra G :=
  (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G).symm <|
    monoidAlgebraGroupStar (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a)

noncomputable instance instStarComplexGroupAlgebra
    {G : Type u} [Group G] : Star (ComplexGroupAlgebra G) where
  star := groupAlgebraStar

@[simp]
theorem toMonoidAlgebraRingEquiv_star
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G (star a) =
      monoidAlgebraGroupStar
        (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a) := by
  exact (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G).apply_symm_apply _

@[simp]
theorem star_apply
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) (g : G) :
    (star a).coeff g = star (a.coeff g⁻¹) := by
  simp [ComplexGroupAlgebra.coeff, monoidAlgebraGroupStar]

@[simp]
theorem star_single
    {G : Type u} [Group G] (g : G) (c : ℂ) :
    star (ComplexGroupAlgebra.single g c) =
      ComplexGroupAlgebra.single g⁻¹ (star c) := by
  classical
  ext h
  by_cases hgh : g = h⁻¹ <;>
    simp [star_apply, hgh, inv_eq_iff_eq_inv]

theorem star_zero_complexGroupAlgebra
    {G : Type u} [Group G] :
    star (0 : ComplexGroupAlgebra G) = 0 := by
  ext g
  simp [star_apply]

theorem star_add_complexGroupAlgebra
    {G : Type u} [Group G] (a b : ComplexGroupAlgebra G) :
    star (a + b) = star a + star b := by
  ext g
  simp [star_apply]

theorem star_mul_complexGroupAlgebra
    {G : Type u} [Group G] (a b : ComplexGroupAlgebra G) :
    star (a * b) = star b * star a := by
  classical
  induction a using ComplexGroupAlgebra.induction_linear with
  | zero => rw [zero_mul, star_zero_complexGroupAlgebra, mul_zero]
  | add x y hx hy =>
      rw [add_mul, star_add_complexGroupAlgebra, star_add_complexGroupAlgebra,
        mul_add, hx, hy]
  | single_case g c =>
      induction b using ComplexGroupAlgebra.induction_linear with
      | zero => rw [mul_zero, star_zero_complexGroupAlgebra, zero_mul]
      | add x y hx hy =>
          rw [mul_add, star_add_complexGroupAlgebra, star_add_complexGroupAlgebra,
            add_mul, hx, hy]
      | single_case h d =>
          simp [ComplexGroupAlgebra.single_mul_single, mul_inv_rev, mul_comm]

noncomputable instance instStarRingComplexGroupAlgebra
    {G : Type u} [Group G] : StarRing (ComplexGroupAlgebra G) where
  star_involutive a := by
    ext g
    simp
  star_mul := star_mul_complexGroupAlgebra
  star_add := star_add_complexGroupAlgebra

noncomputable instance instStarModuleComplexGroupAlgebra
    {G : Type u} [Group G] : StarModule ℂ (ComplexGroupAlgebra G) where
  star_smul c a := by
    ext g
    simp

/-- Reindexing coefficients commutes with the group involution. -/
theorem mapDomain_monoidAlgebraGroupStar
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : MonoidAlgebra ℂ G) :
    MonoidAlgebra.mapDomainRingEquiv ℂ e (monoidAlgebraGroupStar a) =
      monoidAlgebraGroupStar (MonoidAlgebra.mapDomainRingEquiv ℂ e a) := by
  apply MonoidAlgebra.coeff_injective
  ext h
  simp [monoidAlgebraGroupStar, MonoidAlgebra.coeff_mapDomainRingEquiv]

/-- Reindexing on the distinct complex group-algebra carriers. -/
noncomputable def groupAlgebraRingEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) : ComplexGroupAlgebra G ≃+* ComplexGroupAlgebra H :=
  (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G).trans
    ((MonoidAlgebra.mapDomainRingEquiv ℂ e).trans
      (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv H).symm)

@[simp]
theorem toMonoidAlgebraRingEquiv_groupAlgebraRingEquiv_apply
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ComplexGroupAlgebra G) :
    ComplexGroupAlgebra.toMonoidAlgebraRingEquiv H
        (groupAlgebraRingEquiv e a) =
      MonoidAlgebra.mapDomainRingEquiv ℂ e
        (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a) :=
  rfl

/-- Reindexing coefficients along a group equivalence, with the group-algebra
involution included in the bundled equivalence. -/
noncomputable def groupAlgebraEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) : ComplexGroupAlgebra G ≃⋆ₐ[ℂ] ComplexGroupAlgebra H where
  toStarRingEquiv :=
    { toRingEquiv := groupAlgebraRingEquiv e
      map_star' := by
        intro a
        apply (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv H).injective
        change MonoidAlgebra.mapDomainRingEquiv ℂ e
            (monoidAlgebraGroupStar
              (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a)) =
          monoidAlgebraGroupStar
            (MonoidAlgebra.mapDomainRingEquiv ℂ e
              (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a))
        exact mapDomain_monoidAlgebraGroupStar e _ }
  map_smul' c a := by
    apply (ComplexGroupAlgebra.toMonoidAlgebraAlgEquiv H).injective
    change MonoidAlgebra.mapDomainRingEquiv ℂ e
        (ComplexGroupAlgebra.toMonoidAlgebraAlgEquiv G (c • a)) =
      c • MonoidAlgebra.mapDomainRingEquiv ℂ e
        (ComplexGroupAlgebra.toMonoidAlgebraAlgEquiv G a)
    apply MonoidAlgebra.coeff_injective
    ext h
    simp [MonoidAlgebra.coeff_mapDomainRingEquiv]

@[simp]
theorem groupAlgebraEquiv_apply
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ComplexGroupAlgebra G) (h : H) :
    (groupAlgebraEquiv e a).coeff h = a.coeff (e.symm h) := by
  change (MonoidAlgebra.mapDomainRingEquiv ℂ e
    (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a)).coeff h =
      (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv G a).coeff (e.symm h)
  simp [MonoidAlgebra.coeff_mapDomainRingEquiv]

@[simp]
theorem groupAlgebraEquiv_single
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (g : G) (c : ℂ) :
    groupAlgebraEquiv e (ComplexGroupAlgebra.single g c) =
      ComplexGroupAlgebra.single (e g) c := by
  apply (ComplexGroupAlgebra.toMonoidAlgebraRingEquiv H).injective
  simp [groupAlgebraEquiv, ComplexGroupAlgebra.single]

/-! ## The integrated representation and its closure -/

/-- The algebra homomorphism obtained by integrating the left regular
representation over finitely supported coefficients. -/
noncomputable def integratedLeftRegularAlgHom
    (G : Type u) [Group G] :
    ComplexGroupAlgebra G →ₐ[ℂ] (GroupL2 G →L[ℂ] GroupL2 G) :=
  (MonoidAlgebra.lift ℂ (GroupL2 G →L[ℂ] GroupL2 G) G
    (leftRegularOperatorHom G)).comp
      (ComplexGroupAlgebra.toMonoidAlgebraAlgEquiv G).toAlgHom

theorem integratedLeftRegularAlgHom_map_star
    (G : Type u) [Group G] (a : ComplexGroupAlgebra G) :
    integratedLeftRegularAlgHom G (star a) =
      star (integratedLeftRegularAlgHom G a) := by
  classical
  induction a using ComplexGroupAlgebra.induction_linear with
  | zero =>
      rw [star_zero_complexGroupAlgebra, map_zero]
      exact (star_zero (GroupL2 G →L[ℂ] GroupL2 G)).symm
  | add x y hx hy =>
      rw [star_add_complexGroupAlgebra, map_add, map_add, hx, hy]
      exact (star_add (integratedLeftRegularAlgHom G x)
        (integratedLeftRegularAlgHom G y)).symm
  | single_case g c =>
      simp [integratedLeftRegularAlgHom, star_leftRegularOperatorHom]

/-- The integrated left regular star representation. -/
noncomputable def integratedLeftRegular
    (G : Type u) [Group G] :
    ComplexGroupAlgebra G →⋆ₐ[ℂ] (GroupL2 G →L[ℂ] GroupL2 G) where
  toAlgHom := integratedLeftRegularAlgHom G
  map_star' := integratedLeftRegularAlgHom_map_star G

@[simp]
theorem integratedLeftRegular_single
    {G : Type u} [Group G] (g : G) (c : ℂ) :
    integratedLeftRegular G (ComplexGroupAlgebra.single g c) =
      c • (leftRegularOperatorHom G g) := by
  simp [integratedLeftRegular, integratedLeftRegularAlgHom]

@[simp]
theorem integratedLeftRegular_single_apply
    {G : Type u} [Group G] (g h : G) (c : ℂ) (xi : GroupL2 G) :
    (integratedLeftRegular G (ComplexGroupAlgebra.single g c) xi) h =
      c * xi (g⁻¹ * h) := by
  simp [integratedLeftRegular_single]

/-- The reduced group C-star algebra inside the bounded operators on `ℓ²(G)`. -/
noncomputable def reducedGroupCStarSubalgebra
    (G : Type u) [Group G] :
    StarSubalgebra ℂ (GroupL2 G →L[ℂ] GroupL2 G) :=
  (integratedLeftRegular G).range.topologicalClosure

/-- The reduced group C-star algebra of `G`. -/
abbrev ReducedGroupCStarAlgebra
    (G : Type u) [Group G] := reducedGroupCStarSubalgebra G

theorem isClosed_reducedGroupCStarSubalgebra
    (G : Type u) [Group G] :
    IsClosed (reducedGroupCStarSubalgebra G :
      Set (GroupL2 G →L[ℂ] GroupL2 G)) :=
  by
    simp [reducedGroupCStarSubalgebra]

noncomputable instance instCStarAlgebraReducedGroupCStarAlgebra
    (G : Type u) [Group G] : CStarAlgebra (ReducedGroupCStarAlgebra G) := by
  letI : IsClosed (reducedGroupCStarSubalgebra G :
      Set (GroupL2 G →L[ℂ] GroupL2 G)) :=
    isClosed_reducedGroupCStarSubalgebra G
  infer_instance

instance instNontrivialReducedGroupCStarAlgebra
    (G : Type u) [Group G] : Nontrivial (ReducedGroupCStarAlgebra G) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hvec := congrArg
    (fun a : ReducedGroupCStarAlgebra G =>
      (a.1 : GroupL2 G →L[ℂ] GroupL2 G) (delta (1 : G))) h
  have hzero : (0 : GroupL2 G) = delta (1 : G) := by simpa using hvec
  have hnorm := congrArg norm hzero
  simp at hnorm

noncomputable instance instPartialOrderReducedGroupCStarAlgebra
    (G : Type u) [Group G] : PartialOrder (ReducedGroupCStarAlgebra G) :=
  CStarAlgebra.spectralOrder _

noncomputable instance instStarOrderedRingReducedGroupCStarAlgebra
    (G : Type u) [Group G] : StarOrderedRing (ReducedGroupCStarAlgebra G) :=
  CStarAlgebra.spectralOrderedRing _

/-- The dense algebraic map into the reduced group C-star algebra. -/
noncomputable def algebraicMap
    (G : Type u) [Group G] :
    ComplexGroupAlgebra G →⋆ₐ[ℂ] ReducedGroupCStarAlgebra G :=
  (StarSubalgebra.inclusion
      (StarSubalgebra.le_topologicalClosure (integratedLeftRegular G).range)).comp
    (integratedLeftRegular G).rangeRestrict

/-- The algebraic group algebra has dense image in the reduced completion. -/
theorem denseRange_algebraicMap
    (G : Type u) [Group G] : DenseRange (algebraicMap G) := by
  let S := (integratedLeftRegular G).range
  let hS : S ≤ S.topologicalClosure := StarSubalgebra.le_topologicalClosure S
  have hinc : DenseRange
      (StarSubalgebra.inclusion hS) := by
    change DenseRange (Set.inclusion hS)
    apply (denseRange_inclusion_iff hS).2
    change closure (S : Set (GroupL2 G →L[ℂ] GroupL2 G)) ⊆
      closure (S : Set (GroupL2 G →L[ℂ] GroupL2 G))
    exact subset_rfl
  have hrange : DenseRange (integratedLeftRegular G).rangeRestrict := by
    apply Function.Surjective.denseRange
    intro y
    rcases y.2 with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hcomp := hinc.comp hrange
    (continuous_inclusion hS)
  exact hcomp

@[simp]
theorem algebraicMap_val
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    ((algebraicMap G a : ReducedGroupCStarAlgebra G) :
      GroupL2 G →L[ℂ] GroupL2 G) = integratedLeftRegular G a :=
  rfl

/-- The canonical copy of a group element in its reduced group C-star
algebra. -/
noncomputable def groupElement
    {G : Type u} [Group G] (g : G) : ReducedGroupCStarAlgebra G :=
  algebraicMap G (ComplexGroupAlgebra.single g 1)

@[simp]
theorem groupElement_val
    {G : Type u} [Group G] (g : G) :
    ((groupElement g : ReducedGroupCStarAlgebra G) :
      GroupL2 G →L[ℂ] GroupL2 G) = leftRegularOperatorHom G g := by
  rw [groupElement, algebraicMap_val, integratedLeftRegular_single]
  simp

@[simp]
theorem algebraicMap_single
    {G : Type u} [Group G] (g : G) (c : ℂ) :
    algebraicMap G (ComplexGroupAlgebra.single g c) = c • groupElement g := by
  apply Subtype.ext
  simp [algebraicMap_val, groupElement_val]

@[simp]
theorem groupElement_one
    (G : Type u) [Group G] : groupElement (1 : G) = 1 := by
  change algebraicMap G (ComplexGroupAlgebra.single 1 1) = 1
  rw [ComplexGroupAlgebra.single_one_one, map_one]

@[simp]
theorem groupElement_mul
    {G : Type u} [Group G] (g h : G) :
    groupElement (g * h) = groupElement g * groupElement h := by
  change algebraicMap G (ComplexGroupAlgebra.single (g * h) 1) =
    algebraicMap G (ComplexGroupAlgebra.single g 1) *
      algebraicMap G (ComplexGroupAlgebra.single h 1)
  rw [← map_mul]
  simp

@[simp]
theorem star_groupElement
    {G : Type u} [Group G] (g : G) :
    star (groupElement g) = groupElement g⁻¹ := by
  change star (algebraicMap G (ComplexGroupAlgebra.single g 1)) =
    algebraicMap G (ComplexGroupAlgebra.single g⁻¹ 1)
  rw [← map_star]
  simp

/-- A group element as a unitary of the reduced group C-star algebra. -/
noncomputable def groupUnitary
    {G : Type u} [Group G] (g : G) : unitary (ReducedGroupCStarAlgebra G) :=
  ⟨groupElement g, by
    constructor
    · simp [star_groupElement, ← groupElement_mul]
    · simp [star_groupElement, ← groupElement_mul]⟩

@[simp]
theorem groupUnitary_coe
    {G : Type u} [Group G] (g : G) :
    (groupUnitary g : ReducedGroupCStarAlgebra G) = groupElement g :=
  rfl

/-- The canonical group homomorphism into the unitary group of the reduced
group C-star algebra. -/
noncomputable def groupUnitaryHom
    (G : Type u) [Group G] : G →* unitary (ReducedGroupCStarAlgebra G) where
  toFun := groupUnitary
  map_one' := by
    apply Subtype.ext
    exact groupElement_one G
  map_mul' g h := by
    apply Subtype.ext
    exact groupElement_mul g h

@[simp]
theorem groupUnitaryHom_apply
    {G : Type u} [Group G] (g : G) :
    groupUnitaryHom G g = groupUnitary g :=
  rfl

@[simp]
theorem groupUnitary_apply
    {G : Type u} [Group G] (g h : G) (xi : GroupL2 G) :
    (((groupUnitary g : ReducedGroupCStarAlgebra G) :
      GroupL2 G →L[ℂ] GroupL2 G) xi) h = xi (g⁻¹ * h) := by
  rw [show (groupUnitary g : ReducedGroupCStarAlgebra G) = groupElement g from rfl]
  simp

@[simp]
theorem groupUnitary_delta
    {G : Type u} [Group G] (g h : G) :
    ((groupUnitary g : ReducedGroupCStarAlgebra G) :
      GroupL2 G →L[ℂ] GroupL2 G) (delta h) = delta (g * h) := by
  rw [show (groupUnitary g : ReducedGroupCStarAlgebra G) = groupElement g from rfl]
  rw [groupElement_val]
  ext k
  simp only [leftRegularOperatorHom_apply, delta_apply, kroneckerDelta]
  rw [eq_inv_mul_iff_mul_eq]

/-! ## The canonical trace -/

noncomputable def canonicalTraceLinearMap
    (G : Type u) [Group G] : ReducedGroupCStarAlgebra G →ₗ[ℂ] ℂ where
  toFun a := operatorCoefficient (delta (1 : G)) (delta (1 : G)) a.1
  map_add' a b := by
    exact map_add (operatorCoefficient (delta (1 : G)) (delta (1 : G))) a.1 b.1
  map_smul' c a := by
    exact map_smul (operatorCoefficient (delta (1 : G)) (delta (1 : G))) c a.1

theorem norm_canonicalTraceLinearMap_apply_le
    {G : Type u} [Group G] (a : ReducedGroupCStarAlgebra G) :
    ‖canonicalTraceLinearMap G a‖ ≤ ‖a‖ := by
  change ‖operatorCoefficient (delta (1 : G)) (delta (1 : G)) a.1‖ ≤ ‖a‖
  rw [operatorCoefficient_apply]
  calc
    _ ≤ ‖delta (1 : G)‖ * ‖a.1 (delta (1 : G))‖ := norm_inner_le_norm _ _
    _ ≤ ‖delta (1 : G)‖ * (‖a.1‖ * ‖delta (1 : G)‖) := by
      gcongr
      exact a.1.le_opNorm _
    _ = ‖a‖ := by simp

/-- The canonical trace as a bounded functional. -/
noncomputable def canonicalTraceContinuousLinearMap
    (G : Type u) [Group G] : ReducedGroupCStarAlgebra G →L[ℂ] ℂ :=
  LinearMap.mkContinuous (canonicalTraceLinearMap G) 1 fun a => by
    simpa only [one_mul] using norm_canonicalTraceLinearMap_apply_le a

@[simp]
theorem canonicalTraceContinuousLinearMap_apply
    {G : Type u} [Group G] (a : ReducedGroupCStarAlgebra G) :
    canonicalTraceContinuousLinearMap G a = canonicalTraceLinearMap G a :=
  rfl

theorem norm_canonicalTraceContinuousLinearMap
    (G : Type u) [Group G] : ‖canonicalTraceContinuousLinearMap G‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one
      (fun a => by simpa only [one_mul] using
        norm_canonicalTraceLinearMap_apply_le (G := G) a)
  · calc
      1 = ‖canonicalTraceContinuousLinearMap G (1 : ReducedGroupCStarAlgebra G)‖ := by
        simp [canonicalTraceContinuousLinearMap, canonicalTraceLinearMap,
          operatorCoefficient_apply]
      _ ≤ ‖canonicalTraceContinuousLinearMap G‖ * ‖(1 : ReducedGroupCStarAlgebra G)‖ :=
        (canonicalTraceContinuousLinearMap G).le_opNorm _
      _ = ‖canonicalTraceContinuousLinearMap G‖ := by simp

/-- The identity-coefficient vector state on the reduced group C-star
algebra. -/
noncomputable def canonicalTrace
    (G : Type u) [Group G] : ReducedGroupCStarAlgebra G →ₚ[ℂ] ℂ where
  toLinearMap := canonicalTraceLinearMap G
  monotone' := by
    apply (canonicalTraceContinuousLinearMap G).monotone_iff_opNorm_eq_map_one.mpr
    rw [norm_canonicalTraceContinuousLinearMap]
    simp [canonicalTraceContinuousLinearMap, canonicalTraceLinearMap,
      operatorCoefficient_apply]

@[simp]
theorem canonicalTrace_apply
    {G : Type u} [Group G] (a : ReducedGroupCStarAlgebra G) :
    canonicalTrace G a =
      ⟪delta (1 : G),
        (a : GroupL2 G →L[ℂ] GroupL2 G) (delta (1 : G))⟫_ℂ := by
  change canonicalTraceLinearMap G a = _
  change operatorCoefficient (delta (1 : G)) (delta (1 : G)) a.1 = _
  exact operatorCoefficient_apply _ _ _

@[simp]
theorem canonicalTrace_one
    (G : Type u) [Group G] : canonicalTrace G 1 = 1 := by
  classical
  simp [canonicalTrace_apply, delta]

@[simp]
theorem canonicalTrace_groupUnitary
    {G : Type u} [Group G] (g : G) :
    canonicalTrace G (groupUnitary g : ReducedGroupCStarAlgebra G) =
      kroneckerDelta g 1 := by
  rw [canonicalTrace_apply, groupUnitary_delta]
  classical
  simp [delta, kroneckerDelta, lp.inner_single_left, Pi.single_apply, eq_comm]

@[simp]
theorem canonicalTrace_groupElement
    {G : Type u} [Group G] (g : G) :
    canonicalTrace G (groupElement g) = kroneckerDelta g 1 := by
  simpa only [groupUnitary_coe] using canonicalTrace_groupUnitary (G := G) g

@[simp]
theorem canonicalTrace_algebraicMap
    {G : Type u} [Group G] (a : ComplexGroupAlgebra G) :
    canonicalTrace G (algebraicMap G a) = a.coeff 1 := by
  classical
  induction a using ComplexGroupAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      simp
  | single_case g c =>
      by_cases hg : g = 1
      · subst g
        rw [algebraicMap_single, map_smul, canonicalTrace_groupElement]
        simp [kroneckerDelta]
      · rw [algebraicMap_single, map_smul, canonicalTrace_groupElement]
        simp [kroneckerDelta, hg]

theorem coefficientAtOne_mul_comm
    {G : Type u} [Group G] (a b : ComplexGroupAlgebra G) :
    (a * b).coeff 1 = (b * a).coeff 1 := by
  classical
  induction a using ComplexGroupAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single_case g c =>
      induction b using ComplexGroupAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [mul_add, add_mul, hx, hy]
      | single_case h d =>
          by_cases hgh : g * h = 1
          · have hhg : h * g = 1 := mul_eq_one_symm hgh
            simp [ComplexGroupAlgebra.single_mul_single, hgh, hhg, mul_comm]
          · have hhg : h * g ≠ 1 := fun h' => hgh (mul_eq_one_symm h')
            simp [ComplexGroupAlgebra.single_mul_single, hgh, hhg]

/-- The identity-coefficient state is tracial on the entire norm closure. -/
theorem canonicalTrace_mul_comm
    {G : Type u} [Group G] (a b : ReducedGroupCStarAlgebra G) :
    canonicalTrace G (a * b) = canonicalTrace G (b * a) := by
  refine DenseRange.induction_on₂ (denseRange_algebraicMap G) ?_ ?_ a b
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x y
    calc
      canonicalTrace G (algebraicMap G x * algebraicMap G y) =
          canonicalTrace G (algebraicMap G (x * y)) := by
            congr 1
            exact ((algebraicMap G).map_mul x y).symm
      _ = (x * y).coeff 1 := canonicalTrace_algebraicMap (x * y)
      _ = (y * x).coeff 1 := coefficientAtOne_mul_comm x y
      _ = canonicalTrace G (algebraicMap G (y * x)) :=
        (canonicalTrace_algebraicMap (y * x)).symm
      _ = canonicalTrace G (algebraicMap G y * algebraicMap G x) := by
        congr 1
        exact (algebraicMap G).map_mul y x

/-! ## Transport along group equivalences -/

def reindex
    {G : Type u} {H : Type v} (e : G ≃ H) (xi : GroupL2 G) (h : H) : ℂ :=
  xi (e.symm h)

theorem reindex_mem
    {G : Type u} {H : Type v} (e : G ≃ H) (xi : GroupL2 G) :
    Memℓp (reindex e xi) 2 := by
  have hxi := lp.memℓp xi
  rw [memℓp_gen_iff (by norm_num)] at hxi ⊢
  change Summable ((fun i : G => ‖xi i‖ ^ (2 : ℝ≥0∞).toReal) ∘ e.symm)
  exact e.symm.summable_iff.mpr hxi

theorem reindex_norm
    {G : Type u} {H : Type v} (e : G ≃ H) (xi : GroupL2 G) :
    ‖(⟨reindex e xi, reindex_mem e xi⟩ : GroupL2 H)‖ = ‖xi‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  simpa only [reindex] using
    e.symm.tsum_eq (fun g : G => ‖xi g‖ ^ (2 : ℝ≥0∞).toReal)

/-- Reindexing `ℓ²` along an equivalence. -/
noncomputable def groupL2Equiv
    {G : Type u} {H : Type v} (e : G ≃ H) : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 H where
  toFun xi := ⟨reindex e xi, reindex_mem e xi⟩
  invFun eta := ⟨reindex e.symm eta, reindex_mem e.symm eta⟩
  left_inv xi := by
    ext g
    simp [reindex]
  right_inv eta := by
    ext h
    simp [reindex]
  map_add' xi eta := by
    ext h
    rfl
  map_smul' c xi := by
    ext h
    rfl
  norm_map' xi := reindex_norm e xi

@[simp]
theorem groupL2Equiv_apply
    {G : Type u} {H : Type v} (e : G ≃ H) (xi : GroupL2 G) (h : H) :
    groupL2Equiv e xi h = xi (e.symm h) :=
  rfl

@[simp]
theorem groupL2Equiv_symm_apply
    {G : Type u} {H : Type v} (e : G ≃ H) (eta : GroupL2 H) (g : G) :
    (groupL2Equiv e).symm eta g = eta (e g) :=
  rfl

@[simp]
theorem groupL2Equiv_delta
    {G : Type u} {H : Type v} (e : G ≃ H) (g : G) :
    groupL2Equiv e (delta g) = delta (e g) := by
  classical
  ext h
  simp [groupL2Equiv_apply, kroneckerDelta, e.eq_symm_apply]

/-- Conjugation of bounded operators by the coordinate reindexing unitary. -/
noncomputable def ambientEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) :
    (GroupL2 G →L[ℂ] GroupL2 G) ≃⋆ₐ[ℂ]
      (GroupL2 H →L[ℂ] GroupL2 H) :=
  (groupL2Equiv e.toEquiv).conjStarAlgEquiv

@[simp]
theorem ambientEquiv_leftRegular
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    ambientEquiv e (leftRegularOperatorHom G g) =
      leftRegularOperatorHom H (e g) := by
  ext eta h
  simp [ambientEquiv, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

@[simp]
theorem ambientEquiv_integratedLeftRegular
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ComplexGroupAlgebra G) :
    ambientEquiv e (integratedLeftRegular G a) =
      integratedLeftRegular H (groupAlgebraEquiv e a) := by
  classical
  induction a using ComplexGroupAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single_case g c =>
      simp [integratedLeftRegular_single, ambientEquiv_leftRegular]

theorem ambientEquiv_mem_reduced
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : GroupL2 G →L[ℂ] GroupL2 G)
    (ha : a ∈ reducedGroupCStarSubalgebra G) :
    ambientEquiv e a ∈ reducedGroupCStarSubalgebra H := by
  change a ∈ closure
    ((integratedLeftRegular G).range :
      Set (GroupL2 G →L[ℂ] GroupL2 G)) at ha
  change ambientEquiv e a ∈ closure
    ((integratedLeftRegular H).range :
      Set (GroupL2 H →L[ℂ] GroupL2 H))
  refine map_mem_closure (StarAlgEquiv.isometry (ambientEquiv e)).continuous ha ?_
  rintro _ ⟨c, rfl⟩
  exact ⟨groupAlgebraEquiv e c, (ambientEquiv_integratedLeftRegular e c).symm⟩

theorem ambientEquiv_symm_mem_reduced
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (b : GroupL2 H →L[ℂ] GroupL2 H)
    (hb : b ∈ reducedGroupCStarSubalgebra H) :
    (ambientEquiv e).symm b ∈ reducedGroupCStarSubalgebra G := by
  change b ∈ closure
    ((integratedLeftRegular H).range :
      Set (GroupL2 H →L[ℂ] GroupL2 H)) at hb
  change (ambientEquiv e).symm b ∈ closure
    ((integratedLeftRegular G).range :
      Set (GroupL2 G →L[ℂ] GroupL2 G))
  refine map_mem_closure
    (StarAlgEquiv.isometry (ambientEquiv e).symm).continuous hb ?_
  rintro _ ⟨c, rfl⟩
  refine ⟨(groupAlgebraEquiv e).symm c, ?_⟩
  rw [eq_comm, (ambientEquiv e).symm_apply_eq]
  change integratedLeftRegular H c =
    ambientEquiv e (integratedLeftRegular G ((groupAlgebraEquiv e).symm c))
  rw [ambientEquiv_integratedLeftRegular]
  simp

/-- A group equivalence induces a star-algebra equivalence of reduced group
C-star algebras. -/
noncomputable def mapEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) :
    ReducedGroupCStarAlgebra G ≃⋆ₐ[ℂ] ReducedGroupCStarAlgebra H where
  toFun a := ⟨ambientEquiv e a.1, ambientEquiv_mem_reduced e a.1 a.2⟩
  invFun b := ⟨(ambientEquiv e).symm b.1,
    ambientEquiv_symm_mem_reduced e b.1 b.2⟩
  left_inv a := by
    apply Subtype.ext
    exact (ambientEquiv e).left_inv a.1
  right_inv b := by
    apply Subtype.ext
    exact (ambientEquiv e).right_inv b.1
  map_add' a b := by
    apply Subtype.ext
    exact map_add (ambientEquiv e) a.1 b.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (ambientEquiv e) a.1 b.1
  map_star' a := by
    apply Subtype.ext
    exact map_star (ambientEquiv e) a.1
  map_smul' c a := by
    apply Subtype.ext
    exact map_smul (ambientEquiv e) c a.1

@[simp]
theorem mapEquiv_val
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ReducedGroupCStarAlgebra G) :
    ((mapEquiv e a : ReducedGroupCStarAlgebra H) :
      GroupL2 H →L[ℂ] GroupL2 H) = ambientEquiv e a.1 :=
  rfl

@[simp]
theorem mapEquiv_algebraicMap
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ComplexGroupAlgebra G) :
    mapEquiv e (algebraicMap G a) =
      algebraicMap H (groupAlgebraEquiv e a) := by
  apply Subtype.ext
  exact ambientEquiv_integratedLeftRegular e a

@[simp]
theorem mapEquiv_groupUnitary
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    mapEquiv e (groupUnitary g : ReducedGroupCStarAlgebra G) =
      (groupUnitary (e g) : ReducedGroupCStarAlgebra H) := by
  change mapEquiv e (algebraicMap G (ComplexGroupAlgebra.single g 1)) =
    algebraicMap H (ComplexGroupAlgebra.single (e g) 1)
  rw [mapEquiv_algebraicMap, groupAlgebraEquiv_single]

@[simp]
theorem canonicalTrace_mapEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (a : ReducedGroupCStarAlgebra G) :
    canonicalTrace H (mapEquiv e a) = canonicalTrace G a := by
  rw [canonicalTrace_apply, canonicalTrace_apply, mapEquiv_val]
  let U : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 H := groupL2Equiv e.toEquiv
  have hdelta : U (delta (1 : G)) = delta (1 : H) := by
    simp [U]
  rw [← hdelta]
  simp only [ambientEquiv, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    U, LinearIsometryEquiv.symm_apply_apply]
  exact (groupL2Equiv e.toEquiv).inner_map_map _ _

@[simp]
theorem mapEquiv_refl
    (G : Type u) [Group G] :
    mapEquiv (MulEquiv.refl G) = StarAlgEquiv.refl ℂ (ReducedGroupCStarAlgebra G) := by
  apply StarAlgEquiv.ext
  intro a
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro xi
  ext g
  rfl

@[simp]
theorem mapEquiv_trans
    {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H ≃* K) :
    mapEquiv (e.trans f) = (mapEquiv e).trans (mapEquiv f) := by
  apply StarAlgEquiv.ext
  intro a
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro xi
  ext k
  rfl

end

end MathlibExt.Analysis.CStarAlgebra.Group
