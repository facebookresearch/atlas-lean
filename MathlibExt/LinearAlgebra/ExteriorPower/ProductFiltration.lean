/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.Product
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Mixed-weight filtration of an exterior power of a product

For R-modules M and N over a commutative ring, the exterior product decomposition identifies
⋀[R]^m(M × N) with the direct sum of ⋀[R]^i M ⊗[R] ⋀[R]^j N over i + j = m. The mixed
injection places the M factors before the N factors.

The descending stage F_m^q is defined by vanishing of all coordinates with first degree i < q.
It begins at F_m^0 = ⊤ and is zero for q > m. For q ≤ m, projection to the coordinate (q, m −
q) is surjective with a mixed-injection section, and its kernel is the next stage F_m^(q+1)
viewed inside F_m^q. Thus the successive quotient is ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N.

A module decomposition e : W ≃ₗ[R] M × N transports these stages, projections, kernels and
quotient coordinates through ⋀^m e. The construction includes degree zero and both extreme
weights for arbitrary modules and separate carrier universes.

See Bourbaki, *Algebra*, Chapter III, for exterior powers of direct sums.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum

universe u v w

namespace exteriorPower.ProductFiltration

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

-- Bind the native exterior-power subgroup structure to the given scalar ring.
local instance (P : Type*) [AddCommGroup P] [Module R P] (m : ℕ) :
    AddCommGroup (⋀[R]^m P) :=
  Submodule.addCommGroup (R := R) (exteriorPower R m P)

/-- For m : ℕ, Index m is the subtype of pairs (i, j) : ℕ × ℕ satisfying i + j = m. It indexes
every complementary mixed weight in degree m, including (0, m) and (m, 0). -/
abbrev Index (m : ℕ) := {p : ℕ × ℕ // p.1 + p.2 = m}

abbrev Piece (m : ℕ) (p : Index m) := (⋀[R]^p.val.1 M) ⊗[R] (⋀[R]^p.val.2 N)

/-- Let R be a commutative ring and M and N R-modules. For m : ℕ and p = (i, j) with i + j = m,
coordinate R M N m p : ⋀[R]^m (M × N) →ₗ[R] (⋀[R]^i M ⊗[R] ⋀[R]^j N) is the p-th direct-sum
projection after the exterior-product equivalence. -/
def coordinate (m : ℕ) (p : Index m) :
    (⋀[R]^m (M × N)) →ₗ[R] Piece R M N m p :=
  (DirectSum.component R (Index m) (Piece R M N m) p).comp
    (exteriorPower.productEquiv R M N m).toLinearMap

/-- Let R be a commutative ring and M and N R-modules. For p = (i, j) with i + j = m, injection R
M N m p maps ⋀[R]^i M ⊗[R] ⋀[R]^j N into ⋀[R]^m (M × N) using the inverse exterior-product
equivalence and the p-th summand inclusion. A pure tensor x ⊗ y maps to the exterior image of
x under inl multiplied by the exterior image of y under inr, in that order. -/
def injection (m : ℕ) (p : Index m) :
    Piece R M N m p →ₗ[R] (⋀[R]^m (M × N)) :=
  (exteriorPower.productEquiv R M N m).symm.toLinearMap.comp
    (DirectSum.lof R (Index m) (Piece R M N m) p)

theorem coordinate_injection_same (m : ℕ) (p : Index m) (z : Piece R M N m p) :
    coordinate R M N m p (injection R M N m p z) = z := by
  simp only [coordinate, injection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]

theorem coordinate_injection_ne (m : ℕ) (p p' : Index m) (h : p ≠ p')
    (z : Piece R M N m p') :
    coordinate R M N m p (injection R M N m p' z) = 0 := by
  simp only [coordinate, injection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, DirectSum.component.of,
    dif_neg (Ne.symm h)]

/-- Let R be a commutative ring and M and N R-modules. For m, q : ℕ, filtration R M N m q is the
submodule of ⋀[R]^m (M × N) consisting of z with coordinate R M N m (i, j) z = 0 whenever i +
j = m and i < q. Thus only first weights at least q are retained. -/
def filtration (m q : ℕ) : Submodule R (⋀[R]^m (M × N)) where
  carrier := {z | ∀ p : Index m, p.val.1 < q → coordinate R M N m p z = 0}
  zero_mem' := by intro p _; exact map_zero _
  add_mem' := by
    intro x y hx hy p hp
    rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by
    intro r z hz p hp
    rw [map_smul, hz p hp, smul_zero]

-- The stage inherits its native subgroup structure over the same ring R.
local instance (m q : ℕ) : AddCommGroup (filtration R M N m q) :=
  Submodule.addCommGroup (R := R) (filtration R M N m q)

theorem filtration_antitone (m : ℕ) {q q' : ℕ} (h : q ≤ q') :
    filtration R M N m q' ≤ filtration R M N m q := by
  intro z hz p hp
  exact hz p (lt_of_lt_of_le hp h)

theorem filtration_zero (m : ℕ) : filtration R M N m 0 = ⊤ := by
  ext z
  change (∀ p : Index m, p.val.1 < 0 → coordinate R M N m p z = 0) ↔ True
  simp only [Nat.not_lt_zero, false_implies, implies_true]

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. If m < q, then filtration R
M N m q = ⊥, since every complementary first weight is at most m. -/
theorem filtration_eq_bot (m q : ℕ) (h : m < q) :
    filtration R M N m q = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  apply (exteriorPower.productEquiv R M N m).injective
  rw [map_zero]
  apply DirectSum.ext_component R
  intro p
  change coordinate R M N m p z = 0
  exact hz p (by have hp := p.property; omega)

/-- For m, q : ℕ with q ≤ m, index m q hq is the pair (q, m − q) in Index m. Its degree sum is q +
(m − q) = m. -/
def index (m q : ℕ) (hq : q ≤ m) : Index m := ⟨(q, m - q), by omega⟩

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m, gradeProjection
R M N m q hq : F_m^q →ₗ[R] ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N is the restriction of the coordinate
projection for (q, m − q) to F_m^q. -/
def gradeProjection (m q : ℕ) (hq : q ≤ m) :
    filtration R M N m q →ₗ[R] Piece R M N m (index m q hq) :=
  (coordinate R M N m (index m q hq)).comp (filtration R M N m q).subtype

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m, gradeSection R M
N m q hq maps the mixed tensor piece ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N into F_m^q by the (q, m − q)
injection. Its other first-weight coordinates below q are zero, and projection to the q-th
grade returns the given tensor. -/
def gradeSection (m q : ℕ) (hq : q ≤ m) :
    Piece R M N m (index m q hq) →ₗ[R] filtration R M N m q :=
  (injection R M N m (index m q hq)).codRestrict (filtration R M N m q) (by
    intro z p hp
    apply coordinate_injection_ne
    intro h
    have hfirst := congrArg (fun p : Index m => p.val.1) h
    change p.val.1 = q at hfirst
    omega)

theorem gradeProjection_section (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) :
    gradeProjection R M N m q hq (gradeSection R M N m q hq z) = z :=
  coordinate_injection_same R M N m (index m q hq) z

theorem gradeProjection_surjective (m q : ℕ) (hq : q ≤ m) :
    Function.Surjective (gradeProjection R M N m q hq) :=
  fun z => ⟨gradeSection R M N m q hq z, gradeProjection_section R M N m q hq z⟩

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. Define nextStage R M N m q
as the inverse image of F_m^(q+1) under the inclusion F_m^q → ⋀[R]^m (M × N). It is F_m^(q+1)
viewed as a submodule of F_m^q. -/
def nextStage (m q : ℕ) : Submodule R (filtration R M N m q) :=
  (filtration R M N m (q + 1)).comap (filtration R M N m q).subtype

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m, the kernel of
gradeProjection R M N m q hq equals nextStage R M N m q. A stage element lies in the next
stage precisely when its remaining coordinate of first weight q vanishes. -/
theorem gradeProjection_ker (m q : ℕ) (hq : q ≤ m) :
    (gradeProjection R M N m q hq).ker = nextStage R M N m q := by
  ext z
  change coordinate R M N m (index m q hq) z.val = 0 ↔
    ∀ p : Index m, p.val.1 < q + 1 → coordinate R M N m p z.val = 0
  constructor
  · intro hz p hp
    by_cases hpq : p.val.1 < q
    · exact z.property p hpq
    · have heq : p = index m q hq := by
        apply Subtype.ext
        apply Prod.ext <;> have hsum := p.property <;> dsimp [index] <;> omega
      subst p
      exact hz
  · intro hz
    exact hz (index m q hq) (by dsimp [index]; omega)

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For m, q : ℕ,
associatedGraded R M N m q is F_m^q ⧸ nextStage R M N m q, the quotient of the current stage
by the next stage viewed inside it. -/
def associatedGraded (m q : ℕ) :=
  _root_.Quotient (Submodule.quotientRel (R := R) (M := filtration R M N m q)
    (nextStage R M N m q))

-- These are the native quotient structures on the adjacent-stage quotient.
instance (m q : ℕ) : AddCommGroup (associatedGraded R M N m q) :=
  Submodule.Quotient.addCommGroup (R := R) (M := filtration R M N m q)
    (nextStage R M N m q)

instance (m q : ℕ) : Module R (associatedGraded R M N m q) :=
  Submodule.Quotient.module (R := R) (M := filtration R M N m q)
    (nextStage R M N m q)

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m, the coordinate
projection induces an R-linear equivalence associatedGraded R M N m q ≃ₗ[R] ⋀[R]^q M ⊗[R]
⋀[R]^(m−q) N. Its inverse takes a mixed tensor to the class of its grade section. -/
def associatedGradedEquiv (m q : ℕ) (hq : q ≤ m) :
    associatedGraded R M N m q ≃ₗ[R]
      (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  by
    let eQ := Submodule.quotEquivOfEq (R := R) (M := filtration R M N m q)
      (nextStage R M N m q)
      (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm
    let eP := LinearMap.quotKerEquivOfSurjective (R := R)
      (M := filtration R M N m q)
      (M₂ := Piece R M N m (index m q hq))
      (gradeProjection R M N m q hq)
      (gradeProjection_surjective R M N m q hq)
    let e := eQ.trans eP
    exact e

/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m and z : F_m^q,
associatedGradedEquiv R M N m q hq [z] = coordinate R M N m (q, m − q) z.val. The class [z] is
in the quotient by nextStage. -/
theorem associatedGradedEquiv_mk (m q : ℕ) (hq : q ≤ m)
    (z : filtration R M N m q) :
    associatedGradedEquiv R M N m q hq
      (Submodule.Quotient.mk (p := nextStage R M N m q) z) =
      coordinate R M N m (index m q hq) z.val := by
  let eQ := Submodule.quotEquivOfEq (R := R) (M := filtration R M N m q)
      (nextStage R M N m q)
    (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm
  let eP := LinearMap.quotKerEquivOfSurjective (R := R)
    (M := filtration R M N m q)
    (M₂ := Piece R M N m (index m q hq))
    (gradeProjection R M N m q hq)
    (gradeProjection_surjective R M N m q hq)
  have hQ : eQ (Submodule.Quotient.mk (p := nextStage R M N m q) z) =
      Submodule.Quotient.mk (p := (gradeProjection R M N m q hq).ker) z :=
    Submodule.quotEquivOfEq_mk (R := R) (M := filtration R M N m q)
      (nextStage R M N m q)
      (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm z
  have hP : eP (Submodule.Quotient.mk (p := (gradeProjection R M N m q hq).ker) z) =
      gradeProjection R M N m q hq z :=
    LinearMap.quotKerEquivOfSurjective_apply_mk (R := R)
      (M := filtration R M N m q)
      (M₂ := Piece R M N m (index m q hq))
      (gradeProjection R M N m q hq)
      (gradeProjection_surjective R M N m q hq) z
  change eP (eQ (Submodule.Quotient.mk (p := nextStage R M N m q) z)) =
    gradeProjection R M N m q hq z
  exact (congrArg eP hQ).trans hP

section Transport

universe z

variable {W : Type z} [AddCommGroup W] [Module R W] (e : W ≃ₗ[R] M × N)

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For m, q : ℕ,
transportedFiltration R M N e m q is the inverse image θ_m⁻¹(F_m^q) in ⋀[R]^m W, where F_m^q
is the product filtration defined by zero coordinates of first weight below q. -/
def transportedFiltration (m q : ℕ) : Submodule R (⋀[R]^m W) :=
  (filtration R M N m q).comap (exteriorPower.mapEquiv R W m e).toLinearMap

-- The transported stage uses the native subgroup structure over R as well.
local instance (m q : ℕ) : AddCommGroup (transportedFiltration R M N e m q) :=
  Submodule.addCommGroup (R := R) (transportedFiltration R M N e m q)

theorem transportedFiltration_zero (m : ℕ) : transportedFiltration R M N e m 0 = ⊤ := by
  rw [transportedFiltration, filtration_zero, Submodule.comap_top]

theorem transportedFiltration_eq_bot (m q : ℕ) (h : m < q) :
    transportedFiltration R M N e m q = ⊥ := by
  rw [transportedFiltration, filtration_eq_bot R M N m q h, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (exteriorPower.mapEquiv R W m e).injective

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For m, q : ℕ,
restricting θ_m gives an R-linear equivalence transportedFiltration R M N e m q ≃ₗ[R]
filtration R M N m q. Its forward map is θ_m on the underlying stage element, and its inverse
is θ_m⁻¹. -/
def transportedStageEquiv (m q : ℕ) :
    transportedFiltration R M N e m q ≃ₗ[R] filtration R M N m q :=
  (exteriorPower.mapEquiv R W m e).ofSubmodule' (filtration R M N m q)

def transportedNextStage (m q : ℕ) : Submodule R (transportedFiltration R M N e m q) :=
  (transportedFiltration R M N e m (q + 1)).comap
    (transportedFiltration R M N e m q).subtype

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For q ≤ m,
transportedGradeProjection R M N e m q hq sends a transported stage element z to the (q, m −
q) coordinate of θ_m(z.val). Its target is ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N. -/
def transportedGradeProjection (m q : ℕ) (hq : q ≤ m) :
    transportedFiltration R M N e m q →ₗ[R] Piece R M N m (index m q hq) :=
  (gradeProjection R M N m q hq).comp (transportedStageEquiv R M N e m q).toLinearMap

theorem transportedGradeProjection_surjective (m q : ℕ) (hq : q ≤ m) :
    Function.Surjective (transportedGradeProjection R M N e m q hq) :=
  (gradeProjection_surjective R M N m q hq).comp
    (transportedStageEquiv R M N e m q).surjective

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For q ≤ m, the
kernel of transportedGradeProjection R M N e m q hq equals transportedNextStage R M N e m q,
the inverse image of the transported stage q + 1 inside stage q. -/
theorem transportedGradeProjection_ker (m q : ℕ) (hq : q ≤ m) :
    (transportedGradeProjection R M N e m q hq).ker =
      transportedNextStage R M N e m q := by
  rw [transportedGradeProjection, LinearMap.ker_comp, gradeProjection_ker]
  ext x
  change ((transportedStageEquiv R M N e m q x : filtration R M N m q) :
      ⋀[R]^m (M × N)) ∈ filtration R M N m (q + 1) ↔
    exteriorPower.mapEquiv R W m e x.val ∈ filtration R M N m (q + 1)
  rfl

def transportedAssociatedGraded (m q : ℕ) :=
  _root_.Quotient (Submodule.quotientRel (R := R) (M := transportedFiltration R M N e m q)
    (transportedNextStage R M N e m q))

-- Transported quotients use the same native group and module structures.
instance (m q : ℕ) : AddCommGroup (transportedAssociatedGraded R M N e m q) :=
  Submodule.Quotient.addCommGroup (R := R) (M := transportedFiltration R M N e m q)
    (transportedNextStage R M N e m q)

instance (m q : ℕ) : Module R (transportedAssociatedGraded R M N e m q) :=
  Submodule.Quotient.module (R := R) (M := transportedFiltration R M N e m q)
    (transportedNextStage R M N e m q)

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For q ≤ m, the
transported adjacent-stage quotient is R-linearly equivalent to ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N. It
sends a class [z] to the (q, m − q) coordinate of θ_m(z.val). -/
def transportedAssociatedGradedEquiv (m q : ℕ) (hq : q ≤ m) :
    transportedAssociatedGraded R M N e m q ≃ₗ[R]
      (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  by
    let eQ := Submodule.quotEquivOfEq (R := R) (M := transportedFiltration R M N e m q)
      (transportedNextStage R M N e m q)
      (transportedGradeProjection R M N e m q hq).ker
      (transportedGradeProjection_ker R M N e m q hq).symm
    let eP := LinearMap.quotKerEquivOfSurjective (R := R)
      (M := transportedFiltration R M N e m q)
      (M₂ := Piece R M N m (index m q hq))
      (transportedGradeProjection R M N e m q hq)
      (transportedGradeProjection_surjective R M N e m q hq)
    let eG := eQ.trans eP
    exact eG

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For q ≤ m and z
: ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N, transportedMixedClass assigns the class of
θ_m⁻¹(injection_(q,m−q)(z)) in the quotient of transported stage q by transported stage q + 1.
This representative is supplied by the inverse stage equivalence applied to the product grade
section. -/
def transportedMixedClass (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) : transportedAssociatedGraded R M N e m q :=
  Submodule.Quotient.mk (p := transportedNextStage R M N e m q)
    ((transportedStageEquiv R M N e m q).symm (gradeSection R M N m q hq z))

theorem transportedAssociatedGradedEquiv_mk (m q : ℕ) (hq : q ≤ m)
    (z : transportedFiltration R M N e m q) :
    transportedAssociatedGradedEquiv R M N e m q hq
      (Submodule.Quotient.mk (p := transportedNextStage R M N e m q) z) =
      transportedGradeProjection R M N e m q hq z := by
  let eQ := Submodule.quotEquivOfEq (R := R) (M := transportedFiltration R M N e m q)
      (transportedNextStage R M N e m q)
    (transportedGradeProjection R M N e m q hq).ker
    (transportedGradeProjection_ker R M N e m q hq).symm
  let eP := LinearMap.quotKerEquivOfSurjective (R := R)
    (M := transportedFiltration R M N e m q)
    (M₂ := Piece R M N m (index m q hq))
    (transportedGradeProjection R M N e m q hq)
    (transportedGradeProjection_surjective R M N e m q hq)
  have hQ : eQ (Submodule.Quotient.mk (p := transportedNextStage R M N e m q) z) =
      Submodule.Quotient.mk (p := (transportedGradeProjection R M N e m q hq).ker) z :=
    Submodule.quotEquivOfEq_mk (R := R) (M := transportedFiltration R M N e m q)
      (transportedNextStage R M N e m q)
      (transportedGradeProjection R M N e m q hq).ker
      (transportedGradeProjection_ker R M N e m q hq).symm z
  have hP : eP (Submodule.Quotient.mk (p := (transportedGradeProjection R M N e m q hq).ker) z) =
      transportedGradeProjection R M N e m q hq z :=
    LinearMap.quotKerEquivOfSurjective_apply_mk (R := R)
      (M := transportedFiltration R M N e m q)
      (M₂ := Piece R M N m (index m q hq))
      (transportedGradeProjection R M N e m q hq)
      (transportedGradeProjection_surjective R M N e m q hq) z
  change eP (eQ (Submodule.Quotient.mk (p := transportedNextStage R M N e m q) z)) =
    transportedGradeProjection R M N e m q hq z
  exact (congrArg eP hQ).trans hP

/-- Let R be a commutative ring and M and N R-modules. Let W be an R-module and e : W ≃ₗ[R] M × N
a module decomposition. Write θ_m = ⋀^m e for its exterior-power equivalence. For q ≤ m and
any tensor z in ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N, transportedAssociatedGradedEquiv applied to
transportedMixedClass z equals z. -/
theorem transportedMixedClass_equiv (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) :
    transportedAssociatedGradedEquiv R M N e m q hq
        (transportedMixedClass R M N e m q hq z) = z := by
  rw [transportedMixedClass, transportedAssociatedGradedEquiv_mk]
  change gradeProjection R M N m q hq
    ((transportedStageEquiv R M N e m q)
      ((transportedStageEquiv R M N e m q).symm (gradeSection R M N m q hq z))) = z
  rw [LinearEquiv.apply_symm_apply, gradeProjection_section]

theorem transportedMixedClass_ne_zero (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) (hz : z ≠ 0) :
    transportedMixedClass R M N e m q hq z ≠ 0 := by
  intro h
  have h' := transportedMixedClass_equiv R M N e m q hq z
  rw [h, map_zero] at h'
  exact hz h'.symm

end Transport

end exteriorPower.ProductFiltration

end
