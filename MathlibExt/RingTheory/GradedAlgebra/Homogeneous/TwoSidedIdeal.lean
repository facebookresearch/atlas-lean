/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Graded quotient by a homogeneous two-sided ideal

For a graded `R`-algebra `A = ⨁ i, Agrade i` and a two-sided ideal `I` whose
underlying ideal is homogeneous, the quotient `A ⧸ I.ringCon` inherits a grading
with `i`-th piece the image of `Agrade i` under `mkₐ`. We construct the
`GradedAlgebra` instance via componentwise mapping of `decomposeAlgEquiv`,
descent through `RingCon.liftₐ`, and `GradedAlgebra.ofAlgHom`; we also expose
the canonical quotient map as a `GradedRingHom` and prove that a homogeneous
element decomposes to `of` its class.

The convenience `GradedAlgebra` instance is synthesized when a
`Fact (I.asIdeal.IsHomogeneous Agrade)` instance is available, while the explicit
constructor `TwoSidedIdeal.gradedAlgebraQuotientGrade` accepts the homogeneity
proof directly.
-/

@[expose] public section

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

/-- `i`-th graded piece of the quotient by a two-sided ideal: image of `Agrade i` under `mkₐ`. -/
def TwoSidedIdeal.quotientGrade (I : TwoSidedIdeal A) (Agrade : ι → Submodule R A) (i : ι) :
    Submodule R I.ringCon.Quotient :=
  (Agrade i).map (I.ringCon.mkₐ R).toLinearMap

end

@[expose] public section QuotientComponent

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

variable {ι : Type*} {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A}

/-- Canonical `R`-linear projection from the `i`-th graded piece `Agrade i`
into its image in the quotient `A ⧸ I.ringCon`, i.e. `I.quotientGrade Agrade i`.
This is the degreewise component of the graded quotient map. It does not require
homogeneity of `I`; homogeneity is only needed for the full graded algebra
structure on the quotient. -/
def TwoSidedIdeal.quotientGradeComponent (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    Agrade i →ₗ[R] I.quotientGrade Agrade i where
  toFun x := ⟨(I.ringCon.mkₐ R) (x : A), Submodule.mem_map_of_mem x.2⟩
  map_add' a b := by apply Subtype.ext; simp
  map_smul' r a := by apply Subtype.ext; simp

/-- The component map lands in the quotient as `mkₐ`. -/
@[simp]
theorem TwoSidedIdeal.quotientGradeComponent_coe (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) (x : Agrade i) :
    (I.quotientGradeComponent (Agrade := Agrade) i x : I.ringCon.Quotient) =
      (I.ringCon.mkₐ R) (x : A) :=
  rfl

/-- The degreewise quotient component map is surjective onto `I.quotientGrade Agrade i`. -/
theorem TwoSidedIdeal.quotientGradeComponent_surjective (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    Function.Surjective (I.quotientGradeComponent (Agrade := Agrade) i) := by
  intro y
  have hy : (y : I.ringCon.Quotient) ∈ (Agrade i).map (I.ringCon.mkₐ R).toLinearMap := by
    simpa [TwoSidedIdeal.quotientGrade] using y.2
  rw [Submodule.mem_map] at hy
  obtain ⟨a, ha, ha_eq⟩ := hy
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  exact ha_eq

/-- Kernel of the degreewise quotient component map is the comap of `I.asIdeal`
along the subtype `Agrade i → A`, considered as an `R`-submodule via restriction of
scalars. This description does not need homogeneity. -/
theorem TwoSidedIdeal.quotientGradeComponent_ker (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    LinearMap.ker (I.quotientGradeComponent (Agrade := Agrade) i) =
      Submodule.comap (Agrade i).subtype (I.asIdeal.restrictScalars R) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem,
    TwoSidedIdeal.mem_asIdeal]
  have h_zero : I.quotientGradeComponent (Agrade := Agrade) i x = 0 ↔
      (I.ringCon.mkₐ R) (x : A) = 0 := by
    constructor
    · intro h
      have : (I.quotientGradeComponent i x : I.ringCon.Quotient) = 0 := by
        calc (I.quotientGradeComponent i x : I.ringCon.Quotient)
            = ((0 : I.quotientGrade Agrade i) : I.ringCon.Quotient) := by rw [h]
          _ = 0 := rfl
      rwa [TwoSidedIdeal.quotientGradeComponent_coe] at this
    · intro h
      exact Subtype.ext (by simpa [TwoSidedIdeal.quotientGradeComponent_coe] using h)
  rw [h_zero]
  have hker : TwoSidedIdeal.ker (I.ringCon.mkₐ R).toRingHom = I := by
    have : TwoSidedIdeal.ker (I.ringCon.mkₐ R).toRingHom =
        TwoSidedIdeal.ker I.ringCon.mk' := by
      ext y; simp [RingCon.mkₐ]
    rw [this, TwoSidedIdeal.ker_ringCon_mk']
  have h_eq : (I.ringCon.mkₐ R).toRingHom (x : A) = (I.ringCon.mkₐ R) (x : A) := rfl
  rw [← h_eq, ← TwoSidedIdeal.mem_ker, hker]
  rfl

end QuotientComponent

@[expose] public section QuotientComponentEquiv

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable {ι : Type*} {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A}

/-- Linear equivalence between the quotient of a graded component by the comap of
`I.asIdeal` (as an `R`-submodule) and its image `I.quotientGrade Agrade i` in the
two-sided quotient. This is the first isomorphism theorem for `quotientGradeComponent`.
Requires `CommRing R` for the `Submodule` quotient API. -/
noncomputable def TwoSidedIdeal.quotientGradeEquiv (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    (Agrade i ⧸ Submodule.comap (Agrade i).subtype (I.asIdeal.restrictScalars R)) ≃ₗ[R]
      I.quotientGrade Agrade i :=
  (Submodule.quotEquivOfEq _ _ (I.quotientGradeComponent_ker (Agrade := Agrade) i).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (I.quotientGradeComponent (Agrade := Agrade) i)
      (I.quotientGradeComponent_surjective i))

/-- The equivalence `quotientGradeEquiv` sends the class of `x` to the component map. -/
@[simp]
theorem TwoSidedIdeal.quotientGradeEquiv_mk (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) (x : Agrade i) :
    I.quotientGradeEquiv (Agrade := Agrade) i (Submodule.Quotient.mk x) =
      I.quotientGradeComponent i x := by
  unfold TwoSidedIdeal.quotientGradeEquiv
  calc (Submodule.quotEquivOfEq _ _
          (I.quotientGradeComponent_ker (Agrade := Agrade) i).symm).trans
          (LinearMap.quotKerEquivOfSurjective _ _) (Submodule.Quotient.mk x)
      = (LinearMap.quotKerEquivOfSurjective
            (I.quotientGradeComponent (Agrade := Agrade) i)
            (I.quotientGradeComponent_surjective i))
          ((Submodule.quotEquivOfEq _ _
              (I.quotientGradeComponent_ker (Agrade := Agrade) i).symm)
            (Submodule.Quotient.mk x)) := by
        simp [LinearEquiv.trans_apply]
    _ = (LinearMap.quotKerEquivOfSurjective
            (I.quotientGradeComponent (Agrade := Agrade) i)
            (I.quotientGradeComponent_surjective i))
          (Submodule.Quotient.mk x) := by
        simp [Submodule.quotEquivOfEq_mk]
    _ = I.quotientGradeComponent (Agrade := Agrade) i x := by
        simp [LinearMap.quotKerEquivOfSurjective_apply_mk]

end QuotientComponentEquiv

@[expose] public section

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

variable {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]

/-- The quotient grading by a homogeneous two-sided ideal inherits the graded unit,
    with `1` in degree `0` induced from the base grading. -/
instance instGradedOneQuotientGrade : SetLike.GradedOne (I.quotientGrade (Agrade := Agrade)) where
  one_mem := by
    have h1 : (1 : A) ∈ Agrade 0 := SetLike.one_mem_graded Agrade
    change (1 : I.ringCon.Quotient) ∈ I.quotientGrade Agrade 0
    rw [TwoSidedIdeal.quotientGrade, Submodule.mem_map]
    exact ⟨1, h1, by simp⟩

/-- The quotient grading by a homogeneous two-sided ideal respects graded
    multiplication, with products of quotient pieces lying in the sum degree. -/
instance instGradedMulQuotientGrade :
    SetLike.GradedMul (I.quotientGrade (Agrade := Agrade)) where
  mul_mem := by
    intro i j x y hx hy
    have hx' : x ∈ (Agrade i).map (I.ringCon.mkₐ R).toLinearMap := by
      simpa [TwoSidedIdeal.quotientGrade] using hx
    have hy' : y ∈ (Agrade j).map (I.ringCon.mkₐ R).toLinearMap := by
      simpa [TwoSidedIdeal.quotientGrade] using hy
    rw [Submodule.mem_map] at hx' hy'
    obtain ⟨x0, hx0, rfl⟩ := hx'
    obtain ⟨y0, hy0, rfl⟩ := hy'
    rw [TwoSidedIdeal.quotientGrade, Submodule.mem_map]
    exact ⟨x0 * y0, SetLike.mul_mem_graded hx0 hy0, by simp⟩

/-- Combined graded-monoid structure on the quotient grading by a homogeneous
    two-sided ideal, combining the graded unit and multiplication. -/
instance instGradedMonoidQuotientGrade :
    SetLike.GradedMonoid (I.quotientGrade (Agrade := Agrade)) where

end

section PrivateConstruction

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

variable {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]

private def TwoSidedIdeal.quotientGradeLoF (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    Agrade i →ₗ[R] (⨁ i, I.quotientGrade Agrade i) :=
  (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) i).comp
    (I.quotientGradeComponent (Agrade := Agrade) i)

private def TwoSidedIdeal.directSumMapToQuotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] :
    (⨁ i, Agrade i) →ₐ[R] (⨁ i, I.quotientGrade Agrade i) :=
  DirectSum.toAlgebra R (fun i => Agrade i)
    (fun i => I.quotientGradeLoF (Agrade := Agrade) i)
    (by
      have h_one_src : GradedMonoid.GOne.one (A := fun i => Agrade i) =
          (⟨1, SetLike.one_mem_graded Agrade⟩ : Agrade 0) := rfl
      have h_inner : I.quotientGradeComponent (Agrade := Agrade) 0
          (GradedMonoid.GOne.one (A := fun i => Agrade i)) =
          GradedMonoid.GOne.one (A := fun i => I.quotientGrade Agrade i) := by
        rw [h_one_src]; apply Subtype.ext; simp [TwoSidedIdeal.quotientGradeComponent]
      calc I.quotientGradeLoF (Agrade := Agrade) 0
            (GradedMonoid.GOne.one (A := fun i => Agrade i))
          = (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) 0)
              (I.quotientGradeComponent 0
                (GradedMonoid.GOne.one (A := fun i => Agrade i))) := rfl
        _ = (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) 0)
              (GradedMonoid.GOne.one (A := fun i => I.quotientGrade Agrade i)) := by
            rw [h_inner]
        _ = 1 := rfl
    )
    (by
      intro i j ai aj
      have h_mul_src : GradedMonoid.GMul.mul (A := fun i => Agrade i) ai aj =
          (⟨(ai : A) * (aj : A), SetLike.mul_mem_graded ai.2 aj.2⟩ : Agrade (i + j)) := rfl
      have h_inner : I.quotientGradeComponent (Agrade := Agrade) (i + j)
          (GradedMonoid.GMul.mul (A := fun i => Agrade i) ai aj) =
          GradedMonoid.GMul.mul (A := fun i => I.quotientGrade Agrade i)
            (I.quotientGradeComponent i ai) (I.quotientGradeComponent j aj) := by
        apply Subtype.ext; simp [TwoSidedIdeal.quotientGradeComponent, h_mul_src]
      calc I.quotientGradeLoF (Agrade := Agrade) (i + j)
            (GradedMonoid.GMul.mul (A := fun i => Agrade i) ai aj)
          = DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) (i + j)
              (I.quotientGradeComponent (i + j)
                (GradedMonoid.GMul.mul (A := fun i => Agrade i) ai aj)) := rfl
        _ = DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) (i + j)
              (GradedMonoid.GMul.mul (A := fun i => I.quotientGrade Agrade i)
                (I.quotientGradeComponent i ai) (I.quotientGradeComponent j aj)) := by
            rw [h_inner]
        _ = DirectSum.of (fun i => (I.quotientGrade Agrade i : Type _)) (i + j)
              (GradedMonoid.GMul.mul (A := fun i => I.quotientGrade Agrade i)
                (I.quotientGradeComponent i ai) (I.quotientGradeComponent j aj)) := by
            rw [DirectSum.lof_eq_of]
        _ = DirectSum.of (fun i => (I.quotientGrade Agrade i : Type _)) i
              (I.quotientGradeComponent i ai) *
            DirectSum.of (fun i => (I.quotientGrade Agrade i : Type _)) j
              (I.quotientGradeComponent j aj) := by
            rw [DirectSum.of_mul_of]
        _ = (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) i
                (I.quotientGradeComponent i ai)) *
            (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) j
                (I.quotientGradeComponent j aj)) := by
            rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
        _ = I.quotientGradeLoF i ai * I.quotientGradeLoF j aj := rfl
    )

private theorem TwoSidedIdeal.directSumMap_of (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] (i : ι) (x : Agrade i) :
    I.directSumMapToQuotientGrade (DirectSum.of (fun i => Agrade i) i x) =
      I.quotientGradeLoF i x := by
  have h_toMod : (I.directSumMapToQuotientGrade (Agrade := Agrade).toLinearMap) =
      DirectSum.toModule R ι (⨁ i, I.quotientGrade Agrade i)
        (fun i => I.quotientGradeLoF (Agrade := Agrade) i) := rfl
  calc I.directSumMapToQuotientGrade (DirectSum.of _ i x)
      = I.directSumMapToQuotientGrade.toLinearMap (DirectSum.of _ i x) := rfl
    _ = (DirectSum.toModule R ι (⨁ i, I.quotientGrade Agrade i)
          (fun i => I.quotientGradeLoF i)) (DirectSum.of _ i x) := by rw [h_toMod]
    _ = (DirectSum.toModule R ι (⨁ i, I.quotientGrade Agrade i)
          (fun i => I.quotientGradeLoF i)) (DirectSum.lof R ι (fun i => Agrade i) i x) := by
        rw [DirectSum.lof_eq_of]
    _ = I.quotientGradeLoF i x := by rw [DirectSum.toModule_lof]

private def TwoSidedIdeal.phiToQuotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] :
    A →ₐ[R] (⨁ i, I.quotientGrade Agrade i) :=
  (I.directSumMapToQuotientGrade (Agrade := Agrade)).comp
    (DirectSum.decomposeAlgEquiv Agrade).toAlgHom

private theorem TwoSidedIdeal.phi_eq_zero_of_mem (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) {x : A} (hx : x ∈ I) :
    I.phiToQuotientGrade (Agrade := Agrade) x = 0 := by
  classical
  have h_decomp : DirectSum.decompose Agrade x =
      ∑ i ∈ (DirectSum.decompose Agrade x).support,
        DirectSum.of (fun i => Agrade i) i (DirectSum.decompose Agrade x i) :=
    (DirectSum.sum_support_of (DirectSum.decompose Agrade x)).symm
  have h_phi : I.phiToQuotientGrade (Agrade := Agrade) x =
      I.directSumMapToQuotientGrade (DirectSum.decompose Agrade x) := rfl
  rw [h_phi, h_decomp, map_sum]
  have h_eq : ∀ i ∈ (DirectSum.decompose Agrade x).support,
      I.directSumMapToQuotientGrade (DirectSum.of _ i (DirectSum.decompose Agrade x i)) =
        I.quotientGradeLoF i (DirectSum.decompose Agrade x i) := by
    intro i _; rw [TwoSidedIdeal.directSumMap_of]
  rw [Finset.sum_congr rfl h_eq]
  apply Finset.sum_eq_zero
  intro i _hi
  have h_mem_I : (DirectSum.decompose Agrade x i : A) ∈ I := hI i hx
  have h_mk_zero : (I.ringCon.mkₐ R) (DirectSum.decompose Agrade x i : A) = 0 := by
    have h_eq_ker : TwoSidedIdeal.ker (I.ringCon.mkₐ R).toRingHom = I := by
      have : TwoSidedIdeal.ker (I.ringCon.mkₐ R).toRingHom = TwoSidedIdeal.ker I.ringCon.mk' := by
        ext y; simp [RingCon.mkₐ]
      rw [this, TwoSidedIdeal.ker_ringCon_mk']
    have h_in_ker : (DirectSum.decompose Agrade x i : A) ∈
        TwoSidedIdeal.ker (I.ringCon.mkₐ R).toRingHom := by
      rw [h_eq_ker]; exact h_mem_I
    rw [TwoSidedIdeal.mem_ker] at h_in_ker
    simpa using h_in_ker
  have h_lin_zero : I.quotientGradeComponent (Agrade := Agrade) i
      (DirectSum.decompose Agrade x i) = 0 := by
    apply Subtype.ext; exact h_mk_zero
  have h_lof_zero : I.quotientGradeLoF (Agrade := Agrade) i
      (DirectSum.decompose Agrade x i) = 0 := by
    calc I.quotientGradeLoF i (DirectSum.decompose Agrade x i)
        = (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) i)
            (I.quotientGradeComponent i (DirectSum.decompose Agrade x i)) := rfl
      _ = (DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) i) 0 := by
          rw [h_lin_zero]
      _ = 0 := by simp
  exact h_lof_zero

private theorem TwoSidedIdeal.phiToQuotientGrade_ringCon_le (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) :
    I.ringCon ≤ RingCon.ker (I.phiToQuotientGrade (Agrade := Agrade)).toRingHom := by
  intro x y hxy
  have h_mem : x - y ∈ I := by
    have h_iff := TwoSidedIdeal.rel_iff (I := I) (x := x) (y := y)
    exact h_iff.mp hxy
  have h_phi_sub : I.phiToQuotientGrade (Agrade := Agrade) (x - y) = 0 :=
    I.phi_eq_zero_of_mem (Agrade := Agrade) hI h_mem
  have h_add : y + (x - y) = x := add_sub_cancel y x
  have h_x_eq : x = y + (x - y) := h_add.symm
  have h_phi_x : I.phiToQuotientGrade (Agrade := Agrade) x =
      I.phiToQuotientGrade (Agrade := Agrade) y +
        I.phiToQuotientGrade (Agrade := Agrade) (x - y) := by
    have h1 : I.phiToQuotientGrade (Agrade := Agrade) x =
        I.phiToQuotientGrade (Agrade := Agrade) (y + (x - y)) :=
      congrArg (I.phiToQuotientGrade (Agrade := Agrade)) h_x_eq
    have h2 : I.phiToQuotientGrade (Agrade := Agrade) (y + (x - y)) =
        I.phiToQuotientGrade (Agrade := Agrade) y +
          I.phiToQuotientGrade (Agrade := Agrade) (x - y) :=
      map_add (I.phiToQuotientGrade (Agrade := Agrade)) y (x - y)
    exact h1.trans h2
  rw [h_phi_sub, add_zero] at h_phi_x
  have h_eq : (I.phiToQuotientGrade (Agrade := Agrade)).toRingHom x =
      (I.phiToQuotientGrade (Agrade := Agrade)).toRingHom y := by
    simpa using h_phi_x
  exact h_eq

private noncomputable def TwoSidedIdeal.quotientGradeDecomposeAlgHom (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) :
    I.ringCon.Quotient →ₐ[R] (⨁ i, I.quotientGrade Agrade i) :=
  I.ringCon.liftₐ (I.phiToQuotientGrade (Agrade := Agrade))
    (I.phiToQuotientGrade_ringCon_le (Agrade := Agrade) hI)

private theorem TwoSidedIdeal.quotientGradeDecomposeAlgHom_mk (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) (x : A) :
    I.quotientGradeDecomposeAlgHom (Agrade := Agrade) hI ((I.ringCon.mkₐ R) x) =
      I.phiToQuotientGrade (Agrade := Agrade) x := by
  have h_eq : ((I.ringCon.mkₐ R) x : I.ringCon.Quotient) = (↑x : I.ringCon.Quotient) := rfl
  have h := RingCon.liftₐ_mk I.ringCon (I.phiToQuotientGrade (Agrade := Agrade))
    (I.phiToQuotientGrade_ringCon_le (Agrade := Agrade) hI) x
  calc I.quotientGradeDecomposeAlgHom hI ((I.ringCon.mkₐ R) x)
      = I.quotientGradeDecomposeAlgHom hI (↑x : I.ringCon.Quotient) := by rw [h_eq]
    _ = I.phiToQuotientGrade x := h

private def TwoSidedIdeal.quotientGradeSubtype (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} (i : ι) :
    I.quotientGrade Agrade i →ₗ[R] I.ringCon.Quotient :=
  (I.quotientGrade Agrade i).subtype

private noncomputable def TwoSidedIdeal.quotientGradeToQuotientAlgHom (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] :
    (⨁ i, I.quotientGrade Agrade i) →ₐ[R] I.ringCon.Quotient :=
  coeAlgHom (I.quotientGrade Agrade)

private theorem TwoSidedIdeal.coeAlgHom_of_quotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] (i : ι)
    (x : I.quotientGrade Agrade i) :
    I.quotientGradeToQuotientAlgHom (Agrade := Agrade)
        (DirectSum.of (fun i => I.quotientGrade Agrade i) i x) = (x : I.ringCon.Quotient) := by
  have h_toMod : (I.quotientGradeToQuotientAlgHom (Agrade := Agrade).toLinearMap) =
      DirectSum.toModule R ι I.ringCon.Quotient
        (fun i => I.quotientGradeSubtype (Agrade := Agrade) i) := rfl
  calc I.quotientGradeToQuotientAlgHom (DirectSum.of _ i x)
      = I.quotientGradeToQuotientAlgHom.toLinearMap (DirectSum.of _ i x) := rfl
    _ = (DirectSum.toModule R ι I.ringCon.Quotient
          (fun i => I.quotientGradeSubtype i)) (DirectSum.of _ i x) := by rw [h_toMod]
    _ = (DirectSum.toModule R ι I.ringCon.Quotient
          (fun i => I.quotientGradeSubtype i))
          (DirectSum.lof R ι (fun i => I.quotientGrade Agrade i) i x) := by rw [DirectSum.lof_eq_of]
    _ = I.quotientGradeSubtype i x := by rw [DirectSum.toModule_lof]
    _ = (x : I.ringCon.Quotient) := rfl

private theorem TwoSidedIdeal.coeAlgHom_of_Agrade {Agrade : ι → Submodule R A}
    [GradedAlgebra Agrade] (i : ι) (x : Agrade i) :
    (coeAlgHom Agrade) (DirectSum.of (fun i => Agrade i) i x) = (x : A) := by
  have h_toMod : (coeAlgHom Agrade).toLinearMap =
      DirectSum.toModule R ι A (fun i => (Agrade i).subtype) := rfl
  calc (coeAlgHom Agrade) (DirectSum.of _ i x)
      = (coeAlgHom Agrade).toLinearMap (DirectSum.of _ i x) := rfl
    _ = (DirectSum.toModule R ι A (fun i => (Agrade i).subtype)) (DirectSum.of _ i x) := by
        rw [h_toMod]
    _ = (DirectSum.toModule R ι A (fun i => (Agrade i).subtype))
          (DirectSum.lof R ι (fun i => Agrade i) i x) := by rw [DirectSum.lof_eq_of]
    _ = (Agrade i).subtype x := by rw [DirectSum.toModule_lof]
    _ = (x : A) := rfl

private theorem TwoSidedIdeal.coe_comp_directSumMap (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] (i : ι) (x : Agrade i) :
    I.quotientGradeToQuotientAlgHom (Agrade := Agrade)
        (I.directSumMapToQuotientGrade (Agrade := Agrade)
          (DirectSum.of (fun i => Agrade i) i x)) =
      (I.ringCon.mkₐ R) ((coeAlgHom Agrade) (DirectSum.of (fun i => Agrade i) i x)) := by
  rw [TwoSidedIdeal.directSumMap_of, TwoSidedIdeal.coeAlgHom_of_Agrade]
  have h_left : I.quotientGradeToQuotientAlgHom
      (I.quotientGradeLoF (Agrade := Agrade) i x) =
      (I.ringCon.mkₐ R) (x : A) := by
    calc I.quotientGradeToQuotientAlgHom (I.quotientGradeLoF i x)
        = I.quotientGradeToQuotientAlgHom
            ((DirectSum.lof R ι (fun i => (I.quotientGrade Agrade i : Type _)) i)
              (I.quotientGradeComponent i x)) := rfl
      _ = I.quotientGradeToQuotientAlgHom
            (DirectSum.of (fun i => (I.quotientGrade Agrade i : Type _)) i
              (I.quotientGradeComponent i x)) := by rw [DirectSum.lof_eq_of]
      _ = ((I.quotientGradeComponent i x : I.quotientGrade Agrade i) : I.ringCon.Quotient) := by
          rw [TwoSidedIdeal.coeAlgHom_of_quotientGrade]
      _ = (I.ringCon.mkₐ R) (x : A) := rfl
  exact h_left

private theorem TwoSidedIdeal.coe_comp_directSumMap_eq (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] :
    (I.quotientGradeToQuotientAlgHom (Agrade := Agrade)).comp
        (I.directSumMapToQuotientGrade (Agrade := Agrade)) =
      (I.ringCon.mkₐ R).comp (coeAlgHom Agrade) := by
  apply DirectSum.algHom_ext
  intro i x
  exact TwoSidedIdeal.coe_comp_directSumMap I i x

private theorem TwoSidedIdeal.coeAlgHom_eq_symm {Agrade : ι → Submodule R A}
    [GradedAlgebra Agrade] :
    coeAlgHom Agrade = (DirectSum.decomposeAlgEquiv Agrade).symm.toAlgHom := by
  apply DirectSum.algHom_ext
  intro i x
  have h_decomp : DirectSum.decompose Agrade (x : A) =
      DirectSum.of (fun i => Agrade i) i x :=
    decompose_coe Agrade x
  have h_symm : (DirectSum.decomposeAlgEquiv Agrade).symm
      (DirectSum.of (fun i => Agrade i) i x) = (x : A) := by
    calc (DirectSum.decomposeAlgEquiv Agrade).symm
          (DirectSum.of (fun i => Agrade i) i x)
        = (DirectSum.decomposeAlgEquiv Agrade).symm
            (DirectSum.decompose Agrade (x : A)) := by rw [← h_decomp]
      _ = (x : A) := by simp
  calc (coeAlgHom Agrade) (DirectSum.of (fun i => Agrade i) i x)
      = (x : A) := TwoSidedIdeal.coeAlgHom_of_Agrade i x
    _ = (DirectSum.decomposeAlgEquiv Agrade).symm
          (DirectSum.of (fun i => Agrade i) i x) := by rw [h_symm]

private theorem TwoSidedIdeal.coe_decompose_Agrade {Agrade : ι → Submodule R A}
    [GradedAlgebra Agrade] (x : A) :
    (coeAlgHom Agrade) (DirectSum.decompose Agrade x) = x := by
  calc (coeAlgHom Agrade) (DirectSum.decompose Agrade x)
      = (DirectSum.decomposeAlgEquiv Agrade).symm.toAlgHom
          (DirectSum.decompose Agrade x) := by rw [TwoSidedIdeal.coeAlgHom_eq_symm]
    _ = (DirectSum.decomposeAlgEquiv Agrade).symm
          ((DirectSum.decomposeAlgEquiv Agrade) x) := rfl
    _ = x := by rw [AlgEquiv.symm_apply_apply]

private theorem TwoSidedIdeal.coe_comp_decompose_mk (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) (a : A) :
    I.quotientGradeToQuotientAlgHom (Agrade := Agrade)
        (I.quotientGradeDecomposeAlgHom (Agrade := Agrade) hI ((I.ringCon.mkₐ R) a)) =
      (I.ringCon.mkₐ R) a := by
  calc I.quotientGradeToQuotientAlgHom
        (I.quotientGradeDecomposeAlgHom hI ((I.ringCon.mkₐ R) a))
      = I.quotientGradeToQuotientAlgHom
          (I.phiToQuotientGrade (Agrade := Agrade) a) := by
        rw [TwoSidedIdeal.quotientGradeDecomposeAlgHom_mk]
    _ = I.quotientGradeToQuotientAlgHom
          (I.directSumMapToQuotientGrade (Agrade := Agrade)
            (DirectSum.decompose Agrade a)) := rfl
    _ = (I.ringCon.mkₐ R) ((coeAlgHom Agrade) (DirectSum.decompose Agrade a)) := by
        have h_eq := TwoSidedIdeal.coe_comp_directSumMap_eq I (Agrade := Agrade)
        have h_eq' : I.quotientGradeToQuotientAlgHom
            (I.directSumMapToQuotientGrade (DirectSum.decompose Agrade a)) =
            (I.ringCon.mkₐ R) ((coeAlgHom Agrade) (DirectSum.decompose Agrade a)) := by
          calc I.quotientGradeToQuotientAlgHom
                (I.directSumMapToQuotientGrade (DirectSum.decompose Agrade a))
              = ((I.quotientGradeToQuotientAlgHom.comp
                  I.directSumMapToQuotientGrade) (DirectSum.decompose Agrade a)) := rfl
            _ = (((I.ringCon.mkₐ R).comp (coeAlgHom Agrade))
                  (DirectSum.decompose Agrade a)) := by rw [h_eq]
            _ = (I.ringCon.mkₐ R) ((coeAlgHom Agrade) (DirectSum.decompose Agrade a)) := rfl
        exact h_eq'
    _ = (I.ringCon.mkₐ R) a := by
        rw [TwoSidedIdeal.coe_decompose_Agrade]

private theorem TwoSidedIdeal.right_inv_quotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) :
    (coeAlgHom (I.quotientGrade Agrade)).comp
        (I.quotientGradeDecomposeAlgHom (Agrade := Agrade) hI) =
      AlgHom.id R I.ringCon.Quotient := by
  apply AlgHom.ext
  intro q
  obtain ⟨a, ha⟩ : ∃ a : A, (↑a : I.ringCon.Quotient) = q :=
    Quotient.exists_rep q
  have ha_mk : (I.ringCon.mkₐ R) a = q := by
    have : ((I.ringCon.mkₐ R) a : I.ringCon.Quotient) = (↑a : I.ringCon.Quotient) := rfl
    rw [this, ha]
  calc (coeAlgHom (I.quotientGrade Agrade)).comp
          (I.quotientGradeDecomposeAlgHom hI) q
      = (coeAlgHom (I.quotientGrade Agrade)).comp
          (I.quotientGradeDecomposeAlgHom hI) ((I.ringCon.mkₐ R) a) := by rw [← ha_mk]
    _ = (coeAlgHom (I.quotientGrade Agrade))
          (I.quotientGradeDecomposeAlgHom hI ((I.ringCon.mkₐ R) a)) := rfl
    _ = (I.ringCon.mkₐ R) a := by
        have : coeAlgHom (I.quotientGrade Agrade) =
            I.quotientGradeToQuotientAlgHom (Agrade := Agrade) := rfl
        rw [this]
        exact TwoSidedIdeal.coe_comp_decompose_mk I hI a
    _ = q := by rw [ha_mk]

private theorem TwoSidedIdeal.left_inv_quotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) (i : ι)
    (x : I.quotientGrade Agrade i) :
    I.quotientGradeDecomposeAlgHom (Agrade := Agrade) hI (x : I.ringCon.Quotient) =
      DirectSum.of (fun i => I.quotientGrade Agrade i) i x := by
  have hx : (x : I.ringCon.Quotient) ∈ I.quotientGrade Agrade i := x.2
  have hx' : (x : I.ringCon.Quotient) ∈
      (Agrade i).map (I.ringCon.mkₐ R).toLinearMap := by
    simpa [TwoSidedIdeal.quotientGrade] using hx
  rw [Submodule.mem_map] at hx'
  obtain ⟨a, ha, ha_eq⟩ := hx'
  have ha_eq' : (I.ringCon.mkₐ R) a = (x : I.ringCon.Quotient) := ha_eq
  calc I.quotientGradeDecomposeAlgHom hI (x : I.ringCon.Quotient)
      = I.quotientGradeDecomposeAlgHom hI ((I.ringCon.mkₐ R) a) := by rw [← ha_eq']
    _ = I.phiToQuotientGrade (Agrade := Agrade) a := by
        rw [TwoSidedIdeal.quotientGradeDecomposeAlgHom_mk]
    _ = I.directSumMapToQuotientGrade (Agrade := Agrade)
          (DirectSum.decompose Agrade a) := rfl
    _ = I.directSumMapToQuotientGrade
          (DirectSum.of (fun i => Agrade i) i ⟨a, ha⟩) := by
        rw [decompose_coe Agrade ⟨a, ha⟩]
    _ = I.quotientGradeLoF i ⟨a, ha⟩ := by
        rw [TwoSidedIdeal.directSumMap_of]
    _ = DirectSum.of (fun i => I.quotientGrade Agrade i) i
          ⟨(I.ringCon.mkₐ R) a, Submodule.mem_map_of_mem ha⟩ := rfl
    _ = DirectSum.of (fun i => I.quotientGrade Agrade i) i x := by
        have h_sub : (⟨(I.ringCon.mkₐ R) a, Submodule.mem_map_of_mem ha⟩ :
            I.quotientGrade Agrade i) = x := by
          apply Subtype.ext
          exact ha_eq'
        rw [h_sub]

end PrivateConstruction

public section

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

variable {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]

/-- Graded algebra structure on the quotient grading via `ofAlgHom`. -/
@[instance_reducible]
noncomputable def TwoSidedIdeal.gradedAlgebraQuotientGrade (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]
    (hI : I.asIdeal.IsHomogeneous Agrade) :
    GradedAlgebra (I.quotientGrade Agrade) :=
  GradedAlgebra.ofAlgHom (I.quotientGrade Agrade)
    (TwoSidedIdeal.quotientGradeDecomposeAlgHom I (Agrade := Agrade) hI)
    (TwoSidedIdeal.right_inv_quotientGrade I hI)
    (TwoSidedIdeal.left_inv_quotientGrade I hI)

end

@[expose] public section

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

variable {I : TwoSidedIdeal A} {Agrade : ι → Submodule R A} [GradedAlgebra Agrade]

/-- Canonical quotient map as a graded ring hom; it does not need homogeneity. -/
def TwoSidedIdeal.quotientGradeMap (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] :
    GradedRingHom Agrade (I.quotientGrade Agrade) where
  toRingHom := I.ringCon.mk'
  map_mem := by
    intro i x hx
    change (I.ringCon.mk' x) ∈ I.quotientGrade Agrade i
    rw [TwoSidedIdeal.quotientGrade, Submodule.mem_map]
    exact ⟨x, hx, by simp [RingCon.mkₐ, RingCon.mk']⟩

/-- The graded quotient map computes as `I.ringCon.mk'` on each homogeneous component. -/
@[simp]
theorem TwoSidedIdeal.quotientGradeMap_apply (I : TwoSidedIdeal A)
    {Agrade : ι → Submodule R A} [GradedAlgebra Agrade] (x : A) :
    (I.quotientGradeMap (Agrade := Agrade)) x = I.ringCon.mk' x :=
  rfl

end

public section DecompCompat

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Ring A] [Algebra R A]

variable (I : TwoSidedIdeal A) (Agrade : ι → Submodule R A) [GradedAlgebra Agrade]
  [hI : Fact (I.asIdeal.IsHomogeneous Agrade)]

/-- A `Fact` witnessing that the two-sided ideal is homogeneous supplies the
quotient grading with its `GradedAlgebra` instance via
`TwoSidedIdeal.gradedAlgebraQuotientGrade`. -/
noncomputable instance instGradedAlgebraQuotientGradeFact :
    GradedAlgebra (I.quotientGrade Agrade) :=
  TwoSidedIdeal.gradedAlgebraQuotientGrade I Fact.out

/-- Decomposition of a homogeneous element in the quotient is `of` its class. -/
theorem TwoSidedIdeal.decompose_quotientGrade_of_mem {i : ι} {x : A} (hx : x ∈ Agrade i) :
    (decompose (I.quotientGrade Agrade)) (I.ringCon.mk' x) =
      DirectSum.of (fun i => I.quotientGrade Agrade i) i
        ⟨I.ringCon.mk' x, Submodule.mem_map_of_mem hx⟩ := by
  have hx' : ((I.ringCon.mkₐ R) x : I.ringCon.Quotient) ∈ I.quotientGrade Agrade i := by
    rw [TwoSidedIdeal.quotientGrade, Submodule.mem_map]
    exact ⟨x, hx, rfl⟩
  have h_eq : (I.ringCon.mk' x : I.ringCon.Quotient) =
      ((⟨(I.ringCon.mkₐ R) x, hx'⟩ : I.quotientGrade Agrade i) : I.ringCon.Quotient) := rfl
  calc (decompose (I.quotientGrade Agrade)) (I.ringCon.mk' x)
      = (decompose (I.quotientGrade Agrade))
          ((⟨(I.ringCon.mkₐ R) x, hx'⟩ : I.quotientGrade Agrade i) : I.ringCon.Quotient) := by
        rw [h_eq]
    _ = TwoSidedIdeal.quotientGradeDecomposeAlgHom I Fact.out
          ((⟨(I.ringCon.mkₐ R) x, hx'⟩ : I.quotientGrade Agrade i) : I.ringCon.Quotient) := rfl
    _ = DirectSum.of (fun i => I.quotientGrade Agrade i) i
          ⟨(I.ringCon.mkₐ R) x, hx'⟩ :=
        TwoSidedIdeal.left_inv_quotientGrade I Fact.out i ⟨(I.ringCon.mkₐ R) x, hx'⟩
    _ = DirectSum.of (fun i => I.quotientGrade Agrade i) i
          ⟨I.ringCon.mk' x, Submodule.mem_map_of_mem hx⟩ := by
        have : (⟨(I.ringCon.mkₐ R) x, hx'⟩ : I.quotientGrade Agrade i) =
            (⟨I.ringCon.mk' x, Submodule.mem_map_of_mem hx⟩ : I.quotientGrade Agrade i) := by
          apply Subtype.ext; rfl
        rw [this]

end DecompCompat
