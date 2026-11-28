/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The quotient of a graded algebra by a homogeneous ideal

Let `𝒜` be a grading of an `R`-algebra `A` and `I` a homogeneous ideal of `A`. The images
`(𝒜 i).map (A → A ⧸ I)` grade `A ⧸ I` (`Ideal.IsHomogeneous.gradedAlgebra`): the component of
degree `i` of the class of `a` is the class of the component of degree `i` of `a`, which is well
defined because `I` contains the homogeneous components of its elements
(`Ideal.IsHomogeneous.decompose_mk`).

## Main definitions

* `Ideal.quotientGrading 𝒜 I`: the images `i ↦ (𝒜 i).map (Ideal.Quotient.mkₐ R I)` in `A ⧸ I`,
  for any family of submodules `𝒜` and any ideal `I`.
* `Ideal.IsHomogeneous.gradedAlgebra`: these images grade `A ⧸ I` when `𝒜` is a grading of `A`
  and `I` is homogeneous.
-/

@[expose] public section

open DirectSum

namespace Ideal

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) (I : Ideal A)

/-- The images in `A ⧸ I` of the submodules `𝒜 i`: the submodule
`(𝒜 i).map (Ideal.Quotient.mkₐ R I)`. For an arbitrary family `𝒜` and ideal `I` they need not
grade `A ⧸ I`; they form a grading when `𝒜` is a grading of `A` and `I` is homogeneous
(`Ideal.IsHomogeneous.gradedAlgebra`). -/
def quotientGrading (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

variable {𝒜 I}

/-- The class of an element of `𝒜 i` lies in the image `quotientGrading 𝒜 I i` of `𝒜 i`. -/
theorem mk_mem_quotientGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I a ∈ quotientGrading 𝒜 I i :=
  Submodule.mem_map_of_mem ha

/-- The additive map `𝒜 i → (𝒜 i).map π` induced by the quotient map `π : A → A ⧸ I`. -/
def quotientGradingMk (i : ι) : 𝒜 i →+ quotientGrading 𝒜 I i where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotientGrading x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_quotientGradingMk (i : ι) (x : 𝒜 i) :
    ((quotientGradingMk (I := I) i x : quotientGrading 𝒜 I i) : A ⧸ I) =
      Ideal.Quotient.mk I x :=
  rfl

variable [DecidableEq ι] [AddMonoid ι]

instance quotientGrading.gradedMonoid [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (quotientGrading 𝒜 I) where
  one_mem := by
    simpa using mk_mem_quotientGrading (I := I) SetLike.GradedOne.one_mem
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    simpa using mk_mem_quotientGrading (I := I) (SetLike.GradedMul.mul_mem ha hb)

variable [GradedAlgebra 𝒜]

/-- The ring map `A → ⨁ i, (𝒜 i).map π` sending `a` to the classes of its homogeneous
components. -/
noncomputable def quotientDecomposeAux : A →+* ⨁ i, quotientGrading 𝒜 I i :=
  (DirectSum.toSemiring (fun i => (DirectSum.of (fun i => quotientGrading 𝒜 I i) i).comp
      (quotientGradingMk (I := I) i))
    (by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rfl)
    (by
      intro i j x y
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.of_mul_of]
      congr 1)).comp (decomposeRingEquiv 𝒜).toRingHom

theorem quotientDecomposeAux_apply (a : A) :
    quotientDecomposeAux (I := I) a =
      DirectSum.toAddMonoid (fun i => (DirectSum.of (fun i => quotientGrading 𝒜 I i) i).comp
        (quotientGradingMk (I := I) i)) (decompose 𝒜 a) :=
  rfl

theorem quotientDecomposeAux_of_mem {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    quotientDecomposeAux (I := I) a =
      DirectSum.of (fun i => quotientGrading 𝒜 I i) i ⟨Ideal.Quotient.mk I a,
        mk_mem_quotientGrading ha⟩ := by
  rw [quotientDecomposeAux_apply, decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

theorem coe_quotientDecomposeAux (a : A) :
    (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I)) (quotientDecomposeAux (I := I) a) =
      Ideal.Quotient.mk I a := by
  classical
  conv_rhs => rw [← sum_support_decompose 𝒜 a]
  rw [map_sum]
  conv_lhs => rw [← sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [quotientDecomposeAux_of_mem (decompose 𝒜 a i).2, DirectSum.coeAddMonoidHom_of]

variable (hI : I.IsHomogeneous 𝒜)
include hI

theorem quotientDecomposeAux_eq_zero {a : A} (ha : a ∈ I) :
    quotientDecomposeAux (I := I) a = (0 : ⨁ i, quotientGrading 𝒜 I i) := by
  classical
  rw [← sum_support_decompose 𝒜 a, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [quotientDecomposeAux_of_mem (decompose 𝒜 a i).2]
  have h0 : (⟨Ideal.Quotient.mk I (decompose 𝒜 a i), mk_mem_quotientGrading (decompose 𝒜 a i).2⟩ :
      quotientGrading 𝒜 I i) = 0 :=
    Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr (hI i ha))
  rw [h0, map_zero]

/-- The decomposition of `A ⧸ I` into the classes of homogeneous components. -/
noncomputable def quotientDecompose : A ⧸ I →+* ⨁ i, quotientGrading 𝒜 I i :=
  Ideal.Quotient.lift I quotientDecomposeAux fun _ ha => quotientDecomposeAux_eq_zero hI ha

/-- The quotient of a graded algebra by a homogeneous ideal is graded by the images of the
homogeneous components. -/
noncomputable abbrev IsHomogeneous.gradedAlgebra : GradedAlgebra (quotientGrading 𝒜 I) where
  toGradedMonoid := inferInstance
  toDecomposition := DirectSum.Decomposition.ofAddHom _ (quotientDecompose hI).toAddMonoidHom
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact coe_quotientDecomposeAux a)
    (by
      refine DirectSum.addHom_ext fun i y => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := y
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact quotientDecomposeAux_of_mem ha)

/-- In the grading of `A ⧸ I` by a homogeneous ideal, the component of degree `i` of the class of
`a` is the class of the component of degree `i` of `a`. -/
theorem IsHomogeneous.decompose_mk (a : A) (i : ι) :
    letI := hI.gradedAlgebra
    ((decompose (quotientGrading 𝒜 I) (Ideal.Quotient.mk I a) i : quotientGrading 𝒜 I i) :
      A ⧸ I) = Ideal.Quotient.mk I (decompose 𝒜 a i) := by
  let := hI.gradedAlgebra
  classical
  conv_lhs => rw [← sum_support_decompose 𝒜 a, map_sum, decompose_sum]
  rw [DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hi : i ∈ (decompose 𝒜 a).support
  · rw [Finset.sum_eq_single_of_mem i hi]
    · exact decompose_of_mem_same _ (mk_mem_quotientGrading (decompose 𝒜 a i).2)
    · intro j _ hji
      exact decompose_of_mem_ne _ (mk_mem_quotientGrading (decompose 𝒜 a j).2) hji
  · rw [Finset.sum_eq_zero]
    · rw [DFinsupp.notMem_support_iff.mp hi]
      simp
    · intro j hj
      exact decompose_of_mem_ne _ (mk_mem_quotientGrading (decompose 𝒜 a j).2)
        (fun h => hi (h ▸ hj))

end Ideal
