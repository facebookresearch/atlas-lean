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

public import MathlibExt.KTheory.Milnor.ClassicalDegreeSteinbergEq

/-!
# Classical degreewise presentation as textbook quotient

`MilnorK F n` is the canonical homogeneous component `MilnorKRing.degree F n`
of the Milnor K-ring, i.e. the image of `TensorRing.degree F n` under the
quotient map `MilnorKRing.mkLinear`. This module supplies the textbook
quotient presentation: the `ℤ`-module quotient of `TensorRing.degree F n` by
the explicit Steinberg span `steinbergDegreeSpanInDegree F n`, together with
the linear equivalence

`MilnorK.classicalPresentationEquiv F n : MilnorK F n ≃ₗ[ℤ] MilnorK.MilnorKPresentation F n`

realized as the inverse of the generic
`TwoSidedIdeal.quotientGradeEquiv` composed with the equality
`steinbergDegreeSubmodule = steinbergDegreeSpanInDegree`.

## Main definitions
* `MilnorK.MilnorKPresentation F n` – textbook quotient
  `TensorRing.degree F n ⧸ steinbergDegreeSpanInDegree F n`
* `MilnorK.classicalPresentationEquiv`

## Main results
* `MilnorK.classicalPresentationEquiv_apply_mk`
* `MilnorK.classicalPresentationEquiv_symm_apply_mk`
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

/-- Textbook quotient presentation of `MilnorK F n` as
`TensorRing.degree F n ⧸ steinbergDegreeSpanInDegree F n`. -/
abbrev MilnorKPresentation (n : ℕ) : Type _ :=
  TensorRing.degree F n ⧸ steinbergDegreeSpanInDegree F n

/-- The equivalence between `MilnorK F n` and its textbook quotient presentation.

It is built as the inverse of the generic homogeneous quotient equivalence
`TwoSidedIdeal.quotientGradeEquiv` for `steinbergIdeal F`, followed by the
quotient transport along `steinbergDegreeSubmodule = steinbergDegreeSpanInDegree`. -/
noncomputable def classicalPresentationEquiv (n : ℕ) :
    MilnorK F n ≃ₗ[ℤ] MilnorKPresentation F n :=
  ((steinbergIdeal F).quotientGradeEquiv (Agrade := TensorRing.degree F) n).symm.trans
    (Submodule.quotEquivOfEq _ _
      (steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree F n))

/-- The forward direction of `classicalPresentationEquiv` sends the class `mk F n x`
to the quotient class of `x` modulo `steinbergDegreeSpanInDegree`. -/
@[simp]
lemma classicalPresentationEquiv_apply_mk (n : ℕ)
    (x : TensorRing.degree F n) :
    classicalPresentationEquiv F n (mk F n x) =
      Submodule.Quotient.mk x := by
  let e := (steinbergIdeal F).quotientGradeEquiv (Agrade := TensorRing.degree F) n
  let q := Submodule.quotEquivOfEq _ _
    (steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree F n)
  have h_e_mk : e (Submodule.Quotient.mk x) = mk F n x :=
    (TwoSidedIdeal.quotientGradeEquiv_mk
      (I := steinbergIdeal F) (Agrade := TensorRing.degree F) (i := n) (x := x)).trans rfl
  have h_symm : e.symm (mk F n x) = Submodule.Quotient.mk x := by
    calc e.symm (mk F n x) = e.symm (e (Submodule.Quotient.mk x)) := by
            rw [← h_e_mk]
      _ = Submodule.Quotient.mk x := e.symm_apply_apply (Submodule.Quotient.mk x)
  have h_q : q (e.symm (mk F n x)) = q (Submodule.Quotient.mk x) :=
    congrArg q h_symm
  calc classicalPresentationEquiv F n (mk F n x)
      = q (e.symm (mk F n x)) := rfl
    _ = q (Submodule.Quotient.mk x) := h_q
    _ = Submodule.Quotient.mk x :=
        Submodule.quotEquivOfEq_mk _ _ _ x

/-- The inverse of `classicalPresentationEquiv` sends the quotient class of `x`
to the Milnor class `mk F n x`. -/
@[simp]
lemma classicalPresentationEquiv_symm_apply_mk (n : ℕ)
    (x : TensorRing.degree F n) :
    (classicalPresentationEquiv F n).symm (Submodule.Quotient.mk x) =
      mk F n x := by
  calc (classicalPresentationEquiv F n).symm (Submodule.Quotient.mk x)
      = (classicalPresentationEquiv F n).symm
          (classicalPresentationEquiv F n (mk F n x)) := by
        rw [classicalPresentationEquiv_apply_mk]
    _ = mk F n x :=
        (classicalPresentationEquiv F n).symm_apply_apply (mk F n x)

end MilnorK
