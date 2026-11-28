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

public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.InjectiveShiftedRange
public import MathlibExt.RingTheory.Length.Graded

/-!
# Length recurrence for injective shifted maps

An injective degree-`d` map identifies each source grade with the corresponding
shifted grade of its homogeneous range.  Combining that equivalence with the
fixed-degree range/ambient/quotient exact sequence gives the natural-valued
length recurrence.  Degree-one endomorphisms yield the successor form used by
Hilbert--Serre induction.

The range-grade identification preserves natural-number lengths over any
commutative coefficient ring. Additivity of the finite component lengths
uses the Artinian coefficient-ring and finite-degree-piece hypotheses.

## Main declarations

* `GradedModule.IsHomogeneousOfDegree.moduleLengthNat_rangeGrade_eq`
* `GradedModule.IsHomogeneousOfDegree.gradedPieceLength_eq_add_rangeQuotient`
* `GradedModule.IsHomogeneousOfDegree.gradedPieceLength_succ_eq_add_rangeQuotient`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GradedModule.IsHomogeneousOfDegree

universe uA uS uM uN

variable {A : Type uA} [CommRing A] [IsArtinianRing A]
variable {S : Type uS} [CommRing S] [Algebra A S]
variable {M : Type uM} [AddCommGroup M]
  [Module A M] [Module S M] [IsScalarTower A S M]
variable {N : Type uN} [AddCommGroup N]
  [Module A N] [Module S N] [IsScalarTower A S N]

variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M)
  [DirectSum.Decomposition Mgrade]
  [∀ n, Module.Finite A (Mgrade n)]
variable (Ngrade : ℕ → Submodule A N)
  [SetLike.GradedSMul Sgrade Ngrade]
  [DirectSum.Decomposition Ngrade]
  [∀ n, Module.Finite A (Ngrade n)]
variable {d : ℕ} {f : M →ₗ[S] N}
variable (hf : GradedModule.IsHomogeneousOfDegree Mgrade Ngrade d f)

omit [∀ n, Module.Finite A (Ngrade n)] [∀ n, Module.Finite A (Mgrade n)]
    [IsArtinianRing A] in
/-- Let `A` be a commutative ring, `S` a graded commutative `A`-algebra,
and `M`, `N` graded `S`-modules with compatible `A`-actions. If a linear map
`f : M → N` is injective and homogeneous of degree `d`, the natural-number
length of degree `d+n` in its inherited homogeneous range equals the
natural-number length of `M_n`. This equality does not require Artinian
coefficients or finite graded pieces. -/
theorem moduleLengthNat_rangeGrade_eq
    (hinj : Function.Injective f) (n : ℕ) :
    HilbertSamuel.moduleLengthNat A
        ((hf.rangeHomogeneousSubmodule Sgrade).grade
          Sgrade Ngrade (d + n)) =
      HilbertSamuel.gradedPieceLength A Mgrade n := by
  unfold HilbertSamuel.moduleLengthNat HilbertSamuel.gradedPieceLength
  exact congrArg ENat.toNat
    (rangeGradeEquiv Sgrade Mgrade Ngrade hf hinj n).length_eq.symm

/-- Let `A` be an Artinian commutative ring, `S` a graded commutative
`A`-algebra, and `M`, `N` graded `S`-modules with compatible `A`-actions and
finite `A`-module degree pieces. For an injective homogeneous map `f : M → N`
of degree `d`, `lengthNat_A(N_{d+n})` equals `lengthNat_A(M_n)` plus the
length of degree `d+n` in the quotient by the homogeneous range of `f`. -/
theorem gradedPieceLength_eq_add_rangeQuotient
    (hinj : Function.Injective f) (n : ℕ) :
    HilbertSamuel.gradedPieceLength A Ngrade (d + n) =
      HilbertSamuel.gradedPieceLength A Mgrade n +
        HilbertSamuel.moduleLengthNat A
          ((hf.rangeHomogeneousSubmodule Sgrade).quotientGrade
            Sgrade Ngrade (d + n)) := by
  let R := hf.rangeHomogeneousSubmodule Sgrade
  let e := rangeGradeEquiv Sgrade Mgrade Ngrade hf hinj n
  let _ : Module.Finite A (R.grade Sgrade Ngrade (d + n)) :=
    Module.Finite.equiv e
  simpa only [HilbertSamuel.gradedPieceLength] using
    HilbertSamuel.moduleLengthNat_eq_add_of_exact A
      ((R.gradeInclusion Sgrade Ngrade (d + n)).comp e.toLinearMap)
      (R.gradeQuotient Sgrade Ngrade (d + n))
      ((R.gradeInclusion_injective Sgrade Ngrade (d + n)).comp
        e.injective)
      (R.gradeQuotient_surjective Sgrade Ngrade (d + n))
      (rangeGrade_exact Sgrade Mgrade Ngrade hf hinj n)

/-- Let `A` be an Artinian commutative ring, `S` a graded commutative
`A`-algebra, and `M` a graded `S`-module with compatible `A`-action and finite
`A`-module degree pieces. For an injective homogeneous endomorphism `f` of
degree one, `lengthNat_A(M_{n+1})` equals `lengthNat_A(M_n)` plus the
length of degree `n+1` in the quotient by the homogeneous range of `f`. -/
theorem gradedPieceLength_succ_eq_add_rangeQuotient
    [SetLike.GradedSMul Sgrade Mgrade]
    {f : Module.End S M}
    (hf : GradedModule.IsHomogeneousOfDegree Mgrade Mgrade 1 f)
    (hinj : Function.Injective f) (n : ℕ) :
    HilbertSamuel.gradedPieceLength A Mgrade (n + 1) =
      HilbertSamuel.gradedPieceLength A Mgrade n +
        HilbertSamuel.moduleLengthNat A
          ((hf.rangeHomogeneousSubmodule Sgrade).quotientGrade
            Sgrade Mgrade (n + 1)) := by
  have h := gradedPieceLength_eq_add_rangeQuotient
    Sgrade Mgrade Mgrade hf hinj n
  rw [Nat.one_add] at h
  simpa only [Nat.add_one] using h

end GradedModule.IsHomogeneousOfDegree
